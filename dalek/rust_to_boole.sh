#!/bin/sh
# Rust (a Verus-annotated dalek-lite module) -> Boole -> a Strata-Boole benchmark file.
#
#   dalek/rust_to_boole.sh <module.rs> --only <fn> --dalek-lite <dir> --strata-boole <dir> \
#                          --verus-bin <dir> [--lean-out <file.lean>] [--no-lean] [--lean-only]
#
#   dalek/rust_to_boole.sh dalek/input/scalar_helpers.rs --only sum_of_slice \
#       --dalek-lite <path/to/dalek-lite> --strata-boole <path/to/Strata-Boole> \
#       --verus-bin <path/to/verus>/source/target-verus/release
#     -> dalek/out/sum_of_slice.boole.st                       (the Boole program)
#     -> <strata-boole>/StrataBooleTest/dalek_sum_of_slice_translated.lean
#        (three levels: Verus source, Boole + cvc5 #guard_msgs, Lean theorem), built.
#
#   --dalek-lite <dir>     the dalek-lite crate the Rust module is verified in (its
#                          Cargo.toml must point vstd/verus_builtin at the Verus fork —
#                          see README.md for the expected sibling layout)
#   --strata-boole <dir>   the Strata-Boole checkout the Lean file is written into and
#                          built in (its lakefile resolves Strata itself, from git)
#   --verus-bin <dir>      the Verus fork's built release dir (`cargo build --release`
#                          under <verus>/source, toolchain 1.93.1), providing `cargo-verus`
#
# See README.md for the full one-time setup (four repos, toolchain, first build).
#
# Steps
#   1. the module file replaces `curve25519-dalek/src/<module>.rs` in the dalek-lite crate
#      (the function must live in the crate: its contract names dalek's spec functions and
#      vstd, and Verus verifies it there before exporting);
#   2. the Verus fork exports the VLIR of the module and of the modules its contract reaches
#      (`--export-lean-all`, one JSON per module) into dalek/export_json/;
#   3. verus-lean turns the directory of exports into one Boole program:
#        --only <fn>    keep what <fn> transitively needs; other exec/proof fns become
#                       contract stubs (assume false)
#        --u8-as-int    u8 as int      (lean-smt has no bv->int conversion)
#        --drop-proof-hints  no Verus lemma calls or ghost bookkeeping (asserts kept)
#        --values-invariants  a congruence-shaped loop invariant f(a) == f(b), f a mod
#                       reduction, becomes a == b (no modular arithmetic left for Lean)
#        --literal-consts-as-axioms  Scalar::ZERO-style literal constants as an
#                       uninterpreted constant plus length/element axioms
#        --index-by-prefix  a spec fn recursing on subrange(s, 0, len - 1) is re-indexed
#                       by the prefix length: f(s, n); callers f(subrange(e, 0, k)) become
#                       f(e, k) and the `=~=` extensionality hints disappear
#        --total-select  [T; N] reads as Sequence.select! (total); spec fns then carry no
#                       synthesized length requires, so their calls create no obligations
#        --short-names  last path segment as the name (Scalar, group_canonical, sum_of_slice)
#      With --drop-proof-hints a lemma call with no arguments keeps its ensures as axioms.
#   4. gen_lean.py wraps it and Strata-Boole builds the result.  By default this is two
#      builds: a throwaway one to capture cvc5's per-obligation result as a `#guard_msgs`
#      pin on Level 2 (the Boole program plus `#eval Strata.Boole.verify "cvc5"` — cvc5
#      trusted directly), then the real file with Level 3 on top (`gen_smt_vcs_boole; smt`
#      — cvc5's proof reconstructed and checked by the Lean kernel).  `--lean-only` skips
#      the throwaway build and Level 2's `#eval` check
#      entirely, going straight to Level 3.  Faster, but if Level 3 then fails you can no
#      longer tell whether cvc5 couldn't prove the obligation or proved it and Lean's replay
#      choked — Level 2 is what makes that distinction, not a duplicate of Level 3's work.
set -eu

RUST=""; FN=""; DALEK_LITE=""; STRATA_BOOLE=""; VERUS_BIN=""; LEAN_OUT=""; DO_LEAN=1; LEAN_ONLY=0
while [ $# -gt 0 ]; do
  case "$1" in
    --only) FN=$2; shift 2 ;;
    --dalek-lite) DALEK_LITE=$2; shift 2 ;;
    --strata-boole) STRATA_BOOLE=$2; shift 2 ;;
    --verus-bin) VERUS_BIN=$2; shift 2 ;;
    --lean-out) LEAN_OUT=$2; shift 2 ;;
    --no-lean) DO_LEAN=0; shift ;;
    --lean-only) LEAN_ONLY=1; shift ;;
    -*) echo "unknown option $1" >&2; exit 2 ;;
    *) RUST=$1; shift ;;
  esac
done
[ -n "$RUST" ] && [ -n "$FN" ] && [ -n "$DALEK_LITE" ] && [ -n "$STRATA_BOOLE" ] && [ -n "$VERUS_BIN" ] || {
  echo "usage: $0 <module.rs> --only <fn> --dalek-lite <dir> --strata-boole <dir> --verus-bin <dir> [--lean-out <file.lean>] [--no-lean] [--lean-only]" >&2
  exit 2
}
case "$RUST" in /*) ;; *) RUST="$PWD/$RUST" ;; esac
DALEK_LITE=$(cd "$DALEK_LITE" && pwd)
STRATA_BOOLE=$(cd "$STRATA_BOOLE" && pwd)
VERUS_BIN=$(cd "$VERUS_BIN" && pwd)

HERE=$(cd "$(dirname "$0")" && pwd)                          # <verus-boogie>/dalek
VERUS_LEAN=$HERE/../.lake/build/bin/verus-lean
JSON_DIR=$HERE/export_json
OUT=$HERE/out/$FN.boole.st
MODULE=$(basename "$RUST" .rs)
# Modules whose spec functions / operator impls the contract reaches (dalek-lite layout).
EXTRA_MODULES=${EXTRA_MODULES:-"scalar specs::scalar_specs specs::core_specs specs::scalar52_specs"}
[ -n "$LEAN_OUT" ] || LEAN_OUT=$STRATA_BOOLE/StrataBooleTest/dalek_${FN}_translated.lean

# 1. the Rust goes into the crate
cp "$RUST" "$DALEK_LITE/curve25519-dalek/src/$MODULE.rs"

# 2. Verus export
mkdir -p "$JSON_DIR" "$HERE/out"; rm -f "$JSON_DIR"/*.json
args="--verify-module $MODULE"
for m in $EXTRA_MODULES; do args="$args --verify-module $m"; done
# `cargo verus` passes everything after `--` to EVERY verus-checked crate it compiles,
# not just `-p`'s.  On a cold target dir that includes vstd, which has no module by these
# names and fails with "could not find module ... specified by --verify-module".  So build
# the graph once with `--no-verify` (valid for any crate, no module names): vstd lands in
# the cache and the real, scoped run below reuses it instead of re-checking it.  A no-op
# once warm.
( cd "$DALEK_LITE" && PATH="$VERUS_BIN:$PATH" RUSTUP_TOOLCHAIN=1.93.1 \
    cargo verus verify -p curve25519-dalek -- --no-verify > "$JSON_DIR/prime.log" 2>&1 || true )
( cd "$DALEK_LITE" && PATH="$VERUS_BIN:$PATH" RUSTUP_TOOLCHAIN=1.93.1 \
    cargo verus verify -p curve25519-dalek -- $args --export-lean-all > "$JSON_DIR/export.log" 2>&1 || true
  mv "$DALEK_LITE"/*.json "$JSON_DIR"/ 2>/dev/null || {
    echo "ERROR: the Verus export produced no JSON; see $JSON_DIR/export.log" >&2; exit 1; } )
echo "exported: $(ls "$JSON_DIR"/*.json | xargs -n1 basename | tr '\n' ' ')"

# 3. translate
"$VERUS_LEAN" boole --only "$FN" --u8-as-int --drop-proof-hints --values-invariants --literal-consts-as-axioms --index-by-prefix --total-select --short-names "$JSON_DIR" "$OUT" 2> "$HERE/out/$FN.translate.log"
echo "wrote $OUT ($(wc -l < "$OUT" | tr -d ' ') lines)"
grep -q "assume false" "$OUT" && grep -A3 "procedure [A-Za-z_]*_$FN " "$OUT" | grep -q "assume false" && { echo "ERROR: the entry procedure has no body" >&2; exit 1; }

[ "$DO_LEAN" = 1 ] || exit 0
cd "$STRATA_BOOLE"

if [ "$LEAN_ONLY" = 1 ]; then
  # skip the cvc5 guard entirely; Level 2 has no #eval check, Level 3 is the only result
  python3 "$HERE/gen_lean.py" "$FN" "$RUST" "$OUT" "$LEAN_OUT" --no-eval
else
  # 4a. cvc5 guard: build a Level-2-only copy once (seconds), capture the obligations
  TMP=StrataBooleTest/zz_guard_$FN.lean
  python3 "$HERE/gen_lean.py" "$FN" "$RUST" "$OUT" "$TMP" --level2-only > /dev/null
  lake build "StrataBooleTest.zz_guard_$FN" > "$HERE/out/$FN.cvc5.log" 2>&1 || true
  rm -f "$TMP"
  python3 - "$HERE/out/$FN.cvc5.log" "$HERE/out/$FN.guard.txt" <<'EOF'
import sys
log=open(sys.argv[1]).read()
if "Obligation:" not in log:
    print("ERROR: no obligations in the cvc5 log; see", sys.argv[1]); sys.exit(1)
i=log.index("Obligation:"); j=max(log.rfind("Result: ✅ pass"), log.rfind("Result: ❌"), log.rfind("Result: ❓"), log.rfind("Result: 🚨"))
j=log.index("\n", j) if "\n" in log[j:] else len(log)
msg=log[i:j]
n=msg.count("Obligation:"); ok=msg.count("✅ pass")
open(sys.argv[2],"w").write(msg)
print(f"cvc5: {ok}/{n} obligations pass" + ("" if ok==n else "  <-- NOT ALL PASS"))
EOF
  # 4b. the real file, with the guard, then build it (this runs the Lean theorem)
  python3 "$HERE/gen_lean.py" "$FN" "$RUST" "$OUT" "$LEAN_OUT" --guard "$HERE/out/$FN.guard.txt"
fi

MOD=StrataBooleTest.$(basename "$LEAN_OUT" .lean)
if lake build "$MOD" > "$HERE/out/$FN.lean.log" 2>&1; then
  echo "Lean: $MOD builds — every obligation certified by lean-smt"
else
  echo "Lean: $MOD FAILED; see $HERE/out/$FN.lean.log"; grep -n "^error" "$HERE/out/$FN.lean.log" | head -5; exit 1
fi
