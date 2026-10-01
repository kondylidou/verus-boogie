#!/bin/sh
# Rust (a Verus-annotated dalek-lite module) -> Boole -> a checked Strata-Boole file.
#
#   dalek/rust_to_boole.sh <module.rs> --only <fn> --dalek-lite <dir> --strata-boole <dir> \
#                          --verus-bin <dir> [--lean-out <file.lean>] [--no-lean] [--lean-only]
#
# Writes dalek/out/<fn>.boole.st and <strata-boole>/StrataBooleTest/dalek_<fn>.lean.
# Setup and expected output: DALEK_BENCHMARK.md in Strata-Boole.
#
#   --dalek-lite     the dalek-lite checkout (a sibling of the Verus fork)
#   --strata-boole   the Strata-Boole checkout the Lean file is written into and built in
#   --verus-bin      the Verus fork's release dir, providing `cargo-verus`
#   --no-lean        stop after the Boole program
#   --lean-only      skip the cvc5 check (Level 2); a Level 3 failure is then ambiguous
#
# Steps: (1) copy the module into the crate; (2) Verus verifies it and exports JSON;
# (3) verus-lean translates; (4) gen_lean.py wraps the program and Strata-Boole builds it,
# once to record cvc5's verdicts and once for the final file.
#
# Translator flags used in step 3 (u8 is bv8 and nat is Boole's nat without any flag):
#   --only <fn>                 keep what <fn> needs; other functions become contract stubs
#   --drop-proof-hints          no Verus lemma calls or ghost code; asserts are kept
#   --values-invariants         an invariant f(a) == f(b), f a mod reduction, becomes a == b
#   --literal-consts-as-axioms  Scalar::ZERO as a constant with length and element axioms
#   --index-by-prefix           f(subrange(s, 0, k)) becomes f(s, k)
#   --total-select              [T; N] reads are total (select!), so no length facts
#   --short-names               last path segment as the name
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

HERE=$(cd "$(dirname "$0")" && pwd)                          # <verus-boole>/dalek
VERUS_LEAN=$HERE/../.lake/build/bin/verus-lean
JSON_DIR=$HERE/export_json
OUT=$HERE/out/$FN.boole.st
MODULE=$(basename "$RUST" .rs)
# Modules whose spec functions / operator impls the contract reaches (dalek-lite layout).
EXTRA_MODULES=${EXTRA_MODULES:-"scalar specs::scalar_specs specs::core_specs specs::scalar52_specs"}
[ -n "$LEAN_OUT" ] || LEAN_OUT=$STRATA_BOOLE/StrataBooleTest/dalek_${FN}.lean

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
"$VERUS_LEAN" boole --only "$FN" --drop-proof-hints --values-invariants --literal-consts-as-axioms --index-by-prefix --total-select --short-names "$JSON_DIR" "$OUT" 2> "$HERE/out/$FN.translate.log"
echo "wrote $OUT ($(wc -l < "$OUT" | tr -d ' ') lines)"
# The entry procedure must be there and must have its real body.  A contract stub
# (`{ assume false; }`) in its place would make every obligation pass vacuously.
awk -v fn="$FN" '
  $0 ~ ("^procedure ([A-Za-z0-9_]*_)?" fn " *[(]") { seen = 1; inside = 1; next }
  inside && /^(procedure|function|rec function|axiom|type|datatype|const|var) / { inside = 0 }
  inside && /assume false/ { stub = 1 }
  END { if (!seen) exit 2; if (stub) exit 3; exit 0 }' "$OUT" || {
  case $? in
    2) echo "ERROR: no entry procedure '$FN' in $OUT" >&2 ;;
    *) echo "ERROR: the entry procedure '$FN' is a stub (assume false), not its body" >&2 ;;
  esac
  exit 1; }

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
  echo "Lean: $MOD builds: every obligation checked by the Lean kernel"
else
  echo "Lean: $MOD FAILED; see $HERE/out/$FN.lean.log"; grep -n "^error" "$HERE/out/$FN.lean.log" | head -5; exit 1
fi
