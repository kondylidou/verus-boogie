#!/usr/bin/env python3
"""Wrap a translated Boole program into a Strata-Boole three-level benchmark file.

    gen_lean.py <fn> <input.rs> <program.boole.st> <out.lean>
                [--level2-only] [--guard <obligations.txt>] [--no-eval]

Level 1: the Verus function, verbatim from the input Rust module.
Level 2: the Boole program exactly as `verus-lean boole` produced it, under
         `#eval Strata.Boole.verify "cvc5"` (add the `#guard_msgs` block by building once).
         `--no-eval` drops this check entirely (Level 2 is just the program).  Level 2
         trusts cvc5 directly; Level 3 has the Lean kernel check a reconstructed proof.
         Without Level 2, a Level 3 failure can't tell you whether cvc5 couldn't prove the
         obligation or proved it but Lean couldn't replay it.
Level 3: the Lean theorem, every obligation closed by lean-smt.
"""
import re, sys

fn, rs_path, st_path, out_path = sys.argv[1:5]
opts = sys.argv[5:]
level2_only = "--level2-only" in opts
no_eval = "--no-eval" in opts
guard = open(opts[opts.index("--guard") + 1]).read().rstrip("\n") if "--guard" in opts else None
assert not (no_eval and guard), "--no-eval and --guard are mutually exclusive"
rs = open(rs_path).read().split("\n")
st = open(st_path).read().rstrip("\n")

# Verus source: the doc comment + attributes + `pub fn <fn>` … up to the closing
# brace at the function's own indentation.
start = next(i for i, l in enumerate(rs) if re.search(rf"\bfn {re.escape(fn)}\b", l))
indent = len(rs[start]) - len(rs[start].lstrip())
end = next(i for i in range(start + 1, len(rs)) if rs[i] == " " * indent + "}")
b = start
while b > 0 and (rs[b-1].strip().startswith("///") or rs[b-1].strip().startswith("#[")):
    b -= 1
src = "\n".join(l[indent:] if l.startswith(" " * indent) else l for l in rs[b:end+1])
assert "-/" not in src and "/-" not in src

# same name in the guard-only build and the final file: obligation ids carry byte offsets
seed = re.sub(r"[^A-Za-z0-9]", "", fn) + "TranslatedSeed"
guard_block = f"/-- info:\n{guard}\n-/\n#guard_msgs in\n" if guard else ""
eval_block = "" if no_eval else f'{guard_block}#eval Strata.Boole.verify "cvc5" {seed} (options := .quiet)\n'
level3 = "" if level2_only else f"""
-- Lean backend: every obligation is proved by cvc5 and the proof is replayed in the Lean
-- kernel (lean-smt).  Spec functions are opaque atoms to the solver here; the goals that
-- need a definition unfolded (e.g. scalar_as_nat(acc) < ℓ from is_canonical_scalar(acc))
-- get it from `inline_boole_defs` (the analogue of Verus's `reveal`) in a second pass.
set_option maxHeartbeats 1000000 in  -- one proof block for all obligations; the default budget is per declaration
example : Strata.smtVCsCorrectBoole {seed} := by
  gen_smt_vcs_boole
  all_goals (try smt (timeout := .some 2))
  all_goals (inline_boole_defs; smt)
"""
lean = f"""/-
  Copyright Strata Contributors
  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataBoole.MetaVerifier
import Smt

open Strata

/-
Benchmark: {fn} — translated by verus-lean from the Verus export of dalek-lite.

GENERATED FILE.  Produced by `verus-boogie/dalek/rust_to_boole.sh {fn}`:
  1. the Verus fork exports the VLIR of the crate modules the function reaches;
  2. `verus-lean boole --only {fn} --u8-as-int --drop-proof-hints
     --values-invariants --literal-consts-as-axioms --index-by-prefix --total-select --short-names`
     turns them into the Boole program below (callees as contract stubs, u8 and nat
     as int with their typing facts, no Verus proof hints, the recursive spec fn
     indexed by prefix length);
  3. this wrapper adds the Verus source and the two verification levels.
The hand-written counterpart is dalek_{fn}.lean.

Verus source (verbatim from the input Rust module):

{chr(10).join("  " + l if l else "" for l in src.split(chr(10)))}
-/

/-
Boole program, exactly as emitted by the translator.
-/
private def {seed} : StrataDDM.Program :=
#strata
{st}
#end

{eval_block}{level3}"""
open(out_path, "w").write(lean)
print(f"wrote {out_path}")
