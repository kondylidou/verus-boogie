# Boole backend: status and open items

Last updated 2026-10-01.

## Status

`dalek/rust_to_boole.sh` takes dalek-lite's `Scalar::sum_of_slice` from Rust to a checked
Lean file. Setup and expected output: `DALEK_BENCHMARK.md` in Strata-Boole.

- Boole program: 82 lines. `u8` is `bv8`, Verus `nat` is Boole's native `nat`, and the
  contract of `sum_of_slice` has the same clauses as the Verus source.
- cvc5: 36/36 obligations.
- Lean kernel: all 36. The 28 program goals by `inline_boole_defs; smt`; the 8 goals of
  Boole's nat library and lean-smt's bitvector side goals by hand (`dalek/gen_lean.py`).
- `tests/check_working_tests.sh`: 67 passed, 15 skipped (3 Strata gaps, 12 solver
  unknown), 0 failed.

## Where the output differs from the Verus source

Each of these is a flag the demo passes. None is on by default.

- `--only f`: every other exec and proof function becomes a stub (`assume false`). For a
  callee that is modular verification. For a lemma it means assumed, not proved, and
  nothing reports which lemmas were assumed.
- `--drop-proof-hints`: proof blocks are removed. A lemma with no parameters and no
  `requires` keeps its `ensures` as axioms.
- `--values-invariants`: an invariant `f(a) == f(b)`, with `f` a `mod` reduction, is
  strengthened to `a == b`. Sound, but a heuristic: it may not verify elsewhere.
- `--index-by-prefix`: a spec function recursing on `subrange(s, 0, len - 1)` gets a
  prefix-length parameter, and the `=~=` hints that existed for it are dropped.
- `--literal-consts-as-axioms`: `Scalar::ZERO` becomes a constant with a length axiom and
  an element axiom. Only a uniform array has been exercised.
- `--total-select`: reads of `[T; N]` are total and no `length == N` facts are emitted.
  This is a patch, see the first open item.
- `--short-names`: names only.

Also: the unfolding axiom of a recursive spec function is guarded by its `recommends`,
and a recursive spec function has a `decreases` only if its defining module was exported.

All of the above is verified on `sum_of_slice` only.

## Open

1. **Translate reads by mode, then delete `--total-select`.** In Verus a spec read
   (`Seq::index`) is total (`recommends` only) and an exec read (`array_index_get`) has
   `requires 0 <= i < N`. The translator emits a checked `select` for both by default
   (too strict for spec code, which is why it synthesizes `requires` on spec functions),
   and with the flag a total `select!` for both (too lax for exec code). Spec reads
   should be `select!` and exec reads `select`, with no flag.
2. Report what `--only` stubbed, or split it into separate choices for callees and lemmas.
3. `=~=` on sets and maps lowers to `==`. Whether to change this depends on how Strata
   ends up encoding them (native theories make `=~=` and `==` coincide).
4. The order of datatype declarations varies between runs for files with several
   datatypes (`matching`, `guide/datatypes`). Cause not yet found.
5. lean-smt cannot replay cvc5's real-arithmetic proofs (the `pos.fromInt` termination
   goals) and leaves `(b <= c) = !(c < b)` side goals for unsigned comparisons. Both are
   worked around by hand in the generated proof.
6. `--inline-spec-fns` exists but is unused and untested since the proof shape changed.
7. Rename the repository to `verus-boole`.

## Lesson

A pass count means nothing if the entry function was emitted as `assume false`. This
happened once (an "81/81" that was vacuous). `rust_to_boole.sh` now refuses to continue
if the entry procedure is missing or is a stub.
