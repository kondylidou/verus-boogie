# Changes of 2026-09-07/08 (Strata-Boole `lean_smt` integration) — what is real, what is a patch

Context: make `verus-lean boole` produce, from the dalek-lite export, a Boole program for
`Scalar::sum_of_slice` that Strata-Boole (branch `lean_smt`) loads and verifies.  Driver:
`dalek/rust_to_boole.sh` (Rust input in `dalek/input/`, exports in `dalek/export_json/`, output
in `dalek/out/`; `dalek/gen_lean.py` wraps the output into a three-level Strata-Boole file).
Status (2026-09-09): with all flags (now also `--index-by-prefix`, `--total-select`) the program is
114 lines and has the hand-written benchmark's shape: `sum_of_scalars(scalars, n)` on a prefix
length, no extensionality assert/assume pairs, no temps, the loop body is the one `Scalar_add`
call, ZERO's lemma as axioms, `Scalar_wf` (length + byte range) as the typing predicate, spec fns
without synthesized `requires`, no destructor (`s`, not `Scalar..bytes(s)`), ℓ folded to one
literal.  cvc5 38/38 (hand-written file: 24).  Lean (lean-smt): all 38 obligations replayed;
Level 3 is `all_goals (try smt (timeout := .some 2)); all_goals (inline_boole_defs; smt)` —
two goals (`scalar_as_nat(acc) < ℓ` from `is_canonical_scalar(acc)`, invariant and
postcondition) need a spec-fn body, everything else closes with the definitions opaque.
`dalek/rust_to_boole.sh dalek/input/scalar_helpers.rs --only sum_of_slice` runs end to end (3m17s:
Verus export, translation, cvc5 35/35 guard, Lean build of the generated file in 77 s incl. its cvc5
level).  Timing of the Lean module: hand file ~35 s, generated 77 s (single-pass inlining everywhere: 69 s;
plain `smt` on those two goals never returns — lean-smt runs cvc5 with `enum-inst` and no
timeout, so a definition-dependent goal with opaque definitions is a hang, not a failure).

Lesson (2026-09-08): an earlier "81/81" was vacuous — the entry function itself had been emitted
as `{ assume false; }` (an imported bodiless copy from another module shard won the dedupe).
Always read the emitted body of the function under test before quoting a number.

Nothing below is committed yet.  The test suite (`tests/`) has NOT been re-run after the port.

## Genuine fixes and features — meant to stay

- **Port to current Strata-Boole / StrataDDM API** (`Builder.lean`, `Cast.lean`,
  `SupportEmit.lean`, `Translate.lean`, `Main.lean`): bit-vector types are `bv W8`-style
  constructors; statements and commands carry a metadata-annotation slot (`Builder.noMd`);
  `command_constdecl` lost its type-args argument; `command_constdef` handled in `cmdDeclName?`.
- **Struct field projection names** (`Names.projFieldNameOf`): a struct's single variant is named
  after the type's last path segment (`scalar.Scalar` → variant `Scalar`) while the datatype name
  keeps the module prefix (`Scalar_scalar`); the old check compared only the full name, so field
  reads were emitted as `Scalar_scalar..Scalar_scalar_Scalar_bytes` against a declared
  `Scalar_scalar..bytes`.
- **Command deduplication across module shards** (`Main.dedupeNamedCommands`, `cmdDeclName?`):
  a single `command_recfndefs` is now named; a recursive definition *with* a `decreases` measure
  (from its defining module) outranks an imported copy without one; the surviving copy is placed at
  the first occurrence so its `_unfold` axiom, emitted next to the dropped copy, still follows it.
- **Non-fatal declaration parsing** (`Parser.Decls.fromJson?`, `ParserState.skipped`): a declaration
  whose JSON the parser does not model is skipped with a warning instead of aborting the whole
  export.  Needed for whole-module exports (`scalar` contains constructs we do not translate).
- **Directory input** (`Main.collectJsonBundleFiles`): `verus-lean boole <dir>` loads every
  `*.json` in the directory, one Verus module export each.
- **`--only f,g`** (`Pruning.pruneToEntries`, `Main`): keep only declarations transitively
  reachable from the named functions; trait-method calls are resolved to their impls
  (`TraitResolve.resolveTraitSpecCalls`) *before* pruning so the impl, not the abstract trait
  method, is kept.  Matching is exact or `_<name>` suffix.
- **Length facts for sequence elements** (`Translate.componentLenFacts`, `seqElemTyp?`): the
  synthesized fixed-array length facts now also cover elements of slice/`Vec`/`Seq` bindings,
  quantified over the index (`∀ i_elem :: 0 <= i_elem < length(s) ==> …`).  `componentLenFacts`
  takes a `BuildM BExpr` thunk so the expression is rebuilt inside the quantifier scope (de Bruijn
  indices of parameter references stay right).  This closed the last two cvc5 obligations.
- **Dedupe rank**: a `{ assume false; }` body ranks below a real body, so an imported
  declaration of a function never shadows its definition (this was the vacuous-result bug).
- **`pow2`/`pow` constant folding** (`Fold.lean`, `TraitResolve.mapExp/mapStm/mapDecl`
  generalized to any expression rewrite): `pow2(252)` → literal, so `group_order` and every
  `mod group_order` are linear, and the byte sum reads `select(bytes, k) * 256^k`.
- **Extensional-equality asserts** (`stmToBoole`, `.Assert (ExtEq …)`): `assert a =~= b` on
  sequences lowers to the pointwise condition (same length, equal elements); the companion
  `assume a =~= b` still lowers to `a == b`.  Strata's Sequence theory has no extensionality
  axiom; this is one explicit instance of it per Verus assert.
- **Loop upper bound** (`Synth.upperBoundInvExp`): `i <= endExp` next to the existing `lo <= i`,
  so `i == len` is known after the loop.
- **Length invariants for wrapper-typed locals reassigned in a loop** (`lenInvs` uses
  `boundaryLenFacts`): `acc : Scalar` keeps `length(bytes(acc)) == 32` across the loop.
- **`--drop-proof-hints`** (`Hints.lean`): removes calls to proof functions and then, to a
  fixpoint, assignments to locals nothing reads (the ghost `let`s of a Verus `proof {}` block);
  `assert`/`assume` are kept.  For `sum_of_slice` the body shrinks to the code, the invariants and
  the three extensionality steps — the shape of the hand-written benchmark.  Verification of the
  no-hints output: pending (see status).
- **`subrange(s, 0, k)` → `Sequence.take(s, k)`** (`Translate`, `Seq_subrange`): one operation
  instead of `take(drop(s, 0), k - 0)`; fewer axiom instantiations, simpler Lean goals.
- **Strata-Boole (other repo, `StrataBoole/MetaVerifier.lean`)**: `inline_boole_defs` now keeps
  definitions whose body uses `%` opaque (`inline_boole_defs!` inlines them too) — lean-smt
  cannot replay cvc5's modular-arithmetic proofs, and goals that need such a definition only by
  congruence close with it opaque.
- **Strata-Boole (other repo, `StrataBoole/Verify.lean`)**: lowering for the polymorphic
  `Sequence.empty<T>()` (`.seq_empty _ ty`), which the grammar accepted but the verifier rejected.

- **`--index-by-prefix`** (`Prefix.lean`): a recursive spec fn whose self-call is on
  `subrange(s, 0, len(s) - 1)` and whose other uses of `s` are `len(s)`/`s[_]` gets a prefix-length
  parameter `n : nat` (`recommends n <= len(s)`): `len(s)` → `n`, `f(subrange(s, 0, k))` → `f(s, k)`
  in the body and the measure; every caller `f(subrange(e, 0, k))` → `f(e, k)` (`k as int`),
  `f(e)` → `f(e, len(e))`.  `assert a =~= b` (and its `assume` twin, via the `tmp := a =~= b`
  temp) are dropped: they existed only to relate subrange terms.  Semantics preserved because
  `f(s, n)` reads `s[0..n)` only.  On `sum_of_slice` this removes every sequence-equality step.
- **Closed lemmas as axioms** (`Hints.closedLemmaAxioms`, with `--drop-proof-hints`): a call to a
  proof fn with no parameters and no `requires` (e.g. `lemma_scalar_zero_properties()`) keeps each
  `ensures` as an axiom `<lemma>_ensures_k` (a `Decl.assertion`; `Translate` now lowers closed
  assertions to `axiom`, `Pruning` keeps an assertion whose references are kept).  Same trust as a
  callee's contract stub.
- **Wrapper typing predicate `<T>_wf`** (`Translate`, struct pass): `Scalar_wf(s) == length == 32 &&
  ∀ k. 0 <= bytes[k] < 256`, used wherever a binding of the wrapper type needs its facts
  (`componentLenFacts`), instead of repeating the length fact.  Declared uninterpreted with a defining
  axiom `<T>_wf_def`, not as a bodied function: Strata inlines bodied functions as SMT macros, and a
  macro with a `∀ k` inside, used under the `∀ i_elem` element fact, becomes a nested quantifier
  that cvc5 (after prenexing) fails to instantiate — two obligations came back `unknown` in 0.02 s
  (the hand-written file has the same nesting and passes only by SAT decision order;
  `--prenex-quant=none` proves both).  Opaque predicate + axiom is the Boogie/Dafny treatment.
- **`--total-select`** (`Translate.arraySelect`/`isFixedArrayOperand`/`selectFor`, `specFnParamLenElts`):
  a read of a fixed-size array `[T; N]` (`a[i]`, `a@[i]`, through a view, a box or a struct field)
  lowers to `Sequence.select!`, the total read — Verus checked the index against `N` statically —
  and spec fns then carry no synthesized length/range/wf `requires` (the facts still reach the
  solver through procedure contracts, invariants and `<T>_wf`).  Reason: each spec-fn `requires`
  turns every call site into a `_calls_` obligation; `sum_of_slice` had 83 of them (110 vs the
  hand file's 24), and each is a cvc5 run plus proof reconstruction on the Lean side.  Now 38.
  The `nat` requires of recursive spec fns stay (their measure needs them).
- **Literal arithmetic folding** (`Fold.foldArith`): closed `+`/`-`/`*` on literals becomes one
  literal, so `group_order` is the number ℓ and not `pow2(252) + 27742…` at every use.
- **No identity destructor** (`Translate.applyDtor`): the single-field wrapper lowered to a type
  synonym has no `<T>..field` function any more; its projection is the operand itself.
- **Strata-Boole (other repo, `StrataBoole/MetaVerifier.lean`), `inline_boole_defs` fix**: the
  `Meta.transform`-based zeta reduction stopped at the first definition it kept opaque
  (`group_canonical`, `%`), leaving every later definition opaque too — the reason
  `inline_boole_defs; smt` still failed on the two definition-dependent goals.  Now a hand-written
  reduction of the `let` chain.  Definitions with a deeply nested body (nesting depth > 16, the
  32-term byte sum) also stay opaque by default: inlined everywhere they make each `smt` call 2–4×
  slower; `inline_boole_defs!` inlines everything.
- **`--u8-as-int` range facts** (`u8RangeFacts`): `0 <= s[k] < 256` for `[u8; N]` arrays — direct
  params (`fixedArrayLenElts`), wrapper fields (in `<T>_wf`), literal constants.  Closes the gap
  listed under "partial" below.
- **Recursive-fn `_unfold` axiom guarded by the function's domain** (`recommends` + `nat` facts):
  `∀ params :: guard ==> f(params) == body`.  Verus's own definitional axiom is unconditional; the
  guard is sound (weaker) and stops the axiom from being instantiated into the negative range on the
  new prefix parameter.  NOTE: a program whose proof used the unfolding outside `recommends` would
  now fail — none in the tests as far as known; re-check when running `tests/`.
- **`usize` promotion through `as int`** (`IntPromotion.isMathCast`): an argument written
  `x as int`/`x as nat` to an opaque user call is int-safe, not a rejecting bv slot; the
  `sum_of_slice` loop index stayed `int` after the prefix rewrite put `i` into `sum_of_scalars(_, i)`.
- **`--short-names`** (`Main.shortenNames`, text-level after rendering): last path segment
  (`group_canonical`, `sum_of_slice`, type `Scalar`, `Scalar_ctor`, `Scalar..bytes`); trait-impl
  items and constants keep the owner prefix (`Scalar_add`, `Scalar_ZERO`); collisions stay long;
  derived labels (`_unfold`, `_lit_N`) follow.  Internal names are untouched, so library-shape
  recognition keeps working.
- **Layout** (`Emit.tidy`): one blank line between declarations, none inside; axioms glued to the
  declaration they follow (which also makes `pruneUnreferencedDecls` drop them with it); `requires`/
  `ensures`/`decreases`/`invariant` on their own indented lines; braces on their own lines.
- **Unreferenced-declaration pruning** (`Main.pruneUnreferencedDecls`, with `--only`): drops
  `type`/`function` blocks nothing else mentions (`Choice`, `CtOption`, `Scalar52`, `Seq_empty`).
- **Call-temp folding** (`Normalize.foldCallTemps`): `tmp7 := f(..); acc := tmp7` → `acc := f(..)`
  (Verus names call results `tmp%7`).
- **Loop bounds as one leading invariant** `lo <= i && i <= hi`; invariants printed in source order.

## Patches made for the presentation — revisit before relying on them

- **`--values-invariants`** (`Strengthen.lean`): a loop invariant that unfolds to `f(a) == f(b)`
  with `f` a `p mod M` reduction becomes `a == b`.  Sound (a stronger invariant) but a heuristic:
  it may fail to verify on other programs.  It is what removes all modular arithmetic from the
  Lean goals; lean-smt cannot replay cvc5's `mod` proofs (they go through the reals).
- **`--literal-consts-as-axioms`** (`Translate.declToBoole`, `.specFn`): a nullary spec fn whose
  body is a wrapper struct around a literal array is emitted uninterpreted with a length axiom and
  an element axiom.  Only the uniform-array case has been exercised.

- **`Flags.lean`: process-global toggles read through `unsafeBaseIO`** for `--u8-as-int` (and
  the other flags).  `Coercions` is pure and consulted from many sites, so the flags were not
  threaded through the config.  Proper fix: carry them in `SynthConfig`/`BuildCtx` and make
  `Coercions` take the config (or precompute the numeric-domain table once).
- **`--u8-as-int`**: removes width 8 from `supportedBvWidths`, so `u8` falls into the existing
  "unsupported width → int" paths; sequence literals of `u8` become `Sequence.of_int`; range facts
  for `[u8; N]` arrays and wrappers (above).  Missing: range facts on scalar `u8` bindings; exec-mode
  wrapping arithmetic on `u8` under the flag is untested.  Only exercised on `sum_of_slice`.
- ~~`--nat-as-int`~~ **removed (2026-09-23).**  The translator emits Boole's own `nat`
  (`Main.nativeNatNames`; the `prelude/Nat.boole.st` block is loaded for name registration only,
  never emitted — `Strata.Boole.verify` injects the binary-datatype library).  With Strata-Boole
  #14 (library as uninterpreted symbols + axioms) `sum_of_slice` verifies 43/43 at Level 2.
  Level 3 does not yet work on native `nat`: Strata's VC-to-Lean translation
  (`Strata/DL/SMT/Translate.lean`) has no datatype support — next Strata PR.  Until then the
  keynote file's Level 3 theorem cannot be regenerated.
- **`--index-by-prefix`** is a shape rewrite for one idiom (fold over `subrange(s, 0, len - 1)`);
  the `k as int` cast on the count and the dropping of `=~=` hints are tied to that idiom.
- **`--inline-spec-fns` (tried, not wired into the script): does not get single-line `all_goals smt`
  closure.** Emits shallow, `mod`-free, non-recursive spec fns as Boole `inline function`
  (`Translate.inlineSpecFn?`), so Strata substitutes them before cvc5/Lean ever see them — the
  hope was that this replaces the generated file's two-pass Level 3
  (`try smt; inline_boole_defs; smt`) with the hand file's one-liner.  Measured 2026-09-09: cvc5
  still 35/35 at the Boole level, but under lean-smt's solver config (`enum-inst`,
  `produce-proofs`, no timeout) 6 DIFFERENT goals get stuck (the loop-invariant-establishment and
  maintenance goals, not the two postcondition goals the two-pass form needs).  Inlining more just
  moves which goals are hard for lean-smt's specific instantiation strategy; it does not remove the
  underlying problem.  Left in the translator (flag exists, code builds) but not in
  `rust_to_boole.sh`'s flag list or `gen_lean.py`'s template — the two-pass Level 3 is what ships.
- **`stubNonEntries` (with `--only`)** turns every non-entry exec *and proof* function into a
  contract stub (`{ assume false; }`).  For exec callees this is modular verification; for proof
  functions it means their statements are assumed, not proved.  Should become an explicit option
  (`--stub-callees`, `--assume-lemmas`) or at least be printed as a summary.
- **`pruneToEntries` keeps every `struct`/`enum`** (no type reachability) and drops all
  module-level `assertion`s.
- **`decreases` on imported recursive spec fns** depends on the *defining* module being exported
  (the Verus export gives imported copies `termination_check: null`).  The pipeline exports the
  spec modules for that reason; the translator does not synthesize a measure.
- **Outside this repo, dalek-lite working tree:** `curve25519-dalek/Cargo.toml` points
  `vstd`/`verus_builtin`/`verus_builtin_macros` at the local Verus fork by path; four `;` added in
  `montgomery.rs` after `match` blocks inside `assert … by { }` (the fork's parser rejects a
  block-final `match`).  Not committed there either.

## Not done / next

- Re-run `tests/` and fix whatever the port and the new passes broke.
- Remove `unsafeBaseIO` (flags into the config).
- The extensional-equality lowering only handles `Seq`/slice/`Vec` (via `seqElemTyp?`); sets and
  maps still lower `=~=` to `==`.
- `rust_to_boole.sh` builds the `#guard_msgs` block itself (Level-2-only build, then the real file).
- A `--stub-callees`/`--assume-lemmas` split for `stubNonEntries`.
