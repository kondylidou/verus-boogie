/-
  Boole.Flags — process-wide encoding toggles set from the command line.

  Two lowering choices are needed by the Lean (lean-smt) backend, which has no
  bit-vector→int conversion and no uninterpreted `nat` prelude:

    --u8-as-int   model `u8` as `int` (with explicit `0 <= x < 256` facts on
                  the bindings the translator already annotates with length facts);
    --nat-as-int  model `nat` as `int` (no `nat` prelude, no `nat.toInt`/`nat.fromInt`).

  The numeric-domain classification (`Coercions`) is pure and consulted from
  hundreds of sites, so the toggles are process globals read through
  `unsafeBaseIO`.  They are set once, in `Main`, before any translation runs.
-/
namespace VerusLean.Boole.Flags

initialize u8AsIntRef : IO.Ref Bool ← IO.mkRef false
initialize natAsIntRef : IO.Ref Bool ← IO.mkRef false
/-- `--short-names`: emit the last path segment of every name (`group_canonical`
    instead of `Specs_Scalar52_specs_group_canonical`), except where two program
    names would collide (`ambiguousShortRef`, computed in `Main`) and for impl
    methods, which keep their module prefix (`Scalar_add`). -/
initialize shortNamesRef : IO.Ref Bool ← IO.mkRef false
initialize ambiguousShortRef : IO.Ref (List String) ← IO.mkRef []
/-- `--literal-consts-as-axioms`: see `Translate.declToBoole` (`.specFn`). -/
initialize literalConstsAsAxiomsRef : IO.Ref Bool ← IO.mkRef false
/-- `--total-select`: fixed-size array reads as `Sequence.select!`, no synthesized
    definedness `requires` on spec fns (see `Translate`). -/
initialize totalSelectRef : IO.Ref Bool ← IO.mkRef false
/-- `--inline-spec-fns`: shallow, `mod`-free, non-recursive spec fns as Boole `inline function`. -/
initialize inlineSpecFnsRef : IO.Ref Bool ← IO.mkRef false

private unsafe def u8AsIntImpl (_ : Unit) : Bool := unsafeBaseIO u8AsIntRef.get
private unsafe def natAsIntImpl (_ : Unit) : Bool := unsafeBaseIO natAsIntRef.get
private unsafe def shortNamesImpl (_ : Unit) : Bool := unsafeBaseIO shortNamesRef.get
private unsafe def ambiguousShortImpl (_ : Unit) : List String := unsafeBaseIO ambiguousShortRef.get
private unsafe def literalConstsAsAxiomsImpl (_ : Unit) : Bool := unsafeBaseIO literalConstsAsAxiomsRef.get
private unsafe def totalSelectImpl (_ : Unit) : Bool := unsafeBaseIO totalSelectRef.get
private unsafe def inlineSpecFnsImpl (_ : Unit) : Bool := unsafeBaseIO inlineSpecFnsRef.get

/-- `--u8-as-int` is on. -/
@[implemented_by u8AsIntImpl] opaque u8AsInt (_ : Unit) : Bool
/-- `--nat-as-int` is on. -/
@[implemented_by natAsIntImpl] opaque natAsInt (_ : Unit) : Bool
/-- `--short-names` is on. -/
@[implemented_by shortNamesImpl] opaque shortNames (_ : Unit) : Bool
/-- Short names that several program names share (kept long). -/
@[implemented_by ambiguousShortImpl] opaque ambiguousShort (_ : Unit) : List String
/-- `--literal-consts-as-axioms` is on. -/
@[implemented_by literalConstsAsAxiomsImpl] opaque literalConstsAsAxioms (_ : Unit) : Bool
/-- `--total-select` is on. -/
@[implemented_by totalSelectImpl] opaque totalSelect (_ : Unit) : Bool
/-- `--inline-spec-fns` is on. -/
@[implemented_by inlineSpecFnsImpl] opaque inlineSpecFns (_ : Unit) : Bool

end VerusLean.Boole.Flags
