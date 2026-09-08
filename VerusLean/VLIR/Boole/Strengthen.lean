/-
  Boole.Strengthen — `--values-invariants`: state congruence-shaped loop
  invariants as equalities of values.

  Verus proofs often phrase a loop invariant as a congruence through a
  reduction function, `canonical(acc) == canonical(sum)`, and discharge each
  step with modular-arithmetic lemmas.  When both sides are already reduced the
  stronger `acc == sum` also holds, and every step then closes by congruence
  alone — no `mod` reasoning, which is what the Lean (lean-smt) backend cannot
  replay.  This pass rewrites an invariant `f(a) == f(b)` — after unfolding the
  spec functions until both sides share their head — into `a == b`, provided
  the shared head `f` is a reduction: its body unfolds to `p mod M`.

  A heuristic: the stronger invariant may fail to verify (then the option
  should be dropped).  It never changes specifications, only loop invariants.
-/
import VerusLean.VLIR.Defs
import VerusLean.VLIR.Boole.Names
import VerusLean.VLIR.Boole.Normalize

namespace VerusLean.Boole.Strengthen

open VerusLean
open VerusLean.Boole.Names

abbrev SpecMap := Std.HashMap String SpecFn

def specFnMap (decls : List Decl) : SpecMap := Id.run do
  let mut m : SpecMap := {}
  let rec go (m : SpecMap) : Decl → SpecMap
    | .specFn f => m.insert (identToBoole f.name) f
    | .mutualBlock ds => ds.foldl go m
    | _ => m
  for d in decls do m := go m d
  return m

/-- One unfolding of a spec-function call whose definition is known. -/
def unfoldCall (m : SpecMap) : Exp → Option Exp
  | .Call (.Fun f) _ args =>
    match m.get? (identToBoole f) with
    | some sf =>
      match sf.body with
      | some body => if sf.inputs.length == args.length then some (Normalize.substExps (sf.inputs.map (·.1) |>.zip args) body) else none
      | none => none
    | none => none
  | _ => none

/-- Drop the coercion/annotation wrappers the SST puts around expressions. -/
partial def stripBox : Exp → Exp
  | .Unary (.Box _) e => stripBox e
  | .Unary (.Unbox _) e => stripBox e
  | .Unary (.Clip _ _) e => stripBox e
  | .Unary .Trigger e => stripBox e
  | e => e

/-- `f` is a reduction `p ↦ p mod M` (possibly through wrapper spec fns). -/
partial def isModReduction (m : SpecMap) (fuel : Nat) (f : Ident) : Bool :=
  match fuel, m.get? (identToBoole f) with
  | 0, _ => false
  | _, none => false
  | fuel + 1, some sf =>
    match sf.inputs, sf.body with
    | [(p, _)], some body =>
      match stripBox body with
      | .Binary (.Arith .EuclideanMod _) x _ => stripBox x == .Var p
      | .Call (.Fun g) _ [x] => stripBox x == .Var p && isModReduction m fuel g
      | _ => false
    | _, _ => false

/-- Unfold either side until both are `g(x)`, `g(y)` for the same `g`. -/
partial def toSameHead (m : SpecMap) (fuel : Nat) (l r : Exp) : Option (Ident × Exp × Exp) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match stripBox l, stripBox r with
    | .Call (.Fun g) _ [x], .Call (.Fun g') _ [y] =>
      if identToBoole g == identToBoole g' then some (g, x, y)
      else
        -- unfold the left head first, then the right
        (unfoldCall m (stripBox l)).bind (fun l' => toSameHead m fuel l' r)
        <|> (unfoldCall m (stripBox r)).bind (fun r' => toSameHead m fuel l r')
    | _, _ =>
      (unfoldCall m (stripBox l)).bind (fun l' => toSameHead m fuel l' r)
      <|> (unfoldCall m (stripBox r)).bind (fun r' => toSameHead m fuel l r')

/-- Match `pat` (with hole `Var p`) against `e`; the value bound to the hole. -/
partial def matchOne (p : String) : Exp → Exp → Option Exp
  | .Var v, e => if v == p then some e else (if e == .Var v then none else none)
  | .Call f1 t1 a1, .Call f2 t2 a2 =>
    if f1 == f2 && t1 == t2 && a1.length == a2.length then
      (a1.zip a2).foldl (fun acc (x, y) => match acc, matchOne p x y with
        | some b, some b' => if b == b' then some b else none
        | none, r => r
        | some b, none => if x == y then some b else none) none
    else none
  | .Unary o1 e1, .Unary o2 e2 => if o1 == o2 then matchOne p e1 e2 else none
  | .Binary o1 a1 b1, .Binary o2 a2 b2 =>
    if o1 == o2 then
      match matchOne p a1 a2, matchOne p b1 b2 with
      | some x, some y => if x == y then some x else none
      | some x, none => if b1 == b2 then some x else none
      | none, some y => if a1 == a2 then some y else none
      | none, none => none
    else none
  | _, _ => none

/-- Re-express `x` as `h(arg)` for a single-parameter spec fn `h` whose body
    is exactly `x` with the parameter in place of `arg` (cosmetic:
    `u8_32_as_nat(bytes(acc))` → `scalar_as_nat(acc)`). -/
def refold (m : SpecMap) (x : Exp) : Exp := Id.run do
  for (_, sf) in m.toList do
    match sf.inputs, sf.body with
    | [(p, _)], some body =>
      if body != .Var p then
        match matchOne p (stripBox body) (stripBox x) with
        | some arg => return .Call (.Fun sf.name) [] [arg]
        | none => pure ()
    | _, _ => pure ()
  return x

partial def strengthenInv (m : SpecMap) (fuel : Nat) (e : Exp) : Exp :=
  match fuel with
  | 0 => e
  | fuel + 1 =>
    match e with
    | .Binary (.Eq md) l r =>
      match toSameHead m 6 l r with
      | some (g, x, y) => if isModReduction m 6 g then .Binary (.Eq md) (refold m x) (refold m y) else e
      | none => e
    | .Call (.Fun _) _ _ =>
      match unfoldCall m e with
      | some e' =>
        match stripBox e' with
        | .Binary (.Eq _) _ _ => let s := strengthenInv m fuel (stripBox e'); if s == stripBox e' then e else s
        | _ => e
      | none => e
    | _ => e

/-- Debug: constructor/head of an expression (three levels). -/
def headStr1 : Exp → String
  | .Const c _ => s!"Const {repr c}"
  | .StructCtor dt _ => s!"StructCtor {identToBoole dt}"
  | .ArrayLiteral elems => s!"ArrayLiteral/{elems.length}"
  | .Call (.Fun f) _ _ => s!"Call {identToBoole f}"
  | .Unary op _ => s!"Unary {repr op}"
  | .Var v => s!"Var {v}"
  | .Binary op _ _ => s!"Binary {repr op}"
  | .Bind _ _ => "Bind"
  | .If .. => "If"
  | _ => "other"

def headStr0 : Exp → String
  | .StructCtor dt _ => s!"StructCtor {identToBoole dt}"
  | .ArrayLiteral elems => s!"ArrayLiteral/{elems.length} [{(elems.head?.map headStr1).getD ""}]"
  | .Const c _ => s!"Const {repr c}"
  | .Call (.Fun f) _ args => s!"Call {identToBoole f}({String.intercalate "," (args.map headStr1)})"
  | .Unary op e => s!"Unary {repr op} [{headStr1 e}]"
  | .Var v => s!"Var {v}"
  | .Binary op a b => s!"Binary {repr op} [{headStr1 a}] [{headStr1 b}]"
  | .Bind _ _ => "Bind"
  | .If .. => "If"
  | _ => "other"

def headStr : Exp → String
  | .StructCtor dt fields => s!"StructCtor {identToBoole dt} [{String.intercalate "," (fields.map fun (n, e) => n ++ ": " ++ headStr0 e)}]"
  | .ArrayLiteral elems => s!"ArrayLiteral/{elems.length} [{(elems.head?.map headStr0).getD ""}]"
  | .Call (.Fun f) _ args => s!"Call {identToBoole f}({String.intercalate "," (args.map headStr0)})"
  | .Call (.Recursive f) _ args => s!"RecCall {identToBoole f}/{args.length}"
  | .Binary op a b => s!"Binary {repr op} [{headStr0 a}] [{headStr0 b}]"
  | .Unary op e => s!"Unary {repr op} [{headStr0 e}]"
  | .Var v => s!"Var {v}"
  | .Bind _ _ => "Bind"
  | .If .. => "If"
  | _ => "other"

/-- Strengthen under the `let` bindings Verus wraps a loop invariant in
    (`let i = iter.cur; <invariant>`), and under coercion wrappers. -/
partial def strengthenDeep (m : SpecMap) : Exp → Exp
  | .Bind (.Let v ty rhs) body => .Bind (.Let v ty rhs) (strengthenDeep m body)
  | .Unary (.Box ty) e => .Unary (.Box ty) (strengthenDeep m e)
  | .Unary (.Unbox ty) e => .Unary (.Unbox ty) (strengthenDeep m e)
  | .Unary .Trigger e => .Unary .Trigger (strengthenDeep m e)
  | e => strengthenInv m 4 e

partial def onLoops (m : SpecMap) : Stm → Stm
  | .Loop isFor label cond body invs decrease =>
    let invs := invs.map fun inv => { inv with body := strengthenDeep m inv.body }
    .Loop isFor label cond (onLoops m body) invs decrease
  | .Block ss => .Block (ss.map (onLoops m))
  | .If c b1 b2 => .If c (onLoops m b1) (b2.map (onLoops m))
  | .DeadEnd s => .DeadEnd (onLoops m s)
  | .OpenInvariant s => .OpenInvariant (onLoops m s)
  | .ClosureInner s => .ClosureInner (onLoops m s)
  | .AssertQuery mode s => .AssertQuery mode (onLoops m s)
  | s => s

def valuesInvariants (decls : List Decl) : List Decl :=
  let m := specFnMap decls
  decls.map fun d => match d with
    | .execFn f => .execFn { f with body := onLoops m f.body }
    | d => d

end VerusLean.Boole.Strengthen
