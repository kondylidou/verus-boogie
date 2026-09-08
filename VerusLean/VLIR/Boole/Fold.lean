/-
  Boole.Fold — constant folding of vstd power functions.

  `vstd::arithmetic::power2::pow2(k)` and `power::pow(b, k)` with literal
  arguments are folded to the literal result.  Left as calls they reach the
  solver as uninterpreted symbols, so e.g. dalek's
  `group_order() = pow2(252) + …` is a symbolic modulus: every `mod` becomes
  nonlinear and every lemma precondition `0 < group_order()` unprovable.
  Verus itself evaluates these by computation (`lemma2_to64`, `pow2` unfolding).
-/
import VerusLean.VLIR.Defs
import VerusLean.VLIR.Boole.Names
import VerusLean.VLIR.Boole.TraitResolve

namespace VerusLean.Boole.Fold

open VerusLean
open VerusLean.Boole.Names

/-- The integer value of a closed arithmetic expression, if it is one. -/
partial def constInt? : Exp → Option Int
  | .Const (.Int i) _ => some i
  | .Unary (.Clip _ _) e => constInt? e
  | .Unary (.Box _) e => constInt? e
  | .Unary (.Unbox _) e => constInt? e
  | .Binary (.Arith .Add _) a b => do pure ((← constInt? a) + (← constInt? b))
  | .Binary (.Arith .Sub _) a b => do pure ((← constInt? a) - (← constInt? b))
  | .Binary (.Arith .Mul _) a b => do pure ((← constInt? a) * (← constInt? b))
  | _ => none

private def natLit (n : Int) : Exp := .Const (.Int n) .Nat

/-- Fold one call (post-order step). -/
def foldPow : Exp → Exp
  | e@(.Call (.Fun name) _ [k]) =>
    if identToBoole name == "Arithmetic_Power2_pow2" then
      match constInt? k with
      | some k => if k >= 0 && k <= 1024 then natLit ((2 : Int) ^ k.toNat) else e
      | none => e
    else e
  | e@(.Call (.Fun name) _ [b, k]) =>
    if identToBoole name == "Arithmetic_Power_pow" then
      match constInt? b, constInt? k with
      | some b, some k => if k >= 0 && k <= 1024 then natLit (b ^ k.toNat) else e
      | _, _ => e
    else e
  | e => e

/-- Fold closed `+`/`-`/`*` arithmetic on literals into one literal (post-order
    step, after `foldPow`): `pow2(252) + 27742…` becomes the single number ℓ.
    Only binary arithmetic nodes are folded, so a lone literal keeps its type. -/
def foldArith : Exp → Exp
  | e@(.Binary (.Arith .Add _) _ _) | e@(.Binary (.Arith .Sub _) _ _) | e@(.Binary (.Arith .Mul _) _ _) =>
    match constInt? e with
    | some v => .Const (.Int v) (if v >= 0 then .Nat else .Int)
    | none => e
  | e => e

/-- Fold every literal `pow2`/`pow` call, and the literal arithmetic around it, in the program. -/
def foldPowCalls (decls : List Decl) : List Decl :=
  decls.map (TraitResolve.mapDecl (TraitResolve.mapExp (fun e => foldArith (foldPow e))))

end VerusLean.Boole.Fold
