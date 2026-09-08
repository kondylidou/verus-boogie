/-
  Boole.TraitResolve — point spec-level trait-method calls at the concrete
  impl that implements them.

  An exec call to a trait method arrives already resolved (`resolved_method`
  names the impl).  The spec-level clauses an impl inherits from its trait —
  e.g. `impl&%13::mul`'s `requires mul_req(self, rhs)` — arrive with
  `resolved_method = null`, naming the abstract trait spec fn rather than the
  impl's.  Left that way, a caller sees an uninterpreted predicate, the
  impl's own spec fn (`Impl__12_mul_req`) is dropped as unreferenced, and the
  leftover generic vstd declarations fail SMT encoding.

  This pass rewrites such a call to the impl's spec fn, but only when the
  program contains exactly one impl of that method and the call's type
  arguments are all concrete — the same resolution Verus performs at compile
  time.  A method with two impls (ambiguous) or a call with open type
  parameters is left unchanged.  It runs before pruning, so the reference
  counts pruning consults already point at the impl: the impl's spec fn is
  kept, the abstract trait declaration dropped.
-/
import VerusLean.VLIR.Defs
import VerusLean.VLIR.Boole.Names
import VerusLean.VLIR.Boole.Reveal

namespace VerusLean.Boole.TraitResolve

open VerusLean
open VerusLean.Boole.Names

/-- The type names no type parameter. -/
def typIsConcrete (ty : Typ) : Bool := (Reveal.typTypeVars ty).isEmpty

/-- The `(trait method, impl name)` pair of a `TraitMethodImpl` decl. -/
private def declTraitImpl? : Decl → Option (Ident × Ident)
  | .specFn f => f.traitImplMethod?.map (·, f.name)
  | .execFn f => f.traitImplMethod?.map (·, f.name)
  | _ => none

/-- All `(method, impl)` pairs in the program, including inside
    `mutualBlock`s. -/
private partial def collectTraitImpls : List Decl → List (Ident × Ident)
  | [] => []
  | .mutualBlock ds :: rest => collectTraitImpls ds ++ collectTraitImpls rest
  | d :: rest => (declTraitImpl? d).toList ++ collectTraitImpls rest

/-- Map each trait method (by Boole name) to its unique impl in the program.
    A method with two or more distinct impls is omitted — the target would be
    ambiguous.  A repeated copy of the same impl does not count as a second
    one (Verus can split a program across several JSON files, so an impl may
    appear more than once). -/
def buildTraitImplMap (decls : List Decl) : Std.HashMap String Ident :=
  -- `none` marks a method with ≥ 2 distinct impls.
  let tallied : Std.HashMap String (Option Ident) :=
    (collectTraitImpls decls).foldl (init := {}) fun m (method, impl) =>
      let key := identToBoole method
      match m.get? key with
      | none => m.insert key (some impl)
      | some (some prev) =>
        if identToBoole prev == identToBoole impl then m else m.insert key none
      | some none => m
  Std.HashMap.ofList (tallied.toList.filterMap fun (k, v?) => v?.map (k, ·))

/-- Bottom-up rewrite of every subexpression by `post`. -/
partial def mapExp (post : Exp → Exp) : Exp → Exp
  | .Const c ty => post (.Const c ty)
  | .Var v => post (.Var v)
  | .Call fn typs exps => post (.Call fn typs (exps.map (mapExp post)))
  | .CallLambda body args => post (.CallLambda (mapExp post body) (args.map (mapExp post)))
  | .StructCtor n fields => post (.StructCtor n (fields.map fun (f, e) => (f, mapExp post e)))
  | .EnumCtor n v fields => post (.EnumCtor n v (fields.map fun (f, e) => (f, mapExp post e)))
  | .TupleCtor n data => post (.TupleCtor n (data.map (mapExp post)))
  | .Unary op e => post (.Unary op (mapExp post e))
  | .Binary op a b => post (.Binary op (mapExp post a) (mapExp post b))
  | .If c t f => post (.If (mapExp post c) (mapExp post t) (mapExp post f))
  | .Bind bind body =>
    let bind := match bind with
      | .Let v ty rhs => .Let v ty (mapExp post rhs)
      | .Quant q vars trigs => .Quant q vars (trigs.map (·.map (mapExp post)))
      | .Lambda vars => .Lambda vars
      | .Choose vars pred => .Choose vars (mapExp post pred)
    post (.Bind bind (mapExp post body))
  | .ArrayLiteral elems => post (.ArrayLiteral (elems.map (mapExp post)))
  | .MatchBlock (scrut, pat) body => post (.MatchBlock (mapExp post scrut, pat) (mapExp post body))

/-- The trait-call redirection, as a `mapExp` post-function. -/
private def resolveCall (m : Std.HashMap String Ident) : Exp → Exp
  | .Call (.Fun name) typs exps =>
    match m.get? (identToBoole name) with
    | some impl => if typs.all typIsConcrete then .Call (.Fun impl) typs exps else .Call (.Fun name) typs exps
    | none => .Call (.Fun name) typs exps
  | e => e

partial def rewriteExp (m : Std.HashMap String Ident) : Exp → Exp := mapExp (resolveCall m)

/-- `rewriteStm`/`mapStm`: an expression rewrite lifted over the expressions inside a statement. -/
partial def mapStm (rewriteExp : Exp → Exp) : Stm → Stm
  | .Call fn typArgs args => .Call fn typArgs (args.map rewriteExp)
  | .Assert e => .Assert (rewriteExp e)
  | .AssertBitVector reqs enss =>
    .AssertBitVector (reqs.map rewriteExp) (enss.map rewriteExp)
  | .AssertQuery mode body => .AssertQuery mode (mapStm rewriteExp body)
  | .AssertCompute e => .AssertCompute (rewriteExp e)
  | .AssertLean e => .AssertLean (rewriteExp e)
  | .Assume e => .Assume (rewriteExp e)
  | .Assign lhs lhsTy rhs lhsIsInit => .Assign lhs lhsTy (rewriteExp rhs) lhsIsInit
  | .DeadEnd s => .DeadEnd (mapStm rewriteExp s)
  | .Return e? => .Return (e?.map rewriteExp)
  | .BreakOrContinue label isBreak => .BreakOrContinue label isBreak
  | .If cond b1 b2 => .If (rewriteExp cond) (mapStm rewriteExp b1) (b2.map (mapStm rewriteExp))
  | .Loop isFor label cond body invs decrease =>
    let cond := cond.map fun (s, e) => (mapStm rewriteExp s, rewriteExp e)
    let invs := invs.map fun inv => { inv with body := rewriteExp inv.body }
    .Loop isFor label cond (mapStm rewriteExp body) invs (decrease.map rewriteExp)
  | .OpenInvariant s => .OpenInvariant (mapStm rewriteExp s)
  | .ClosureInner s => .ClosureInner (mapStm rewriteExp s)
  | .Block stms => .Block (stms.map (mapStm rewriteExp))
  | .Reveal fn fuel => .Reveal fn fuel

/-- An expression rewrite lifted over every expression a decl holds
    (body, spec clauses, recommends, decreases). -/
partial def mapDecl (rewriteExp : Exp → Exp) : Decl → Decl
  | .specFn f => .specFn { f with
      body := f.body.map rewriteExp
      decreases := f.decreases.map (mapStm rewriteExp)
      recommends := f.recommends.map rewriteExp }
  | .proofFn f => .proofFn { f with
      requires := f.requires.map rewriteExp
      ensures := f.ensures.map rewriteExp
      body := f.body.map (mapStm rewriteExp)
      decreases := f.decreases.map (mapStm rewriteExp) }
  | .execFn f => .execFn { f with
      requires := f.requires.map rewriteExp
      ensures := f.ensures.map rewriteExp
      body := mapStm rewriteExp f.body
      decreases := f.decreases.map (mapStm rewriteExp) }
  | .func f => .func { f with
      reqs := f.reqs.map rewriteExp
      postCondition := f.postCondition.map rewriteExp }
  | .mutualBlock ds => .mutualBlock (ds.map (mapDecl rewriteExp))
  | d => d

/-- Point every spec-level call to an abstract trait method — where the
    call's type arguments are concrete — at its unique impl.  No-op when the
    program declares no unambiguous trait-method impls. -/
def resolveTraitSpecCalls (decls : List Decl) : List Decl :=
  let m := buildTraitImplMap decls
  if m.isEmpty then decls else decls.map (mapDecl (rewriteExp m))

end VerusLean.Boole.TraitResolve
