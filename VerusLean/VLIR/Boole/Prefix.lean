/-
  Boole.Prefix — `--index-by-prefix`: re-index a recursive spec function that
  recurses on `subrange(s, 0, len(s) - 1)` by the prefix length.

  Verus writes a fold over a sequence as
  `f(s) = … f(s.subrange(0, s.len() - 1)) … s[s.len() - 1] …`, and a caller
  that talks about a prefix writes `f(s.subrange(0, k))`.  Every such call is a
  fresh sequence term, and relating two of them
  (`sub.subrange(0, i) =~= s.subrange(0, i)`) needs sequence extensionality,
  which Strata's Sequence theory does not have and which Verus itself has to be
  told with `assert … =~= …` hints.

  The same function indexed by the prefix length,
  `f(s, n) = … f(s, n - 1) … s[n - 1] …`, reads `s[0..n)` only, so
  `f(s.subrange(0, k)) = f(s, k)` and `f(s) = f(s, len(s))`, and no sequence
  equality is needed anywhere.  The pass
    * adds a parameter `n : nat` with `recommends n <= len(s)`, replaces `len(s)`
      by `n` in the body and the `decreases` measure, and turns the recursive
      call `f(subrange(s, 0, k))` into `f(s, k)`;
    * rewrites every other call: `f(subrange(e, 0, k))` → `f(e, k)`,
      `f(e)` → `f(e, len(e))`;
    * drops `assert a =~= b` on sequences from exec bodies (the extensionality
      hints, now without a purpose).
  A function qualifies only if its body uses `s` as `len(s)`, `s[_]`, and the
  recursive `subrange(s, 0, _)` argument — that is what makes `f(s, n)` depend
  on `s[0..n)` alone, and the call rewrite valid.
-/
import VerusLean.VLIR.Defs
import VerusLean.VLIR.Boole.Names
import VerusLean.VLIR.Boole.TraitResolve
import VerusLean.VLIR.Boole.Strengthen
import VerusLean.VLIR.Boole.Hints

namespace VerusLean.Boole.Prefix

open VerusLean
open VerusLean.Boole.Names

def seqLen : Ident := `Vstd.Seq.len
def seqIndex : Ident := `Vstd.Seq.index
def seqSubrange : Ident := `Vstd.Seq.subrange

def isZeroConst : Exp → Bool
  | .Const (.Int c) _ => c == 0
  | _ => false

/-- `subrange(e, 0, k)` → `(e, k)` (`k` as written, with its casts). -/
def prefixOf? (e : Exp) : Option (Exp × Exp) :=
  match Strengthen.stripBox e with
  | .Call (.Fun fn) _ [base, lo, k] =>
    if fn == seqSubrange && isZeroConst (Strengthen.stripBox lo) then some (base, k) else none
  | _ => none

/-- The prefix length as an integer argument: `k as int` unless already a
    mathematical cast (the new parameter is a `nat`, whatever `k`'s source
    type; the explicit cast also tells the `usize` classifier the slot is
    integer, not bit-vector). -/
def asIntArg (k : Exp) : Exp :=
  match k with
  | .Unary (.Box _) (.Unary (.Clip .Int _) _) | .Unary (.Clip .Int _) _
  | .Unary (.Box _) (.Unary (.Clip .Nat _) _) | .Unary (.Clip .Nat _) _ => k
  | _ => .Unary (.Clip .Int false) k

def isSeqTyp : Typ → Bool
  | .Struct n _ => n == `Vstd.Seq
  | _ => false

/-- A qualifying function: its name, the sequence parameter and its position. -/
structure Cand where
  name : Ident
  sName : String
  sIdx : Nat
  arity : Nat
  nName : String

/-- Argument lists of the recursive self-calls of `g` in an expression. -/
partial def recCallArgs (g : Ident) : Exp → List (List Exp)
  | .Call fn _ exps =>
    let here := match fn with | .Recursive h => if h == g then [exps] else [] | _ => []
    here ++ exps.flatMap (recCallArgs g)
  | .CallLambda body args => recCallArgs g body ++ args.flatMap (recCallArgs g)
  | .StructCtor _ fields => fields.flatMap (fun (_, e) => recCallArgs g e)
  | .EnumCtor _ _ fields => fields.flatMap (fun (_, e) => recCallArgs g e)
  | .TupleCtor _ data => data.flatMap (recCallArgs g)
  | .Unary _ e => recCallArgs g e
  | .Binary _ a b => recCallArgs g a ++ recCallArgs g b
  | .If c t f => recCallArgs g c ++ recCallArgs g t ++ recCallArgs g f
  | .Bind bind body =>
    let bindArgs := match bind with
      | .Let _ _ rhs => recCallArgs g rhs
      | .Quant _ _ trigs => trigs.flatMap (·.flatMap (recCallArgs g))
      | .Lambda _ => []
      | .Choose _ pred => recCallArgs g pred
    bindArgs ++ recCallArgs g body
  | .ArrayLiteral elems => elems.flatMap (recCallArgs g)
  | .MatchBlock (scrut, _) body => recCallArgs g scrut ++ recCallArgs g body
  | .Const _ _ | .Var _ => []

/-- The Seq parameter (name, position) that a recursive self-call passes as
    `subrange(s, 0, _)`. -/
private def recPrefixArg? (f : SpecFn) (body : Exp) : Option (String × Nat) :=
  (recCallArgs f.name body).findSome? fun args =>
    (args.zipIdx.findSome? fun (a, i) =>
      if i < f.inputs.length then
        match prefixOf? a with
        | some (.Var v, _) =>
          if v == f.inputs[i]!.1 && isSeqTyp f.inputs[i]!.2 then some (v, i) else none
        | _ => none
      else none)

/-- After masking the allowed uses of `s` (`len(s)`, `s[_]`, the recursive
    `subrange(s, 0, _)`), nothing may still read `s`. -/
private def usesAreLenIndexPrefix (f : SpecFn) (s : String) (body : Exp) : Bool :=
  let masked := TraitResolve.mapExp (fun e =>
    match e with
    | .Call (.Fun fn) _ [.Var v] => if v == s && fn == seqLen then .Var "%len" else e
    | .Call (.Fun fn) t (.Var v :: rest) => if v == s && fn == seqIndex then .Call (.Fun fn) t (.Var "%idx" :: rest) else e
    | .Call (.Recursive g) t args =>
      if g == f.name then
        .Call (.Recursive g) t (args.map fun a => match prefixOf? a with
          | some (.Var v, k) => if v == s then k else a
          | _ => a)
      else e
    | e => e) body
  !(Hints.expReads masked).contains s

private def candOf? (f : SpecFn) : Option Cand := do
  let body ← f.body
  let (s, i) ← recPrefixArg? f body
  guard (usesAreLenIndexPrefix f s body)
  let taken := f.inputs.map (·.1)
  let n := if taken.contains "n" then "n_prefix" else "n"
  pure { name := f.name, sName := s, sIdx := i, arity := f.inputs.length, nName := n }

/-- Body/measure rewrite inside the function itself. -/
private def rewriteInside (c : Cand) : Exp → Exp := TraitResolve.mapExp fun e =>
  match e with
  | .Call (.Fun fn) _ [.Var v] => if v == c.sName && fn == seqLen then .Var c.nName else e
  | .Call (.Recursive g) t args =>
    if g == c.name then
      let main := args.take c.arity
      let tail := args.drop c.arity          -- Verus's fuel argument, if present
      let k? := main.findSome? fun a => match prefixOf? a with
        | some (.Var v, k) => if v == c.sName then some k else none
        | _ => none
      match k? with
      | some k =>
        let main' := main.map fun a => match prefixOf? a with
          | some (.Var v, _) => if v == c.sName then .Var c.sName else a
          | _ => a
        .Call (.Recursive g) t (main' ++ [asIntArg k] ++ tail)
      | none => e
    else e
  | e => e

/-- Call-site rewrite everywhere else. -/
private def rewriteCalls (cs : List Cand) : Exp → Exp := TraitResolve.mapExp fun e =>
  match e with
  | .Call (.Fun g) t args =>
    match cs.find? (·.name == g) with
    | some c =>
      if args.length == c.arity then
        let a := args[c.sIdx]!
        match prefixOf? a with
        | some (base, k) => .Call (.Fun g) t (args.set c.sIdx base ++ [asIntArg k])
        | none => .Call (.Fun g) t (args ++ [.Call (.Fun seqLen) [] [Strengthen.stripBox a]])
      else e
    | none => e
  | e => e

private def isExtEq (e : Exp) : Bool :=
  match Strengthen.stripBox e with
  | .Binary (.ExtEq _ _) _ _ => true
  | _ => false

/-- Locals that hold an `a =~= b` value (`tmp := a =~= b; assert tmp` is how
    the SST spells `assert(a =~= b)`). -/
private partial def extEqTemps : Stm → List String
  | .Assign (.Var v) _ rhs _ => if isExtEq rhs then [v] else []
  | .Block ss => ss.flatMap extEqTemps
  | .If _ b1 b2 => extEqTemps b1 ++ (b2.map extEqTemps).getD []
  | .Loop _ _ _ body _ _ => extEqTemps body
  | .DeadEnd s | .OpenInvariant s | .ClosureInner s | .AssertQuery _ s => extEqTemps s
  | _ => []

/-- `assert(a =~= b)` reaches the SST as `tmp := a =~= b; assert tmp; assume tmp`. -/
private def isExtEqAssert (temps : List String) : Stm → Bool
  | .Assert e | .Assume e => isExtEq e || (match e with | .Var v => temps.contains v | _ => false)
  | _ => false

private def dropExtEqAsserts (body : Stm) : Stm :=
  (Hints.filterStm (isExtEqAssert (extEqTemps body)) body).getD (.Block [])

private def reindex (c : Cand) (f : SpecFn) : SpecFn :=
  let lenS : Exp := .Call (.Fun seqLen) [] [.Var c.sName]
  { f with
    inputs := f.inputs ++ [(c.nName, .Nat)]
    body := f.body.map (rewriteInside c)
    decreases := f.decreases.map (TraitResolve.mapStm (rewriteInside c))
    recommends := f.recommends ++ [.Binary (.Inequality .Le) (.Var c.nName) lenS] }

partial def indexByPrefix (decls : List Decl) : List Decl :=
  let rec cands : Decl → List Cand
    | .specFn f => (candOf? f).toList
    | .mutualBlock ds => ds.flatMap cands
    | _ => []
  let cs := decls.flatMap cands
  if cs.isEmpty then decls else
  let rec onDecl : Decl → Decl
    | .specFn f =>
      match cs.find? (·.name == f.name) with
      | some c => .specFn (reindex c f)
      | none => .specFn f
    | .mutualBlock ds => .mutualBlock (ds.map onDecl)
    | d => d
  decls.map fun d =>
    let d := onDecl d
    let d := TraitResolve.mapDecl (rewriteCalls cs) d
    match d with
    | .execFn f => .execFn { f with body := dropExtEqAsserts f.body }
    | .proofFn f => .proofFn { f with body := f.body.map dropExtEqAsserts }
    | d => d

end VerusLean.Boole.Prefix
