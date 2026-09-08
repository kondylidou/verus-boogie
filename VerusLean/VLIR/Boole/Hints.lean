/-
  Boole.Hints — `--drop-proof-hints`: remove the Verus proof scaffolding from
  exec function bodies.

  A Verus `proof { … }` block reaches the SST as ordinary statements: ghost
  `let` bindings become assignments, lemma invocations become calls to proof
  functions.  For Boole these are hints for a different prover.  This pass
  removes (1) calls to proof functions and (2) assignments to locals that are
  then never read (to a fixpoint), and drops the corresponding local
  declarations.  `assert`/`assume` statements are kept: they are checked, and a
  Verus `assert a =~= b` is the one extensionality fact Strata's sequence theory
  cannot derive (see `stmToBoole`).
-/
import VerusLean.VLIR.Defs
import VerusLean.VLIR.Boole.Names
import VerusLean.VLIR.Boole.Locals
import VerusLean.VLIR.Boole.Pruning

namespace VerusLean.Boole.Hints

open VerusLean
open VerusLean.Boole.Names

/-- Names of the variables an expression reads. -/
partial def expReads : Exp → List String
  | .Const _ _ => []
  | .Var v => [v]
  | .Call _ _ exps => exps.flatMap expReads
  | .CallLambda body args => expReads body ++ args.flatMap expReads
  | .StructCtor _ fields => fields.flatMap (fun (_, e) => expReads e)
  | .EnumCtor _ _ fields => fields.flatMap (fun (_, e) => expReads e)
  | .TupleCtor _ data => data.flatMap expReads
  | .Unary _ e => expReads e
  | .Binary _ a b => expReads a ++ expReads b
  | .If c t f => expReads c ++ expReads t ++ expReads f
  | .Bind bind body =>
    let bindReads := match bind with
      | .Let _ _ rhs => expReads rhs
      | .Quant _ _ trigs => trigs.flatMap (·.flatMap expReads)
      | .Lambda _ => []
      | .Choose _ pred => expReads pred
    bindReads ++ expReads body
  | .ArrayLiteral elems => elems.flatMap expReads
  | .MatchBlock (scrut, _) body => expReads scrut ++ expReads body

private def lvalueReads : LValue → List String
  | .Var _ => []
  | .Proj base .. => lvalueReads base
  | .Proj' base _ _ => lvalueReads base
  | .Index base idx => lvalueReads base ++ expReads idx

/-- Names of the variables a statement reads (assignment targets excluded,
    except through projections/indices, which read the base). -/
partial def stmReads : Stm → List String
  | .Call _ _ args => args.flatMap expReads
  | .Assert e | .AssertCompute e | .AssertLean e | .Assume e => expReads e
  | .AssertBitVector reqs enss => reqs.flatMap expReads ++ enss.flatMap expReads
  | .AssertQuery _ body => stmReads body
  | .Assign lhs _ rhs _ =>
    (match lhs with | .Var _ => [] | l => lvalueReads l ++ (l.baseVar?.toList)) ++ expReads rhs
  | .DeadEnd s | .OpenInvariant s | .ClosureInner s => stmReads s
  | .Return e? => (e?.map expReads).getD []
  | .BreakOrContinue _ _ | .Reveal .. => []
  | .If c b1 b2 => expReads c ++ stmReads b1 ++ (b2.map stmReads).getD []
  | .Loop _ _ cond body invs decrease =>
    (match cond with | some (s, e) => stmReads s ++ expReads e | none => [])
      ++ stmReads body ++ invs.flatMap (fun i => expReads i.body) ++ decrease.flatMap expReads
  | .Block stms => stms.flatMap stmReads

/-- Remove statements for which `drop` holds, everywhere. -/
partial def filterStm (drop : Stm → Bool) : Stm → Option Stm
  | s =>
    if drop s then none else
    match s with
    | .Block stms => some (.Block (stms.filterMap (filterStm drop)))
    | .If c b1 b2 =>
      some (.If c ((filterStm drop b1).getD (.Block [])) (b2.bind (filterStm drop)))
    | .Loop isFor label cond body invs decrease =>
      some (.Loop isFor label cond ((filterStm drop body).getD (.Block [])) invs decrease)
    | .DeadEnd s => (filterStm drop s).map .DeadEnd
    | .OpenInvariant s => (filterStm drop s).map .OpenInvariant
    | .ClosureInner s => (filterStm drop s).map .ClosureInner
    | .AssertQuery mode body => (filterStm drop body).map (.AssertQuery mode)
    | s => some s

private def isLemmaCall (proofFns : List String) : Stm → Bool
  | .Call fn _ _ => proofFns.contains (identToBoole fn)
  | _ => false

/-- Assignments to a plain local that nothing reads (`keep` lists names that
    must survive: parameters and the return variable). -/
private def isDeadStore (reads keep : List String) : Stm → Bool
  | .Assign (.Var v) _ _ _ => !reads.contains v && !keep.contains v
  | _ => false

partial def dropHintsFromBody (proofFns keep : List String) (body : Stm) : Stm :=
  let body := (filterStm (isLemmaCall proofFns) body).getD (.Block [])
  let rec dead (fuel : Nat) (b : Stm) : Stm :=
    match fuel with
    | 0 => b
    | fuel + 1 =>
      let reads := stmReads b
      let b' := (filterStm (isDeadStore reads keep) b).getD (.Block [])
      if reprStr b' == reprStr b then b else dead fuel b'
  dead 64 body

/-- Apply to every exec function; `proofFns` are the Boole names of the
    program's proof functions. -/
def dropProofHints (proofFns : List String) (decls : List Decl) : List Decl :=
  decls.map fun d =>
    match d with
    | .execFn f =>
      let keep := f.retName :: f.inputs.map (·.1)
      let body := dropHintsFromBody proofFns keep f.body
      let assigned := (Locals.collectSetVars body).map (·.name)
      let reads := stmReads body
      let locals := f.locals.filter (fun l => assigned.contains l.name || reads.contains l.name)
      let f' : ExecFn := { f with body := body, locals := locals }
      .execFn f'
    | d => d

/-- A call to a proof function with no parameters and no `requires` is a
    closed fact: its `ensures` hold outright (Verus proved the lemma).  Dropping
    the call would lose them, so each ensures clause becomes an assertion
    (an axiom `<lemma>_ensures_k` in Boole) — the same trust as a callee's
    contract stub.  Only lemmas some exec body calls are kept; each assertion is
    placed after the last declaration it refers to. -/
def closedLemmaAxioms (decls : List Decl) : List Decl :=
  let called : List String := decls.flatMap fun d => match d with
    | .execFn f => Pruning.stmCallRefs f.body
    | _ => []
  let axioms : List Decl := decls.flatMap fun d => match d with
    | .proofFn f =>
      if f.inputs.isEmpty && f.requires.isEmpty && called.contains (identToBoole f.name) then
        f.ensures.zipIdx.filterMap fun (e, k) =>
          if (expReads e).isEmpty then
            some (.assertion { name := f.name.mapTail (· ++ s!"_ensures_{k}"), decls := [], body := e })
          else none
      else []
    | _ => []
  if axioms.isEmpty then decls else
  -- insert after the last referenced declaration
  let names : List (Option String) := decls.map Pruning.declName?
  let posOf := fun (r : String) => (names.zipIdx.filterMap fun (n?, i) => if n? == some r then some i else none).head?
  let withPos : List (Nat × Decl) := axioms.map fun a =>
    let refs := match a with | .assertion x => Pruning.expCallRefs x.body | _ => []
    ((refs.filterMap posOf).foldl max 0, a)
  (decls.zipIdx.flatMap fun (d, i) => d :: (withPos.filter (·.1 == i)).map (·.2))

end VerusLean.Boole.Hints
