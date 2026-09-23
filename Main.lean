import Lean
import VerusLean
import VerusLean.VLIR.Boole.Translate
import VerusLean.VLIR.Boole.Emit
import VerusLean.VLIR.Boole.Prelude
import VerusLean.VLIR.Boole.TraitResolve
import VerusLean.VLIR.Boole.Flags
import VerusLean.VLIR.Boole.Fold
import VerusLean.VLIR.Boole.Hints
import VerusLean.VLIR.Boole.Strengthen
import VerusLean.VLIR.Boole.Prefix

open VerusLean
open VerusLean.Boole

/-- Text preludes keep source comments for maintainability, but generated
    output files should stay concise. Drop standalone `// ...` lines before
    prepending the prelude text. -/
private def stripLineComments (text : String) : String :=
  String.intercalate "\n" <|
    (text.splitOn "\n").filter (fun line =>
      let trimmed := line.trimAscii.toString
      !trimmed.startsWith "//")

/-- Locate `prelude/<fileName>` by walking up from `start` (bounded), so the
    prelude is found whether `verus-lean` runs from the repo root or a subdir. -/
private def searchUpForPrelude
    (start : System.FilePath) (fileName : String) : IO (Option System.FilePath) := do
  let mut dir := start
  for _ in [0:16] do
    let cand := dir / "prelude" / fileName
    if ← cand.pathExists then
      return some cand
    match dir.parent with
    | some p => dir := p
    | none => return none
  return none

/-- Read a Boole prelude file.  Resolves `prelude/<fileName>` robustly — first by
    walking up from the current directory, then from the running binary's
    location — so a generated `.boole.st` is self-contained (the `nat` prelude it
    references is defined) regardless of the invocation cwd. -/
private def readPreludeBody? (fileName : String) : IO (Option String) := do
  let path? ←
    match ← searchUpForPrelude (← IO.currentDir) fileName with
    | some p => pure (some p)
    | none =>
      match (← IO.appPath).parent with
      | some binDir => searchUpForPrelude binDir fileName
      | none => pure none
  match path? with
  | some path =>
    let text ← IO.FS.readFile path
    pure <| some <| stripLineComments text
  | none =>
    pure none

private def readNatPreludeBody? : IO (Option String) :=
  readPreludeBody? "Nat.boole.st"

private def readSeqPreludeBody? : IO (Option String) :=
  readPreludeBody? "Seq.boole.st"

private def readVecPreludeBody? : IO (Option String) :=
  readPreludeBody? "Vec.boole.st"

/-- Render the translator's internal nat names (`nat.toInt`, `nat.add`, …, the
    declarations of `prelude/Nat.boole.st`) as Boole's native operator surface
    (`nat_toInt`, `nat_add`, …).  Token-exact: `nat.` is replaced only where it
    starts an identifier, so `xnat.add` or `Scalar_nat.x` are left alone. -/
private def nativeNatNames (text : String) : String := Id.run do
  let ops := ["toInt", "fromInt", "add", "sub", "mul", "div", "mod", "lt", "le", "gt", "ge"]
  let isIdChar := fun (c : Char) => c.isAlphanum || c == '_'
  let mut out := ""
  let mut i := 0
  let cs := text.toList.toArray
  while i < cs.size do
    let atIdentStart := i == 0 || !isIdChar cs[i-1]!
    let rest := String.mk (cs.extract i (min cs.size (i + 12))).toList
    match (if atIdentStart && rest.startsWith "nat." then
             ops.find? fun op => rest.startsWith s!"nat.{op}"
               && (i + 4 + op.length ≥ cs.size || !isIdChar cs[i + 4 + op.length]!)
           else none) with
    | some op =>
      out := out ++ s!"nat_{op}"
      i := i + 4 + op.length
    | none =>
      out := out.push cs[i]!
      i := i + 1
  return out

private def failWith (msg : String) : IO α :=
  throw <| IO.userError s!"Error: {msg}"

private def collectJsonBundleFiles (target : System.FilePath) : IO (List System.FilePath) := do
  -- A directory: every `*.json` in it is one shard (e.g. one Verus module export each).
  if ← target.isDir then
    let entries ← target.readDir
    let files := entries.foldl (init := ([] : List System.FilePath)) (fun acc e =>
      if e.fileName.endsWith ".json" then e.path :: acc else acc)
    return (files.toArray.qsort (fun a b => a.toString < b.toString)).toList
  match target.fileStem, target.extension with
  | some stem, some "json" => do
    let dir := target.parent.getD (System.FilePath.mk ".")
    let shardPrefix := s!"{stem}_"
    let entries ← dir.readDir
    let shards :=
      entries.foldl (init := ([] : List System.FilePath)) (fun acc entry =>
        if entry.fileName.startsWith shardPrefix && entry.fileName.endsWith ".json" then
          entry.path :: acc
        else
          acc)
    let sortedShards := (shards.toArray.qsort (fun a b => a.toString < b.toString)).toList
    pure (target :: sortedShards)
  | _, _ => pure [target]

/-- A procedure body that is exactly `{ assume false; }` — what a bodiless
    (declaration-only or stubbed) function lowers to.  Ranks below a real body,
    so an imported declaration of a function never shadows its definition. -/
private def isAssumeFalseBody (b : Option (Strata.BooleDDM.Block StrataDDM.SourceRange)) : Bool :=
  match b with
  | some (.block _ ⟨_, #[.assume _ _ _ (.bfalse _)]⟩) => true
  | _ => false

private def booleCommandRank (cmd : Boole.Builder.BCmd) : Nat :=
  match cmd with
  | .command_fndef .. => 2
  -- A recursive definition with a `decreases` measure (from the module that
  -- defines it) outranks an imported copy without one.
  | .command_recfndefs _ _ ⟨_, #[.recfn_decl _ _ _ _ _ _ decr _]⟩ => if decr.val.isSome then 3 else 2
  | .boole_procedure _ _ _ _ _ _ _ bodyAnn =>
    if bodyAnn.val.isSome && !isAssumeFalseBody bodyAnn.val then 2 else 1
  | .command_procedure _ _ _ _ _ _ bodyAnn =>
    if bodyAnn.val.isSome && !isAssumeFalseBody bodyAnn.val then 2 else 1
  | .command_typedecl .. => 2
  | .command_typesynonym .. => 2
  | .command_datatypes .. => 2
  | _ => 1

private def maxRankForName (cmds : List Boole.Builder.BCmd) (name : String) : Nat :=
  cmds.foldl (init := 0) fun acc cmd =>
    if Translate.cmdDeclName? cmd == some name then
      Nat.max acc (booleCommandRank cmd)
    else
      acc

/-- Module shards can contain both an imported declaration and the defining
    body for the same symbol. Keep one named command, preferring definitions
    over declarations, before building a Strata global context. -/
private def dedupeNamedCommands (cmds : Array Boole.Builder.BCmd) :
    Array Boole.Builder.BCmd := Id.run do
  -- Keep, for each name, the best-ranked command (first among ties), placed at
  -- the position of the name's first occurrence: axioms emitted next to an
  -- earlier (dropped) copy — e.g. a recursive function's `_unfold` axiom —
  -- then still follow the surviving declaration.
  let all := cmds.toList
  let mut best : Std.HashMap String Boole.Builder.BCmd := {}
  for cmd in all do
    if let some name := Translate.cmdDeclName? cmd then
      match best.get? name with
      | none => best := best.insert name cmd
      | some prev =>
        if booleCommandRank cmd > booleCommandRank prev then best := best.insert name cmd
  let mut seen : List String := []
  let mut out : Array Boole.Builder.BCmd := #[]
  for cmd in all do
    match Translate.cmdDeclName? cmd with
    | none => out := out.push cmd
    | some name =>
      if seen.contains name then pure ()
      else
        seen := name :: seen
        out := out.push (best.getD name cmd)
  return out

/-- Build the synthesized-aid toggle config from the `BOOLE_SYNTH_DISABLE`
    environment variable — a comma-separated list of `SynthConfig` field names
    to turn *off* (e.g. `fixedArrayLengths,loopLowerBound,seqMapPrecond`).
    Empty/unset means all aids on (the default).  Unknown names are ignored. -/
def synthConfigFromEnv : IO Context.SynthConfig := do
  let raw := (← IO.getEnv "BOOLE_SYNTH_DISABLE").getD ""
  let off := (raw.splitOn ",").map (·.trim) |>.filter (· != "")
  pure {
    fixedArrayLengths := !off.contains "fixedArrayLengths"
    loopLowerBound    := !off.contains "loopLowerBound"
    seqMapPrecond     := !off.contains "seqMapPrecond"
    recFnUnfold       := !off.contains "recFnUnfold"
  }


/-- `--short-names`: rename the program's own declarations in the rendered text
    to their last path segment (`Specs_Scalar52_specs_group_canonical` →
    `group_canonical`, type `Scalar_scalar` → `Scalar`, its constructor
    `Scalar_scalar_ctor` → `Scalar_ctor`, destructor `Scalar_scalar..bytes` →
    `Scalar..bytes`).  Impl-block items keep their module prefix (`Scalar_add`).
    A short name is skipped when two declarations would share it, or when it
    already occurs in the text.  Purely cosmetic: applied after rendering, so
    the translator's internal name-based recognition is untouched. -/
private def shortenNames (decls : List Decl) (text : String) : String := Id.run do
  let isIdChar := fun (c : Char) => c.isAlphanum || c == '_' || c == '\'' || c == '?' || c == '!'
  -- tokens of the text
  let mut toks : Array (String × Bool) := #[]   -- (token, isIdentifier)
  let mut cur := ""; let mut curId := false; let mut first := true
  for c in text.toList do
    let isId := isIdChar c
    if first then
      cur := c.toString
      curId := isId
      first := false
    else if isId == curId then
      cur := cur.push c
    else
      toks := toks.push (cur, curId)
      cur := c.toString
      curId := isId
  toks := toks.push (cur, curId)
  let present : Std.HashSet String := Std.HashSet.ofList (toks.toList.filterMap fun (s, b) => if b then some s else none)
  -- candidate renames from the declarations
  let fixCase := fun (s : String) =>   -- `zERO` (decapitalized const) → `ZERO`
    match s.toList with
    | c :: rest => if c.isLower && !rest.isEmpty && rest.all (fun d => d.isUpper || d.isDigit || d == '_') then (c.toUpper.toString ++ String.ofList rest) else s
    | [] => s
  -- (ident, isType, isTraitImpl): a trait-impl item keeps its owner prefix (`Scalar_add`)
  let rec idents : Decl → List (Ident × Bool × Bool)
    | .specFn f => [(f.name, false, f.traitImplMethod?.isSome)]
    | .proofFn f => [(f.name, false, false)]
    | .execFn f => [(f.name, false, f.traitImplMethod?.isSome)]
    | .func f => [(f.name, false, false)] | .struct s => [(s.name, true, false)] | .enum e => [(e.name, true, false)]
    | .mutualBlock ds => ds.flatMap idents | .assertion a => [(a.name, false, false)]
  let all := (decls.flatMap idents).eraseDups
  -- short names of the program's types: a function whose path goes through one
  -- of them is a method (`scalar::Scalar::add`) and keeps `<Type>_` as prefix.
  let typeShorts : List String := all.filterMap fun (i, isType, _) =>
    if isType then some (Boole.Names.lastSegmentName i |>.capitalize) else none
  let mut pairs : List (String × String) := []
  for (i, isType, isTraitImpl) in all do
    if isType then
      let long := Boole.Names.datatypeNameOf i
      let short := Boole.Names.lastSegmentName i |>.capitalize
      pairs := (long, short) :: (long ++ "_ctor", short ++ "_ctor") :: pairs
    else
      let long := Boole.Names.identToBooleLong i
      let segs := (i.toString.splitOn ".").map Boole.Names.sanitizeIdent
      let last := fixCase (segs.getLast!)
      -- Items of an impl block: a trait impl (`impl Add for Scalar`) or a constant
      -- (`Scalar::ZERO`) keeps the owner as prefix; an inherent method
      -- (`impl Scalar { fn sum_of_slice }`) is just its name.
      let isConstLike := last.any Char.isUpper && !(last.any Char.isLower)
      let short :=
        match Boole.Names.implOwnerSegment? i with
        | some owner =>
          if isTraitImpl || isConstLike then (Boole.Names.sanitizeIdent owner).capitalize ++ "_" ++ last else last
        | none =>
          match segs.reverse with
          | _ :: owner :: _ => if typeShorts.contains owner.capitalize then owner.capitalize ++ "_" ++ last else last
          | _ => last
      pairs := (long, short) :: (long ++ "_unfold", short ++ "_unfold") :: pairs
  let cands := pairs.filter fun (l, s) => l != s && present.contains l
  let ok := fun (l : String) (s : String) =>
    (cands.filter (fun p => p.2 == s)).length == 1 && !(present.contains s && l != s)
  let m : Std.HashMap String String := Std.HashMap.ofList (cands.filter (fun (l, s) => ok l s))
  -- derived tokens `<long>_unfold`, `<long>_lit_N`, `<long>_ret_len`, `<long>_nat`, `<type>_wf` follow their base name
  let derived := fun (tok : String) =>
    (cands.findSome? fun (l, s) =>
      if tok.startsWith (l ++ "_") && m.contains l then
        let rest := (tok.toSubstring.drop (l.length + 1)).toString
        if rest == "unfold" || rest == "ret_len" || rest == "nat" || rest == "wf" || rest == "wf_def" || rest.startsWith "lit_"
        then some (s ++ "_" ++ rest) else none
      else none).getD tok
  return String.join (toks.toList.map fun (s, b) => if b then (if m.contains s then m.getD s s else derived s) else s)


/-- Identifier tokens of a text (maximal runs of identifier characters). -/
private def identTokens (s : String) : List String := Id.run do
  let isIdChar := fun (c : Char) => c.isAlphanum || c == '_' || c == '\'' || c == '?' || c == '!'
  let mut out : Array String := #[]
  let mut cur := ""
  for c in s.toList do
    if isIdChar c then cur := cur.push c
    else if !cur.isEmpty then
      out := out.push cur
      cur := ""
  if !cur.isEmpty then out := out.push cur
  return out.toList

/-- With `--only`: drop top-level `type`/`function`/`rec function` declarations
    (never procedures or axioms) whose name occurs in no other declaration —
    support types and helpers that the kept declarations do not use.  Blocks are
    the blank-line-separated groups `Emit.tidy` produces.  Iterated to a fixpoint. -/
private def pruneUnreferencedDecls (text : String) : String := Id.run do
  let tokensOf := identTokens
  let declName? := fun (block : String) =>
    let l : String := (block.splitOn "\n").headD ""
    let rest : Option String :=
      if l.startsWith "rec function " then some ((l.toSubstring.drop 13).toString)
      else if l.startsWith "function " then some ((l.toSubstring.drop 9).toString)
      else if l.startsWith "type " then some ((l.toSubstring.drop 5).toString) else none
    match rest with
    | none => none
    | some r =>
      match tokensOf r with
      | n :: _ => some n
      | [] => none
  let mut blocks : List String := text.splitOn "\n\n"
  let mut changed := true
  let mut fuel := 50
  while changed && fuel > 0 do
    fuel := fuel - 1
    changed := false
    let named := blocks.map fun b => (b, declName? b)
    let mut keep : List String := []
    for (b, n?) in named do
      match n? with
      | none => keep := b :: keep
      | some n =>
        let usedElsewhere := named.any fun (b2, n2?) => b2 != b && n2? != some n && (tokensOf b2).contains n
        if usedElsewhere then keep := b :: keep else changed := true
    blocks := keep.reverse
  return String.intercalate "\n\n" blocks

/-- Command-line options of `verus-lean boole`. -/
structure CliOptions where
  /-- `--only f,g`: keep only declarations reachable from these functions. -/
  only : List String := []
  /-- `--u8-as-int`: model `u8` as `int` with explicit range facts. -/
  u8AsInt : Bool := false
  /-- `--drop-proof-hints`: remove Verus proof scaffolding (lemma calls, ghost
      bookkeeping) from exec bodies; `assert`/`assume` are kept. -/
  dropProofHints : Bool := false
  /-- `--short-names`: last path segment as the Boole name where unambiguous. -/
  shortNames : Bool := false
  /-- `--values-invariants`: congruence-shaped loop invariants `f(a) == f(b)` with
      `f` a `mod` reduction become `a == b` (see `Strengthen`). -/
  valuesInvariants : Bool := false
  /-- `--literal-consts-as-axioms`: nullary literal-array constants as uninterpreted + axioms. -/
  literalConstsAsAxioms : Bool := false
  /-- `--index-by-prefix`: a recursive spec fn over `subrange(s, 0, len - 1)` is
      re-indexed by the prefix length (see `Prefix`). -/
  indexByPrefix : Bool := false
  /-- `--total-select`: fixed-size array reads as `Sequence.select!`; no synthesized
      definedness `requires` on spec fns. -/
  totalSelect : Bool := false
  /-- `--inline-spec-fns`: shallow, `mod`-free, non-recursive spec fns as `inline function`. -/
  inlineSpecFns : Bool := false

private def parseCli : List String → Except String (CliOptions × List String)
  | "--only" :: names :: rest => do
    let (o, pos) ← parseCli rest
    pure ({ o with only := o.only ++ (names.splitOn ",").filter (· != "") }, pos)
  | "--u8-as-int" :: rest => do
    let (o, pos) ← parseCli rest; pure ({ o with u8AsInt := true }, pos)
  | "--drop-proof-hints" :: rest => do
    let (o, pos) ← parseCli rest; pure ({ o with dropProofHints := true }, pos)
  | "--short-names" :: rest => do
    let (o, pos) ← parseCli rest; pure ({ o with shortNames := true }, pos)
  | "--values-invariants" :: rest => do
    let (o, pos) ← parseCli rest; pure ({ o with valuesInvariants := true }, pos)
  | "--literal-consts-as-axioms" :: rest => do
    let (o, pos) ← parseCli rest; pure ({ o with literalConstsAsAxioms := true }, pos)
  | "--index-by-prefix" :: rest => do
    let (o, pos) ← parseCli rest; pure ({ o with indexByPrefix := true }, pos)
  | "--total-select" :: rest => do
    let (o, pos) ← parseCli rest; pure ({ o with totalSelect := true }, pos)
  | "--inline-spec-fns" :: rest => do
    let (o, pos) ← parseCli rest; pure ({ o with inlineSpecFns := true }, pos)
  | arg :: rest =>
    if arg.startsWith "--" then throw s!"unknown option {arg}"
    else do let (o, pos) ← parseCli rest; pure (o, arg :: pos)
  | [] => pure ({}, [])

unsafe def genBooleFromFile
    (path : String)
    (printFn : String → IO Unit) (opts : CliOptions := {}) : IO Unit := do
  let target := System.FilePath.mk path
  let bundleFiles ← collectJsonBundleFiles target
  let natPreludeBody? ← readNatPreludeBody?
  let seqPreludeBody? ← readSeqPreludeBody?
  let vecPreludeBody? ← readVecPreludeBody?
  let mut allDecls : List Decl := []
  for f in bundleFiles do
    match ← Decls.fromFile? f.toString with
    | .ok (_ns, defs, thms, _callTypes) =>
      allDecls := allDecls ++ defs ++ thms
    | .error e =>
      if f == target then failWith e
      else IO.eprintln s!"warning: skipping shard {f}: {e}"
  -- Literal `pow2(k)` / `pow(b, k)` become literals (see `Fold`).
  allDecls := Boole.Fold.foldPowCalls allDecls
  -- Resolve trait-method calls (e.g. `+` on Scalar) to their impls before pruning,
  -- so the impl (and not the abstract trait method) is what `--only` keeps.
  if !opts.only.isEmpty then
    allDecls := Boole.TraitResolve.resolveTraitSpecCalls allDecls
  -- Stub first, then prune: callees of the entry are kept by their contracts
  -- alone, so their own callees do not get pulled in.
  allDecls := Boole.Pruning.stubNonEntries opts.only allDecls
  if opts.indexByPrefix then
    allDecls := Boole.Prefix.indexByPrefix allDecls
  if opts.dropProofHints then
    let proofFns := allDecls.filterMap fun d => match d with
      | .proofFn f => some (Boole.Names.identToBoole f.name)
      | _ => none
    -- closed lemmas keep their statements as axioms, then the calls go
    allDecls := Boole.Hints.closedLemmaAxioms allDecls
    allDecls := Boole.Hints.dropProofHints proofFns allDecls
  if opts.valuesInvariants then
    allDecls := Boole.Strengthen.valuesInvariants allDecls
  allDecls := Boole.Pruning.pruneToEntries opts.only allDecls
  if let some want := (← IO.getEnv "VERUS_LEAN_DEBUG_SPEC") then
    for d in allDecls do
      match d with
      | .specFn f => if (Boole.Names.identToBooleLong f.name).endsWith want then
          IO.eprintln s!"[spec] {f.name.toString}\n inputs={repr f.inputs}\n ret={repr f.returnType}\n recommends={repr f.recommends}\n decreases={repr f.decreases}\n body={repr f.body}"
      | .execFn f => if (Boole.Names.identToBooleLong f.name).endsWith want then
          IO.eprintln s!"[exec] {f.name.toString}\n ensures={repr f.ensures}\n body={repr f.body}"
      | .proofFn f => if (Boole.Names.identToBooleLong f.name).endsWith want then
          IO.eprintln s!"[proof] {f.name.toString}\n inputs={repr f.inputs} ret={f.retName}\n requires={repr f.requires}\n ensures={repr f.ensures}"
      | _ => pure ()
  if (← IO.getEnv "VERUS_LEAN_DEBUG_STMS").isSome then
    for d in allDecls do
      match d with
      | .specFn f =>
        IO.eprintln s!"[names] specFn ident={f.name.toString} long={Boole.Names.identToBooleLong f.name}"
        if f.inputs.isEmpty then
          IO.eprintln s!"[body0] {Boole.Names.identToBooleLong f.name} = {(f.body.map Boole.Strengthen.headStr).getD "none"}"
      | .struct s => IO.eprintln s!"[names] struct ident={s.name.toString} long={Boole.Names.datatypeNameOf s.name}"
      | .proofFn f => IO.eprintln s!"[names] proofFn ident={f.name.toString} long={Boole.Names.identToBooleLong f.name}"
      | _ => pure ()
    for d in allDecls do
      match d with
      | .execFn f =>
        let rec heads (depth : Nat) : Stm → List String
          | .Block ss => if depth == 0 then ["Block"] else ss.flatMap (heads (depth - 1))
          | .Loop _ _ _ body _ _ => ["Loop{"] ++ (if depth == 0 then [] else heads (depth - 1) body) ++ ["}"]
          | .Assign lhs _ rhs init => [s!"Assign({repr lhs}, init={init}, rhs={match rhs with | .Call fn _ _ => "Call " ++ (Boole.Names.identToBoole (CallFun.name fn)) | .Var v => "Var " ++ v | _ => "expr"})"]
          | .Call fn _ _ => [s!"Call {Boole.Names.identToBoole fn}"]
          | .Assert _ => ["Assert"] | .Assume _ => ["Assume"]
          | _ => ["other"]
        IO.eprintln s!"[names] execFn ident={f.name.toString} long={Boole.Names.identToBooleLong f.name}"
        IO.eprintln s!"[stms] {Boole.Names.identToBoole f.name}:"
        for h in heads 30 f.body do IO.eprintln s!"    {h}"
      | _ => pure ()
  if !opts.only.isEmpty && allDecls.isEmpty then
    failWith s!"--only: no declaration matches {opts.only}"
  -- Plan prelude loading from VLIR syntax before BooleDDM construction, then
  -- translate once with the parsed prelude names pre-registered so fvar
  -- indices align with Strata's global context.
  let synthCfg ← synthConfigFromEnv
  let preludePlan := Boole.Prelude.planDecls allDecls
  -- Load each prelude piece separately so the `nat` block can be dropped when
  -- the emitted program never references it.  `nat`'s names are registered
  -- (loaded) whenever the file is present, keeping fvar indices stable; whether
  -- the `nat` declarations are *emitted* is decided post-translation from the
  -- rendered text.  Seq/Vec gate on their VLIR triggers.
  let loadPiece (needed : Bool) (body? : Option String) := do
    if needed then
      match body? with
      | some text =>
        match ← Boole.Emit.loadPrelude text with
        | .ok r => pure r
        | .error e => failWith e
      | none => pure (#[], #[])
    else pure (#[], #[])
  let (natOps, natNames) ← loadPiece natPreludeBody?.isSome natPreludeBody?
  let (seqOps, seqNames) ← loadPiece (preludePlan.needsSeq && seqPreludeBody?.isSome) seqPreludeBody?
  let (vecOps, vecNames) ← loadPiece (preludePlan.needsVec && vecPreludeBody?.isSome) vecPreludeBody?
  -- Order matters: Nat first — Seq bodies reference `int_to_nat` from Nat.
  let preludeNames := natNames ++ seqNames ++ vecNames
  match Translate.translateDeclsWithPrelude allDecls preludeNames synthCfg with
  | .error e => failWith e
  | .ok (cmds, finalCtx) =>
    -- Filter out user commands whose names are already in the prelude
    let preludeSet := preludeNames.toList
    let cmds := cmds.filter fun cmd =>
      match Translate.cmdDeclName? cmd with
      | some name => !preludeSet.contains name
      | none => true
    let cmds := dedupeNamedCommands cmds
    let bodyOps := Boole.Emit.commandsToOps cmds
    -- Boole has grammar-level `nat`/`pos` with a binary-datatype library that
    -- `Strata.Boole.verify` injects itself, so the translator's `nat` prelude is
    -- loaded for name registration only and never emitted; its names are
    -- rendered as Boole's native operator surface (`nativeNatNames`).
    let _ := natOps
    let preludeOps := seqOps ++ vecOps
    match Boole.Emit.renderProgram preludeOps bodyOps finalCtx.allFreeVars with
    | .ok output =>
      let output := if opts.only.isEmpty then output else pruneUnreferencedDecls output
      let output := if opts.shortNames then shortenNames allDecls output else output
      let output := nativeNatNames output
      -- final compaction: `tidy`'s blank line between declarations (needed above,
      -- to find block boundaries for pruning/renaming) is not wanted in the
      -- rendered program — no separators between declarations at all, matching
      -- the density of the hand-written benchmark.
      printFn (output.replace "

" "
")
    | .error e => failWith e

unsafe def main (args : List String) : IO Unit := do
  let args := match args with | "boole" :: rest => rest | a => a
  match parseCli args with
  | .error e => IO.eprintln s!"Error: {e}"; IO.Process.exit 2
  | .ok (opts, [path]) =>
    Boole.Flags.u8AsIntRef.set opts.u8AsInt
    Boole.Flags.literalConstsAsAxiomsRef.set opts.literalConstsAsAxioms
    Boole.Flags.totalSelectRef.set opts.totalSelect
    Boole.Flags.inlineSpecFnsRef.set opts.inlineSpecFns
    genBooleFromFile path IO.println opts
  | .ok (opts, [path, toFile]) =>
    Boole.Flags.u8AsIntRef.set opts.u8AsInt
    Boole.Flags.literalConstsAsAxiomsRef.set opts.literalConstsAsAxioms
    Boole.Flags.totalSelectRef.set opts.totalSelect
    Boole.Flags.inlineSpecFnsRef.set opts.inlineSpecFns
    genBooleFromFile path (IO.FS.writeFile toFile) opts
  | .ok _ =>
    IO.println "Usage: ./verus-lean [boole] [--only f,g] [--u8-as-int] [--drop-proof-hints] [--short-names] [--values-invariants] [--literal-consts-as-axioms] <input.json> [output.boole.st]"
