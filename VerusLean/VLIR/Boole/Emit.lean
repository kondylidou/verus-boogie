/-
  Boole.Emit — Assemble BooleDDM commands into a StrataDDM.Program and emit text.

  This module owns the final step:  `Array BooleDDM.Command → String`.
  It handles:
    • Name resolution context for free/bound variable indices.
    • Prelude text loading + merging.
    • Calling Strata's official formatter (`Boole.formatProgram`).
-/
import VerusLean.VLIR.Boole.Builder
import VerusLean.VLIR.Boole.Context

import StrataBoole.Boole
import StrataBoole.Verify
import StrataDDM

namespace VerusLean.Boole.Emit

open Strata
open Strata.BooleDDM
open VerusLean.Boole.Builder
open VerusLean.Boole.Context

export VerusLean.Boole.Context (BuildCtx BuildM SupportDecl emptyCtx requireSupport freshLoopLabelId)

/-- Run a sub-computation in a fresh scope (pushes and pops). -/
def withScope (k : BuildM α) : BuildM α := do
  modify BuildCtx.pushScope
  try
    let out ← k
    modify BuildCtx.popScope
    pure out
  catch e =>
    modify BuildCtx.popScope
    throw e

/-- Add names as bound variables in the current scope.

    Boole verification resolves bvar index 0 to the newest/rightmost binder.
    Keep binders in source order here and make lookup search from the right;
    this preserves source binder order while producing verifier-compatible
    de Bruijn indices. -/
def addBoundVars (names : Array String) : BuildM Unit := do
  modify (·.addBoundVars names)

/-- Push a single bound var to current scope (convenience for init stmts). -/
def pushBoundVar (name : String) : BuildM Unit :=
  modify (·.pushBoundVar name)

/-- Register names as global free variables (skip already-registered). -/
def addFreeVars (names : Array String) : BuildM Unit := do
  let ctx ← get
  let fresh := names.filter (fun name => ctx.freeVarIndex? name |>.isNone)
  modify (·.addGlobalFreeVars fresh)

/-- Look up the free variable index for a name, registering it if new. -/
def resolveFreeVar (name : String) : BuildM Nat := do
  addFreeVars #[name]
  let ctx ← get
  match ctx.freeVarIndex? name with
  | some idx => pure idx
  | none => throw s!"bug: failed to register free variable '{name}'"

/-- Find the de Bruijn index of the rightmost matching binder.

    This handles ordinary shadowing correctly: inner scopes are appended after
    outer scopes, and later declarations in the same binder list are newer. -/
private def findBoundVarIndex? (vars : Array String) (name : String) : Option Nat :=
  let rec go (remaining : Nat) (offset : Nat) : Option Nat :=
    match remaining with
    | 0 => none
    | i + 1 =>
        match vars[i]? with
        | some v => if v == name then some offset else go i (offset + 1)
        | none => none
  go vars.size 0

/-- Look up a bound variable by name. Returns `none` if not in scope. -/
def lookupBoundVar (name : String) : BuildM (Option Nat) := do
  let ctx ← get
  pure (findBoundVarIndex? ctx.allBoundVars name)

/-- Convert an array of BooleDDM Commands to Strata Operations. -/
def commandsToOps (cmds : Array BCmd) : Array StrataDDM.Operation :=
  cmds.map (·.toAst)

/-- Loaded dialect map for Boole. -/
private def loadedBooleDialects : StrataDDM.Elab.LoadedDialects :=
  StrataDDM.Elab.LoadedDialects.ofDialects! Strata.Boole_map.toList.toArray

/-- Parse Boole text into a StrataDDM.Program (for prelude loading). -/
def parseBooleText (text : String) : IO (Except String StrataDDM.Program) := do
  let fm ← StrataDDM.DialectFileMap.new loadedBooleDialects
  match ← StrataDDM.readStrataText fm "<generated-boole>" text.toUTF8 with
  | .program pgm => pure (.ok pgm)
  | .dialect _ => pure (.error "expected a Boole program, but Strata parsed a dialect")

/-- Load prelude text, parse it, and return its operations + global names. -/
def loadPrelude (preludeText : String) :
    IO (Except String (Array StrataDDM.Operation × Array String)) := do
  match ← parseBooleText s!"program Boole;\n\n{preludeText.trimAsciiEnd.toString}\n" with
  | .ok pgm =>
    pure (.ok (pgm.commands, pgm.globalContext.vars.map (·.1)))
  | .error e => pure (.error e)

/-- Build a `GlobalContext` from a list of names, in order. Uses
    `GlobalKind.type [] none` as a placeholder kind; the formatter only looks
    up names by index, not by kind. -/
def buildGlobalContext (names : Array String) : StrataDDM.GlobalContext :=
  names.foldl (fun ctx name =>
    ctx.ensureDefined name (.type [] none)) {}

/-- Cosmetic clean-up of the formatter's output: no leading blank on top-level
    lines, one blank line between top-level declarations and none inside them
    (axioms stay glued to the declaration they follow),
    `requires`/`ensures`/`decreases`/`invariant` each on its own indented line. -/
def tidy (s : String) : String := Id.run do
  let isTop (l : String) : Bool :=
    ["type ", "function ", "inline function ", "rec function ", "procedure ", "axiom ", "datatype ", "const "].any
      (fun k => l.startsWith k || l.startsWith (" " ++ k))
  -- split glued keywords: `… - 1invariant …`, `) : int requires …`
  let s := (s.replace "invariant " "\n    invariant ").replace "\n\n    invariant" "\n    invariant"
  let s := (s.replace " requires " "\n  requires ").replace " ensures " "\n  ensures "
  let s := s.replace "\ndecreases " "\n  decreases "
  let mut out : Array String := #[]
  let mut inProc := false
  for l in s.splitOn "\n" do
    let l : String := if l.startsWith " " && isTop l then (l.toSubstring.drop 1).toString else l
    if l.trimAscii.isEmpty then continue           -- blank lines are re-inserted below
    if isTop l then
      -- an `axiom` attaches to the declaration before it (no blank line)
      if !out.isEmpty && !(l.startsWith "axiom ") then out := out.push ""
      inProc := l.startsWith "procedure "
    -- a function body's `{` sits on its own unindented line; inside procedures
    -- the formatter's indentation is kept.  `} {` (end of spec, start of body)
    -- becomes two lines.
    if l.trimAscii.toString == "{" && !inProc then out := out.push "{"
    else if l.trimAscii.toString == "} {" then
      out := out.push "}"
      out := out.push "{"
    else out := out.push l
  -- procedure/function bodies: `};` closers and `{` openers keep their own lines
  return String.intercalate "\n" out.toList

/-- Render Boole commands to text using Strata's `Boole.formatProgram` with an
    explicit `GlobalContext`. This uses the PR fix to resolve fvar indices when
    commands come from `BooleDDM.toAst` (which doesn't populate globalContext).

    `preludeOps` are the parsed prelude's operations (or empty).
    `bodyOps` are our translated commands as operations.
    `freeVarNames` is the ordered list of names in our `BuildCtx.allFreeVars`
    — used to construct the `GlobalContext` for Strata's formatter. -/
def renderProgram
    (preludeOps bodyOps : Array StrataDDM.Operation)
    (freeVarNames : Array String) : Except String String :=
  let allOps := preludeOps ++ bodyOps
  let pgm := StrataDDM.Program.create Strata.Boole_map "Boole" allOps
  match Strata.Boole.getProgram pgm with
  | .error e => .error (toString e)
  | .ok booleProg =>
    let gctx := buildGlobalContext freeVarNames
    let formatted := Strata.Boole.formatProgram booleProg gctx Strata.Boole_map
    let body := Std.Format.pretty formatted 100
    -- `Boole.formatProgram` emits only the program body; the dialect header
    -- is required for the output to be re-parseable (this mirrors the fix
    -- Strata PR #767 applied the same header fix to Core formatting.
    let output := s!"program Boole;\n\n{tidy body}"
    let output := if output.endsWith "\n" then output else output ++ "\n"
    .ok output

end VerusLean.Boole.Emit
