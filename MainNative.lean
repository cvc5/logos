import Cpc.Native
import Lean

private def reportMessages (msgLog : Lean.MessageLog) (opts : Lean.Options)
    (json : Bool) (severityOverrides : Lean.NameMap Lean.MessageSeverity) (numErrors : Nat) : IO Nat := do
  let includeEndPos := Lean.Language.printMessageEndPos.get opts
  msgLog.unreported.foldlM (init := numErrors) fun numErrors msg => do
    let numErrors := numErrors + (if msg.severity matches .error then 1 else 0)
    let maxErrorsReached := Lean.Language.maxErrors.get opts != 0 && numErrors > Lean.Language.maxErrors.get opts
    let msg : Lean.Message :=
      if maxErrorsReached then { msg with
        data := s!"maximum number of errors ({Lean.Language.maxErrors.get opts}; from option `maxErrors`) reached, exiting"
        severity := .error
      } else if let some severity := severityOverrides.find? msg.kind then
        {msg with severity}
      else
        msg
    unless msg.isSilent do
      if json then
        let j ← msg.toJson
        IO.println j.compress
      else
        let s ← msg.toString includeEndPos
        IO.print s
    if maxErrorsReached then
      IO.Process.exit 1
    return numErrors

def evalLogoExpr (path : String) : Lean.Meta.MetaM Nat := do
  try
    let stx ← Lean.Parser.testParseFile (← Lean.getEnv) path
    let .node _ _ #[_, .node _ _ args] := stx
      | throwError "Expected a proof of the following form:\nimport Cpc.Native\n\n#eval! <proof>\n\ngot:\n{stx}"
    Lean.liftCommandElabM do
      for arg in args do
        Lean.Elab.Command.elabCommand arg
  catch e =>
    Lean.logError m!"{e.toMessageData}"
  Lean.printTraces
  reportMessages (← Lean.Core.getMessageLog) (← Lean.getOptions) false {} 0

-- unsafe due to IO operations?
unsafe def main (args : List String) : IO UInt32 := do
  let [path] := args
    | IO.eprintln "usage: logos-native <path-to-proof-file>"
      return 1
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let env ← Lean.importModules #[`Cpc.Native] {} 0 (loadExts := true)
  let coreContext := { fileName := path, fileMap := default }
  let coreState := { env }
  let (res, _, _) ← Lean.Meta.MetaM.toIO (evalLogoExpr path) coreContext coreState
  return res.toUInt32

-- To build, run "lake build logos-native" in this directory.
-- To run, use "lake exe logos-native <path-to-proof-file>".
