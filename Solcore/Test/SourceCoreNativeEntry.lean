import Solcore.Frontend.SourceCoreGeneralEntry
import Solcore.Frontend.SourceCoreStageCodebook
import Solcore.Frontend.SourceCoreCallableFaultSites

/-! The shared native runner checks every input payload and retains typing
across suspension. Its definitions need not come from the strict catalog. -/
set_option autoImplicit false
namespace Tests.SourceCoreNativeEntry
open Solcore Solcore.Core Solcore.Frontend SourceCoreGeneralEntry

private def definitions : DataEnvironment := [⟨[.product .integer .bool]⟩]
private def body : Expr := Core.LanguageResult.bind (.namedData ⟨0⟩)
  (Core.OptionalCell.read (.namedData ⟨0⟩) (.var 0) Word.zero)
  (Core.LanguageResult.success (.var 0))
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc"
  externalLibraries := []
  mainSources := [{path := "main.solc", content := "function empty() returns () {}"}]
}

example {definitions : DataEnvironment} (entry : NativeEntry definitions) (arguments : List Core.Value)
    (checkpoint : Checkpoint definitions entry.resultType) (_accepted : entry.start arguments = .ok checkpoint) :
    Core.StateHasType checkpoint.state (Core.LanguageResult.resultType entry.resultType) definitions :=
  checkpoint.typed

def run : IO Unit := do
  let entry ← match NativeEntry.compile definitions [.namedData ⟨0⟩] (.namedData ⟨0⟩) body with
    | .ok entry => pure entry
    | .error error => throw (IO.userError s!"native entry rejected: {reprStr error}")
  let value : Core.Value := .constructed ⟨⟨0⟩, 0⟩ (.pair (.integer (-900)) (.bool true))
  let checkpoint ← match entry.start [value] with
    | .ok checkpoint => pure checkpoint
    | .error error => throw (IO.userError s!"native input rejected: {reprStr error}")
  let suspended := checkpoint.resume 0
  let next ← match suspended.checkpoint? with
    | some next => pure next
    | none => throw (IO.userError "native zero fuel did not suspend")
  match (next.resume 100).observation with
    | .succeeded actual [.inRight .unit stored] =>
        unless actual == value && stored == value do throw (IO.userError "native input/result changed")
    | result => throw (IO.userError s!"native resume failed: {reprStr result}")
  for malformed in [Core.Value.constructed ⟨⟨0⟩, 0⟩ (.pair (.bool false) (.bool true)),
      .constructed ⟨⟨0⟩, 1⟩ .unit,
      .constructed ⟨⟨0⟩, 0⟩ (.pair (.integer 0) (.cellRef .bool 0))] do
    match entry.start [malformed] with
      | .error (.input 0 _) => pure ()
      | _ => throw (IO.userError "native boundary accepted malformed nested payload")
  match entry.start [value] [.unit] with
    | .error (.initialStoreUnsupported 1) => pure ()
    | _ => throw (IO.userError "native Core initial-store behavior changed")
  match NativeEntry.compile definitions [.namedData ⟨0⟩] .bool body with
    | .error (.coreCheckFailed _ _) => pure ()
    | _ => throw (IO.userError "native body accepted the wrong result projection")
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error error => throw (IO.userError s!"native diagnostic fixture rejected: {reprStr error}")
  let table ← match SourceCoreStageCodebook.prepareWithProjection
      program ⟨[], [], [], []⟩ (fun _ => pure .unit) with
    | .ok table => pure table
    | .error error => throw (IO.userError s!"empty native descriptor inventory failed: {reprStr error}")
  let owner ← match program.signatures.functions.head? with
    | some signature => pure signature.id
    | none => throw (IO.userError "native diagnostic root missing")
  let base : SourceCoreFaultSites.Table := {
    owner, resultType := .unit, reads := [], escapedReason := Word.zero, additional := []}
  let diagnostics ← match SourceCoreCallableFaultSites.prepare ⟨[], [], [], []⟩ table base 70000 with
    | .ok diagnostics => pure diagnostics
    | .error error => throw (IO.userError s!"native diagnostic reservation failed: {reprStr error}")
  unless diagnostics.unknown.val == 70000 do throw (IO.userError "callable tokens overlapped reserved dynamic ranges")
  IO.println "shared native input checking, typed resume and diagnostic reservation GREEN"

end Tests.SourceCoreNativeEntry
