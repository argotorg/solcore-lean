import Solcore.Test.SourceCoreMixedWhileInventory
import Solcore.Test.SourceCoreMixedWhileWellFormed
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionState

/-! Actual opening, export-aware bootstrap and public input receipt, recorded
before resuming the selected function. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMixedWhile
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open SelectedCompilationPublicSessionState (StartedCall)

structure Started (fixture : CompiledFixture) (key : SourceCoreIndexedSession.Key)
    (arguments : List SourceCorePublicValues.Value) where
  artifact : SourceCoreExecution.Artifact
  opened : artifact.CompiledAt fixture.facade
  bootstrap : SourceCoreExecution.Bootstrap artifact
  fresh : bootstrap.FreshAt
  authority : bootstrap.ExportAuthorityAt
  session : SourceCoreExecution.Session artifact
  ready : bootstrap.resume 100000 = .ready session
  call : StartedCall session key arguments runOptions

def observeStarted (fixture : CompiledFixture) (key : SourceCoreIndexedSession.Key)
    (arguments : List SourceCorePublicValues.Value) : IO (Started fixture key arguments) := do
  let opened ← fixture.facade.openWithReceipt
  let bootstrap ← opened.val.bootstrapWithExportReceipt
  match ready : bootstrap.val.resume 100000 with
  | .error error => throw (IO.userError (reprStr error))
  | .outOfFuel _ => throw (IO.userError "generalized local bootstrap exhausted")
  | .ready session =>
    match started : session.start key arguments runOptions.inputValidationFuel with
    | .error error => throw (IO.userError (reprStr error))
    | .ok checkpoint => return ⟨opened.val, opened.property, bootstrap.val, bootstrap.property.1,
        bootstrap.property.2, session, ready, checkpoint, started⟩


end Tests.SourceCoreMixedWhile
