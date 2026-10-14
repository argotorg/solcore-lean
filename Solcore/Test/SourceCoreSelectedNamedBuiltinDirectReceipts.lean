import Solcore.Test.SourceCoreSelectedLexicalFailureMeaning
import Solcore.Test.SourceCoreDirectIssuedSequence
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionIssuance

set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedNamedBuiltinDirect
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreInitialLexicalFailure
open Tests.SourceCoreCertifiedLexicalFailure (FreshIdentity)
open Tests.SourceCoreDirectIssued (ObservedNamed ObservedBuiltin observeNamed observeBuiltin)

def integerArgument : Int := 37
def convertedWord : Core.Word := Core.Word.ofIntModulo integerArgument

structure Handles (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (fresh : FreshIdentity fixture observed) where
  identity : ObservedNamed fresh.call.completion.session observed.identityRow.row.key
  builtin : ObservedBuiltin identity.completion.session
  failed : ObservedNamed builtin.completion.session observed.failedRow.row.key
  identityCheckpoint : SourceCoreExecution.Checkpoint fresh.artifact
  identityStarted : failed.completion.session.startHandlePacked identity.handle (.word seed)
    runOptions.inputValidationFuel = .ok identityCheckpoint
  builtinCheckpoint : SourceCoreExecution.Checkpoint fresh.artifact
  builtinStarted : failed.completion.session.startHandlePacked builtin.handle (.integer integerArgument)
    runOptions.inputValidationFuel = .ok builtinCheckpoint
  failedCheckpoint : SourceCoreExecution.Checkpoint fresh.artifact
  failedStarted : failed.completion.session.startHandlePacked failed.handle .unit
    runOptions.inputValidationFuel = .ok failedCheckpoint

def observeHandles {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    (fresh : FreshIdentity fixture observed) : IO (Handles fixture observed fresh) := do
  let identity ← observeNamed fresh.call.completion.session observed.identityRow.row.key
  let builtin ← observeBuiltin identity.completion.session
  let failed ← observeNamed builtin.completion.session observed.failedRow.row.key
  match identityStarted : failed.completion.session.startHandlePacked identity.handle (.word seed)
      runOptions.inputValidationFuel with
  | .error error => throw (IO.userError (reprStr error))
  | .ok identityCheckpoint =>
    match builtinStarted : failed.completion.session.startHandlePacked builtin.handle (.integer integerArgument)
        runOptions.inputValidationFuel with
    | .error error => throw (IO.userError (reprStr error))
    | .ok builtinCheckpoint =>
      match failedStarted : failed.completion.session.startHandlePacked failed.handle .unit
          runOptions.inputValidationFuel with
      | .error error => throw (IO.userError (reprStr error))
      | .ok failedCheckpoint =>
        pure ⟨identity, builtin, failed, identityCheckpoint, identityStarted,
          builtinCheckpoint, builtinStarted, failedCheckpoint, failedStarted⟩

end Tests.SourceCoreSelectedNamedBuiltinDirect
