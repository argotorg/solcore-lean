import Solcore.Test.SourceCoreSelectedNamedBuiltinDirectSourceFirst

set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedNamedBuiltinDirect
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreInitialLexicalFailure

private def require (condition : Bool) (message : String) : IO Unit :=
  if condition then pure () else throw (IO.userError message)

def run : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeProgram fixture
  let profile ← Tests.SourceCoreSelectedLexicalFailure.observeProfile fixture
  let stages ← observeStages fixture observed.identityRow
  let fresh ← Tests.SourceCoreCertifiedLexicalFailure.observeFreshIdentity fixture observed
  let calls ← observeHandles observed fresh
  have _sourceFirst := meaning profile stages fresh calls
  let .outOfFuel namedSuspended ← calls.identityCheckpoint.resume 0 0
    | throw (IO.userError "named direct call did not suspend at zero fuel")
  let .succeeded named ← namedSuspended.resume 100000 1000
    | throw (IO.userError "named direct Source identity did not complete")
  require (named.value == .word seed) "named direct Source identity result changed"
  let .outOfFuel builtinSuspended ← calls.builtinCheckpoint.resume 0 0
    | throw (IO.userError "builtin direct call did not suspend at zero fuel")
  let .succeeded builtin ← builtinSuspended.resume 100000 1000
    | throw (IO.userError "builtin direct Source conversion did not complete")
  require (builtin.value == .word convertedWord) "builtin direct Source conversion result changed"
  let .outOfFuel failedSuspended ← calls.failedCheckpoint.resume 0 0
    | throw (IO.userError "named direct failure did not suspend at zero fuel")
  let .failed reason after ← failedSuspended.resume 100000 0
    | throw (IO.userError "named direct absent read did not fail")
  let .ok (some diagnostic) := after.diagnostic observed.failedRow.row.key reason
    | throw (IO.userError "named direct absent-read diagnostic missing")
  require (match diagnostic.error with | .uninitializedLocal _ => true | _ => false)
    "named direct semantic fault changed"
  let .ok continuedCheckpoint := after.startHandlePacked calls.identity.handle (.word seed)
      runOptions.inputValidationFuel
    | throw (IO.userError "failed direct session lost the earlier named handle")
  let .succeeded continued ← continuedCheckpoint.resume 100000 1000
    | throw (IO.userError "earlier named handle could not continue after failure")
  require (continued.value == .word seed) "retained named continuation changed"
  let .ok convertedCheckpoint := continued.session.startHandlePacked calls.builtin.handle (.integer integerArgument)
      runOptions.inputValidationFuel
    | throw (IO.userError "continuation lost the earlier builtin handle")
  let .succeeded converted ← convertedCheckpoint.resume 100000 1000
    | throw (IO.userError "earlier builtin handle could not continue after failure")
  require (converted.value == .word convertedWord) "retained builtin continuation changed"
  require (calls.identity.completion.session.heapSize == fresh.call.completion.session.heapSize &&
    calls.builtin.completion.session.heapSize == calls.identity.completion.session.heapSize &&
    calls.failed.completion.session.heapSize == calls.builtin.completion.session.heapSize)
    "genuine handle issuance changed the existing runtime heap"
  require ([fresh.call.completion.session.heapSize, named.session.heapSize,
    builtin.session.heapSize, after.heapSize, continued.session.heapSize, converted.session.heapSize]
    == [6, 9, 6, 9, 12, 12]) "direct Source-first exact heap sizes changed"
  require (fixture.recipe.compiled.indexed.base.functions.length == 2)
    "original lexical cache changed"
  IO.println s!"SOURCE_FIRST_DIRECT_NAMED_BUILTIN_PASS: original checker1000/compiler100; retained named identity37, builtin integer37-to-word37 and named absent-cell semantic fault; ordinary traces precede direct execution; closed scalar/full-output/fault alternatives; zero-fuel resume; retained named+builtin reuse after failure; heaps{[fresh.call.completion.session.heapSize, named.session.heapSize, builtin.session.heapSize, after.heapSize, continued.session.heapSize, converted.session.heapSize]}"

end Tests.SourceCoreSelectedNamedBuiltinDirect
