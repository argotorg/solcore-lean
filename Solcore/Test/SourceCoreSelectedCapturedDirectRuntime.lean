import Solcore.Test.SourceCoreSelectedCapturedDirectFixture

set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedCapturedDirect
open Solcore Frontend SourceInference SourceSemantics CoreLowering

private def require (condition : Bool) (message : String) : IO Unit :=
  if condition then pure () else throw (IO.userError message)

def run : IO Unit := do
  let fixture ← fixture
  let started ← observeStarted fixture
  have _sourceFirst := from_source fixture started
  let .outOfFuel factorySuspended ← started.call.checkpoint.resume 0 0
    | throw (IO.userError "captured factory did not suspend at zero fuel")
  let .succeeded factory ← factorySuspended.resume 100000 1000
    | throw (IO.userError "captured factory did not complete")
  let .function handle := factory.value
    | throw (IO.userError "captured factory did not return its closure handle")
  require (handle.sourceType == .function .unit .word) "captured handle type changed"
  let .ok checkpoint := factory.session.startHandlePacked handle .unit runOptions.inputValidationFuel
    | throw (IO.userError "captured direct call did not start")
  let .outOfFuel suspended ← checkpoint.resume 0 0
    | throw (IO.userError "captured direct call did not suspend at zero fuel")
  let .succeeded first ← suspended.resume 100000 1000
    | throw (IO.userError "captured direct call did not complete")
  require (first.value == .word seed) "captured Source read changed"
  let .ok repeatedCheckpoint := first.session.startHandlePacked handle .unit runOptions.inputValidationFuel
    | throw (IO.userError "captured handle was not retained after the direct call")
  let .succeeded repeated ← repeatedCheckpoint.resume 100000 1000
    | throw (IO.userError "retained captured call did not complete")
  require (repeated.value == .word seed) "retained captured Source read changed"
  require ([started.session.heapSize, factory.session.heapSize, first.session.heapSize, repeated.session.heapSize]
    == [2, 5, 5, 5]) "captured direct heap sizes changed"
  require (fixture.recipe.compiled.indexed.base.functions.length == 1) "captured cache changed"
  IO.println s!"SOURCE_FIRST_DIRECT_CAPTURED_PASS: actual checked factory captures parameter37 at Source location0; independently constructed factory and direct closure traces before execution; closed initial function/full-output and retained direct scalar alternatives; zero-fuel factory/direct resume; old closure handle repeated; heaps{[started.session.heapSize, factory.session.heapSize, first.session.heapSize, repeated.session.heapSize]}"

end Tests.SourceCoreSelectedCapturedDirect
