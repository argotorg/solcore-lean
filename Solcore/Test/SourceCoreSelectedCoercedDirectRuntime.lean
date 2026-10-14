import Solcore.Test.SourceCoreSelectedCoercedDirectPublic

set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedCoercedDirect
open Solcore Frontend SourceInference SourceSemantics CoreLowering

private def require (condition : Bool) (message : String) : IO Unit :=
  if condition then pure () else throw (IO.userError message)

private def branch (fixture : Fixture) (flag : Bool) : IO Unit := do
  let started ← observeStarted fixture flag
  have _sourceFirst := from_source fixture flag started
  let .outOfFuel factorySuspended ← started.call.checkpoint.resume 0 0
    | throw (IO.userError "coerced factory did not suspend at zero fuel")
  let .succeeded factory ← factorySuspended.resume 300000 2048
    | throw (IO.userError "coerced factory did not complete")
  let .function handle := factory.value
    | throw (IO.userError "coerced factory did not return its closure handle")
  require (handle.sourceType == .function .unit .word) "coerced handle type changed"
  let .ok checkpoint := factory.session.startHandlePacked handle .unit runOptions.inputValidationFuel
    | throw (IO.userError "coerced direct call did not start")
  let .outOfFuel suspended ← checkpoint.resume 0 0
    | throw (IO.userError "coerced direct call did not suspend at zero fuel")
  let .succeeded first ← suspended.resume 300000 2048
    | throw (IO.userError "coerced direct call did not complete")
  require (first.value == .word (converted flag)) "coerced Source read changed"
  let .ok repeatedCheckpoint := first.session.startHandlePacked handle .unit runOptions.inputValidationFuel
    | throw (IO.userError "coerced handle was not retained after the direct call")
  let .succeeded repeated ← repeatedCheckpoint.resume 300000 2048
    | throw (IO.userError "retained coerced call did not complete")
  require (repeated.value == .word (converted flag)) "retained coerced Source read changed"
  require ([started.session.heapSize, factory.session.heapSize, first.session.heapSize, repeated.session.heapSize]
    == [5, 8, 14, 20]) "coerced exact heap sizes changed"
  require (fixture.recipe.compiled.indexed.base.functions.length == 4) "coerced cache changed"
  IO.println s!"SOURCE_FIRST_COERCED_BRANCH_PASS: flag={flag}; result={converted flag}; heaps{[started.session.heapSize, factory.session.heapSize, first.session.heapSize, repeated.session.heapSize]}"

def run : IO Unit := do
  let fixture ← fixture
  branch fixture true
  branch fixture false
  IO.println "SOURCE_FIRST_COERCED_PROFILE_PASS: unchanged checked1024/compiled1000 original four-row program; automatic same-profile issuance; independent captured Bool/Mark dictionary/keep/Coerce traces; closed initial function and full output, direct scalar; both 41/7 branches, zero-fuel resumes and retained handle reuse"

end Tests.SourceCoreSelectedCoercedDirect
