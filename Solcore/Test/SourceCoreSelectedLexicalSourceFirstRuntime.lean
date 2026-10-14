import Solcore.Test.SourceCoreSelectedLexicalSourceFirst

set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedLexicalSourceFirst
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreInitialLexicalFailure
open Tests.SourceCoreSelectedLexicalSourceStart

private def require (condition : Bool) (message : String) : IO Unit :=
  if condition then pure () else throw (IO.userError message)

def run : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeProgram fixture
  let profile ← Tests.SourceCoreSelectedLexicalFailure.observeProfile fixture
  let failureStages ← observeStages fixture observed.failedRow
  let scalarStages ← observeStages fixture observed.identityRow
  let failed ← observeStarted fixture observed.failedRow.row.key []
  let scalar ← observeStarted fixture observed.identityRow.row.key [.word seed]
  have _first := fault_from_source profile failureStages failed
  have _scalar := scalar_from_source profile scalarStages scalar
  let .outOfFuel suspended ← failed.call.checkpoint.resume 0 0
    | throw (IO.userError "source-first failure did not suspend at zero fuel")
  let .failed reason after ← suspended.resume 100000 0
    | throw (IO.userError "source-first uninitialized read did not fail")
  let .ok (some diagnostic) := after.diagnostic observed.failedRow.row.key reason
    | throw (IO.userError "source-first lexical diagnostic missing")
  require (match diagnostic.error with | .uninitializedLocal _ => true | _ => false)
    "source-first failure reason changed"
  let .outOfFuel suspended ← scalar.call.checkpoint.resume 0 0
    | throw (IO.userError "source-first scalar did not suspend at zero fuel")
  let .succeeded completed ← suspended.resume 100000 1000
    | throw (IO.userError "source-first identity did not complete")
  require (completed.value == .word seed) "source-first identity did not return37"
  let .ok checkpoint := after.start observed.identityRow.row.key [.word seed] runOptions.inputValidationFuel
    | throw (IO.userError "source-first returned session could not start identity")
  let .succeeded continued ← checkpoint.resume 100000 1000
    | throw (IO.userError "source-first identity after failure did not complete")
  require (continued.value == .word seed) "source-first continuation changed the value"
  require ([failed.session.heapSize, after.heapSize, scalar.session.heapSize,
    completed.session.heapSize, continued.session.heapSize] == [3, 6, 3, 6, 9])
    "source-first public stores changed"
  require (fixture.recipe.compiled.indexed.base.functions.length == 2)
    "source-first original cache changed"
  IO.println "LEXICAL_SOURCE_FIRST_FORWARD_PASS: original checker1000/compiler100; startup-only receipts; independently constructed ordinary identity37 and absent-cell fault; closed forward alternatives; zero-fuel resume; exact public heaps3/6/3/6/9 and returned-session identity37"

end Tests.SourceCoreSelectedLexicalSourceFirst
