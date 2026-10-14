import Solcore.Test.SourceCoreSelectedBitNotSourceFirst
import Solcore.Test.SourceCoreUnifiedCorpusSupport

set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedBitNot
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering

private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def word (n : Nat) : SourceCorePublicValues.Value := .word (Word.ofNatModulo n)
private def flipped (n : Nat) : SourceCorePublicValues.Value := .word (Word.ofNatModulo n).bitNot

private def success {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreExecution.Key)
    (arguments : List SourceCorePublicValues.Value) (expected : SourceCorePublicValues.Value) :
    IO (SourceCoreExecution.Session artifact) := do
  let started ← get "bitnot startup" (session.start key arguments)
  let .outOfFuel suspended ← started.resume 0 0
    | throw (IO.userError "bitnot zero fuel did not suspend")
  let .succeeded completed ← suspended.resume 100000 1000
    | throw (IO.userError "bitnot success missing")
  require (completed.value == expected) "bitnot result changed"
  pure completed.session

private def failure {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreExecution.Key) :
    IO (SourceCoreExecution.Session artifact) := do
  let started ← get "bitnot fault startup" (session.start key [])
  let .failed reason after ← started.resume 100000 1000
    | throw (IO.userError "bitnot absent target did not fail")
  let some diagnostic ← get "bitnot diagnostic" (after.diagnostic key reason)
    | throw (IO.userError "bitnot diagnostic missing")
  require (match diagnostic.error with | .invalidUnaryOperand .bitNot none => true | _ => false)
    "bitnot unary diagnostic changed"
  pure after

/-- The first call consumes the independent Source proof before completion.
Header controls and captured-cell reuse are runtime companions in the same
original eight-function program and the same public session. -/
def run : IO Unit := do
  let fixture ← compileFixture
  let observed ← observeProgram fixture
  let some profile := SelectedCompilationCompilerStaticProfile.validateCheckedProfile
      fixture.recipe.compiled fixture.checked
    | throw (IO.userError "bitnot original selected profile rejected")
  require (fixture.recipe.compiled.indexed.base.functions.length == 8 && profile.table.rows.length == 8)
    "bitnot original cache/table changed"
  let started ← observeStarted fixture observed.invertRow.original.key [word 7]
  have _sourceFirst := initial_from_source fixture observed profile started
  let .outOfFuel suspended ← started.call.checkpoint.resume 0 0
    | throw (IO.userError "bitnot initial zero fuel did not suspend")
  let .succeeded one ← suspended.resume 100000 1000
    | throw (IO.userError "bitnot initial complement failed")
  require (one.value == flipped 7) "bitnot initial complement changed"
  let keys ← ["initialize", "post", "stop", "postMissing", "initialMissing", "make"].mapM
    (SourceCoreUnifiedCorpusSupport.key fixture.recipe.compiled.sourceProgram)
  let [initializer, post, stop, postMissing, initialMissing, make] := keys
    | throw (IO.userError "bitnot original keys changed")
  let two ← success one.session initializer [word 7] (flipped 7)
  let three ← success two post [word 7] (flipped 7)
  let four ← success three stop [word 7] (word 7)
  let five ← failure four observed.missingRow.original.key
  let six ← failure five postMissing
  let seven ← failure six initialMissing
  let eight ← success seven observed.invertRow.original.key [word 7] (flipped 7)
  let pending ← get "bitnot factory startup" (eight.start make [word 7])
  let .succeeded made ← pending.resume 100000 1000
    | throw (IO.userError "bitnot factory failed")
  let .function handle := made.value | throw (IO.userError "bitnot captured handle missing")
  let pendingFirst ← get "bitnot captured first" (made.session.startHandlePacked handle (word 0))
  let .succeeded first ← pendingFirst.resume 100000 1000
    | throw (IO.userError "bitnot captured first failed")
  require (first.value == flipped 7) "bitnot captured first result changed"
  let pendingLast ← get "bitnot captured repeated" (first.session.startHandlePacked handle (word 0))
  let .succeeded last ← pendingLast.resume 100000 1000
    | throw (IO.userError "bitnot captured reuse failed")
  require (last.value == word 7) "bitnot captured reused result changed"
  let heaps := [started.session.heapSize, one.session.heapSize, two.heapSize, three.heapSize,
    four.heapSize, five.heapSize, six.heapSize, seven.heapSize, eight.heapSize,
    made.session.heapSize, first.session.heapSize, last.session.heapSize]
  require (heaps == [9, 12, 16, 23, 30, 33, 40, 43, 46, 49, 52, 55])
    "bitnot original native stores changed"
  IO.println s!"BITNOT_CACHE: cache{fixture.recipe.compiled.indexed.base.functions.length}/table{profile.table.rows.length}"
  IO.println s!"BITNOT_NATIVE_HEAPS: {heaps}"
  IO.println "BITNOT_COMPILER_PROFILE_FORWARD_PASS"

end Tests.SourceCoreSelectedBitNot
