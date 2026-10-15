import Solcore.Test.SourceCoreSelectedProjectedAssignmentSourceFirst
import Solcore.Test.SourceCoreUnifiedCorpusSupport

set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedProjectedAssignment
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering

private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def word (n : Nat) : SourceCorePublicValues.Value := .word (Word.ofNatModulo n)
private def table (entries : List (Nat × Nat)) : SourceCorePublicValues.Value :=
  .mapping .word .word (entries.map fun pair => (word pair.1, word pair.2))
private def nested : SourceCorePublicValues.Value :=
  .mapping .word mappingType [(word 7, table [(2, 4)])]

private def success {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreExecution.Key)
    (arguments : List SourceCorePublicValues.Value) (expected : SourceCorePublicValues.Value) :
    IO (SourceCoreExecution.Session artifact) := do
  let pending ← get "projected startup" (session.start key arguments)
  let .outOfFuel suspended ← pending.resume 0 0
    | throw (IO.userError "projected zero fuel did not suspend")
  let .succeeded completed ← suspended.resume 100000 1000
    | throw (IO.userError "projected success missing")
  require (completed.value == expected) "projected result changed"
  pure completed.session

private def failure {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreExecution.Key)
    (arguments : List SourceCorePublicValues.Value) : IO (SourceCoreExecution.Session artifact) := do
  let pending ← get "projected fault startup" (session.start key arguments)
  let .failed reason after ← pending.resume 100000 1000
    | throw (IO.userError "projected original read did not fail")
  let some diagnostic ← get "projected diagnostic" (after.diagnostic key reason)
    | throw (IO.userError "projected diagnostic missing")
  require (match diagnostic.error with | .uninitializedLocal _ => true | _ => false)
    "projected original read diagnostic changed"
  pure after

/-- All configured rows come from the unchanged complete original program.
The bootstrap-to-mapping theorem is constructed before execution. Ordered key
calls, fault prefixes, header controls and repeated capture are runtime companions. -/
def run : IO Unit := do
  let fixture ← compileFixture
  let observed ← observeProgram fixture
  let some profile := SelectedCompilationCompilerStaticProfile.validateCheckedProfile
      fixture.recipe.compiled fixture.checked
    | throw (IO.userError "projected original selected profile rejected")
  require (fixture.recipe.compiled.sourceProgram.functions.length == 15 &&
      fixture.recipe.compiled.indexed.base.functions.length == 15 && profile.table.rows.length == 15)
    "projected original declarations/cache/table changed"
  let started ← observeStarted fixture observed.keyRow.original.key [word 7]
  have _sourceFirst := initial_then_add fixture observed profile started
    (Word.ofNatModulo 7) (Word.ofNatModulo 4) (Word.ofNatModulo 3)
    [(Word.ofNatModulo 7, Word.ofNatModulo 99), (Word.ofNatModulo 2, Word.ofNatModulo 6)]
  let .outOfFuel suspended ← started.call.checkpoint.resume 0 0
    | throw (IO.userError "projected initial zero fuel did not suspend")
  let .succeeded initial ← suspended.resume 100000 1000
    | throw (IO.userError "projected initial helper failed")
  require (initial.value == word 7) "projected initial helper changed"
  let mut session := initial.session
  let mut heaps := [started.session.heapSize, initial.session.heapSize]
  for (name, arguments, expected) in [
      ("replace", [table [(7,4),(7,99),(2,6)], word 7, word 8], table [(7,8),(7,99),(2,6)]),
      ("add", [table [(7,4),(7,99),(2,6)], word 7, word 3], table [(7,7),(7,99),(2,6)]),
      ("divide", [table [(7,4)], word 7, word 0], table [(7,0)]),
      ("ordered", [table [(7,4),(7,99),(2,6)]], table [(7,80),(7,99),(2,6),(9,90)]),
      ("nested", [nested, word 7, word 2, word 3], word 7),
      ("effects", [table [(7,4)], word 7, word 3], table [(7,7)]),
      ("initialize", [table [], word 7, word 8], table [(7,8)]),
      ("post", [table []], table [(0,2)]),
      ("stop", [table []], table [])] do
    let key ← SourceCoreUnifiedCorpusSupport.key fixture.recipe.compiled.sourceProgram name
    session ← success session key arguments expected
    heaps := heaps ++ [session.heapSize]
  for name in ["keyFailure", "rhsFailure", "missing"] do
    let key ← SourceCoreUnifiedCorpusSupport.key fixture.recipe.compiled.sourceProgram name
    let arguments := if name == "missing" then [table [(7,4)], word 7]
      else [table [(7,4)], word 7, word 3]
    session ← failure session key arguments
    heaps := heaps ++ [session.heapSize]
  session ← success session observed.addRow.original.key [table [(7,4)], word 7, word 3] (table [(7,7)])
  heaps := heaps ++ [session.heapSize]
  let make ← SourceCoreUnifiedCorpusSupport.key fixture.recipe.compiled.sourceProgram "make"
  let pending ← get "projected captured factory" (session.start make [table [(7,4)]])
  let .succeeded made ← pending.resume 100000 1000
    | throw (IO.userError "projected captured factory failed")
  let .function handle := made.value | throw (IO.userError "projected captured handle missing")
  let pending ← get "projected captured first" (made.session.startHandlePacked handle (word 7))
  let .succeeded first ← pending.resume 100000 1000
    | throw (IO.userError "projected captured first failed")
  let pending ← get "projected captured reuse" (first.session.startHandlePacked handle (word 7))
  let .succeeded last ← pending.resume 100000 1000
    | throw (IO.userError "projected captured reuse failed")
  require (first.value == word 5 && last.value == word 6) "projected captured result changed"
  heaps := heaps ++ [made.session.heapSize, first.session.heapSize, last.session.heapSize]
  require (heaps == [16, 22, 40, 58, 76, 97, 133, 163, 182, 198, 205, 223, 250, 262, 280, 283, 298, 313])
    "projected exact native heaps changed"
  IO.println s!"PROJECTED_CACHE: cache{fixture.recipe.compiled.indexed.base.functions.length}/table{profile.table.rows.length}"
  IO.println s!"PROJECTED_NATIVE_HEAPS: {heaps}"
  IO.println "PROJECTED_ASSIGNMENT_COMPILER_PROFILE_FORWARD_PASS"

end Tests.SourceCoreSelectedProjectedAssignment
