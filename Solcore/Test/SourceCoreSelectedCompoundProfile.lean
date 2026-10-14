import Solcore.Test.SourceCoreSelectedCompoundSourceFirst
import Solcore.Test.SourceCoreUnifiedCorpusSupport

set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedCompound
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering

private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def word (n : Nat) : SourceCorePublicValues.Value := .word (Word.ofNatModulo n)

private def runProgram (workspace : Workspace.RawWorkspace) (names : List String) (cacheSize : Nat)
    (run : ∀ artifact : SourceCoreExecution.Artifact, SourceCoreExecution.Session artifact →
      List SourceCoreExecution.Key → IO Unit) : IO Unit := do
  match checked : checkProgram workspace options.checkingFuel with
  | .error errors => throw (IO.userError s!"compound checking: {reprStr errors}")
  | .ok program =>
    let roots ← names.mapM (SourceCoreUnifiedCorpusSupport.key program)
    match generated : SourceCoreCompiler.compileChecked program
        (roots.map (fun key => .declaration key.declaration)) options with
    | .error error => throw (IO.userError s!"compound compilation: {reprStr error}")
    | .ok source =>
      match present : source.artifact? with
      | none => throw (IO.userError "compound cached artifact missing")
      | some cached =>
        have sameProgram : cached.sourceProgram = program :=
          (source.artifact_fields present).1.trans (SourceCoreCompiler.compileChecked_program generated)
        have original : checkProgram workspace options.checkingFuel = .ok cached.sourceProgram := by
          rw [sameProgram]; exact checked
        let some profile := SelectedCompilationCompilerStaticProfile.validateCheckedProfile cached original
          | throw (IO.userError "compound selected profile rejected")
        require (cached.indexed.base.functions.length == cacheSize && profile.table.rows.length == cacheSize)
          "compound actual cache/table size changed"
        match preparedRecipe : SourceCoreIndexedSession.Recipe.prepare cached with
        | .error error => throw (IO.userError s!"compound recipe: {reprStr error}")
        | .ok recipe =>
          match entries : cached.indexed.entries with
          | [] => throw (IO.userError "compound root entry missing")
          | entry :: _ =>
            have _issued : Nonempty (SelectedCompilationCertifiedPublicSession.Issued recipe) := by
              have same := SourceCoreIndexedSession.Recipe.prepare_compiled preparedRecipe
              cases same
              exact SelectedCompilationCertifiedPublicSession.of_checked_profile profile preparedRecipe
                (entry := entry) (by rw [entries]; simp) original
            let prepared ← get "compound public preparation" (SourceCoreExecution.prepare source)
            let artifact ← prepared.open
            let bootstrap ← artifact.bootstrap
            let .ready initial := bootstrap.resume 100000
              | throw (IO.userError "compound bootstrap missing")
            IO.println s!"COMPOUND_CACHE: {names}; cache{cached.indexed.base.functions.length}/table{profile.table.rows.length}; heap{initial.heapSize}"
            run artifact initial roots


private def success {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreExecution.Key)
    (arguments : List SourceCorePublicValues.Value) (value : SourceCorePublicValues.Value) :
    IO (SourceCoreExecution.Session artifact) := do
  let started ← get "compound startup" (session.start key arguments)
  let .outOfFuel suspended ← started.resume 0 0
    | throw (IO.userError "compound zero fuel did not suspend")
  let .succeeded completed ← suspended.resume 100000 1000
    | throw (IO.userError "compound success missing")
  require (completed.value == value) "compound result changed"
  pure completed.session

private def failure {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreExecution.Key)
    (arguments : List SourceCorePublicValues.Value) (operator : Syntax.ValueAssignOp) :
    IO (SourceCoreExecution.Session artifact) := do
  let started ← get "compound fault startup" (session.start key arguments)
  let .failed reason after ← started.resume 100000 1000
    | throw (IO.userError "compound absent target did not fail")
  let some diagnostic ← get "compound diagnostic" (after.diagnostic key reason)
    | throw (IO.userError "compound diagnostic missing")
  require (match diagnostic.error with
    | .invalidAssignmentOperands actual none (some .word) => actual == operator
    | _ => false) "compound operand diagnostic changed"
  pure after

private def sourceFirst : IO Unit := do
  let fixture ← compileFixture
  let observed ← observeProgram fixture
  let some profile := SelectedCompilationCompilerStaticProfile.validateCheckedProfile
      fixture.recipe.compiled fixture.checked
    | throw (IO.userError "compound original selected profile rejected")
  require (fixture.recipe.compiled.indexed.base.functions.length == 3 && profile.table.rows.length == 3)
    "compound original cache/table changed"
  let started ← observeStarted fixture observed.addRow.original.key [word 37, word 5]
  have _sourceFirst := initial_from_source fixture observed profile started
  let .outOfFuel suspended ← started.call.checkpoint.resume 0 0
    | throw (IO.userError "compound initial zero fuel did not suspend")
  let .succeeded first ← suspended.resume 100000 1000
    | throw (IO.userError "compound initial addition failed")
  require (first.value == word 42) "compound initial sum changed"
  let second ← success first.session observed.divideRow.original.key [word 42, word 0] (word 0)
  let third ← failure second observed.missingRow.original.key [word 0] .divide
  let fourth ← success third observed.addRow.original.key [word 20, word 22] (word 42)
  require ([started.session.heapSize, first.session.heapSize, second.heapSize, third.heapSize, fourth.heapSize]
    == [4, 10, 16, 22, 28]) "compound native stores changed"
  IO.println s!"COMPOUND_SOURCE_HEAPS: {[started.session.heapSize, first.session.heapSize, second.heapSize, third.heapSize, fourth.heapSize]}"

def headerWorkspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function post(limit: Word) returns (Word) { let count: Word = 0; for (let i: Word = 0; limit > i; i += 1) { count += 1; continue; } return count; }",
    "function stop() returns (Word) { let missing: Word; for (let i: Word = 0; true; missing += 1) { break; } return 7; }",
    "function failedPost() returns (Word) { let missing: Word; for (let i: Word = 0; true; missing += 1) { continue; } return 7; }",
    "function initialize(value: Word) returns (Word) { for (value += 1; false; value += 1) { } return value; }"
  ]}] }

/-- The runtime companion retains one captured cell across successful calls and
an operand fault after an indirect RHS call mutates that captured cell. -/
def captureWorkspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function make(value: Word) returns (function(Word) returns (Word)) { return lam(next: Word) -> Word { value += next; return value; }; }",
    "function missingRhs(action: function(Word) returns (Word)) returns (Word) { let missing: Word; missing += action(9); return missing; }"
  ]}] }

private def handleSuccess {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (handle : SourceCorePublicValues.Handle)
    (argument expected : SourceCorePublicValues.Value) : IO (SourceCoreExecution.Session artifact) := do
  let started ← get "compound captured startup" (session.startHandlePacked handle argument)
  let .succeeded completed ← started.resume 100000 1000
    | throw (IO.userError "compound captured invocation failed")
  require (completed.value == expected) "compound captured result changed"
  pure completed.session

def run : IO Unit := do
  sourceFirst
  runProgram headerWorkspace ["post", "stop", "failedPost", "initialize"] 4 fun _ initial keys => do
    let [post, stop, failedPost, initializer] := keys
      | throw (IO.userError "compound header keys changed")
    let first ← success initial post [word 3] (word 3)
    let second ← success first stop [] (word 7)
    let third ← failure second failedPost [] .add
    let fourth ← success third post [word 2] (word 2)
    let fifth ← success fourth initializer [word 41] (word 42)
    require ([initial.heapSize, first.heapSize, second.heapSize, third.heapSize, fourth.heapSize, fifth.heapSize]
      == [5, 15, 22, 29, 39, 43]) "compound header native stores changed"
    IO.println s!"COMPOUND_HEADER_HEAPS: {[initial.heapSize, first.heapSize, second.heapSize, third.heapSize, fourth.heapSize, fifth.heapSize]}"
  runProgram captureWorkspace ["make", "missingRhs"] 2 fun _ initial keys => do
    let [make, missingRhs] := keys | throw (IO.userError "compound capture keys changed")
    let pending ← get "compound factory startup" (initial.start make [word 10])
    let .succeeded made ← pending.resume 100000 1000
      | throw (IO.userError "compound factory failed")
    let .function handle := made.value | throw (IO.userError "compound captured handle missing")
    let first ← handleSuccess made.session handle (word 7) (word 17)
    let second ← handleSuccess first handle (word 20) (word 37)
    let failed ← failure second missingRhs [.function handle] .add
    let reused ← handleSuccess failed handle (word 0) (word 46)
    require ([initial.heapSize, made.session.heapSize, first.heapSize, second.heapSize, failed.heapSize, reused.heapSize]
      == [3, 6, 9, 12, 21, 24]) "compound captured RHS native stores changed"
    IO.println s!"COMPOUND_CAPTURE_HEAPS: {[initial.heapSize, made.session.heapSize, first.heapSize, second.heapSize, failed.heapSize, reused.heapSize]}"
  IO.println "COMPOUND_COMPILER_PROFILE_FORWARD_PASS"

end Tests.SourceCoreSelectedCompound
