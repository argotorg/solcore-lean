import Solcore.Test.SourceCoreSelectedMatchSourceFirst
import Solcore.Test.SourceCoreUnifiedCorpusSupport

set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedMatch
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering

private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def word (n : Nat) : SourceCorePublicValues.Value := .word (Word.ofNatModulo n)

private def runProgram (workspace : Workspace.RawWorkspace) (names : List String) (cacheSize : Nat)
    (run : ∀ artifact : SourceCoreExecution.Artifact, SourceCoreExecution.Session artifact →
      List SourceCoreExecution.Key → IO Unit) : IO Unit := do
  match checked : checkProgram workspace options.checkingFuel with
  | .error errors => throw (IO.userError s!"match checking: {reprStr errors}")
  | .ok program =>
    let roots ← names.mapM (SourceCoreUnifiedCorpusSupport.key program)
    match generated : SourceCoreCompiler.compileChecked program
        (roots.map (fun key => .declaration key.declaration)) options with
    | .error error => throw (IO.userError s!"match compilation: {reprStr error}")
    | .ok source =>
      match present : source.artifact? with
      | none => throw (IO.userError "match cached artifact missing")
      | some cached =>
        have sameProgram : cached.sourceProgram = program :=
          (source.artifact_fields present).1.trans (SourceCoreCompiler.compileChecked_program generated)
        have original : checkProgram workspace options.checkingFuel = .ok cached.sourceProgram := by
          rw [sameProgram]; exact checked
        let some profile := SelectedCompilationCompilerStaticProfile.validateCheckedProfile cached original
          | throw (IO.userError "match selected profile rejected")
        require (cached.indexed.base.functions.length == cacheSize && profile.table.rows.length == cacheSize)
          "match actual cache/table size changed"
        if names.contains "early" then
          let earlyKey ← SourceCoreUnifiedCorpusSupport.key program "early"
          let some row := cached.indexed.base.functions.find? (fun row => row.signature.key == earlyKey)
            | throw (IO.userError "match early row missing")
          require (row.specialized.function.typedBody.nodes.any fun
            | .statement node => match node.form with | .matchWith _ => node.type == .word | _ => false
            | _ => false) "match genuine result-valued annotation changed"
        match preparedRecipe : SourceCoreIndexedSession.Recipe.prepare cached with
        | .error error => throw (IO.userError s!"match recipe: {reprStr error}")
        | .ok recipe =>
          match entries : cached.indexed.entries with
          | [] => throw (IO.userError "match root entry missing")
          | entry :: _ =>
            have _issued : Nonempty (SelectedCompilationCertifiedPublicSession.Issued recipe) := by
              have same := SourceCoreIndexedSession.Recipe.prepare_compiled preparedRecipe
              cases same
              exact SelectedCompilationCertifiedPublicSession.of_checked_profile profile preparedRecipe
                (entry := entry) (by rw [entries]; simp) original
            let prepared ← get "match public preparation" (SourceCoreExecution.prepare source)
            let artifact ← prepared.open
            let bootstrap ← artifact.bootstrap
            let .ready initial := bootstrap.resume 100000
              | throw (IO.userError "match bootstrap missing")
            IO.println s!"BODY_CACHE: {names}; cache{cached.indexed.base.functions.length}/table{profile.table.rows.length}; heap{initial.heapSize}"
            run artifact initial roots

private def success {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreExecution.Key)
    (arguments : List SourceCorePublicValues.Value) (value : SourceCorePublicValues.Value) :
    IO (SourceCoreExecution.Session artifact) := do
  let started ← get "match startup" (session.start key arguments)
  let .outOfFuel suspended ← started.resume 0 0
    | throw (IO.userError "match zero fuel did not suspend")
  let .succeeded completed ← suspended.resume 100000 1000
    | throw (IO.userError "match success missing")
  require (completed.value == value) "match result changed"
  pure completed.session

private def failure {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreExecution.Key)
    (arguments : List SourceCorePublicValues.Value) : IO (SourceCoreExecution.Session artifact) := do
  let started ← get "match fault startup" (session.start key arguments)
  let .failed reason after ← started.resume 100000 1000
    | throw (IO.userError "match absent read did not fail")
  let some diagnostic ← get "match diagnostic" (after.diagnostic key reason)
    | throw (IO.userError "match diagnostic missing")
  require (match diagnostic.error with | .uninitializedLocal _ => true | _ => false)
    "match failure reason changed"
  pure after

def casesWorkspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function select(value: Word) returns (Word) { let result: Word = 99; match (value) { case 0 { result = 5; } case 1 { result = 6; } default { result = 7; } } return result; }",
    "function early(value: Word) returns (Word) { match (value) { case 0 { return 5; } default { return 6; } } return 9; }",
    "function tuple(value: (Word, Word)) returns (Word) { let result: Word = 0; match (value) { case (left, right) { result = left + right; } } return result; }",
    "function scrutineeFault() returns (Word) { let missing: Word; match (missing) { case _ {} } return 0; }",
    "function armFault(value: Word) returns (Word) { match (value) { case 0 { let missing: Word; return missing; } default {} } return 7; }",
    "function control(limit: Word) returns (Word) { for (let i: Word = 0; i < limit; i = i + 1) { match (i) { case 0 { continue; } default { break; } } } return limit; }"
  ]}]
}

def factoryWorkspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{path := "main.solc", content :=
    "function make(value: Word) returns (function(Word) returns (Word)) { return lam(next: Word) -> Word { match (next) { case copy { value = copy; } } return value; }; }"}]
}

private def boundaries (fixture : Fixture) : IO Unit := do
  let source := fixture.named.specialized.function.typedBody
  require (AcceptedCompilerBodyProfile.validate source (fun _ => True)).isSome "match original body profile"
  require (AcceptedCompilerBodyProfile.validate source (fun id => id ≠ fixture.shape.initialRead.node.id)).isNone
    "match scrutinee coverage omitted"
  let expressions := source.nodes.filterMap fun | .expression node => some node.id | _ => none
  let roots := [fixture.shape.matchNode.id, fixture.shape.statement.id]
  require (AcceptedCompilerBodySubsetProfile.validate source expressions roots).isSome "match original subset profile"
  require (AcceptedCompilerBodySubsetProfile.validate source
      (expressions.filter (fun id => id != fixture.shape.localRead.node.id)) roots).isNone
    "match actual arm coverage omitted"
  let missing := {fixture.shape.assignment.id with occurrence := {fixture.shape.assignment.id.occurrence with index := 1000000}}
  let missingArm := {source with nodes := source.nodes.map fun
    | .statement node => if node.id == fixture.shape.matchNode.id then .statement {node with
        form := .matchWith {fixture.shape.matching with cases := [{fixture.shape.arm with body := [missing]}]}}
      else .statement node
    | node => node}
  require (AcceptedCompilerBodySubsetProfile.validate missingArm expressions roots).isNone
    "match nonexistent arm statement accepted"
  let missingDefault := {source with nodes := source.nodes.map fun
    | .statement node => if node.id == fixture.shape.matchNode.id then .statement {node with
        form := .matchWith {fixture.shape.matching with defaultBody := some [missing]}}
      else .statement node
    | node => node}
  require (AcceptedCompilerBodySubsetProfile.validate missingDefault expressions roots).isNone
    "match nonexistent default statement accepted"

def run : IO Unit := do
  let fixture ← fixture
  boundaries fixture
  require (fixture.recipe.compiled.indexed.base.functions.length == 1 && fixture.profile.table.rows.length == 1)
    "match original cache/table changed"
  let started ← observeStarted fixture
  have _sourceFirst := from_source fixture started
  let .outOfFuel suspended ← started.call.checkpoint.resume 0 0
    | throw (IO.userError "match initial zero fuel did not suspend")
  let .succeeded first ← suspended.resume 100000 1000
    | throw (IO.userError "match Source-first update failed")
  require (first.value == .word seed) "match Source-first result changed"
  let second ← success first.session fixture.named.signature.key [word 22, word 23] (word 23)
  require ([started.session.heapSize, first.session.heapSize, second.heapSize] == [2, 14, 26])
    "match Source-first native heap changed"
  IO.println s!"MATCH_SOURCE_HEAPS: {[started.session.heapSize, first.session.heapSize, second.heapSize]}"
  runProgram casesWorkspace ["select", "early", "tuple", "scrutineeFault", "armFault", "control"] 6 fun _ initial keys => do
    let [select, early, tuple, scrutineeFault, armFault, control] := keys
      | throw (IO.userError "match corpus keys changed")
    let zero ← success initial select [word 0] (word 5)
    let one ← success zero select [word 1] (word 6)
    let fallback ← success one select [word 2] (word 7)
    let returned ← success fallback early [word 0] (word 5)
    let defaultReturned ← success returned early [word 3] (word 6)
    let unpacked ← success defaultReturned tuple [.product (word 8) (word 9)] (word 17)
    let missing ← failure unpacked scrutineeFault []
    let armMissing ← failure missing armFault [word 0]
    let reused ← success armMissing armFault [word 1] (word 7)
    let controlled ← success reused control [word 3] (word 3)
    require ([initial.heapSize, zero.heapSize, one.heapSize, fallback.heapSize, returned.heapSize, defaultReturned.heapSize, unpacked.heapSize, missing.heapSize, armMissing.heapSize, reused.heapSize, controlled.heapSize] == [7, 16, 25, 34, 40, 46, 61, 64, 73, 79, 92])
      "match corpus native heap changed"
    IO.println s!"MATCH_CASE_HEAPS: {[initial.heapSize, zero.heapSize, one.heapSize, fallback.heapSize, returned.heapSize, defaultReturned.heapSize, unpacked.heapSize, missing.heapSize, armMissing.heapSize, reused.heapSize, controlled.heapSize]}"
  runProgram factoryWorkspace ["make"] 1 fun _ initial keys => do
    let [key] := keys | throw (IO.userError "match factory key")
    let checkpoint ← get "match factory startup" (initial.start key [word 11])
    let .succeeded made ← checkpoint.resume 100000 1000
      | throw (IO.userError "match factory failed")
    let .function handle := made.value | throw (IO.userError "match factory handle missing")
    let firstCheckpoint ← get "match captured startup" (made.session.startHandlePacked handle (word 12))
    let .succeeded first ← firstCheckpoint.resume 100000 1000
      | throw (IO.userError "match captured invocation failed")
    require (first.value == word 12) "match captured mutation changed"
    let nextCheckpoint ← get "match captured reuse" (first.session.startHandlePacked handle (word 23))
    let .succeeded next ← nextCheckpoint.resume 100000 1000
      | throw (IO.userError "match captured reuse failed")
    require (next.value == word 23) "match captured reuse result changed"
    require ([initial.heapSize, made.session.heapSize, first.session.heapSize, next.session.heapSize] == [2, 5, 14, 23])
      "match captured native heap changed"
    IO.println s!"MATCH_CAPTURE_HEAPS: {[initial.heapSize, made.session.heapSize, first.session.heapSize, next.session.heapSize]}"
  IO.println "MATCH_COMPILER_PROFILE_FORWARD_PASS"

end Tests.SourceCoreSelectedMatch
