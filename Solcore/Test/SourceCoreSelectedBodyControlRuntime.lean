import Solcore.Test.SourceCoreSelectedBodyControlSourceFirst
import Solcore.Test.SourceCoreSelectedCompositeProfile

set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedBodyControl
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering

private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def word (n : Nat) : SourceCorePublicValues.Value := .word (Word.ofNatModulo n)

private def runProgram (workspace : Workspace.RawWorkspace) (names : List String) (cacheSize : Nat)
    (run : ∀ artifact : SourceCoreExecution.Artifact, SourceCoreExecution.Session artifact →
      List SourceCoreExecution.Key → IO Unit) : IO Unit := do
  match checked : checkProgram workspace options.checkingFuel with
  | .error errors => throw (IO.userError s!"body control checking: {reprStr errors}")
  | .ok program =>
    let roots ← names.mapM (SourceCoreUnifiedCorpusSupport.key program)
    match generated : SourceCoreCompiler.compileChecked program
        (roots.map (fun key => .declaration key.declaration)) options with
    | .error error => throw (IO.userError s!"body control compilation: {reprStr error}")
    | .ok source =>
      match present : source.artifact? with
      | none => throw (IO.userError "body control cached artifact missing")
      | some cached =>
        have sameProgram : cached.sourceProgram = program :=
          (source.artifact_fields present).1.trans (SourceCoreCompiler.compileChecked_program generated)
        have original : checkProgram workspace options.checkingFuel = .ok cached.sourceProgram := by
          rw [sameProgram]; exact checked
        let some profile := SelectedCompilationCompilerStaticProfile.validateCheckedProfile cached original
          | throw (IO.userError "body control selected profile rejected")
        require (cached.indexed.base.functions.length == cacheSize && profile.table.rows.length == cacheSize)
          "body control actual cache/table size changed"
        match preparedRecipe : SourceCoreIndexedSession.Recipe.prepare cached with
        | .error error => throw (IO.userError s!"body control recipe: {reprStr error}")
        | .ok recipe =>
          match entries : cached.indexed.entries with
          | [] => throw (IO.userError "body control root entry missing")
          | entry :: _ =>
            have _issued : Nonempty (SelectedCompilationCertifiedPublicSession.Issued recipe) := by
              have same := SourceCoreIndexedSession.Recipe.prepare_compiled preparedRecipe
              cases same
              exact SelectedCompilationCertifiedPublicSession.of_checked_profile profile preparedRecipe
                (entry := entry) (by rw [entries]; simp) original
            let prepared ← get "body control public preparation" (SourceCoreExecution.prepare source)
            let artifact ← prepared.open
            let bootstrap ← artifact.bootstrap
            let .ready initial := bootstrap.resume 100000
              | throw (IO.userError "body control bootstrap missing")
            IO.println s!"BODY_CACHE: {names}; cache{cached.indexed.base.functions.length}/table{profile.table.rows.length}; heap{initial.heapSize}"
            run artifact initial roots

private def success {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreExecution.Key)
    (arguments : List SourceCorePublicValues.Value) (value : SourceCorePublicValues.Value) :
    IO (SourceCoreExecution.Session artifact) := do
  let started ← get "body control startup" (session.start key arguments)
  let .outOfFuel suspended ← started.resume 0 0
    | throw (IO.userError "body control zero fuel did not suspend")
  let .succeeded completed ← suspended.resume 100000 1000
    | throw (IO.userError "body control success missing")
  require (completed.value == value) "body control result changed"
  pure completed.session

private def failure {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreExecution.Key)
    (arguments : List SourceCorePublicValues.Value) : IO (SourceCoreExecution.Session artifact) := do
  let started ← get "body control fault startup" (session.start key arguments)
  let .failed reason after ← started.resume 100000 1000
    | throw (IO.userError "body control absent read did not fail")
  let some diagnostic ← get "body control diagnostic" (after.diagnostic key reason)
    | throw (IO.userError "body control diagnostic missing")
  require (match diagnostic.error with | .uninitializedLocal _ => true | _ => false)
    "body control failure reason changed"
  pure after

private def controlWorkspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function blockReturn(first: Word, second: Word) returns (Word) {",
    "  { return first; } let later: Word = second; return later;",
    "}",
    "function branch(flag: Bool, first: Word, second: Word) returns (Word) {",
    "  let result: Word = first; if (flag) { return first; } else { result = second; } return result;",
    "}",
    "function branchFault(flag: Bool, value: Word) returns (Word) {",
    "  let absent: Word; if (flag) { absent; } else { value; } let later: Word = value; return later;",
    "}"
  ]}] }

private def checkConditionalBoundary : IO Unit := do
  let workspace : Workspace.RawWorkspace := {
    entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content :=
      "function both(flag: Bool, first: Word, second: Word) returns (Word) { if (flag) { return first; } else { return second; } return first; }"}] }
  match checked : checkProgram workspace options.checkingFuel with
  | .error errors => throw (IO.userError s!"body control boundary checking: {reprStr errors}")
  | .ok program =>
    let keys ← ["both"].mapM (SourceCoreUnifiedCorpusSupport.key program)
    match generated : SourceCoreCompiler.compileChecked program
        (keys.map (fun key => .declaration key.declaration)) options with
    | .error error => throw (IO.userError s!"body control boundary compilation: {reprStr error}")
    | .ok source =>
      match present : source.artifact? with
      | none => throw (IO.userError "body control boundary artifact missing")
      | some cached =>
        have sameProgram : cached.sourceProgram = program :=
          (source.artifact_fields present).1.trans (SourceCoreCompiler.compileChecked_program generated)
        have original : checkProgram workspace options.checkingFuel = .ok cached.sourceProgram := by
          rw [sameProgram]; exact checked
        require (cached.indexed.base.functions.any (fun named =>
          named.specialized.function.typedBody.nodes.any (fun node => match node with
            | .statement statement => match statement.form with
              | .ifThen _ _ _ => decide (statement.type ≠ .unit)
              | _ => false
            | _ => false))) "body control boundary lost its original non-unit annotation"
        match SelectedCompilationCompilerStaticProfile.validateCheckedProfile cached original with
        | none => throw (IO.userError "non-unit conditional profile rejected")
        | some _ => pure ()

def run : IO Unit := do
  checkConditionalBoundary
  let fixture ← fixture
  let started ← observeStarted fixture
  have _sourceFirst := from_source fixture started
  let .outOfFuel suspended ← started.call.checkpoint.resume 0 0
    | throw (IO.userError "body control initial discard did not suspend")
  let .succeeded discarded ← suspended.resume 100000 1000
    | throw (IO.userError "body control initial discard did not complete")
  require (discarded.value == .word seed) "body control independent Source result changed"
  require ([started.session.heapSize, discarded.session.heapSize] == [2, 5])
    "body control independent Source heap changed"
  runProgram SourceCoreSelectedCompositeProfile.entryWorkspace ["scoped"] 1 fun _ initial keys => do
    let [key] := keys | throw (IO.userError "body control scoped key changed")
    let selected ← success initial key [.bool true, word 11, word 29] (word 29)
    let unselected ← success selected key [.bool false, word 37, word 41] (word 37)
    require ([initial.heapSize, selected.heapSize, unselected.heapSize] == [2, 17, 32])
      "body control lexical scope restoration changed"
    IO.println s!"BODY_SCOPE_HEAPS: {[initial.heapSize, selected.heapSize, unselected.heapSize]}"
  runProgram SourceCoreSelectedCompositeProfile.basicWorkspace ["discardFailure", "sequence"] 2 fun _ initial keys => do
    let [discard, sequence] := keys | throw (IO.userError "body control sequence keys changed")
    let failed ← failure initial discard [word 11]
    let continued ← success failed sequence [.bool true, word 37, word 41] (.product (word 37) (.bool true))
    require ([initial.heapSize, failed.heapSize, continued.heapSize] == [3, 9, 24])
      "body control discard fault prefix or continuation changed"
    IO.println s!"BODY_DISCARD_HEAPS: {[initial.heapSize, failed.heapSize, continued.heapSize]}"
  runProgram controlWorkspace ["blockReturn", "branch", "branchFault"] 3 fun _ initial keys => do
    let [block, branch, fault] := keys | throw (IO.userError "body control branch keys changed")
    let escaped ← success initial block [word 5, word 7] (word 5)
    let early ← success escaped branch [.bool true, word 11, word 13] (word 11)
    let later ← success early branch [.bool false, word 17, word 19] (word 19)
    let failed ← failure later fault [.bool true, word 23]
    let continued ← success failed fault [.bool false, word 29] (word 29)
    require ([initial.heapSize, escaped.heapSize, early.heapSize, later.heapSize, failed.heapSize, continued.heapSize]
      == [4, 10, 22, 34, 43, 55]) "body control return or branch fault prefix changed"
    IO.println s!"BODY_BRANCH_HEAPS: {[initial.heapSize, escaped.heapSize, early.heapSize, later.heapSize, failed.heapSize, continued.heapSize]}"
  IO.println "SOURCE_FIRST_BODY_CONTROL_PASS: actual checker/compiler/profile/automatic issuer; independent discard Source trace before public execution; closed initial whole-output theorem; block return and lexical restoration; both conditional branches; discarded-read fault prefixes and same-session continuation; zero-fuel resume"

end Tests.SourceCoreSelectedBodyControl
