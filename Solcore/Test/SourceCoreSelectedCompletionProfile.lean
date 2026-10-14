import Solcore.Test.SourceCoreSelectedCompletionSourceFirst
import Solcore.Test.SourceCoreUnifiedCorpusSupport
import Solcore.SourceSemantics.CoreLowering.AcceptedCompilerBodyCompletion

set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedCompletion
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering

private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def word (n : Nat) : SourceCorePublicValues.Value := .word (Word.ofNatModulo n)

private def runProgram (workspace : Workspace.RawWorkspace) (names : List String) (cacheSize : Nat)
    (run : ∀ artifact : SourceCoreExecution.Artifact, SourceCoreExecution.Session artifact →
      List SourceCoreExecution.Key → IO Unit) : IO Unit := do
  match checked : checkProgram workspace options.checkingFuel with
  | .error errors => throw (IO.userError s!"completion checking: {reprStr errors}")
  | .ok program =>
    let roots ← names.mapM (SourceCoreUnifiedCorpusSupport.key program)
    match generated : SourceCoreCompiler.compileChecked program
        (roots.map (fun key => .declaration key.declaration)) options with
    | .error error => throw (IO.userError s!"completion compilation: {reprStr error}")
    | .ok source =>
      match present : source.artifact? with
      | none => throw (IO.userError "completion cached artifact missing")
      | some cached =>
        have sameProgram : cached.sourceProgram = program :=
          (source.artifact_fields present).1.trans (SourceCoreCompiler.compileChecked_program generated)
        have original : checkProgram workspace options.checkingFuel = .ok cached.sourceProgram := by
          rw [sameProgram]; exact checked
        let some profile := SelectedCompilationCompilerStaticProfile.validateCheckedProfile cached original
          | throw (IO.userError "completion selected profile rejected")
        require (cached.indexed.base.functions.length == cacheSize && profile.table.rows.length == cacheSize)
          "completion actual cache/table size changed"
        match preparedRecipe : SourceCoreIndexedSession.Recipe.prepare cached with
        | .error error => throw (IO.userError s!"completion recipe: {reprStr error}")
        | .ok recipe =>
          match entries : cached.indexed.entries with
          | [] => throw (IO.userError "completion root entry missing")
          | entry :: _ =>
            have _issued : Nonempty (SelectedCompilationCertifiedPublicSession.Issued recipe) := by
              have same := SourceCoreIndexedSession.Recipe.prepare_compiled preparedRecipe
              cases same
              exact SelectedCompilationCertifiedPublicSession.of_checked_profile profile preparedRecipe
                (entry := entry) (by rw [entries]; simp) original
            let prepared ← get "completion public preparation" (SourceCoreExecution.prepare source)
            let artifact ← prepared.open
            let bootstrap ← artifact.bootstrap
            let .ready initial := bootstrap.resume 100000
              | throw (IO.userError "completion bootstrap missing")
            IO.println s!"BODY_CACHE: {names}; cache{cached.indexed.base.functions.length}/table{profile.table.rows.length}; heap{initial.heapSize}"
            run artifact initial roots

private def success {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreExecution.Key)
    (arguments : List SourceCorePublicValues.Value) (value : SourceCorePublicValues.Value) :
    IO (SourceCoreExecution.Session artifact) := do
  let started ← get "completion startup" (session.start key arguments)
  let .outOfFuel suspended ← started.resume 0 0
    | throw (IO.userError "completion zero fuel did not suspend")
  let .succeeded completed ← suspended.resume 100000 1000
    | throw (IO.userError "completion success missing")
  require (completed.value == value) "completion result changed"
  pure completed.session

private def failure {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreExecution.Key)
    (arguments : List SourceCorePublicValues.Value) : IO (SourceCoreExecution.Session artifact) := do
  let started ← get "completion fault startup" (session.start key arguments)
  let .failed reason after ← started.resume 100000 1000
    | throw (IO.userError "completion absent read did not fail")
  let some diagnostic ← get "completion diagnostic" (after.diagnostic key reason)
    | throw (IO.userError "completion diagnostic missing")
  require (match diagnostic.error with | .uninitializedLocal _ => true | _ => false)
    "completion failure reason changed"
  pure after

def casesWorkspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function letUnit() { let value: Word = 37; }",
    "function missing() returns (Word) { let value: Word; value }",
    "function reuse(value: Word) returns (Word) { value }",
    "function discarded(value: Word) returns (Word) { { value; } return 41; }",
    "function conditionFault(flag: Bool) returns (Word) { if (flag) { let value: Word; return value; } else { return 7; } }",
    "function matchReturn(value: Word) returns (Word) { match (value) { case 0 { return 41; } default { return 7; } } }",
    "function blockReturn(value: Word) returns (Word) { { let copy: Word = value; return copy; } }"
  ]}]
}

def factoryWorkspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{path := "main.solc", content :=
    "function make(value: Word) returns (function(Word) returns ()) { return lam(next: Word) -> Unit { value = next; }; }"}]
}

private def expected : Example → SourceCorePublicValues.Value
  | .branch _ | .tail => word 37
  | .unit | .letUnit => .unit

private def nativeHeaps : Example → List Nat
  | .branch true => [2, 11]
  | .branch false => [2, 8]
  | .tail => [2, 5]
  | .unit => [2, 2]
  | .letUnit => [2, 8]

private def sourceFirst (spec : Example) : IO Unit := do
  let fixture ← fixture spec
  require (fixture.recipe.compiled.indexed.base.functions.length == 1 && fixture.profile.table.rows.length == 1)
    "completion independent cache/table changed"
  require (AcceptedCompilerBodyProfile.validate fixture.named.specialized.function.typedBody
    (fun _ => True)).isSome "completion actual body profile rejected"
  match spec with
  | .unit => pure ()
  | _ => require (AcceptedCompilerBodyProfile.validate fixture.named.specialized.function.typedBody
      (fun _ => False)).isNone "completion missing expression coverage accepted"
  let source := fixture.named.specialized.function.typedBody
  let statements := source.roots.filterMap fun | .statement id => some id | _ => none
  require (AcceptedCompilerBodyCompletion.finish? source spec.resultType true statements).isSome
    "completion actual raw result refused"
  match spec with
  | .tail =>
    require (AcceptedCompilerBodyCompletion.finish? source .bool true statements).isNone
      "completion wrong raw tail result accepted"
    require (AcceptedCompilerBodyCompletion.finish? source .word true (statements ++ statements)).isNone
      "completion nonfinal bare expression accepted"
  | .unit | .letUnit =>
    require (AcceptedCompilerBodyCompletion.finish? source .word true statements).isNone
      "completion non-Unit fallthrough accepted"
  | .branch _ => pure ()
  let started ← observeStarted fixture
  have _sourceFirst := from_source fixture started
  let .outOfFuel suspended ← started.call.checkpoint.resume 0 0
    | throw (IO.userError "completion initial zero fuel did not suspend")
  let .succeeded completed ← suspended.resume 100000 1000
    | throw (IO.userError "completion independent Source execution failed")
  require (completed.value == expected spec) "completion independent result changed"
  require ([started.session.heapSize, completed.session.heapSize] == nativeHeaps spec)
    "completion independent native stores changed"
  IO.println s!"COMPLETION_SOURCE_HEAPS: {reprStr spec}; {[started.session.heapSize, completed.session.heapSize]}"

/-- The profile expansion does not change the parser's nested-block policy. -/
private def parserBoundaries : IO Unit := do
  for content in [
      "function bad(value: Word) returns (Word) { { value } return 41; }",
      "function bad() returns (function(Word) returns (Word)) { return lam(value: Word) -> Word { value }; }"] do
    let workspace : Workspace.RawWorkspace := {
      entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := content}]}
    match checkProgram workspace options.checkingFuel with
    | .error errors =>
      require (errors.any fun
        | .loading (.sourceDiagnostics _ _ diagnostics) => diagnostics.any fun diagnostic =>
            match diagnostic.kind with
            | .constraintViolation .expressionRequiresSemicolon => true
            | _ => false
        | _ => false) "completion nested semicolon diagnostic changed"
    | .ok _ => throw (IO.userError "completion nested semicolon policy changed")

/-- A stopped structured head still emits its outer suffix; direct return does not. -/
private def completionSuffixGuards : IO Unit := do
  for (content, stopped) in [
      ("function suffix(flag: Bool, value: Word) returns (Word) { if (flag) { return value; } else { return value; } value }", true),
      ("function suffix(value: Word) returns (Word) { return value; value }", false)] do
    let workspace : Workspace.RawWorkspace := {
      entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := content}]}
    let .ok checked := checkProgram workspace options.checkingFuel
      | throw (IO.userError "completion suffix guard checking failed")
    let [function] := checked.functions
      | throw (IO.userError "completion suffix guard function changed")
    let source := function.typedBody
    let [head, tail] := source.roots.filterMap fun | .statement id => some id | _ => none
      | throw (IO.userError "completion suffix guard original roots changed")
    require (AcceptedCompilerBodyCompletion.finish? source .word true [head, tail]).isSome
      "completion original stopped suffix refused"
    let duplicated := (AcceptedCompilerBodyCompletion.finish? source .word true [head, tail, tail]).isSome
    require (duplicated == !stopped)
      "completion emitted versus omitted bare suffix boundary changed"

def run : IO Unit := do
  completionSuffixGuards
  parserBoundaries
  sourceFirst (.branch true)
  sourceFirst (.branch false)
  sourceFirst .tail
  sourceFirst .unit
  sourceFirst .letUnit
  runProgram casesWorkspace ["letUnit", "missing", "reuse", "discarded", "conditionFault", "matchReturn", "blockReturn"] 7 fun _ initial keys => do
    let [letUnit, missing, reuse, discarded, conditionFault, matchReturn, blockReturn] := keys
      | throw (IO.userError "completion corpus keys changed")
    let unitResult ← success initial letUnit [] .unit
    let missingResult ← failure unitResult missing []
    let reused ← success missingResult reuse [word 19] (word 19)
    let discardedResult ← success reused discarded [word 37] (word 41)
    let branchMissing ← failure discardedResult conditionFault [.bool true]
    let branchReused ← success branchMissing conditionFault [.bool false] (word 7)
    let matched ← success branchReused matchReturn [word 0] (word 41)
    let defaulted ← success matched matchReturn [word 1] (word 7)
    let blocked ← success defaulted blockReturn [word 37] (word 37)
    require ([initial.heapSize, unitResult.heapSize, missingResult.heapSize, reused.heapSize,
      discardedResult.heapSize, branchMissing.heapSize, branchReused.heapSize, matched.heapSize,
      defaulted.heapSize, blocked.heapSize] == [8, 11, 14, 17, 20, 26, 29, 35, 41, 47])
      "completion control and fault-continuation stores changed"
    IO.println s!"COMPLETION_CASE_HEAPS: {[initial.heapSize, unitResult.heapSize, missingResult.heapSize, reused.heapSize, discardedResult.heapSize, branchMissing.heapSize, branchReused.heapSize, matched.heapSize, defaulted.heapSize, blocked.heapSize]}"
  runProgram factoryWorkspace ["make"] 1 fun _ initial keys => do
    let [key] := keys | throw (IO.userError "completion factory key")
    let checkpoint ← get "completion factory startup" (initial.start key [word 11])
    let .succeeded made ← checkpoint.resume 100000 1000
      | throw (IO.userError "completion factory failed")
    let .function handle := made.value | throw (IO.userError "completion factory handle missing")
    let firstCheckpoint ← get "completion captured startup" (made.session.startHandlePacked handle (word 12))
    let .succeeded first ← firstCheckpoint.resume 100000 1000
      | throw (IO.userError "completion captured invocation failed")
    require (first.value == .unit) "completion captured Unit result changed"
    let nextCheckpoint ← get "completion captured reuse" (first.session.startHandlePacked handle (word 23))
    let .succeeded next ← nextCheckpoint.resume 100000 1000
      | throw (IO.userError "completion captured reuse failed")
    require (next.value == .unit) "completion captured reuse result changed"
    require ([initial.heapSize, made.session.heapSize, first.session.heapSize, next.session.heapSize] == [2, 5, 8, 11])
      "completion captured Unit fallthrough stores changed"
    IO.println s!"COMPLETION_CAPTURE_HEAPS: {[initial.heapSize, made.session.heapSize, first.session.heapSize, next.session.heapSize]}"
  IO.println "COMPLETION_COMPILER_PROFILE_FORWARD_PASS"

end Tests.SourceCoreSelectedCompletion
