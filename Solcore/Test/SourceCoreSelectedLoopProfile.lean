import Solcore.Test.SourceCoreSelectedLoopSourceFirst
import Solcore.Test.SourceCoreUnifiedCorpusSupport

set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedLoop
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering

private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def word (n : Nat) : SourceCorePublicValues.Value := .word (Word.ofNatModulo n)

private def runProgram (workspace : Workspace.RawWorkspace) (names : List String) (cacheSize : Nat)
    (run : ∀ artifact : SourceCoreExecution.Artifact, SourceCoreExecution.Session artifact →
      List SourceCoreExecution.Key → IO Unit) : IO Unit := do
  match checked : checkProgram workspace options.checkingFuel with
  | .error errors => throw (IO.userError s!"loop control checking: {reprStr errors}")
  | .ok program =>
    let roots ← names.mapM (SourceCoreUnifiedCorpusSupport.key program)
    match generated : SourceCoreCompiler.compileChecked program
        (roots.map (fun key => .declaration key.declaration)) options with
    | .error error => throw (IO.userError s!"loop control compilation: {reprStr error}")
    | .ok source =>
      match present : source.artifact? with
      | none => throw (IO.userError "loop control cached artifact missing")
      | some cached =>
        have sameProgram : cached.sourceProgram = program :=
          (source.artifact_fields present).1.trans (SourceCoreCompiler.compileChecked_program generated)
        have original : checkProgram workspace options.checkingFuel = .ok cached.sourceProgram := by
          rw [sameProgram]; exact checked
        let some profile := SelectedCompilationCompilerStaticProfile.validateCheckedProfile cached original
          | throw (IO.userError "loop control selected profile rejected")
        require (cached.indexed.base.functions.length == cacheSize && profile.table.rows.length == cacheSize)
          "loop control actual cache/table size changed"
        match preparedRecipe : SourceCoreIndexedSession.Recipe.prepare cached with
        | .error error => throw (IO.userError s!"loop control recipe: {reprStr error}")
        | .ok recipe =>
          match entries : cached.indexed.entries with
          | [] => throw (IO.userError "loop control root entry missing")
          | entry :: _ =>
            have _issued : Nonempty (SelectedCompilationCertifiedPublicSession.Issued recipe) := by
              have same := SourceCoreIndexedSession.Recipe.prepare_compiled preparedRecipe
              cases same
              exact SelectedCompilationCertifiedPublicSession.of_checked_profile profile preparedRecipe
                (entry := entry) (by rw [entries]; simp) original
            let prepared ← get "loop control public preparation" (SourceCoreExecution.prepare source)
            let artifact ← prepared.open
            let bootstrap ← artifact.bootstrap
            let .ready initial := bootstrap.resume 100000
              | throw (IO.userError "loop control bootstrap missing")
            IO.println s!"BODY_CACHE: {names}; cache{cached.indexed.base.functions.length}/table{profile.table.rows.length}; heap{initial.heapSize}"
            run artifact initial roots

private def success {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreExecution.Key)
    (arguments : List SourceCorePublicValues.Value) (value : SourceCorePublicValues.Value) :
    IO (SourceCoreExecution.Session artifact) := do
  let started ← get "loop control startup" (session.start key arguments)
  let .outOfFuel suspended ← started.resume 0 0
    | throw (IO.userError "loop control zero fuel did not suspend")
  let .succeeded completed ← suspended.resume 100000 1000
    | throw (IO.userError "loop control success missing")
  require (completed.value == value) "loop control result changed"
  pure completed.session

private def failure {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreExecution.Key)
    (arguments : List SourceCorePublicValues.Value) : IO (SourceCoreExecution.Session artifact) := do
  let started ← get "loop control fault startup" (session.start key arguments)
  let .failed reason after ← started.resume 100000 1000
    | throw (IO.userError "loop control absent read did not fail")
  let some diagnostic ← get "loop control diagnostic" (after.diagnostic key reason)
    | throw (IO.userError "loop control diagnostic missing")
  require (match diagnostic.error with | .uninitializedLocal _ => true | _ => false)
    "loop control failure reason changed"
  pure after

def originalWorkspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "function whileCount(start: Word) returns (Word, Word) {",
    "  let remaining: Word = start; let count: Word = 0;",
    "  while (remaining > 0) { let copy: Word = remaining; remaining = remaining - 1; count = count + 1; }",
    "  return (remaining, count);",
    "}",
    "function forOrder(limit: Word) returns (Word, Word) {",
    "  let count: Word = 0;",
    "  for (let i: Word = 0; limit > i; i = i + 1) {",
    "    count = count + 1; if (i == 1) { continue; } count = count + 10;",
    "  } return (count, limit);",
    "}",
    "function forBreak(limit: Word) returns (Word) {",
    "  let count: Word = 0; for (let i: Word = 0; limit > i; i = i + 1) { count = count + 1; break; }",
    "  return count;",
    "}",
    "function initializerScope(limit: Word) returns (Word) {",
    "  let i: Word = 17; for (let i: Word = 0; limit > i; i = i + 1) { } return i;",
    "}",
    "function postScope(limit: Word) returns (Word) {",
    "  let copy: Word = 99;",
    "  for (let i: Word = 0; limit > i; let copy: Word = i, i = copy + 1) { } return copy;",
    "}",
    "function nested() returns (Word, Word) {",
    "  let outer: Word = 2; let count: Word = 0; while (outer > 0) {",
    "    let inner: Word = 2; while (inner > 0) {",
    "      inner = inner - 1; if (inner == 1) { continue; } count = count + 1; break;",
    "    } outer = outer - 1;",
    "  } return (count, outer);",
    "}",
    "function returnInside(limit: Word) returns (Word) {",
    "  let remaining: Word = limit; while (remaining > 0) { return remaining; } return 0;",
    "}",
    "function absentCondition() returns (Word) { let missing: Bool; while (missing) { return 17; } return 0; }",
    "function absentPost() returns (Word) { let missing: Word; for (let i: Word = 0; true; i = missing) { continue; } return 0; }",
    "function absentInitializer() returns (Word) { let missing: Word; for (let i: Word = missing; true; i = i + 1) { break; } return 0; }",
    "function spin() { while (true) { continue; } }",
    "function compound(limit: Word) { for (let i: Word = 0; limit > i; i += 1) { } }"
  ] }]
}

private def checkBoundary (name : String) (acceptedProfile : Bool) : IO Unit := do
  match checked : checkProgram originalWorkspace options.checkingFuel with
  | .error errors => throw (IO.userError (reprStr errors))
  | .ok program =>
    let key ← SourceCoreUnifiedCorpusSupport.key program name
    match generated : SourceCoreCompiler.compileChecked program [.declaration key.declaration] options with
    | .error error => throw (IO.userError (reprStr error))
    | .ok source =>
      match present : source.artifact? with
      | none => throw (IO.userError "loop boundary artifact missing")
      | some cached =>
        have sameProgram : cached.sourceProgram = program :=
          (source.artifact_fields present).1.trans (SourceCoreCompiler.compileChecked_program generated)
        have original : checkProgram originalWorkspace options.checkingFuel = .ok cached.sourceProgram := by
          rw [sameProgram]; exact checked
        require ((SelectedCompilationCompilerStaticProfile.validateCheckedProfile cached original).isSome == acceptedProfile)
          s!"loop profile boundary changed: {name}"
        if name == "compound" then
          let some named := cached.indexed.base.functions.head?
            | throw (IO.userError "compound loop cached row missing")
          require (AcceptedCompilerBodyProfile.validate named.specialized.function.typedBody (fun _ => True)).isNone
            "compound header profile restriction changed"

private def checkMissingInitializer (fixture : Fixture) : IO Unit := do
  let source := fixture.named.specialized.function.typedBody
  require (AcceptedCompilerBodyProfile.validate source (fun _ => True)).isSome "loop actual source body profile"
  require (AcceptedCompilerBodyProfile.validate source (fun id => id ≠ fixture.shape.first.id)).isNone
    "loop initializer expression coverage was not required"
  let dirty := {source with nodes := source.nodes.map fun
    | .statement node => if node.id == fixture.shape.loop.id then .statement {node with
        form := .forLoop [.letDecl {fixture.shape.copy with scheme := {fixture.shape.copy.scheme with quantified := [⟨999⟩]}}
          (some fixture.shape.first.id)] fixture.shape.condition.id [] [fixture.shape.breaking.id]}
      else .statement node
    | node => node}
  require (AcceptedCompilerBodyProfile.validate dirty (fun _ => True)).isNone "loop polymorphic header was accepted"

def run : IO Unit := do
  checkBoundary "spin" true
  checkBoundary "compound" false
  let fixture ← fixture
  checkMissingInitializer fixture
  let started ← observeStarted fixture
  have _sourceFirst := from_source fixture started
  let .outOfFuel suspended ← started.call.checkpoint.resume 0 0
    | throw (IO.userError "loop initial zero fuel did not suspend")
  let .succeeded stopped ← suspended.resume 100000 1000
    | throw (IO.userError "loop source-first break did not complete")
  require (stopped.value == .word seed) "loop independent Source result changed"
  require ([started.session.heapSize, stopped.session.heapSize] == [2, 9]) "loop Source-first native heap changed"
  IO.println s!"LOOP_SOURCE_HEAPS: {[started.session.heapSize, stopped.session.heapSize]}"
  runProgram originalWorkspace
    ["whileCount", "forOrder", "forBreak", "initializerScope", "postScope", "nested", "returnInside",
      "absentCondition", "absentPost", "absentInitializer"] 10 fun _ initial keys => do
    let [whileKey, order, breaking, initialScope, postScope, nested, returned, missingCondition, missingPost, missingInitial] := keys
      | throw (IO.userError "loop original key order changed")
    let counted ← success initial whileKey [word 3] (.product (word 0) (word 3))
    let ordered ← success counted order [word 3] (.product (word 23) (word 3))
    let broken ← success ordered breaking [word 3] (word 1)
    let restored ← success broken initialScope [word 2] (word 17)
    let postRestored ← success restored postScope [word 3] (word 99)
    let nestedResult ← success postRestored nested [] (.product (word 2) (word 0))
    let early ← success nestedResult returned [word 3] (word 3)
    let conditionFault ← failure early missingCondition []
    let postFault ← failure conditionFault missingPost []
    let initializerFault ← failure postFault missingInitial []
    let continued ← success initializerFault breaking [word 3] (word 1)
    let heaps := [initial.heapSize, counted.heapSize, ordered.heapSize, broken.heapSize,
      restored.heapSize, postRestored.heapSize, nestedResult.heapSize, early.heapSize, conditionFault.heapSize,
      postFault.heapSize, initializerFault.heapSize, continued.heapSize]
    require (heaps == [11, 30, 40, 50, 60, 79, 94, 101, 105, 112, 115, 125]) "loop original native heap sequence changed"
    IO.println s!"LOOP_CORPUS_HEAPS: {heaps}"
  IO.println "LOOP_COMPILER_PROFILE_FORWARD_PASS: original source corpus and cache10/table10; actual initializer/post scopes; break/continue and nested loops; independent Source initializer-break-return trace into the closed public endpoint; exact outcomes, fault prefixes and subsequent session reuse; zero-fuel resumption"

end Tests.SourceCoreSelectedLoop
