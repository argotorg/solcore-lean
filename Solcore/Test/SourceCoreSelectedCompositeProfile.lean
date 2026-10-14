import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCheckedPublicSession
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCompilerStaticProfile
import Solcore.Test.SourceCoreUnifiedCorpusSupport

/-! Unchanged source programs exercise the new composite profile through the
actual checker, compiler cache, automatic issuer, and public session runtime. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedCompositeProfile
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering

def entryWorkspace : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "function mutate(flag: Bool, first: Word, second: Word) returns (Word, Bool) {",
    "  let value: Word; value = first; value = second; return (value, flag);",
    "}",
    "function keep<T>(input: T) returns (T) { let stored: T = input; return stored; }",
    "function absent(input: Word) returns (Word) { let value: Word; return value; }",
    "function staged(comptime input: (Word, Bool)) returns (Word, Bool) {",
    "  let stored: (Word, Bool) = input; return stored;",
    "}",
    "function nested(input: (Word, (Bool, Word))) returns (Word, (Bool, Word)) { return input; }",
    "function blocked(input: Word) returns (Word) { { return input; } }",
    "function scoped(flag: Bool, initial: Word, replacement: Word) returns (Word) {",
    "  let value: Word = initial; { let value: Word = replacement; value = initial; }",
    "  if (flag) { value = replacement; } return value;",
    "}",
    "function branchFailure(flag: Bool) returns (Word) {",
    "  let absent: Word; return flag ? absent : absent;",
    "}",
    "function chooseFailure(flag: Bool, value: Word) returns (Word) {",
    "  let absent: Word; return flag ? value : absent;",
    "}",
    "function loop(flag: Bool) { while (flag) { break; } }",
    "function stagedResult(comptime input: Word) returns (comptime<Word>) { return input; }",
    "function literalEvidence() returns (Word) { return 1; }"
  ] }]
  externalLibraries := []
}

def basicWorkspace : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "function sequence(flag: Bool, initial: Word, replacement: Word) returns (Word, Bool) {",
    "  let value: Word; value = initial; let copied: Word = value;",
    "  value = replacement; copied; return (copied, flag);",
    "}",
    "function early(initial: Word, replacement: Word) returns (Word) {",
    "  let value: Word = initial; return value; value = replacement;",
    "}",
    "function initializerFailure(input: Word) returns (Word) {",
    "  let absent: Word; let never: Word = absent; let later: Word = input; return later;",
    "}",
    "function assignmentFailure(input: Word, replacement: Word) returns (Word) {",
    "  let target: Word = input; let absent: Word; target = absent;",
    "  target = replacement; return target;",
    "}",
    "function discardFailure(input: Word) returns (Word) {",
    "  let absent: Word; absent; let later: Word = input; return later;",
    "}",
    "function pairFailure(flag: Bool) returns (Word, Bool) {",
    "  let absent: Word; return (absent, flag);",
    "}",
    "function tail(value: Word) returns (Word) { value }",
    "function empty() { return; }",
    "function fallthrough() { true; }",
    "function unit() { return (); }",
    "function bool() returns (Bool) { return (true); }",
    "function literalEvidence() returns (Word) { return 1; }",
    "function blocked(value: Word) returns (Word) { { return value; } }"
  ] }]
  externalLibraries := []
}

def tupleContent : String := String.intercalate "\n" [
  "function side(x: Word) returns (Word) { return x; }",
  "function fail() returns (Word) { let written = 5; let gap: Word; return gap; }",
  "function triple() returns ((Word, Bool, Word)) { return (side(7), true, 3 + 4); }",
  "function quadruple() returns ((Word, Bool, Word, Bool)) { return (side(11), false, side(13), true); }",
  "function nested() returns (((Word, Bool, Word), Word, Bool)) { return ((side(17), true, 5 + 6), side(19), false); }",
  "function firstFault() returns ((Word, Word, Word)) { return (fail(), side(91), side(92)); }",
  "function laterFault() returns ((Word, Word, Word, Word)) { return (side(23), side(29), fail(), side(99)); }",
  "function singleton() returns (Word) { return (side(31)); }"
]

def tupleWorkspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [],
  mainSources := [{path := "main.solc", content := tupleContent}]
}

def options : SourceCompiler.Options := {
  checkingFuel := 1000, compilationFuel := 1000, specializationBudget := 512
}
private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def word (n : Nat) : SourceCorePublicValues.Value := .word (Word.ofNatModulo n)

private def runProgram (workspace : Workspace.RawWorkspace) (names : List String) (cacheSize : Nat)
    (run : ∀ artifact : SourceCoreExecution.Artifact, SourceCoreExecution.Session artifact →
      List SourceCoreExecution.Key → IO Unit) : IO Unit := do
  match checked : checkProgram workspace options.checkingFuel with
  | .error errors => throw (IO.userError s!"composite checking: {reprStr errors}")
  | .ok program =>
    let roots ← names.mapM (SourceCoreUnifiedCorpusSupport.key program)
    match generated : SourceCoreCompiler.compileChecked program
        (roots.map (fun key => .declaration key.declaration)) options with
    | .error error => throw (IO.userError s!"composite compilation: {reprStr error}")
    | .ok source =>
      match present : source.artifact? with
      | none => throw (IO.userError "composite cached artifact missing")
      | some cached =>
        have sameProgram : cached.sourceProgram = program :=
          (source.artifact_fields present).1.trans (SourceCoreCompiler.compileChecked_program generated)
        have original : checkProgram workspace options.checkingFuel = .ok cached.sourceProgram := by
          rw [sameProgram]; exact checked
        let some profile := SelectedCompilationCompilerStaticProfile.validateCheckedProfile cached original
          | throw (IO.userError "composite selected profile rejected")
        require (cached.indexed.base.functions.length == cacheSize && profile.table.rows.length == cacheSize)
          "composite actual cache/table size changed"
        match preparedRecipe : SourceCoreIndexedSession.Recipe.prepare cached with
        | .error error => throw (IO.userError s!"composite recipe: {reprStr error}")
        | .ok recipe =>
          match entries : cached.indexed.entries with
          | [] => throw (IO.userError "composite root entry missing")
          | entry :: _ =>
            have _issued : Nonempty (SelectedCompilationCertifiedPublicSession.Issued recipe) := by
              have same := SourceCoreIndexedSession.Recipe.prepare_compiled preparedRecipe
              cases same
              exact SelectedCompilationCertifiedPublicSession.of_checked_profile profile preparedRecipe
                (entry := entry) (by rw [entries]; simp) original
            let prepared ← get "composite public preparation" (SourceCoreExecution.prepare source)
            let artifact ← prepared.open
            let bootstrap ← artifact.bootstrap
            let .ready initial := bootstrap.resume 100000
              | throw (IO.userError "composite bootstrap missing")
            IO.println s!"COMPOSITE_CACHE: {names}; cache{cached.indexed.base.functions.length}/table{profile.table.rows.length}; heap{initial.heapSize}"
            run artifact initial roots

private def success {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreExecution.Key)
    (arguments : List SourceCorePublicValues.Value) (value : SourceCorePublicValues.Value) :
    IO (SourceCoreExecution.Session artifact) := do
  let started ← get "composite startup" (session.start key arguments)
  let .outOfFuel suspended ← started.resume 0 0
    | throw (IO.userError "composite zero fuel did not suspend")
  let .succeeded completed ← suspended.resume 100000 1000
    | throw (IO.userError "composite success missing")
  require (completed.value == value) "composite result changed"
  pure completed.session

private def failure {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreExecution.Key)
    (arguments : List SourceCorePublicValues.Value) : IO (SourceCoreExecution.Session artifact) := do
  let started ← get "composite fault startup" (session.start key arguments)
  let .failed reason after ← started.resume 100000 1000
    | throw (IO.userError "composite absent read did not fail")
  let some diagnostic ← get "composite diagnostic" (after.diagnostic key reason)
    | throw (IO.userError "composite diagnostic missing")
  require (match diagnostic.error with | .uninitializedLocal _ => true | _ => false)
    "composite failure reason changed"
  pure after

theorem general_forms (first second third : ExpressionId) :
    AcceptedCompilerExpressionProfile.supportedForm false false false (.group first) = true ∧
    AcceptedCompilerExpressionProfile.supportedForm false false false (.tuple [first]) = true ∧
    AcceptedCompilerExpressionProfile.supportedForm false false false (.tuple [first, second, first]) = true ∧
    AcceptedCompilerExpressionProfile.supportedForm false false false (.conditional first second third) = true := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem narrow_forms (first second third : ExpressionId) :
    AcceptedCompilerExpressionProfile.supportedForm true false false (.group first) = false ∧
    AcceptedCompilerExpressionProfile.supportedForm true false false (.tuple [first, second]) = false ∧
    AcceptedCompilerExpressionProfile.supportedForm true false false (.conditional first second third) = false := by
  exact ⟨rfl, rfl, rfl⟩

def run : IO Unit := do
  runProgram entryWorkspace ["mutate", "chooseFailure", "branchFailure"] 3 fun _ initial keys => do
    let [mutate, choose, branch] := keys | throw (IO.userError "composite entry keys changed")
    let first ← success initial mutate [.bool true, word 11, word 29] (.product (word 29) (.bool true))
    let selected ← success first choose [.bool true, word 37] (word 37)
    let failed ← failure selected choose [.bool false, word 41]
    let continued ← success failed mutate [.bool false, word 2, word 7] (.product (word 7) (.bool false))
    let left ← failure continued branch [.bool true]
    let right ← failure left branch [.bool false]
    require ([initial.heapSize, first.heapSize, selected.heapSize, failed.heapSize, continued.heapSize, left.heapSize, right.heapSize] == [4, 16, 25, 34, 46, 52, 58])
      "composite branch/write prefix heaps changed"
    IO.println s!"COMPOSITE_ENTRY_HEAPS: {[initial.heapSize, first.heapSize, selected.heapSize, failed.heapSize, continued.heapSize, left.heapSize, right.heapSize]}"
  runProgram basicWorkspace ["bool"] 1 fun _ initial keys => do
    let [key] := keys | throw (IO.userError "composite group key changed")
    let after ← success initial key [] (.bool true)
    require (after.heapSize == initial.heapSize) "composite group allocated unexpectedly"
  runProgram tupleWorkspace ["quadruple", "firstFault", "laterFault", "singleton"] 6 fun _ initial keys => do
    let [quad, firstFault, laterFault, single] := keys | throw (IO.userError "composite tuple keys changed")
    let first ← success initial quad [] (.product (word 11) (.product (.bool false) (.product (word 13) (.bool true))))
    let early ← failure first firstFault []
    let late ← failure early laterFault []
    let after ← success late single [] (word 31)
    require ([initial.heapSize, first.heapSize, early.heapSize, late.heapSize, after.heapSize] == [7, 13, 19, 31, 34])
      "composite tuple ordering/fault prefix heaps changed"
    IO.println s!"COMPOSITE_TUPLE_HEAPS: {[initial.heapSize, first.heapSize, early.heapSize, late.heapSize, after.heapSize]}"
  IO.println "COMPOSITE_COMPILER_PROFILE_PASS: actual checker/profile/automatic issuer; unchanged source programs; ordered products, conditional branch fault, group, tuple fault prefixes, zero-fuel resume, same-session continuation"

end Tests.SourceCoreSelectedCompositeProfile
