import Solcore.Test.SourceCompilerFeatureSupport
import Solcore.SourceSemantics.CoreLowering.CellAwareNamedProgramProfiles

/-! Runtime coverage of returned generalized instances and retained captures.
Independent Source/public correspondence is established by separate proofs. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreGeneralizedExport
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCompilerFeatureSupport (get require boot word)

def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function make(flag: Bool) returns (function(Word) returns (Word), function(Bool) returns (Bool)) { let f = lam(value) { return value; }; return (f, f); }",
    "function capture(seed: Word) returns (function(Bool) returns (Word)) { let f = lam(value) { return seed; }; return f; }",
    "function tick(flag: Bool) returns (Bool) { return flag; }" ]}] }
def options : SourceCoreCompiler.Options :=
  {checkingFuel := 1000, compilationFuel := 1000, specializationBudget := 128}
def runOptions : SourceCoreExecution.RunOptions :=
  {executionFuel := 300000, outputValidationFuel := 1000}

private def succeeded {artifact : SourceCoreExecution.Artifact}
    (label : String) : Except SourceCoreIndexedSession.Error (SourceCoreExecution.Outcome artifact) →
    IO (SourceCoreExecution.Completion artifact)
  | .ok (.succeeded result) => pure result
  | .ok (.failed reason _) => throw (IO.userError s!"{label}: language failure {reprStr reason}")
  | .ok (.exportError error _) => throw (IO.userError s!"{label}: output {reprStr error}")
  | .ok (.outOfFuel _) => throw (IO.userError s!"{label}: fuel exhausted")
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")

def probe : IO Unit := do
  let program ← get "check generalized exports" (checkProgram workspace options.checkingFuel)
  let source ← get "compile generalized exports" (SourceCoreCompiler.compileChecked program
    (program.signatures.functions.map fun signature => SourceCompiler.Seed.declaration signature.id) options)
  let some cached := source.artifact? | throw (IO.userError "generalized export cache absent")
  require (program.functions.length == 3 && cached.indexed.base.functions.length == 3) "complete export cache changed"
  let some _profiles := CellAwareNamedProgramProfiles.profile? cached.indexed
    | throw (IO.userError "generalized export complete profile rejected")
  let recipe ← get "prepare generalized exports" (SourceCoreIndexedSession.Recipe.prepare cached)
  let some make := recipe.roots[0]? | throw (IO.userError "make root absent")
  let some capture := recipe.roots[1]? | throw (IO.userError "capture root absent")
  let some tick := recipe.roots[2]? | throw (IO.userError "tick root absent")
  let facade ← get "public generalized exports" (SourceCoreExecution.prepare source)
  let artifact ← facade.open
  let initial ← boot artifact
  let pair ← succeeded "make" (← initial.run make.key [.bool true] runOptions)
  let .product (.function first) (.function second) := pair.value
    | throw (IO.userError "generalized export pair shape")
  let saved ← succeeded "capture" (← pair.session.run capture.key [.word (word 29)] runOptions)
  let .function captured := saved.value | throw (IO.userError "generalized captured handle shape")
  let intervening ← succeeded "tick" (← saved.session.run tick.key [.bool false] runOptions)
  require (intervening.value == .bool false) "intervening call result"
  let firstCall ← succeeded "Word handle" (← intervening.session.invokePacked first (.word (word 47)) runOptions)
  require (firstCall.value == .word (word 47)) "generalized Word result"
  let secondCall ← succeeded "Bool handle" (← firstCall.session.invokePacked second (.bool true) runOptions)
  require (secondCall.value == .bool true) "generalized Bool result"
  let capturedCall ← succeeded "captured handle" (← secondCall.session.invokePacked captured (.bool false) runOptions)
  require (capturedCall.value == .word (word 29)) "generalized captured value changed"
  let repeatCall ← succeeded "repeated Word handle" (← capturedCall.session.invokePacked first (.word (word 61)) runOptions)
  require (repeatCall.value == .word (word 61)) "repeated generalized handle changed"
  IO.println s!"GENERALIZED_EXPORT_HEAPS: {[initial.heapSize,pair.session.heapSize,saved.session.heapSize,intervening.session.heapSize,firstCall.session.heapSize,secondCall.session.heapSize,capturedCall.session.heapSize,repeatCall.session.heapSize]}"
  IO.println "GENERALIZED_EXPORT_FULL_INVENTORY: originals3/cache3/profile3"
  IO.println "GENERALIZED_EXPORT_PROBE_PASS"

end Tests.SourceCoreGeneralizedExport
