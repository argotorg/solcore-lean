import Solcore.Test.SourceCompilerFeatureSupport
import Solcore.Frontend.SourceCompiler

/-! One unchanged original body combines a conditional, a generalized identity,
and a returned builtin function value. This probe observes acceptance and runtime;
independent Source and public correspondence use the same unchanged workspace. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMixedConditional
open Solcore Frontend SourceInference
open Tests.SourceCompilerFeatureSupport (get require boot word)

def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function conditionalPair(flag: Bool) returns (Bool, function(Word) returns (integer)) {",
    "  let f = lam(value) { return value; };",
    "  return (flag ? f(true) : f(false), wordToInteger);",
    "}" ]}] }
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
  let program ← get "check mixed conditional" (checkProgram workspace options.checkingFuel)
  let source ← get "compile mixed conditional" (SourceCoreCompiler.compileChecked program
    (program.signatures.functions.map fun signature => SourceCompiler.Seed.declaration signature.id) options)
  let some cached := source.artifact? | throw (IO.userError "mixed conditional cache absent")
  require (program.functions.length == 1 && cached.indexed.base.functions.length == 1) "complete mixed cache changed"
  let recipe ← get "prepare mixed conditional" (SourceCoreIndexedSession.Recipe.prepare cached)
  let some root := recipe.roots[0]? | throw (IO.userError "mixed root absent")
  let facade ← get "public mixed conditional" (SourceCoreExecution.prepare source)
  let artifact ← facade.open
  let initial ← boot artifact
  let first ← succeeded "builtin factory" (← initial.run root.key [.bool true] runOptions)
  let .product (.bool true) (.function handle) := first.value | throw (IO.userError "builtin factory output")
  let invoked ← succeeded "returned builtin" (← first.session.invokePacked handle (.word (word 17)) runOptions)
  require (invoked.value == .integer 17) "returned builtin result"
  let second ← succeeded "factory reused" (← invoked.session.run root.key [.bool false] runOptions)
  let .product (.bool false) (.function _) := second.value | throw (IO.userError "reused factory output")
  IO.println s!"MIXED_CONDITIONAL_NATIVE_HEAPS: {[initial.heapSize,first.session.heapSize,invoked.session.heapSize,second.session.heapSize]}"
  IO.println "MIXED_CONDITIONAL_ORIGINAL_INVENTORY: originals1/cache1"
  IO.println "MIXED_CONDITIONAL_PROBE_PASS"

end Tests.SourceCoreMixedConditional
