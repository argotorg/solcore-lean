import Solcore.Test.SourceCompilerFeatureSupport
import Solcore.Frontend.SourceCompiler

/-! One original combines a retained generalized identity, a virtual mapping
root, a projected assignment and actual for initializer/post writes. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMixedIndexRead
open Solcore Frontend SourceInference
open Tests.SourceCompilerFeatureSupport (get require boot word)

def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function mixedIndexRead(flag: Bool) returns (Word, Bool) {",
    "  let f = lam(value) { return value; };",
    "  let table: mapping(Word => Word);",
    "  let active = flag;",
    "  table[3] = f(10);",
    "  for (table[3] += 1; active; table[3] += 2) {",
    "    active = false;",
    "    continue;",
    "  }",
    "  return (table[f(3)], f(flag));",
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
  let program ← get "check mixed index read" (checkProgram workspace options.checkingFuel)
  let source ← get "compile mixed index read" (SourceCoreCompiler.compileChecked program
    (program.signatures.functions.map fun signature => SourceCompiler.Seed.declaration signature.id) options)
  let some cached := source.artifact? | throw (IO.userError "mixed index read cache absent")
  require (program.functions.length == 1 && cached.indexed.base.functions.length == 1) "complete mixed cache changed"
  let recipe ← get "prepare mixed index read" (SourceCoreIndexedSession.Recipe.prepare cached)
  let some root := recipe.roots[0]? | throw (IO.userError "mixed root absent")
  let facade ← get "public mixed index read" (SourceCoreExecution.prepare source)
  let artifact ← facade.open
  let initial ← boot artifact
  let first ← succeeded "one post" (← initial.run root.key [.bool true] runOptions)
  require (first.value == .product (.word (word 13)) (.bool true)) "mixed true result"
  let second ← succeeded "zero post" (← first.session.run root.key [.bool false] runOptions)
  require (second.value == .product (.word (word 11)) (.bool false)) "mixed false result"
  let repeated ← succeeded "one post reused" (← second.session.run root.key [.bool true] runOptions)
  require (repeated.value == .product (.word (word 13)) (.bool true)) "mixed reused result"
  IO.println s!"MIXED_INDEX_READ_NATIVE_HEAPS: {[initial.heapSize,first.session.heapSize,second.session.heapSize,repeated.session.heapSize]}"
  IO.println "MIXED_INDEX_READ_ORIGINAL_INVENTORY: originals1/cache1"
  IO.println "MIXED_INDEX_READ_PROBE_PASS"

end Tests.SourceCoreMixedIndexRead
