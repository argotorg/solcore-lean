import Solcore.Test.SourceCompilerFeatureSupport
import Solcore.Frontend.SourceCompiler
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreGeneralizedLexicalBody
open Solcore Frontend SourceInference
open Tests.SourceCompilerFeatureSupport (get require boot word)
def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function duplicate(flag: Bool) returns (((Word, Word), (Bool, Word)), ((Bool, Bool), (Bool, Word))) {",
    "  let f = lam(value) { let unused: Word; let copied = value; { flag; } if (flag) { flag; } return ((value, value), (flag, 0)); };",
    "  return (f(11), f(flag));",
    "}" ]}] }
def options : SourceCoreCompiler.Options :=
  {checkingFuel := 1000, compilationFuel := 1000, specializationBudget := 128}
def runOptions : SourceCoreExecution.RunOptions :=
  {executionFuel := 300000, outputValidationFuel := 1000}
def publicOutput (flag : Bool) : SourceCorePublicValues.Value :=
  .product (.product (.product (.word (word 11)) (.word (word 11))) (.product (.bool flag) (.word (word 0))))
    (.product (.product (.bool flag) (.bool flag)) (.product (.bool flag) (.word (word 0))))

private def succeeded {artifact : SourceCoreExecution.Artifact}
    (label : String) : Except SourceCoreIndexedSession.Error (SourceCoreExecution.Outcome artifact) →
    IO (SourceCoreExecution.Completion artifact)
  | .ok (.succeeded result) => pure result
  | _ => throw (IO.userError s!"{label}: public execution did not succeed")

def nativeProbe : IO Unit := do
  let program ← get "check duplicate" (checkProgram workspace options.checkingFuel)
  let source ← get "compile duplicate" (SourceCoreCompiler.compileChecked program
    (program.signatures.functions.map fun signature => SourceCompiler.Seed.declaration signature.id) options)
  let some cached := source.artifact? | throw (IO.userError "complete cache absent")
  require (program.functions.length == 1 && cached.indexed.base.functions.length == 1) "complete original/cache"
  let recipe ← get "prepare duplicate" (SourceCoreIndexedSession.Recipe.prepare cached)
  let some root := recipe.roots[0]? | throw (IO.userError "root absent")
  let facade ← get "public duplicate" (SourceCoreExecution.prepare source)
  let artifact ← facade.open
  let initial ← boot artifact
  let first ← succeeded "true" (← initial.run root.key [.bool true] runOptions)
  require (first.value == publicOutput true) "first duplicate/captured/numeric value"
  let second ← succeeded "false" (← first.session.run root.key [.bool false] runOptions)
  require (second.value == publicOutput false) "second duplicate/captured/numeric value"
  let third ← succeeded "true again" (← second.session.run root.key [.bool true] runOptions)
  require (third.value == publicOutput true) "third duplicate/captured/numeric value"
  IO.println s!"GENERALIZED_LEXICAL_BODY_NATIVE_HEAPS: {[initial.heapSize,first.session.heapSize,second.session.heapSize,third.session.heapSize]}"
  IO.println "GENERALIZED_LEXICAL_BODY_NATIVE_PASS"
end Tests.SourceCoreGeneralizedLexicalBody
