import Lean.Data.Json
import Solcore.Frontend.SourceCompiler

/-! Execute pinned upstream source fixtures through the public Core boundary.
The JSON protocol keeps source text intact and distinguishes compilation stages
from execution outcomes. This runner does not evaluate typed source directly. -/

set_option autoImplicit false

namespace Tests.RustParity

open Lean Solcore Solcore.Frontend

structure Scalar where
  kind : String
  value : String := ""
  deriving FromJson, ToJson, BEq

structure Source where
  path : String
  content : String
  deriving FromJson

structure Request where
  id : String
  entry : String := "main.sol"
  sources : List Source
  function : String := "main"
  arguments : List Scalar := []
  expected : Option Scalar := none
  checkingFuel : Nat := 4096
  compilationFuel : Nat := 4096
  specializationBudget : Nat := 1024
  executionFuel : Nat := 1000000
  deriving FromJson

structure Observation where
  id : String
  stage : String
  status : String
  detail : String := ""
  value : Option Scalar := none
  deriving ToJson

private def failure (request : Request) (stage detail : String)
    (status : String := "rejected") : Observation :=
  {id := request.id, stage, status, detail}

private def loadStage : ProgramLoadError → String
  | .workspace _ => "workspace"
  | .syntaxInvariant _ _ => "parser-invariant"
  | .sourceDiagnostics _ lexical _ => if lexical.isEmpty then "parsing" else "lexing"
  | .environment _ => "name-resolution"

private def checkStage : ProgramCheckError → String
  | .loading error => loadStage error
  | .signature _ => "signatures"
  | .signatureFormation _ => "signature-formation"
  | .inference _ | .methodInference _ _ => "inference"
  | .noSolution _ _ | .methodNoSolution _ _ => "trait-resolution"
  | .inconclusive _ _ | .methodInconclusive _ _ => "trait-resolution-inconclusive"

private def compileStage : SourceCompiler.CompileError → String
  | .preparation _ => "core-preparation"
  | .discovery _ => "entry-discovery"
  | .compilation error => match error with
    | .checking errors => (errors.head?.map checkStage).getD "checking"
    | .seed _ _ _ => "entry-discovery"
    | .worklist _ | .specializationBudgetExhausted _ _ => "specialization"
    | .invalidPlan _ => "linking"
    | .planEvidence _ => "plan-validation"
    | .compilation _ => "core-lowering"
    | .root _ _ | .rootCountMismatch _ _ | .rootOrderMismatch => "root-validation"

private def input (scalar : Scalar) : Except String SourceCompiler.Value := do
  match scalar.kind with
  | "unit" => pure .unit
  | "bool" => match scalar.value with
    | "true" => pure (.bool true)
    | "false" => pure (.bool false)
    | _ => throw "Boolean inputs must be true or false"
  | "word" =>
      let value ← match scalar.value.toNat? with
        | some value => pure value
        | none => throw "Word inputs must be unsigned decimal integers"
      if value < Core.wordModulus then pure (.word (Core.Word.ofNatModulo value))
      else throw "Word input exceeds 256 bits"
  | "integer" =>
      let value ← match scalar.value.toInt? with
        | some value => pure value
        | none => throw "Integer inputs must be signed decimal integers"
      pure (.integer value)
  | _ => throw s!"unsupported scalar input kind: {scalar.kind}"

private def output : SourceCompiler.Value → Option Scalar
  | .unit => some {kind := "unit"}
  | .bool value => some {kind := "bool", value := toString value}
  | .word value => some {kind := "word", value := toString value.val}
  | .integer value => some {kind := "integer", value := toString value}
  | _ => none

def run (request : Request) : IO Observation := do
  let arguments ← match request.arguments.mapM input with
    | .ok values => pure values
    | .error error => return failure request "harness-input" error
  let raw : Workspace.RawWorkspace := {
    entry := request.entry
    mainSources := request.sources.map fun source => {path := source.path, content := source.content}
    externalLibraries := []
  }
  let loaded ← match loadProgram raw with
    | .ok loaded => pure loaded
    | .error errors => return failure request ((errors.head?.map loadStage).getD "loading") (reprStr errors)
  let checked ← match checkLoadedProgram loaded request.checkingFuel with
    | .ok checked => pure checked
    | .error errors => return failure request ((errors.head?.map checkStage).getD "checking") (reprStr errors)
  let options : SourceCompiler.Options := {
    checkingFuel := request.checkingFuel
    compilationFuel := request.compilationFuel
    specializationBudget := request.specializationBudget
  }
  let seed := SourceCompiler.Seed.named loaded.workspace.entry.toModuleId request.function
  let compiled ← match SourceCompiler.compileChecked checked [seed] options with
    | .ok compiled => pure compiled
    | .error error => return failure request (compileStage error) (reprStr error)
  let key ← match compiled.keys with
    | [key] => pure key
    | _ => return failure request "root-validation" "expected one selected entry"
  let artifact ← compiled.open
  let bootstrap ← artifact.bootstrap
  let session ← match bootstrap.resume request.executionFuel with
    | .ready session => pure session
    | .error error => return failure request "bootstrap" (reprStr error)
    | .outOfFuel _ => return failure request "bootstrap" "initialization exhausted fuel" "out-of-fuel"
  let result ← session.run key arguments {
    inputValidationFuel := request.checkingFuel
    outputValidationFuel := request.checkingFuel
    executionFuel := request.executionFuel
  }
  match result with
  | .error error => return failure request "invocation" (reprStr error)
  | .ok (.failed reason _) => return failure request "execution" (reprStr reason) "language-failure"
  | .ok (.outOfFuel _) => return failure request "execution" "execution exhausted fuel" "out-of-fuel"
  | .ok (.exportError error _) => return failure request "export" (reprStr error)
  | .ok (.succeeded completion) =>
      match output completion.value with
      | none => return failure request "observation" (reprStr completion.value) "unsupported-result"
      | some value =>
          let mismatch := request.expected.any (fun expected => expected != value)
          let observation : Observation := {
            id := request.id
            stage := "execution"
            value := some value
            status := if mismatch then "mismatch" else "succeeded"
            detail := if mismatch then s!"expected {(toJson request.expected).compress}" else ""
          }
          return observation

end Tests.RustParity

def main (args : List String) : IO UInt32 := do
  let [path] := args | throw (IO.userError "usage: lean --run Tests/RustParity.lean REQUESTS.json")
  let json ← match Lean.Json.parse (← IO.FS.readFile path) with
    | .ok json => pure json
    | .error error => throw (IO.userError error)
  let requests ← match (Lean.fromJson? json : Except String (List Tests.RustParity.Request)) with
    | .ok requests => pure requests
    | .error error => throw (IO.userError error)
  for request in requests do
    let observation ← Tests.RustParity.run request
    IO.println (Lean.toJson observation).compress
  return 0
