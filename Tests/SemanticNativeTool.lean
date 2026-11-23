import Lean.Data.Json
import Solcore.Frontend.SourceCompiler

/-! Lean's native frontend as a differential path. One program's sources go through the public
pipeline: loading, checking and the compilation of one named function. Then each input runs on
the same freshly booted session.

The request and the result are JSON (`solcore-lean.semantic-native-request.v1` and `-result.v1`).
An input's observation is the function's Word result, a language failure, out of fuel, or the
stage that refused the run. A language failure is decoded by the session's own diagnostic:
`Panic(code)` and upstream's `DirtyHigherBitsForInteger()` carry upstream's revert data, and any
other failure names its runtime error. The tool compares nothing; `scripts/semantic-native.py`
compares the observations with each case's direct Core result. -/

set_option autoImplicit false

namespace Tests.SemanticNativeTool

open Lean Solcore Solcore.Frontend

def requestSchema : String := "solcore-lean.semantic-native-request.v1"
def resultSchema : String := "solcore-lean.semantic-native-result.v1"

/-- The longest error text a result keeps. -/
def detailLimit : Nat := 4000

structure Source where
  path : String
  content : String
  deriving FromJson

/-- Inputs are lists of Words, each in unsigned decimal. -/
structure Request where
  schema : String
  entry : String
  sources : List Source
  function : String
  inputs : List (List String)
  checkingFuel : Nat
  compilationFuel : Nat
  specializationBudget : Nat
  executionFuel : Nat
  deriving FromJson

/-- An error text on one line, its whitespace runs collapsed, then clipped: `Json.compress` leaves a
`Repr` text's line breaks raw. -/
private def clip (text : String) : String :=
  let step := fun (state : Array Char × Bool) (char : Char) =>
    if !char.isWhitespace then (state.1.push char, false)
    else if state.2 then state else (state.1.push ' ', true)
  let collapsed := (text.toList.foldl step (#[], true)).1
  let chars := if collapsed.back? == some ' ' then collapsed.pop else collapsed
  if chars.size ≤ detailLimit then String.ofList chars.toList
  else String.ofList (chars.toList.take detailLimit) ++ "…"

private def loadStage : ProgramLoadError → String
  | .workspace _ => "workspace"
  | .syntaxInvariant _ _ => "parser-invariant"
  | .sourceDiagnostics _ lexical _ => if lexical.isEmpty then "parsing" else "lexing"
  | .pragmaSolcore _ _ => "parsing"
  | .uncheckedBlock _ _ => "unchecked-blocks"
  | .environment _ => "name-resolution"
  | .imports _ => "imports"

private def checkStage : ProgramCheckError → String
  | .loading error => loadStage error
  | .signature _ | .missingSuperclassInstance _ _ _ => "signatures"
  | .signatureFormation _ => "signature-formation"
  | .inference _ | .methodInference _ _ => "inference"
  | .noSolution _ _ | .methodNoSolution _ _ => "trait-resolution"
  | .inconclusive _ _ | .methodInconclusive _ _
  | .ambiguousGiven _ _ | .methodAmbiguousGiven _ _ => "trait-resolution-inconclusive"

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
    | .root _ _ | .rootCountMismatch _ _ | .rootOrderMismatch
    | .rootWithoutPublicValue _ _ => "root-validation"

private def word (text : String) : Except String SourceCompiler.Value :=
  match text.toNat? with
  | some value =>
      if value < Core.wordModulus then .ok (.word (Core.Word.ofNatModulo value))
      else .error "a Word input exceeds 256 bits"
  | none => .error "Word inputs are unsigned decimal integers"

private def hexByte (byte : UInt8) : String :=
  let digit (value : Nat) : Char :=
    if value < 10 then Char.ofNat (48 + value) else Char.ofNat (87 + value)
  String.ofList [digit (byte.toNat / 16), digit (byte.toNat % 16)]

private def hex (bytes : ByteArray) : String :=
  bytes.toList.foldl (fun text byte => text ++ hexByte byte) "0x"

/-- The constructor's name at the head of a `Repr` text. -/
private def constructorName (text : String) : String :=
  let head := String.ofList (text.toList.takeWhile fun char => !char.isWhitespace)
  ((head.splitOn ".").getLast?).getD head

private def refused (stage detail : String) (milliseconds : Nat) : Json :=
  Json.mkObj [("status", "rejected"), ("stage", stage), ("detail", detail),
    ("ms", toJson milliseconds)]

/-- A language failure, decoded by the session's diagnostic for the function's key. -/
private def failure {artifact : SourceCompiler.Artifact}
    (session : SourceCompiler.Session artifact) (key : SourceCompiler.Key) (reason : Core.Word)
    (milliseconds : Nat) : Json :=
  let common : List (String × Json) :=
    [("reason", toJson (toString reason.val)), ("ms", toJson milliseconds)]
  let object (fields : List (String × Json)) : Json := Json.mkObj (fields ++ common)
  match session.diagnostic key reason with
  | .ok (some diagnostic) => match diagnostic.error with
    | .panic code => object [("status", "reverted"), ("error", "panic"),
        ("output", hex (SourceCorePanics.revertData code))]
    | .dirtyHigherBitsForInteger => object [("status", "reverted"),
        ("error", "dirtyHigherBitsForInteger"), ("output", hex SourceCorePanics.dirtyRevertData)]
    | error => object [("status", "failed"), ("error", constructorName (reprStr error)),
        ("detail", clip (reprStr diagnostic))]
  | .ok none => object [("status", "failed"), ("error", Json.null)]
  | .error error => object [("status", "failed"), ("error", "diagnostic"),
      ("detail", clip (reprStr error))]

private def observe {artifact : SourceCompiler.Artifact}
    (session : SourceCompiler.Session artifact) (key : SourceCompiler.Key) (request : Request)
    (arguments : List String) : IO Json := do
  let values ← match arguments.mapM word with
    | .ok values => pure values
    | .error error => return refused "harness-input" error 0
  let started ← IO.monoMsNow
  let result ← session.run key values {
    inputValidationFuel := request.checkingFuel
    outputValidationFuel := request.checkingFuel
    executionFuel := request.executionFuel
  }
  let milliseconds := (← IO.monoMsNow) - started
  match result with
  | .error error => return refused "invocation" (clip (reprStr error)) milliseconds
  | .ok (.succeeded completion) => match completion.value with
    | .word value => return Json.mkObj [("status", "returned"), ("word", toString value.val),
        ("ms", toJson milliseconds)]
    | value => return refused "observation" (clip (reprStr value)) milliseconds
  | .ok (.failed reason _) => return failure session key reason milliseconds
  | .ok (.outOfFuel _) => return Json.mkObj [("status", "out-of-fuel"), ("stage", "execution"),
      ("ms", toJson milliseconds)]
  | .ok (.exportError error _) => return refused "export" (clip (reprStr error)) milliseconds

private def result (status stage detail : String) (times : List (String × Nat))
    (observations : Array Json := #[]) : Json :=
  Json.mkObj [("schema", resultSchema), ("status", status), ("stage", stage), ("detail", detail),
    ("milliseconds", Json.mkObj (times.map fun (name, value) => (name, toJson value))),
    ("observations", toJson observations)]

/-- Load, check and compile the request's function once, then run every input from the same
booted session. -/
def run (request : Request) : IO Json := do
  let raw : Workspace.RawWorkspace := {
    entry := request.entry
    mainSources := request.sources.map fun source =>
      {path := source.path, content := source.content}
    externalLibraries := []
  }
  let started ← IO.monoMsNow
  let loaded ← match loadProgram raw with
    | .ok loaded => pure loaded
    | .error errors =>
        let stage := (errors.head?.map loadStage).getD "loading"
        let detail := clip ((errors.head?.map reprStr).getD "")
        let now ← IO.monoMsNow
        return result "rejected" stage detail [("load", now - started)]
  let loadedAt ← IO.monoMsNow
  let checked ← match checkLoadedProgram loaded request.checkingFuel with
    | .ok checked => pure checked
    | .error errors =>
        let stage := (errors.head?.map checkStage).getD "checking"
        let detail := clip ((errors.head?.map reprStr).getD "")
        let now ← IO.monoMsNow
        return result "rejected" stage detail
          [("load", loadedAt - started), ("check", now - loadedAt)]
  let checkedAt ← IO.monoMsNow
  let options : SourceCompiler.Options := {
    checkingFuel := request.checkingFuel
    compilationFuel := request.compilationFuel
    specializationBudget := request.specializationBudget
  }
  let seed := SourceCompiler.Seed.named loaded.workspace.entry.toModuleId request.function
  let before := [("load", loadedAt - started), ("check", checkedAt - loadedAt)]
  let compiled ← match SourceCompiler.compileChecked checked [seed] options with
    | .ok compiled => pure compiled
    | .error error =>
        let now ← IO.monoMsNow
        return result "rejected" (compileStage error) (clip (reprStr error))
          (before ++ [("compile", now - checkedAt)])
  let compiledAt ← IO.monoMsNow
  let times := before ++ [("compile", compiledAt - checkedAt)]
  let key ← match compiled.keys with
    | [key] => pure key
    | _ => return result "rejected" "root-validation" "expected one selected entry" times
  let artifact ← compiled.open
  let bootstrap ← artifact.bootstrap
  let session ← match bootstrap.resume request.executionFuel with
    | .ready session => pure session
    | .error error =>
        let now ← IO.monoMsNow
        return result "rejected" "bootstrap" (clip (reprStr error))
          (times ++ [("boot", now - compiledAt)])
    | .outOfFuel _ =>
        let now ← IO.monoMsNow
        return result "out-of-fuel" "bootstrap" "initialization exhausted fuel"
          (times ++ [("boot", now - compiledAt)])
  let bootedAt ← IO.monoMsNow
  let mut observations := #[]
  for arguments in request.inputs do
    observations := observations.push (← observe session key request arguments)
  let finished ← IO.monoMsNow
  return result "compiled" "compiled" ""
    (times ++ [("boot", bootedAt - compiledAt), ("runs", finished - bootedAt)]) observations

private def readRequest (path : String) : IO Request := do
  let limit := 16 * 1024 * 1024
  unless (← (System.FilePath.mk path).metadata).byteSize.toNat ≤ limit do
    throw (IO.userError "the request exceeds 16 MiB")
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  let request ← IO.ofExcept (fromJson? json : Except String Request)
  unless request.schema == requestSchema do
    throw (IO.userError s!"the request's schema is not {requestSchema}")
  return request

end Tests.SemanticNativeTool

def main (args : List String) : IO UInt32 := do
  match args with
  | [path] =>
      try
        let request ← Tests.SemanticNativeTool.readRequest path
        IO.println (← Tests.SemanticNativeTool.run request).compress
        return 0
      catch error =>
        IO.eprintln s!"semantic-native-tool: {error}"
        return 2
  | _ =>
      IO.eprintln "usage: semantic-native-tool REQUEST.json"
      return 2
