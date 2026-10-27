import Solcore.Synthesis.Source.InputCases
import Solcore.Synthesis.Source.FunctionEmitter

/-! Replayable, bounded cases for acyclic named Word functions. The original
Core lambda chain is retained and executed independently of source lowering.
The older scalar profiles and their replay rules remain unchanged. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.Function
open Lean Solcore.Core Solcore.Synthesis.Core

def caseSchema : String := "solcore-lean.semantic-function-case.v1"
def profileVersion : String := "runtime-functions-v1/seed-chain-v1"

structure CheckedInput where
  function : CheckedWordFunctionDAG
  input : Word

def CheckedInput.program (value : CheckedInput) : Wire.Program :=
  value.function.instantiate value.input

def observe (function : CheckedWordFunctionDAG) (input : Word) (fuel : Nat) : Json :=
  let fields := match (function.instantiate input).toCore.runStateful fuel with
    | .done (.word word) _ =>
        [("status", toJson "returned"), ("word", toJson (toString word.val))]
    | .done value _ =>
        [("status", toJson "invalid-result"), ("detail", toJson (reprStr value))]
    | .outOfFuel _ => [("status", toJson "out-of-fuel")]
    | .fault reason _ => [("status", toJson "core-fault"), ("detail", toJson (reprStr reason))]
  Json.mkObj (("stage", toJson "execution") :: fields)

def contractJson (emitted : EmittedProgram) (input : Word) : Json := Json.mkObj [
  ("name", toJson emitted.contractName), ("method", toJson emitted.methodName),
  ("signature", toJson emitted.methodSignature),
  ("deployPath", toJson emitted.deployPath), ("runtimePath", toJson emitted.runtimePath),
  ("calldata", toJson (Input.calldata input)), ("constructorCalldata", toJson "0x")]

def makeCase (function : CheckedWordFunctionDAG) (input : Word) (emitted : EmittedProgram)
    (origin : Json) (fuel : Nat) (revision : GeneratorRevision := .v1)
    (mask : FeatureMask := FeatureMask.all) : Json := Json.mkObj [
  ("schema", toJson caseSchema), ("program", Wire.encodeProgram (function.instantiate input)),
  ("input", toJson (toString input.val)), ("source", toJson emitted.source),
  ("provenance", Json.mkObj <| swarmField revision mask ++ [
    ("origin", origin), ("profileVersion", toJson profileVersion),
    ("functionVersion", toJson wordFunctionDAGVersion),
    ("abstractionVersion", toJson abstractionVersion),
    ("generatorVersion", toJson revision.version),
    ("emitterVersion", toJson emitterVersion), ("wrapperVersion", toJson wrapperVersion),
    ("features", toJson function.features)]),
  ("contract", contractJson emitted input), ("executionFuel", toJson fuel),
  ("directCore", observe function input fuel)]

def emitCase (function : CheckedWordFunctionDAG) (input : Word)
    (origin : Json) (fuel : Nat) (revision : GeneratorRevision := .v1)
    (mask : FeatureMask := FeatureMask.all) : Except String Json := do
  unless Wire.programNodes (function.instantiate input) ≤ 512 do
    throw "applied function DAG exceeds the 512-node case limit"
  let emitted ← (emit function).mapError reprStr
  return makeCase function input emitted origin fuel revision mask

private def decodeProgram (json : Json) : Except String Wire.Program := do
  let program ← (Wire.decodeProgramWithBudget
    {maxDepth := 512, maxNodes := 512, maxIntegerBytes := 4096} json).mapError (fun
      | .protocol error => error.toJson.compress
      | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)
  unless Wire.programNodes program ≤ 512 do throw "Core program exceeds the 512-node case limit"
  return program

def checkedFunction (json : Json) : Except String CheckedWordFunctionDAG := do
  let some function := CheckedWordFunctionDAG.ofProgram? (← decodeProgram json) |
    throw "program is not a checked scalar Word function DAG"
  return function

def caseProgram (json : Json) : Except String CheckedInput := do
  unless (← json.getObjValAs? String "schema") = caseSchema do
    throw "unsupported semantic function case schema"
  let input ← Input.inputWord (← json.getObjValAs? String "input")
  let program ← decodeProgram (← json.getObjVal? "program")
  match program with
  | { resultType := .word, dataDefinitions := [], body := .apply functionBody (.word argument) } =>
      unless argument = input do throw "saved program argument differs from input"
      let some function := CheckedWordFunctionDAG.ofProgram? {
        resultType := .function .word .word, dataDefinitions := [], body := functionBody } |
        throw "applied function is outside the checked function DAG profile"
      return ⟨function, input⟩
  | _ => throw "function case program is not a closed Word function DAG application"

/-- Scalar budgets account for every helper lambda, binding, call, input and
program node. The final measured applied program remains the admission rule. -/
def generatedFunction (seed : Seed) (nodes : Nat) (revision : GeneratorRevision := .v1) :
    Except String (CheckedWordFunctionDAG × Json) := do
  let count := 1 + seed.toNat % 3
  unless nodes ≤ 512 && 9 * count + 6 ≤ nodes do
    throw "node budget is too small for the selected helper count or exceeds 512"
  let scalarBudget := (nodes - (8 * count + 6)) / count + 2
  let mut helpers : List Wire.Expr := []
  let mut metadata : Array Json := #[]
  let mut finalSeed := seed
  -- One mask for every helper of the case.
  let mask := revision.caseMask seed
  for index in List.range count do
    let helperSeed := Seed.ofNat (seed.toNat + index)
    let generated ←
      (generate {seed := helperSeed, maxProgramNodes := scalarBudget, revision, mask}).mapError reprStr
    let literals := literalCount generated.program.body
    unless literals > 0 do throw "generated helper has no Word literal to abstract"
    let selected := helperSeed.toNat % literals
    let some scalar := CheckedWordFunction.fromProgram? generated.checkedProgram selected |
      throw "helper literal abstraction did not produce a checked Word function"
    let body := if index = 0 then scalar.body else
      Wire.Expr.binary .wordAdd scalar.body (.apply (.var 1) (.var 0))
    helpers := helpers ++ [body]
    metadata := metadata.push (Json.mkObj [
      ("index", toJson index), ("seed", toJson (toString helperSeed.toNat)),
      ("finalSeed", toJson (toString generated.finalSeed.toNat)),
      ("maxProgramNodes", toJson scalarBudget), ("literalIndex", toJson selected)])
    finalSeed := generated.finalSeed
  let some function := CheckedWordFunctionDAG.ofParts? helpers (.apply (.var 1) (.var 0)) |
    throw "generated helper chain did not pass the full Core checker"
  unless Wire.programNodes (function.instantiate Word.zero) ≤ nodes do
    throw "applied helper chain exceeds its requested node budget"
  let origin := Json.mkObj [
    ("kind", toJson "function-generated"), ("seed", toJson (toString seed.toNat)),
    ("finalSeed", toJson (toString finalSeed.toNat)), ("maxProgramNodes", toJson nodes),
    ("helperCount", toJson count), ("helpers", .arr metadata)]
  return (function, origin)

def boundaryResults (function : CheckedWordFunctionDAG) (fuel : Nat) : Except String (List Word) :=
  Input.boundaryInputs.mapM fun input =>
    match (function.instantiate input).toCore.runStateful fuel with
    | .done (.word value) _ => .ok value
    | .done _ _ => .error "boundary observation did not return a Word"
    | .outOfFuel _ => .error "boundary observation exhausted Core fuel"
    | .fault _ _ => .error "boundary observation produced a Core fault"

def inputSensitive (function : CheckedWordFunctionDAG) (fuel : Nat) : Except String Unit := do
  let results ← boundaryResults function fuel
  unless results.any (fun value => results.any (fun other => value != other)) do
    throw "all four boundary inputs returned the same Word"

def generateCases (firstSeed : Seed) (nodes count attempts fuel : Nat)
    (revision : GeneratorRevision := .v1) (inputSelection : InputSelection := .boundary) :
    Json := Id.run do
  let mut cases : Array Json := #[]
  let mut excluded : Array Json := #[]
  let mut attempted := 0
  for index in List.range attempts do
    if cases.size < count then
      attempted := attempted + 1
      let seed := Seed.ofNat (firstSeed.toNat + index)
      let result := do
        let (function, origin) ← generatedFunction seed nodes revision
        let emitted ← (emit function).mapError reprStr
        inputSensitive function fuel
        return (function, origin, emitted)
      match result with
      | .error error =>
          let resource := error == "boundary observation exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "function-profile"),
            ("reason", toJson error),
            ("code", toJson (if resource then "boundary-out-of-fuel" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok (function, origin, emitted) =>
          for (input, inputIndex) in (inputSelection.inputs Input.boundaryInputs seed).zipIdx do
            if cases.size < count then
              let origin := (origin.setObjVal! "inputIndex" (toJson inputIndex)).setObjVal!
                "validationFuel" (toJson fuel)
              cases := cases.push
                (makeCase function input emitted (inputSelection.record origin) fuel revision
                  (revision.caseMask seed))
  return Json.mkObj [("schema", toJson corpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

def replayCase (json : Json) (fuel : Nat) : Except String Json := do
  let admitted ← caseProgram json
  let provenance ← json.getObjVal? "provenance"
  let revision := savedRevision provenance
  for (name, expected) in [
      ("generatorVersion", revision.version), ("profileVersion", profileVersion),
      ("functionVersion", wordFunctionDAGVersion), ("abstractionVersion", abstractionVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let mask ← savedMask provenance revision
  let emitted ← (emit admitted.function).mapError reprStr
  unless (← json.getObjValAs? String "source") = emitted.source do
    throw "saved source differs from emission of the original Core function DAG"
  unless (← json.getObjVal? "contract") == contractJson emitted admitted.input do
    throw "saved contract metadata differs from the function wrapper"
  unless (← provenance.getObjVal? "features") == toJson admitted.function.features do
    throw "saved features differ from the original Core function DAG"
  let kind ← origin.getObjValAs? String "kind"
  unless kind = "function-generated" || kind = "imported" || kind = "reduced" do
    throw "unsupported function case origin"
  if kind = "function-generated" then
    let seedText ← origin.getObjValAs? String "seed"
    let some seed := seedText.toNat? | throw "invalid saved seed"
    unless seed < 2 ^ 64 && toString seed = seedText do throw "noncanonical saved seed"
    unless mask == revision.caseMask (Seed.ofNat seed) do
      throw "saved swarm mask differs from its generation seed"
    let nodes ← origin.getObjValAs? Nat "maxProgramNodes"
    let (function, expectedOrigin) ← generatedFunction (Seed.ofNat seed) nodes revision
    for name in ["kind", "seed", "finalSeed", "maxProgramNodes", "helperCount", "helpers"] do
      unless (← origin.getObjVal? name) == (← expectedOrigin.getObjVal? name) do
        throw ("saved " ++ name ++ " differs from generated helper provenance")
    unless Wire.encodeProgram function.program == Wire.encodeProgram admitted.function.program do
      throw "saved function DAG differs from its generation seed"
    let inputIndex ← origin.getObjValAs? Nat "inputIndex"
    let inputSelection ← InputSelection.ofOrigin origin
    unless (inputSelection.inputs Input.boundaryInputs (Seed.ofNat seed))[inputIndex]? = some admitted.input do
      throw "saved input differs from its boundary index"
    let validationFuel ← origin.getObjValAs? Nat "validationFuel"
    unless validationFuel ≤ 10000000 do throw "saved validation fuel exceeds limit"
    inputSensitive function validationFuel
  return makeCase admitted.function admitted.input emitted origin fuel revision mask

structure Reduction (source : CheckedInput) where private mk ::
  candidate : CheckedInput
  sameHelperCount : candidate.function.helpers.length = source.function.helpers.length
  strict : (complexity candidate.program.body).StrictlySmaller (complexity source.program.body)

private def sealReduction (source : CheckedInput) (helpers : List Wire.Expr)
    (entry : Wire.Expr) (input : Word) : Option (Reduction source) := do
  let function ← CheckedWordFunctionDAG.ofParts? helpers entry
  let candidate : CheckedInput := ⟨function, input⟩
  if count : candidate.function.helpers.length = source.function.helpers.length then
    if strict : (complexity candidate.program.body).StrictlySmaller (complexity source.program.body)
      then some ⟨candidate, count, strict⟩ else none
  else none

/-- Local rewrites never remove or reorder the surrounding function bindings.
Removing a scalar binder is deliberately omitted; final DAG checking validates
every variable and call after all other rewrites. -/
private def bodyReductions (target : Target) : Wire.Expr → List Wire.Expr
  | .word _ | .bool _ | .var _ => [if target = .word then .word Word.zero else .bool false]
  | .letE initializer body =>
      [if target = .word then .word Word.zero else .bool false] ++
      (if target = .word then [initializer] else []) ++
      (bodyReductions .word initializer).map (fun changed => .letE changed body) ++
      (bodyReductions target body).map (.letE initializer)
  | .ifE condition yes no =>
      [if target = .word then .word Word.zero else .bool false, yes, no] ++
      (bodyReductions .bool condition).map (fun changed => .ifE changed yes no) ++
      (bodyReductions target yes).map (fun changed => .ifE condition changed no) ++
      (bodyReductions target no).map (.ifE condition yes)
  | .unary operation operand =>
      [if target = .word then .word Word.zero else .bool false, operand] ++
      (bodyReductions (Target.unaryOperand operation) operand).map (.unary operation)
  | .binary operation left right =>
      [if target = .word then .word Word.zero else .bool false, left, right] ++
      (bodyReductions .word left).map (fun changed => .binary operation changed right) ++
      (bodyReductions .word right).map (.binary operation left)
  | .ternary operation first second third =>
      [.word Word.zero, first, second, third] ++
      (bodyReductions .word first).map (fun changed => .ternary operation changed second third) ++
      (bodyReductions .word second).map (fun changed => .ternary operation first changed third) ++
      (bodyReductions .word third).map (.ternary operation first second)
  | .apply function argument =>
      [.word Word.zero, argument] ++ (bodyReductions .word argument).map (.apply function)
  | _ => []

def reductions (source : CheckedInput) : List (Reduction source) := Id.run do
  let mut raw : List (List Wire.Expr × Wire.Expr × Word) := []
  for (body, index) in source.function.helpers.zipIdx do
    for changed in bodyReductions .word body do
      raw := raw ++ [(source.function.helpers.set index changed, source.function.entry, source.input)]
  for changed in bodyReductions .word source.function.entry do
    raw := raw ++ [(source.function.helpers, changed, source.input)]
  for input in [Word.zero, Word.ofNatModulo 1, Word.ofNatModulo (source.input.val / 2)] do
    raw := raw ++ [(source.function.helpers, source.function.entry, input)]
  let mut seen : List String := []
  let mut result := []
  for (helpers, entry, input) in raw do
    if let some reduced := sealReduction source helpers entry input then
      let key := (Wire.encodeProgram reduced.candidate.program).compress
      if !seen.contains key then
        seen := key :: seen
        result := result ++ [reduced]
  return result

def shrinkCases (json : Json) (limit fuel : Nat) : Except String Json := do
  let _ ← replayCase json fuel
  let source ← caseProgram json
  let provenance ← json.getObjVal? "provenance"
  let revision := savedRevision provenance
  let mask ← savedMask provenance revision
  let mut cases : Array Json := #[]
  for reduced in (reductions source).take limit do
    let origin := Json.mkObj [
      ("kind", toJson "reduced"), ("parentProgram", Wire.encodeProgram source.program),
      ("parentInput", toJson (toString source.input.val))]
    cases := cases.push
      (← emitCase reduced.candidate.function reduced.candidate.input origin fuel revision mask)
  return Json.mkObj [("schema", toJson corpusSchema), ("cases", .arr cases)]

end Solcore.Synthesis.Source.Function
