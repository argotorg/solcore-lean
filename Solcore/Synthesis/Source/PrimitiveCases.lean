import Solcore.Synthesis.Source.Cases
import Solcore.Synthesis.Source.InputSelection
import Solcore.Synthesis.Source.PrimitiveEmitter

/-! Extended primitive cases retain the independently checked original Core
function. Generation reuses the unchanged broad G0 grammar and literal
abstraction, then checks the new emitter boundary. Saved observations never
supply the oracle. The complete applied program, including its input, is bounded. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.Primitive
open Lean
open Solcore.Core
open Solcore.Synthesis.Core

def caseSchema : String := "solcore-lean.semantic-primitive-case.v1"
def profileVersion : String := "runtime-primitives-v1/literal-seed-v1"
def generatorVersion : String := "core-primitives-v1/" ++ Solcore.Synthesis.Core.generatorVersion

/-- The profile layer over one G0 revision; `generatorVersion` is its `v1` value. -/
def generatorVersionFor (revision : GeneratorRevision) : String :=
  "core-primitives-v1/" ++ revision.version
def boundaryVersion : String := "word-primitive-boundary-bank-v1"

/-- Difference measured from the existing Wire node-count definitions, including
the lambda's parameter/result types and the actual input application. -/
def appliedOverhead : Nat :=
  let scalar : Wire.Program := {resultType := .word, dataDefinitions := [], body := .word Word.zero}
  let applied : Wire.Program := {
    resultType := .word, dataDefinitions := [],
    body := .apply (wordFunctionProgram scalar.body).body (.word Word.zero)}
  Wire.programNodes applied - Wire.programNodes scalar

def minimumProgramNodes : Nat := Solcore.Synthesis.Core.minimumProgramNodes + appliedOverhead

def boundaryInputs : List Word :=
  [Word.zero, Word.ofNatModulo 1, Word.ofNatModulo 2, Word.ofNatModulo 255,
    Word.ofNatModulo 256, Word.maximum, Word.ofNatModulo (2 ^ 255),
    Word.ofNatModulo (2 ^ 255 - 1)]

def inputWord (text : String) : Except String Word := do
  let some value := text.toNat? | throw "input is not a decimal Word"
  unless toString value = text && value < 2 ^ 256 do
    throw "input must be a canonical decimal Word"
  return Word.ofNatModulo value

/-- The fixed-width ABI argument, following the independently checked selector. -/
def calldata (input : Word) : String :=
  selector ++ String.ofList ((List.range 64).map fun index =>
    Char.ofNat (let digit := input.val / 16 ^ (63 - index) % 16
      if digit < 10 then 48 + digit else 87 + digit))

structure CheckedInput where
  function : CheckedWordFunction
  input : Word

def CheckedInput.program (value : CheckedInput) : Wire.Program :=
  value.function.instantiate value.input

def observe (function : CheckedWordFunction) (input : Word) (fuel : Nat) : Json :=
  let fields := match (function.instantiate input).toCore.runStateful fuel with
    | .done (.word word) _ =>
        [("status", toJson "returned"), ("word", toJson (toString word.val))]
    | .done value _ =>
        [("status", toJson "invalid-result"), ("detail", toJson (reprStr value))]
    | .outOfFuel _ => [("status", toJson "out-of-fuel")]
    | .fault reason _ =>
        [("status", toJson "core-fault"), ("detail", toJson (reprStr reason))]
  Json.mkObj (("stage", toJson "execution") :: fields)

def contractJson (emitted : EmittedProgram) (input : Word) : Json := Json.mkObj [
  ("name", toJson emitted.contractName), ("method", toJson emitted.methodName),
  ("signature", toJson emitted.methodSignature),
  ("deployPath", toJson emitted.deployPath), ("runtimePath", toJson emitted.runtimePath),
  ("calldata", toJson (calldata input)), ("constructorCalldata", toJson "0x")]

def makeCase (function : CheckedWordFunction) (input : Word) (emitted : EmittedProgram)
    (origin : Json) (fuel : Nat) (revision : GeneratorRevision := .v1)
    (mask : FeatureMask := FeatureMask.all) : Json := Json.mkObj [
  ("schema", toJson caseSchema),
  ("program", Wire.encodeProgram (function.instantiate input)),
  ("input", toJson (toString input.val)), ("source", toJson emitted.source),
  ("provenance", Json.mkObj <| swarmField revision mask ++ [
    ("origin", origin), ("profileVersion", toJson profileVersion),
    ("functionVersion", toJson wordFunctionVersion),
    ("abstractionVersion", toJson abstractionVersion),
    ("generatorVersion", toJson (generatorVersionFor revision)),
    ("baseGeneratorVersion", toJson revision.version),
    ("boundaryVersion", toJson boundaryVersion),
    ("emitterVersion", toJson emitterVersion), ("wrapperVersion", toJson wrapperVersion),
    ("features", toJson ((features function.body).map featureName))]),
  ("contract", contractJson emitted input), ("executionFuel", toJson fuel),
  ("directCore", observe function input fuel)]

def emitCase (function : CheckedWordFunction) (input : Word)
    (origin : Json) (fuel : Nat) (revision : GeneratorRevision := .v1)
    (mask : FeatureMask := FeatureMask.all) : Except String Json := do
  unless Wire.programNodes (function.instantiate input) ≤ 512 do
    throw "applied primitive function exceeds the 512-node case limit"
  let emitted ← (emit function).mapError reprStr
  return makeCase function input emitted origin fuel revision mask

private def decodeProgram (json : Json) : Except String Wire.Program := do
  let program ← (Wire.decodeProgramWithBudget
    {maxDepth := 512, maxNodes := 512, maxIntegerBytes := 4096} json).mapError (fun
      | .protocol error => error.toJson.compress
      | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)
  unless Wire.programNodes program ≤ 512 do throw "Core program exceeds the 512-node case limit"
  return program

def checkedFunction (json : Json) : Except String CheckedWordFunction := do
  let some function := CheckedWordFunction.ofProgram? (← decodeProgram json) |
    throw "program is not a checked scalar Word-to-Word function"
  unless PrimitiveRenderer.supported function.body do
    throw "unsupported source primitive in the checked function"
  return function

def caseProgram (json : Json) : Except String CheckedInput := do
  unless (← json.getObjValAs? String "schema") = caseSchema do
    throw "unsupported semantic primitive case schema"
  let input ← inputWord (← json.getObjValAs? String "input")
  let program ← decodeProgram (← json.getObjVal? "program")
  match program with
  | { resultType := .word, dataDefinitions := [],
      body := .apply (.lambda .word .word body) (.word argument) } =>
      unless argument = input do throw "saved program argument differs from input"
      let some function := CheckedWordFunction.ofBody? body |
        throw "applied function is outside the checked scalar input profile"
      unless PrimitiveRenderer.supported function.body do
        throw "unsupported source primitive in the applied function"
      let admitted : CheckedInput := ⟨function, input⟩
      unless Wire.encodeProgram admitted.program == (← json.getObjVal? "program") do
        throw "saved Core function application is not canonical"
      return admitted
  | _ => throw "input case program is not a closed Word function application"

private def candidate (seed : Seed) (nodes : Nat) (revision : GeneratorRevision) :
    Except String (GeneratedProgram × Nat × CheckedWordFunction) := do
  unless minimumProgramNodes ≤ nodes && nodes ≤ 512 do
    throw "complete primitive program budget must be between the profile minimum and 512"
  let mask := revision.caseMask seed
  let generated ←
    (generate {seed, maxProgramNodes := nodes - appliedOverhead, revision, mask}).mapError reprStr
  let count := literalCount generated.program.body
  unless count > 0 do throw "generated body has no Word literal to abstract"
  let literalIndex := seed.toNat % count
  let some function := CheckedWordFunction.fromProgram? generated.checkedProgram literalIndex |
    throw "literal abstraction did not produce a checked Word function"
  unless Wire.programNodes (function.instantiate Word.zero) ≤ nodes do
    throw "applied primitive function exceeds its complete program budget"
  return (generated, literalIndex, function)

/-- A generation filter, not a claim that this finite bank covers a function. -/
def boundaryResults (function : CheckedWordFunction) (fuel : Nat) : Except String (List Word) := do
  boundaryInputs.mapM fun input =>
    match (function.instantiate input).toCore.runStateful fuel with
    | .done (.word value) _ => .ok value
    | .done _ _ => .error "boundary observation did not return a Word"
    | .outOfFuel _ => .error "boundary observation exhausted Core fuel"
    | .fault _ _ => .error "boundary observation produced a Core fault"

def inputSensitive (function : CheckedWordFunction) (fuel : Nat) : Except String Unit := do
  let results ← boundaryResults function fuel
  unless results.any (fun value => results.any (fun other => value != other)) do
    throw "all eight boundary inputs returned the same Word"

/-- Attempt limits count functions; case limits count individual runtime inputs.
One accepted function emits the fixed eight inputs in order, truncated by count. -/
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
        let (generated, literalIndex, function) ← candidate seed nodes revision
        let emitted ← (emit function).mapError (fun error => "unsupported source primitive: " ++ reprStr error)
        inputSensitive function fuel
        return (generated, literalIndex, function, emitted)
      match result with
      | .error error =>
          let resource := error == "boundary observation exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)),
            ("stage", toJson "primitive-profile"), ("reason", toJson error),
            ("code", toJson (if resource then "boundary-out-of-fuel"
              else if error.startsWith "unsupported source primitive:" then "unsupported-operation" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok (generated, literalIndex, function, emitted) =>
          for (input, inputIndex) in (inputSelection.inputs boundaryInputs seed).zipIdx do
            if cases.size < count then
              let origin := Json.mkObj [
                ("kind", toJson "primitive-generated"),
                ("seed", toJson (toString generated.initialSeed.toNat)),
                ("finalSeed", toJson (toString generated.finalSeed.toNat)),
                ("maxProgramNodes", toJson nodes),
                ("baseProgramNodes", toJson generated.maxProgramNodes),
                ("literalIndex", toJson literalIndex), ("inputIndex", toJson inputIndex),
                ("validationFuel", toJson fuel)]
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
  let revision := savedRevision provenance "baseGeneratorVersion"
  for (name, expected) in [
      ("generatorVersion", generatorVersionFor revision), ("profileVersion", profileVersion),
      ("baseGeneratorVersion", revision.version), ("boundaryVersion", boundaryVersion),
      ("functionVersion", wordFunctionVersion), ("abstractionVersion", abstractionVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do
      throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let mask ← savedMask provenance revision
  let emitted ← (emit admitted.function).mapError reprStr
  unless (← json.getObjValAs? String "source") = emitted.source do
    throw "saved source differs from emission of the original Core function"
  unless (← json.getObjVal? "contract") == contractJson emitted admitted.input do
    throw "saved contract metadata differs from the input wrapper"
  unless (← provenance.getObjVal? "features") ==
      toJson ((features admitted.function.body).map featureName) do
    throw "saved features differ from the original Core function"
  let kind ← origin.getObjValAs? String "kind"
  unless kind = "primitive-generated" || kind = "imported" || kind = "reduced" do
    throw "unsupported input case origin"
  if kind = "primitive-generated" then
    let seedText ← origin.getObjValAs? String "seed"
    let some seed := seedText.toNat? | throw "invalid saved seed"
    unless seed < 2 ^ 64 && toString seed = seedText do throw "noncanonical saved seed"
    unless mask == revision.caseMask (Seed.ofNat seed) do
      throw "saved swarm mask differs from its generation seed"
    let nodes ← origin.getObjValAs? Nat "maxProgramNodes"
    unless minimumProgramNodes ≤ nodes && nodes ≤ 512 do throw "saved generation budget exceeds profile limits"
    let (generated, literalIndex, function) ← candidate (Seed.ofNat seed) nodes revision
    unless (← origin.getObjValAs? Nat "literalIndex") = literalIndex do
      throw "saved literal index differs from the input profile"
    unless Wire.encodeProgram function.program == Wire.encodeProgram admitted.function.program do
      throw "saved function differs from its generation seed"
    unless (← origin.getObjValAs? String "finalSeed") = toString generated.finalSeed.toNat do
      throw "saved final seed differs from generation"
    unless (← origin.getObjValAs? Nat "baseProgramNodes") = generated.maxProgramNodes do
      throw "saved base program budget differs from generation"
    let inputIndex ← origin.getObjValAs? Nat "inputIndex"
    let inputSelection ← InputSelection.ofOrigin origin
    unless (inputSelection.inputs boundaryInputs (Seed.ofNat seed))[inputIndex]? = some admitted.input do
      throw "saved input differs from its boundary index"
    let validationFuel ← origin.getObjValAs? Nat "validationFuel"
    unless validationFuel ≤ 10000000 do throw "saved validation fuel exceeds limit"
    inputSensitive function validationFuel
    unless origin == inputSelection.record (Json.mkObj [
        ("kind", toJson "primitive-generated"), ("seed", toJson seedText),
        ("finalSeed", toJson (toString generated.finalSeed.toNat)), ("maxProgramNodes", toJson nodes),
        ("baseProgramNodes", toJson generated.maxProgramNodes), ("literalIndex", toJson literalIndex),
        ("inputIndex", toJson inputIndex), ("validationFuel", toJson validationFuel)]) do
      throw "generated primitive provenance is not canonical"
  else if kind = "imported" then
    unless origin == Json.mkObj [("kind", toJson "imported")] do
      throw "imported primitive provenance is not canonical"
  else
    let parentProgram ← origin.getObjVal? "parentProgram"
    let parentText ← origin.getObjValAs? String "parentInput"
    let parent ← caseProgram (Json.mkObj [
      ("schema", toJson caseSchema), ("program", parentProgram), ("input", toJson parentText)])
    unless (complexity admitted.program.body).isStrictlySmaller (complexity parent.program.body) do
      throw "saved primitive reduction is not strictly smaller than its checked parent"
    unless origin == Json.mkObj [("kind", toJson "reduced"), ("parentProgram", parentProgram),
        ("parentInput", toJson parentText)] do
      throw "reduced primitive provenance is not canonical"
  let fresh := makeCase admitted.function admitted.input emitted origin fuel revision mask
  unless (← fresh.getObjVal? "provenance") == provenance do
    throw "primitive provenance contains unexpected fields"
  return fresh

/-- Sealing includes both full Core typing and a strictly smaller applied case. -/
structure Reduction (source : CheckedInput) where private mk ::
  candidate : CheckedInput
  strict : (complexity candidate.program.body).StrictlySmaller (complexity source.program.body)

private def sealReduction (source : CheckedInput) (body : Wire.Expr) (input : Word) :
    Option (Reduction source) := do
  let function ← CheckedWordFunction.ofBody? body
  if !PrimitiveRenderer.supported function.body then none else do
    let candidate : CheckedInput := ⟨function, input⟩
    if strict : (complexity candidate.program.body).StrictlySmaller (complexity source.program.body)
      then some ⟨candidate, strict⟩ else none

/-- Reuse capture-avoiding G0 shrinking under a dummy Word binder. Only candidates
retaining that binder are extracted; the input function is then independently
sealed. Input reduction is separate and cannot change the emitted source. -/
def reductions (source : CheckedInput) : List (Reduction source) := Id.run do
  let wrapped : Wire.Program := {
    resultType := .word, dataDefinitions := [],
    body := .letE (.word Word.zero) source.function.body }
  let mut bodies : List Wire.Expr := [.word Word.zero, .var 0]
  if let some checked := CheckedWordProgram.ofProgram? wrapped then
    for reduced in shrink checked do
      if let .letE (.word value) body := reduced.body then
        if value = Word.zero then bodies := bodies ++ [body]
  let raw := bodies.map (fun body => (body, source.input)) ++
    [Word.zero, Word.ofNatModulo 1, Word.ofNatModulo (source.input.val / 2)].map
      (fun input => (source.function.body, input))
  let mut seen : List String := []
  let mut result := []
  for (body, input) in raw do
    if let some reduced := sealReduction source body input then
      let key := (Wire.encodeProgram reduced.candidate.program).compress
      if !seen.contains key then
        seen := key :: seen
        result := result ++ [reduced]
  return result

def shrinkCases (json : Json) (limit fuel : Nat) : Except String Json := do
  let _ ← replayCase json fuel
  let source ← caseProgram json
  let provenance ← json.getObjVal? "provenance"
  let revision := savedRevision provenance "baseGeneratorVersion"
  let mask ← savedMask provenance revision
  let mut cases : Array Json := #[]
  for reduced in (reductions source).take limit do
    let origin := Json.mkObj [
      ("kind", toJson "reduced"), ("parentProgram", Wire.encodeProgram source.program),
      ("parentInput", toJson (toString source.input.val))]
    cases := cases.push
      (← emitCase reduced.candidate.function reduced.candidate.input origin fuel revision mask)
  return Json.mkObj [("schema", toJson corpusSchema), ("cases", .arr cases)]

end Solcore.Synthesis.Source.Primitive
