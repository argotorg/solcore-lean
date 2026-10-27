import Solcore.Synthesis.Source.AggregateCases
import Solcore.Synthesis.Source.AggregateCallGraphEmitter
import Solcore.Synthesis.Source.PrimitiveCases

/-! Replayable cases for directly generated graphs that compose Word pairs,
Word sums, projections and case payload scopes with helper calls. The original
Core lambda chain is retained and executed independently of source lowering.
The template aggregate and scalar call-graph profiles remain unchanged. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.AggregateCallGraph
open Lean Solcore.Core Solcore.Synthesis.Core

def caseSchema : String := "solcore-lean.semantic-aggregate-call-graph-case.v1"
def profileVersion : String := "runtime-aggregate-call-graphs-v1/direct-grammar-v1"
def functionVersion : String := Aggregates.version
def generatorVersion : String := Solcore.Synthesis.Core.AggregateCallGraph.version
def boundaryVersion : String := Primitive.boundaryVersion
def shapeVersion : String := Solcore.Synthesis.Core.AggregateCallGraph.shapeVersion
def boundaryInputs : List Word := Primitive.boundaryInputs
def minimumProgramNodes : Nat := Solcore.Synthesis.Core.AggregateCallGraph.minimumAppliedNodes 1

def aggregateShapes (function : Aggregates.CheckedDAG) : List String :=
  Solcore.Synthesis.Core.AggregateCallGraph.structuralShapes function

def inputWord := Primitive.inputWord

structure CheckedInput where
  function : Aggregates.CheckedDAG
  input : Word

def CheckedInput.program (value : CheckedInput) : Wire.Program :=
  value.function.instantiate value.input

def observe (function : Aggregates.CheckedDAG) (input : Word) (fuel : Nat) : Json :=
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

def makeCase (function : Aggregates.CheckedDAG) (input : Word) (emitted : EmittedProgram)
    (origin : Json) (fuel : Nat) : Json := Json.mkObj [
  ("schema", toJson caseSchema), ("program", Wire.encodeProgram (function.instantiate input)),
  ("input", toJson (toString input.val)), ("source", toJson emitted.source),
  ("provenance", Json.mkObj [
    ("origin", origin), ("profileVersion", toJson profileVersion),
    ("functionVersion", toJson functionVersion), ("boundaryVersion", toJson boundaryVersion),
    ("shapeVersion", toJson shapeVersion), ("generatorVersion", toJson generatorVersion),
    ("emitterVersion", toJson emitterVersion), ("wrapperVersion", toJson wrapperVersion),
    ("features", toJson function.features), ("helperCount", toJson function.helpers.length),
    ("aggregateShapes", toJson (aggregateShapes function))]),
  ("contract", contractJson emitted input), ("executionFuel", toJson fuel),
  ("directCore", observe function input fuel)]

def emitCase (function : Aggregates.CheckedDAG) (input : Word)
    (origin : Json) (fuel : Nat) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds profile limit"
  unless Solcore.Synthesis.Core.AggregateCallGraph.graphWithinGrammar function do
    throw "aggregate graph is outside the call-graph composition grammar"
  unless Wire.programNodes (function.instantiate input) ≤ 512 do
    throw "applied aggregate graph exceeds the 512-node case limit"
  let emitted ← (emit function).mapError reprStr
  return makeCase function input emitted origin fuel

private def decodeProgram (json : Json) : Except String Wire.Program := do
  let program ← (Wire.decodeProgramWithBudget
    {maxDepth := 512, maxNodes := 512, maxIntegerBytes := 4096} json).mapError (fun
      | .protocol error => error.toJson.compress
      | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)
  unless Wire.programNodes program ≤ 512 do throw "Core program exceeds the 512-node case limit"
  return program

private def admitted (program : Wire.Program) : Except String Aggregates.CheckedDAG := do
  let some function := Aggregates.CheckedDAG.ofProgram? program |
    throw "program is not a checked aggregate Word function DAG"
  unless Solcore.Synthesis.Core.AggregateCallGraph.graphWithinGrammar function do
    throw "aggregate graph is outside the call-graph composition grammar"
  return function

def checkedFunction (json : Json) : Except String Aggregates.CheckedDAG := do
  admitted (← decodeProgram json)

def caseProgram (json : Json) : Except String CheckedInput := do
  unless (← json.getObjValAs? String "schema") = caseSchema do
    throw "unsupported semantic aggregate call-graph case schema"
  let input ← inputWord (← json.getObjValAs? String "input")
  let program ← decodeProgram (← json.getObjVal? "program")
  match program with
  | { resultType := .word, dataDefinitions := [], body := .apply functionBody (.word argument) } =>
      unless argument = input do throw "saved program argument differs from input"
      let function ← admitted {resultType := .function .word .word, dataDefinitions := [], body := functionBody}
      let value : CheckedInput := ⟨function, input⟩
      unless Wire.encodeProgram value.program == (← json.getObjVal? "program") do
        throw "saved Core aggregate graph application is not canonical"
      return value
  | _ => throw "aggregate call-graph case program is not a closed Word function DAG application"

def generatedFunction (seed : Seed) (nodes : Nat) :
    Except String (Aggregates.CheckedDAG × Json) := do
  let generated ← (Solcore.Synthesis.Core.AggregateCallGraph.generate
    {seed, maxProgramNodes := nodes}).mapError reprStr
  let origin := Json.mkObj [
    ("kind", toJson "aggregate-call-graph-generated"),
    ("seed", toJson (toString generated.initialSeed.toNat)),
    ("finalSeed", toJson (toString generated.finalSeed.toNat)),
    ("maxProgramNodes", toJson generated.maxProgramNodes),
    ("helperCount", toJson generated.function.helpers.length),
    ("bodyBudgets", toJson generated.bodyBudgets)]
  return (generated.function, origin)

/-- Helper-only calls are dead without an entry call. This is a syntactic
condition, not a claim that a branch, call or payload executes. -/
def hasEntryCall (function : Aggregates.CheckedDAG) : Bool :=
  (Aggregates.features function.entry).contains "functionCall"

def hasCallComposition (function : Aggregates.CheckedDAG) : Bool :=
  (aggregateShapes function).any Solcore.Synthesis.Core.AggregateCallGraph.callCompositionShapes.contains

def boundaryResults (function : Aggregates.CheckedDAG) (fuel : Nat) : Except String (List Word) :=
  boundaryInputs.mapM fun input =>
    match (function.instantiate input).toCore.runStateful fuel with
    | .done (.word value) _ => .ok value
    | .done _ _ => .error "boundary observation did not return a Word"
    | .outOfFuel _ => .error "boundary observation exhausted Core fuel"
    | .fault _ _ => .error "boundary observation produced a Core fault"

/-- Generated graphs need an entry call, a syntactic composition of a call with
an aggregate value or payload scope, and varied results over the eight inputs. -/
def inputSensitive (function : Aggregates.CheckedDAG) (fuel : Nat) : Except String Unit := do
  unless hasEntryCall function do throw "entry has no helper call"
  unless hasCallComposition function do throw "no call composes with an aggregate value or payload"
  let results ← boundaryResults function fuel
  unless results.any (fun value => results.any (fun other => value != other)) do
    throw "all eight boundary inputs returned the same Word"

/-- Attempts count complete graph candidates. Accepted graphs yield up to eight
cases in fixed input order. Fuel exhaustion is an inconclusive exclusion. -/
def generateCases (firstSeed : Seed) (nodes count attempts fuel : Nat)
    (inputSelection : InputSelection := .boundary) : Json := Id.run do
  let mut cases : Array Json := #[]
  let mut excluded : Array Json := #[]
  let mut attempted := 0
  for index in List.range attempts do
    if cases.size < count then
      attempted := attempted + 1
      let seed := Seed.ofNat (firstSeed.toNat + index)
      let result := do
        unless fuel ≤ 10000000 do throw "validation fuel exceeds profile limit"
        let (function, origin) ← generatedFunction seed nodes
        let emitted ← (emit function).mapError reprStr
        inputSensitive function fuel
        return (function, origin, emitted)
      match result with
      | .error error =>
          let resource := error == "boundary observation exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "aggregate-call-graph-profile"),
            ("reason", toJson error),
            ("code", toJson (if resource then "boundary-out-of-fuel" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok (function, origin, emitted) =>
          for (input, inputIndex) in (inputSelection.inputs boundaryInputs seed).zipIdx do
            if cases.size < count then
              let origin := (origin.setObjVal! "inputIndex" (toJson inputIndex)).setObjVal!
                "validationFuel" (toJson fuel)
              cases := cases.push
                (makeCase function input emitted (inputSelection.record origin) fuel)
  return Json.mkObj [("schema", toJson corpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

def replayCase (json : Json) (fuel : Nat) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds profile limit"
  let admitted ← caseProgram json
  let savedFuel ← json.getObjValAs? Nat "executionFuel"
  unless savedFuel ≤ 10000000 do throw "saved execution fuel exceeds profile limit"
  let provenance ← json.getObjVal? "provenance"
  for (name, expected) in [
      ("generatorVersion", generatorVersion), ("profileVersion", profileVersion),
      ("functionVersion", functionVersion), ("boundaryVersion", boundaryVersion),
      ("shapeVersion", shapeVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let emitted ← (emit admitted.function).mapError reprStr
  unless (← json.getObjValAs? String "source") = emitted.source do
    throw "saved source differs from emission of the original Core aggregate graph"
  unless (← json.getObjVal? "contract") == contractJson emitted admitted.input do
    throw "saved contract metadata differs from the aggregate call-graph wrapper"
  unless (← provenance.getObjVal? "features") == toJson admitted.function.features do
    throw "saved features differ from the original Core aggregate graph"
  unless (← provenance.getObjValAs? Nat "helperCount") = admitted.function.helpers.length do
    throw "saved helper count differs from the original Core aggregate graph"
  unless (← provenance.getObjVal? "aggregateShapes") == toJson (aggregateShapes admitted.function) do
    throw "saved aggregate shapes differ from the original Core aggregate graph"
  let kind ← origin.getObjValAs? String "kind"
  if kind = "aggregate-call-graph-generated" then
    let seedText ← origin.getObjValAs? String "seed"
    let some seed := seedText.toNat? | throw "invalid saved seed"
    unless seed < 2 ^ 64 && toString seed = seedText do throw "noncanonical saved seed"
    let nodes ← origin.getObjValAs? Nat "maxProgramNodes"
    let (function, expectedOrigin) ← generatedFunction (Seed.ofNat seed) nodes
    unless Wire.encodeProgram function.program == Wire.encodeProgram admitted.function.program do
      throw "saved aggregate graph differs from its generation seed"
    let inputIndex ← origin.getObjValAs? Nat "inputIndex"
    let inputSelection ← InputSelection.ofOrigin origin
    unless (inputSelection.inputs boundaryInputs (Seed.ofNat seed))[inputIndex]? = some admitted.input do
      throw "saved input differs from its boundary index"
    let validationFuel ← origin.getObjValAs? Nat "validationFuel"
    unless validationFuel ≤ 10000000 do throw "saved validation fuel exceeds limit"
    inputSensitive function validationFuel
    let canonicalOrigin := (expectedOrigin.setObjVal! "inputIndex" (toJson inputIndex)).setObjVal!
      "validationFuel" (toJson validationFuel)
    unless origin == inputSelection.record canonicalOrigin do throw "generated aggregate graph provenance is not canonical"
  else if kind = "imported" then
    unless origin == Json.mkObj [("kind", toJson "imported")] do
      throw "imported aggregate graph provenance is not canonical"
  else if kind = "reduced" then
    let parentProgram ← origin.getObjVal? "parentProgram"
    let parentText ← origin.getObjValAs? String "parentInput"
    let parent ← caseProgram (Json.mkObj [
      ("schema", toJson caseSchema), ("program", parentProgram), ("input", toJson parentText)])
    unless admitted.function.helpers.length = parent.function.helpers.length do
      throw "saved graph reduction changes helper count"
    unless Aggregate.bindingInventory admitted.function = Aggregate.bindingInventory parent.function do
      throw "saved graph reduction changes typed binders or payload scopes"
    unless (complexity admitted.program.body).isStrictlySmaller (complexity parent.program.body) do
      throw "saved graph reduction is not strictly smaller than its checked parent"
    unless origin == Json.mkObj [("kind", toJson "reduced"), ("parentProgram", parentProgram),
        ("parentInput", toJson parentText)] do
      throw "reduced aggregate graph provenance is not canonical"
  else throw "unsupported aggregate call-graph case origin"
  let fresh := makeCase admitted.function admitted.input emitted origin fuel
  unless (← fresh.getObjVal? "provenance") == provenance do
    throw "aggregate call-graph provenance contains unexpected fields"
  -- Ignore the saved observation, but require the complete canonical envelope.
  let _ ← json.getObjVal? "directCore"
  let savedEnvelope := json.setObjVal! "directCore" .null
  let freshEnvelope := (fresh.setObjVal! "directCore" .null).setObjVal!
    "executionFuel" (toJson savedFuel)
  unless savedEnvelope == freshEnvelope do throw "saved aggregate call-graph case envelope is not canonical"
  return fresh

structure Reduction (source : CheckedInput) where private mk ::
  candidate : CheckedInput
  sameHelperCount : candidate.function.helpers.length = source.function.helpers.length
  sameBindings : Aggregate.bindingInventory candidate.function = Aggregate.bindingInventory source.function
  strict : (complexity candidate.program.body).StrictlySmaller (complexity source.program.body)

/-- Reuse the typed aggregate reductions: every typed let, both case payload
scopes and every helper binding are retained, and each result was resealed.
Their canonical replacements stay inside this profile's grammar. -/
def reductions (source : CheckedInput) : List (Reduction source) :=
  (Aggregate.reductions ⟨source.function, source.input⟩).map fun reduced =>
    ⟨⟨reduced.candidate.function, reduced.candidate.input⟩, reduced.sameHelperCount,
      reduced.sameBindings, reduced.strict⟩

def shrinkCases (json : Json) (limit fuel : Nat) : Except String Json := do
  let _ ← replayCase json fuel
  let source ← caseProgram json
  let mut cases : Array Json := #[]
  for reduced in (reductions source).take limit do
    let origin := Json.mkObj [
      ("kind", toJson "reduced"), ("parentProgram", Wire.encodeProgram source.program),
      ("parentInput", toJson (toString source.input.val))]
    cases := cases.push (← emitCase reduced.candidate.function reduced.candidate.input origin fuel)
  return Json.mkObj [("schema", toJson corpusSchema), ("cases", .arr cases)]

end Solcore.Synthesis.Source.AggregateCallGraph
