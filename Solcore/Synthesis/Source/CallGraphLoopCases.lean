import Solcore.Synthesis.Source.CallGraphCases
import Solcore.Synthesis.Source.CallGraphLoopEmitter
import Solcore.Synthesis.Source.LoopCases

/-! Replayable bounded loops over directly generated scalar call graphs. Every
origin reconstructs the canonical finite Core reference from the saved scalar
graph and mask; source execution uses a real while loop. The older loop and
call-graph profiles and their replay rules remain unchanged. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.CallGraphLoop
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.Synthesis.Core.CallGraphLoop (CheckedPlan)

def caseSchema : String := "solcore-lean.semantic-call-graph-loop-case.v1"
def planSchema : String := "solcore-lean.call-graph-loop-plan.v1"
def profileVersion : String := "runtime-call-graph-loops-v1/direct-grammar-bounded-while-v1"
def functionVersion : String := Solcore.Synthesis.Core.CallGraphLoop.version
def generatorVersion : String := Solcore.Synthesis.Core.CallGraphLoop.grammarVersion
def boundaryVersion : String := "word-loop-boundary-bank-v1"
def stepBoundaryVersion : String := CallGraph.boundaryVersion
def callShapeVersion : String := CallGraph.callShapeVersion

/-- Iteration counts 0, 1, 3 and 7 under mask seven, plus both Word extremes. -/
def boundaryInputs : List Word := Loop.boundaryInputs

def inputWord := CallGraph.inputWord

def callShapes (plan : CheckedPlan) : List String := CallGraph.callShapes plan.graph

structure CheckedInput where
  plan : CheckedPlan
  input : Word

def CheckedInput.program (value : CheckedInput) : Wire.Program :=
  value.plan.instantiate value.input

def planJson (plan : CheckedPlan) : Json := Json.mkObj [
  ("schema", toJson planSchema), ("stepProgram", Wire.encodeProgram plan.graph.program),
  ("mask", toJson plan.mask)]

def checkedPlan (json : Json) : Except String CheckedPlan := do
  unless (← json.getObjValAs? String "schema") = planSchema do
    throw "unsupported call-graph loop plan schema"
  let graph ← CallGraph.checkedFunction (← json.getObjVal? "stepProgram")
  let mask ← json.getObjValAs? Nat "mask"
  let some plan := CheckedPlan.ofParts? graph mask |
    throw "call-graph loop plan has an invalid mask or failed the full Core checker"
  unless json == planJson plan do
    throw "saved call-graph loop plan differs from its canonical checked representation"
  unless Wire.programNodes (plan.instantiate Word.zero) ≤ 512 do
    throw "canonical applied call-graph loop exceeds the 512-node case limit"
  return plan

def observe (plan : CheckedPlan) (input : Word) (fuel : Nat) : Json :=
  let fields := match (plan.instantiate input).toCore.runStateful fuel with
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

def makeCase (plan : CheckedPlan) (input : Word) (emitted : EmittedProgram)
    (origin : Json) (fuel : Nat) : Json := Json.mkObj [
  ("schema", toJson caseSchema), ("loopPlan", planJson plan),
  ("program", Wire.encodeProgram (plan.instantiate input)),
  ("input", toJson (toString input.val)), ("source", toJson emitted.source),
  ("provenance", Json.mkObj [
    ("origin", origin), ("profileVersion", toJson profileVersion),
    ("functionVersion", toJson functionVersion), ("loopVersion", toJson BoundedLoop.version),
    ("stepFunctionVersion", toJson wordFunctionDAGVersion),
    ("aggregateVersion", toJson Aggregates.version),
    ("boundaryVersion", toJson boundaryVersion),
    ("stepBoundaryVersion", toJson stepBoundaryVersion),
    ("callShapeVersion", toJson callShapeVersion),
    ("generatorVersion", toJson generatorVersion),
    ("emitterVersion", toJson emitterVersion), ("wrapperVersion", toJson wrapperVersion),
    ("features", toJson plan.features),
    ("helperCount", toJson plan.graph.helpers.length), ("callShapes", toJson (callShapes plan))]),
  ("contract", contractJson emitted input), ("executionFuel", toJson fuel),
  ("directCore", observe plan input fuel)]

def emitCase (plan : CheckedPlan) (input : Word) (origin : Json) (fuel : Nat) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds profile limit"
  unless Wire.programNodes (plan.instantiate input) ≤ 512 do
    throw "canonical applied call-graph loop exceeds the 512-node case limit"
  let emitted ← (emit plan).mapError reprStr
  return makeCase plan input emitted origin fuel

/-- Even imported and reduced cases retain the exact canonical reference; no
origin makes a saved arbitrary Core program trusted. -/
def caseProgram (json : Json) : Except String CheckedInput := do
  unless (← json.getObjValAs? String "schema") = caseSchema do
    throw "unsupported semantic call-graph loop case schema"
  let plan ← checkedPlan (← json.getObjVal? "loopPlan")
  let input ← inputWord (← json.getObjValAs? String "input")
  let program ← (Wire.decodeProgramWithBudget
    {maxDepth := 512, maxNodes := 512, maxIntegerBytes := 4096}
    (← json.getObjVal? "program")).mapError (fun
      | .protocol error => error.toJson.compress
      | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)
  unless Wire.encodeProgram program == Wire.encodeProgram (plan.instantiate input) do
    throw "saved Core program differs from its canonical call-graph loop plan and runtime input"
  let admitted : CheckedInput := ⟨plan, input⟩
  unless Wire.encodeProgram admitted.program == (← json.getObjVal? "program") do
    throw "saved Core call-graph loop application is not canonical"
  return admitted

def generatedPlan (seed : Seed) (nodes : Nat) : Except String (CheckedPlan × Json) := do
  let generated ← (Solcore.Synthesis.Core.CallGraphLoop.generate
    {seed, maxProgramNodes := nodes}).mapError reprStr
  let step := generated.step
  let stepOrigin := Json.mkObj [
    ("kind", toJson "call-graph-generated"),
    ("seed", toJson (toString step.initialSeed.toNat)),
    ("finalSeed", toJson (toString step.finalSeed.toNat)),
    ("maxProgramNodes", toJson step.maxProgramNodes),
    ("helperCount", toJson step.function.helpers.length),
    ("bodyBudgets", toJson step.bodyBudgets)]
  let origin := Json.mkObj [
    ("kind", toJson "call-graph-loop-generated"),
    ("seed", toJson (toString generated.initialSeed.toNat)),
    ("finalSeed", toJson (toString generated.finalSeed.toNat)),
    ("maxProgramNodes", toJson generated.maxProgramNodes),
    ("mask", toJson generated.plan.mask), ("stepBudget", toJson generated.stepBudget),
    ("stepOrigin", stepOrigin)]
  return (generated.plan, origin)

def boundaryResults (plan : CheckedPlan) (fuel : Nat) : Except String (List Word) :=
  boundaryInputs.mapM fun input =>
    match (plan.instantiate input).toCore.runStateful fuel with
    | .done (.word value) _ => .ok value
    | .done _ _ => .error "loop boundary observation did not return a Word"
    | .outOfFuel _ => .error "boundary observation exhausted Core fuel"
    | .fault _ _ => .error "loop boundary observation produced a Core fault"

/-- The step must contain an entry call and vary across the primitive bank.
Zero-trip inputs return themselves, so a positive-trip input must also change.
These are original Core observations, not executed source or opcode coverage. -/
def inputSensitive (plan : CheckedPlan) (fuel : Nat) : Except String Unit := do
  CallGraph.inputSensitive plan.graph fuel
  let results ← boundaryResults plan fuel
  unless (boundaryInputs.zip results).any (fun (input, result) =>
      (input.bitAnd (Word.ofNatModulo plan.mask)).val > 0 && result != input) do
    throw "all positive-trip boundary inputs returned their original input"

/-- Attempts count complete plan candidates. Accepted plans yield up to six
cases in fixed input order. Fuel exhaustion is an inconclusive exclusion. -/
def generateCases (firstSeed : Seed) (nodes count attempts fuel : Nat) : Json := Id.run do
  let mut cases : Array Json := #[]
  let mut excluded : Array Json := #[]
  let mut attempted := 0
  for index in List.range attempts do
    if cases.size < count then
      attempted := attempted + 1
      let seed := Seed.ofNat (firstSeed.toNat + index)
      let result := do
        unless fuel ≤ 10000000 do throw "validation fuel exceeds profile limit"
        let (plan, origin) ← generatedPlan seed nodes
        let emitted ← (emit plan).mapError reprStr
        inputSensitive plan fuel
        return (plan, origin, emitted)
      match result with
      | .error error =>
          let resource := error == "boundary observation exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "call-graph-loop-profile"),
            ("reason", toJson error),
            ("code", toJson (if resource then "boundary-out-of-fuel" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok (plan, origin, emitted) =>
          for (input, inputIndex) in boundaryInputs.zipIdx do
            if cases.size < count then
              let origin := (origin.setObjVal! "inputIndex" (toJson inputIndex)).setObjVal!
                "validationFuel" (toJson fuel)
              cases := cases.push (makeCase plan input emitted origin fuel)
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
      ("functionVersion", functionVersion), ("loopVersion", BoundedLoop.version),
      ("stepFunctionVersion", wordFunctionDAGVersion), ("aggregateVersion", Aggregates.version),
      ("boundaryVersion", boundaryVersion), ("stepBoundaryVersion", stepBoundaryVersion),
      ("callShapeVersion", callShapeVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let emitted ← (emit admitted.plan).mapError reprStr
  unless (← json.getObjValAs? String "source") = emitted.source do
    throw "saved source differs from emission of the canonical call-graph loop plan"
  unless (← json.getObjVal? "contract") == contractJson emitted admitted.input do
    throw "saved contract metadata differs from the call-graph loop wrapper"
  unless (← provenance.getObjVal? "features") == toJson admitted.plan.features do
    throw "saved features differ from the original Core call graph"
  unless (← provenance.getObjValAs? Nat "helperCount") = admitted.plan.graph.helpers.length do
    throw "saved helper count differs from the original Core call graph"
  unless (← provenance.getObjVal? "callShapes") == toJson (callShapes admitted.plan) do
    throw "saved call shapes differ from the original Core call graph"
  let kind ← origin.getObjValAs? String "kind"
  if kind = "call-graph-loop-generated" then
    let seedText ← origin.getObjValAs? String "seed"
    let some seed := seedText.toNat? | throw "invalid saved seed"
    unless seed < 2 ^ 64 && toString seed = seedText do throw "noncanonical saved seed"
    let nodes ← origin.getObjValAs? Nat "maxProgramNodes"
    let (plan, expectedOrigin) ← generatedPlan (Seed.ofNat seed) nodes
    unless planJson plan == planJson admitted.plan do
      throw "saved call-graph loop plan differs from its generation seed"
    let inputIndex ← origin.getObjValAs? Nat "inputIndex"
    unless boundaryInputs[inputIndex]? = some admitted.input do
      throw "saved input differs from its loop boundary index"
    let validationFuel ← origin.getObjValAs? Nat "validationFuel"
    unless validationFuel ≤ 10000000 do throw "saved validation fuel exceeds limit"
    inputSensitive plan validationFuel
    let canonicalOrigin := (expectedOrigin.setObjVal! "inputIndex" (toJson inputIndex)).setObjVal!
      "validationFuel" (toJson validationFuel)
    unless origin == canonicalOrigin do throw "generated call-graph loop provenance is not canonical"
  else if kind = "imported" then
    unless origin == Json.mkObj [("kind", toJson "imported")] do
      throw "imported call-graph loop provenance is not canonical"
  else if kind = "reduced" then
    let parentPlan ← origin.getObjVal? "parentPlan"
    let parentText ← origin.getObjValAs? String "parentInput"
    let parent : CheckedInput := ⟨← checkedPlan parentPlan, ← inputWord parentText⟩
    unless admitted.plan.graph.helpers.length = parent.plan.graph.helpers.length do
      throw "saved loop reduction changes helper count"
    unless admitted.plan.mask ≤ parent.plan.mask do
      throw "saved loop reduction increases its mask"
    unless (complexity admitted.program.body).isStrictlySmaller (complexity parent.program.body) do
      throw "saved loop reduction is not strictly smaller than its checked parent"
    unless origin == Json.mkObj [("kind", toJson "reduced"), ("parentPlan", parentPlan),
        ("parentInput", toJson parentText)] do
      throw "reduced call-graph loop provenance is not canonical"
  else throw "unsupported call-graph loop case origin"
  let fresh := makeCase admitted.plan admitted.input emitted origin fuel
  unless (← fresh.getObjVal? "provenance") == provenance do
    throw "call-graph loop provenance contains unexpected fields"
  -- Ignore the saved observation, but require the complete canonical envelope.
  let _ ← json.getObjVal? "directCore"
  let savedEnvelope := json.setObjVal! "directCore" .null
  let freshEnvelope := (fresh.setObjVal! "directCore" .null).setObjVal!
    "executionFuel" (toJson savedFuel)
  unless savedEnvelope == freshEnvelope do throw "saved call-graph loop case envelope is not canonical"
  return fresh

structure Reduction (source : CheckedInput) where private mk ::
  candidate : CheckedInput
  sameHelperCount : candidate.plan.graph.helpers.length = source.plan.graph.helpers.length
  boundedMask : candidate.plan.mask ≤ source.plan.mask
  strict : (complexity candidate.program.body).StrictlySmaller (complexity source.program.body)

private def sealReduction (source : CheckedInput) (graph : CheckedWordFunctionDAG)
    (mask : Nat) (input : Word) : Option (Reduction source) := do
  let plan ← CheckedPlan.ofParts? graph mask
  let candidate : CheckedInput := ⟨plan, input⟩
  if count : candidate.plan.graph.helpers.length = source.plan.graph.helpers.length then
    if bounded : candidate.plan.mask ≤ source.plan.mask then
      if strict : (complexity candidate.program.body).StrictlySmaller (complexity source.program.body) then
        some ⟨candidate, count, bounded, strict⟩
      else none
    else none
  else none

/-- Typed scalar graph reductions keep every helper binding. Smaller masks
remove complete canonical guards; every candidate is resealed as a plan. -/
def reductions (source : CheckedInput) : List (Reduction source) := Id.run do
  let mut raw : List (CheckedWordFunctionDAG × Nat × Word) := []
  for reduced in CallGraph.reductions ⟨source.plan.graph, source.input⟩ do
    raw := raw ++ [(reduced.candidate.function, source.plan.mask, reduced.candidate.input)]
  for mask in [0, 1, 3] do
    if mask < source.plan.mask then raw := raw ++ [(source.plan.graph, mask, source.input)]
  for input in boundaryInputs do
    raw := raw ++ [(source.plan.graph, source.plan.mask, input)]
  let mut seen : List String := []
  let mut result := []
  for (graph, mask, input) in raw do
    if let some reduced := sealReduction source graph mask input then
      let key := (Wire.encodeProgram reduced.candidate.program).compress
      if !seen.contains key then
        seen := key :: seen
        result := result ++ [reduced]
  return result

def shrinkCases (json : Json) (limit fuel : Nat) : Except String Json := do
  let _ ← replayCase json fuel
  let source ← caseProgram json
  let mut cases : Array Json := #[]
  for reduced in (reductions source).take limit do
    let origin := Json.mkObj [
      ("kind", toJson "reduced"), ("parentPlan", planJson source.plan),
      ("parentInput", toJson (toString source.input.val))]
    cases := cases.push (← emitCase reduced.candidate.plan reduced.candidate.input origin fuel)
  return Json.mkObj [("schema", toJson corpusSchema), ("cases", .arr cases)]

end Solcore.Synthesis.Source.CallGraphLoop
