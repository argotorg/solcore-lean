import Solcore.Synthesis.Source.AggregateCases
import Solcore.Synthesis.Source.ClosureEmitter

/-! Closure cases retain a checked step DAG and capture variant. Every origin
reconstructs the actual original Core program, including explicit Word snapshots
before closure creation. Shrinking preserves the capture variant and step scope. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.Closure
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.Synthesis.Core.Closure (CheckedPlan)

def caseSchema : String := "solcore-lean.semantic-closure-case.v1"
def planSchema : String := "solcore-lean.closure-plan.v1"
def profileVersion : String := "runtime-closures-v2/capture-seed-v1"
def templateVersion : String := "word-closure-snapshot-v1"

def boundaryInputs : List Word :=
  [Word.zero, Word.ofNatModulo 1, Word.maximum, Word.ofNatModulo (2 ^ 255)]

structure CheckedInput where
  plan : CheckedPlan
  input : Word

def CheckedInput.program (value : CheckedInput) : Wire.Program :=
  value.plan.instantiate value.input

def planJson (plan : CheckedPlan) : Json := Json.mkObj [
  ("schema", toJson planSchema), ("stepProgram", Wire.encodeProgram plan.step.program),
  ("variant", toJson plan.variant.name)]

def checkedPlan (json : Json) : Except String CheckedPlan := do
  unless (← json.getObjValAs? String "schema") = planSchema do
    throw "unsupported closure plan schema"
  let step ← Aggregate.checkedFunction (← json.getObjVal? "stepProgram")
  let variantText ← json.getObjValAs? String "variant"
  let some variant := Solcore.Synthesis.Core.Closure.Variant.ofString? variantText | throw "unsupported closure variant"
  let some plan := CheckedPlan.ofParts? step variant |
    throw "closure plan failed the full Core checker"
  unless json == planJson plan do throw "saved closure plan differs from its canonical checked representation"
  unless Wire.programNodes (plan.instantiate Word.zero) ≤ 512 do
    throw "canonical applied closure exceeds the 512-node case limit"
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
  ("schema", toJson caseSchema), ("closurePlan", planJson plan),
  ("program", Wire.encodeProgram (plan.instantiate input)),
  ("input", toJson (toString input.val)), ("source", toJson emitted.source),
  ("provenance", Json.mkObj [
    ("origin", origin), ("profileVersion", toJson profileVersion),
    ("functionVersion", toJson Solcore.Synthesis.Core.Closure.version), ("templateVersion", toJson templateVersion),
    ("stepProfileVersion", toJson Aggregate.profileVersion),
    ("stepFunctionVersion", toJson Aggregates.version),
    ("stepTemplateVersion", toJson Aggregate.templateVersion),
    ("generatorVersion", toJson generatorVersion),
    ("emitterVersion", toJson emitterVersion), ("wrapperVersion", toJson wrapperVersion),
    ("features", toJson plan.step.features)]),
  ("contract", contractJson emitted input), ("executionFuel", toJson fuel),
  ("directCore", observe plan input fuel)]

def emitCase (plan : CheckedPlan) (input : Word) (origin : Json) (fuel : Nat) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
  unless Wire.programNodes (plan.instantiate input) ≤ 512 do
    throw "canonical applied closure exceeds the 512-node case limit"
  let emitted ← (emit plan).mapError reprStr
  return makeCase plan input emitted origin fuel

/-- Even imported and reduced cases must retain the exact canonical reference;
there is no origin for which a saved arbitrary Core program is trusted. -/
def caseProgram (json : Json) : Except String CheckedInput := do
  unless (← json.getObjValAs? String "schema") = caseSchema do
    throw "unsupported semantic closure case schema"
  let plan ← checkedPlan (← json.getObjVal? "closurePlan")
  let input ← Input.inputWord (← json.getObjValAs? String "input")
  let program ← (Wire.decodeProgramWithBudget
    {maxDepth := 512, maxNodes := 512, maxIntegerBytes := 4096}
    (← json.getObjVal? "program")).mapError (fun
      | .protocol error => error.toJson.compress
      | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)
  unless Wire.encodeProgram program == Wire.encodeProgram (plan.instantiate input) do
    throw "saved Core program differs from its canonical closure plan and runtime input"
  return ⟨plan, input⟩

def variantFor (seed : Seed) : Solcore.Synthesis.Core.Closure.Variant :=
  if seed.toNat / 3 % 2 = 0 then .snapshot else .independent

/-- The actual wrapper syntax supplies the step budget. The complete applied
program is measured and checked again after the independent step generator. -/
def generatedPlan (seed : Seed) (nodes : Nat) : Except String (CheckedPlan × Json) := do
  let variant := variantFor seed
  let overhead := Solcore.Synthesis.Core.Closure.appliedOverhead variant
  unless nodes ≤ 512 && overhead < nodes do
    throw "node budget is too small for the selected closure variant or exceeds 512"
  let (step, stepOrigin) ← Aggregate.generatedFunction seed (nodes - overhead)
  let some plan := CheckedPlan.ofParts? step variant |
    throw "generated closure plan failed the full Core checker"
  unless Wire.programNodes (plan.instantiate Word.zero) ≤ nodes do
    throw "canonical applied closure exceeds its requested node budget"
  let origin := Json.mkObj [
    ("kind", toJson "closure-generated"), ("seed", toJson (toString seed.toNat)),
    ("finalSeed", ← stepOrigin.getObjVal? "finalSeed"), ("maxProgramNodes", toJson nodes),
    ("variant", toJson variant.name), ("stepOrigin", stepOrigin)]
  return (plan, origin)

def boundaryResults (plan : CheckedPlan) (fuel : Nat) : Except String (List Word) :=
  boundaryInputs.mapM fun input =>
    match (plan.instantiate input).toCore.runStateful fuel with
    | .done (.word value) _ => .ok value
    | .done _ _ => .error "closure boundary observation did not return a Word"
    | .outOfFuel _ => .error "boundary observation exhausted Core fuel"
    | .fault _ _ => .error "closure boundary observation produced a Core fault"

/-- Require both the generated step and the complete closure reference to
vary over the fixed boundary inputs. Imported and reduced constants remain valid. -/
def inputSensitive (plan : CheckedPlan) (fuel : Nat) : Except String Unit := do
  Aggregate.inputSensitive plan.step fuel
  let results ← boundaryResults plan fuel
  unless results.any (fun result => some result != results.head?) do
    throw "all closure boundary inputs returned the same result"

def generateCases (firstSeed : Seed) (nodes count attempts fuel : Nat) : Json := Id.run do
  let mut cases : Array Json := #[]
  let mut excluded : Array Json := #[]
  let mut attempted := 0
  for index in List.range attempts do
    if cases.size < count then
      attempted := attempted + 1
      let seed := Seed.ofNat (firstSeed.toNat + index)
      let result := do
        let (plan, origin) ← generatedPlan seed nodes
        let emitted ← (emit plan).mapError reprStr
        inputSensitive plan fuel
        return (plan, origin, emitted)
      match result with
      | .error error =>
          let resource := error == "boundary observation exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "closure-profile"),
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

structure Reduction (source : CheckedInput) where private mk ::
  candidate : CheckedInput
  sameHelperCount : candidate.plan.step.helpers.length = source.plan.step.helpers.length
  sameBindings : Aggregate.bindingInventory candidate.plan.step = Aggregate.bindingInventory source.plan.step
  sameVariant : candidate.plan.variant = source.plan.variant
  strict : (complexity candidate.program.body).StrictlySmaller (complexity source.program.body)

private def sealReduction (source : CheckedInput) (step : Aggregates.CheckedDAG)
    (input : Word) : Option (Reduction source) := do
  let plan ← CheckedPlan.ofParts? step source.plan.variant
  let candidate : CheckedInput := ⟨plan, input⟩
  if count : candidate.plan.step.helpers.length = source.plan.step.helpers.length then
    if bindings : Aggregate.bindingInventory candidate.plan.step = Aggregate.bindingInventory source.plan.step then
      if variant : candidate.plan.variant = source.plan.variant then
        if strict : (complexity candidate.program.body).StrictlySmaller (complexity source.program.body) then
          some ⟨candidate, count, bindings, variant, strict⟩
        else none
      else none
    else none
  else none

/-- Step reductions retain all typed binders, including sum case payloads.
The closure variant is fixed; every candidate is fully checked and strictly
smaller as a complete applied reference, including its runtime input. -/
def reductions (source : CheckedInput) : List (Reduction source) := Id.run do
  let mut raw : List (Aggregates.CheckedDAG × Word) := []
  for reduced in Aggregate.reductions ⟨source.plan.step, source.input⟩ do
    raw := raw ++ [(reduced.candidate.function, reduced.candidate.input)]
  for input in boundaryInputs do raw := raw ++ [(source.plan.step, input)]
  let mut seen : List String := []
  let mut result := []
  for (step, input) in raw do
    if let some reduced := sealReduction source step input then
      let key := (Wire.encodeProgram reduced.candidate.program).compress
      if !seen.contains key then
        seen := key :: seen
        result := result ++ [reduced]
  return result

def replayCase (json : Json) (fuel : Nat) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
  let admitted ← caseProgram json
  let provenance ← json.getObjVal? "provenance"
  for (name, expected) in [
      ("generatorVersion", generatorVersion), ("profileVersion", profileVersion),
      ("functionVersion", Solcore.Synthesis.Core.Closure.version), ("templateVersion", templateVersion),
      ("stepProfileVersion", Aggregate.profileVersion), ("stepFunctionVersion", Aggregates.version),
      ("stepTemplateVersion", Aggregate.templateVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let emitted ← (emit admitted.plan).mapError reprStr
  unless (← json.getObjValAs? String "source") = emitted.source do
    throw "saved source differs from emission of the canonical closure plan"
  unless (← json.getObjVal? "contract") == contractJson emitted admitted.input do
    throw "saved contract metadata differs from the closure wrapper"
  unless (← provenance.getObjVal? "features") == toJson admitted.plan.step.features do
    throw "saved features differ from the checked step DAG"
  let kind ← origin.getObjValAs? String "kind"
  unless kind = "closure-generated" || kind = "imported" || kind = "reduced" do
    throw "unsupported closure case origin"
  if kind = "closure-generated" then
    let seedText ← origin.getObjValAs? String "seed"
    unless seedText.length ≤ 20 do throw "saved seed exceeds limit"
    let some seed := seedText.toNat? | throw "invalid saved seed"
    unless seed < 2 ^ 64 && toString seed = seedText do throw "noncanonical saved seed"
    let nodes ← origin.getObjValAs? Nat "maxProgramNodes"
    let (plan, expectedOrigin) ← generatedPlan (Seed.ofNat seed) nodes
    unless planJson plan == planJson admitted.plan do
      throw "saved closure plan differs from its generation seed"
    let inputIndex ← origin.getObjValAs? Nat "inputIndex"
    unless boundaryInputs[inputIndex]? = some admitted.input do
      throw "saved input differs from its closure boundary index"
    let validationFuel ← origin.getObjValAs? Nat "validationFuel"
    unless validationFuel ≤ 10000000 do throw "saved validation fuel exceeds limit"
    unless origin == (expectedOrigin.setObjVal! "inputIndex" (toJson inputIndex)).setObjVal!
        "validationFuel" (toJson validationFuel) do throw "saved origin differs from generated closure provenance"
    inputSensitive plan validationFuel
  else if kind = "imported" then
    unless origin == Json.mkObj [("kind", toJson "imported")] do throw "noncanonical imported origin"
  else if kind = "reduced" then
    let parentPlan ← checkedPlan (← origin.getObjVal? "parentPlan")
    let parentInput ← Input.inputWord (← origin.getObjValAs? String "parentInput")
    let parent : CheckedInput := ⟨parentPlan, parentInput⟩
    unless (← origin.getObjVal? "parentProgram") == Wire.encodeProgram parent.program do
      throw "reduction parent program differs from its canonical plan and input"
    unless admitted.plan.variant == parent.plan.variant &&
        (sealReduction parent admitted.plan.step admitted.input).isSome do
      throw "reduction changed its variant/binders or did not strictly decrease"
    unless origin == Json.mkObj [("kind", toJson "reduced"), ("parentPlan", planJson parent.plan),
        ("parentProgram", Wire.encodeProgram parent.program), ("parentInput", toJson (toString parent.input.val))] do
      throw "noncanonical reduced origin"
  return makeCase admitted.plan admitted.input emitted origin fuel


def shrinkCases (json : Json) (limit fuel : Nat) : Except String Json := do
  let _ ← replayCase json fuel
  let source ← caseProgram json
  let mut cases : Array Json := #[]
  for reduced in (reductions source).take limit do
    let origin := Json.mkObj [
      ("kind", toJson "reduced"), ("parentProgram", Wire.encodeProgram source.program),
      ("parentPlan", planJson source.plan), ("parentInput", toJson (toString source.input.val))]
    cases := cases.push (← emitCase reduced.candidate.plan reduced.candidate.input origin fuel)
  return Json.mkObj [("schema", toJson corpusSchema), ("cases", .arr cases)]

end Solcore.Synthesis.Source.Closure
