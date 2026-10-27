import Solcore.Synthesis.Source.AggregateCases
import Solcore.Synthesis.Source.RecursionEmitter

/-! A recursion case retains its checked step DAG, depth mask, recursion form
and the independently executable canonical Core reference. Every origin
reconstructs the full reference before replay; source execution makes real
recursive calls instead of running the ordinal guards. A case's depth is
`input & mask`, prescribed by the plan and the input. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.Recursion
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.Synthesis.Core.Recursion (CheckedPlan Form)

def caseSchema : String := "solcore-lean.semantic-recursion-case.v1"
def planSchema : String := "solcore-lean.recursion-plan.v1"
def profileVersion : String := "runtime-recursion-v1/bounded-depth-seed-v1"
def templateVersion : String := "bounded-word-recursion-v1"

/-- Depths zero to three and seven under mask seven, and an even positive depth. -/
def boundaryInputs : List Word :=
  [Word.zero, Word.ofNatModulo 1, Word.ofNatModulo 2, Word.ofNatModulo 3, Word.ofNatModulo 7,
    Word.maximum, Word.ofNatModulo (2 ^ 255)]

structure CheckedInput where
  plan : CheckedPlan
  input : Word

def CheckedInput.program (value : CheckedInput) : Wire.Program :=
  value.plan.instantiate value.input

def planJson (plan : CheckedPlan) : Json := Json.mkObj [
  ("schema", toJson planSchema), ("stepProgram", Wire.encodeProgram plan.step.program),
  ("depthMask", toJson plan.mask), ("form", toJson plan.form.name)]

def checkedPlan (json : Json) : Except String CheckedPlan := do
  unless (← json.getObjValAs? String "schema") = planSchema do
    throw "unsupported recursion plan schema"
  let step ← Aggregate.checkedFunction (← json.getObjVal? "stepProgram")
  let mask ← json.getObjValAs? Nat "depthMask"
  let some form := Form.ofString? (← json.getObjValAs? String "form") |
    throw "unsupported recursion form"
  let some plan := CheckedPlan.ofParts? step mask form |
    throw "recursion plan has an invalid depth mask or failed the full Core checker"
  unless json == planJson plan do
    throw "saved recursion plan differs from its canonical checked representation"
  unless Wire.programNodes (plan.instantiate Word.zero) ≤ 512 do
    throw "canonical applied recursion exceeds the 512-node case limit"
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
    (origin : Json) (fuel : Nat) (revision : GeneratorRevision := .v1)
    (mask : FeatureMask := FeatureMask.all) : Json := Json.mkObj [
  ("schema", toJson caseSchema), ("recursionPlan", planJson plan),
  ("program", Wire.encodeProgram (plan.instantiate input)),
  ("input", toJson (toString input.val)), ("source", toJson emitted.source),
  ("provenance", Json.mkObj <| swarmField revision mask ++ [
    ("origin", origin), ("profileVersion", toJson profileVersion),
    ("functionVersion", toJson Recursion.version), ("templateVersion", toJson templateVersion),
    ("stepProfileVersion", toJson Aggregate.profileVersion),
    ("stepFunctionVersion", toJson Aggregates.version),
    ("stepTemplateVersion", toJson Aggregate.templateVersion),
    ("generatorVersion", toJson revision.version),
    ("emitterVersion", toJson emitterVersion), ("wrapperVersion", toJson wrapperVersion),
    ("features", toJson plan.step.features)]),
  ("contract", contractJson emitted input), ("executionFuel", toJson fuel),
  ("directCore", observe plan input fuel)]

def emitCase (plan : CheckedPlan) (input : Word) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1)
    (mask : FeatureMask := FeatureMask.all) : Except String Json := do
  unless Wire.programNodes (plan.instantiate input) ≤ 512 do
    throw "canonical applied recursion exceeds the 512-node case limit"
  let emitted ← (emit plan).mapError reprStr
  return makeCase plan input emitted origin fuel revision mask

/-- Even imported and reduced cases must retain the exact canonical reference;
there is no origin for which a saved arbitrary Core program is trusted. -/
def caseProgram (json : Json) : Except String CheckedInput := do
  unless (← json.getObjValAs? String "schema") = caseSchema do
    throw "unsupported semantic recursion case schema"
  let plan ← checkedPlan (← json.getObjVal? "recursionPlan")
  let input ← Input.inputWord (← json.getObjValAs? String "input")
  let program ← (Wire.decodeProgramWithBudget
    {maxDepth := 512, maxNodes := 512, maxIntegerBytes := 4096}
    (← json.getObjVal? "program")).mapError (fun
      | .protocol error => error.toJson.compress
      | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)
  unless Wire.encodeProgram program == Wire.encodeProgram (plan.instantiate input) do
    throw "saved Core program differs from its canonical recursion plan and runtime input"
  return ⟨plan, input⟩

/-- The nine generation shapes: each form at depth masks one, three and seven. -/
def shapes : List (Nat × Form) :=
  Form.all.flatMap fun form => [(1, form), (3, form), (7, form)]

/-- Separates the shape stream from other uses of a case seed. -/
private def shapeDomain : UInt64 := 0x7265637572736501

/-- A SplitMix64 hash of the seed, so that consecutive seeds vary in shape
independently of the step's helper count and template. -/
def shapeFor (seed : Seed) : Nat × Form :=
  shapes[(GeneratorV2.mix (seed.toUInt64 ^^^ shapeDomain)).toNat % shapes.length]?.getD (7, .tail)

/-- The actual wrapper syntax supplies the step budget. The complete applied
program is measured and checked again after the independent step generator. -/
def generatedPlan (seed : Seed) (nodes : Nat) (revision : GeneratorRevision := .v1) :
    Except String (CheckedPlan × Json) := do
  let (mask, form) := shapeFor seed
  let overhead := Recursion.appliedOverhead mask form
  unless nodes ≤ 512 && overhead < nodes do
    throw "node budget is too small for the selected recursion shape or exceeds 512"
  let (step, stepOrigin) ← Aggregate.generatedFunction seed (nodes - overhead) revision
  let some plan := CheckedPlan.ofParts? step mask form |
    throw "generated recursion plan failed the full Core checker"
  unless Wire.programNodes (plan.instantiate Word.zero) ≤ nodes do
    throw "canonical applied recursion exceeds its requested node budget"
  let origin := Json.mkObj [
    ("kind", toJson "recursion-generated"), ("seed", toJson (toString seed.toNat)),
    ("finalSeed", ← stepOrigin.getObjVal? "finalSeed"), ("maxProgramNodes", toJson nodes),
    ("depthMask", toJson mask), ("form", toJson form.name), ("stepOrigin", stepOrigin)]
  return (plan, origin)

def boundaryResults (plan : CheckedPlan) (fuel : Nat) : Except String (List Word) :=
  boundaryInputs.mapM fun input =>
    match (plan.instantiate input).toCore.runStateful fuel with
    | .done (.word value) _ => .ok value
    | .done _ _ => .error "recursion boundary observation did not return a Word"
    | .outOfFuel _ => .error "boundary observation exhausted Core fuel"
    | .fault _ _ => .error "recursion boundary observation produced a Core fault"

/-- A depth-zero input returns itself, so a generated recursion must change
some boundary input. -/
def inputSensitive (plan : CheckedPlan) (fuel : Nat) : Except String Unit := do
  Aggregate.inputSensitive plan.step fuel
  let results ← boundaryResults plan fuel
  if results == boundaryInputs then throw Acceptance.identityReason

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
        let (plan, origin) ← generatedPlan seed nodes revision
        let emitted ← (emit plan).mapError reprStr
        inputSensitive plan fuel
        return (plan, origin, emitted)
      match result with
      | .error error =>
          let resource := error == "boundary observation exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "recursion-profile"),
            ("reason", toJson error),
            ("code", toJson (if resource then "boundary-out-of-fuel"
              else if error == Acceptance.identityReason then "boundary-identity" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok (plan, origin, emitted) =>
          for (input, inputIndex) in (inputSelection.inputs boundaryInputs seed).zipIdx do
            if cases.size < count then
              let origin := (origin.setObjVal! "inputIndex" (toJson inputIndex)).setObjVal!
                "validationFuel" (toJson fuel)
              cases := cases.push
                (makeCase plan input emitted (inputSelection.record origin) fuel revision
                  (revision.caseMask seed featureSupport))
  return Json.mkObj [("schema", toJson corpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

def replayCase (json : Json) (fuel : Nat) : Except String Json := do
  let admitted ← caseProgram json
  let provenance ← json.getObjVal? "provenance"
  let revision := savedPureRevision provenance
  for (name, expected) in [
      ("generatorVersion", revision.version), ("profileVersion", profileVersion),
      ("functionVersion", Recursion.version), ("templateVersion", templateVersion),
      ("stepProfileVersion", Aggregate.profileVersion), ("stepFunctionVersion", Aggregates.version),
      ("stepTemplateVersion", Aggregate.templateVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let mask ← savedMask provenance revision featureSupport
  let emitted ← (emit admitted.plan).mapError reprStr
  unless (← json.getObjValAs? String "source") = emitted.source do
    throw "saved source differs from emission of the canonical recursion plan"
  unless (← json.getObjVal? "contract") == contractJson emitted admitted.input do
    throw "saved contract metadata differs from the recursion wrapper"
  unless (← provenance.getObjVal? "features") == toJson admitted.plan.step.features do
    throw "saved features differ from the checked step DAG"
  let kind ← origin.getObjValAs? String "kind"
  unless kind = "recursion-generated" || kind = "imported" || kind = "reduced" do
    throw "unsupported recursion case origin"
  if kind = "recursion-generated" then
    let seedText ← origin.getObjValAs? String "seed"
    let some seed := seedText.toNat? | throw "invalid saved seed"
    unless seed < 2 ^ 64 && toString seed = seedText do throw "noncanonical saved seed"
    unless mask == revision.caseMask (Seed.ofNat seed) featureSupport do
      throw "saved swarm mask differs from its generation seed"
    let nodes ← origin.getObjValAs? Nat "maxProgramNodes"
    let (plan, expectedOrigin) ← generatedPlan (Seed.ofNat seed) nodes revision
    for name in ["kind", "seed", "finalSeed", "maxProgramNodes", "depthMask", "form", "stepOrigin"] do
      unless (← origin.getObjVal? name) == (← expectedOrigin.getObjVal? name) do
        throw ("saved " ++ name ++ " differs from generated recursion provenance")
    unless planJson plan == planJson admitted.plan do
      throw "saved recursion plan differs from its generation seed"
    let inputIndex ← origin.getObjValAs? Nat "inputIndex"
    let inputSelection ← InputSelection.ofOrigin origin
    unless (inputSelection.inputs boundaryInputs (Seed.ofNat seed))[inputIndex]? = some admitted.input do
      throw "saved input differs from its recursion boundary index"
    let validationFuel ← origin.getObjValAs? Nat "validationFuel"
    unless validationFuel ≤ 10000000 do throw "saved validation fuel exceeds limit"
    inputSensitive plan validationFuel
  return makeCase admitted.plan admitted.input emitted origin fuel revision mask

structure Reduction (source : CheckedInput) where private mk ::
  candidate : CheckedInput
  sameHelperCount : candidate.plan.step.helpers.length = source.plan.step.helpers.length
  sameBindings : Aggregate.bindingInventory candidate.plan.step = Aggregate.bindingInventory source.plan.step
  boundedMask : candidate.plan.mask ≤ source.plan.mask
  strict : (complexity candidate.program.body).StrictlySmaller (complexity source.program.body)

private def sealReduction (source : CheckedInput) (step : Aggregates.CheckedDAG)
    (mask : Nat) (form : Form) (input : Word) : Option (Reduction source) := do
  let plan ← CheckedPlan.ofParts? step mask form
  let candidate : CheckedInput := ⟨plan, input⟩
  if count : candidate.plan.step.helpers.length = source.plan.step.helpers.length then
    if bindings : Aggregate.bindingInventory candidate.plan.step = Aggregate.bindingInventory source.plan.step then
      if bounded : candidate.plan.mask ≤ source.plan.mask then
        if strict : (complexity candidate.program.body).StrictlySmaller (complexity source.program.body) then
          some ⟨candidate, count, bindings, bounded, strict⟩
        else none
      else none
    else none
  else none

/-- Only the checked step's binders must remain unchanged. Lowering the depth
mask removes complete canonical guards and the tail form replaces larger
frames; neither removes an arbitrary Core scope. -/
def reductions (source : CheckedInput) : List (Reduction source) := Id.run do
  let plan := source.plan
  let mut raw : List (Aggregates.CheckedDAG × Nat × Form × Word) := []
  for reduced in Aggregate.reductions ⟨plan.step, source.input⟩ do
    raw := raw ++ [(reduced.candidate.function, plan.mask, plan.form, reduced.candidate.input)]
  for mask in [0, 1, 3] do
    if mask < plan.mask then raw := raw ++ [(plan.step, mask, plan.form, source.input)]
  if plan.form != .tail then raw := raw ++ [(plan.step, plan.mask, .tail, source.input)]
  for input in boundaryInputs do
    raw := raw ++ [(plan.step, plan.mask, plan.form, input)]
  let mut seen : List String := []
  let mut result := []
  for (step, mask, form, input) in raw do
    if let some reduced := sealReduction source step mask form input then
      let key := (Wire.encodeProgram reduced.candidate.program).compress
      if !seen.contains key then
        seen := key :: seen
        result := result ++ [reduced]
  return result

def shrinkCases (json : Json) (limit fuel : Nat) : Except String Json := do
  let _ ← replayCase json fuel
  let source ← caseProgram json
  let provenance ← json.getObjVal? "provenance"
  let revision := savedPureRevision provenance
  let mask ← savedMask provenance revision featureSupport
  let mut cases : Array Json := #[]
  for reduced in (reductions source).take limit do
    let origin := Json.mkObj [
      ("kind", toJson "reduced"), ("parentProgram", Wire.encodeProgram source.program),
      ("parentPlan", planJson source.plan), ("parentInput", toJson (toString source.input.val))]
    cases := cases.push
      (← emitCase reduced.candidate.plan reduced.candidate.input origin fuel revision mask)
  return Json.mkObj [("schema", toJson corpusSchema), ("cases", .arr cases)]

end Solcore.Synthesis.Source.Recursion
