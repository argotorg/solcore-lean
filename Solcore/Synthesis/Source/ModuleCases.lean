import Solcore.Synthesis.Source.AggregateCases
import Solcore.Synthesis.Source.ModuleEmitter

/-! Module cases retain both original typed ASTs and the complete fixed source
bundle. All origins reconstruct the original Core reference and every source
file; reduction changes typed ASTs and inputs, never arbitrary bundle contents. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.Modules
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.Synthesis.Core.Modules (CheckedPlan)

def caseSchema : String := "solcore-lean.semantic-module-case.v1"
def planSchema : String := "solcore-lean.module-plan.v1"
def profileVersion : String := "runtime-modules-v2/bundle-seed-v1"
def templateVersion : String := "original-four-module-mix-v1"

def boundaryInputs : List Word :=
  [Word.zero, Word.ofNatModulo 1, Word.maximum, Word.ofNatModulo (2 ^ 255)]

structure CheckedInput where
  plan : CheckedPlan
  input : Word

def CheckedInput.program (value : CheckedInput) : Wire.Program :=
  value.plan.instantiate value.input

def planJson (plan : CheckedPlan) : Json := Json.mkObj [
  ("schema", toJson planSchema), ("constantProgram", Wire.encodeProgram plan.constant.program),
  ("stepProgram", Wire.encodeProgram plan.step.program)]

def checkedPlan (json : Json) : Except String CheckedPlan := do
  unless (← json.getObjValAs? String "schema") = planSchema do
    throw "unsupported module plan schema"
  let constant ← Solcore.Synthesis.Source.checkedProgram (← json.getObjVal? "constantProgram")
  let step ← Aggregate.checkedFunction (← json.getObjVal? "stepProgram")
  let some plan := CheckedPlan.ofParts? constant step |
    throw "module plan failed the full Core checker"
  unless json == planJson plan do throw "saved module plan differs from its canonical checked representation"
  unless Wire.programNodes (plan.instantiate Word.zero) ≤ 512 do
    throw "canonical applied module exceeds the 512-node case limit"
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

def contractJson (emitted : EmittedBundle) (input : Word) : Json := Json.mkObj [
  ("name", toJson emitted.contractName), ("method", toJson emitted.methodName),
  ("signature", toJson emitted.methodSignature),
  ("deployPath", toJson emitted.deployPath), ("runtimePath", toJson emitted.runtimePath),
  ("calldata", toJson (Input.calldata input)), ("constructorCalldata", toJson "0x")]

def makeCase (plan : CheckedPlan) (input : Word) (emitted : EmittedBundle)
    (origin : Json) (fuel : Nat) (revision : GeneratorRevision := .v1)
    (mask : FeatureMask := FeatureMask.all) : Json := Json.mkObj [
  ("schema", toJson caseSchema), ("modulePlan", planJson plan),
  ("program", Wire.encodeProgram (plan.instantiate input)),
  ("input", toJson (toString input.val)), ("source", toJson emitted.source),
  ("sourceBundle", bundleJson emitted),
  ("provenance", Json.mkObj <| swarmField revision mask ++ [
    ("origin", origin), ("profileVersion", toJson profileVersion),
    ("functionVersion", toJson Solcore.Synthesis.Core.Modules.version), ("templateVersion", toJson templateVersion),
    ("stepProfileVersion", toJson Aggregate.profileVersion),
    ("stepFunctionVersion", toJson Aggregates.version),
    ("stepTemplateVersion", toJson Aggregate.templateVersion),
    ("generatorVersion", toJson revision.version),
    ("emitterVersion", toJson emitterVersion), ("wrapperVersion", toJson wrapperVersion),
    ("features", toJson plan.step.features),
    ("constantFeatures", toJson ((features plan.constant.program.body).map featureName))]),
  ("contract", contractJson emitted input), ("executionFuel", toJson fuel),
  ("directCore", observe plan input fuel)]

def emitCase (plan : CheckedPlan) (input : Word) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1)
    (mask : FeatureMask := FeatureMask.all) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
  unless Wire.programNodes (plan.instantiate input) ≤ 512 do
    throw "canonical applied module exceeds the 512-node case limit"
  let emitted ← (emit plan).mapError reprStr
  return makeCase plan input emitted origin fuel revision mask

/-- Even imported and reduced cases must retain the exact canonical reference;
there is no origin for which a saved arbitrary Core program is trusted. -/
def caseProgram (json : Json) : Except String CheckedInput := do
  unless (← json.getObjValAs? String "schema") = caseSchema do
    throw "unsupported semantic module case schema"
  let plan ← checkedPlan (← json.getObjVal? "modulePlan")
  let input ← Input.inputWord (← json.getObjValAs? String "input")
  let program ← (Wire.decodeProgramWithBudget
    {maxDepth := 512, maxNodes := 512, maxIntegerBytes := 4096}
    (← json.getObjVal? "program")).mapError (fun
      | .protocol error => error.toJson.compress
      | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)
  unless Wire.encodeProgram program == Wire.encodeProgram (plan.instantiate input) do
    throw "saved Core program differs from its canonical module plan and runtime input"
  return ⟨plan, input⟩

/-- The actual wrapper syntax supplies the step budget. The complete applied
program is measured and checked again after the independent step generator. -/
def generatedPlan (seed : Seed) (nodes : Nat) (revision : GeneratorRevision := .v1) :
    Except String (CheckedPlan × Json) := do
  let overhead := Solcore.Synthesis.Core.Modules.appliedOverhead
  unless nodes ≤ 512 && overhead < nodes do
    throw "node budget is too small for the module composition or exceeds 512"
  let available := nodes - overhead
  let constantBudget := min 8 (available / 8)
  let constantSeed := Seed.ofNat (seed.toNat + 104729)
  -- The constant shares the case mask, restricted under revision four to the
  -- scalar renderer's features; that is the recorded step mask restricted alike.
  let mask := revision.caseMask seed constantSupport
  let generated ←
    (generate {seed := constantSeed, maxProgramNodes := constantBudget, revision, mask}).mapError reprStr
  let constant := generated.checkedProgram
  let constantOrigin := Json.mkObj [
    ("kind", toJson "generated"), ("seed", toJson (toString generated.initialSeed.toNat)),
    ("finalSeed", toJson (toString generated.finalSeed.toNat)),
    ("maxProgramNodes", toJson generated.maxProgramNodes)]
  let (step, stepOrigin) ← Aggregate.generatedFunction seed (available - constantBudget) revision
  let some plan := CheckedPlan.ofParts? constant step |
    throw "generated module plan failed the full Core checker"
  unless Wire.programNodes (plan.instantiate Word.zero) ≤ nodes do
    throw "canonical applied module exceeds its requested node budget"
  let origin := Json.mkObj [
    ("kind", toJson "module-generated"), ("seed", toJson (toString seed.toNat)),
    ("finalSeed", ← stepOrigin.getObjVal? "finalSeed"), ("maxProgramNodes", toJson nodes),
    ("constantOrigin", constantOrigin), ("stepOrigin", stepOrigin)]
  return (plan, origin)

def boundaryResults (plan : CheckedPlan) (fuel : Nat) : Except String (List Word) :=
  boundaryInputs.mapM fun input =>
    match (plan.instantiate input).toCore.runStateful fuel with
    | .done (.word value) _ => .ok value
    | .done _ _ => .error "module boundary observation did not return a Word"
    | .outOfFuel _ => .error "boundary observation exhausted Core fuel"
    | .fault _ _ => .error "module boundary observation produced a Core fault"

/-- This is an AST admission condition, not a claim that every operation is
reached. The actual complete Core execution supplies all boundary observations. -/
def constantUsesOperation (constant : CheckedWordProgram) : Bool :=
  (features constant.program.body).any fun
    | .unary _ | .binary _ | .ternary _ => true
    | _ => false

/-- Generation retains a nonliteral constant computation and an input-sensitive
runtime step. Imported and reduced literals and constant steps remain valid. -/
def inputSensitive (plan : CheckedPlan) (fuel : Nat)
    (acceptance : Acceptance := .profile) : Except String Unit := do
  unless constantUsesOperation plan.constant do throw "constant AST contains no operation"
  Aggregate.inputSensitive plan.step fuel
  let results ← boundaryResults plan fuel
  unless results.any (fun result => some result != results.head?) do
    throw "all module boundary inputs returned the same result"
  acceptance.check boundaryInputs results

def generateCases (firstSeed : Seed) (nodes count attempts fuel : Nat)
    (revision : GeneratorRevision := .v1) (inputSelection : InputSelection := .boundary)
    (acceptance : Acceptance := .profile) : Json := Id.run do
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
        inputSensitive plan fuel acceptance
        return (plan, origin, emitted)
      match result with
      | .error error =>
          let resource := error == "boundary observation exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "module-profile"),
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
                (makeCase plan input emitted (acceptance.record (inputSelection.record origin)) fuel revision
                  (revision.caseMask seed featureSupport))
  return Json.mkObj [("schema", toJson corpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

structure Reduction (source : CheckedInput) where private mk ::
  candidate : CheckedInput
  sameHelperCount : candidate.plan.step.helpers.length = source.plan.step.helpers.length
  sameBindings : Aggregate.bindingInventory candidate.plan.step = Aggregate.bindingInventory source.plan.step
  strict : (complexity candidate.program.body).StrictlySmaller (complexity source.program.body)

private def sealReduction (source : CheckedInput) (constant : CheckedWordProgram)
    (step : Aggregates.CheckedDAG) (input : Word) : Option (Reduction source) := do
  let plan ← CheckedPlan.ofParts? constant step
  let candidate : CheckedInput := ⟨plan, input⟩
  if count : candidate.plan.step.helpers.length = source.plan.step.helpers.length then
    if bindings : Aggregate.bindingInventory candidate.plan.step = Aggregate.bindingInventory source.plan.step then
      if strict : (complexity candidate.program.body).StrictlySmaller (complexity source.program.body) then
        some ⟨candidate, count, bindings, strict⟩
      else none
    else none
  else none

/-- Constant reductions recheck closed G0 typing; step reductions retain all
typed binders, including sum case payloads.
The fixed module composition remains intact; every candidate is checked and strictly
smaller as a complete applied reference, including its runtime input. -/
def reductions (source : CheckedInput) : List (Reduction source) := Id.run do
  let mut raw : List (CheckedWordProgram × Aggregates.CheckedDAG × Word) := []
  for reduced in shrink source.plan.constant do
    raw := raw ++ [(reduced.checkedProgram, source.plan.step, source.input)]
  for reduced in Aggregate.reductions ⟨source.plan.step, source.input⟩ do
    raw := raw ++ [(source.plan.constant, reduced.candidate.function, reduced.candidate.input)]
  for input in boundaryInputs do raw := raw ++ [(source.plan.constant, source.plan.step, input)]
  let mut seen : List String := []
  let mut result := []
  for (constant, step, input) in raw do
    if let some reduced := sealReduction source constant step input then
      let key := (Wire.encodeProgram reduced.candidate.program).compress
      if !seen.contains key then
        seen := key :: seen
        result := result ++ [reduced]
  return result

def replayCase (json : Json) (fuel : Nat) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
  let admitted ← caseProgram json
  let provenance ← json.getObjVal? "provenance"
  let revision := savedPureRevision provenance
  for (name, expected) in [
      ("generatorVersion", revision.version), ("profileVersion", profileVersion),
      ("functionVersion", Solcore.Synthesis.Core.Modules.version), ("templateVersion", templateVersion),
      ("stepProfileVersion", Aggregate.profileVersion), ("stepFunctionVersion", Aggregates.version),
      ("stepTemplateVersion", Aggregate.templateVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let mask ← savedMask provenance revision featureSupport
  let emitted ← (emit admitted.plan).mapError reprStr
  unless (← json.getObjValAs? String "source") = emitted.source do
    throw "saved source differs from emission of the canonical module plan"
  unless (← json.getObjVal? "sourceBundle") == bundleJson emitted do
    throw "saved module bundle differs from all canonical source files"
  unless (← json.getObjVal? "contract") == contractJson emitted admitted.input do
    throw "saved contract metadata differs from the module wrapper"
  unless (← provenance.getObjVal? "features") == toJson admitted.plan.step.features do
    throw "saved features differ from the checked step DAG"
  unless (← provenance.getObjVal? "constantFeatures") ==
      toJson ((features admitted.plan.constant.program.body).map featureName) do
    throw "saved constant features differ from the original G0 expression"
  let kind ← origin.getObjValAs? String "kind"
  unless kind = "module-generated" || kind = "imported" || kind = "reduced" do
    throw "unsupported module case origin"
  if kind = "module-generated" then
    let seedText ← origin.getObjValAs? String "seed"
    unless seedText.length ≤ 20 do throw "saved seed exceeds limit"
    let some seed := seedText.toNat? | throw "invalid saved seed"
    unless seed < 2 ^ 64 && toString seed = seedText do throw "noncanonical saved seed"
    unless mask == revision.caseMask (Seed.ofNat seed) featureSupport do
      throw "saved swarm mask differs from its generation seed"
    let nodes ← origin.getObjValAs? Nat "maxProgramNodes"
    let (plan, expectedOrigin) ← generatedPlan (Seed.ofNat seed) nodes revision
    unless planJson plan == planJson admitted.plan do
      throw "saved module plan differs from its generation seed"
    let inputIndex ← origin.getObjValAs? Nat "inputIndex"
    let inputSelection ← InputSelection.ofOrigin origin
    unless (inputSelection.inputs boundaryInputs (Seed.ofNat seed))[inputIndex]? = some admitted.input do
      throw "saved input differs from its module boundary index"
    let validationFuel ← origin.getObjValAs? Nat "validationFuel"
    unless validationFuel ≤ 10000000 do throw "saved validation fuel exceeds limit"
    let canonicalOrigin := (expectedOrigin.setObjVal! "inputIndex" (toJson inputIndex)).setObjVal!
      "validationFuel" (toJson validationFuel)
    let acceptance ← Acceptance.ofOrigin origin
    unless origin == acceptance.record (inputSelection.record canonicalOrigin) do throw "saved origin differs from generated module provenance"
    inputSensitive plan validationFuel acceptance
  else if kind = "imported" then
    unless origin == Json.mkObj [("kind", toJson "imported")] do throw "noncanonical imported origin"
  else if kind = "reduced" then
    let parentPlan ← checkedPlan (← origin.getObjVal? "parentPlan")
    let parentInput ← Input.inputWord (← origin.getObjValAs? String "parentInput")
    let parent : CheckedInput := ⟨parentPlan, parentInput⟩
    unless (← origin.getObjVal? "parentProgram") == Wire.encodeProgram parent.program do
      throw "reduction parent program differs from its canonical plan and input"
    unless (sealReduction parent admitted.plan.constant admitted.plan.step admitted.input).isSome do
      throw "reduction changed step binders or did not strictly decrease"
    unless origin == Json.mkObj [("kind", toJson "reduced"), ("parentPlan", planJson parent.plan),
        ("parentProgram", Wire.encodeProgram parent.program), ("parentInput", toJson (toString parent.input.val))] do
      throw "noncanonical reduced origin"
  return makeCase admitted.plan admitted.input emitted origin fuel revision mask


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

end Solcore.Synthesis.Source.Modules
