import Solcore.Synthesis.Source.AggregateCases
import Solcore.Synthesis.Source.NestedLoopEmitter

/-! A nested-loop case retains its checked step DAG, both masks, the inner
bound form and the independently executable canonical Core reference. Every
origin reconstructs the full reference before replay; source execution runs
two real while loops instead of the ordinal guards. A case also records the
inner trip count of every outer iteration it runs, specified by the plan, the
input and the step's original Core results, not measured. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.NestedLoop
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.Synthesis.Core.NestedLoop (CheckedPlan Bound)

def caseSchema : String := "solcore-lean.semantic-nested-loop-case.v1"
def planSchema : String := "solcore-lean.nested-loop-plan.v1"
def profileVersion : String := "runtime-nested-loops-v1/bounded-while-seed-v1"
def templateVersion : String := "bounded-nested-word-loops-v1"

/-- Zero to three outer iterations under the outer mask three. -/
def boundaryInputs : List Word :=
  [Word.zero, Word.ofNatModulo 1, Word.ofNatModulo 2, Word.ofNatModulo 3,
    Word.maximum, Word.ofNatModulo (2 ^ 255)]

structure CheckedInput where
  plan : CheckedPlan
  input : Word

def CheckedInput.program (value : CheckedInput) : Wire.Program :=
  value.plan.instantiate value.input

def planJson (plan : CheckedPlan) : Json := Json.mkObj [
  ("schema", toJson planSchema), ("stepProgram", Wire.encodeProgram plan.step.program),
  ("outerMask", toJson plan.outer), ("innerMask", toJson plan.inner),
  ("innerBound", toJson plan.bound.name)]

def checkedPlan (json : Json) : Except String CheckedPlan := do
  unless (← json.getObjValAs? String "schema") = planSchema do
    throw "unsupported nested loop plan schema"
  let step ← Aggregate.checkedFunction (← json.getObjVal? "stepProgram")
  let outer ← json.getObjValAs? Nat "outerMask"
  let inner ← json.getObjValAs? Nat "innerMask"
  let some bound := Bound.ofString? (← json.getObjValAs? String "innerBound") |
    throw "unsupported nested loop inner bound"
  let some plan := CheckedPlan.ofParts? step outer inner bound |
    throw "nested loop plan has an invalid mask or failed the full Core checker"
  unless json == planJson plan do
    throw "saved nested loop plan differs from its canonical checked representation"
  unless Wire.programNodes (plan.instantiate Word.zero) ≤ 512 do
    throw "canonical applied nested loop exceeds the 512-node case limit"
  return plan

/-- The step's original Core result for one call. -/
def stepResult (plan : CheckedPlan) (value : Word) (fuel : Nat) : Option Word :=
  match (plan.step.instantiate value).toCore.runStateful fuel with
  | .done (.word result) _ => some result
  | _ => none

/-- The inner trip count of each outer iteration a call runs and the final
accumulator, evaluating the step's original Core call by call. `none` when a
step call does not return a Word within the fuel. -/
def simulate (plan : CheckedPlan) (input : Word) (fuel : Nat) : Option (List Nat × Word) := Id.run do
  let mut accumulator := input
  let mut trips : List Nat := []
  for ordinal in List.range (plan.outerTrips input) do
    let count := plan.innerTrips input accumulator ordinal
    for _ in List.range count do
      match stepResult plan accumulator fuel with
      | some value => accumulator := value
      | none => return none
    trips := trips ++ [count]
  return some (trips, accumulator)

def iterationsJson (plan : CheckedPlan) (input : Word) (fuel : Nat) : Json :=
  match simulate plan input fuel with
  | some (trips, _) => toJson trips
  | none => .null

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
  ("schema", toJson caseSchema), ("nestedLoopPlan", planJson plan),
  ("program", Wire.encodeProgram (plan.instantiate input)),
  ("input", toJson (toString input.val)), ("source", toJson emitted.source),
  ("provenance", Json.mkObj <| swarmField revision mask ++ [
    ("origin", origin), ("profileVersion", toJson profileVersion),
    ("functionVersion", toJson NestedLoop.version), ("templateVersion", toJson templateVersion),
    ("stepProfileVersion", toJson Aggregate.profileVersion),
    ("stepFunctionVersion", toJson Aggregates.version),
    ("stepTemplateVersion", toJson Aggregate.templateVersion),
    ("generatorVersion", toJson revision.version),
    ("emitterVersion", toJson emitterVersion), ("wrapperVersion", toJson wrapperVersion),
    ("features", toJson plan.step.features), ("iterations", iterationsJson plan input fuel)]),
  ("contract", contractJson emitted input), ("executionFuel", toJson fuel),
  ("directCore", observe plan input fuel)]

def emitCase (plan : CheckedPlan) (input : Word) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1)
    (mask : FeatureMask := FeatureMask.all) : Except String Json := do
  unless Wire.programNodes (plan.instantiate input) ≤ 512 do
    throw "canonical applied nested loop exceeds the 512-node case limit"
  let emitted ← (emit plan).mapError reprStr
  return makeCase plan input emitted origin fuel revision mask

/-- Even imported and reduced cases must retain the exact canonical reference;
there is no origin for which a saved arbitrary Core program is trusted. -/
def caseProgram (json : Json) : Except String CheckedInput := do
  unless (← json.getObjValAs? String "schema") = caseSchema do
    throw "unsupported semantic nested loop case schema"
  let plan ← checkedPlan (← json.getObjVal? "nestedLoopPlan")
  let input ← Input.inputWord (← json.getObjValAs? String "input")
  let program ← (Wire.decodeProgramWithBudget
    {maxDepth := 512, maxNodes := 512, maxIntegerBytes := 4096}
    (← json.getObjVal? "program")).mapError (fun
      | .protocol error => error.toJson.compress
      | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)
  unless Wire.encodeProgram program == Wire.encodeProgram (plan.instantiate input) do
    throw "saved Core program differs from its canonical nested loop plan and runtime input"
  return ⟨plan, input⟩

/-- The twelve generation shapes: both masks from one and three, then the bound. -/
def shapes : List (Nat × Nat × Bound) :=
  Bound.all.flatMap fun bound => [(1, 1, bound), (1, 3, bound), (3, 1, bound), (3, 3, bound)]

/-- Separates the shape stream from other uses of a case seed. -/
private def shapeDomain : UInt64 := 0x6e65737465643031

/-- A SplitMix64 hash of the seed, so that consecutive seeds vary in shape
independently of the step's helper count and template. -/
def shapeFor (seed : Seed) : Nat × Nat × Bound :=
  shapes[(GeneratorV2.mix (seed.toUInt64 ^^^ shapeDomain)).toNat % shapes.length]?.getD (3, 3, .input)

/-- The actual wrapper syntax supplies the step budget. The complete applied
program is measured and checked again after the independent step generator. -/
def generatedPlan (seed : Seed) (nodes : Nat) (revision : GeneratorRevision := .v1) :
    Except String (CheckedPlan × Json) := do
  let (outer, inner, bound) := shapeFor seed
  let overhead := NestedLoop.appliedOverhead outer inner bound
  unless nodes ≤ 512 && overhead < nodes do
    throw "node budget is too small for the selected nested loop shape or exceeds 512"
  let (step, stepOrigin) ← Aggregate.generatedFunction seed (nodes - overhead) revision
  let some plan := CheckedPlan.ofParts? step outer inner bound |
    throw "generated nested loop plan failed the full Core checker"
  unless Wire.programNodes (plan.instantiate Word.zero) ≤ nodes do
    throw "canonical applied nested loop exceeds its requested node budget"
  let origin := Json.mkObj [
    ("kind", toJson "nested-loop-generated"), ("seed", toJson (toString seed.toNat)),
    ("finalSeed", ← stepOrigin.getObjVal? "finalSeed"), ("maxProgramNodes", toJson nodes),
    ("outerMask", toJson outer), ("innerMask", toJson inner), ("innerBound", toJson bound.name),
    ("stepOrigin", stepOrigin)]
  return (plan, origin)

def boundaryResults (plan : CheckedPlan) (fuel : Nat) : Except String (List Word) :=
  boundaryInputs.mapM fun input =>
    match (plan.instantiate input).toCore.runStateful fuel with
    | .done (.word value) _ => .ok value
    | .done _ _ => .error "nested loop boundary observation did not return a Word"
    | .outOfFuel _ => .error "boundary observation exhausted Core fuel"
    | .fault _ _ => .error "nested loop boundary observation produced a Core fault"

/-- A boundary input without a step call returns itself, so a generated nested
loop must change some boundary input. -/
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
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "nested-loop-profile"),
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
      ("functionVersion", NestedLoop.version), ("templateVersion", templateVersion),
      ("stepProfileVersion", Aggregate.profileVersion), ("stepFunctionVersion", Aggregates.version),
      ("stepTemplateVersion", Aggregate.templateVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let mask ← savedMask provenance revision featureSupport
  let emitted ← (emit admitted.plan).mapError reprStr
  unless (← json.getObjValAs? String "source") = emitted.source do
    throw "saved source differs from emission of the canonical nested loop plan"
  unless (← json.getObjVal? "contract") == contractJson emitted admitted.input do
    throw "saved contract metadata differs from the nested loop wrapper"
  unless (← provenance.getObjVal? "features") == toJson admitted.plan.step.features do
    throw "saved features differ from the checked step DAG"
  let savedFuel ← json.getObjValAs? Nat "executionFuel"
  unless savedFuel ≤ 10000000 do throw "saved execution fuel exceeds limit"
  unless (← provenance.getObjVal? "iterations") == iterationsJson admitted.plan admitted.input savedFuel do
    throw "saved iterations differ from the plan, input and step"
  let kind ← origin.getObjValAs? String "kind"
  unless kind = "nested-loop-generated" || kind = "imported" || kind = "reduced" do
    throw "unsupported nested loop case origin"
  if kind = "nested-loop-generated" then
    let seedText ← origin.getObjValAs? String "seed"
    let some seed := seedText.toNat? | throw "invalid saved seed"
    unless seed < 2 ^ 64 && toString seed = seedText do throw "noncanonical saved seed"
    unless mask == revision.caseMask (Seed.ofNat seed) featureSupport do
      throw "saved swarm mask differs from its generation seed"
    let nodes ← origin.getObjValAs? Nat "maxProgramNodes"
    let (plan, expectedOrigin) ← generatedPlan (Seed.ofNat seed) nodes revision
    for name in ["kind", "seed", "finalSeed", "maxProgramNodes", "outerMask", "innerMask", "innerBound",
        "stepOrigin"] do
      unless (← origin.getObjVal? name) == (← expectedOrigin.getObjVal? name) do
        throw ("saved " ++ name ++ " differs from generated nested loop provenance")
    unless planJson plan == planJson admitted.plan do
      throw "saved nested loop plan differs from its generation seed"
    let inputIndex ← origin.getObjValAs? Nat "inputIndex"
    let inputSelection ← InputSelection.ofOrigin origin
    unless (inputSelection.inputs boundaryInputs (Seed.ofNat seed))[inputIndex]? = some admitted.input do
      throw "saved input differs from its nested loop boundary index"
    let validationFuel ← origin.getObjValAs? Nat "validationFuel"
    unless validationFuel ≤ 10000000 do throw "saved validation fuel exceeds limit"
    inputSensitive plan validationFuel
  return makeCase admitted.plan admitted.input emitted origin fuel revision mask

structure Reduction (source : CheckedInput) where private mk ::
  candidate : CheckedInput
  sameHelperCount : candidate.plan.step.helpers.length = source.plan.step.helpers.length
  sameBindings : Aggregate.bindingInventory candidate.plan.step = Aggregate.bindingInventory source.plan.step
  boundedOuter : candidate.plan.outer ≤ source.plan.outer
  boundedInner : candidate.plan.inner ≤ source.plan.inner
  strict : (complexity candidate.program.body).StrictlySmaller (complexity source.program.body)

private def sealReduction (source : CheckedInput) (step : Aggregates.CheckedDAG)
    (outer inner : Nat) (bound : Bound) (input : Word) : Option (Reduction source) := do
  let plan ← CheckedPlan.ofParts? step outer inner bound
  let candidate : CheckedInput := ⟨plan, input⟩
  if count : candidate.plan.step.helpers.length = source.plan.step.helpers.length then
    if bindings : Aggregate.bindingInventory candidate.plan.step = Aggregate.bindingInventory source.plan.step then
      if boundedOuter : candidate.plan.outer ≤ source.plan.outer then
        if boundedInner : candidate.plan.inner ≤ source.plan.inner then
          if strict : (complexity candidate.program.body).StrictlySmaller (complexity source.program.body) then
            some ⟨candidate, count, bindings, boundedOuter, boundedInner, strict⟩
          else none
        else none
      else none
    else none
  else none

/-- Only the checked step's binders must remain unchanged. Lowering a mask
removes complete canonical guards and the input bound replaces a larger inner
bound expression; neither removes an arbitrary Core scope. -/
def reductions (source : CheckedInput) : List (Reduction source) := Id.run do
  let plan := source.plan
  let mut raw : List (Aggregates.CheckedDAG × Nat × Nat × Bound × Word) := []
  for reduced in Aggregate.reductions ⟨plan.step, source.input⟩ do
    raw := raw ++ [(reduced.candidate.function, plan.outer, plan.inner, plan.bound, reduced.candidate.input)]
  for outer in [0, 1] do
    if outer < plan.outer then raw := raw ++ [(plan.step, outer, plan.inner, plan.bound, source.input)]
  for inner in [0, 1] do
    if inner < plan.inner then raw := raw ++ [(plan.step, plan.outer, inner, plan.bound, source.input)]
  if plan.bound != .input then raw := raw ++ [(plan.step, plan.outer, plan.inner, .input, source.input)]
  for input in boundaryInputs do
    raw := raw ++ [(plan.step, plan.outer, plan.inner, plan.bound, input)]
  let mut seen : List String := []
  let mut result := []
  for (step, outer, inner, bound, input) in raw do
    if let some reduced := sealReduction source step outer inner bound input then
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

end Solcore.Synthesis.Source.NestedLoop
