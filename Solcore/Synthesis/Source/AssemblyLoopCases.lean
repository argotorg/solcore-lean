import Solcore.Synthesis.Source.CallGraphLoopCases
import Solcore.Synthesis.Source.AssemblyLoopEmitter

/-! An inline Yul loop case retains the independently checked plan of the
call-graph loop profile and the form that renders it. Generation repeats that
profile's steps, so its finite Core reference is unchanged, and draws the form
from a hash of the seed. Saved observations never supply the oracle. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.AssemblyLoop
open Lean Solcore.Core Solcore.Synthesis.Core

def caseSchema : String := "solcore-lean.semantic-assembly-loop-case.v1"
def planSchema : String := "solcore-lean.assembly-loop-plan.v1"
def profileVersion : String := "runtime-assembly-loops-v1/form-seed-v1"

/-- A checked call-graph loop plan and the form that renders it. -/
structure CheckedPlan where
  loop : Solcore.Synthesis.Core.CallGraphLoop.CheckedPlan
  form : Form

structure CheckedInput where
  plan : CheckedPlan
  input : Word

def CheckedInput.program (value : CheckedInput) : Wire.Program :=
  value.plan.loop.instantiate value.input

def planJson (plan : CheckedPlan) : Json := Json.mkObj [
  ("schema", toJson planSchema), ("stepProgram", Wire.encodeProgram plan.loop.graph.program),
  ("mask", toJson plan.loop.mask), ("form", toJson plan.form.name)]

/-- The call-graph loop profile checks the step and mask, then the form and the
whole saved plan must be canonical. -/
def checkedPlan (json : Json) : Except String CheckedPlan := do
  unless (← json.getObjValAs? String "schema") = planSchema do
    throw "unsupported assembly loop plan schema"
  let loop ← CallGraphLoop.checkedPlan (Json.mkObj [("schema", toJson CallGraphLoop.planSchema),
    ("stepProgram", ← json.getObjVal? "stepProgram"), ("mask", ← json.getObjVal? "mask")])
  let some form := Form.ofString? (← json.getObjValAs? String "form") |
    throw "assembly loop form must be for, break, continue, leave or pair"
  let plan : CheckedPlan := ⟨loop, form⟩
  unless json == planJson plan do
    throw "saved assembly loop plan differs from its canonical checked representation"
  return plan

def makeCase (plan : CheckedPlan) (input : Word) (emitted : EmittedProgram)
    (origin : Json) (fuel : Nat) : Json := Json.mkObj [
  ("schema", toJson caseSchema), ("assemblyLoopPlan", planJson plan),
  ("program", Wire.encodeProgram (plan.loop.instantiate input)),
  ("input", toJson (toString input.val)), ("source", toJson emitted.source),
  ("provenance", Json.mkObj [
    ("origin", origin), ("profileVersion", toJson profileVersion),
    ("loopProfileVersion", toJson CallGraphLoop.profileVersion),
    ("functionVersion", toJson CallGraphLoop.functionVersion), ("loopVersion", toJson BoundedLoop.version),
    ("stepFunctionVersion", toJson wordFunctionDAGVersion),
    ("aggregateVersion", toJson Aggregates.version),
    ("boundaryVersion", toJson CallGraphLoop.boundaryVersion),
    ("stepBoundaryVersion", toJson CallGraphLoop.stepBoundaryVersion),
    ("callShapeVersion", toJson CallGraphLoop.callShapeVersion),
    ("generatorVersion", toJson CallGraphLoop.generatorVersion),
    ("emitterVersion", toJson emitterVersion), ("wrapperVersion", toJson wrapperVersion),
    ("features", toJson plan.loop.features),
    ("helperCount", toJson plan.loop.graph.helpers.length),
    ("callShapes", toJson (CallGraphLoop.callShapes plan.loop))]),
  ("contract", CallGraphLoop.contractJson emitted input), ("executionFuel", toJson fuel),
  ("directCore", CallGraphLoop.observe plan.loop input fuel)]

def emitCase (plan : CheckedPlan) (input : Word) (origin : Json) (fuel : Nat) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds profile limit"
  unless Wire.programNodes (plan.loop.instantiate input) ≤ 512 do
    throw "canonical applied assembly loop exceeds the 512-node case limit"
  let emitted ← (emit plan.form plan.loop).mapError reprStr
  return makeCase plan input emitted origin fuel

/-- Even imported and reduced cases retain the exact canonical reference; no
origin makes a saved arbitrary Core program trusted. -/
def caseProgram (json : Json) : Except String CheckedInput := do
  unless (← json.getObjValAs? String "schema") = caseSchema do
    throw "unsupported semantic assembly loop case schema"
  let plan ← checkedPlan (← json.getObjVal? "assemblyLoopPlan")
  let input ← CallGraphLoop.inputWord (← json.getObjValAs? String "input")
  let program ← (Wire.decodeProgramWithBudget
    {maxDepth := 512, maxNodes := 512, maxIntegerBytes := 4096}
    (← json.getObjVal? "program")).mapError (fun
      | .protocol error => error.toJson.compress
      | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)
  unless Wire.encodeProgram program == Wire.encodeProgram (plan.loop.instantiate input) do
    throw "saved Core program differs from its canonical assembly loop plan and runtime input"
  let admitted : CheckedInput := ⟨plan, input⟩
  unless Wire.encodeProgram admitted.program == (← json.getObjVal? "program") do
    throw "saved Core assembly loop application is not canonical"
  return admitted

/-- Separates the form stream from other uses of a case seed. -/
private def formDomain : UInt64 := 0x61736d6c6f6f7001

/-- A SplitMix64 hash of the seed, so that consecutive seeds vary in form
independently of the call-graph loop plan. -/
def formFor (seed : Seed) : Form :=
  Form.all[(GeneratorV2.mix (seed.toUInt64 ^^^ formDomain)).toNat % Form.all.length]?.getD .bounded

/-- The call-graph loop profile's plan and generated origin for the seed, with
the seed's form. A registered test requires both profiles to agree. -/
def generatedPlan (seed : Seed) (nodes : Nat) : Except String (CheckedPlan × Json) := do
  let (loop, origin) ← CallGraphLoop.generatedPlan seed nodes
  let form := formFor seed
  return (⟨loop, form⟩,
    (origin.setObjVal! "kind" (toJson "assembly-loop-generated")).setObjVal! "form" (toJson form.name))

/-- Attempts count complete plan candidates. Accepted plans yield up to six
cases in fixed input order. The exclusions are those of the call-graph loop
profile, in its order; fuel exhaustion is an inconclusive exclusion. -/
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
        let (plan, origin) ← generatedPlan seed nodes
        let emitted ← (emit plan.form plan.loop).mapError reprStr
        CallGraphLoop.inputSensitive plan.loop fuel
        return (plan, origin, emitted)
      match result with
      | .error error =>
          let resource := error == "boundary observation exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "assembly-loop-profile"),
            ("reason", toJson error),
            ("code", toJson (if resource then "boundary-out-of-fuel" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok (plan, origin, emitted) =>
          for (input, inputIndex) in (inputSelection.inputs CallGraphLoop.boundaryInputs seed).zipIdx do
            if cases.size < count then
              let origin := (origin.setObjVal! "inputIndex" (toJson inputIndex)).setObjVal!
                "validationFuel" (toJson fuel)
              cases := cases.push
                (makeCase plan input emitted (inputSelection.record origin) fuel)
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
      ("generatorVersion", CallGraphLoop.generatorVersion), ("profileVersion", profileVersion),
      ("loopProfileVersion", CallGraphLoop.profileVersion),
      ("functionVersion", CallGraphLoop.functionVersion), ("loopVersion", BoundedLoop.version),
      ("stepFunctionVersion", wordFunctionDAGVersion), ("aggregateVersion", Aggregates.version),
      ("boundaryVersion", CallGraphLoop.boundaryVersion),
      ("stepBoundaryVersion", CallGraphLoop.stepBoundaryVersion),
      ("callShapeVersion", CallGraphLoop.callShapeVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let emitted ← (emit admitted.plan.form admitted.plan.loop).mapError reprStr
  unless (← json.getObjValAs? String "source") = emitted.source do
    throw "saved source differs from emission of the assembly loop plan"
  unless (← json.getObjVal? "contract") == CallGraphLoop.contractJson emitted admitted.input do
    throw "saved contract metadata differs from the assembly loop wrapper"
  unless (← provenance.getObjVal? "features") == toJson admitted.plan.loop.features do
    throw "saved features differ from the original Core call graph"
  unless (← provenance.getObjValAs? Nat "helperCount") = admitted.plan.loop.graph.helpers.length do
    throw "saved helper count differs from the original Core call graph"
  unless (← provenance.getObjVal? "callShapes") == toJson (CallGraphLoop.callShapes admitted.plan.loop) do
    throw "saved call shapes differ from the original Core call graph"
  let kind ← origin.getObjValAs? String "kind"
  if kind = "assembly-loop-generated" then
    let seedText ← origin.getObjValAs? String "seed"
    let some seed := seedText.toNat? | throw "invalid saved seed"
    unless seed < 2 ^ 64 && toString seed = seedText do throw "noncanonical saved seed"
    let nodes ← origin.getObjValAs? Nat "maxProgramNodes"
    let (plan, expectedOrigin) ← generatedPlan (Seed.ofNat seed) nodes
    unless admitted.plan.form == plan.form do
      throw "saved assembly loop form differs from its generation seed"
    unless planJson plan == planJson admitted.plan do
      throw "saved assembly loop plan differs from its generation seed"
    let inputIndex ← origin.getObjValAs? Nat "inputIndex"
    let inputSelection ← InputSelection.ofOrigin origin
    unless (inputSelection.inputs CallGraphLoop.boundaryInputs (Seed.ofNat seed))[inputIndex]? =
        some admitted.input do
      throw "saved input differs from its loop boundary index"
    let validationFuel ← origin.getObjValAs? Nat "validationFuel"
    unless validationFuel ≤ 10000000 do throw "saved validation fuel exceeds limit"
    CallGraphLoop.inputSensitive plan.loop validationFuel
    let canonicalOrigin := (expectedOrigin.setObjVal! "inputIndex" (toJson inputIndex)).setObjVal!
      "validationFuel" (toJson validationFuel)
    unless origin == inputSelection.record canonicalOrigin do
      throw "generated assembly loop provenance is not canonical"
  else if kind = "imported" then
    unless origin == Json.mkObj [("kind", toJson "imported")] do
      throw "imported assembly loop provenance is not canonical"
  else if kind = "reduced" then
    let parentPlan ← origin.getObjVal? "parentPlan"
    let parentText ← origin.getObjValAs? String "parentInput"
    let parent : CheckedInput := ⟨← checkedPlan parentPlan, ← CallGraphLoop.inputWord parentText⟩
    unless parent.plan.form == admitted.plan.form do
      throw "saved assembly loop reduction changes its parent's form"
    unless admitted.plan.loop.graph.helpers.length = parent.plan.loop.graph.helpers.length do
      throw "saved loop reduction changes helper count"
    unless admitted.plan.loop.mask ≤ parent.plan.loop.mask do
      throw "saved loop reduction increases its mask"
    unless (complexity admitted.program.body).isStrictlySmaller (complexity parent.program.body) do
      throw "saved loop reduction is not strictly smaller than its checked parent"
    unless origin == Json.mkObj [("kind", toJson "reduced"), ("parentPlan", parentPlan),
        ("parentInput", toJson parentText)] do
      throw "reduced assembly loop provenance is not canonical"
  else throw "unsupported assembly loop case origin"
  let fresh := makeCase admitted.plan admitted.input emitted origin fuel
  unless (← fresh.getObjVal? "provenance") == provenance do
    throw "assembly loop provenance contains unexpected fields"
  -- Ignore the saved observation, but require the complete canonical envelope.
  let _ ← json.getObjVal? "directCore"
  let savedEnvelope := json.setObjVal! "directCore" .null
  let freshEnvelope := (fresh.setObjVal! "directCore" .null).setObjVal!
    "executionFuel" (toJson savedFuel)
  unless savedEnvelope == freshEnvelope do throw "saved assembly loop case envelope is not canonical"
  return fresh

/-- A call-graph loop reduction, rendered in the parent's form. -/
structure Reduction (source : CheckedInput) where private mk ::
  candidate : CheckedInput
  sameForm : candidate.plan.form = source.plan.form
  sameHelperCount : candidate.plan.loop.graph.helpers.length = source.plan.loop.graph.helpers.length
  boundedMask : candidate.plan.loop.mask ≤ source.plan.loop.mask
  strict : (complexity candidate.program.body).StrictlySmaller (complexity source.program.body)

/-- The call-graph loop reductions: typed graph reductions that keep every
helper binding, smaller masks and boundary inputs, each resealed and strictly
smaller. Keeping the form changes no Core node. -/
def reductions (source : CheckedInput) : List (Reduction source) :=
  (CallGraphLoop.reductions ⟨source.plan.loop, source.input⟩).map fun reduced =>
    ⟨⟨⟨reduced.candidate.plan, source.plan.form⟩, reduced.candidate.input⟩, rfl,
      reduced.sameHelperCount, reduced.boundedMask, reduced.strict⟩

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

end Solcore.Synthesis.Source.AssemblyLoop
