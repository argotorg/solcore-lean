import Solcore.Synthesis.Source.PrimitiveCases
import Solcore.Synthesis.Source.AssemblyEmitter

/-! An inline Yul case retains the independently checked original Core
function of the primitive profile and the form that renders it. Generation
repeats the primitive profile's steps, so its Core reference is unchanged, and
draws the form from a hash of the seed. Saved observations never supply the
oracle. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.Assembly
open Lean Solcore.Core Solcore.Synthesis.Core
open AssemblyRenderer (Form)

def caseSchema : String := "solcore-lean.semantic-assembly-case.v1"
def planSchema : String := "solcore-lean.assembly-plan.v1"
def profileVersion : String := "runtime-assembly-v1/form-seed-v1"

/-- A checked primitive function and the form that renders it. -/
structure CheckedPlan where
  function : CheckedWordFunction
  form : Form

structure CheckedInput where
  plan : CheckedPlan
  input : Word

def CheckedInput.program (value : CheckedInput) : Wire.Program :=
  value.plan.function.instantiate value.input

def planJson (plan : CheckedPlan) : Json := Json.mkObj [
  ("schema", toJson planSchema), ("functionProgram", Wire.encodeProgram plan.function.program),
  ("form", toJson plan.form.name)]

def checkedPlan (json : Json) : Except String CheckedPlan := do
  unless (← json.getObjValAs? String "schema") = planSchema do
    throw "unsupported assembly plan schema"
  let function ← Primitive.checkedFunction (← json.getObjVal? "functionProgram")
  let some form := Form.ofString? (← json.getObjValAs? String "form") |
    throw "assembly form must be switch, if or operations"
  let plan : CheckedPlan := ⟨function, form⟩
  unless json == planJson plan do
    throw "saved assembly plan differs from its canonical checked representation"
  unless Wire.programNodes (function.instantiate Word.zero) ≤ 512 do
    throw "applied assembly function exceeds the 512-node case limit"
  return plan

def makeCase (plan : CheckedPlan) (input : Word) (emitted : EmittedProgram)
    (origin : Json) (fuel : Nat) (revision : GeneratorRevision := .v1)
    (mask : FeatureMask := FeatureMask.all) : Json := Json.mkObj [
  ("schema", toJson caseSchema), ("assemblyPlan", planJson plan),
  ("program", Wire.encodeProgram (plan.function.instantiate input)),
  ("input", toJson (toString input.val)), ("source", toJson emitted.source),
  ("provenance", Json.mkObj <| swarmField revision mask ++ [
    ("origin", origin), ("profileVersion", toJson profileVersion),
    ("functionProfileVersion", toJson Primitive.profileVersion),
    ("functionVersion", toJson wordFunctionVersion),
    ("abstractionVersion", toJson abstractionVersion),
    ("generatorVersion", toJson (Primitive.generatorVersionFor revision)),
    ("baseGeneratorVersion", toJson revision.version),
    ("boundaryVersion", toJson Primitive.boundaryVersion),
    ("emitterVersion", toJson emitterVersion), ("wrapperVersion", toJson wrapperVersion),
    ("features", toJson ((features plan.function.body).map featureName))]),
  ("contract", Primitive.contractJson emitted input), ("executionFuel", toJson fuel),
  ("directCore", Primitive.observe plan.function input fuel)]

def emitCase (plan : CheckedPlan) (input : Word) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1)
    (mask : FeatureMask := FeatureMask.all) : Except String Json := do
  unless Wire.programNodes (plan.function.instantiate input) ≤ 512 do
    throw "applied assembly function exceeds the 512-node case limit"
  let emitted ← (emit plan.form plan.function).mapError reprStr
  return makeCase plan input emitted origin fuel revision mask

/-- Every origin keeps the canonical applied function of its plan. -/
def caseProgram (json : Json) : Except String CheckedInput := do
  unless (← json.getObjValAs? String "schema") = caseSchema do
    throw "unsupported semantic assembly case schema"
  let plan ← checkedPlan (← json.getObjVal? "assemblyPlan")
  let input ← Primitive.inputWord (← json.getObjValAs? String "input")
  let program ← (Wire.decodeProgramWithBudget
    {maxDepth := 512, maxNodes := 512, maxIntegerBytes := 4096}
    (← json.getObjVal? "program")).mapError (fun
      | .protocol error => error.toJson.compress
      | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)
  unless Wire.encodeProgram program == Wire.encodeProgram (plan.function.instantiate input) do
    throw "saved Core program differs from its assembly plan's function and runtime input"
  return ⟨plan, input⟩

/-- Separates the form stream from other uses of a case seed. -/
private def formDomain : UInt64 := 0x617373656d626c01

/-- A SplitMix64 hash of the seed, so that consecutive seeds vary in form
independently of the primitive function. -/
def formFor (seed : Seed) : Form :=
  Form.all[(GeneratorV2.mix (seed.toUInt64 ^^^ formDomain)).toNat % Form.all.length]?.getD .switch

/-- The steps of the primitive profile's generation, repeated: the same G0
program under the same swarm mask, then the same literal abstraction. A
registered test requires both profiles' functions to agree. -/
def primitiveFunction (seed : Seed) (nodes : Nat) (revision : GeneratorRevision) :
    Except String (GeneratedProgram × Nat × CheckedWordFunction) := do
  unless Primitive.minimumProgramNodes ≤ nodes && nodes ≤ 512 do
    throw "complete primitive program budget must be between the profile minimum and 512"
  let mask := revision.caseMask seed featureSupport
  let generated ← (generate {seed, maxProgramNodes := nodes - Primitive.appliedOverhead, revision, mask}).mapError reprStr
  let count := literalCount generated.program.body
  unless count > 0 do throw "generated body has no Word literal to abstract"
  let literalIndex := seed.toNat % count
  let some function := CheckedWordFunction.fromProgram? generated.checkedProgram literalIndex |
    throw "literal abstraction did not produce a checked Word function"
  unless Wire.programNodes (function.instantiate Word.zero) ≤ nodes do
    throw "applied primitive function exceeds its complete program budget"
  return (generated, literalIndex, function)

/-- The generated origin before its input index, validation fuel, input
selection and acceptance filter. -/
private def generatedOrigin (seed : Seed) (nodes : Nat) (generated : GeneratedProgram)
    (literalIndex : Nat) (form : Form) : List (String × Json) := [
  ("kind", toJson "assembly-generated"), ("seed", toJson (toString seed.toNat)),
  ("finalSeed", toJson (toString generated.finalSeed.toNat)), ("maxProgramNodes", toJson nodes),
  ("baseProgramNodes", toJson generated.maxProgramNodes), ("literalIndex", toJson literalIndex),
  ("form", toJson form.name)]

/-- Attempt limits count functions; case limits count individual runtime inputs.
The exclusions are those of the primitive profile, in its order. -/
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
        let (generated, literalIndex, function) ← primitiveFunction seed nodes revision
        let plan : CheckedPlan := ⟨function, formFor seed⟩
        let emitted ← (emit plan.form plan.function).mapError
          (fun error => "unsupported source primitive: " ++ reprStr error)
        Primitive.inputSensitive function fuel acceptance
        return (generated, literalIndex, plan, emitted)
      match result with
      | .error error =>
          let resource := error == "boundary observation exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)),
            ("stage", toJson "assembly-profile"), ("reason", toJson error),
            ("code", toJson (if resource then "boundary-out-of-fuel"
              else if error.startsWith "unsupported source primitive:" then "unsupported-operation"
              else if error == Acceptance.identityReason then "boundary-identity" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok (generated, literalIndex, plan, emitted) =>
          for (input, inputIndex) in (inputSelection.inputs Primitive.boundaryInputs seed).zipIdx do
            if cases.size < count then
              let origin := Json.mkObj (generatedOrigin seed nodes generated literalIndex plan.form ++
                [("inputIndex", toJson inputIndex), ("validationFuel", toJson fuel)])
              cases := cases.push
                (makeCase plan input emitted (acceptance.record (inputSelection.record origin)) fuel revision
                  (revision.caseMask seed featureSupport))
  return Json.mkObj [("schema", toJson corpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

def replayCase (json : Json) (fuel : Nat) : Except String Json := do
  let admitted ← caseProgram json
  let provenance ← json.getObjVal? "provenance"
  let revision := savedPureRevision provenance "baseGeneratorVersion"
  for (name, expected) in [
      ("generatorVersion", Primitive.generatorVersionFor revision), ("profileVersion", profileVersion),
      ("functionProfileVersion", Primitive.profileVersion),
      ("baseGeneratorVersion", revision.version), ("boundaryVersion", Primitive.boundaryVersion),
      ("functionVersion", wordFunctionVersion), ("abstractionVersion", abstractionVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do
      throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let mask ← savedMask provenance revision featureSupport
  let emitted ← (emit admitted.plan.form admitted.plan.function).mapError reprStr
  unless (← json.getObjValAs? String "source") = emitted.source do
    throw "saved source differs from emission of the assembly plan"
  unless (← json.getObjVal? "contract") == Primitive.contractJson emitted admitted.input do
    throw "saved contract metadata differs from the assembly wrapper"
  unless (← provenance.getObjVal? "features") ==
      toJson ((features admitted.plan.function.body).map featureName) do
    throw "saved features differ from the original Core function"
  let kind ← origin.getObjValAs? String "kind"
  unless kind = "assembly-generated" || kind = "imported" || kind = "reduced" do
    throw "unsupported assembly case origin"
  if kind = "assembly-generated" then
    let seedText ← origin.getObjValAs? String "seed"
    let some seed := seedText.toNat? | throw "invalid saved seed"
    unless seed < 2 ^ 64 && toString seed = seedText do throw "noncanonical saved seed"
    unless mask == revision.caseMask (Seed.ofNat seed) featureSupport do
      throw "saved swarm mask differs from its generation seed"
    let nodes ← origin.getObjValAs? Nat "maxProgramNodes"
    unless Primitive.minimumProgramNodes ≤ nodes && nodes ≤ 512 do
      throw "saved generation budget exceeds profile limits"
    let (generated, literalIndex, function) ← primitiveFunction (Seed.ofNat seed) nodes revision
    unless admitted.plan.form == formFor (Seed.ofNat seed) do
      throw "saved assembly form differs from its generation seed"
    unless Wire.encodeProgram function.program == Wire.encodeProgram admitted.plan.function.program do
      throw "saved function differs from its generation seed"
    let inputIndex ← origin.getObjValAs? Nat "inputIndex"
    let inputSelection ← InputSelection.ofOrigin origin
    unless (inputSelection.inputs Primitive.boundaryInputs (Seed.ofNat seed))[inputIndex]? = some admitted.input do
      throw "saved input differs from its boundary index"
    let validationFuel ← origin.getObjValAs? Nat "validationFuel"
    unless validationFuel ≤ 10000000 do throw "saved validation fuel exceeds limit"
    let acceptance ← Acceptance.ofOrigin origin
    Primitive.inputSensitive function validationFuel acceptance
    unless origin == acceptance.record (inputSelection.record (Json.mkObj (
        generatedOrigin (Seed.ofNat seed) nodes generated literalIndex admitted.plan.form ++
        [("inputIndex", toJson inputIndex), ("validationFuel", toJson validationFuel)]))) do
      throw "generated assembly provenance is not canonical"
  else if kind = "imported" then
    unless origin == Json.mkObj [("kind", toJson "imported")] do
      throw "imported assembly provenance is not canonical"
  else
    let parentProgram ← origin.getObjVal? "parentProgram"
    let parentPlan ← origin.getObjVal? "parentPlan"
    let parentText ← origin.getObjValAs? String "parentInput"
    let parent ← caseProgram (Json.mkObj [("schema", toJson caseSchema), ("assemblyPlan", parentPlan),
      ("program", parentProgram), ("input", toJson parentText)])
    unless parent.plan.form == admitted.plan.form do
      throw "saved assembly reduction changes its parent's form"
    unless (complexity admitted.program.body).isStrictlySmaller (complexity parent.program.body) do
      throw "saved assembly reduction is not strictly smaller than its checked parent"
    unless origin == Json.mkObj [("kind", toJson "reduced"), ("parentProgram", parentProgram),
        ("parentPlan", parentPlan), ("parentInput", toJson parentText)] do
      throw "reduced assembly provenance is not canonical"
  let fresh := makeCase admitted.plan admitted.input emitted origin fuel revision mask
  unless (← fresh.getObjVal? "provenance") == provenance do
    throw "assembly provenance contains unexpected fields"
  return fresh

/-- A primitive reduction of the Core function, rendered in the parent's form. -/
structure Reduction (source : CheckedInput) where private mk ::
  candidate : CheckedInput
  sameForm : candidate.plan.form = source.plan.form
  strict : (complexity candidate.program.body).StrictlySmaller (complexity source.program.body)

/-- The primitive reductions: G0 shrinking under the abstraction and smaller
inputs, each sealed by the full checker and strictly smaller. Keeping the form
changes no Core node. -/
def reductions (source : CheckedInput) : List (Reduction source) :=
  (Primitive.reductions ⟨source.plan.function, source.input⟩).map fun reduced =>
    ⟨⟨⟨reduced.candidate.function, source.plan.form⟩, reduced.candidate.input⟩, rfl, reduced.strict⟩

def shrinkCases (json : Json) (limit fuel : Nat) : Except String Json := do
  let _ ← replayCase json fuel
  let source ← caseProgram json
  let provenance ← json.getObjVal? "provenance"
  let revision := savedPureRevision provenance "baseGeneratorVersion"
  let mask ← savedMask provenance revision featureSupport
  let mut cases : Array Json := #[]
  for reduced in (reductions source).take limit do
    let origin := Json.mkObj [
      ("kind", toJson "reduced"), ("parentProgram", Wire.encodeProgram source.program),
      ("parentPlan", planJson source.plan), ("parentInput", toJson (toString source.input.val))]
    cases := cases.push
      (← emitCase reduced.candidate.plan reduced.candidate.input origin fuel revision mask)
  return Json.mkObj [("schema", toJson corpusSchema), ("cases", .arr cases)]

end Solcore.Synthesis.Source.Assembly
