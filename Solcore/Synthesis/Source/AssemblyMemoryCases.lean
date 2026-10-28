import Solcore.Synthesis.Source.AssemblyCases
import Solcore.Synthesis.Source.AssemblyMemoryEmitter

/-! An inline Yul memory case retains the independently checked original Core
function of the primitive profile, the step, and the memory schedule drawn
from its seed. Generation repeats the primitive profile's steps for the step,
and the reference composes the step with the window model of
`Solcore.Synthesis.Core.AssemblyMemory`, which never reads the Yul text. Saved
observations never supply the oracle. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.AssemblyMemory
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.Synthesis.Core.AssemblyMemory (Schedule Stage Hash Width)

def caseSchema : String := "solcore-lean.semantic-assembly-memory-case.v1"
def planSchema : String := "solcore-lean.assembly-memory-plan.v1"
def profileVersion : String := "runtime-assembly-memory-v1/schedule-seed-v1"

/-- The applied step's limit, as for `runtime-assembly`; the schedule and the
closure lie outside it. -/
def stepLimit : Nat := 512

/-- A checked step, an admitted schedule, and a full Core check of the
composed reference. The input is a literal, so its check does not depend on it. -/
structure CheckedPlan where private mk ::
  function : CheckedWordFunction
  schedule : Schedule
  admitted : schedule.admitted = true
  checked : (AssemblyMemory.program function.program.body schedule Word.zero).check = true

namespace CheckedPlan

def ofParts? (function : CheckedWordFunction) (schedule : Schedule) : Option CheckedPlan :=
  if admitted : schedule.admitted = true then
    if checked : (AssemblyMemory.program function.program.body schedule Word.zero).check = true then
      some ⟨function, schedule, admitted, checked⟩
    else none
  else none

def program (plan : CheckedPlan) (input : Word) : Wire.Program :=
  AssemblyMemory.program plan.function.program.body plan.schedule input

end CheckedPlan

structure CheckedInput where
  plan : CheckedPlan
  input : Word

def CheckedInput.program (value : CheckedInput) : Wire.Program := value.plan.program value.input

private def stageJson (stage : Stage) : Json := Json.mkObj [
  ("read", toJson stage.read), ("width", toJson stage.width.name), ("write", toJson stage.write)]

def scheduleJson (schedule : Schedule) : List (String × Json) := [
  ("stages", .arr (schedule.stages.map stageJson).toArray), ("finalRead", toJson schedule.final),
  ("hash", match schedule.hash with
    | none => Json.null
    | some hash => Json.mkObj [("offset", toJson hash.offset), ("length", toJson hash.length)])]

def planJson (plan : CheckedPlan) : Json := Json.mkObj ([
  ("schema", toJson planSchema), ("functionProgram", Wire.encodeProgram plan.function.program)] ++
  scheduleJson plan.schedule)

private def stageOf (json : Json) : Except String Stage := do
  let some width := Width.ofString? (← json.getObjValAs? String "width") |
    throw "assembly memory stage width must be word or byte"
  return ⟨← json.getObjValAs? Nat "read", width, ← json.getObjValAs? Nat "write"⟩

def scheduleOf (json : Json) : Except String Schedule := do
  let stages ← (← json.getObjValAs? (Array Json) "stages").toList.mapM stageOf
  let final ← json.getObjValAs? Nat "finalRead"
  let hash ← match ← json.getObjVal? "hash" with
    | .null => pure none
    | value => pure (some ⟨← value.getObjValAs? Nat "offset", ← value.getObjValAs? Nat "length"⟩)
  return ⟨stages, final, hash⟩

def checkedPlan (json : Json) : Except String CheckedPlan := do
  unless (← json.getObjValAs? String "schema") = planSchema do
    throw "unsupported assembly memory plan schema"
  let function ← Primitive.checkedFunction (← json.getObjVal? "functionProgram")
  let schedule ← scheduleOf json
  unless schedule.admitted do
    throw "assembly memory schedule is outside the admitted stages, offsets and hashed lengths"
  let some plan := CheckedPlan.ofParts? function schedule |
    throw "assembly memory reference failed the full Core checker"
  unless json == planJson plan do
    throw "saved assembly memory plan differs from its canonical checked representation"
  unless Wire.programNodes (function.instantiate Word.zero) ≤ stepLimit do
    throw "applied assembly memory step exceeds the 512-node step limit"
  return plan

/-- The reference on one input, with the observation fields of the primitive profile. -/
def observe (plan : CheckedPlan) (input : Word) (fuel : Nat) : Json :=
  let fields := match (plan.program input).toCore.runStateful fuel with
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
  ("calldata", toJson (Primitive.calldata input)), ("constructorCalldata", toJson "0x")]

def makeCase (plan : CheckedPlan) (input : Word) (emitted : EmittedProgram)
    (origin : Json) (fuel : Nat) (revision : GeneratorRevision := .v1)
    (mask : FeatureMask := FeatureMask.all) : Json := Json.mkObj [
  ("schema", toJson caseSchema), ("assemblyMemoryPlan", planJson plan),
  ("program", Wire.encodeProgram (plan.program input)),
  ("input", toJson (toString input.val)), ("source", toJson emitted.source),
  ("provenance", Json.mkObj <| swarmField revision mask ++ [
    ("origin", origin), ("profileVersion", toJson profileVersion),
    ("functionProfileVersion", toJson Primitive.profileVersion),
    ("functionVersion", toJson wordFunctionVersion),
    ("abstractionVersion", toJson abstractionVersion),
    ("generatorVersion", toJson (Primitive.generatorVersionFor revision)),
    ("baseGeneratorVersion", toJson revision.version),
    ("boundaryVersion", toJson Primitive.boundaryVersion),
    ("memoryVersion", toJson AssemblyMemory.version),
    ("emitterVersion", toJson emitterVersion), ("wrapperVersion", toJson wrapperVersion),
    ("features", toJson ((features plan.function.body).map featureName))]),
  ("contract", contractJson emitted input), ("executionFuel", toJson fuel),
  ("directCore", observe plan input fuel)]

def emitCase (plan : CheckedPlan) (input : Word) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1)
    (mask : FeatureMask := FeatureMask.all) : Except String Json := do
  unless Wire.programNodes (plan.function.instantiate input) ≤ stepLimit do
    throw "applied assembly memory step exceeds the 512-node step limit"
  unless (plan.program input).check do
    throw "assembly memory reference failed the full Core checker"
  let emitted ← (emit plan.function plan.schedule).mapError reprStr
  return makeCase plan input emitted origin fuel revision mask

/-- The decode bound of a saved reference: the step limit, the schedule's
largest overhead and the largest closure. -/
def caseLimit : Nat := 3282

/-- Every origin keeps the canonical reference of its plan at its input. -/
def caseProgram (json : Json) : Except String CheckedInput := do
  unless (← json.getObjValAs? String "schema") = caseSchema do
    throw "unsupported semantic assembly memory case schema"
  let plan ← checkedPlan (← json.getObjVal? "assemblyMemoryPlan")
  let input ← Primitive.inputWord (← json.getObjValAs? String "input")
  let program ← (Wire.decodeProgramWithBudget
    {maxDepth := caseLimit, maxNodes := caseLimit, maxIntegerBytes := 4096}
    (← json.getObjVal? "program")).mapError (fun
      | .protocol error => error.toJson.compress
      | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)
  unless Wire.encodeProgram program == Wire.encodeProgram (plan.program input) do
    throw "saved Core program differs from its assembly memory plan's reference and runtime input"
  return ⟨plan, input⟩

/-- Separates the schedule stream from other uses of a case seed. -/
private def scheduleDomain : UInt64 := 0x61736d6d656d6f01

private def gamma : UInt64 := 0x9e3779b97f4a7c15

/-- Value `index` of the seed's schedule stream, reduced to `[0, bound)` from its upper 32 bits. -/
private def draw (seed : Seed) (index bound : Nat) : Nat :=
  ((GeneratorV2.mix ((seed.toUInt64 ^^^ scheduleDomain) + UInt64.ofNat (index + 1) * gamma)).toNat / 2 ^ 32) % bound

/-- The delta classes 0, 1, 2–15, 16, 17–30 and 31. -/
def deltaClasses : List (Nat × Nat) := [(0, 0), (1, 1), (2, 15), (16, 16), (17, 30), (31, 31)]

/-- An offset from three stream values: its class, its delta in the class, and
its Word: 0, 32 or 64 for a byte or a delta of zero, else 0 or 32. -/
private def drawOffset (seed : Seed) (index : Nat) (byte : Bool) : Nat :=
  let (low, high) := deltaClasses.getD (draw seed index 6) (0, 0)
  let delta := low + draw seed (index + 1) (high - low + 1)
  32 * draw seed (index + 2) (if byte || delta = 0 then 3 else 2) + delta

/-- The schedule of a case seed: the stage count; per stage the read offset,
the width and the write offset; the final read offset; the hash, none or one
of the six lengths; then its offset. -/
def scheduleFor (seed : Seed) : Schedule := Id.run do
  let count := 1 + draw seed 0 AssemblyMemory.maximumStages
  let mut index := 1
  let mut stages : List Stage := []
  for _ in List.range count do
    let read := drawOffset seed index false
    let width := if draw seed (index + 3) 2 = 0 then Width.word else Width.byte
    let write := drawOffset seed (index + 4) (width == .byte)
    stages := stages ++ [⟨read, width, write⟩]
    index := index + 7
  let final := drawOffset seed index false
  let choice := draw seed (index + 3) (AssemblyMemory.hashLengths.length + 1)
  let hash := if choice = 0 then none else
    let length := AssemblyMemory.hashLengths.getD (choice - 1) 0
    some ⟨draw seed (index + 4) (AssemblyMemory.windowBytes - length + 1), length⟩
  return ⟨stages, final, hash⟩

/-- A generation filter on the composed reference, not a claim that this
finite bank covers a function. -/
def boundaryResults (plan : CheckedPlan) (fuel : Nat) : Except String (List Word) := do
  Primitive.boundaryInputs.mapM fun input =>
    match (plan.program input).toCore.runStateful fuel with
    | .done (.word value) _ => .ok value
    | .done _ _ => .error "boundary observation did not return a Word"
    | .outOfFuel _ => .error "boundary observation exhausted Core fuel"
    | .fault _ _ => .error "boundary observation produced a Core fault"

def inputSensitive (plan : CheckedPlan) (fuel : Nat) (acceptance : Acceptance := .profile) :
    Except String Unit := do
  let results ← boundaryResults plan fuel
  unless results.any (fun value => results.any (fun other => value != other)) do
    throw "all eight boundary inputs returned the same Word"
  acceptance.check Primitive.boundaryInputs results

/-- The generated origin before its input index, validation fuel, input
selection and acceptance filter. -/
private def generatedOrigin (seed : Seed) (nodes : Nat) (generated : GeneratedProgram)
    (literalIndex : Nat) : List (String × Json) := [
  ("kind", toJson "assembly-memory-generated"), ("seed", toJson (toString seed.toNat)),
  ("finalSeed", toJson (toString generated.finalSeed.toNat)), ("maxProgramNodes", toJson nodes),
  ("baseProgramNodes", toJson generated.maxProgramNodes), ("literalIndex", toJson literalIndex)]

/-- The step by the primitive profile's steps and the seed's schedule. -/
def generatedPlan (seed : Seed) (nodes : Nat) (revision : GeneratorRevision) :
    Except String (GeneratedProgram × Nat × CheckedPlan) := do
  let (generated, literalIndex, function) ← Assembly.primitiveFunction seed nodes revision
  let some plan := CheckedPlan.ofParts? function (scheduleFor seed) |
    throw "assembly memory reference failed the full Core checker"
  return (generated, literalIndex, plan)

/-- Attempt limits count functions; case limits count individual runtime inputs. -/
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
        let (generated, literalIndex, plan) ← generatedPlan seed nodes revision
        let emitted ← (emit plan.function plan.schedule).mapError
          (fun error => "unsupported source primitive: " ++ reprStr error)
        inputSensitive plan fuel acceptance
        return (generated, literalIndex, plan, emitted)
      match result with
      | .error error =>
          let resource := error == "boundary observation exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)),
            ("stage", toJson "assembly-memory-profile"), ("reason", toJson error),
            ("code", toJson (if resource then "boundary-out-of-fuel"
              else if error.startsWith "unsupported source primitive:" then "unsupported-operation"
              else if error == Acceptance.identityReason then "boundary-identity" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok (generated, literalIndex, plan, emitted) =>
          for (input, inputIndex) in (inputSelection.inputs Primitive.boundaryInputs seed).zipIdx do
            if cases.size < count then
              let origin := Json.mkObj (generatedOrigin seed nodes generated literalIndex ++
                [("inputIndex", toJson inputIndex), ("validationFuel", toJson fuel)])
              cases := cases.push
                (makeCase plan input emitted (acceptance.record (inputSelection.record origin)) fuel revision
                  (revision.caseMask seed featureSupport))
  return Json.mkObj [("schema", toJson corpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

/-- The lexicographic shrink measure: stages, hash rank, delta sum, then the
applied step's nodes and literal weight. -/
structure Measure where
  stages : Nat
  hash : Nat
  deltas : Nat
  step : Complexity
  deriving Repr, BEq, DecidableEq

namespace Measure

def StrictlySmaller (candidate source : Measure) : Prop :=
  candidate.stages < source.stages ∨ (candidate.stages = source.stages ∧
    (candidate.hash < source.hash ∨ (candidate.hash = source.hash ∧
      (candidate.deltas < source.deltas ∨ (candidate.deltas = source.deltas ∧
        candidate.step.StrictlySmaller source.step)))))

instance (candidate source : Measure) : Decidable (candidate.StrictlySmaller source) := by
  unfold StrictlySmaller
  infer_instance

end Measure

def CheckedInput.measure (value : CheckedInput) : Measure :=
  ⟨value.plan.schedule.stages.length, value.plan.schedule.hashRank, value.plan.schedule.deltaSum,
    complexity (value.plan.function.instantiate value.input).body⟩

def replayCase (json : Json) (fuel : Nat) : Except String Json := do
  let admitted ← caseProgram json
  let provenance ← json.getObjVal? "provenance"
  let revision := savedPureRevision provenance "baseGeneratorVersion"
  for (name, expected) in [
      ("generatorVersion", Primitive.generatorVersionFor revision), ("profileVersion", profileVersion),
      ("functionProfileVersion", Primitive.profileVersion),
      ("baseGeneratorVersion", revision.version), ("boundaryVersion", Primitive.boundaryVersion),
      ("functionVersion", wordFunctionVersion), ("abstractionVersion", abstractionVersion),
      ("memoryVersion", AssemblyMemory.version),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do
      throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let mask ← savedMask provenance revision featureSupport
  let emitted ← (emit admitted.plan.function admitted.plan.schedule).mapError reprStr
  unless (← json.getObjValAs? String "source") = emitted.source do
    throw "saved source differs from emission of the assembly memory plan"
  unless (← json.getObjVal? "contract") == contractJson emitted admitted.input do
    throw "saved contract metadata differs from the assembly memory wrapper"
  unless (← provenance.getObjVal? "features") ==
      toJson ((features admitted.plan.function.body).map featureName) do
    throw "saved features differ from the original Core step"
  let kind ← origin.getObjValAs? String "kind"
  unless kind = "assembly-memory-generated" || kind = "imported" || kind = "reduced" do
    throw "unsupported assembly memory case origin"
  if kind = "assembly-memory-generated" then
    let seedText ← origin.getObjValAs? String "seed"
    let some seed := seedText.toNat? | throw "invalid saved seed"
    unless seed < 2 ^ 64 && toString seed = seedText do throw "noncanonical saved seed"
    unless mask == revision.caseMask (Seed.ofNat seed) featureSupport do
      throw "saved swarm mask differs from its generation seed"
    let nodes ← origin.getObjValAs? Nat "maxProgramNodes"
    unless Primitive.minimumProgramNodes ≤ nodes && nodes ≤ 512 do
      throw "saved generation budget exceeds profile limits"
    let (generated, literalIndex, plan) ← generatedPlan (Seed.ofNat seed) nodes revision
    unless admitted.plan.schedule == plan.schedule do
      throw "saved assembly memory schedule differs from its generation seed"
    unless Wire.encodeProgram plan.function.program == Wire.encodeProgram admitted.plan.function.program do
      throw "saved step differs from its generation seed"
    let inputIndex ← origin.getObjValAs? Nat "inputIndex"
    let inputSelection ← InputSelection.ofOrigin origin
    unless (inputSelection.inputs Primitive.boundaryInputs (Seed.ofNat seed))[inputIndex]? = some admitted.input do
      throw "saved input differs from its boundary index"
    let validationFuel ← origin.getObjValAs? Nat "validationFuel"
    unless validationFuel ≤ 10000000 do throw "saved validation fuel exceeds limit"
    let acceptance ← Acceptance.ofOrigin origin
    inputSensitive plan validationFuel acceptance
    unless origin == acceptance.record (inputSelection.record (Json.mkObj (
        generatedOrigin (Seed.ofNat seed) nodes generated literalIndex ++
        [("inputIndex", toJson inputIndex), ("validationFuel", toJson validationFuel)]))) do
      throw "generated assembly memory provenance is not canonical"
  else if kind = "imported" then
    unless origin == Json.mkObj [("kind", toJson "imported")] do
      throw "imported assembly memory provenance is not canonical"
  else
    let parentPlan ← origin.getObjVal? "parentPlan"
    let parentText ← origin.getObjValAs? String "parentInput"
    let parent : CheckedInput := ⟨← checkedPlan parentPlan, ← Primitive.inputWord parentText⟩
    unless decide (admitted.measure.StrictlySmaller parent.measure) do
      throw "saved assembly memory reduction is not strictly smaller than its checked parent"
    unless origin == Json.mkObj [("kind", toJson "reduced"), ("parentPlan", parentPlan),
        ("parentInput", toJson parentText)] do
      throw "reduced assembly memory provenance is not canonical"
  let fresh := makeCase admitted.plan admitted.input emitted origin fuel revision mask
  unless (← fresh.getObjVal? "provenance") == provenance do
    throw "assembly memory provenance contains unexpected fields"
  return fresh

/-- Sealing includes the full Core check of the composed reference and a
strictly smaller measure. -/
structure Reduction (source : CheckedInput) where private mk ::
  candidate : CheckedInput
  strict : candidate.measure.StrictlySmaller source.measure

private def sealReduction (source : CheckedInput) (function : CheckedWordFunction) (schedule : Schedule)
    (input : Word) : Option (Reduction source) := do
  let plan ← CheckedPlan.ofParts? function schedule
  let candidate : CheckedInput := ⟨plan, input⟩
  if strict : candidate.measure.StrictlySmaller source.measure then some ⟨candidate, strict⟩ else none

private def aligned (offset : Nat) : Nat := offset - offset % 32

/-- One stage removed, keeping one; the hash removed or shortened at its
offset; one offset aligned within its Word. -/
def scheduleReductions (schedule : Schedule) : List Schedule :=
  let stages := schedule.stages
  let removed := if stages.length > 1 then
      (List.range stages.length).map fun index => {schedule with stages := stages.eraseIdx index}
    else []
  let hashes := match schedule.hash with
    | none => []
    | some hash => {schedule with hash := none} ::
        ((AssemblyMemory.hashLengths.filter (· < hash.length)).map fun length =>
          {schedule with hash := some ⟨hash.offset, length⟩})
  let stageAligned := stages.zipIdx.flatMap fun (stage, index) =>
    [{schedule with stages := stages.set index {stage with read := aligned stage.read}},
     {schedule with stages := stages.set index {stage with write := aligned stage.write}}]
  let finalAligned := [{schedule with final := aligned schedule.final}]
  let hashAligned := match schedule.hash with
    | none => []
    | some hash => [{schedule with hash := some ⟨aligned hash.offset, hash.length⟩}]
  removed ++ hashes ++ stageAligned ++ finalAligned ++ hashAligned

/-- The schedule reductions with the step and input kept, then the primitive
reductions of the step and input with the schedule kept. -/
def reductions (source : CheckedInput) : List (Reduction source) := Id.run do
  let raw := (scheduleReductions source.plan.schedule).map
      (fun schedule => (source.plan.function, schedule, source.input)) ++
    (Primitive.reductions ⟨source.plan.function, source.input⟩).map fun reduced =>
      (reduced.candidate.function, source.plan.schedule, reduced.candidate.input)
  let mut seen : List String := []
  let mut result := []
  for (function, schedule, input) in raw do
    if let some reduced := sealReduction source function schedule input then
      let key := (planJson reduced.candidate.plan).compress ++ toString reduced.candidate.input.val
      if !seen.contains key then
        seen := key :: seen
        result := result ++ [reduced]
  return result

/-- A plan with a hash embeds the closure in every candidate, so its shrink
response holds at most eight. -/
def shrinkBatch (plan : CheckedPlan) (limit : Nat) : Nat :=
  if plan.schedule.hash.isSome then min limit 8 else limit

def shrinkCases (json : Json) (limit fuel : Nat) : Except String Json := do
  let _ ← replayCase json fuel
  let source ← caseProgram json
  let provenance ← json.getObjVal? "provenance"
  let revision := savedPureRevision provenance "baseGeneratorVersion"
  let mask ← savedMask provenance revision featureSupport
  let mut cases : Array Json := #[]
  for reduced in (reductions source).take (shrinkBatch source.plan limit) do
    let origin := Json.mkObj [
      ("kind", toJson "reduced"), ("parentPlan", planJson source.plan),
      ("parentInput", toJson (toString source.input.val))]
    cases := cases.push
      (← emitCase reduced.candidate.plan reduced.candidate.input origin fuel revision mask)
  return Json.mkObj [("schema", toJson corpusSchema), ("cases", .arr cases)]

end Solcore.Synthesis.Source.AssemblyMemory
