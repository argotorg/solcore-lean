import Solcore.Synthesis.Source.PrimitiveCases
import Solcore.Synthesis.Source.IntegersEmitter
import Solcore.Synthesis.Core.IntegersShrink

/-! The cases of the two integer profiles, `runtime-checked-arithmetic` and
`runtime-shifts`. A case retains its plan, drawn from the case seed, and the
plan's complete original Core reference at the case input, built from the plan,
never from the source. The reference's right injection is the revert data: a
length and two Words, observed as the bytes they hold. Saved observations never
supply the oracle. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.Integers
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.Synthesis.Core.Integers

/-- What tells the two profiles apart: their names, versions and keys, the
plans they admit, how they draw, emit and shape a plan. -/
structure Profile where
  caseSchema : String
  planSchema : String
  profileVersion : String
  emitterVersion : String
  wrapperVersion : String
  planKey : String
  shapesKey : String
  originKind : String
  stage : String
  label : String
  admitted : Plan → Bool
  generate : UInt64 → Plan
  emit : Plan → EmittedProgram
  shapes : Plan → List (String × List String)

/-- The node budget, which bounds the applied reference, and the decode bound
of a saved reference. -/
def defaultNodes : Nat := 1024
def minimumNodes : Nat := 256
def maximumNodes : Nat := 2048
def caseLimit : Nat := 4096

/-- An admitted plan whose reference passes the full Core checker. The input
is a literal, so the check at zero holds at every input. -/
structure CheckedPlan (profile : Profile) where private mk ::
  plan : Plan
  admitted : profile.admitted plan = true
  checked : (plan.applied Word.zero).check = true

namespace CheckedPlan

def ofPlan? {profile : Profile} (plan : Plan) : Option (CheckedPlan profile) :=
  if admitted : profile.admitted plan = true then
    if checked : (plan.applied Word.zero).check = true then some ⟨plan, admitted, checked⟩ else none
  else none

def program {profile : Profile} (plan : CheckedPlan profile) (input : Word) : Wire.Program := plan.plan.applied input

end CheckedPlan

structure CheckedInput (profile : Profile) where
  plan : CheckedPlan profile
  input : Word

/-! Plan JSON. Every decoder is strict and the decoded plan must re-encode to
the saved JSON. -/

def valueTypeName : ValueType → String := ValueType.name

def valueTypeOf (text : String) : Except String ValueType :=
  match ValueType.all.find? (·.name == text) with
  | some type => .ok type
  | none => .error "unknown integer type"

def opOf (text : String) : Except String Op :=
  match Op.all.find? (·.name == text) with
  | some op => .ok op
  | none => .error "unknown integer operation"

def operandJson : Operand → Json
  | .input index => Json.mkObj [("input", toJson index)]
  | .var index => Json.mkObj [("var", toJson index)]
  | .literal index => Json.mkObj [("literal", toJson index)]

def operandOf (json : Json) : Except String Operand := do
  if let .ok index := json.getObjValAs? Nat "input" then return .input index
  if let .ok index := json.getObjValAs? Nat "var" then return .var index
  if let .ok index := json.getObjValAs? Nat "literal" then return .literal index
  throw "unknown integer operand"

def amountJson : Amount → Json
  | .input index => Json.mkObj [("input", toJson index)]
  | .literal index => Json.mkObj [("literal", toJson index)]

def amountOf (json : Json) : Except String Amount := do
  if let .ok index := json.getObjValAs? Nat "input" then return .input index
  if let .ok index := json.getObjValAs? Nat "literal" then return .literal index
  throw "unknown integer shift amount"

def testJson : Test → Json
  | .lt constant => Json.mkObj [("test", toJson "lt"), ("constant", toJson (toString constant))]
  | .gt constant => Json.mkObj [("test", toJson "gt"), ("constant", toJson (toString constant))]
  | .eq constant => Json.mkObj [("test", toJson "eq"), ("constant", toJson (toString constant))]
  | .bits mask value => Json.mkObj [("test", toJson "bits"), ("mask", toJson mask), ("value", toJson value)]

private def natText (text : String) : Except String Nat :=
  match text.toNat? with
  | some value => if toString value == text then .ok value else .error "noncanonical integer plan number"
  | none => .error "integer plan number is not decimal"

def testOf (json : Json) : Except String Test := do
  match ← json.getObjValAs? String "test" with
  | "lt" => return .lt (← natText (← json.getObjValAs? String "constant"))
  | "gt" => return .gt (← natText (← json.getObjValAs? String "constant"))
  | "eq" => return .eq (← natText (← json.getObjValAs? String "constant"))
  | "bits" => return .bits (← json.getObjValAs? Nat "mask") (← json.getObjValAs? Nat "value")
  | _ => throw "unknown integer test"

def formJson : Form → Json
  | .binary op left right => Json.mkObj [("form", toJson "binary"), ("op", toJson op.name),
      ("left", operandJson left), ("right", operandJson right)]
  | .neg operand => Json.mkObj [("form", toJson "neg"), ("operand", operandJson operand)]
  | .compound op left right => Json.mkObj [("form", toJson "compound"), ("op", toJson op.name),
      ("left", operandJson left), ("right", operandJson right)]
  | .call helper left right => Json.mkObj [("form", toJson "call"), ("helper", toJson helper),
      ("left", operandJson left), ("right", operandJson right)]
  | .apply op unchecked left right => Json.mkObj [("form", toJson "apply"), ("op", toJson op.name),
      ("unchecked", toJson unchecked), ("left", operandJson left), ("right", operandJson right)]

def formOf (json : Json) : Except String Form := do
  let pair : Except String (Operand × Operand) := do
    return (← operandOf (← json.getObjVal? "left"), ← operandOf (← json.getObjVal? "right"))
  match ← json.getObjValAs? String "form" with
  | "binary" => let (left, right) ← pair; return .binary (← opOf (← json.getObjValAs? String "op")) left right
  | "neg" => return .neg (← operandOf (← json.getObjVal? "operand"))
  | "compound" => let (left, right) ← pair; return .compound (← opOf (← json.getObjValAs? String "op")) left right
  | "call" => let (left, right) ← pair; return .call (← json.getObjValAs? Nat "helper") left right
  | "apply" =>
      let (left, right) ← pair
      return .apply (← opOf (← json.getObjValAs? String "op")) (← json.getObjValAs? Bool "unchecked") left right
  | _ => throw "unknown integer form"

def stepJson : Step → Json
  | .assign form => Json.mkObj [("assign", formJson form)]
  | .default made => Json.mkObj [("default", Json.mkObj [("initial", toJson made.initial),
      ("test", testJson made.test), ("chosen", toJson made.chosen), ("op", toJson made.op.name),
      ("operand", toJson made.operand)])]
  | .shift shift => Json.mkObj [("shift", Json.mkObj [
      ("direction", toJson (match shift.direction with
        | .left => "left"
        | .right => "right")), ("compound", toJson shift.compound),
      ("value", operandJson shift.value), ("amount", amountJson shift.amount)])]

def stepOf (json : Json) : Except String Step := do
  if let .ok form := json.getObjVal? "assign" then return .assign (← formOf form)
  if let .ok made := json.getObjVal? "default" then
    let initial ← made.getObjValAs? Nat "initial"
    let test ← testOf (← made.getObjVal? "test")
    let chosen ← made.getObjValAs? Nat "chosen"
    let op ← opOf (← made.getObjValAs? String "op")
    let operand ← made.getObjValAs? Nat "operand"
    return .default {initial, test, chosen, op, operand}
  if let .ok shift := json.getObjVal? "shift" then
    let direction ← match ← shift.getObjValAs? String "direction" with
      | "left" => pure Direction.left
      | "right" => pure Direction.right
      | _ => throw "unknown shift direction"
    let compound ← shift.getObjValAs? Bool "compound"
    let value ← operandOf (← shift.getObjVal? "value")
    let amount ← amountOf (← shift.getObjVal? "amount")
    return .shift {direction, compound, value, amount}
  throw "unknown integer step"

def planJsonWith (schema : String) (plan : Plan) : Json := Json.mkObj [
  ("schema", toJson schema), ("value", toJson plan.value.name), ("abi", toJson plan.abi), ("raw", toJson plan.raw),
  ("inputs", toJson (plan.inputs.map toString)),
  ("amounts", Json.arr (plan.amounts.map (fun amount => Json.mkObj [("type", toJson amount.type.name),
    ("offset", toJson amount.offset)])).toArray),
  ("helpers", Json.arr (plan.helpers.map (fun helper => Json.mkObj [("op", toJson helper.op.name),
    ("unchecked", toJson helper.unchecked)])).toArray),
  ("groups", Json.arr (plan.groups.map (fun group => Json.mkObj [("unchecked", toJson group.unchecked),
    ("steps", Json.arr (group.steps.map stepJson).toArray)])).toArray)]

private def array (json : Json) (key : String) : Except String (List Json) := do
  return (← json.getObjValAs? (Array Json) key).toList

def planOfWith (schema : String) (json : Json) : Except String Plan := do
  unless (← json.getObjValAs? String "schema") = schema do throw "unsupported integer plan schema"
  let inputs ← (← array json "inputs").mapM fun item => do natText (← item.getStr?)
  let amounts ← (← array json "amounts").mapM fun item => do
    return ({type := ← valueTypeOf (← item.getObjValAs? String "type"), offset := ← item.getObjValAs? Nat "offset"} :
      AmountInput)
  let helpers ← (← array json "helpers").mapM fun item => do
    return ({op := ← opOf (← item.getObjValAs? String "op"), unchecked := ← item.getObjValAs? Bool "unchecked"} :
      Helper)
  let groups ← (← array json "groups").mapM fun item => do
    return ({unchecked := ← item.getObjValAs? Bool "unchecked", steps := ← (← array item "steps").mapM stepOf} : Group)
  let value ← valueTypeOf (← json.getObjValAs? String "value")
  let abi ← json.getObjValAs? Bool "abi"
  let raw ← json.getObjValAs? Bool "raw"
  return {value, abi, raw, inputs, amounts, helpers, groups}

namespace Profile

def planJson (profile : Profile) (plan : Plan) : Json := planJsonWith profile.planSchema plan

def checkedPlan (profile : Profile) (json : Json) : Except String (CheckedPlan profile) := do
  let plan ← planOfWith profile.planSchema json
  unless profile.admitted plan do
    throw (profile.label ++ " plan is outside the admitted types, inputs, steps, operands and literals")
  let some checked := CheckedPlan.ofPlan? (profile := profile) plan
    | throw (profile.label ++ " reference failed the full Core checker")
  unless json == profile.planJson plan do
    throw ("saved " ++ profile.label ++ " plan differs from its canonical checked representation")
  unless plan.nodes ≤ caseLimit do throw (profile.label ++ " reference exceeds the 4,096-node case limit")
  return checked

def shapesJson (profile : Profile) (plan : Plan) : Json :=
  Json.mkObj ((profile.shapes plan).map fun (dimension, values) => (dimension, toJson values))

end Profile

/-! Observation: the reference's right injection is the revert data. -/

private def hexDigit (value : Nat) : Char := "0123456789abcdef".toList.getD value '0'

def hexBytes (bytes : List Nat) : String :=
  "0x" ++ String.ofList (bytes.flatMap fun byte => [hexDigit (byte / 16), hexDigit (byte % 16)])

def wordBytes (value : Nat) : List Nat := (List.range 32).reverse.map fun index => (value / 256 ^ index) % 256

/-- A returned Word, or revert data. -/
inductive Observed where
  | word (value : Word)
  | reverted (data : List Nat)
  deriving BEq

def Observed.ofValue? : Value → Option Observed
  | .inLeft _ (.word returned) => some (.word returned)
  | .inRight _ (.pair (.word length) (.pair (.word first) (.word second))) =>
      if length.val ≤ 64 then some (.reverted ((wordBytes first.val ++ wordBytes second.val).take length.val)) else none
  | _ => none

def observe {profile : Profile} (plan : CheckedPlan profile) (input : Word) (fuel : Nat) : Json :=
  let fields := match (plan.program input).toCore.runStateful fuel with
    | .done value _ => match Observed.ofValue? value with
        | some (.word word) => [("status", toJson "returned"), ("word", toJson (toString word.val))]
        | some (.reverted data) => [("status", toJson "reverted"), ("output", toJson (hexBytes data))]
        | none => [("status", toJson "invalid-result"), ("detail", toJson (reprStr value))]
    | .outOfFuel _ => [("status", toJson "out-of-fuel")]
    | .fault reason _ => [("status", toJson "core-fault"), ("detail", toJson (reprStr reason))]
  Json.mkObj (("stage", toJson "execution") :: fields)

/-- The selector of the plan's signature, then the input as one Word. -/
def calldata (plan : Plan) (input : Word) : String :=
  let selector := if plan.abi then plan.type.selector else Primitive.selector
  selector ++ String.ofList ((List.range 64).map fun index =>
    Char.ofNat (let digit := input.val / 16 ^ (63 - index) % 16
      if digit < 10 then 48 + digit else 87 + digit))

def contractJson (plan : Plan) (emitted : EmittedProgram) (input : Word) : Json := Json.mkObj [
  ("name", toJson emitted.contractName), ("method", toJson emitted.methodName),
  ("signature", toJson emitted.methodSignature),
  ("deployPath", toJson emitted.deployPath), ("runtimePath", toJson emitted.runtimePath),
  ("calldata", toJson (calldata plan input)), ("constructorCalldata", toJson "0x")]

namespace Profile

def makeCase (profile : Profile) (plan : CheckedPlan profile) (input : Word) (emitted : EmittedProgram) (origin : Json)
    (fuel : Nat) : Json :=
  Json.mkObj [
    ("schema", toJson profile.caseSchema), (profile.planKey, profile.planJson plan.plan),
    ("program", Wire.encodeProgram (plan.program input)),
    ("input", toJson (toString input.val)), ("source", toJson emitted.source),
    ("provenance", Json.mkObj [
      ("origin", origin), ("profileVersion", toJson profile.profileVersion),
      ("generatorVersion", toJson integerVersion), ("boundaryVersion", toJson Primitive.boundaryVersion),
      ("emitterVersion", toJson profile.emitterVersion), ("wrapperVersion", toJson profile.wrapperVersion),
      ("features", toJson ([] : List String)), ("referenceNodes", toJson plan.plan.nodes),
      (profile.shapesKey, profile.shapesJson plan.plan)]),
    ("contract", contractJson plan.plan emitted input), ("executionFuel", toJson fuel),
    ("directCore", observe plan input fuel)]

def emitCase (profile : Profile) (plan : CheckedPlan profile) (input : Word) (origin : Json) (fuel : Nat) :
    Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds profile limit"
  unless plan.plan.nodes ≤ caseLimit do throw (profile.label ++ " reference exceeds the 4,096-node case limit")
  return profile.makeCase plan input (profile.emit plan.plan) origin fuel

/-- Every origin keeps the canonical reference of its plan at its input. -/
def caseProgram (profile : Profile) (json : Json) : Except String (CheckedInput profile) := do
  unless (← json.getObjValAs? String "schema") = profile.caseSchema do
    throw ("unsupported semantic " ++ profile.label ++ " case schema")
  let plan ← profile.checkedPlan (← json.getObjVal? profile.planKey)
  let input ← Primitive.inputWord (← json.getObjValAs? String "input")
  let program ← (Wire.decodeProgramWithBudget
    {maxDepth := caseLimit, maxNodes := caseLimit, maxIntegerBytes := 4096}
    (← json.getObjVal? "program")).mapError (fun
      | .protocol error => error.toJson.compress
      | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)
  unless Wire.encodeProgram program == Wire.encodeProgram (plan.program input) do
    throw ("saved Core program differs from its " ++ profile.label ++ " plan's reference and runtime input")
  return ⟨plan, input⟩

/-- A generation filter on the reference, not a claim that this finite bank
covers a plan. -/
def boundaryOutcomes {profile : Profile} (plan : CheckedPlan profile) (fuel : Nat) : Except String (List Observed) := do
  Primitive.boundaryInputs.mapM fun input =>
    match (plan.program input).toCore.runStateful fuel with
    | .done value _ => match Observed.ofValue? value with
        | some outcome => .ok outcome
        | none => .error "boundary observation did not return a Word or revert data"
    | .outOfFuel _ => .error "boundary observation exhausted Core fuel"
    | .fault _ _ => .error "boundary observation produced a Core fault"

/-- At least two outcomes differ; with the identity filter, the Words are not
the inputs. -/
def inputSensitive {profile : Profile} (plan : CheckedPlan profile) (fuel : Nat) (acceptance : Acceptance := .profile) :
    Except String Unit := do
  let outcomes ← boundaryOutcomes plan fuel
  unless outcomes.any (fun outcome => outcomes.any (fun other => outcome != other)) do
    throw "all eight boundary inputs had the same outcome"
  let words := outcomes.filterMap fun outcome => match outcome with
    | .word value => some value
    | .reverted _ => none
  if words.length = outcomes.length then acceptance.check Primitive.boundaryInputs words

/-- The seed's plan, its steps dropped from the end while the reference
exceeds the budget. -/
def generatedPlan (profile : Profile) (seed : Seed) (nodes : Nat) : Except String (CheckedPlan profile) := do
  let plan := (profile.generate seed.toUInt64).fit nodes
  unless plan.nodes ≤ nodes do throw (profile.label ++ " reference exceeds the node budget")
  let some checked := CheckedPlan.ofPlan? (profile := profile) plan
    | throw (profile.label ++ " reference failed admission or the full Core checker")
  return checked

def generatedOrigin (profile : Profile) (seed : Seed) (nodes inputIndex fuel : Nat) : Json := Json.mkObj [
  ("kind", toJson profile.originKind), ("seed", toJson (toString seed.toNat)), ("maxProgramNodes", toJson nodes),
  ("inputIndex", toJson inputIndex), ("validationFuel", toJson fuel)]

/-- Attempt limits count plans; case limits count individual runtime inputs. -/
def generateCases (profile : Profile) (firstSeed : Seed) (nodes count attempts fuel : Nat)
    (inputSelection : InputSelection := .boundary) (acceptance : Acceptance := .profile) : Json := Id.run do
  let mut cases : Array Json := #[]
  let mut excluded : Array Json := #[]
  let mut attempted := 0
  for index in List.range attempts do
    if cases.size < count then
      attempted := attempted + 1
      let seed := Seed.ofNat (firstSeed.toNat + index)
      let result := do
        unless minimumNodes ≤ nodes && nodes ≤ maximumNodes do
          throw (profile.label ++ " node budget is outside 256 to 2,048")
        let plan ← profile.generatedPlan seed nodes
        inputSensitive plan fuel acceptance
        return plan
      match result with
      | .error error =>
          let resource := error == "boundary observation exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson profile.stage), ("reason", toJson error),
            ("code", toJson (if resource then "boundary-out-of-fuel"
              else if error == Acceptance.identityReason then "boundary-identity" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok plan =>
          let emitted := profile.emit plan.plan
          for (input, inputIndex) in (inputSelection.inputs Primitive.boundaryInputs seed).zipIdx do
            if cases.size < count then
              let origin := acceptance.record (inputSelection.record (profile.generatedOrigin seed nodes inputIndex fuel))
              cases := cases.push (profile.makeCase plan input emitted origin fuel)
  return Json.mkObj [("schema", toJson corpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

end Profile

/-! Reduction. -/

/-- The lexicographic shrink measure: plan size, then input. -/
structure Measure where
  plan : Nat
  input : Nat
  deriving Repr, BEq, DecidableEq

def Measure.StrictlySmaller (candidate source : Measure) : Prop :=
  candidate.plan < source.plan ∨ (candidate.plan = source.plan ∧ candidate.input < source.input)

instance (candidate source : Measure) : Decidable (candidate.StrictlySmaller source) := by
  unfold Measure.StrictlySmaller
  infer_instance

def CheckedInput.measure {profile : Profile} (value : CheckedInput profile) : Measure :=
  ⟨value.plan.plan.size, value.input.val⟩

structure Reduction {profile : Profile} (source : CheckedInput profile) where private mk ::
  candidate : CheckedInput profile
  strict : candidate.measure.StrictlySmaller source.measure

private def sealReduction {profile : Profile} (source : CheckedInput profile) (plan : Plan) (input : Word) :
    Option (Reduction source) := do
  let plan ← CheckedPlan.ofPlan? (profile := profile) plan
  guard (plan.plan.nodes ≤ caseLimit)
  let candidate : CheckedInput profile := ⟨plan, input⟩
  if strict : candidate.measure.StrictlySmaller source.measure then some ⟨candidate, strict⟩ else none

/-- The plan reductions with the input kept; then the inputs 0, 1 and half the
input with the plan kept. -/
def reductions {profile : Profile} (source : CheckedInput profile) : List (Reduction source) := Id.run do
  let input := source.input
  let raw := (source.plan.plan.reductions).map (fun plan => (plan, input)) ++
    [Word.zero, Word.ofNatModulo 1, Word.ofNatModulo (input.val / 2)].map fun value => (source.plan.plan, value)
  let mut seen : List String := []
  let mut result := []
  for (plan, input) in raw do
    if let some reduced := sealReduction source plan input then
      let key := (profile.planJson reduced.candidate.plan.plan).compress ++ toString reduced.candidate.input.val
      if !seen.contains key then
        seen := key :: seen
        result := result ++ [reduced]
  return result

namespace Profile

def replayCase (profile : Profile) (json : Json) (fuel : Nat) : Except String Json := do
  let admitted ← profile.caseProgram json
  let provenance ← json.getObjVal? "provenance"
  for (name, expected) in [
      ("profileVersion", profile.profileVersion), ("generatorVersion", integerVersion),
      ("boundaryVersion", Primitive.boundaryVersion),
      ("emitterVersion", profile.emitterVersion), ("wrapperVersion", profile.wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do
      throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let emitted := profile.emit admitted.plan.plan
  unless (← json.getObjValAs? String "source") = emitted.source do
    throw ("saved source differs from emission of the " ++ profile.label ++ " plan")
  unless (← json.getObjVal? "contract") == contractJson admitted.plan.plan emitted admitted.input do
    throw ("saved contract metadata differs from the " ++ profile.label ++ " wrapper")
  unless (← provenance.getObjVal? profile.shapesKey) == profile.shapesJson admitted.plan.plan do
    throw ("saved " ++ profile.label ++ " shapes differ from the plan")
  let kind ← origin.getObjValAs? String "kind"
  unless kind = profile.originKind || kind = "imported" || kind = "reduced" do
    throw ("unsupported " ++ profile.label ++ " case origin")
  if kind = profile.originKind then
    let seedText ← origin.getObjValAs? String "seed"
    let some seed := seedText.toNat? | throw "invalid saved seed"
    unless seed < 2 ^ 64 && toString seed = seedText do throw "noncanonical saved seed"
    let nodes ← origin.getObjValAs? Nat "maxProgramNodes"
    unless minimumNodes ≤ nodes && nodes ≤ maximumNodes do
      throw "saved generation budget exceeds profile limits"
    let plan ← profile.generatedPlan (Seed.ofNat seed) nodes
    unless profile.planJson plan.plan == profile.planJson admitted.plan.plan do
      throw ("saved " ++ profile.label ++ " plan differs from its generation seed")
    let inputIndex ← origin.getObjValAs? Nat "inputIndex"
    let inputSelection ← InputSelection.ofOrigin origin
    unless (inputSelection.inputs Primitive.boundaryInputs (Seed.ofNat seed))[inputIndex]? = some admitted.input do
      throw "saved input differs from its boundary index"
    let validationFuel ← origin.getObjValAs? Nat "validationFuel"
    unless validationFuel ≤ 10000000 do throw "saved validation fuel exceeds limit"
    let acceptance ← Acceptance.ofOrigin origin
    inputSensitive plan validationFuel acceptance
    unless origin == acceptance.record (inputSelection.record
        (profile.generatedOrigin (Seed.ofNat seed) nodes inputIndex validationFuel)) do
      throw ("generated " ++ profile.label ++ " provenance is not canonical")
  else if kind = "imported" then
    unless origin == Json.mkObj [("kind", toJson "imported")] do
      throw ("imported " ++ profile.label ++ " provenance is not canonical")
  else
    let parentPlan ← origin.getObjVal? "parentPlan"
    let parentText ← origin.getObjValAs? String "parentInput"
    let parent : CheckedInput profile := ⟨← profile.checkedPlan parentPlan, ← Primitive.inputWord parentText⟩
    unless decide (admitted.measure.StrictlySmaller parent.measure) do
      throw ("saved " ++ profile.label ++ " reduction is not strictly smaller than its checked parent")
    unless origin == Json.mkObj [("kind", toJson "reduced"), ("parentPlan", parentPlan),
        ("parentInput", toJson parentText)] do
      throw ("reduced " ++ profile.label ++ " provenance is not canonical")
  let fresh := profile.makeCase admitted.plan admitted.input emitted origin fuel
  unless (← fresh.getObjVal? "provenance") == provenance do
    throw (profile.label ++ " provenance contains unexpected fields")
  return fresh

/-- A shrink response stops before its compressed cases would exceed 1.5 MB,
below the campaign's 2 MiB tool-output limit. -/
def shrinkBytes : Nat := 1500000

def shrinkCases (profile : Profile) (json : Json) (limit fuel : Nat) : Except String Json := do
  let _ ← profile.replayCase json fuel
  let source ← profile.caseProgram json
  let mut cases : Array Json := #[]
  let mut bytes := 0
  for reduced in (reductions source).take limit do
    let origin := Json.mkObj [
      ("kind", toJson "reduced"), ("parentPlan", profile.planJson source.plan.plan),
      ("parentInput", toJson (toString source.input.val))]
    let case ← profile.emitCase reduced.candidate.plan reduced.candidate.input origin fuel
    let size := case.compress.utf8ByteSize
    if bytes + size > shrinkBytes then break
    bytes := bytes + size
    cases := cases.push case
  return Json.mkObj [("schema", toJson corpusSchema), ("cases", .arr cases)]

end Profile

end Solcore.Synthesis.Source.Integers
