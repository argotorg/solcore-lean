import Solcore.Synthesis.Source.MemoryValuesCases
import Solcore.Synthesis.Source.MemoryCallsEmitter
import Solcore.Synthesis.Core.MemoryCallsShrink

/-! A memory call case retains its plan, drawn from the case seed, and the
plan's complete original Core reference at the case input. The reference is
`runtime-memory-values`' byte-list model with every call inlined, built from
the plan, never from the source. Its right injection is an out-of-range
access, observed as std's `OutOfBounds()` revert data. Saved observations
never supply the oracle. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.MemoryCalls
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.Synthesis.Core.MemoryCalls
open Solcore.Synthesis.Core.MemoryValues (Ref Fold Width Operand Index)

def caseSchema : String := "solcore-lean.semantic-memory-call-case.v1"
def planSchema : String := "solcore-lean.memory-call-plan.v1"
def profileVersion : String := "runtime-memory-calls-v1/plan-seed-v1"
def outOfBounds : String := MemoryValues.outOfBounds

/-- The node budget, which bounds the applied reference without the hash
closure, and the decode bound of a saved reference. -/
def defaultNodes : Nat := 1024
def minimumNodes : Nat := 256
def maximumNodes : Nat := 2048
def caseLimit : Nat := 5120

/-- An admitted plan whose reference passes the full Core checker. The input
is a literal, so the check at zero holds at every input. -/
structure CheckedPlan where private mk ::
  plan : Plan
  admitted : plan.admitted = true
  checked : (plan.applied Word.zero).check = true

namespace CheckedPlan

def ofPlan? (plan : Plan) : Option CheckedPlan :=
  if admitted : plan.admitted = true then
    if checked : (plan.applied Word.zero).check = true then some ⟨plan, admitted, checked⟩ else none
  else none

def program (plan : CheckedPlan) (input : Word) : Wire.Program := plan.plan.applied input

end CheckedPlan

structure CheckedInput where
  plan : CheckedPlan
  input : Word

def CheckedInput.program (value : CheckedInput) : Wire.Program := value.plan.program value.input

/-! Plan JSON, with `runtime-memory-values`' encoding of operands, indices,
variables and actions. Every decoder is strict and the decoded plan must
re-encode to the saved JSON. -/

private def foldName : Fold → String
  | .add => "add"
  | .xor => "xor"

private def foldOf (text : String) : Except String Fold :=
  match text with
  | "add" => .ok .add
  | "xor" => .ok .xor
  | _ => .error "unknown memory call fold"

def paramOf (text : String) : Except String Param :=
  match text with
  | "bytes" => .ok .bytes
  | "slice" => .ok .slice
  | "generic" => .ok .generic
  | "array" => .ok .array
  | "pair" => .ok .pair
  | "sum" => .ok .sum
  | "enum" => .ok .enum
  | _ => .error "unknown memory call parameter"

def obsOf (text : String) : Except String Obs :=
  match text with
  | "length" => .ok .length
  | "word" => .ok .word
  | "byte" => .ok .byte
  | "hash" => .ok .hash
  | "element" => .ok .element
  | _ => .error "unknown memory call observation"

def helperJson (helper : Helper) : Json :=
  let fields : List (String × Json) := match helper.kind with
    | .read obs fold => [("kind", toJson "read"), ("obs", toJson obs.name), ("fold", toJson (foldName fold))]
    | .write width => [("kind", toJson "write"), ("width", toJson width.name)]
    | .view start => [("kind", toJson "view"), ("start", toJson start)]
    | .copy => [("kind", toJson "copy")]
    | .call callee constant => [("kind", toJson "call"), ("callee", toJson callee), ("constant", toJson constant)]
    | .pack constant => [("kind", toJson "pack"), ("constant", toJson constant)]
    | .take obs fold written => [("kind", toJson "take"), ("obs", toJson obs.name), ("fold", toJson (foldName fold)),
        ("written", toJson written)]
  Json.mkObj ([("param", toJson helper.param.name)] ++ fields)

def argJson (arg : Arg) : Json := toJson arg.name

def datumJson : Datum → Json
  | .pair ref word => Json.mkObj [("datum", toJson "pair"), ("value", MemoryValues.refJson ref),
      ("word", MemoryValues.operandJson word)]
  | .inl ref => Json.mkObj [("datum", toJson "inl"), ("value", MemoryValues.refJson ref)]
  | .inr word => Json.mkObj [("datum", toJson "inr"), ("word", MemoryValues.operandJson word)]
  | .first ref word => Json.mkObj [("datum", toJson "enum0"), ("value", MemoryValues.refJson ref),
      ("word", MemoryValues.operandJson word)]
  | .second word => Json.mkObj [("datum", toJson "enum1"), ("word", MemoryValues.operandJson word)]

def stepJson : Step → Json
  | .action single => Json.mkObj [("action", MemoryValues.actionJson single)]
  | .call helper arg index word form fold constant => Json.mkObj [("call", Json.mkObj [
      ("helper", toJson helper), ("arg", argJson arg), ("index", MemoryValues.indexJson index),
      ("word", MemoryValues.operandJson word),
      ("form", toJson (match form with
        | .direct => "direct"
        | .value => "value")), ("fold", toJson (foldName fold)), ("constant", toJson constant)])]
  | .data datum => Json.mkObj [("data", datumJson datum)]
  | .closure ref obs => Json.mkObj [("closure", Json.mkObj [("value", MemoryValues.refJson ref), ("obs", toJson obs.name)])]
  | .apply number index fold constant => Json.mkObj [("apply", Json.mkObj [("closure", toJson number),
      ("index", MemoryValues.indexJson index), ("fold", toJson (foldName fold)), ("constant", toJson constant)])]

def planJson (plan : Plan) : Json := Json.mkObj [
  ("schema", toJson planSchema), ("helpers", .arr (plan.helpers.map helperJson).toArray),
  ("steps", .arr (plan.steps.map stepJson).toArray)]

private def array (json : Json) (key : String) : Except String (List Json) := do
  return (← json.getObjValAs? (Array Json) key).toList

def helperOf (json : Json) : Except String Helper := do
  let param ← paramOf (← json.getObjValAs? String "param")
  let kind ← match ← json.getObjValAs? String "kind" with
    | "read" => pure (Kind.read (← obsOf (← json.getObjValAs? String "obs")) (← foldOf (← json.getObjValAs? String "fold")))
    | "write" =>
        match ← json.getObjValAs? String "width" with
        | "word" => pure (Kind.write .word)
        | "byte" => pure (Kind.write .byte)
        | _ => throw "unknown memory call write width"
    | "view" => pure (Kind.view (← json.getObjValAs? Nat "start"))
    | "copy" => pure Kind.copy
    | "call" => pure (Kind.call (← json.getObjValAs? Nat "callee") (← json.getObjValAs? Nat "constant"))
    | "pack" => pure (Kind.pack (← json.getObjValAs? Nat "constant"))
    | "take" => pure (Kind.take (← obsOf (← json.getObjValAs? String "obs")) (← foldOf (← json.getObjValAs? String "fold"))
        (← json.getObjValAs? Bool "written"))
    | _ => throw "unknown memory call helper kind"
  return {param, kind}

def argOf (json : Json) : Except String Arg := do
  let text ← json.getStr?
  let number := fun (head : String) => do
    let digits := (text.drop head.length).toString
    let some value := digits.toNat? | throw "unknown memory call argument"
    unless toString value = digits do throw "noncanonical memory call argument"
    return value
  if text.startsWith "sc_t" then return .pair (← number "sc_t")
  else if text.startsWith "sc_u" then return .sum (← number "sc_u")
  else if text.startsWith "sc_e" then return .enum (← number "sc_e")
  else return .value (← MemoryValues.refOf json)

def datumOf (json : Json) : Except String Datum := do
  match ← json.getObjValAs? String "datum" with
  | "pair" => return .pair (← MemoryValues.refOf (← json.getObjVal? "value")) (← MemoryValues.operandOf (← json.getObjVal? "word"))
  | "inl" => return .inl (← MemoryValues.refOf (← json.getObjVal? "value"))
  | "inr" => return .inr (← MemoryValues.operandOf (← json.getObjVal? "word"))
  | "enum0" => return .first (← MemoryValues.refOf (← json.getObjVal? "value")) (← MemoryValues.operandOf (← json.getObjVal? "word"))
  | "enum1" => return .second (← MemoryValues.operandOf (← json.getObjVal? "word"))
  | _ => throw "unknown memory call datum"

def stepOf (json : Json) : Except String Step := do
  if let .ok single := json.getObjVal? "action" then return .action (← MemoryValues.actionOf single)
  if let .ok call := json.getObjVal? "call" then
    let form ← match ← call.getObjValAs? String "form" with
      | "direct" => pure Form.direct
      | "value" => pure Form.value
      | _ => throw "unknown memory call form"
    return .call (← call.getObjValAs? Nat "helper") (← argOf (← call.getObjVal? "arg"))
      (← MemoryValues.indexOf (← call.getObjVal? "index")) (← MemoryValues.operandOf (← call.getObjVal? "word")) form
      (← foldOf (← call.getObjValAs? String "fold")) (← call.getObjValAs? Nat "constant")
  if let .ok datum := json.getObjVal? "data" then return .data (← datumOf datum)
  if let .ok closure := json.getObjVal? "closure" then
    return .closure (← MemoryValues.refOf (← closure.getObjVal? "value")) (← obsOf (← closure.getObjValAs? String "obs"))
  let applied ← json.getObjVal? "apply"
  return .apply (← applied.getObjValAs? Nat "closure") (← MemoryValues.indexOf (← applied.getObjVal? "index"))
    (← foldOf (← applied.getObjValAs? String "fold")) (← applied.getObjValAs? Nat "constant")

def planOf (json : Json) : Except String Plan := do
  unless (← json.getObjValAs? String "schema") = planSchema do throw "unsupported memory call plan schema"
  return {helpers := ← (← array json "helpers").mapM helperOf, steps := ← (← array json "steps").mapM stepOf}

def checkedPlan (json : Json) : Except String CheckedPlan := do
  let plan ← planOf json
  unless plan.admitted do
    throw "memory call plan is outside the admitted helpers, steps, values, lengths and indices"
  let some checked := CheckedPlan.ofPlan? plan | throw "memory call reference failed the full Core checker"
  unless json == planJson plan do throw "saved memory call plan differs from its canonical checked representation"
  unless plan.nodes ≤ caseLimit do throw "memory call reference exceeds the 5,120-node case limit"
  return checked

def shapesJson (plan : Plan) : Json :=
  Json.mkObj (plan.shapes.map fun (dimension, values) => (dimension, toJson values))

/-- A returned Word, or an out-of-range access. -/
inductive Outcome where
  | word (value : Word)
  | outOfRange
  deriving BEq

def observe (plan : CheckedPlan) (input : Word) (fuel : Nat) : Json :=
  let fields := match (plan.program input).toCore.runStateful fuel with
    | .done (.inLeft _ (.word word)) _ =>
        [("status", toJson "returned"), ("word", toJson (toString word.val))]
    | .done (.inRight _ .unit) _ =>
        [("status", toJson "reverted"), ("output", toJson outOfBounds)]
    | .done value _ =>
        [("status", toJson "invalid-result"), ("detail", toJson (reprStr value))]
    | .outOfFuel _ => [("status", toJson "out-of-fuel")]
    | .fault reason _ =>
        [("status", toJson "core-fault"), ("detail", toJson (reprStr reason))]
  Json.mkObj (("stage", toJson "execution") :: fields)

def makeCase (plan : CheckedPlan) (input : Word) (emitted : EmittedProgram) (origin : Json) (fuel : Nat) : Json :=
  Json.mkObj [
    ("schema", toJson caseSchema), ("memoryCallPlan", planJson plan.plan),
    ("program", Wire.encodeProgram (plan.program input)),
    ("input", toJson (toString input.val)), ("source", toJson emitted.source),
    ("provenance", Json.mkObj [
      ("origin", origin), ("profileVersion", toJson profileVersion),
      ("generatorVersion", toJson callsVersion), ("boundaryVersion", toJson Primitive.boundaryVersion),
      ("emitterVersion", toJson emitterVersion), ("wrapperVersion", toJson wrapperVersion),
      ("features", toJson ([] : List String)), ("referenceNodes", toJson plan.plan.nodes),
      ("memoryCallShapes", shapesJson plan.plan)]),
    ("contract", Enums.contractJson emitted input), ("executionFuel", toJson fuel),
    ("directCore", observe plan input fuel)]

def emitCase (plan : CheckedPlan) (input : Word) (origin : Json) (fuel : Nat) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds profile limit"
  unless plan.plan.nodes ≤ caseLimit do throw "memory call reference exceeds the 5,120-node case limit"
  return makeCase plan input (emit plan.plan) origin fuel

/-- Every origin keeps the canonical reference of its plan at its input. -/
def caseProgram (json : Json) : Except String CheckedInput := do
  unless (← json.getObjValAs? String "schema") = caseSchema do throw "unsupported semantic memory call case schema"
  let plan ← checkedPlan (← json.getObjVal? "memoryCallPlan")
  let input ← Primitive.inputWord (← json.getObjValAs? String "input")
  let program ← (Wire.decodeProgramWithBudget
    {maxDepth := caseLimit, maxNodes := caseLimit, maxIntegerBytes := 4096}
    (← json.getObjVal? "program")).mapError (fun
      | .protocol error => error.toJson.compress
      | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)
  unless Wire.encodeProgram program == Wire.encodeProgram (plan.program input) do
    throw "saved Core program differs from its memory call plan's reference and runtime input"
  return ⟨plan, input⟩

/-- A generation filter on the reference, not a claim that this finite bank
covers a plan. -/
def boundaryOutcomes (plan : CheckedPlan) (fuel : Nat) : Except String (List Outcome) := do
  Primitive.boundaryInputs.mapM fun input =>
    match (plan.program input).toCore.runStateful fuel with
    | .done (.inLeft _ (.word value)) _ => .ok (.word value)
    | .done (.inRight _ .unit) _ => .ok .outOfRange
    | .done _ _ => .error "boundary observation did not return a Word or an out-of-range access"
    | .outOfFuel _ => .error "boundary observation exhausted Core fuel"
    | .fault _ _ => .error "boundary observation produced a Core fault"

/-- At least two outcomes differ; with the identity filter, the Words are not
the inputs. -/
def inputSensitive (plan : CheckedPlan) (fuel : Nat) (acceptance : Acceptance := .profile) :
    Except String Unit := do
  let outcomes ← boundaryOutcomes plan fuel
  unless outcomes.any (fun outcome => outcomes.any (fun other => outcome != other)) do
    throw "all eight boundary inputs had the same outcome"
  let words := outcomes.filterMap fun outcome => match outcome with
    | .word value => some value
    | .outOfRange => none
  if words.length = outcomes.length then acceptance.check Primitive.boundaryInputs words

/-- The seed's plan, its steps dropped from the end while the budgeted
reference exceeds the budget. -/
def generatedPlan (seed : Seed) (nodes : Nat) : Except String CheckedPlan := do
  let plan := (generate seed.toUInt64).fit nodes
  unless plan.budgetNodes ≤ nodes do throw "memory call reference exceeds the node budget"
  let some checked := CheckedPlan.ofPlan? plan
    | throw "memory call reference failed admission or the full Core checker"
  return checked

private def generatedOrigin (seed : Seed) (nodes inputIndex fuel : Nat) : Json := Json.mkObj [
  ("kind", toJson "memory-call-generated"), ("seed", toJson (toString seed.toNat)), ("maxProgramNodes", toJson nodes),
  ("inputIndex", toJson inputIndex), ("validationFuel", toJson fuel)]

/-- Attempt limits count plans; case limits count individual runtime inputs. -/
def generateCases (firstSeed : Seed) (nodes count attempts fuel : Nat)
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
          throw "memory call node budget is outside 256 to 2,048"
        let plan ← generatedPlan seed nodes
        inputSensitive plan fuel acceptance
        return plan
      match result with
      | .error error =>
          let resource := error == "boundary observation exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "memory-call-profile"), ("reason", toJson error),
            ("code", toJson (if resource then "boundary-out-of-fuel"
              else if error == Acceptance.identityReason then "boundary-identity" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok plan =>
          let emitted := emit plan.plan
          for (input, inputIndex) in (inputSelection.inputs Primitive.boundaryInputs seed).zipIdx do
            if cases.size < count then
              let origin := acceptance.record (inputSelection.record (generatedOrigin seed nodes inputIndex fuel))
              cases := cases.push (makeCase plan input emitted origin fuel)
  return Json.mkObj [("schema", toJson corpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

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

def CheckedInput.measure (value : CheckedInput) : Measure := ⟨value.plan.plan.size, value.input.val⟩

structure Reduction (source : CheckedInput) where private mk ::
  candidate : CheckedInput
  strict : candidate.measure.StrictlySmaller source.measure

private def sealReduction (source : CheckedInput) (plan : Plan) (input : Word) : Option (Reduction source) := do
  let plan ← CheckedPlan.ofPlan? plan
  guard (plan.plan.nodes ≤ caseLimit)
  let candidate : CheckedInput := ⟨plan, input⟩
  if strict : candidate.measure.StrictlySmaller source.measure then some ⟨candidate, strict⟩ else none

/-- The plan reductions with the input kept; then the inputs 0, 1 and half the
input with the plan kept. -/
def reductions (source : CheckedInput) : List (Reduction source) := Id.run do
  let input := source.input
  let raw := (planReductions source.plan.plan).map (fun plan => (plan, input)) ++
    [Word.zero, Word.ofNatModulo 1, Word.ofNatModulo (input.val / 2)].map fun value => (source.plan.plan, value)
  let mut seen : List String := []
  let mut result := []
  for (plan, input) in raw do
    if let some reduced := sealReduction source plan input then
      let key := (planJson reduced.candidate.plan.plan).compress ++ toString reduced.candidate.input.val
      if !seen.contains key then
        seen := key :: seen
        result := result ++ [reduced]
  return result

def replayCase (json : Json) (fuel : Nat) : Except String Json := do
  let admitted ← caseProgram json
  let provenance ← json.getObjVal? "provenance"
  for (name, expected) in [
      ("profileVersion", profileVersion), ("generatorVersion", callsVersion),
      ("boundaryVersion", Primitive.boundaryVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do
      throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let emitted := emit admitted.plan.plan
  unless (← json.getObjValAs? String "source") = emitted.source do
    throw "saved source differs from emission of the memory call plan"
  unless (← json.getObjVal? "contract") == Enums.contractJson emitted admitted.input do
    throw "saved contract metadata differs from the memory call wrapper"
  unless (← provenance.getObjVal? "memoryCallShapes") == shapesJson admitted.plan.plan do
    throw "saved memory call shapes differ from the plan"
  let kind ← origin.getObjValAs? String "kind"
  unless kind = "memory-call-generated" || kind = "imported" || kind = "reduced" do
    throw "unsupported memory call case origin"
  if kind = "memory-call-generated" then
    let seedText ← origin.getObjValAs? String "seed"
    let some seed := seedText.toNat? | throw "invalid saved seed"
    unless seed < 2 ^ 64 && toString seed = seedText do throw "noncanonical saved seed"
    let nodes ← origin.getObjValAs? Nat "maxProgramNodes"
    unless minimumNodes ≤ nodes && nodes ≤ maximumNodes do
      throw "saved generation budget exceeds profile limits"
    let plan ← generatedPlan (Seed.ofNat seed) nodes
    unless planJson plan.plan == planJson admitted.plan.plan do
      throw "saved memory call plan differs from its generation seed"
    let inputIndex ← origin.getObjValAs? Nat "inputIndex"
    let inputSelection ← InputSelection.ofOrigin origin
    unless (inputSelection.inputs Primitive.boundaryInputs (Seed.ofNat seed))[inputIndex]? = some admitted.input do
      throw "saved input differs from its boundary index"
    let validationFuel ← origin.getObjValAs? Nat "validationFuel"
    unless validationFuel ≤ 10000000 do throw "saved validation fuel exceeds limit"
    let acceptance ← Acceptance.ofOrigin origin
    inputSensitive plan validationFuel acceptance
    unless origin == acceptance.record (inputSelection.record
        (generatedOrigin (Seed.ofNat seed) nodes inputIndex validationFuel)) do
      throw "generated memory call provenance is not canonical"
  else if kind = "imported" then
    unless origin == Json.mkObj [("kind", toJson "imported")] do
      throw "imported memory call provenance is not canonical"
  else
    let parentPlan ← origin.getObjVal? "parentPlan"
    let parentText ← origin.getObjValAs? String "parentInput"
    let parent : CheckedInput := ⟨← checkedPlan parentPlan, ← Primitive.inputWord parentText⟩
    unless decide (admitted.measure.StrictlySmaller parent.measure) do
      throw "saved memory call reduction is not strictly smaller than its checked parent"
    unless origin == Json.mkObj [("kind", toJson "reduced"), ("parentPlan", parentPlan),
        ("parentInput", toJson parentText)] do
      throw "reduced memory call provenance is not canonical"
  let fresh := makeCase admitted.plan admitted.input emitted origin fuel
  unless (← fresh.getObjVal? "provenance") == provenance do
    throw "memory call provenance contains unexpected fields"
  return fresh

/-- A shrink response stops before its compressed cases would exceed 1.5 MB,
below the campaign's 2 MiB tool-output limit. -/
def shrinkBytes : Nat := 1500000

def shrinkCases (json : Json) (limit fuel : Nat) : Except String Json := do
  let _ ← replayCase json fuel
  let source ← caseProgram json
  let mut cases : Array Json := #[]
  let mut bytes := 0
  for reduced in (reductions source).take limit do
    let origin := Json.mkObj [
      ("kind", toJson "reduced"), ("parentPlan", planJson source.plan.plan),
      ("parentInput", toJson (toString source.input.val))]
    let case ← emitCase reduced.candidate.plan reduced.candidate.input origin fuel
    let size := case.compress.utf8ByteSize
    if bytes + size > shrinkBytes then break
    bytes := bytes + size
    cases := cases.push case
  return Json.mkObj [("schema", toJson corpusSchema), ("cases", .arr cases)]

end Solcore.Synthesis.Source.MemoryCalls
