import Solcore.Synthesis.Source.EnumCases
import Solcore.Synthesis.Source.MemoryValuesEmitter
import Solcore.Synthesis.Core.MemoryValuesShrink

/-! A memory value case retains its plan, drawn from the case seed, and the
plan's complete original Core reference at the case input. The reference
models every value as its byte list, never std's layout, and is built from
the plan, never from the source. Its right injection is an out-of-range
access, observed as std's `OutOfBounds()` revert data. Saved observations
never supply the oracle. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.MemoryValues
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.Synthesis.Core.MemoryValues

def caseSchema : String := "solcore-lean.semantic-memory-value-case.v1"
def planSchema : String := "solcore-lean.memory-value-plan.v1"
def profileVersion : String := "runtime-memory-values-v1/plan-seed-v1"

/-- std's `OutOfBounds()` selector, the whole revert data of `slice_`,
`truncate` and `IndexAccess` past a value's end. -/
def outOfBounds : String := "0xb4120f14"

/-- The node budget, which bounds the applied reference without the hash
closure, and the decode bound of a saved reference: the largest budget and
the closure. -/
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

/-! Plan JSON. Every decoder is strict and the decoded plan must re-encode to
the saved JSON. -/

def operandJson : Operand → Json
  | .input => Json.mkObj [("operand", toJson "input")]
  | .add constant => Json.mkObj [("operand", toJson "add"), ("constant", toJson constant)]
  | .mul constant => Json.mkObj [("operand", toJson "mul"), ("constant", toJson constant)]
  | .xor constant => Json.mkObj [("operand", toJson "xor"), ("constant", toJson constant)]
  | .acc => Json.mkObj [("operand", toJson "acc")]
  | .counter => Json.mkObj [("operand", toJson "counter")]

def indexJson : Index → Json
  | .literal value => Json.mkObj [("index", toJson "literal"), ("value", toJson value)]
  | .input shift modulus => Json.mkObj [("index", toJson "input"), ("shift", toJson shift), ("modulus", toJson modulus)]
  | .counter scale offset => Json.mkObj [("index", toJson "counter"), ("scale", toJson scale), ("offset", toJson offset)]

def refJson (ref : Ref) : Json := toJson (refName ref)

def partJson : Part → Json
  | .word operand => Json.mkObj [("part", toJson "word"), ("operand", operandJson operand)]
  | .zeros count => Json.mkObj [("part", toJson "zeros"), ("count", toJson count)]
  | .value ref => Json.mkObj [("part", toJson "value"), ("value", refJson ref)]

def accessJson : Access → Json
  | .length => Json.mkObj [("access", toJson "length")]
  | .word index => Json.mkObj [("access", toJson "word"), ("index", indexJson index)]
  | .byte index => Json.mkObj [("access", toJson "byte"), ("index", indexJson index)]
  | .hash => Json.mkObj [("access", toJson "hash")]
  | .element index get => Json.mkObj [("access", toJson "element"), ("index", indexJson index),
      ("form", toJson (if get then "get" else "index"))]

def actionJson : Action → Json
  | .bytes (.toBytes part) => Json.mkObj [("kind", toJson "bytes"), ("build", toJson "to_bytes"),
      ("parts", .arr #[partJson part])]
  | .bytes (.concat left right) => Json.mkObj [("kind", toJson "bytes"), ("build", toJson "concat"),
      ("parts", .arr #[partJson left, partJson right])]
  | .slice source cut =>
      let fields := match cut with
        | .drop start => [("cut", toJson "drop"), ("start", toJson start)]
        | .take kept => [("cut", toJson "take"), ("length", toJson kept)]
        | .window start kept => [("cut", toJson "window"), ("start", toJson start), ("length", toJson kept)]
      Json.mkObj ([("kind", toJson "slice"), ("source", refJson source)] ++ fields)
  | .alias source => Json.mkObj [("kind", toJson "alias"), ("source", refJson source)]
  | .array allocated elements => Json.mkObj [("kind", toJson "array"),
      ("form", toJson (if allocated then "allocated" else "literal")),
      ("elements", .arr (elements.map operandJson).toArray)]
  | .write target index value width form => Json.mkObj [("kind", toJson "write"), ("target", refJson target),
      ("index", indexJson index), ("value", operandJson value), ("width", toJson width.name), ("form", toJson form.name)]
  | .observe fold constant value access => Json.mkObj [("kind", toJson "observe"),
      ("fold", toJson (match fold with
        | .add => "add"
        | .xor => "xor")), ("constant", toJson constant), ("value", refJson value), ("access", accessJson access)]

def loopJson : MemoryValues.Loop → Json
  | .single mask => Json.mkObj [("form", toJson "single"), ("mask", toJson mask)]
  | .nested outer bound inner => Json.mkObj [("form", toJson "nested"), ("outer", toJson outer),
      ("bound", toJson (match bound with
        | .input => "input"
        | .counter => "counter")), ("inner", toJson inner)]

def stepJson : Step → Json
  | .action action => Json.mkObj [("action", actionJson action)]
  | .loop shape body => Json.mkObj [("loop", loopJson shape), ("body", .arr (body.map actionJson).toArray)]

def planJson (plan : Plan) : Json := Json.mkObj [
  ("schema", toJson planSchema), ("steps", .arr (plan.steps.map stepJson).toArray)]

private def array (json : Json) (key : String) : Except String (List Json) := do
  return (← json.getObjValAs? (Array Json) key).toList

def operandOf (json : Json) : Except String Operand := do
  match ← json.getObjValAs? String "operand" with
  | "input" => return .input
  | "add" => return .add (← json.getObjValAs? Nat "constant")
  | "mul" => return .mul (← json.getObjValAs? Nat "constant")
  | "xor" => return .xor (← json.getObjValAs? Nat "constant")
  | "acc" => return .acc
  | "counter" => return .counter
  | _ => throw "unknown memory value operand"

def indexOf (json : Json) : Except String Index := do
  match ← json.getObjValAs? String "index" with
  | "literal" => return .literal (← json.getObjValAs? Nat "value")
  | "input" => return .input (← json.getObjValAs? Nat "shift") (← json.getObjValAs? Nat "modulus")
  | "counter" => return .counter (← json.getObjValAs? Nat "scale") (← json.getObjValAs? Nat "offset")
  | _ => throw "unknown memory value index"

def refOf (json : Json) : Except String Ref := do
  let text ← json.getStr?
  let number := fun (head : String) => do
    let digits := (text.drop head.length).toString
    let some value := digits.toNat? | throw "unknown memory value variable"
    unless toString value = digits do throw "noncanonical memory value variable"
    return value
  if text.startsWith "sc_b" then return .bytes (← number "sc_b")
  else if text.startsWith "sc_s" then return .slice (← number "sc_s")
  else if text.startsWith "sc_a" then return .array (← number "sc_a")
  else throw "unknown memory value variable"

def partOf (json : Json) : Except String Part := do
  match ← json.getObjValAs? String "part" with
  | "word" => return .word (← operandOf (← json.getObjVal? "operand"))
  | "zeros" => return .zeros (← json.getObjValAs? Nat "count")
  | "value" => return .value (← refOf (← json.getObjVal? "value"))
  | _ => throw "unknown memory value part"

def accessOf (json : Json) : Except String Access := do
  match ← json.getObjValAs? String "access" with
  | "length" => return .length
  | "word" => return .word (← indexOf (← json.getObjVal? "index"))
  | "byte" => return .byte (← indexOf (← json.getObjVal? "index"))
  | "hash" => return .hash
  | "element" =>
      let get ← match ← json.getObjValAs? String "form" with
        | "get" => pure true
        | "index" => pure false
        | _ => throw "unknown memory value element form"
      return .element (← indexOf (← json.getObjVal? "index")) get
  | _ => throw "unknown memory value access"

def actionOf (json : Json) : Except String Action := do
  match ← json.getObjValAs? String "kind" with
  | "bytes" =>
      let parts ← (← array json "parts").mapM partOf
      match ← json.getObjValAs? String "build", parts with
      | "to_bytes", [part] => return .bytes (.toBytes part)
      | "concat", [left, right] => return .bytes (.concat left right)
      | _, _ => throw "unknown memory value build"
  | "slice" =>
      let source ← refOf (← json.getObjVal? "source")
      match ← json.getObjValAs? String "cut" with
      | "drop" => return .slice source (.drop (← json.getObjValAs? Nat "start"))
      | "take" => return .slice source (.take (← json.getObjValAs? Nat "length"))
      | "window" => return .slice source (.window (← json.getObjValAs? Nat "start") (← json.getObjValAs? Nat "length"))
      | _ => throw "unknown memory value cut"
  | "alias" => return .alias (← refOf (← json.getObjVal? "source"))
  | "array" =>
      let allocated ← match ← json.getObjValAs? String "form" with
        | "allocated" => pure true
        | "literal" => pure false
        | _ => throw "unknown memory value array form"
      return .array allocated (← (← array json "elements").mapM operandOf)
  | "write" =>
      let width ← match ← json.getObjValAs? String "width" with
        | "word" => pure Width.word
        | "byte" => pure Width.byte
        | _ => throw "unknown memory value write width"
      let form ← match ← json.getObjValAs? String "form" with
        | "inline" => pure Form.inline
        | "helper" => pure Form.helper
        | _ => throw "unknown memory value write form"
      return .write (← refOf (← json.getObjVal? "target")) (← indexOf (← json.getObjVal? "index"))
        (← operandOf (← json.getObjVal? "value")) width form
  | "observe" =>
      let fold ← match ← json.getObjValAs? String "fold" with
        | "add" => pure Fold.add
        | "xor" => pure Fold.xor
        | _ => throw "unknown memory value fold"
      return .observe fold (← json.getObjValAs? Nat "constant") (← refOf (← json.getObjVal? "value"))
        (← accessOf (← json.getObjVal? "access"))
  | _ => throw "unknown memory value action"

def loopOf (json : Json) : Except String MemoryValues.Loop := do
  match ← json.getObjValAs? String "form" with
  | "single" => return .single (← json.getObjValAs? Nat "mask")
  | "nested" =>
      let bound ← match ← json.getObjValAs? String "bound" with
        | "input" => pure Bound.input
        | "counter" => pure Bound.counter
        | _ => throw "unknown memory value loop bound"
      return .nested (← json.getObjValAs? Nat "outer") bound (← json.getObjValAs? Nat "inner")
  | _ => throw "unknown memory value loop form"

def stepOf (json : Json) : Except String Step := do
  match json.getObjVal? "action" with
  | .ok action => return .action (← actionOf action)
  | .error _ => return .loop (← loopOf (← json.getObjVal? "loop")) (← (← array json "body").mapM actionOf)

def planOf (json : Json) : Except String Plan := do
  unless (← json.getObjValAs? String "schema") = planSchema do throw "unsupported memory value plan schema"
  return {steps := ← (← array json "steps").mapM stepOf}

def checkedPlan (json : Json) : Except String CheckedPlan := do
  let plan ← planOf json
  unless plan.admitted do
    throw "memory value plan is outside the admitted steps, values, lengths, indices and loops"
  let some checked := CheckedPlan.ofPlan? plan | throw "memory value reference failed the full Core checker"
  unless json == planJson plan do throw "saved memory value plan differs from its canonical checked representation"
  unless plan.nodes ≤ caseLimit do throw "memory value reference exceeds the 5,120-node case limit"
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
    ("schema", toJson caseSchema), ("memoryValuePlan", planJson plan.plan),
    ("program", Wire.encodeProgram (plan.program input)),
    ("input", toJson (toString input.val)), ("source", toJson emitted.source),
    ("provenance", Json.mkObj [
      ("origin", origin), ("profileVersion", toJson profileVersion),
      ("generatorVersion", toJson memoryVersion), ("boundaryVersion", toJson Primitive.boundaryVersion),
      ("emitterVersion", toJson emitterVersion), ("wrapperVersion", toJson wrapperVersion),
      ("features", toJson ([] : List String)), ("referenceNodes", toJson plan.plan.nodes),
      ("memoryValueShapes", shapesJson plan.plan)]),
    ("contract", Enums.contractJson emitted input), ("executionFuel", toJson fuel),
    ("directCore", observe plan input fuel)]

def emitCase (plan : CheckedPlan) (input : Word) (origin : Json) (fuel : Nat) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds profile limit"
  unless plan.plan.nodes ≤ caseLimit do throw "memory value reference exceeds the 5,120-node case limit"
  return makeCase plan input (emit plan.plan) origin fuel

/-- Every origin keeps the canonical reference of its plan at its input. -/
def caseProgram (json : Json) : Except String CheckedInput := do
  unless (← json.getObjValAs? String "schema") = caseSchema do throw "unsupported semantic memory value case schema"
  let plan ← checkedPlan (← json.getObjVal? "memoryValuePlan")
  let input ← Primitive.inputWord (← json.getObjValAs? String "input")
  let program ← (Wire.decodeProgramWithBudget
    {maxDepth := caseLimit, maxNodes := caseLimit, maxIntegerBytes := 4096}
    (← json.getObjVal? "program")).mapError (fun
      | .protocol error => error.toJson.compress
      | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)
  unless Wire.encodeProgram program == Wire.encodeProgram (plan.program input) do
    throw "saved Core program differs from its memory value plan's reference and runtime input"
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
  unless plan.budgetNodes ≤ nodes do throw "memory value reference exceeds the node budget"
  let some checked := CheckedPlan.ofPlan? plan
    | throw "memory value reference failed admission or the full Core checker"
  return checked

private def generatedOrigin (seed : Seed) (nodes inputIndex fuel : Nat) : Json := Json.mkObj [
  ("kind", toJson "memory-generated"), ("seed", toJson (toString seed.toNat)), ("maxProgramNodes", toJson nodes),
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
          throw "memory value node budget is outside 256 to 2,048"
        let plan ← generatedPlan seed nodes
        inputSensitive plan fuel acceptance
        return plan
      match result with
      | .error error =>
          let resource := error == "boundary observation exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "memory-profile"), ("reason", toJson error),
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
      ("profileVersion", profileVersion), ("generatorVersion", memoryVersion),
      ("boundaryVersion", Primitive.boundaryVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do
      throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let emitted := emit admitted.plan.plan
  unless (← json.getObjValAs? String "source") = emitted.source do
    throw "saved source differs from emission of the memory value plan"
  unless (← json.getObjVal? "contract") == Enums.contractJson emitted admitted.input do
    throw "saved contract metadata differs from the memory value wrapper"
  unless (← provenance.getObjVal? "memoryValueShapes") == shapesJson admitted.plan.plan do
    throw "saved memory value shapes differ from the plan"
  let kind ← origin.getObjValAs? String "kind"
  unless kind = "memory-generated" || kind = "imported" || kind = "reduced" do
    throw "unsupported memory value case origin"
  if kind = "memory-generated" then
    let seedText ← origin.getObjValAs? String "seed"
    let some seed := seedText.toNat? | throw "invalid saved seed"
    unless seed < 2 ^ 64 && toString seed = seedText do throw "noncanonical saved seed"
    let nodes ← origin.getObjValAs? Nat "maxProgramNodes"
    unless minimumNodes ≤ nodes && nodes ≤ maximumNodes do
      throw "saved generation budget exceeds profile limits"
    let plan ← generatedPlan (Seed.ofNat seed) nodes
    unless planJson plan.plan == planJson admitted.plan.plan do
      throw "saved memory value plan differs from its generation seed"
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
      throw "generated memory value provenance is not canonical"
  else if kind = "imported" then
    unless origin == Json.mkObj [("kind", toJson "imported")] do
      throw "imported memory value provenance is not canonical"
  else
    let parentPlan ← origin.getObjVal? "parentPlan"
    let parentText ← origin.getObjValAs? String "parentInput"
    let parent : CheckedInput := ⟨← checkedPlan parentPlan, ← Primitive.inputWord parentText⟩
    unless decide (admitted.measure.StrictlySmaller parent.measure) do
      throw "saved memory value reduction is not strictly smaller than its checked parent"
    unless origin == Json.mkObj [("kind", toJson "reduced"), ("parentPlan", parentPlan),
        ("parentInput", toJson parentText)] do
      throw "reduced memory value provenance is not canonical"
  let fresh := makeCase admitted.plan admitted.input emitted origin fuel
  unless (← fresh.getObjVal? "provenance") == provenance do
    throw "memory value provenance contains unexpected fields"
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

end Solcore.Synthesis.Source.MemoryValues
