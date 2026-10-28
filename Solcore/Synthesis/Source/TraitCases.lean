import Solcore.Synthesis.Source.EnumCases
import Solcore.Synthesis.Source.TraitEmitter
import Solcore.Synthesis.Core.TraitShrink

/-! A trait case retains its plan, drawn from the case seed, and the plan's
complete original Core reference at the case input. The reference builds
every instance's closure from the plan, never from the source. Saved
observations never supply the oracle. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.Traits
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.Synthesis.Core.Traits
open Solcore.Synthesis.Core.Enums (Decl LeafOp Form)

def caseSchema : String := "solcore-lean.semantic-trait-case.v1"
def planSchema : String := "solcore-lean.trait-plan.v1"
def profileVersion : String := "runtime-traits-v1/plan-seed-v1"

/-- The decode bound of a saved reference and the largest node budget. -/
def caseLimit : Nat := 4096
def defaultNodes : Nat := 2048
def minimumNodes : Nat := 256

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

/-! Plan JSON. Words are decimal strings; every decoder is strict and the
decoded plan must re-encode to the saved JSON. -/

private def wordJson (value : Nat) : Json := toJson (toString value)

def instJson : Inst → Json
  | .word => toJson "word"
  | .tuple left right => Json.mkObj [("tuple", .arr #[instJson left, instJson right])]
  | .sum left right => Json.mkObj [("sum", .arr #[instJson left, instJson right])]
  | .enum index => Json.mkObj [("enum", toJson index)]
  | .applied index argument => Json.mkObj [("enum", toJson index), ("argument", instJson argument)]

private def fieldsJson (form : Form) (index : Nat) (fields : Array Json) : Json :=
  Json.mkObj [("constructor", toJson index), ("form", toJson form.name), ("fields", .arr fields)]

def valJson : Val → Json
  | .leaf op constant => Json.mkObj [("leaf", toJson op.name), ("constant", wordJson constant)]
  | .tuple left right => Json.mkObj [("tuple", .arr #[valJson left, valJson right])]
  | .inl value => Json.mkObj [("inl", valJson value)]
  | .inr value => Json.mkObj [("inr", valJson value)]
  | .ctor0 index form => fieldsJson form index #[]
  | .ctor1 index field form => fieldsJson form index #[valJson field]
  | .ctor2 index first second form => fieldsJson form index #[valJson first, valJson second]

def stepJson (step : Step) : Json := Json.mkObj [
  ("combine", toJson step.combine.name), ("op", toJson step.op.name), ("constant", wordJson step.constant)]

def headJson : Head → Json
  | .word => toJson "word"
  | .tuple => toJson "tuple"
  | .sum => toJson "sum"
  | .decl index => Json.mkObj [("enum", toJson index)]

def implJson (impl : Impl) : Json := Json.mkObj [
  ("head", headJson impl.head), ("unary", .arr (impl.unary.map stepJson).toArray),
  ("binary", .arr (impl.binary.map stepJson).toArray), ("form", toJson impl.form.name),
  ("mismatch", .arr (impl.mismatch.map wordJson).toArray)]

def helperJson (helper : Helper) : Json := Json.mkObj [
  ("call", toJson helper.call.name), ("method", toJson helper.method.name), ("op", toJson helper.op.name),
  ("constant", wordJson helper.constant)]

def builderJson (builder : Traits.Builder) : Json := Json.mkObj [
  ("offset", toJson builder.offset), ("values", .arr (builder.trees.map valJson).toArray)]

def useJson (use : Use) : Json := Json.mkObj [
  ("method", toJson use.method.name), ("call", toJson use.call.name), ("type", instJson use.type),
  ("shift", toJson use.shift), ("builder", builderJson use.builder)]

def methodsJson (plan : Plan) : Json :=
  toJson ((if plan.unary then ["unary"] else []) ++ (if plan.binary then ["binary"] else []))

def planJson (plan : Plan) : Json := Json.mkObj [
  ("schema", toJson planSchema), ("declarations", .arr (plan.decls.map Enums.declJson).toArray),
  ("methods", methodsJson plan), ("impls", .arr (plan.impls.map implJson).toArray),
  ("helpers", .arr (plan.helpers.map helperJson).toArray), ("uses", .arr (plan.uses.map useJson).toArray)]

private def decodeFuel : Nat := 64

private def wordOf (json : Json) : Except String Nat := do
  let text ← json.getStr?
  let some value := text.toNat? | throw "trait plan constant is not a decimal Word"
  unless toString value = text && value < 2 ^ 256 do throw "trait plan constant is not a canonical decimal Word"
  return value

private def array (json : Json) (key : String) : Except String (List Json) := do
  return (← json.getObjValAs? (Array Json) key).toList

private def pairOf (json : Json) (key : String) : Except String (Option (Json × Json)) := do
  match json.getObjValAs? (Array Json) key with
  | .ok components =>
      let [left, right] := components.toList | throw "trait plan pairs have two components"
      return some (left, right)
  | .error _ => return none

def instOf : Nat → Json → Except String Inst
  | 0, _ => throw "trait plan type is too deep"
  | fuel + 1, json => do
      if let .ok text := json.getStr? then
        if text = "word" then return .word else throw "unknown trait plan type"
      if let some (left, right) := (← pairOf json "tuple") then return .tuple (← instOf fuel left) (← instOf fuel right)
      if let some (left, right) := (← pairOf json "sum") then return .sum (← instOf fuel left) (← instOf fuel right)
      let index ← json.getObjValAs? Nat "enum"
      match json.getObjVal? "argument" with
      | .ok argument => return .applied index (← instOf fuel argument)
      | .error _ => return .enum index

private def opOf (json : Json) : Except String Traits.Op := do
  let some op := Enums.Op.ofString? (← json.getStr?) | throw "unknown trait plan operation"
  return op

def valOf : Nat → Json → Except String Val
  | 0, _ => throw "trait value is too deep"
  | fuel + 1, json => do
      if let .ok op := json.getObjValAs? String "leaf" then
        let some op := LeafOp.ofString? op | throw "unknown trait value leaf"
        return .leaf op (← wordOf (← json.getObjVal? "constant"))
      if let some (left, right) := (← pairOf json "tuple") then return .tuple (← valOf fuel left) (← valOf fuel right)
      if let .ok value := json.getObjVal? "inl" then return .inl (← valOf fuel value)
      if let .ok value := json.getObjVal? "inr" then return .inr (← valOf fuel value)
      let index ← json.getObjValAs? Nat "constructor"
      let some form := Form.ofString? (← json.getObjValAs? String "form") | throw "unknown constructor form"
      match ← array json "fields" with
      | [] => return .ctor0 index form
      | [field] => return .ctor1 index (← valOf fuel field) form
      | [first, second] => return .ctor2 index (← valOf fuel first) (← valOf fuel second) form
      | _ => throw "trait constructor values have at most two fields"

def stepOf (json : Json) : Except String Step := do
  return {combine := ← opOf (← json.getObjVal? "combine"), op := ← opOf (← json.getObjVal? "op"),
          constant := ← wordOf (← json.getObjVal? "constant")}

def headOfJson (json : Json) : Except String Head := do
  if let .ok text := json.getStr? then
    match text with
    | "word" => return .word
    | "tuple" => return .tuple
    | "sum" => return .sum
    | _ => throw "unknown trait impl head"
  return .decl (← json.getObjValAs? Nat "enum")

def implOf (json : Json) : Except String Impl := do
  let some form := MatchForm.ofString? (← json.getObjValAs? String "form") | throw "unknown trait match form"
  return {head := ← headOfJson (← json.getObjVal? "head"), unary := ← (← array json "unary").mapM stepOf,
          binary := ← (← array json "binary").mapM stepOf, form,
          mismatch := ← (← array json "mismatch").mapM wordOf}

def helperOf (json : Json) : Except String Helper := do
  let some call := Call.ofString? (← json.getObjValAs? String "call") | throw "unknown trait helper call"
  let some method := Method.ofString? (← json.getObjValAs? String "method") | throw "unknown trait method"
  return {call, method, op := ← opOf (← json.getObjVal? "op"), constant := ← wordOf (← json.getObjVal? "constant")}

def builderOf (json : Json) : Except String Traits.Builder := do
  return {offset := ← json.getObjValAs? Nat "offset", trees := ← (← array json "values").mapM (valOf decodeFuel)}

def useOf (json : Json) : Except String Use := do
  let some method := Method.ofString? (← json.getObjValAs? String "method") | throw "unknown trait method"
  let some call := Call.ofString? (← json.getObjValAs? String "call") | throw "unknown trait call form"
  return {method, call, type := ← instOf decodeFuel (← json.getObjVal? "type"),
          shift := ← json.getObjValAs? Nat "shift", builder := ← builderOf (← json.getObjVal? "builder")}

def planOf (json : Json) : Except String Plan := do
  unless (← json.getObjValAs? String "schema") = planSchema do throw "unsupported trait plan schema"
  let methods ← (← array json "methods").mapM fun method => method.getStr?
  return {decls := ← (← array json "declarations").mapM Enums.declOf,
          unary := methods.contains "unary", binary := methods.contains "binary",
          impls := ← (← array json "impls").mapM implOf, helpers := ← (← array json "helpers").mapM helperOf,
          uses := ← (← array json "uses").mapM useOf}

def checkedPlan (json : Json) : Except String CheckedPlan := do
  let plan ← planOf json
  unless plan.admitted do
    throw "trait plan is outside the admitted declarations, impls, helpers, uses and builders"
  let some checked := CheckedPlan.ofPlan? plan | throw "trait reference failed the full Core checker"
  unless json == planJson plan do throw "saved trait plan differs from its canonical checked representation"
  unless plan.nodes ≤ caseLimit do throw "trait reference exceeds the 4,096-node case limit"
  return checked

def shapesJson (plan : Plan) : Json :=
  Json.mkObj (plan.shapes.map fun (dimension, values) => (dimension, toJson values))

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

def makeCase (plan : CheckedPlan) (input : Word) (emitted : EmittedProgram) (origin : Json) (fuel : Nat) : Json :=
  Json.mkObj [
    ("schema", toJson caseSchema), ("traitPlan", planJson plan.plan),
    ("program", Wire.encodeProgram (plan.program input)),
    ("input", toJson (toString input.val)), ("source", toJson emitted.source),
    ("provenance", Json.mkObj [
      ("origin", origin), ("profileVersion", toJson profileVersion),
      ("generatorVersion", toJson traitVersion), ("boundaryVersion", toJson Primitive.boundaryVersion),
      ("emitterVersion", toJson emitterVersion), ("wrapperVersion", toJson wrapperVersion),
      ("features", toJson ([] : List String)), ("referenceNodes", toJson plan.plan.nodes),
      ("traitShapes", shapesJson plan.plan)]),
    ("contract", Enums.contractJson emitted input), ("executionFuel", toJson fuel),
    ("directCore", observe plan input fuel)]

def emitCase (plan : CheckedPlan) (input : Word) (origin : Json) (fuel : Nat) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds profile limit"
  unless plan.plan.nodes ≤ caseLimit do throw "trait reference exceeds the 4,096-node case limit"
  return makeCase plan input (emit plan.plan) origin fuel

/-- Every origin keeps the canonical reference of its plan at its input. -/
def caseProgram (json : Json) : Except String CheckedInput := do
  unless (← json.getObjValAs? String "schema") = caseSchema do throw "unsupported semantic trait case schema"
  let plan ← checkedPlan (← json.getObjVal? "traitPlan")
  let input ← Primitive.inputWord (← json.getObjValAs? String "input")
  let program ← (Wire.decodeProgramWithBudget
    {maxDepth := caseLimit, maxNodes := caseLimit, maxIntegerBytes := 4096}
    (← json.getObjVal? "program")).mapError (fun
      | .protocol error => error.toJson.compress
      | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)
  unless Wire.encodeProgram program == Wire.encodeProgram (plan.program input) do
    throw "saved Core program differs from its trait plan's reference and runtime input"
  return ⟨plan, input⟩

/-- A generation filter on the reference, not a claim that this finite bank
covers a plan. -/
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

/-- The seed's plan, its uses dropped from the end while the reference
exceeds the budget. -/
def generatedPlan (seed : Seed) (nodes : Nat) : Except String CheckedPlan := do
  let plan := (generate seed.toUInt64).fit nodes
  unless plan.nodes ≤ nodes do throw "trait reference exceeds the node budget"
  let some checked := CheckedPlan.ofPlan? plan | throw "trait reference failed admission or the full Core checker"
  return checked

private def generatedOrigin (seed : Seed) (nodes inputIndex fuel : Nat) : Json := Json.mkObj [
  ("kind", toJson "trait-generated"), ("seed", toJson (toString seed.toNat)), ("maxProgramNodes", toJson nodes),
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
        unless minimumNodes ≤ nodes && nodes ≤ caseLimit do throw "trait node budget is outside 256 to 4,096"
        let plan ← generatedPlan seed nodes
        inputSensitive plan fuel acceptance
        return plan
      match result with
      | .error error =>
          let resource := error == "boundary observation exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "trait-profile"), ("reason", toJson error),
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

/-- The plan reductions, normalized, with the input kept; then the inputs 0,
1 and half the input with the plan kept. -/
def reductions (source : CheckedInput) : List (Reduction source) := Id.run do
  let input := source.input
  let raw := (planReductions source.plan.plan).map (fun plan => (plan.normalize, input)) ++
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
      ("profileVersion", profileVersion), ("generatorVersion", traitVersion),
      ("boundaryVersion", Primitive.boundaryVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do
      throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let emitted := emit admitted.plan.plan
  unless (← json.getObjValAs? String "source") = emitted.source do
    throw "saved source differs from emission of the trait plan"
  unless (← json.getObjVal? "contract") == Enums.contractJson emitted admitted.input do
    throw "saved contract metadata differs from the trait wrapper"
  unless (← provenance.getObjVal? "traitShapes") == shapesJson admitted.plan.plan do
    throw "saved trait shapes differ from the plan"
  let kind ← origin.getObjValAs? String "kind"
  unless kind = "trait-generated" || kind = "imported" || kind = "reduced" do
    throw "unsupported trait case origin"
  if kind = "trait-generated" then
    let seedText ← origin.getObjValAs? String "seed"
    let some seed := seedText.toNat? | throw "invalid saved seed"
    unless seed < 2 ^ 64 && toString seed = seedText do throw "noncanonical saved seed"
    let nodes ← origin.getObjValAs? Nat "maxProgramNodes"
    unless minimumNodes ≤ nodes && nodes ≤ caseLimit do
      throw "saved generation budget exceeds profile limits"
    let plan ← generatedPlan (Seed.ofNat seed) nodes
    unless planJson plan.plan == planJson admitted.plan.plan do
      throw "saved trait plan differs from its generation seed"
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
      throw "generated trait provenance is not canonical"
  else if kind = "imported" then
    unless origin == Json.mkObj [("kind", toJson "imported")] do
      throw "imported trait provenance is not canonical"
  else
    let parentPlan ← origin.getObjVal? "parentPlan"
    let parentText ← origin.getObjValAs? String "parentInput"
    let parent : CheckedInput := ⟨← checkedPlan parentPlan, ← Primitive.inputWord parentText⟩
    unless decide (admitted.measure.StrictlySmaller parent.measure) do
      throw "saved trait reduction is not strictly smaller than its checked parent"
    unless origin == Json.mkObj [("kind", toJson "reduced"), ("parentPlan", parentPlan),
        ("parentInput", toJson parentText)] do
      throw "reduced trait provenance is not canonical"
  let fresh := makeCase admitted.plan admitted.input emitted origin fuel
  unless (← fresh.getObjVal? "provenance") == provenance do
    throw "trait provenance contains unexpected fields"
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

end Solcore.Synthesis.Source.Traits
