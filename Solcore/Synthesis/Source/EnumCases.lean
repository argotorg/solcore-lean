import Solcore.Synthesis.Source.PrimitiveCases
import Solcore.Synthesis.Source.EnumEmitter
import Solcore.Synthesis.Core.EnumShrink

/-! An enum case retains its plan, drawn from the case seed, and the plan's
complete original Core reference at the case input. The reference compiles
every match itself from the plan, never from the source. Saved observations
never supply the oracle. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.Enums
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.Synthesis.Core.Enums

def caseSchema : String := "solcore-lean.semantic-enum-case.v1"
def planSchema : String := "solcore-lean.enum-plan.v1"
def profileVersion : String := "runtime-enums-v1/plan-seed-v1"

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

def tyJson : Enums.Ty → Json
  | .word => toJson "word"
  | .param => toJson "param"
  | .tuple left right => Json.mkObj [("tuple", .arr #[tyJson left, tyJson right])]
  | .enum index => Json.mkObj [("enum", toJson index)]
  | .applied index argument => Json.mkObj [("enum", toJson index), ("argument", tyJson argument)]

def declJson (decl : Decl) : Json := Json.mkObj [
  ("generic", toJson decl.generic), ("sameName", toJson decl.sameName),
  ("constructors", .arr (decl.constructors.map fun fields => Json.arr (fields.map tyJson).toArray).toArray)]

def patJson : Pat → Json
  | .wild => toJson "_"
  | .var name => Json.mkObj [("var", toJson (names.getD name "_"))]
  | .tuple left right => Json.mkObj [("tuple", .arr #[patJson left, patJson right])]
  | .ctor0 index form => Json.mkObj [("constructor", toJson index), ("form", toJson form.name), ("fields", .arr #[])]
  | .ctor1 index field form =>
      Json.mkObj [("constructor", toJson index), ("form", toJson form.name), ("fields", .arr #[patJson field])]
  | .ctor2 index first second form => Json.mkObj [("constructor", toJson index), ("form", toJson form.name),
      ("fields", .arr #[patJson first, patJson second])]

def valueJson : Enums.Value → Json
  | .leaf op constant => Json.mkObj [("leaf", toJson op.name), ("constant", wordJson constant)]
  | .tuple left right => Json.mkObj [("tuple", .arr #[valueJson left, valueJson right])]
  | .ctor0 index form => Json.mkObj [("constructor", toJson index), ("form", toJson form.name), ("fields", .arr #[])]
  | .ctor1 index field form =>
      Json.mkObj [("constructor", toJson index), ("form", toJson form.name), ("fields", .arr #[valueJson field])]
  | .ctor2 index first second form => Json.mkObj [("constructor", toJson index), ("form", toJson form.name),
      ("fields", .arr #[valueJson first, valueJson second])]

def termJson : Enums.Term → Json
  | .name name => Json.mkObj [("name", toJson (names.getD name "_"))]
  | .constant value => Json.mkObj [("constant", wordJson value)]

def bodyJson (body : Body) : Json := Json.mkObj [
  ("terms", .arr ((body.first :: body.rest.map Prod.snd).map termJson).toArray),
  ("operations", .arr (body.rest.map fun (op, _) => toJson op.name).toArray),
  ("constant", wordJson body.constant)]

private def patternsJson (patterns : List Pat) : Json := .arr (patterns.map patJson).toArray

def armJson (arm : Arm) : Json := match arm.body with
  | .expr body => Json.mkObj [("patterns", patternsJson arm.patterns), ("return", bodyJson body)]
  | .nested scrutinee arms => Json.mkObj [("patterns", patternsJson arm.patterns),
      ("match", toJson (names.getD scrutinee "_")),
      ("arms", .arr (arms.map fun inner => Json.mkObj [("patterns", patternsJson inner.patterns),
        ("return", bodyJson inner.body)]).toArray)]

def builderJson (builder : Builder) : Json := Json.mkObj [
  ("offset", toJson builder.offset), ("values", .arr (builder.trees.map valueJson).toArray)]

def viewJson (view : View) : Json := Json.mkObj [
  ("kind", toJson view.kind.name), ("scrutinees", .arr (view.scrutinees.map tyJson).toArray),
  ("instances", .arr (view.instances.map tyJson).toArray), ("arms", .arr (view.arms.map armJson).toArray),
  ("builders", .arr (view.builders.map builderJson).toArray), ("wordOffset", wordJson view.wordOffset)]

def planJson (plan : Plan) : Json := Json.mkObj [
  ("schema", toJson planSchema), ("declarations", .arr (plan.decls.map declJson).toArray),
  ("views", .arr (plan.views.map viewJson).toArray)]

private def decodeFuel : Nat := 64

private def wordOf (json : Json) : Except String Nat := do
  let text ← json.getStr?
  let some value := text.toNat? | throw "enum plan constant is not a decimal Word"
  unless toString value = text && value < 2 ^ 256 do throw "enum plan constant is not a canonical decimal Word"
  return value

private def nameOf (json : Json) : Except String Nat := do
  let text ← json.getStr?
  let some index := names.idxOf? text | throw "unknown enum pattern variable"
  return index

private def array (json : Json) (key : String) : Except String (List Json) := do
  return (← json.getObjValAs? (Array Json) key).toList

def tyOf : Nat → Json → Except String Enums.Ty
  | 0, _ => throw "enum plan type is too deep"
  | fuel + 1, json => do
      if let .ok text := json.getStr? then
        match text with
        | "word" => return .word
        | "param" => return .param
        | _ => throw "unknown enum plan type"
      if let .ok components := json.getObjValAs? (Array Json) "tuple" then
        let [left, right] := components.toList | throw "enum plan tuple types have two components"
        return .tuple (← tyOf fuel left) (← tyOf fuel right)
      let index ← json.getObjValAs? Nat "enum"
      match json.getObjVal? "argument" with
      | .ok argument => return .applied index (← tyOf fuel argument)
      | .error _ => return .enum index

private def formOf (json : Json) : Except String Form := do
  let some form := Form.ofString? (← json.getObjValAs? String "form") | throw "unknown constructor form"
  return form

def patOf : Nat → Json → Except String Pat
  | 0, _ => throw "enum pattern is too deep"
  | fuel + 1, json => do
      if json == toJson "_" then return .wild
      if let .ok name := json.getObjVal? "var" then return .var (← nameOf name)
      if let .ok components := json.getObjValAs? (Array Json) "tuple" then
        let [left, right] := components.toList | throw "enum tuple patterns have two components"
        return .tuple (← patOf fuel left) (← patOf fuel right)
      let index ← json.getObjValAs? Nat "constructor"
      let form ← formOf json
      match ← array json "fields" with
      | [] => return .ctor0 index form
      | [field] => return .ctor1 index (← patOf fuel field) form
      | [first, second] => return .ctor2 index (← patOf fuel first) (← patOf fuel second) form
      | _ => throw "enum constructor patterns have at most two fields"

def valueOf : Nat → Json → Except String Enums.Value
  | 0, _ => throw "enum value is too deep"
  | fuel + 1, json => do
      if let .ok op := json.getObjValAs? String "leaf" then
        let some op := LeafOp.ofString? op | throw "unknown enum value leaf"
        return .leaf op (← wordOf (← json.getObjVal? "constant"))
      if let .ok components := json.getObjValAs? (Array Json) "tuple" then
        let [left, right] := components.toList | throw "enum tuple values have two components"
        return .tuple (← valueOf fuel left) (← valueOf fuel right)
      let index ← json.getObjValAs? Nat "constructor"
      let form ← formOf json
      match ← array json "fields" with
      | [] => return .ctor0 index form
      | [field] => return .ctor1 index (← valueOf fuel field) form
      | [first, second] => return .ctor2 index (← valueOf fuel first) (← valueOf fuel second) form
      | _ => throw "enum constructor values have at most two fields"

private def termOf (json : Json) : Except String Enums.Term := do
  if let .ok name := json.getObjVal? "name" then return .name (← nameOf name)
  return .constant (← wordOf (← json.getObjVal? "constant"))

def bodyOf (json : Json) : Except String Body := do
  let terms ← (← array json "terms").mapM termOf
  let operations ← (← array json "operations").mapM fun operation => do
    let some op := Op.ofString? (← operation.getStr?) | throw "unknown enum body operation"
    return op
  let first :: rest := terms | throw "an enum body has a term"
  unless operations.length = rest.length do throw "an enum body has one operation per later term"
  return {first, rest := operations.zip rest, constant := ← wordOf (← json.getObjVal? "constant")}

private def patternsOf (json : Json) : Except String (List Pat) := do
  (← array json "patterns").mapM (patOf decodeFuel)

def armOf (json : Json) : Except String Arm := do
  let patterns ← patternsOf json
  match json.getObjVal? "match" with
  | .ok scrutinee =>
      let arms ← (← array json "arms").mapM fun inner => do
        return ({patterns := ← patternsOf inner, body := ← bodyOf (← inner.getObjVal? "return")} : InnerArm)
      return {patterns, body := .nested (← nameOf scrutinee) arms}
  | .error _ => return {patterns, body := .expr (← bodyOf (← json.getObjVal? "return"))}

def builderOf (json : Json) : Except String Builder := do
  let trees ← (← array json "values").mapM (valueOf decodeFuel)
  return {offset := ← json.getObjValAs? Nat "offset", trees}

def viewOf (json : Json) : Except String View := do
  let some kind := Kind.ofString? (← json.getObjValAs? String "kind") | throw "unknown enum view kind"
  let scrutinees ← (← array json "scrutinees").mapM (tyOf decodeFuel)
  let instances ← (← array json "instances").mapM (tyOf decodeFuel)
  let arms ← (← array json "arms").mapM armOf
  let builders ← (← array json "builders").mapM builderOf
  return {kind, scrutinees, instances, arms, builders, wordOffset := ← wordOf (← json.getObjVal? "wordOffset")}

def declOf (json : Json) : Except String Decl := do
  let constructors ← (← array json "constructors").mapM fun fields => do
    let fields ← fields.getArr?
    fields.toList.mapM (tyOf decodeFuel)
  return {generic := ← json.getObjValAs? Bool "generic", sameName := ← json.getObjValAs? Bool "sameName",
          constructors}

def planOf (json : Json) : Except String Plan := do
  unless (← json.getObjValAs? String "schema") = planSchema do throw "unsupported enum plan schema"
  let decls ← (← array json "declarations").mapM declOf
  return {decls, views := ← (← array json "views").mapM viewOf}

def checkedPlan (json : Json) : Except String CheckedPlan := do
  let plan ← planOf json
  unless plan.admitted do
    throw "enum plan is outside the admitted declarations, views, arms, patterns, bodies and builders"
  let some checked := CheckedPlan.ofPlan? plan | throw "enum reference failed the full Core checker"
  unless json == planJson plan do throw "saved enum plan differs from its canonical checked representation"
  unless plan.nodes ≤ caseLimit do throw "enum reference exceeds the 4,096-node case limit"
  return checked

def shapesJson (plan : Plan) : Json :=
  Json.mkObj (plan.shapes.map fun (dimension, values) => (dimension, toJson values))

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

def makeCase (plan : CheckedPlan) (input : Word) (emitted : EmittedProgram) (origin : Json) (fuel : Nat) : Json :=
  Json.mkObj [
    ("schema", toJson caseSchema), ("enumPlan", planJson plan.plan),
    ("program", Wire.encodeProgram (plan.program input)),
    ("input", toJson (toString input.val)), ("source", toJson emitted.source),
    ("provenance", Json.mkObj [
      ("origin", origin), ("profileVersion", toJson profileVersion),
      ("generatorVersion", toJson matchVersion), ("boundaryVersion", toJson Primitive.boundaryVersion),
      ("emitterVersion", toJson emitterVersion), ("wrapperVersion", toJson wrapperVersion),
      ("features", toJson ([] : List String)), ("referenceNodes", toJson plan.plan.nodes),
      ("enumShapes", shapesJson plan.plan)]),
    ("contract", contractJson emitted input), ("executionFuel", toJson fuel),
    ("directCore", observe plan input fuel)]

def emitCase (plan : CheckedPlan) (input : Word) (origin : Json) (fuel : Nat) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds profile limit"
  unless plan.plan.nodes ≤ caseLimit do throw "enum reference exceeds the 4,096-node case limit"
  return makeCase plan input (emit plan.plan) origin fuel

/-- Every origin keeps the canonical reference of its plan at its input. -/
def caseProgram (json : Json) : Except String CheckedInput := do
  unless (← json.getObjValAs? String "schema") = caseSchema do throw "unsupported semantic enum case schema"
  let plan ← checkedPlan (← json.getObjVal? "enumPlan")
  let input ← Primitive.inputWord (← json.getObjValAs? String "input")
  let program ← (Wire.decodeProgramWithBudget
    {maxDepth := caseLimit, maxNodes := caseLimit, maxIntegerBytes := 4096}
    (← json.getObjVal? "program")).mapError (fun
      | .protocol error => error.toJson.compress
      | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)
  unless Wire.encodeProgram program == Wire.encodeProgram (plan.program input) do
    throw "saved Core program differs from its enum plan's reference and runtime input"
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

/-- The seed's plan, its views dropped from the end while the reference
exceeds the budget. -/
def generatedPlan (seed : Seed) (nodes : Nat) : Except String CheckedPlan := do
  let plan := (generate seed.toUInt64).fit nodes
  unless plan.nodes ≤ nodes do throw "enum reference exceeds the node budget"
  let some checked := CheckedPlan.ofPlan? plan | throw "enum reference failed admission or the full Core checker"
  return checked

private def generatedOrigin (seed : Seed) (nodes inputIndex fuel : Nat) : Json := Json.mkObj [
  ("kind", toJson "enum-generated"), ("seed", toJson (toString seed.toNat)), ("maxProgramNodes", toJson nodes),
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
        unless minimumNodes ≤ nodes && nodes ≤ caseLimit do throw "enum node budget is outside 256 to 4,096"
        let plan ← generatedPlan seed nodes
        inputSensitive plan fuel acceptance
        return plan
      match result with
      | .error error =>
          let resource := error == "boundary observation exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "enum-profile"), ("reason", toJson error),
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
      ("profileVersion", profileVersion), ("generatorVersion", matchVersion),
      ("boundaryVersion", Primitive.boundaryVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do
      throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let emitted := emit admitted.plan.plan
  unless (← json.getObjValAs? String "source") = emitted.source do
    throw "saved source differs from emission of the enum plan"
  unless (← json.getObjVal? "contract") == contractJson emitted admitted.input do
    throw "saved contract metadata differs from the enum wrapper"
  unless (← provenance.getObjVal? "enumShapes") == shapesJson admitted.plan.plan do
    throw "saved enum shapes differ from the plan"
  let kind ← origin.getObjValAs? String "kind"
  unless kind = "enum-generated" || kind = "imported" || kind = "reduced" do
    throw "unsupported enum case origin"
  if kind = "enum-generated" then
    let seedText ← origin.getObjValAs? String "seed"
    let some seed := seedText.toNat? | throw "invalid saved seed"
    unless seed < 2 ^ 64 && toString seed = seedText do throw "noncanonical saved seed"
    let nodes ← origin.getObjValAs? Nat "maxProgramNodes"
    unless minimumNodes ≤ nodes && nodes ≤ caseLimit do
      throw "saved generation budget exceeds profile limits"
    let plan ← generatedPlan (Seed.ofNat seed) nodes
    unless planJson plan.plan == planJson admitted.plan.plan do
      throw "saved enum plan differs from its generation seed"
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
      throw "generated enum provenance is not canonical"
  else if kind = "imported" then
    unless origin == Json.mkObj [("kind", toJson "imported")] do
      throw "imported enum provenance is not canonical"
  else
    let parentPlan ← origin.getObjVal? "parentPlan"
    let parentText ← origin.getObjValAs? String "parentInput"
    let parent : CheckedInput := ⟨← checkedPlan parentPlan, ← Primitive.inputWord parentText⟩
    unless decide (admitted.measure.StrictlySmaller parent.measure) do
      throw "saved enum reduction is not strictly smaller than its checked parent"
    unless origin == Json.mkObj [("kind", toJson "reduced"), ("parentPlan", parentPlan),
        ("parentInput", toJson parentText)] do
      throw "reduced enum provenance is not canonical"
  let fresh := makeCase admitted.plan admitted.input emitted origin fuel
  unless (← fresh.getObjVal? "provenance") == provenance do
    throw "enum provenance contains unexpected fields"
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

end Solcore.Synthesis.Source.Enums
