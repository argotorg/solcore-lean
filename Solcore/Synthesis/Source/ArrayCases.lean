import Solcore.Synthesis.Source.PrimitiveCases
import Solcore.Synthesis.Source.ArraysEmitter
import Solcore.Synthesis.Core.ArraysShrink

/-! The cases of the two array profiles, `runtime-memory-arrays` and
`runtime-array-abi`. A case retains its plan, drawn from the case seed, and
the plan's complete original Core reference at the case input, built from the
plan, never from the source. The reference's left injection is the fold, or
for `runtime-array-abi` the return data and its length; its right injection is
the revert data, a length and two Words, observed as the bytes they hold.
Saved observations never supply the oracle. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.Arrays
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.Synthesis.Core.Arrays
open Solcore.Synthesis.Core.Integers (IntType Op)

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
  minimumNodes : Nat

/-- The node budget, which bounds the applied reference, at least the
profile's minimum, and the decode bound of a saved reference. -/
def defaultNodes : Nat := 1024
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

private def natText (text : String) : Except String Nat :=
  match text.toNat? with
  | some value => if toString value == text then .ok value else .error "noncanonical array plan number"
  | none => .error "array plan number is not decimal"

private def array (json : Json) (key : String) : Except String (List Json) := do
  return (← json.getObjValAs? (Array Json) key).toList

private def list (json : Json) : Except String (List Json) := do
  return (← json.getArr?).toList

def typeOf (text : String) : Except String IntType :=
  match IntType.all.find? (·.name == text) with
  | some type => .ok type
  | none => .error "unknown array element type"

def opOf (text : String) : Except String Op :=
  match Op.all.find? (·.name == text) with
  | some op => .ok op
  | none => .error "unknown array operation"

def indexJson : Index → Json
  | .literal value => Json.mkObj [("literal", toJson value)]
  | .input index => Json.mkObj [("input", toJson index)]
  | .counter => toJson "counter"

def indexOf (json : Json) : Except String Index := do
  if json == toJson "counter" then return .counter
  if let .ok value := json.getObjValAs? Nat "literal" then return .literal value
  if let .ok index := json.getObjValAs? Nat "input" then return .input index
  throw "unknown array index"

def valueJson : Arrays.Value → Json
  | .input index => Json.mkObj [("input", toJson index)]
  | .literal index => Json.mkObj [("literal", toJson index)]

def valueOf (json : Json) : Except String Arrays.Value := do
  if let .ok index := json.getObjValAs? Nat "input" then return .input index
  if let .ok index := json.getObjValAs? Nat "literal" then return .literal index
  throw "unknown array value"

def lengthJson : Length → Json
  | .literal value => Json.mkObj [("literal", toJson value)]
  | .input index => Json.mkObj [("input", toJson index)]

def lengthOf (json : Json) : Except String Length := do
  if let .ok value := json.getObjValAs? Nat "literal" then return .literal value
  if let .ok index := json.getObjValAs? Nat "input" then return .input index
  throw "unknown array length"

def nameJson : Arrays.Name → Json
  | .var index => Json.mkObj [("var", toJson index)]
  | .param index => Json.mkObj [("param", toJson index)]

def nameOf (json : Json) : Except String Arrays.Name := do
  if let .ok index := json.getObjValAs? Nat "var" then return .var index
  if let .ok index := json.getObjValAs? Nat "param" then return .param index
  throw "unknown array name"

def collJson : Coll → Json
  | .array name => Json.mkObj [("array", nameJson name)]
  | .slice index => Json.mkObj [("slice", toJson index)]
  | .storage => toJson "storage"
  | .row grid index => Json.mkObj [("row", Json.mkObj [("grid", toJson grid), ("index", indexJson index)])]
  | .calldata index => Json.mkObj [("calldata", toJson index)]

def collOf (json : Json) : Except String Coll := do
  if json == toJson "storage" then return .storage
  if let .ok name := json.getObjVal? "array" then return .array (← nameOf name)
  if let .ok index := json.getObjValAs? Nat "slice" then return .slice index
  if let .ok row := json.getObjVal? "row" then
    return .row (← row.getObjValAs? Nat "grid") (← indexOf (← row.getObjVal? "index"))
  if let .ok index := json.getObjValAs? Nat "calldata" then return .calldata index
  throw "unknown array collection"

def targetJson : Arrays.Target → Json
  | .array name => Json.mkObj [("array", nameJson name)]
  | .storage => toJson "storage"
  | .row grid index => Json.mkObj [("row", Json.mkObj [("grid", toJson grid), ("index", indexJson index)])]

def targetOf (json : Json) : Except String Arrays.Target := do
  if json == toJson "storage" then return .storage
  if let .ok name := json.getObjVal? "array" then return .array (← nameOf name)
  if let .ok row := json.getObjVal? "row" then
    return .row (← row.getObjValAs? Nat "grid") (← indexOf (← row.getObjVal? "index"))
  throw "unknown array target"

def formJson : Form → Json
  | .plain => toJson "plain"
  | .compound op unchecked => Json.mkObj [("compound", Json.mkObj [("op", toJson op.name),
      ("unchecked", toJson unchecked)])]
  | .put => toJson "put"
  | .inc => toJson "inc"

def formOf (json : Json) : Except String Form := do
  if json == toJson "plain" then return .plain
  if json == toJson "put" then return .put
  if json == toJson "inc" then return .inc
  let compound ← json.getObjVal? "compound"
  return .compound (← opOf (← compound.getObjValAs? String "op")) (← compound.getObjValAs? Bool "unchecked")

def cutJson : Cut → Json
  | .range start stop => Json.mkObj [("range", Json.arr #[indexJson start, indexJson stop])]
  | .start start => Json.mkObj [("start", indexJson start)]
  | .stop stop => Json.mkObj [("stop", indexJson stop)]
  | .all => toJson "all"

def cutOf (json : Json) : Except String Cut := do
  if json == toJson "all" then return .all
  if let .ok bounds := json.getObjVal? "range" then
    match ← list bounds with
    | [start, stop] => return .range (← indexOf start) (← indexOf stop)
    | _ => throw "an array slice range has two bounds"
  if let .ok start := json.getObjVal? "start" then return .start (← indexOf start)
  if let .ok stop := json.getObjVal? "stop" then return .stop (← indexOf stop)
  throw "unknown array slice"

def observationJson : Observation → Json
  | .length coll => Json.mkObj [("length", collJson coll)]
  | .element coll index => Json.mkObj [("element", Json.mkObj [("coll", collJson coll), ("index", indexJson index)])]
  | .gridLength grid => Json.mkObj [("gridLength", toJson grid)]
  | .sum name => Json.mkObj [("sum", nameJson name)]
  | .get coll index => Json.mkObj [("get", Json.mkObj [("coll", collJson coll), ("index", indexJson index)])]
  | .len coll => Json.mkObj [("len", collJson coll)]

def observationOf (json : Json) : Except String Observation := do
  if let .ok coll := json.getObjVal? "length" then return .length (← collOf coll)
  if let .ok read := json.getObjVal? "element" then
    return .element (← collOf (← read.getObjVal? "coll")) (← indexOf (← read.getObjVal? "index"))
  if let .ok grid := json.getObjValAs? Nat "gridLength" then return .gridLength grid
  if let .ok name := json.getObjVal? "sum" then return .sum (← nameOf name)
  if let .ok read := json.getObjVal? "get" then
    return .get (← collOf (← read.getObjVal? "coll")) (← indexOf (← read.getObjVal? "index"))
  if let .ok coll := json.getObjVal? "len" then return .len (← collOf coll)
  throw "unknown array observation"

def actionJson : Action → Json
  | .write target index value form => Json.mkObj [("write", Json.mkObj [("target", targetJson target),
      ("index", indexJson index), ("value", valueJson value), ("form", formJson form)])]
  | .observe observation => Json.mkObj [("observe", observationJson observation)]

def actionOf (json : Json) : Except String Action := do
  if let .ok write := json.getObjVal? "write" then
    return .write (← targetOf (← write.getObjVal? "target")) (← indexOf (← write.getObjVal? "index"))
      (← valueOf (← write.getObjVal? "value")) (← formOf (← write.getObjVal? "form"))
  if let .ok observation := json.getObjVal? "observe" then return .observe (← observationOf observation)
  throw "unknown array action"

def stepJson : Step → Json
  | .alloc length => Json.mkObj [("alloc", lengthJson length)]
  | .literal values => Json.mkObj [("literal", Json.arr (values.map valueJson).toArray)]
  | .alias source => Json.mkObj [("alias", nameJson source)]
  | .copy slice => Json.mkObj [("copy", toJson slice)]
  | .made left right => Json.mkObj [("made", Json.arr #[valueJson left, valueJson right])]
  | .slice base cut => Json.mkObj [("slice", Json.mkObj [("base", collJson base), ("cut", cutJson cut)])]
  | .tail source start => Json.mkObj [("tail", Json.mkObj [("source", nameJson source), ("start", indexJson start)])]
  | .grid length => Json.mkObj [("grid", lengthJson length)]
  | .gridOf sources => Json.mkObj [("gridOf", Json.arr (sources.map nameJson).toArray)]
  | .gridLiteral rows => Json.mkObj [("gridLiteral", Json.arr (rows.map fun row =>
      Json.arr (row.map valueJson).toArray).toArray)]
  | .setRow grid index source => Json.mkObj [("setRow", Json.mkObj [("grid", toJson grid), ("index", indexJson index),
      ("source", nameJson source)])]
  | .act action => actionJson action
  | .fill target value => Json.mkObj [("fill", Json.mkObj [("target", nameJson target), ("value", valueJson value)])]
  | .push value => Json.mkObj [("push", valueJson value)]
  | .pop => toJson "pop"
  | .setLength length => Json.mkObj [("setLength", lengthJson length)]
  | .loop over body => Json.mkObj [("loop", Json.mkObj [("over", collJson over),
      ("body", Json.arr (body.map actionJson).toArray)])]

def stepOf (json : Json) : Except String Step := do
  if json == toJson "pop" then return .pop
  if let .ok length := json.getObjVal? "alloc" then return .alloc (← lengthOf length)
  if let .ok values := json.getObjVal? "literal" then return .literal (← (← list values).mapM valueOf)
  if let .ok source := json.getObjVal? "alias" then return .alias (← nameOf source)
  if let .ok slice := json.getObjValAs? Nat "copy" then return .copy slice
  if let .ok values := json.getObjVal? "made" then
    match ← list values with
    | [left, right] => return .made (← valueOf left) (← valueOf right)
    | _ => throw "an array helper takes two values"
  if let .ok slice := json.getObjVal? "slice" then
    return .slice (← collOf (← slice.getObjVal? "base")) (← cutOf (← slice.getObjVal? "cut"))
  if let .ok tail := json.getObjVal? "tail" then
    return .tail (← nameOf (← tail.getObjVal? "source")) (← indexOf (← tail.getObjVal? "start"))
  if let .ok length := json.getObjVal? "grid" then return .grid (← lengthOf length)
  if let .ok sources := json.getObjVal? "gridOf" then return .gridOf (← (← list sources).mapM nameOf)
  if let .ok rows := json.getObjVal? "gridLiteral" then
    return .gridLiteral (← (← list rows).mapM fun row => do (← list row).mapM valueOf)
  if let .ok row := json.getObjVal? "setRow" then
    return .setRow (← row.getObjValAs? Nat "grid") (← indexOf (← row.getObjVal? "index"))
      (← nameOf (← row.getObjVal? "source"))
  if let .ok fill := json.getObjVal? "fill" then
    return .fill (← nameOf (← fill.getObjVal? "target")) (← valueOf (← fill.getObjVal? "value"))
  if let .ok value := json.getObjVal? "push" then return .push (← valueOf value)
  if let .ok length := json.getObjVal? "setLength" then return .setLength (← lengthOf length)
  if let .ok loop := json.getObjVal? "loop" then
    return .loop (← collOf (← loop.getObjVal? "over")) (← (← array loop "body").mapM actionOf)
  return .act (← actionOf json)

def resultJson : Result → Json
  | .word => toJson "word"
  | .array name => Json.mkObj [("array", nameJson name)]
  | .copy slice => Json.mkObj [("copy", toJson slice)]

def resultOf (json : Json) : Except String Result := do
  if json == toJson "word" then return .word
  if let .ok name := json.getObjVal? "array" then return .array (← nameOf name)
  if let .ok slice := json.getObjValAs? Nat "copy" then return .copy slice
  throw "unknown array result"

def paramLengthJson : ParamLength → Json
  | .literal value => Json.mkObj [("literal", toJson value)]
  | .input shift mask => Json.mkObj [("shift", toJson shift), ("mask", toJson mask)]

def paramLengthOf (json : Json) : Except String ParamLength := do
  if let .ok value := json.getObjValAs? Nat "literal" then return .literal value
  return .input (← json.getObjValAs? Nat "shift") (← json.getObjValAs? Nat "mask")

def planJsonWith (schema : String) (plan : Plan) : Json := Json.mkObj [
  ("schema", toJson schema), ("element", toJson plan.element.name),
  ("values", Json.arr (plan.values.map fun value => Json.mkObj [("offset", toJson (toString value.offset)),
    ("raw", toJson value.raw)]).toArray),
  ("indices", Json.arr (plan.indices.map fun index => Json.mkObj [("shift", toJson index.shift),
    ("mask", toJson index.mask), ("flagged", toJson index.flagged)]).toArray),
  ("params", Json.arr (plan.params.map fun param => Json.mkObj [("calldata", toJson param.calldata),
    ("length", paramLengthJson param.length), ("offset", toJson (toString param.offset)),
    ("raw", toJson param.raw)]).toArray),
  ("steps", Json.arr (plan.steps.map stepJson).toArray), ("result", resultJson plan.result)]

def planOfWith (schema : String) (json : Json) : Except String Plan := do
  unless (← json.getObjValAs? String "schema") = schema do throw "unsupported array plan schema"
  let element ← typeOf (← json.getObjValAs? String "element")
  let values ← (← array json "values").mapM fun item => do
    let offset ← natText (← item.getObjValAs? String "offset")
    let raw ← item.getObjValAs? Bool "raw"
    return ({offset, raw} : ValueInput)
  let indices ← (← array json "indices").mapM fun item => do
    let shift ← item.getObjValAs? Nat "shift"
    let mask ← item.getObjValAs? Nat "mask"
    let flagged ← item.getObjValAs? Bool "flagged"
    return ({shift, mask, flagged} : IndexInput)
  let params ← (← array json "params").mapM fun item => do
    let calldata ← item.getObjValAs? Bool "calldata"
    let length ← paramLengthOf (← item.getObjVal? "length")
    let offset ← natText (← item.getObjValAs? String "offset")
    let raw ← item.getObjValAs? Bool "raw"
    return ({calldata, length, offset, raw} : Param)
  let steps ← (← array json "steps").mapM stepOf
  let result ← resultOf (← json.getObjVal? "result")
  return {element, values, indices, params, steps, result}

namespace Profile

def planJson (profile : Profile) (plan : Plan) : Json := planJsonWith profile.planSchema plan

def checkedPlan (profile : Profile) (json : Json) : Except String (CheckedPlan profile) := do
  let plan ← planOfWith profile.planSchema json
  unless profile.admitted plan do
    throw (profile.label ++ " plan is outside the admitted types, inputs, parameters, steps and operands")
  let some checked := CheckedPlan.ofPlan? (profile := profile) plan
    | throw (profile.label ++ " reference failed the full Core checker")
  unless json == profile.planJson plan do
    throw ("saved " ++ profile.label ++ " plan differs from its canonical checked representation")
  unless plan.nodes ≤ caseLimit do throw (profile.label ++ " reference exceeds the 4,096-node case limit")
  return checked

def shapesJson (profile : Profile) (plan : Plan) : Json :=
  Json.mkObj ((profile.shapes plan).map fun (dimension, values) => (dimension, toJson values))

end Profile

/-! Observation: the left injection is the fold or the return data, the right
injection the revert data. -/

private def hexDigit (value : Nat) : Char := "0123456789abcdef".toList.getD value '0'

def hexBytes (bytes : List Nat) : String :=
  "0x" ++ String.ofList (bytes.flatMap fun byte => [hexDigit (byte / 16), hexDigit (byte % 16)])

/-- A returned Word, return data, or revert data. -/
inductive Observed where
  | word (value : Word)
  | output (data : List Nat)
  | reverted (data : List Nat)
  deriving BEq

private def packetWords : Solcore.Core.Value → List Nat
  | .pair (.word head) rest => head.val :: packetWords rest
  | .word last => [last.val]
  | _ => []

def Observed.ofValue? : Solcore.Core.Value → Option Observed
  | .inLeft _ (.word returned) => some (.word returned)
  | .inLeft _ packet => match packetWords packet with
      | length :: words =>
          if length ≤ 32 * words.length then some (.output ((words.flatMap wordBytes).take length)) else none
      | [] => none
  | .inRight _ (.pair (.word length) (.pair (.word first) (.word second))) =>
      if length.val ≤ 64 then some (.reverted ((wordBytes first.val ++ wordBytes second.val).take length.val)) else none
  | _ => none

def observe {profile : Profile} (plan : CheckedPlan profile) (input : Word) (fuel : Nat) : Json :=
  let fields := match (plan.program input).toCore.runStateful fuel with
    | .done value _ => match Observed.ofValue? value with
        | some (.word word) => [("status", toJson "returned"), ("word", toJson (toString word.val))]
        | some (.output data) => [("status", toJson "returned"), ("output", toJson (hexBytes data))]
        | some (.reverted data) => [("status", toJson "reverted"), ("output", toJson (hexBytes data))]
        | none => [("status", toJson "invalid-result"), ("detail", toJson (reprStr value))]
    | .outOfFuel _ => [("status", toJson "out-of-fuel")]
    | .fault reason _ => [("status", toJson "core-fault"), ("detail", toJson (reprStr reason))]
  Json.mkObj (("stage", toJson "execution") :: fields)

def calldata (plan : Plan) (input : Word) : String := hexBytes (plan.calldata input.val)

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
      ("generatorVersion", toJson arrayVersion), ("boundaryVersion", toJson Primitive.boundaryVersion),
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
        | none => .error "boundary observation did not return or revert"
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
    | .output data => if data.length = 32 then some (Word.ofNatModulo (data.foldl (fun acc byte => acc * 256 + byte) 0))
        else none
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
        unless profile.minimumNodes ≤ nodes && nodes ≤ maximumNodes do
          throw (profile.label ++ " node budget is outside " ++ toString profile.minimumNodes ++ " to 2,048")
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
      ("profileVersion", profile.profileVersion), ("generatorVersion", arrayVersion),
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
    unless profile.minimumNodes ≤ nodes && nodes ≤ maximumNodes do
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

end Solcore.Synthesis.Source.Arrays
