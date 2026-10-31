import Solcore.Synthesis.Source.MemoryValuesCases
import Solcore.Synthesis.Source.RevertDataEmitter
import Solcore.Synthesis.Core.RevertDataShrink

/-! A revert data case retains its plan, drawn from the case seed, and the
plan's complete original Core reference at the case input. The reference is
`runtime-memory-values`' byte-list model with every helper and closure
inlined, built from the plan, never from the source. Its right injection is
the revert data: a length and two Words, observed as the bytes they hold.
Saved observations never supply the oracle. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.RevertData
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.Synthesis.Core.RevertData
open Solcore.Synthesis.Core.MemoryValues (Ref Fold Width Operand Index)

def caseSchema : String := "solcore-lean.semantic-revert-data-case.v1"
def planSchema : String := "solcore-lean.revert-data-plan.v1"
def profileVersion : String := "runtime-revert-data-v1/plan-seed-v1"

/-- The node budget, which bounds the applied reference, and the decode bound
of a saved reference. -/
def defaultNodes : Nat := 1024
def minimumNodes : Nat := 256
def maximumNodes : Nat := 2048
def caseLimit : Nat := 4096

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

/-! Plan JSON, with `runtime-memory-values`' encoding of operands and
actions. Every decoder is strict and the decoded plan must re-encode to the
saved JSON. -/

private def foldName : Fold → String
  | .add => "add"
  | .xor => "xor"

private def foldOf (text : String) : Except String Fold :=
  match text with
  | "add" => .ok .add
  | "xor" => .ok .xor
  | _ => .error "unknown revert data fold"

def testJson : Test → Json
  | .lt constant => Json.mkObj [("test", toJson "lt"), ("constant", toJson constant)]
  | .gt constant => Json.mkObj [("test", toJson "gt"), ("constant", toJson constant)]
  | .eq constant => Json.mkObj [("test", toJson "eq"), ("constant", toJson constant)]
  | .ne constant => Json.mkObj [("test", toJson "ne"), ("constant", toJson constant)]
  | .bits mask value => Json.mkObj [("test", toJson "bits"), ("mask", toJson mask), ("value", toJson value)]

def condJson (cond : Cond) : Json :=
  Json.mkObj [("word", MemoryValues.operandJson cond.word), ("test", testJson cond.test)]

def makeJson : Make → Json
  | .selector word => Json.mkObj [("make", toJson "selector"), ("word", MemoryValues.operandJson word)]
  | .empty => Json.mkObj [("make", toJson "empty")]
  | .message value => Json.mkObj [("make", toJson "message"), ("value", toJson value)]

def sourceJson : Source → Json
  | .make made => Json.mkObj [("source", toJson "make"), ("make", makeJson made)]
  | .named number => Json.mkObj [("source", toJson "named"), ("number", toJson number)]
  | .param => Json.mkObj [("source", toJson "param")]

def payloadJson : Payload → Json
  | .error origin => Json.mkObj [("payload", toJson "error"), ("source", sourceJson origin)]
  | .literal text => Json.mkObj [("payload", toJson "literal"), ("text", toJson text)]
  | .none => Json.mkObj [("payload", toJson "none")]

def siteJson (site : Site) : Json := Json.mkObj [
  ("form", toJson (match site.form with
    | .when => "when"
    | .require => "require")), ("cond", condJson site.cond), ("payload", payloadJson site.payload)]

def helperJson : Helper → Json
  | .raise site fold constant => Json.mkObj [("kind", toJson "raise"), ("site", siteJson site),
      ("fold", toJson (foldName fold)), ("constant", toJson constant)]
  | .make constant => Json.mkObj [("kind", toJson "make"), ("constant", toJson constant)]
  | .message => Json.mkObj [("kind", toJson "message")]
  | .pick test => Json.mkObj [("kind", toJson "pick"), ("test", testJson test)]
  | .call callee constant => Json.mkObj [("kind", toJson "call"), ("callee", toJson callee), ("constant", toJson constant)]

def declJson : Decl → Json
  | .make made => Json.mkObj [("decl", toJson "make"), ("make", makeJson made)]
  | .helper helper word => Json.mkObj [("decl", toJson "helper"), ("helper", toJson helper),
      ("word", MemoryValues.operandJson word)]
  | .message helper value => Json.mkObj [("decl", toJson "message"), ("helper", toJson helper), ("value", toJson value)]
  | .pick helper word first second => Json.mkObj [("decl", toJson "pick"), ("helper", toJson helper),
      ("word", MemoryValues.operandJson word), ("first", sourceJson first), ("second", sourceJson second)]

def datumJson : Datum → Json
  | .pair origin word => Json.mkObj [("datum", toJson "pair"), ("error", sourceJson origin),
      ("word", MemoryValues.operandJson word)]
  | .inl origin => Json.mkObj [("datum", toJson "inl"), ("error", sourceJson origin)]
  | .inr word => Json.mkObj [("datum", toJson "inr"), ("word", MemoryValues.operandJson word)]
  | .first origin word => Json.mkObj [("datum", toJson "enum0"), ("error", sourceJson origin),
      ("word", MemoryValues.operandJson word)]
  | .second word => Json.mkObj [("datum", toJson "enum1"), ("word", MemoryValues.operandJson word)]

def heldJson : Held → Json
  | .pair number => Json.mkObj [("held", toJson "pair"), ("number", toJson number)]
  | .sum number => Json.mkObj [("held", toJson "sum"), ("number", toJson number)]
  | .enum number => Json.mkObj [("held", toJson "enum"), ("number", toJson number)]

def itemJson : Item → Json
  | .action single => Json.mkObj [("action", MemoryValues.actionJson single)]
  | .site single => Json.mkObj [("site", siteJson single)]

def stepJson : Step → Json
  | .action single => Json.mkObj [("action", MemoryValues.actionJson single)]
  | .error decl => Json.mkObj [("error", declJson decl)]
  | .data datum => Json.mkObj [("data", datumJson datum)]
  | .site single => Json.mkObj [("site", siteJson single)]
  | .call helper origin word direct fold constant => Json.mkObj [("call", Json.mkObj [
      ("helper", toJson helper), ("error", sourceJson origin), ("word", MemoryValues.operandJson word),
      ("form", toJson (if direct then "direct" else "value")), ("fold", toJson (foldName fold)),
      ("constant", toJson constant)])]
  | .take held inner fold constant => Json.mkObj [("take", Json.mkObj [("held", heldJson held),
      ("site", siteJson inner), ("fold", toJson (foldName fold)), ("constant", toJson constant)])]
  | .closure inner fold constant => Json.mkObj [("closure", Json.mkObj [("site", siteJson inner),
      ("fold", toJson (foldName fold)), ("constant", toJson constant)])]
  | .apply number word fold constant => Json.mkObj [("apply", Json.mkObj [("closure", toJson number),
      ("word", MemoryValues.operandJson word), ("fold", toJson (foldName fold)), ("constant", toJson constant)])]
  | .loop mask body => Json.mkObj [("loop", Json.mkObj [("mask", toJson mask),
      ("body", .arr (body.map itemJson).toArray)])]

def planJson (plan : Plan) : Json := Json.mkObj [
  ("schema", toJson planSchema), ("helpers", .arr (plan.helpers.map helperJson).toArray),
  ("steps", .arr (plan.steps.map stepJson).toArray)]

private def array (json : Json) (key : String) : Except String (List Json) := do
  return (← json.getObjValAs? (Array Json) key).toList

def testOf (json : Json) : Except String Test := do
  match ← json.getObjValAs? String "test" with
  | "lt" => return .lt (← json.getObjValAs? Nat "constant")
  | "gt" => return .gt (← json.getObjValAs? Nat "constant")
  | "eq" => return .eq (← json.getObjValAs? Nat "constant")
  | "ne" => return .ne (← json.getObjValAs? Nat "constant")
  | "bits" => return .bits (← json.getObjValAs? Nat "mask") (← json.getObjValAs? Nat "value")
  | _ => throw "unknown revert data test"

def condOf (json : Json) : Except String Cond := do
  return {word := ← MemoryValues.operandOf (← json.getObjVal? "word"), test := ← testOf (← json.getObjVal? "test")}

def makeOf (json : Json) : Except String Make := do
  match ← json.getObjValAs? String "make" with
  | "selector" => return .selector (← MemoryValues.operandOf (← json.getObjVal? "word"))
  | "empty" => return .empty
  | "message" => return .message (← json.getObjValAs? Nat "value")
  | _ => throw "unknown revert data make"

def sourceOf (json : Json) : Except String Source := do
  match ← json.getObjValAs? String "source" with
  | "make" => return .make (← makeOf (← json.getObjVal? "make"))
  | "named" => return .named (← json.getObjValAs? Nat "number")
  | "param" => return .param
  | _ => throw "unknown revert data source"

def payloadOf (json : Json) : Except String Payload := do
  match ← json.getObjValAs? String "payload" with
  | "error" => return .error (← sourceOf (← json.getObjVal? "source"))
  | "literal" => return .literal (← json.getObjValAs? Nat "text")
  | "none" => return .none
  | _ => throw "unknown revert data payload"

def siteOf (json : Json) : Except String Site := do
  let form ← match ← json.getObjValAs? String "form" with
    | "when" => pure Form.when
    | "require" => pure Form.require
    | _ => throw "unknown revert data form"
  return {form, cond := ← condOf (← json.getObjVal? "cond"), payload := ← payloadOf (← json.getObjVal? "payload")}

def helperOf (json : Json) : Except String Helper := do
  match ← json.getObjValAs? String "kind" with
  | "raise" =>
      let site ← siteOf (← json.getObjVal? "site")
      let fold ← foldOf (← json.getObjValAs? String "fold")
      return .raise site fold (← json.getObjValAs? Nat "constant")
  | "make" => return .make (← json.getObjValAs? Nat "constant")
  | "message" => return .message
  | "pick" => return .pick (← testOf (← json.getObjVal? "test"))
  | "call" => return .call (← json.getObjValAs? Nat "callee") (← json.getObjValAs? Nat "constant")
  | _ => throw "unknown revert data helper"

def declOf (json : Json) : Except String Decl := do
  match ← json.getObjValAs? String "decl" with
  | "make" => return .make (← makeOf (← json.getObjVal? "make"))
  | "helper" => return .helper (← json.getObjValAs? Nat "helper") (← MemoryValues.operandOf (← json.getObjVal? "word"))
  | "message" => return .message (← json.getObjValAs? Nat "helper") (← json.getObjValAs? Nat "value")
  | "pick" =>
      let helper ← json.getObjValAs? Nat "helper"
      let word ← MemoryValues.operandOf (← json.getObjVal? "word")
      let first ← sourceOf (← json.getObjVal? "first")
      return .pick helper word first (← sourceOf (← json.getObjVal? "second"))
  | _ => throw "unknown revert data declaration"

def datumOf (json : Json) : Except String Datum := do
  match ← json.getObjValAs? String "datum" with
  | "pair" => return .pair (← sourceOf (← json.getObjVal? "error")) (← MemoryValues.operandOf (← json.getObjVal? "word"))
  | "inl" => return .inl (← sourceOf (← json.getObjVal? "error"))
  | "inr" => return .inr (← MemoryValues.operandOf (← json.getObjVal? "word"))
  | "enum0" => return .first (← sourceOf (← json.getObjVal? "error")) (← MemoryValues.operandOf (← json.getObjVal? "word"))
  | "enum1" => return .second (← MemoryValues.operandOf (← json.getObjVal? "word"))
  | _ => throw "unknown revert data datum"

def heldOf (json : Json) : Except String Held := do
  let number ← json.getObjValAs? Nat "number"
  match ← json.getObjValAs? String "held" with
  | "pair" => return .pair number
  | "sum" => return .sum number
  | "enum" => return .enum number
  | _ => throw "unknown revert data data variable"

def itemOf (json : Json) : Except String Item := do
  if let .ok single := json.getObjVal? "action" then return .action (← MemoryValues.actionOf single)
  return .site (← siteOf (← json.getObjVal? "site"))

def stepOf (json : Json) : Except String Step := do
  if let .ok single := json.getObjVal? "action" then return .action (← MemoryValues.actionOf single)
  if let .ok decl := json.getObjVal? "error" then return .error (← declOf decl)
  if let .ok datum := json.getObjVal? "data" then return .data (← datumOf datum)
  if let .ok single := json.getObjVal? "site" then return .site (← siteOf single)
  if let .ok call := json.getObjVal? "call" then
    let direct ← match ← call.getObjValAs? String "form" with
      | "direct" => pure true
      | "value" => pure false
      | _ => throw "unknown revert data call form"
    let helper ← call.getObjValAs? Nat "helper"
    let origin ← sourceOf (← call.getObjVal? "error")
    let word ← MemoryValues.operandOf (← call.getObjVal? "word")
    let fold ← foldOf (← call.getObjValAs? String "fold")
    return .call helper origin word direct fold (← call.getObjValAs? Nat "constant")
  if let .ok take := json.getObjVal? "take" then
    let held ← heldOf (← take.getObjVal? "held")
    let site ← siteOf (← take.getObjVal? "site")
    let fold ← foldOf (← take.getObjValAs? String "fold")
    return .take held site fold (← take.getObjValAs? Nat "constant")
  if let .ok closure := json.getObjVal? "closure" then
    let site ← siteOf (← closure.getObjVal? "site")
    let fold ← foldOf (← closure.getObjValAs? String "fold")
    return .closure site fold (← closure.getObjValAs? Nat "constant")
  if let .ok applied := json.getObjVal? "apply" then
    let number ← applied.getObjValAs? Nat "closure"
    let word ← MemoryValues.operandOf (← applied.getObjVal? "word")
    let fold ← foldOf (← applied.getObjValAs? String "fold")
    return .apply number word fold (← applied.getObjValAs? Nat "constant")
  let loop ← json.getObjVal? "loop"
  return .loop (← loop.getObjValAs? Nat "mask") (← (← array loop "body").mapM itemOf)

def planOf (json : Json) : Except String Plan := do
  unless (← json.getObjValAs? String "schema") = planSchema do throw "unsupported revert data plan schema"
  return {helpers := ← (← array json "helpers").mapM helperOf, steps := ← (← array json "steps").mapM stepOf}

def checkedPlan (json : Json) : Except String CheckedPlan := do
  let plan ← planOf json
  unless plan.admitted do
    throw "revert data plan is outside the admitted helpers, steps, sites, values and literals"
  let some checked := CheckedPlan.ofPlan? plan | throw "revert data reference failed the full Core checker"
  unless json == planJson plan do throw "saved revert data plan differs from its canonical checked representation"
  unless plan.nodes ≤ caseLimit do throw "revert data reference exceeds the 4,096-node case limit"
  return checked

def shapesJson (plan : Plan) : Json :=
  Json.mkObj (plan.shapes.map fun (dimension, values) => (dimension, toJson values))

/-! Observation: the reference's right injection is the revert data. -/

private def hexDigit (value : Nat) : Char := "0123456789abcdef".toList.getD value '0'

def hexBytes (bytes : List Nat) : String :=
  "0x" ++ String.ofList (bytes.flatMap fun byte => [hexDigit (byte / 16), hexDigit (byte % 16)])

def wordBytes (value : Nat) : List Nat := (List.range 32).reverse.map fun index => (value / 256 ^ index) % 256

/-- A returned Word, or revert data. -/
inductive Outcome where
  | word (value : Word)
  | reverted (data : List Nat)
  deriving BEq

def Outcome.ofValue? : Value → Option Outcome
  | .inLeft _ (.word returned) => some (.word returned)
  | .inRight _ (.pair (.word length) (.pair (.word first) (.word second))) =>
      if length.val ≤ 64 then some (.reverted ((wordBytes first.val ++ wordBytes second.val).take length.val)) else none
  | _ => none

def observe (plan : CheckedPlan) (input : Word) (fuel : Nat) : Json :=
  let fields := match (plan.program input).toCore.runStateful fuel with
    | .done value _ => match Outcome.ofValue? value with
        | some (.word word) => [("status", toJson "returned"), ("word", toJson (toString word.val))]
        | some (.reverted data) => [("status", toJson "reverted"), ("output", toJson (hexBytes data))]
        | none => [("status", toJson "invalid-result"), ("detail", toJson (reprStr value))]
    | .outOfFuel _ => [("status", toJson "out-of-fuel")]
    | .fault reason _ =>
        [("status", toJson "core-fault"), ("detail", toJson (reprStr reason))]
  Json.mkObj (("stage", toJson "execution") :: fields)

def makeCase (plan : CheckedPlan) (input : Word) (emitted : EmittedProgram) (origin : Json) (fuel : Nat) : Json :=
  Json.mkObj [
    ("schema", toJson caseSchema), ("revertDataPlan", planJson plan.plan),
    ("program", Wire.encodeProgram (plan.program input)),
    ("input", toJson (toString input.val)), ("source", toJson emitted.source),
    ("provenance", Json.mkObj [
      ("origin", origin), ("profileVersion", toJson profileVersion),
      ("generatorVersion", toJson revertVersion), ("boundaryVersion", toJson Primitive.boundaryVersion),
      ("emitterVersion", toJson emitterVersion), ("wrapperVersion", toJson wrapperVersion),
      ("features", toJson ([] : List String)), ("referenceNodes", toJson plan.plan.nodes),
      ("revertDataShapes", shapesJson plan.plan)]),
    ("contract", Enums.contractJson emitted input), ("executionFuel", toJson fuel),
    ("directCore", observe plan input fuel)]

def emitCase (plan : CheckedPlan) (input : Word) (origin : Json) (fuel : Nat) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds profile limit"
  unless plan.plan.nodes ≤ caseLimit do throw "revert data reference exceeds the 4,096-node case limit"
  return makeCase plan input (emit plan.plan) origin fuel

/-- Every origin keeps the canonical reference of its plan at its input. -/
def caseProgram (json : Json) : Except String CheckedInput := do
  unless (← json.getObjValAs? String "schema") = caseSchema do throw "unsupported semantic revert data case schema"
  let plan ← checkedPlan (← json.getObjVal? "revertDataPlan")
  let input ← Primitive.inputWord (← json.getObjValAs? String "input")
  let program ← (Wire.decodeProgramWithBudget
    {maxDepth := caseLimit, maxNodes := caseLimit, maxIntegerBytes := 4096}
    (← json.getObjVal? "program")).mapError (fun
      | .protocol error => error.toJson.compress
      | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)
  unless Wire.encodeProgram program == Wire.encodeProgram (plan.program input) do
    throw "saved Core program differs from its revert data plan's reference and runtime input"
  return ⟨plan, input⟩

/-- A generation filter on the reference, not a claim that this finite bank
covers a plan. -/
def boundaryOutcomes (plan : CheckedPlan) (fuel : Nat) : Except String (List Outcome) := do
  Primitive.boundaryInputs.mapM fun input =>
    match (plan.program input).toCore.runStateful fuel with
    | .done value _ => match Outcome.ofValue? value with
        | some outcome => .ok outcome
        | none => .error "boundary observation did not return a Word or revert data"
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
    | .reverted _ => none
  if words.length = outcomes.length then acceptance.check Primitive.boundaryInputs words

/-- The seed's plan, its steps dropped from the end while the reference
exceeds the budget. -/
def generatedPlan (seed : Seed) (nodes : Nat) : Except String CheckedPlan := do
  let plan := (generate seed.toUInt64).fit nodes
  unless plan.nodes ≤ nodes do throw "revert data reference exceeds the node budget"
  let some checked := CheckedPlan.ofPlan? plan
    | throw "revert data reference failed admission or the full Core checker"
  return checked

private def generatedOrigin (seed : Seed) (nodes inputIndex fuel : Nat) : Json := Json.mkObj [
  ("kind", toJson "revert-data-generated"), ("seed", toJson (toString seed.toNat)), ("maxProgramNodes", toJson nodes),
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
          throw "revert data node budget is outside 256 to 2,048"
        let plan ← generatedPlan seed nodes
        inputSensitive plan fuel acceptance
        return plan
      match result with
      | .error error =>
          let resource := error == "boundary observation exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "revert-data-profile"), ("reason", toJson error),
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
      ("profileVersion", profileVersion), ("generatorVersion", revertVersion),
      ("boundaryVersion", Primitive.boundaryVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do
      throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let emitted := emit admitted.plan.plan
  unless (← json.getObjValAs? String "source") = emitted.source do
    throw "saved source differs from emission of the revert data plan"
  unless (← json.getObjVal? "contract") == Enums.contractJson emitted admitted.input do
    throw "saved contract metadata differs from the revert data wrapper"
  unless (← provenance.getObjVal? "revertDataShapes") == shapesJson admitted.plan.plan do
    throw "saved revert data shapes differ from the plan"
  let kind ← origin.getObjValAs? String "kind"
  unless kind = "revert-data-generated" || kind = "imported" || kind = "reduced" do
    throw "unsupported revert data case origin"
  if kind = "revert-data-generated" then
    let seedText ← origin.getObjValAs? String "seed"
    let some seed := seedText.toNat? | throw "invalid saved seed"
    unless seed < 2 ^ 64 && toString seed = seedText do throw "noncanonical saved seed"
    let nodes ← origin.getObjValAs? Nat "maxProgramNodes"
    unless minimumNodes ≤ nodes && nodes ≤ maximumNodes do
      throw "saved generation budget exceeds profile limits"
    let plan ← generatedPlan (Seed.ofNat seed) nodes
    unless planJson plan.plan == planJson admitted.plan.plan do
      throw "saved revert data plan differs from its generation seed"
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
      throw "generated revert data provenance is not canonical"
  else if kind = "imported" then
    unless origin == Json.mkObj [("kind", toJson "imported")] do
      throw "imported revert data provenance is not canonical"
  else
    let parentPlan ← origin.getObjVal? "parentPlan"
    let parentText ← origin.getObjValAs? String "parentInput"
    let parent : CheckedInput := ⟨← checkedPlan parentPlan, ← Primitive.inputWord parentText⟩
    unless decide (admitted.measure.StrictlySmaller parent.measure) do
      throw "saved revert data reduction is not strictly smaller than its checked parent"
    unless origin == Json.mkObj [("kind", toJson "reduced"), ("parentPlan", parentPlan),
        ("parentInput", toJson parentText)] do
      throw "reduced revert data provenance is not canonical"
  let fresh := makeCase admitted.plan admitted.input emitted origin fuel
  unless (← fresh.getObjVal? "provenance") == provenance do
    throw "revert data provenance contains unexpected fields"
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

end Solcore.Synthesis.Source.RevertData
