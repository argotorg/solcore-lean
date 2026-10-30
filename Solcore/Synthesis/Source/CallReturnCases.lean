import Solcore.Synthesis.Source.StorageCases
import Solcore.Synthesis.Source.NestedCallCases
import Solcore.Synthesis.Source.EnumReturnCases
import Solcore.Synthesis.Source.CallReturnEmitter
import Solcore.Synthesis.Stateful.CallReturnExecution

/-! A call-return case retains the three original checked Core contracts, the
child's returned value with its delivery, and a role-based transaction
sequence. Every replay reconstructs the contracts from the plan. Each
transaction records std's prescribed rejection, computed by the byte-level
model over the child's bytes; saved outcomes are never an oracle, and the
call-and-resume convention selects the committed worlds. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.CallReturn
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.Synthesis.Core.CallReturn (CheckedPlan Kind Returned Delivery Malformation)
open Solcore.Synthesis.Core.EnumReturn (Constructor Shape)
open Solcore.Synthesis.Stateful.CallReturnExecution (Transaction Bindings)
open Solcore.ContractRuntime (EnumPayload encodeBytesText)

def caseSchema : String := "solcore-lean.semantic-call-return-case.v1"
def planSchema : String := "solcore-lean.call-return-plan.v1"
def profileVersion : String := "stateful-call-returns-v1/call-return-sequence-seed-v1"
def templateVersion : String := "std-raw-call-decode-record-step-revert-odd-input-v1"
def corpusSchema : String := "solcore-lean.semantic-call-return-corpus.v1"

abbrev boundaryInputs := NestedCall.boundaryInputs
abbrev validId := Storage.validId
abbrev validTransactions := Storage.validTransactions

/-- The `bytes` lengths drawn half of the time, std's boundaries. -/
def lengthBank : List Nat := [0, 1, 31, 32, 33, 63, 64]

/-- Random steps and the child's shell stay within the largest step budget. -/
def maxStepNodes : Nat := 512

private def w (value : Nat) : Word := Word.ofNatModulo value

/-- The child's shell and its step, which a node budget bounds. -/
def budgetNodes (plan : CheckedPlan) : Nat :=
  CallReturn.childShellNodes plan.returned + Wire.programNodes plan.step.program

structure CheckedScenario where private mk ::
  plan : CheckedPlan
  transactions : List Transaction
  valid : validTransactions transactions
  bounded : Wire.programNodes plan.childProgram ≤ CallReturn.maxContractNodes ∧
    Wire.programNodes plan.resumeProgram ≤ CallReturn.maxContractNodes ∧
    Wire.programNodes plan.callProgram ≤ CallReturn.maxContractNodes

def checkedScenario (plan : CheckedPlan) (transactions : List Transaction) : Except String CheckedScenario := do
  if valid : validTransactions transactions then
    if bounded : Wire.programNodes plan.childProgram ≤ CallReturn.maxContractNodes ∧
        Wire.programNodes plan.resumeProgram ≤ CallReturn.maxContractNodes ∧
        Wire.programNodes plan.callProgram ≤ CallReturn.maxContractNodes then
      return ⟨plan, transactions, valid, bounded⟩
    else throw "call-return contracts exceed the 1024-node contract limit"
  else throw s!"call-return scenario requires 1..{Stateful.Sequence.maxTransactions} transactions with distinct valid IDs"

/-! ### Plans -/

def malformationKinds : List String := ["truncate", "trailing", "offset", "length", "tag", "tagCut", "tail", "narrow"]

def kindOf : Malformation → String
  | .truncate _ => "truncate"
  | .trailing _ _ => "trailing"
  | .offset _ => "offset"
  | .length _ => "length"
  | .tag _ => "tag"
  | .tagCut _ => "tagCut"
  | .tail _ => "tail"
  | .narrow => "narrow"

def malformationJson : Malformation → Json
  | .truncate kept => Json.mkObj [("kind", toJson "truncate"), ("kept", toJson kept)]
  | .trailing count pattern => Json.mkObj [("kind", toJson "trailing"), ("count", toJson count),
      ("pattern", toJson (Stateful.StdCalldata.patternNames.getD pattern "zeros"))]
  | .offset value => Json.mkObj [("kind", toJson "offset"), ("value", toJson (toString value.val))]
  | .length value => Json.mkObj [("kind", toJson "length"), ("value", toJson (toString value.val))]
  | .tag value => Json.mkObj [("kind", toJson "tag"), ("value", toJson (toString value.val))]
  | .tagCut value => Json.mkObj [("kind", toJson "tagCut"), ("value", toJson (toString value.val))]
  | .tail value => Json.mkObj [("kind", toJson "tail"), ("value", toJson (toString value.val))]
  | .narrow => Json.mkObj [("kind", toJson "narrow")]

private def wordText (text : String) : Except String Word := do
  unless text.length ≤ 78 do throw "a Word exceeds 78 decimal digits"
  Input.inputWord text

def decodeMalformation (json : Json) : Except String Malformation := do
  match ← json.getObjValAs? String "kind" with
  | "truncate" => return .truncate (← json.getObjValAs? Nat "kept")
  | "trailing" =>
      let some pattern := Stateful.StdCalldata.patternNames.idxOf? (← json.getObjValAs? String "pattern")
        | throw "unsupported trailing pattern"
      return .trailing (← json.getObjValAs? Nat "count") pattern
  | "offset" => return .offset (← wordText (← json.getObjValAs? String "value"))
  | "length" => return .length (← wordText (← json.getObjValAs? String "value"))
  | "tag" => return .tag (← wordText (← json.getObjValAs? String "value"))
  | "tagCut" => return .tagCut (← wordText (← json.getObjValAs? String "value"))
  | "tail" => return .tail (← wordText (← json.getObjValAs? String "value"))
  | "narrow" => return .narrow
  | _ => throw "unsupported malformation kind"

def deliveryJson : Delivery → Json
  | .typed => Json.mkObj [("kind", toJson "typed")]
  | .raw malformation => Json.mkObj [("kind", toJson "raw"), ("malformation", malformationJson malformation)]

def decodeDelivery (json : Json) : Except String Delivery := do
  match ← json.getObjValAs? String "kind" with
  | "typed" => return .typed
  | "raw" => return .raw (← decodeMalformation (← json.getObjVal? "malformation"))
  | _ => throw "unsupported delivery"

/-- The kind's name, as the plan records it. -/
def kindName : Kind → String
  | .tuple _ => "tuple"
  | .bytes => "bytes"
  | .enum shape => if shape.dynamic then "dynamic-enum" else "static-enum"

def planJson (plan : CheckedPlan) : Json :=
  let returned := plan.returned
  Json.mkObj ([("schema", toJson planSchema), ("kind", toJson (kindName returned.kind))] ++
    (match returned.kind with
      | .tuple extra => [("arity", toJson (extra + 2))]
      | .enum shape => [("constructors", toJson (shape.constructors.map EnumReturn.constructorJson))]
      | .bytes => []) ++
    [("length", toJson returned.length), ("choice", toJson returned.choice),
      ("delivery", deliveryJson returned.delivery), ("stepProgram", Wire.encodeProgram plan.step.program)])

private def payloadOf? (fields : String) : Option EnumPayload :=
  [EnumPayload.noWords, .oneWord, .twoWords, .boundedBytes].find?
    (Solcore.Synthesis.Core.EnumReturn.fieldSignature · == fields)

def checkedPlan (json : Json) : Except String CheckedPlan := do
  unless (← json.getObjValAs? String "schema") = planSchema do throw "unsupported call-return plan schema"
  let kind ← match ← json.getObjValAs? String "kind" with
    | "tuple" =>
        let arity ← json.getObjValAs? Nat "arity"
        unless 2 ≤ arity && arity ≤ 4 do throw "a returned tuple has two to four Words"
        pure (Kind.tuple (arity - 2))
    | "bytes" => pure .bytes
    | "static-enum" | "dynamic-enum" =>
        let rows ← (← json.getObjVal? "constructors").getArr?
        let constructors ← rows.toList.mapM fun row => do
          let some payload := payloadOf? (← row.getObjValAs? String "fields") | throw "unsupported constructor fields"
          return ({name := ← row.getObjValAs? String "name", payload} : Constructor)
        let some shape := EnumReturn.Shape.ofList? constructors | throw "an enum needs at least two constructors"
        pure (.enum shape)
    | _ => throw "unsupported returned kind"
  let returned : Returned := ⟨kind, ← json.getObjValAs? Nat "length", ← json.getObjValAs? Nat "choice",
    ← decodeDelivery (← json.getObjVal? "delivery")⟩
  let step ← Aggregate.checkedFunction (← json.getObjVal? "stepProgram")
  let some plan := CheckedPlan.ofParts? step returned
    | throw "call-return plan needs a valid returned value, a malformation that applies, and full host-Core admission"
  unless json == planJson plan do throw "call-return plan differs from its canonical checked representation"
  return plan

/-! ### Transactions and their prescribed rejections -/

/-- std's prescribed rejection of each transaction's return data, from the
byte-level model; none when the child reverts or std accepts. -/
def prescribed (plan : CheckedPlan) (fuel : Nat) (transactions : List Transaction) :
    Except String (List (Option ByteArray)) := do
  let some rows := Stateful.CallReturnExecution.model plan fuel transactions
    | throw "call-return model exhausted Core fuel"
  return rows.map (·.rejection)

def rejectionJson : Option ByteArray → Json
  | none => Json.null
  | some data => toJson (encodeBytesText data)

def transactionJson (tx : Transaction) (rejection : Option ByteArray) : Json := Json.mkObj [
  ("id", toJson tx.id), ("input", toJson (toString tx.input.val)),
  ("value", toJson "0"), ("target", toJson "parent"), ("callee", toJson "child"),
  ("stdRejection", rejectionJson rejection)]

def transactionsJson (plan : CheckedPlan) (fuel : Nat) (transactions : List Transaction) : Except String Json := do
  let rejections ← prescribed plan fuel transactions
  return toJson ((transactions.zip rejections).map fun (tx, rejection) => transactionJson tx rejection)

/-- The transactions' identities and inputs; their prescribed rejections are
checked against the model once the plan is known. -/
def decodeSequence (json : Json) : Except String (List Transaction) := do
  let rows ← json.getArr?
  unless 1 ≤ rows.size && rows.size ≤ Stateful.Sequence.maxTransactions do
    throw s!"transaction count must be between 1 and {Stateful.Sequence.maxTransactions}"
  let transactions ← rows.toList.mapM fun row => do
    let input ← wordText (← row.getObjValAs? String "input")
    return ({id := ← row.getObjValAs? String "id", input} : Transaction)
  unless validTransactions transactions do throw "call-return scenario requires distinct valid transaction IDs"
  return transactions

/-- An imported sequence: exactly each transaction's ID and input. -/
def decodeImportedSequence (json : Json) : Except String (List Transaction) := do
  let transactions ← decodeSequence json
  unless json == toJson (transactions.map fun tx =>
      Json.mkObj [("id", toJson tx.id), ("input", toJson (toString tx.input.val))]) do
    throw "imported transactions carry exactly their ID and input"
  return transactions

def decodeTransactions (plan : CheckedPlan) (fuel : Nat) (json : Json) : Except String (List Transaction) := do
  let transactions ← decodeSequence json
  unless json == (← transactionsJson plan fuel transactions) do
    throw "transactions differ from their canonical ID, input, role metadata or prescribed rejection"
  return transactions

/-! ### Cases -/

def programsJson (plan : CheckedPlan) : Json := Json.mkObj [
  ("parentCall", Wire.encodeProgram plan.callProgram), ("parentResume", Wire.encodeProgram plan.resumeProgram),
  ("child", Wire.encodeProgram plan.childProgram)]

def contractsJson : Json := Json.mkObj [
  ("parent", Json.mkObj [("name", toJson parentContractName), ("method", toJson "run"),
    ("signature", toJson parentMethodSignature), ("selector", toJson parentSelector),
    ("deployPath", toJson parentDeployPath), ("runtimePath", toJson parentRuntimePath),
    ("constructorCalldata", toJson "0x"), ("constructorValue", toJson "0")]),
  ("child", Json.mkObj [("name", toJson childContractName), ("method", toJson "get"),
    ("signature", toJson childMethodSignature), ("selector", toJson childSelector),
    ("deployPath", toJson childDeployPath), ("runtimePath", toJson childRuntimePath),
    ("constructorCalldata", toJson "0x"), ("constructorValue", toJson "0")])]

def initialStateJson : Json := Json.mkObj [
  ("accounts", toJson [
    Json.mkObj [("role", toJson "parent"), ("balance", toJson "0"), ("storage", toJson ([] : List Json))],
    Json.mkObj [("role", toJson "child"), ("balance", toJson "0"), ("storage", toJson ([] : List Json))]]),
  ("callerBalance", toJson "0")]

def observedSlotsJson : Json := Json.mkObj [
  ("parent", toJson (Stateful.CallReturnExecution.parentSlots.map fun slot => toString slot.val)),
  ("child", toJson (Stateful.CallReturnExecution.childSlots.map fun slot => toString slot.val))]

def makeCase (scenario : CheckedScenario) (emitted : EmittedContracts) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1) (mask : FeatureMask := FeatureMask.all) : Except String Json := do
  return Json.mkObj [
    ("schema", toJson caseSchema), ("callReturnPlan", planJson scenario.plan),
    ("programs", programsJson scenario.plan),
    ("sources", Json.mkObj [("parent", toJson emitted.parentSource), ("child", toJson emitted.childSource)]),
    ("transactions", ← transactionsJson scenario.plan fuel scenario.transactions),
    ("initialState", initialStateJson), ("observedSlots", observedSlotsJson),
    ("provenance", Json.mkObj <| swarmField revision mask ++ [
      ("origin", origin), ("profileVersion", toJson profileVersion),
      ("functionVersion", toJson CallReturn.childVersion), ("parentVersion", toJson CallReturn.parentVersion),
      ("templateVersion", toJson templateVersion),
      ("stepProfileVersion", toJson Aggregate.profileVersion),
      ("stepFunctionVersion", toJson Aggregates.version),
      ("stepTemplateVersion", toJson Aggregate.templateVersion),
      ("generatorVersion", toJson revision.version),
      ("emitterVersion", toJson emitterVersion), ("wrapperVersion", toJson wrapperVersion),
      ("features", toJson scenario.plan.step.features)]),
    ("contracts", contractsJson), ("executionFuel", toJson fuel)]

def emitCase (scenario : CheckedScenario) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1) (mask : FeatureMask := FeatureMask.all) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
  let emitted ← (emit scenario.plan).mapError reprStr
  makeCase scenario emitted origin fuel revision mask

private def decodeProgram (json : Json) : Except String Wire.Program :=
  (Wire.decodeProgramWithBudget {maxDepth := 512, maxNodes := CallReturn.maxContractNodes, maxIntegerBytes := 4096}
    json).mapError (fun
    | .protocol error => error.toJson.compress
    | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)

/-- Every origin must reconstruct the three fixed host contracts, including
imports and reductions. Arbitrary well-typed programs are not admissible
replacements. -/
def caseProgram (json : Json) : Except String CheckedScenario := do
  unless (← json.getObjValAs? String "schema") = caseSchema do throw "unsupported semantic call-return case schema"
  let plan ← checkedPlan (← json.getObjVal? "callReturnPlan")
  let fuel ← json.getObjValAs? Nat "executionFuel"
  unless fuel ≤ 10000000 do throw "saved execution fuel exceeds limit"
  let transactions ← decodeTransactions plan fuel (← json.getObjVal? "transactions")
  let originals ← json.getObjVal? "programs"
  for (name, expected) in [("parentCall", plan.callProgram), ("parentResume", plan.resumeProgram),
      ("child", plan.childProgram)] do
    let program ← decodeProgram (← originals.getObjVal? name)
    unless Wire.encodeProgram program == Wire.encodeProgram expected do
      throw "saved original Core program differs from its canonical call-return plan"
  unless originals == programsJson plan do throw "saved program roles are not canonical"
  unless (← json.getObjVal? "initialState") == initialStateJson do throw "initial accounts must be empty and unfunded"
  unless (← json.getObjVal? "observedSlots") == observedSlotsJson do
    throw "observed slots must be the parent's 0 to 6 and the child's 0 and 1"
  checkedScenario plan transactions

def observe (scenario : CheckedScenario) (bindings : Bindings) (fuel : Nat) : Json :=
  Stateful.CallReturnExecution.observe scenario.plan scenario.transactions bindings fuel

/-! ### Generation -/

/-- SplitMix64's finalizer. The generator's draws are affine in its start, so
consecutive seeds would otherwise start streams whose draws step by a fixed
residue. -/
private def mixed (value : Nat) : Nat :=
  let z := value % 2 ^ 64
  let z := (z ^^^ (z >>> 30)) * 0xbf58476d1ce4e5b9 % 2 ^ 64
  let z := (z ^^^ (z >>> 27)) * 0x94d049bb133111eb % 2 ^ 64
  z ^^^ (z >>> 31)

/-- High halves of successive draws from the stream that starts at the mixed
`seed` xor `domain`, each below its bound. -/
private def boundedDraws (seed : Seed) (domain : Nat) (bounds : List Nat) : List Nat := Id.run do
  let mut state := Seed.ofNat (mixed (seed.toNat ^^^ domain))
  let mut values : Array Nat := #[]
  for bound in bounds do
    let (value, next) := state.draw
    values := values.push (value.toNat / 2 ^ 32 % bound)
    state := next
  return values.toList

/-- The kind, the tuple's arity, a length selector and a uniform length, the
choice, the delivery's selector, the malformation's kind and its bank entry. -/
def shapeBounds : List Nat := [8, 3, 14, 65, 12, 3, 12, 16]

def shapeChoices (seed : Seed) : List Nat := boundedDraws seed 0x7265742d73686170 shapeBounds

/-- A tuple three times in eight, `bytes` twice and an enum three times, its
shape drawn as for the enum-return profile. -/
def generatedKind (seed : Seed) : Kind :=
  let choices := shapeChoices seed
  match choices.getD 0 0 with
  | 0 | 1 | 2 => .tuple (choices.getD 1 0)
  | 3 | 4 => .bytes
  | _ => .enum (EnumReturn.generatedShape seed)

/-- The returned value with every field its kind does not use set to zero. -/
def canonicalReturned (returned : Returned) : Returned :=
  let choice := match returned.kind with
    | .enum shape => returned.choice % shape.constructors.length
    | _ => 0
  let base := {returned with choice}
  {base with length := if base.carriesBytes then base.length else 0}

private def uniqueNats (values : List Nat) : List Nat := values.eraseDups

/-- The malformations of a kind that apply, in bank order. -/
def malformationBank (returned : Returned) (kind : String) : List Malformation :=
  let typed := {returned with delivery := .typed}
  let n := CallReturn.canonicalSize typed
  let valid := fun (malformation : Malformation) => malformation.valid typed
  let words := fun (values : List Nat) => (uniqueNats values).map w
  (match kind with
    | "truncate" =>
        let boundaries := (List.range ((n + 31) / 32)).filterMap fun index =>
          if 0 < index && 32 * index < n then some index else none
        (uniqueNats (0 :: (boundaries.flatMap fun index => [32 * index - 1, 32 * index]) ++ [n - 1])).map Malformation.truncate
    | "trailing" => [1, 31, 32, 33].flatMap fun count => [0, 1, 2].map (Malformation.trailing count)
    | "offset" => (words [0, 1, n - 31, n, 2 ^ 255, 2 ^ 256 - 32]).map Malformation.offset
    | "length" =>
        let length := returned.length
        let fits := n - (CallReturn.lengthPosition typed + 32)
        (words ([0] ++ (if length > 0 then [length - 1] else []) ++ [length + 1, fits, fits + 1, 2 ^ 256 - 1])).map
          Malformation.length
    | "tag" | "tagCut" =>
        let tag := match returned.kind with
          | .enum shape => (EnumReturn.tag (CallReturn.chosen shape returned.choice)).val
          | _ => 0
        let values := words [0, tag + 1, tag ^^^ 2 ^ 255, 2 ^ 256 - 1]
        if kind == "tag" then values.map Malformation.tag else values.map Malformation.tagCut
    | "tail" => (words [0, 32, n - 32 + 1, 2 ^ 256 - 1]).map Malformation.tail
    | "narrow" => [.narrow]
    | _ => []).filter valid

def applicableKinds (returned : Returned) : List String :=
  malformationKinds.filter fun kind => !(malformationBank returned kind).isEmpty

/-- Typed when the delivery draw is 0, otherwise raw with a kind uniformly
among those that apply and then an entry of its bank uniformly. -/
def generatedReturned (seed : Seed) : Returned :=
  let choices := shapeChoices seed
  let selector := choices.getD 2 0
  let length := if selector < lengthBank.length then lengthBank.getD selector 0 else choices.getD 3 0
  let typed := canonicalReturned ⟨generatedKind seed, length, choices.getD 4 0, .typed⟩
  if choices.getD 5 0 == 0 then typed
  else match applicableKinds typed with
    | [] => typed
    | kinds =>
        let kind := kinds.getD (choices.getD 6 0 % kinds.length) "truncate"
        let entries := malformationBank typed kind
        match entries.getD (choices.getD 7 0 % entries.length) (.truncate 0) with
        | malformation => {typed with delivery := .raw malformation}

/-- Three inputs from the boundary bank. -/
def sequenceBounds : List Nat := [10, 10, 10]

def sequenceChoices (seed : Seed) : List Nat := boundedDraws seed 0x7265742d73657173 sequenceBounds

def blockTransactions (seed : Seed) (first : Nat) : List Transaction :=
  (sequenceChoices seed).zipIdx.map fun (choice, index) =>
    ⟨"tx-" ++ toString (first + index), boundaryInputs.getD choice Word.zero⟩

/-- The first `count` transactions of the seed's consecutive blocks. -/
def generatedTransactions (seed : Seed) (count : Nat := 3) : List Transaction :=
  Stateful.Sequence.blocks blockTransactions seed count

/-- The child's shell lies inside the budget with the step, which the complete
measure bounds again. -/
def generatedScenario (seed : Seed) (nodes : Nat) (revision : GeneratorRevision := .v1)
    (transactions : Nat := 3) : Except String (CheckedScenario × Json) := do
  Stateful.Sequence.checkCount transactions
  let returned := generatedReturned seed
  let shell := CallReturn.childShellNodes returned
  unless nodes ≤ maxStepNodes && shell < nodes do
    throw "node budget is too small for the call-return child or exceeds 512"
  let (step, stepOrigin) ← Aggregate.generatedFunction seed (nodes - shell) revision
  let some plan := CheckedPlan.ofParts? step returned | throw "generated call-return plan failed full Core admission"
  let scenario ← checkedScenario plan (generatedTransactions seed transactions)
  unless budgetNodes scenario.plan ≤ nodes do throw "call-return child exceeds its requested node budget"
  return (scenario, Stateful.Sequence.recordCount (Json.mkObj [
    ("kind", toJson "call-return-generated"), ("seed", toJson (toString seed.toNat)),
    ("finalSeed", ← stepOrigin.getObjVal? "finalSeed"), ("maxProgramNodes", toJson nodes),
    ("stepOrigin", stepOrigin), ("shapeChoices", toJson (shapeChoices seed)),
    ("sequenceChoices", toJson (Stateful.Sequence.blockChoices sequenceChoices seed transactions))]) transactions)

private def rowStatus (row : Json) : Option String := (row.getObjValAs? String "status").toOption

/-- The history must complete with the model's outcomes. -/
def validateGenerated (scenario : CheckedScenario) (fuel : Nat) : Except String Unit := do
  Aggregate.inputSensitive scenario.plan.step fuel
  let observed := observe scenario Solcore.Synthesis.Stateful.NestedCallExecution.fixtureBindings fuel
  let rows ← observed.getObjValAs? (List Json) "transactions"
  unless (← observed.getObjValAs? String "status") = "complete" do
    if rows.any (fun row => rowStatus row == some "out-of-fuel") then throw "call-return history exhausted Core fuel"
    else throw "call-return history stopped without a permitted root completion"
  let some expected := Stateful.CallReturnExecution.model scenario.plan fuel scenario.transactions
    | throw "call-return history exhausted Core fuel"
  unless rows.map rowStatus == expected.map (fun row => some (if row.reverted then "reverted" else "returned")) do
    throw "call-return history did not follow its prescribed outcomes"

def generateCases (firstSeed : Seed) (nodes count attempts fuel : Nat)
    (revision : GeneratorRevision := .v1) (transactions : Nat := 3) : Json := Id.run do
  let mut cases : Array Json := #[]
  let mut excluded : Array Json := #[]
  let mut attempted := 0
  for index in List.range attempts do
    if cases.size < count then
      attempted := attempted + 1
      let seed := Seed.ofNat (firstSeed.toNat + index)
      let result := do
        unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
        let (scenario, origin) ← generatedScenario seed nodes revision transactions
        let emitted ← (emit scenario.plan).mapError reprStr
        validateGenerated scenario fuel
        makeCase scenario emitted (origin.setObjVal! "validationFuel" (toJson fuel)) fuel revision (revision.caseMask seed)
      match result with
      | .error error =>
          let resource := error == "boundary observation exhausted Core fuel" ||
            error == "call-return history exhausted Core fuel" || error == "call-return model exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "call-return-profile"),
            ("reason", toJson error),
            ("code", toJson (if resource then "validation-out-of-fuel" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok case => cases := cases.push case
  return Json.mkObj [("schema", toJson corpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

/-! ### Reductions -/

/-- A tuple's extra Words, then `bytes` and enums by their shape. -/
def kindWeight : Kind → Nat
  | .tuple extra => extra
  | .bytes => 3
  | .enum shape => 4 + EnumReturn.shapeWeight shape

/-- Nothing for a typed delivery, otherwise one plus the malformation's
position in its kind's bank, or one plus the bank's size outside it. -/
def deliveryWeight (returned : Returned) : Nat :=
  match returned.delivery with
  | .typed => 0
  | .raw malformation =>
      let bank := malformationBank returned (kindOf malformation)
      1 + (bank.idxOf? malformation).getD bank.length

def inputWeight (scenario : CheckedScenario) : Nat :=
  scenario.transactions.foldl (fun total transaction => total + transaction.input.val) 0

def scenarioComplexity (scenario : CheckedScenario) : Complexity := complexity scenario.plan.childProgram.body

/-- Transaction count, the kind, the delivery, the `bytes` length, the child's
size and literals, then the inputs. Every axis is a natural number and the
comparison is strictly lexicographic. -/
def StrictlySmaller (candidate source : CheckedScenario) : Prop :=
  candidate.transactions.length < source.transactions.length ∨
  (candidate.transactions.length = source.transactions.length ∧
    (kindWeight candidate.plan.returned.kind < kindWeight source.plan.returned.kind ∨
    (kindWeight candidate.plan.returned.kind = kindWeight source.plan.returned.kind ∧
      (deliveryWeight candidate.plan.returned < deliveryWeight source.plan.returned ∨
      (deliveryWeight candidate.plan.returned = deliveryWeight source.plan.returned ∧
        (candidate.plan.returned.length < source.plan.returned.length ∨
        (candidate.plan.returned.length = source.plan.returned.length ∧
          ((scenarioComplexity candidate).StrictlySmaller (scenarioComplexity source) ∨
          (scenarioComplexity candidate = scenarioComplexity source ∧
            inputWeight candidate < inputWeight source)))))))))

instance (candidate source : CheckedScenario) : Decidable (StrictlySmaller candidate source) := by
  unfold StrictlySmaller
  infer_instance

structure Reduction (source : CheckedScenario) where private mk ::
  candidate : CheckedScenario
  sameHelperCount : candidate.plan.step.helpers.length = source.plan.step.helpers.length
  sameBindings : Aggregate.bindingInventory candidate.plan.step = Aggregate.bindingInventory source.plan.step
  stableIds : (candidate.transactions.map (·.id)).Sublist (source.transactions.map (·.id))
  strict : StrictlySmaller candidate source

private def sealReduction (source : CheckedScenario) (step : Aggregates.CheckedDAG) (returned : Returned)
    (transactions : List Transaction) : Option (Reduction source) := do
  let plan ← CheckedPlan.ofParts? step returned
  let candidate ← (checkedScenario plan transactions).toOption
  if count : candidate.plan.step.helpers.length = source.plan.step.helpers.length then
    if bindings : Aggregate.bindingInventory candidate.plan.step = Aggregate.bindingInventory source.plan.step then
      if ids : (candidate.transactions.map (·.id)).Sublist (source.transactions.map (·.id)) then
        if strict : StrictlySmaller candidate source then some ⟨candidate, count, bindings, ids, strict⟩
        else none
      else none
    else none
  else none

/-- The returned value made canonical, with its malformation kept only when it
still applies. -/
def reanchor (returned : Returned) : Returned :=
  let typed := canonicalReturned {returned with delivery := .typed}
  match returned.delivery with
  | .typed => typed
  | .raw malformation => if malformation.valid typed then {typed with delivery := .raw malformation} else typed

private def moveDown (index value : Nat) : Nat := if value > index then value - 1 else value

/-- The next narrower fields: two Words to one, one Word to none and `bytes`
to none. -/
private def narrower : EnumPayload → Option EnumPayload
  | .twoWords => some .oneWord
  | .oneWord => some .noWords
  | .boundedBytes => some .noWords
  | .noWords => none

/-- Simpler kinds: an enum and `bytes` become a pair of Words, and a tuple
loses its last Word. -/
private def simpler : Kind → Option Kind
  | .enum _ | .bytes => some (.tuple 0)
  | .tuple (extra + 1) => some (.tuple extra)
  | .tuple 0 => none

/-- One-transaction removals, a dropped or earlier malformation, a shorter
length, a simpler kind, dropped and narrowed enum constructors, step
reductions, then per transaction each boundary input. Candidates still need
execution to establish that they preserve a finding. -/
def reductions (source : CheckedScenario) : List (Reduction source) := Id.run do
  let returned := source.plan.returned
  let mut raw : List (Aggregates.CheckedDAG × Returned × List Transaction) := []
  -- Removing one transaction comes first, from the last back: a long
  -- sequence loses the tail beyond a difference before the candidate limit.
  for index in (List.range source.transactions.length).reverse do
    raw := raw ++ [(source.plan.step, returned,
      (source.transactions.zipIdx.filter (fun (_, current) => current != index)).map Prod.fst)]
  if let .raw malformation := returned.delivery then
    raw := raw ++ [(source.plan.step, {returned with delivery := .typed}, source.transactions)]
    let bank := malformationBank returned (kindOf malformation)
    for earlier in bank.take ((bank.idxOf? malformation).getD bank.length) do
      raw := raw ++ [(source.plan.step, {returned with delivery := .raw earlier}, source.transactions)]
  for shorter in [0, returned.length / 2] do
    if shorter < returned.length then
      raw := raw ++ [(source.plan.step, reanchor {returned with length := shorter}, source.transactions)]
  if let some kind := simpler returned.kind then
    raw := raw ++ [(source.plan.step, reanchor {returned with kind, length := 0, choice := 0}, source.transactions)]
  if let .enum shape := returned.kind then
    for index in List.range shape.constructors.length do
      if index != returned.choice then
        if let some smaller := EnumReturn.Shape.ofList? (shape.constructors.eraseIdx index) then
          raw := raw ++ [(source.plan.step,
            reanchor {returned with kind := .enum smaller, choice := moveDown index returned.choice}, source.transactions)]
    for index in List.range shape.constructors.length do
      if let some constructor := shape.constructors[index]? then
        if let some payload := narrower constructor.payload then
          if let some smaller := EnumReturn.Shape.ofList? (shape.constructors.set index {constructor with payload}) then
            raw := raw ++ [(source.plan.step, reanchor {returned with kind := .enum smaller}, source.transactions)]
  for reduced in Aggregate.reductions ⟨source.plan.step, Word.zero⟩ do
    raw := raw ++ [(reduced.candidate.function, returned, source.transactions)]
  for index in List.range source.transactions.length do
    for input in boundaryInputs do
      let transactions := source.transactions.zipIdx.map fun (transaction, current) =>
        if current == index then {transaction with input := input} else transaction
      raw := raw ++ [(source.plan.step, returned, transactions)]
  let mut seen : List String := []
  let mut result := []
  for (step, returned, transactions) in raw do
    if let some reduced := sealReduction source step returned transactions then
      let identity := (Json.mkObj [("plan", planJson reduced.candidate.plan),
        ("transactions", toJson (reduced.candidate.transactions.map fun tx => toString tx.input.val ++ tx.id))]).compress
      if !seen.contains identity then
        seen := identity :: seen
        result := result ++ [reduced]
  return result

private def sequenceJson (transactions : List Transaction) : Json :=
  toJson (transactions.map fun tx => Json.mkObj [("id", toJson tx.id), ("input", toJson (toString tx.input.val))])

private def reducedOrigin (parent : CheckedScenario) : Json := Json.mkObj [
  ("kind", toJson "reduced"), ("parentPlan", planJson parent.plan),
  ("parentPrograms", programsJson parent.plan), ("parentTransactions", sequenceJson parent.transactions)]

def replayCase (json : Json) (fuel : Nat) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
  let admitted ← caseProgram json
  let provenance ← json.getObjVal? "provenance"
  let revision := savedRevision provenance
  let mask ← savedMask provenance revision
  for (name, expected) in [
      ("generatorVersion", revision.version), ("profileVersion", profileVersion),
      ("functionVersion", CallReturn.childVersion), ("parentVersion", CallReturn.parentVersion),
      ("templateVersion", templateVersion),
      ("stepProfileVersion", Aggregate.profileVersion), ("stepFunctionVersion", Aggregates.version),
      ("stepTemplateVersion", Aggregate.templateVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let emitted ← (emit admitted.plan).mapError reprStr
  let sources ← json.getObjVal? "sources"
  unless (← sources.getObjValAs? String "parent") = emitted.parentSource &&
      (← sources.getObjValAs? String "child") = emitted.childSource &&
      sources == Json.mkObj [("parent", toJson emitted.parentSource), ("child", toJson emitted.childSource)] do
    throw "saved sources differ from call-return plan emission"
  unless (← json.getObjVal? "contracts") == contractsJson do throw "saved contract metadata differs from call-return wrappers"
  unless (← provenance.getObjVal? "features") == toJson admitted.plan.step.features do throw "saved features differ from checked step"
  let kind ← origin.getObjValAs? String "kind"
  if kind = "call-return-generated" then
    let seedText ← origin.getObjValAs? String "seed"
    unless seedText.length ≤ 20 do throw "invalid saved seed"
    let some seed := seedText.toNat? | throw "invalid saved seed"
    unless seed < 2 ^ 64 && toString seed = seedText do throw "noncanonical saved seed"
    unless mask == revision.caseMask (Seed.ofNat seed) do throw "saved swarm mask differs from its generation seed"
    let (expected, expectedOrigin) ← generatedScenario (Seed.ofNat seed) (← origin.getObjValAs? Nat "maxProgramNodes") revision
      (← Stateful.Sequence.savedCount origin)
    let validationFuel ← origin.getObjValAs? Nat "validationFuel"
    unless validationFuel ≤ 10000000 do throw "saved validation fuel exceeds limit"
    unless origin == expectedOrigin.setObjVal! "validationFuel" (toJson validationFuel) do
      throw "saved origin differs from generated call-return provenance"
    unless planJson expected.plan == planJson admitted.plan &&
        sequenceJson expected.transactions == sequenceJson admitted.transactions do
      throw "saved plan or transaction sequence differs from its generation seed"
    validateGenerated expected validationFuel
  else if kind = "imported" then
    unless origin == Json.mkObj [("kind", toJson "imported")] do throw "noncanonical imported origin"
  else if kind = "reduced" then
    let parentPlan ← checkedPlan (← origin.getObjVal? "parentPlan")
    let parentTransactions ← decodeSequence (← origin.getObjVal? "parentTransactions")
    let parent ← checkedScenario parentPlan parentTransactions
    unless (← origin.getObjVal? "parentPrograms") == programsJson parent.plan do
      throw "reduction parent programs differ from their plan"
    unless (sealReduction parent admitted.plan.step admitted.plan.returned admitted.transactions).isSome do
      throw "reduction does not preserve bindings/IDs or decrease the complete scenario"
    unless origin == reducedOrigin parent do throw "noncanonical reduced origin"
  else throw "unsupported call-return case origin"
  makeCase admitted emitted origin fuel revision mask

def shrinkCases (json : Json) (limit fuel : Nat) : Except String Json := do
  let _ ← replayCase json fuel
  let source ← caseProgram json
  -- Reductions inherit the parent case's recorded G0 revision and swarm mask.
  let provenance ← json.getObjVal? "provenance"
  let revision := savedRevision provenance
  let mask ← savedMask provenance revision
  let cases ← ((reductions source).take limit).mapM fun reduced =>
    emitCase reduced.candidate (reducedOrigin source) fuel revision mask
  return Json.mkObj [("schema", toJson corpusSchema), ("cases", toJson cases)]

end Solcore.Synthesis.Source.CallReturn
