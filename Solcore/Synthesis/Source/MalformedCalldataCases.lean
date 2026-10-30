import Solcore.Synthesis.Source.DynamicArrayCases
import Solcore.Synthesis.Stateful.MalformedCalldataExecution

/-! Malformed-calldata cases retain the std-modeling original Core contract
around a checked aggregate step and an ordered history of dynamic-array calls,
each with one malformation of its calldata. The compiled contract is the
dynamic-array one, emitted from the same step. Every transaction records its
malformation, the calldata it sends and the outcome std prescribes for those
bytes. Reductions remove transactions, simplify the step, drop or simplify a
malformation, and then reduce elements and flags. Saved outputs are never an
oracle. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.MalformedCalldata
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.ContractRuntime (encodeBytesText encodeWordBytesBE)
open Solcore.Synthesis.Core.MalformedCalldata (CheckedPlan)
open Solcore.Synthesis.Stateful.MalformedCalldataExecution (Malformation Transaction Bindings stdRejection?)

def caseSchema : String := "solcore-lean.semantic-malformed-calldata-case.v1"
def planSchema : String := "solcore-lean.malformed-calldata-plan.v1"
def profileVersion : String := "stateful-malformed-calldata-v1/malformation-sequence-seed-v2"
def templateVersion : String := "std-dispatch-array-fold-slots-count-revert-odd-flags-v1"
def corpusSchema : String := "solcore-lean.semantic-malformed-calldata-corpus.v1"

abbrev boundaryInputs := Storage.boundaryInputs
abbrev emitterVersion := DynamicArray.emitterVersion
abbrev wrapperVersion := DynamicArray.wrapperVersion

/-- Every malformation kind, in catalog order. -/
def malformationKinds : List String := ["none", "short", "selector", "truncate", "trailing", "offset", "length"]

def kindOf : Malformation → String
  | .none => "none"
  | .short _ => "short"
  | .selector _ => "selector"
  | .truncate _ => "truncate"
  | .trailing _ _ => "trailing"
  | .offset _ => "offset"
  | .length _ => "length"

def patternNames : List String := ["zeros", "ones", "ramp"]

def canonicalSize (tx : Transaction) : Nat :=
  (Solcore.Synthesis.Stateful.MalformedCalldataExecution.canonicalBytes tx).size

def validTransaction (tx : Transaction) : Bool :=
  Storage.validId tx.id && tx.values.length ≤ Solcore.Synthesis.Core.MalformedCalldata.maxElements &&
    tx.malformation.valid (canonicalSize tx) &&
    (Solcore.Synthesis.Stateful.MalformedCalldataExecution.inputBytes tx).size ≤
      Solcore.Synthesis.Stateful.MalformedCalldataExecution.maxCalldata

def validTransactions (transactions : List Transaction) : Prop :=
  1 ≤ transactions.length ∧ transactions.length ≤ Stateful.Sequence.maxTransactions ∧
    (transactions.map (·.id)).Nodup ∧ transactions.all validTransaction = true

instance (transactions : List Transaction) : Decidable (validTransactions transactions) := by
  unfold validTransactions
  infer_instance

structure CheckedScenario where private mk ::
  plan : CheckedPlan
  transactions : List Transaction
  valid : validTransactions transactions
  bounded : Wire.programNodes plan.program ≤ 512

def CheckedScenario.program (scenario : CheckedScenario) : Wire.Program := scenario.plan.program

def checkedScenario (plan : CheckedPlan) (transactions : List Transaction) : Except String CheckedScenario := do
  if valid : validTransactions transactions then
    if bounded : Wire.programNodes plan.program ≤ 512 then
      return ⟨plan, transactions, valid, bounded⟩
    else throw "canonical malformed-calldata contract exceeds the 512-node case limit"
  else throw s!"malformed-calldata scenario requires 1..{Stateful.Sequence.maxTransactions} transactions with distinct valid IDs, at most three elements and a valid malformation of at most 1 KiB each"

def malformationJson : Malformation → Json
  | .none => Json.mkObj [("kind", toJson "none")]
  | .short bytes => Json.mkObj [("kind", toJson "short"), ("bytes", toJson bytes)]
  | .selector mask => Json.mkObj [("kind", toJson "selector"), ("mask", toJson (toString mask))]
  | .truncate kept => Json.mkObj [("kind", toJson "truncate"), ("kept", toJson kept)]
  | .trailing count pattern => Json.mkObj [("kind", toJson "trailing"), ("count", toJson count),
      ("pattern", toJson (patternNames.getD pattern "ramp"))]
  | .offset value => Json.mkObj [("kind", toJson "offset"), ("value", toJson (toString value.val))]
  | .length value => Json.mkObj [("kind", toJson "length"), ("value", toJson (toString value.val))]

/-- An error selector as its four bytes. -/
def selectorText (selector : Nat) : String :=
  encodeBytesText (ByteArray.mk #[(selector / 2 ^ 24 % 256).toUInt8, (selector / 2 ^ 16 % 256).toUInt8,
    (selector / 2 ^ 8 % 256).toUInt8, (selector % 256).toUInt8])

def prescribed (tx : Transaction) : Option Nat :=
  stdRejection? (Solcore.Synthesis.Stateful.MalformedCalldataExecution.inputBytes tx)

def transactionJson (tx : Transaction) : Json := Json.mkObj [
  ("id", toJson tx.id), ("flags", toJson (toString tx.flags.val)),
  ("values", toJson (tx.values.map fun value => toString value.val)),
  ("malformation", malformationJson tx.malformation),
  ("calldata", toJson (Solcore.Synthesis.Stateful.MalformedCalldataExecution.calldata tx)),
  ("stdRejection", match prescribed tx with
    | some selector => toJson (selectorText selector)
    | none => Json.null),
  ("value", toJson "0")]

def transactionsJson (transactions : List Transaction) : Json := toJson (transactions.map transactionJson)

private def word (text : String) : Except String Word := do
  unless text.length ≤ 78 do throw "transaction Word exceeds 78 digits"
  Input.inputWord text

private def natural (json : Json) (key : String) : Except String Nat := do
  let value ← json.getObjValAs? Nat key
  unless value ≤ 2 ^ 32 do throw ("malformation " ++ key ++ " is out of range")
  return value

def decodeMalformation (json : Json) : Except String Malformation := do
  let kind ← json.getObjValAs? String "kind"
  if kind = "none" then return .none
  else if kind = "short" then return .short (← natural json "bytes")
  else if kind = "selector" then
    let text ← json.getObjValAs? String "mask"
    unless text.length ≤ 10 do throw "selector mask exceeds 32 bits"
    let some mask := text.toNat? | throw "invalid selector mask"
    return .selector mask
  else if kind = "truncate" then return .truncate (← natural json "kept")
  else if kind = "trailing" then
    let name ← json.getObjValAs? String "pattern"
    let some pattern := patternNames.idxOf? name | throw "unknown trailing pattern"
    return .trailing (← natural json "count") pattern
  else if kind = "offset" then return .offset (← word (← json.getObjValAs? String "value"))
  else if kind = "length" then return .length (← word (← json.getObjValAs? String "value"))
  else throw "unknown malformation kind"

def decodeTransactions (json : Json) : Except String (List Transaction) := do
  let rows ← json.getArr?
  unless 1 ≤ rows.size && rows.size ≤ Stateful.Sequence.maxTransactions do
    throw s!"transaction count must be between 1 and {Stateful.Sequence.maxTransactions}"
  let transactions ← rows.toList.mapM fun row => do
    let texts ← row.getObjValAs? (List String) "values"
    unless texts.length ≤ Solcore.Synthesis.Core.MalformedCalldata.maxElements do throw "array exceeds three elements"
    let transaction : Transaction := ⟨← row.getObjValAs? String "id",
      ← word (← row.getObjValAs? String "flags"), ← texts.mapM word,
      ← decodeMalformation (← row.getObjVal? "malformation")⟩
    unless validTransaction transaction do throw "invalid transaction ID, elements or malformation"
    unless row == transactionJson transaction do
      throw "transaction differs from canonical ID, flags, values, malformation, calldata, std outcome or zero-value metadata"
    return transaction
  unless validTransactions transactions do
    throw "malformed-calldata scenario requires distinct valid transaction IDs"
  return transactions

def planJson (plan : CheckedPlan) : Json := Json.mkObj [
  ("schema", toJson planSchema), ("stepProgram", Wire.encodeProgram plan.step.program)]

/-- The dynamic-array plan of the same step, whose source is the compiled contract. -/
def arrayPlan (plan : CheckedPlan) : Except String Solcore.Synthesis.Core.DynamicArray.CheckedPlan := do
  let some arrayPlan := Solcore.Synthesis.Core.DynamicArray.CheckedPlan.ofStep? plan.step |
    throw "the step fails the dynamic-array contract's admission"
  return arrayPlan

def checkedPlan (json : Json) : Except String CheckedPlan := do
  unless (← json.getObjValAs? String "schema") = planSchema do throw "unsupported malformed-calldata plan schema"
  let step ← Aggregate.checkedFunction (← json.getObjVal? "stepProgram")
  let some plan := CheckedPlan.ofStep? step | throw "malformed-calldata contract failed full host-Core admission"
  unless json == planJson plan do throw "malformed-calldata plan differs from its canonical checked representation"
  unless Wire.programNodes plan.program ≤ 512 do throw "malformed-calldata contract exceeds the 512-node case limit"
  let _ ← arrayPlan plan
  return plan

def emit (plan : CheckedPlan) : Except String EmittedProgram := do
  (DynamicArray.emit (← arrayPlan plan)).mapError reprStr

abbrev contractJson := DynamicArray.contractJson
abbrev initialStateJson := DynamicArray.initialStateJson

def makeCase (scenario : CheckedScenario) (emitted : EmittedProgram) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1) (mask : FeatureMask := FeatureMask.all) : Json :=
  Json.mkObj [
    ("schema", toJson caseSchema), ("malformedCalldataPlan", planJson scenario.plan),
    ("program", Wire.encodeProgram scenario.program), ("source", toJson emitted.source),
    ("transactions", transactionsJson scenario.transactions),
    ("initialState", initialStateJson),
    ("observedSlots", Solcore.Synthesis.Stateful.MalformedCalldataExecution.slotsJson),
    ("provenance", Json.mkObj <| swarmField revision mask ++ [
      ("origin", origin), ("profileVersion", toJson profileVersion),
      ("functionVersion", toJson Solcore.Synthesis.Core.MalformedCalldata.version),
      ("templateVersion", toJson templateVersion),
      ("stepProfileVersion", toJson Aggregate.profileVersion),
      ("stepFunctionVersion", toJson Aggregates.version),
      ("stepTemplateVersion", toJson Aggregate.templateVersion),
      ("generatorVersion", toJson revision.version),
      ("emitterVersion", toJson emitterVersion), ("wrapperVersion", toJson wrapperVersion),
      ("features", toJson scenario.plan.step.features)]),
    ("contract", contractJson emitted), ("executionFuel", toJson fuel)]

def emitCase (scenario : CheckedScenario) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1) (mask : FeatureMask := FeatureMask.all) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
  let emitted ← emit scenario.plan
  return makeCase scenario emitted origin fuel revision mask

/-- Every origin must reconstruct the fixed host contract, including imports and
reductions. An arbitrary well-typed program is not an admissible replacement. -/
def caseProgram (json : Json) : Except String CheckedScenario := do
  unless (← json.getObjValAs? String "schema") = caseSchema do throw "unsupported semantic malformed-calldata case schema"
  let plan ← checkedPlan (← json.getObjVal? "malformedCalldataPlan")
  let transactions ← decodeTransactions (← json.getObjVal? "transactions")
  let program ← (Wire.decodeProgramWithBudget
    {maxDepth := 512, maxNodes := 512, maxIntegerBytes := 4096}
    (← json.getObjVal? "program")).mapError (fun
      | .protocol error => error.toJson.compress
      | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)
  unless Wire.encodeProgram program == Wire.encodeProgram plan.program do
    throw "saved original Core program differs from the canonical malformed-calldata plan"
  unless (← json.getObjVal? "initialState") == initialStateJson do throw "initial storage must be empty"
  unless (← json.getObjVal? "observedSlots") == Solcore.Synthesis.Stateful.MalformedCalldataExecution.slotsJson do
    throw "observed slots must be zero through four"
  unless (← json.getObjValAs? Nat "executionFuel") ≤ 10000000 do throw "saved execution fuel exceeds limit"
  checkedScenario plan transactions

def observe (scenario : CheckedScenario) (bindings : Bindings) (fuel : Nat) : Json :=
  Solcore.Synthesis.Stateful.MalformedCalldataExecution.observe scenario.plan scenario.transactions bindings fuel

/-- The malformations a transaction with `length` elements and canonical size
`size` draws from, by kind: none; short calldata; wrong selectors; cuts inside
the head and the tail; trailing bytes; out-of-range, wrapping and overlapping
head offsets; and too long, wrapping, maximal, shorter and zero lengths. -/
def malformationBank (length size : Nat) : List (List Malformation) := [
  [.none],
  [.short 0, .short 1, .short 2, .short 3],
  [.selector 1, .selector (2 ^ 31), .selector (2 ^ 32 - 1)],
  [.truncate 4, .truncate 36, .truncate 67, .truncate 99, .truncate (size - 32), .truncate (size - 1)],
  [.trailing 1 0, .trailing 31 1, .trailing 32 2, .trailing 33 0, .trailing 64 1, .trailing 64 2],
  [.offset (Word.ofNatModulo (size - 3)), .offset (Word.ofNatModulo (size - 35)), .offset (Word.ofNatModulo (2 ^ 255)),
    .offset (Word.ofNatModulo (2 ^ 256 - 4)), .offset (Word.ofNatModulo (2 ^ 256 - 2)),
    .offset (Word.ofNatModulo (2 ^ 256 - 1)), .offset Word.zero, .offset (Word.ofNatModulo 32)],
  [.length (Word.ofNatModulo (length + 1)), .length (Word.ofNatModulo (2 ^ 251)),
    .length (Word.ofNatModulo (2 ^ 251 + 1)), .length (Word.ofNatModulo (2 ^ 256 - 1)),
    .length (Word.ofNatModulo (length - 1)), .length Word.zero]]

/-- A kind and a parameter for each of three transactions, each the high half of
one draw from a separate stream. The stream starts at SplitMix64's finalizer of
the seed xor its domain, so that consecutive seeds' choices do not step by a
fixed residue. -/
def malformationChoices (seed : Seed) : List Nat := Id.run do
  let mut state := Seed.ofUInt64 (GeneratorV2.mix (seed.toUInt64 ^^^ 0x6d616c666f726d2d))
  let mut values : Array Nat := #[]
  for bound in [7, 8, 7, 8, 7, 8] do
    let (value, next) := state.draw
    values := values.push (value.toNat / 2 ^ 32 % bound)
    state := next
  return values.toList

def blockTransactions (seed : Seed) (first : Nat) : List Transaction :=
  let choices := malformationChoices seed
  (DynamicArray.blockTransactions seed first).zipIdx.map fun (base, index) =>
    let size := (Solcore.Synthesis.Stateful.DynamicArrayExecution.inputBytes base.flags base.values).size
    let bank := (malformationBank base.values.length size).getD (choices.getD (2 * index) 0) [.none]
    ⟨base.id, base.flags, base.values, bank.getD (choices.getD (2 * index + 1) 0 % bank.length) .none⟩

/-- The first `count` transactions of the seed's consecutive blocks. -/
def generatedTransactions (seed : Seed) (count : Nat := 3) : List Transaction :=
  Stateful.Sequence.blocks blockTransactions seed count

private def statusName (odd : Bool) : String := if odd then "reverted" else "returned"

/-- The prescribed completion: the std rejection, or the body's flags parity. -/
def completionName (tx : Transaction) : String :=
  match prescribed tx with
  | some selector => "rejected:" ++ selectorText selector
  | none => statusName (tx.flags.val % 2 == 1)

/-- Reserve the measured host wrapper before generating its independent step;
the complete contract is remeasured as the final budget authority. -/
def generatedScenario (seed : Seed) (nodes : Nat) (revision : GeneratorRevision := .v1)
    (transactions : Nat := 3) : Except String (CheckedScenario × Json) := do
  Stateful.Sequence.checkCount transactions
  unless nodes ≤ 512 && Solcore.Synthesis.Core.MalformedCalldata.programOverhead < nodes do
    throw "node budget is too small for the malformed-calldata wrapper or exceeds 512"
  let (step, stepOrigin) ← Aggregate.generatedFunction seed
    (nodes - Solcore.Synthesis.Core.MalformedCalldata.programOverhead) revision
  let some plan := CheckedPlan.ofStep? step | throw "generated malformed-calldata plan failed full Core admission"
  let _ ← arrayPlan plan
  let scenario ← checkedScenario plan (generatedTransactions seed transactions)
  unless Wire.programNodes scenario.program ≤ nodes do throw "malformed-calldata contract exceeds its requested node budget"
  return (scenario, Stateful.Sequence.recordCount (Json.mkObj [
    ("kind", toJson "malformed-calldata-generated"), ("seed", toJson (toString seed.toNat)),
    ("finalSeed", ← stepOrigin.getObjVal? "finalSeed"), ("maxProgramNodes", toJson nodes),
    ("stepOrigin", stepOrigin),
    ("sequenceChoices", toJson (Stateful.Sequence.blockChoices DynamicArray.sequenceChoices seed transactions)),
    ("malformationChoices", toJson (Stateful.Sequence.blockChoices malformationChoices seed transactions)),
    ("sequenceCompletions", toJson (scenario.transactions.map completionName))]) transactions)

private def rowStatus (row : Json) : Option String := (row.getObjValAs? String "status").toOption

/-- Original Core must give every prescribed outcome: a std rejection reverts
with its selector Word and keeps the prior slots and whole storage; an
accepted transaction completes with its flags parity. -/
def validateGenerated (scenario : CheckedScenario) (fuel : Nat) : Except String Unit := do
  Aggregate.inputSensitive scenario.plan.step fuel
  let observed := observe scenario Solcore.Synthesis.Stateful.StorageExecution.fixtureBindings fuel
  unless (← observed.getObjValAs? String "status") = "complete" do
    throw "malformed-calldata history exhausted Core fuel"
  let rows ← observed.getObjValAs? (List Json) "transactions"
  unless rows.length == scenario.transactions.length do throw "malformed-calldata history length changed"
  let mut prior := (← observed.getObjVal? "initialStorage", ← observed.getObjVal? "initialAccountStorage")
  for (row, tx) in rows.zip scenario.transactions do
    let current := (← row.getObjVal? "committedStorage", ← row.getObjVal? "accountStorage")
    match prescribed tx with
    | some selector =>
        unless rowStatus row == some "reverted" &&
            (row.getObjValAs? String "output").toOption ==
              some (encodeBytesText (encodeWordBytesBE (Word.ofNatModulo selector))) do
          throw "original Core does not revert with the prescribed std selector"
        unless current == prior do throw "a std rejection changed the committed storage"
    | none =>
        unless rowStatus row == some (statusName (tx.flags.val % 2 == 1)) do
          throw "an accepted malformed-calldata transaction did not follow its flags parity"
    prior := current

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
        let emitted ← emit scenario.plan
        validateGenerated scenario fuel
        return (scenario, origin.setObjVal! "validationFuel" (toJson fuel), emitted)
      match result with
      | .error error =>
          let resource := error == "boundary observation exhausted Core fuel" ||
            error == "malformed-calldata history exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "malformed-calldata-profile"),
            ("reason", toJson error),
            ("code", toJson (if resource then "validation-out-of-fuel" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok (scenario, origin, emitted) =>
          cases := cases.push (makeCase scenario emitted origin fuel revision (revision.caseMask seed))
  return Json.mkObj [("schema", toJson corpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

/-- None weighs nothing; otherwise one plus the malformation's parameter. -/
def weight : Malformation → Nat
  | .none => 0
  | .short bytes => 1 + bytes
  | .selector mask => 1 + mask
  | .truncate kept => 1 + kept
  | .trailing count pattern => 1 + count + pattern
  | .offset value => 1 + value.val
  | .length value => 1 + value.val

def malformationWeight (scenario : CheckedScenario) : Nat :=
  scenario.transactions.foldl (fun total transaction => total + weight transaction.malformation) 0

def elementCount (scenario : CheckedScenario) : Nat :=
  scenario.transactions.foldl (fun total transaction => total + transaction.values.length) 0

def valueWeight (scenario : CheckedScenario) : Nat :=
  scenario.transactions.foldl (fun total transaction =>
    transaction.values.foldl (fun sum value => sum + value.val) (total + transaction.flags.val)) 0

/-- Transaction count, complete program size/literals, the malformation
weight, the number of array elements, then flags and element values. Every axis
is a natural number. -/
def StrictlySmaller (candidate source : CheckedScenario) : Prop :=
  candidate.transactions.length < source.transactions.length ∨
  (candidate.transactions.length = source.transactions.length ∧
    ((complexity candidate.program.body).StrictlySmaller (complexity source.program.body) ∨
    (complexity candidate.program.body = complexity source.program.body ∧
      (malformationWeight candidate < malformationWeight source ∨
      (malformationWeight candidate = malformationWeight source ∧
        (elementCount candidate < elementCount source ∨
        (elementCount candidate = elementCount source ∧ valueWeight candidate < valueWeight source)))))))

instance (candidate source : CheckedScenario) : Decidable (StrictlySmaller candidate source) := by
  unfold StrictlySmaller
  infer_instance

structure Reduction (source : CheckedScenario) where private mk ::
  candidate : CheckedScenario
  sameHelperCount : candidate.plan.step.helpers.length = source.plan.step.helpers.length
  sameBindings : Aggregate.bindingInventory candidate.plan.step = Aggregate.bindingInventory source.plan.step
  stableIds : (candidate.transactions.map (·.id)).Sublist (source.transactions.map (·.id))
  strict : StrictlySmaller candidate source

private def sealReduction (source : CheckedScenario) (step : Aggregates.CheckedDAG)
    (transactions : List Transaction) : Option (Reduction source) := do
  let plan ← CheckedPlan.ofStep? step
  let _ ← (arrayPlan plan).toOption
  let candidate ← (checkedScenario plan transactions).toOption
  if count : candidate.plan.step.helpers.length = source.plan.step.helpers.length then
    if bindings : Aggregate.bindingInventory candidate.plan.step = Aggregate.bindingInventory source.plan.step then
      if ids : (candidate.transactions.map (·.id)).Sublist (source.transactions.map (·.id)) then
        if strict : StrictlySmaller candidate source then some ⟨candidate, count, bindings, ids, strict⟩
        else none
      else none
    else none
  else none

private def replaceAt (transactions : List Transaction) (index : Nat) (change : Transaction → Transaction) : List Transaction :=
  transactions.zipIdx.map fun (transaction, current) => if current == index then change transaction else transaction

/-- Simpler malformations of the same kind, from the smallest parameter up. -/
def simpler (tx : Transaction) : List Malformation :=
  let size := canonicalSize tx
  let bank := (malformationBank tx.values.length size).getD
    (malformationKinds.idxOf (kindOf tx.malformation)) []
  let ordered := bank.mergeSort fun left right => weight left ≤ weight right
  ordered.filter (weight · < weight tx.malformation)

/-- One-transaction removals first, from the last back, then step reductions.
Then, for each transaction: no malformation, simpler malformations of its kind,
removal and bank replacement of each element, and bank flags. Candidates still
need execution to establish that they preserve a finding. -/
def reductions (source : CheckedScenario) : List (Reduction source) := Id.run do
  let mut raw : List (Aggregates.CheckedDAG × List Transaction) := []
  for index in (List.range source.transactions.length).reverse do
    raw := raw ++ [(source.plan.step,
      (source.transactions.zipIdx.filter (fun (_, current) => current != index)).map Prod.fst)]
  for reduced in Aggregate.reductions ⟨source.plan.step, Word.zero⟩ do
    raw := raw ++ [(reduced.candidate.function, source.transactions)]
  for (transaction, index) in source.transactions.zipIdx do
    raw := raw ++ [(source.plan.step, replaceAt source.transactions index fun tx => {tx with malformation := .none})]
    for malformation in simpler transaction do
      raw := raw ++ [(source.plan.step, replaceAt source.transactions index fun tx => {tx with malformation})]
    for position in List.range transaction.values.length do
      raw := raw ++ [(source.plan.step, replaceAt source.transactions index fun tx =>
        {tx with values := tx.values.eraseIdx position})]
    for position in List.range transaction.values.length do
      for value in boundaryInputs do
        raw := raw ++ [(source.plan.step, replaceAt source.transactions index fun tx =>
          {tx with values := tx.values.set position value})]
    for flags in boundaryInputs do
      raw := raw ++ [(source.plan.step, replaceAt source.transactions index fun tx => {tx with flags := flags})]
  let mut seen : List String := []
  let mut result := []
  for (step, transactions) in raw do
    if let some reduced := sealReduction source step transactions then
      let identity := (Json.mkObj [("program", Wire.encodeProgram reduced.candidate.program),
        ("transactions", transactionsJson reduced.candidate.transactions)]).compress
      if !seen.contains identity then
        seen := identity :: seen
        result := result ++ [reduced]
  return result

def replayCase (json : Json) (fuel : Nat) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
  let admitted ← caseProgram json
  let provenance ← json.getObjVal? "provenance"
  let revision := savedRevision provenance
  let mask ← savedMask provenance revision
  for (name, expected) in [
      ("generatorVersion", revision.version), ("profileVersion", profileVersion),
      ("functionVersion", Solcore.Synthesis.Core.MalformedCalldata.version), ("templateVersion", templateVersion),
      ("stepProfileVersion", Aggregate.profileVersion), ("stepFunctionVersion", Aggregates.version),
      ("stepTemplateVersion", Aggregate.templateVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let emitted ← emit admitted.plan
  unless (← json.getObjValAs? String "source") = emitted.source do
    throw "saved source differs from the dynamic-array emission of the step"
  unless (← json.getObjVal? "contract") == contractJson emitted do
    throw "saved contract metadata differs from the dynamic-array wrapper"
  unless (← provenance.getObjVal? "features") == toJson admitted.plan.step.features do throw "saved features differ from checked step"
  let kind ← origin.getObjValAs? String "kind"
  if kind = "malformed-calldata-generated" then
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
      throw "saved origin differs from generated malformed-calldata provenance"
    unless planJson expected.plan == planJson admitted.plan &&
        transactionsJson expected.transactions == transactionsJson admitted.transactions do
      throw "saved plan or transaction sequence differs from its generation seed"
    validateGenerated expected validationFuel
  else if kind = "imported" then
    unless origin == Json.mkObj [("kind", toJson "imported")] do throw "noncanonical imported origin"
  else if kind = "reduced" then
    let parentPlan ← checkedPlan (← origin.getObjVal? "parentPlan")
    let parentTransactions ← decodeTransactions (← origin.getObjVal? "parentTransactions")
    let parent ← checkedScenario parentPlan parentTransactions
    unless (← origin.getObjVal? "parentProgram") == Wire.encodeProgram parent.program do throw "reduction parent program differs from its plan"
    unless (sealReduction parent admitted.plan.step admitted.transactions).isSome do
      throw "reduction does not preserve bindings/IDs or decrease the complete scenario"
    unless origin == Json.mkObj [("kind", toJson "reduced"), ("parentPlan", planJson parent.plan),
        ("parentProgram", Wire.encodeProgram parent.program), ("parentTransactions", transactionsJson parent.transactions)] do
      throw "noncanonical reduced origin"
  else throw "unsupported malformed-calldata case origin"
  return makeCase admitted emitted origin fuel revision mask

def shrinkCases (json : Json) (limit fuel : Nat) : Except String Json := do
  let _ ← replayCase json fuel
  let source ← caseProgram json
  let origin := Json.mkObj [("kind", toJson "reduced"), ("parentPlan", planJson source.plan),
    ("parentProgram", Wire.encodeProgram source.program), ("parentTransactions", transactionsJson source.transactions)]
  -- Reductions inherit the parent case's recorded G0 revision and swarm mask.
  let provenance ← json.getObjVal? "provenance"
  let revision := savedRevision provenance
  let mask ← savedMask provenance revision
  let cases ← ((reductions source).take limit).mapM fun reduced => emitCase reduced.candidate origin fuel revision mask
  return Json.mkObj [("schema", toJson corpusSchema), ("cases", toJson cases)]

end Solcore.Synthesis.Source.MalformedCalldata
