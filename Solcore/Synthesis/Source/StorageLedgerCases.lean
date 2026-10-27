import Solcore.Synthesis.Source.StorageCases
import Solcore.Synthesis.Source.StorageLedgerEmitter
import Solcore.Synthesis.Stateful.StorageLedgerExecution

/-! Sender-keyed ledger cases retain one original host-aware Core contract and
an ordered history of `(sender, flags, recipient, amount, input)` transactions
from three fixed senders. Their declared slots are derived from the senders and
recipients: the counter and the entry slot of each. Reductions remove
transactions, move one transaction to an earlier sender, replace recipients,
amounts or inputs by bank values, or simplify flags; a candidate rederives its
declared slots. Saved outputs are never an oracle. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.StorageLedger
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.ContractRuntime (Address addressToWord)
open Solcore.Synthesis.Core.StorageLedger (CheckedPlan hashNodes)
open Solcore.Synthesis.Stateful.StorageLedgerExecution (Transaction Bindings senders senderSlot)
open Solcore.Synthesis.Stateful.StorageMappingExecution (entrySlot)

def caseSchema : String := "solcore-lean.semantic-ledger-case.v1"
def planSchema : String := "solcore-lean.ledger-plan.v1"
def profileVersion : String := "stateful-ledger-v1/ledger-sequence-seed-v1"
def templateVersion : String := "sender-credit-bounded-transfer-revert-odd-flags-v1"
def ledgerCorpusSchema : String := "solcore-lean.semantic-ledger-corpus.v1"

abbrev boundaryInputs := Storage.boundaryInputs

/-- Recipients: the three senders, so value flows between them, the zero key,
the largest address and the largest Word. -/
def recipientBank : List Word :=
  senders.map addressToWord ++ [Word.zero, Word.ofNatModulo (2 ^ 160 - 1), Word.maximum]

/-- Bounded transfer amounts. -/
def amountBank : List Word :=
  [Word.zero, Word.ofNatModulo 1, Word.ofNatModulo 7, Word.ofNatModulo (2 ^ 64 - 1), Word.ofNatModulo (2 ^ 64),
    Word.ofNatModulo (2 ^ 70)]

/-- A sender's position in the fixed order; reductions only move towards zero. -/
def senderPosition (sender : Address) : Nat := senders.idxOf sender

/-- Complete contracts may exceed the step budget by the fixed Keccak closure. -/
def maxProgramNodes : Nat := 512 + hashNodes

def validTransactions (transactions : List Transaction) : Prop :=
  1 ≤ transactions.length ∧ transactions.length ≤ Stateful.Sequence.maxTransactions ∧
    (transactions.map (·.id)).Nodup ∧ transactions.all (fun tx => Storage.validId tx.id) = true ∧
    transactions.all (fun tx => senders.contains tx.sender) = true

instance (transactions : List Transaction) : Decidable (validTransactions transactions) := by
  unfold validTransactions
  infer_instance

structure CheckedScenario where private mk ::
  plan : CheckedPlan
  transactions : List Transaction
  valid : validTransactions transactions
  bounded : Wire.programNodes plan.program ≤ maxProgramNodes

def CheckedScenario.program (scenario : CheckedScenario) : Wire.Program := scenario.plan.program

def CheckedScenario.observedSlots (scenario : CheckedScenario) : List Word :=
  Solcore.Synthesis.Stateful.StorageLedgerExecution.observedSlots scenario.transactions

def checkedScenario (plan : CheckedPlan) (transactions : List Transaction) : Except String CheckedScenario := do
  if valid : validTransactions transactions then
    if bounded : Wire.programNodes plan.program ≤ maxProgramNodes then
      return ⟨plan, transactions, valid, bounded⟩
    else throw "canonical ledger contract exceeds its case limit"
  else throw s!"ledger scenario requires 1..{Stateful.Sequence.maxTransactions} transactions with distinct valid IDs from the fixed senders"

def transactionJson (tx : Transaction) : Json := Json.mkObj [
  ("id", toJson tx.id), ("sender", toJson (toString tx.sender.val)), ("flags", toJson (toString tx.flags.val)),
  ("recipient", toJson (toString tx.recipient.val)), ("amount", toJson (toString tx.amount.val)),
  ("input", toJson (toString tx.input.val)),
  ("calldata", toJson (Solcore.Synthesis.Stateful.StorageLedgerExecution.calldata tx.flags tx.recipient tx.amount
    tx.input)),
  ("value", toJson "0")]

def transactionsJson (transactions : List Transaction) : Json := toJson (transactions.map transactionJson)

private def wordField (row : Json) (key : String) : Except String Word := do
  let text ← row.getObjValAs? String key
  unless text.length ≤ 78 do throw ("transaction " ++ key ++ " exceeds a Word")
  Input.inputWord text

private def senderField (row : Json) : Except String Address := do
  let value ← wordField row "sender"
  let some sender := senders.find? (fun sender => addressToWord sender == value) |
    throw "transaction sender is not one of the fixed senders"
  return sender

def decodeTransactions (json : Json) : Except String (List Transaction) := do
  let rows ← json.getArr?
  unless 1 ≤ rows.size && rows.size ≤ Stateful.Sequence.maxTransactions do
    throw s!"transaction count must be between 1 and {Stateful.Sequence.maxTransactions}"
  let transactions ← rows.toList.mapM fun row => do
    let transaction : Transaction := ⟨← row.getObjValAs? String "id", ← senderField row, ← wordField row "flags",
      ← wordField row "recipient", ← wordField row "amount", ← wordField row "input"⟩
    unless row == transactionJson transaction do
      throw "transaction differs from canonical ID, sender, flags, recipient, amount, input, calldata or zero-value metadata"
    return transaction
  unless validTransactions transactions do
    throw "ledger scenario requires distinct valid transaction IDs"
  return transactions

def planJson (plan : CheckedPlan) : Json := Json.mkObj [
  ("schema", toJson planSchema), ("stepProgram", Wire.encodeProgram plan.step.program)]

def checkedPlan (json : Json) : Except String CheckedPlan := do
  unless (← json.getObjValAs? String "schema") = planSchema do throw "unsupported ledger plan schema"
  let step ← Aggregate.checkedFunction (← json.getObjVal? "stepProgram")
  let some plan := CheckedPlan.ofStep? step | throw "ledger contract failed full host-Core admission"
  unless json == planJson plan do throw "ledger plan differs from its canonical checked representation"
  unless Wire.programNodes plan.program ≤ maxProgramNodes do throw "ledger contract exceeds its case limit"
  return plan

def contractJson (emitted : EmittedProgram) : Json := Json.mkObj [
  ("name", toJson emitted.contractName), ("method", toJson emitted.methodName),
  ("signature", toJson emitted.methodSignature), ("selector", toJson selector),
  ("deployPath", toJson emitted.deployPath), ("runtimePath", toJson emitted.runtimePath),
  ("constructorCalldata", toJson "0x")]

def initialStateJson : Json := Json.mkObj [("storage", toJson ([] : List Json))]

def observedSlotsJson (scenario : CheckedScenario) : Json :=
  Solcore.Synthesis.Stateful.KeyedStorageExecution.slotsJson scenario.observedSlots

def makeCase (scenario : CheckedScenario) (emitted : EmittedProgram) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1) (mask : FeatureMask := FeatureMask.all) : Json :=
  Json.mkObj [
    ("schema", toJson caseSchema), ("ledgerPlan", planJson scenario.plan),
    ("program", Wire.encodeProgram scenario.program), ("source", toJson emitted.source),
    ("transactions", transactionsJson scenario.transactions),
    ("initialState", initialStateJson), ("observedSlots", observedSlotsJson scenario),
    ("provenance", Json.mkObj <| swarmField revision mask ++ [
      ("origin", origin), ("profileVersion", toJson profileVersion),
      ("functionVersion", toJson Solcore.Synthesis.Core.StorageLedger.version),
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
  let emitted ← (emit scenario.plan).mapError reprStr
  return makeCase scenario emitted origin fuel revision mask

/-- Every origin must reconstruct the fixed host contract, including imports and
reductions. An arbitrary well-typed program is not an admissible replacement. -/
def caseProgram (json : Json) : Except String CheckedScenario := do
  unless (← json.getObjValAs? String "schema") = caseSchema do throw "unsupported semantic ledger case schema"
  let plan ← checkedPlan (← json.getObjVal? "ledgerPlan")
  let transactions ← decodeTransactions (← json.getObjVal? "transactions")
  let program ← (Wire.decodeProgramWithBudget
    {maxDepth := 512, maxNodes := maxProgramNodes, maxIntegerBytes := 4096}
    (← json.getObjVal? "program")).mapError (fun
      | .protocol error => error.toJson.compress
      | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)
  unless Wire.encodeProgram program == Wire.encodeProgram plan.program do
    throw "saved original Core program differs from the canonical ledger plan"
  unless (← json.getObjVal? "initialState") == initialStateJson do throw "initial storage must be empty"
  unless (← json.getObjValAs? Nat "executionFuel") ≤ 10000000 do throw "saved execution fuel exceeds limit"
  let scenario ← checkedScenario plan transactions
  unless (← json.getObjVal? "observedSlots") == observedSlotsJson scenario do
    throw "observed slots must be the counter and every sender's and recipient's entry slot"
  return scenario

def aliasCatalog : List String := ["self-transfer", "received-then-sent", "repeated-sender"]

/-- Static aliasing among the transactions' keys, in catalog order. This is
syntax of the sequence; it does not claim that an aliasing transfer committed. -/
def aliases (transactions : List Transaction) : List String :=
  aliasCatalog.filter fun kind =>
    if kind = "self-transfer" then transactions.any fun tx => tx.recipient == addressToWord tx.sender
    else if kind = "received-then-sent" then
      transactions.zipIdx.any fun (earlier, i) => transactions.zipIdx.any fun (later, j) =>
        i < j && earlier.recipient == addressToWord later.sender
    else (transactions.map (·.sender)).eraseDups.length < transactions.length

def distinctSenders (transactions : List Transaction) : Nat := (transactions.map (·.sender)).eraseDups.length

def observe (scenario : CheckedScenario) (bindings : Bindings) (fuel : Nat) : Json :=
  Solcore.Synthesis.Stateful.StorageLedgerExecution.observe scenario.plan scenario.transactions bindings fuel

def reverts (tx : Transaction) : Bool := tx.flags.val % 2 == 1

def parityFlags (odd : Bool) : Word := if odd then Word.ofNatModulo 1 else Word.zero

/-- Odd-flags positions of the four generated patterns. Even flags may still
revert for an insufficient balance. -/
def parityPatterns : List (List Bool) :=
  [[false, false, false], [false, true, false], [true, false, false], [false, false, true]]

/-- Three senders, recipients, amounts and inputs, then the flags pattern. Each
choice uses the high half of one draw from a separate stream: the low bits of a
power-of-two LCG have short periods. -/
def sequenceChoices (seed : Seed) : List Nat := Id.run do
  let mut state := Seed.ofNat (seed.toNat ^^^ 0x6c65646765722d76)
  let mut values : Array Nat := #[]
  for bound in [3, 3, 3, 6, 6, 6, 6, 6, 6, 6, 6, 6, 4] do
    let (value, next) := state.draw
    values := values.push (value.toNat / 2 ^ 32 % bound)
    state := next
  return values.toList

def generatedParities (seed : Seed) : List Bool :=
  parityPatterns.getD ((sequenceChoices seed).getD 12 0) [false, false, false]

def blockTransactions (seed : Seed) (first : Nat) : List Transaction :=
  let choices := sequenceChoices seed
  (generatedParities seed).zipIdx.map fun (odd, index) =>
    ⟨"tx-" ++ toString (first + index), senders.getD (choices.getD index 0) ⟨0, by decide⟩, parityFlags odd,
      recipientBank.getD (choices.getD (3 + index) 0) Word.zero, amountBank.getD (choices.getD (6 + index) 0) Word.zero,
      boundaryInputs.getD (choices.getD (9 + index) 0) Word.zero⟩

/-- The first `count` transactions of the seed's consecutive blocks. -/
def generatedTransactions (seed : Seed) (count : Nat := 3) : List Transaction :=
  Stateful.Sequence.blocks blockTransactions seed count

private def flagsName (odd : Bool) : String := if odd then "odd" else "even"

/-- Reserve the measured protocol wrapper before generating its independent
step; the fixed Keccak closure lies outside the step budget, and the complete
contract is remeasured as the final budget authority. -/
def generatedScenario (seed : Seed) (nodes : Nat) (revision : GeneratorRevision := .v1)
    (transactions : Nat := 3) : Except String (CheckedScenario × Json) := do
  Stateful.Sequence.checkCount transactions
  unless nodes ≤ 512 && Solcore.Synthesis.Core.StorageLedger.programOverhead < nodes do
    throw "node budget is too small for the ledger wrapper or exceeds 512"
  let (step, stepOrigin) ← Aggregate.generatedFunction seed
    (nodes - Solcore.Synthesis.Core.StorageLedger.programOverhead) revision
  let some plan := CheckedPlan.ofStep? step | throw "generated ledger plan failed full Core admission"
  let scenario ← checkedScenario plan (generatedTransactions seed transactions)
  unless Wire.programNodes scenario.program ≤ nodes + hashNodes do
    throw "ledger contract exceeds its requested node budget"
  return (scenario, Stateful.Sequence.recordCount (Json.mkObj [
    ("kind", toJson "ledger-generated"), ("seed", toJson (toString seed.toNat)),
    ("finalSeed", ← stepOrigin.getObjVal? "finalSeed"), ("maxProgramNodes", toJson nodes),
    ("stepOrigin", stepOrigin),
    ("sequenceChoices", toJson (Stateful.Sequence.blockChoices sequenceChoices seed transactions)),
    ("sequenceFlags", toJson ((Stateful.Sequence.blocks (fun blockSeed _ => generatedParities blockSeed) seed
      transactions).map flagsName))]) transactions)

private def decimal (row : Json) (key : String) : Except String Nat := do
  let some value := (← row.getObjValAs? String key).toNat? | throw ("invalid " ++ key)
  return value

/-- The committed value of one declared slot in a storage list. -/
private def storageValue (storage : Json) (slot : Word) : Except String Nat := do
  let rows ← storage.getArr?
  let some entry := rows.find? (fun entry => (entry.getObjValAs? String "slot").toOption == some (toString slot.val)) |
    throw "committed slot missing"
  decimal entry "value"

private def wordOutput (value : Nat) : String :=
  Solcore.ContractRuntime.encodeBytesText (Solcore.ContractRuntime.encodeWordBytesBE (Word.ofNatModulo value))

/-- The ledger protocol, checked from each transaction and the prior committed
slots without evaluating the step. Odd flags revert; an even-flag revert is an
insufficient balance whose payload, the credited balance, is below the amount;
a revert keeps every declared slot. A returned transaction increments the
counter, changes no declared slot but the counter and the two entries, and
returns their sum. A transfer to another key credits the recipient with
exactly the amount and leaves a sender entry the amount does not wrap; a
self-transfer leaves an entry of at least the amount. -/
def checkProtocol (scenario : CheckedScenario) (history : Json) : Except String (List String) := do
  unless (← history.getObjValAs? String "status") = "complete" do
    throw "ledger history exhausted Core fuel"
  let rows ← history.getObjValAs? (List Json) "transactions"
  unless rows.length == scenario.transactions.length do throw "ledger history length changed"
  let counter := Word.ofNatModulo Solcore.Synthesis.Core.StorageLedger.counterSlot
  let mut prior ← history.getObjVal? "initialStorage"
  let mut statuses : List String := []
  for (row, tx) in rows.zip scenario.transactions do
    let status ← row.getObjValAs? String "status"
    let committed ← row.getObjVal? "committedStorage"
    let output ← row.getObjValAs? String "output"
    if status == "reverted" then
      unless committed == prior do throw "a reverted ledger transaction changed the committed slots"
      unless reverts tx do
        let some payload := (Solcore.ContractRuntime.decodeBytesText? output).bind
            Solcore.ContractRuntime.decodeWordBytesBE? | throw "a ledger revert payload is not one Word"
        unless payload.val < tx.amount.val do
          throw "an even-flags ledger revert did not report an insufficient balance"
    else if status == "returned" then
      if reverts tx then throw "an odd-flags ledger transaction returned"
      let source := senderSlot tx.sender
      let target := entrySlot tx.recipient
      let count ← storageValue committed counter
      unless count == ((← storageValue prior counter) + 1) % 2 ^ 256 do
        throw "a returned ledger transaction did not increment the counter"
      let sent ← storageValue committed source
      let received ← storageValue committed target
      if source == target then
        unless tx.amount.val ≤ sent do throw "a self-transfer left an entry below the amount"
      else
        unless received == ((← storageValue prior target) + tx.amount.val) % 2 ^ 256 do
          throw "a returned ledger transfer did not credit the recipient with the amount"
        unless sent + tx.amount.val < 2 ^ 256 do throw "a returned ledger transfer wrapped the sender's entry"
      for slot in scenario.observedSlots do
        unless slot == counter || slot == source || slot == target do
          unless (← storageValue committed slot) == (← storageValue prior slot) do
            throw "a returned ledger transaction changed another declared slot"
      unless output == wordOutput ((sent + received + count) % 2 ^ 256) do
        throw "a returned ledger transaction did not return its entries and counter"
    else throw "ledger history contains an incomplete transaction"
    prior := committed
    statuses := statuses ++ [status]
  return statuses

def validateGenerated (scenario : CheckedScenario) (fuel : Nat) : Except String Unit := do
  Aggregate.inputSensitive scenario.plan.step fuel
  let observed := observe scenario Solcore.Synthesis.Stateful.StorageExecution.fixtureBindings fuel
  let _ ← checkProtocol scenario observed

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
        return (scenario, origin.setObjVal! "validationFuel" (toJson fuel), emitted)
      match result with
      | .error error =>
          let resource := error == "boundary observation exhausted Core fuel" ||
            error == "ledger history exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "ledger-profile"),
            ("reason", toJson error),
            ("code", toJson (if resource then "validation-out-of-fuel" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok (scenario, origin, emitted) =>
          cases := cases.push (makeCase scenario emitted origin fuel revision (revision.caseMask seed))
  return Json.mkObj [("schema", toJson ledgerCorpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

/-- Sender positions, flags, recipients, amounts and inputs all contribute; a
recipient reduction can remove aliasing. -/
def valueWeight (scenario : CheckedScenario) : Nat :=
  scenario.transactions.foldl (fun total transaction =>
    total + senderPosition transaction.sender + transaction.flags.val + transaction.recipient.val +
      transaction.amount.val + transaction.input.val) 0

/-- Transaction count, distinct senders, complete program size/literals, then
runtime sender positions, flags, recipients, amounts and inputs. Every axis is
a natural number and the comparison is lexicographic. -/
def StrictlySmaller (candidate source : CheckedScenario) : Prop :=
  candidate.transactions.length < source.transactions.length ∨
  (candidate.transactions.length = source.transactions.length ∧
    (distinctSenders candidate.transactions < distinctSenders source.transactions ∨
    (distinctSenders candidate.transactions = distinctSenders source.transactions ∧
      ((complexity candidate.program.body).StrictlySmaller (complexity source.program.body) ∨
      (complexity candidate.program.body = complexity source.program.body ∧
        valueWeight candidate < valueWeight source)))))

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
  let candidate ← (checkedScenario plan transactions).toOption
  if count : candidate.plan.step.helpers.length = source.plan.step.helpers.length then
    if bindings : Aggregate.bindingInventory candidate.plan.step = Aggregate.bindingInventory source.plan.step then
      if ids : (candidate.transactions.map (·.id)).Sublist (source.transactions.map (·.id)) then
        if strict : StrictlySmaller candidate source then some ⟨candidate, count, bindings, ids, strict⟩
        else none
      else none
    else none
  else none

private def replaceAt (transactions : List Transaction) (index : Nat) (change : Transaction → Transaction) :
    List Transaction :=
  transactions.zipIdx.map fun (transaction, current) => if current == index then change transaction else transaction

/-- Step reductions, then per transaction: removal, an earlier sender, bank
replacements of the recipient, the amount and the input, and flags reduced to
their parity or with the revert bit cleared. Candidates still need execution to
preserve a finding. -/
def reductions (source : CheckedScenario) : List (Reduction source) := Id.run do
  let step := source.plan.step
  let mut raw : List (Aggregates.CheckedDAG × List Transaction) := []
  -- Removing one transaction comes first, from the last back: a long
  -- sequence loses the tail beyond a difference before the candidate limit.
  for index in (List.range source.transactions.length).reverse do
    raw := raw ++ [(step,
      (source.transactions.zipIdx.filter (fun (_, current) => current != index)).map Prod.fst)]
  for reduced in Aggregate.reductions ⟨step, Word.zero⟩ do
    raw := raw ++ [(reduced.candidate.function, source.transactions)]
  for (transaction, index) in source.transactions.zipIdx do
    for sender in senders.take (senderPosition transaction.sender) do
      raw := raw ++ [(step, replaceAt source.transactions index fun tx => {tx with sender := sender})]
    for recipient in recipientBank do
      raw := raw ++ [(step, replaceAt source.transactions index fun tx => {tx with recipient := recipient})]
    for amount in amountBank do
      raw := raw ++ [(step, replaceAt source.transactions index fun tx => {tx with amount := amount})]
    for input in boundaryInputs do
      raw := raw ++ [(step, replaceAt source.transactions index fun tx => {tx with input := input})]
    raw := raw ++ [(step, replaceAt source.transactions index fun tx =>
      {tx with flags := tx.flags.bitAnd (Word.ofNatModulo 1)})]
    raw := raw ++ [(step, replaceAt source.transactions index fun tx =>
      {tx with flags := tx.flags.bitAnd (Word.ofNatModulo 1).bitNot})]
  let mut seen : List String := []
  let mut result := []
  for (step, transactions) in raw do
    if let some reduced := sealReduction source step transactions then
      let identity := (Json.mkObj [("plan", planJson reduced.candidate.plan),
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
      ("functionVersion", Solcore.Synthesis.Core.StorageLedger.version), ("templateVersion", templateVersion),
      ("stepProfileVersion", Aggregate.profileVersion), ("stepFunctionVersion", Aggregates.version),
      ("stepTemplateVersion", Aggregate.templateVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let emitted ← (emit admitted.plan).mapError reprStr
  unless (← json.getObjValAs? String "source") = emitted.source do throw "saved source differs from ledger plan emission"
  unless (← json.getObjVal? "contract") == contractJson emitted do throw "saved contract metadata differs from ledger wrapper"
  unless (← provenance.getObjVal? "features") == toJson admitted.plan.step.features do throw "saved features differ from checked step"
  let kind ← origin.getObjValAs? String "kind"
  if kind = "ledger-generated" then
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
      throw "saved origin differs from generated ledger provenance"
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
    unless (sealReduction parent admitted.plan.step admitted.transactions).isSome do
      throw "reduction does not preserve bindings/IDs or decrease the complete scenario"
    unless origin == Json.mkObj [("kind", toJson "reduced"), ("parentPlan", planJson parent.plan),
        ("parentTransactions", transactionsJson parent.transactions)] do
      throw "noncanonical reduced origin"
  else throw "unsupported ledger case origin"
  return makeCase admitted emitted origin fuel revision mask

def shrinkCases (json : Json) (limit fuel : Nat) : Except String Json := do
  let _ ← replayCase json fuel
  let source ← caseProgram json
  let origin := Json.mkObj [("kind", toJson "reduced"), ("parentPlan", planJson source.plan),
    ("parentTransactions", transactionsJson source.transactions)]
  -- Reductions inherit the parent case's recorded G0 revision and swarm mask.
  let provenance ← json.getObjVal? "provenance"
  let revision := savedRevision provenance
  let mask ← savedMask provenance revision
  let cases ← ((reductions source).take limit).mapM fun reduced => emitCase reduced.candidate origin fuel revision mask
  return Json.mkObj [("schema", toJson ledgerCorpusSchema), ("cases", toJson cases)]

end Solcore.Synthesis.Source.StorageLedger
