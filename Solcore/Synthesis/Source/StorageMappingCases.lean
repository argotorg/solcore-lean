import Solcore.Synthesis.Source.StorageCases
import Solcore.Synthesis.Source.StorageMappingEmitter
import Solcore.Synthesis.Stateful.StorageMappingExecution

/-! Keccak-mapping cases retain one original host-aware Core contract and an
ordered history of `(flags, key, input)` transactions. Their declared slots
are derived from the keys: the counter and the entry slots of each key and its
wrapping successor. Reductions remove transactions, replace keys or inputs by
bank values, or simplify flags; a candidate rederives its declared slots.
Saved outputs are never an oracle. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.StorageMapping
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.Synthesis.Core.StorageMapping (CheckedPlan hashNodes)
open Solcore.Synthesis.Stateful.StorageMappingExecution (Transaction Bindings entrySlot)

def caseSchema : String := "solcore-lean.semantic-mapping-case.v1"
def planSchema : String := "solcore-lean.mapping-plan.v1"
def profileVersion : String := "stateful-mapping-v1/mapping-sequence-seed-v1"
def templateVersion : String := "keccak-entry-successor-counter-revert-odd-flags-v1"
def mappingCorpusSchema : String := "solcore-lean.semantic-mapping-corpus.v1"

abbrev boundaryInputs := Storage.boundaryInputs

/-- Mapping keys: two successor pairs, the high bit and the maximum, whose
successor wraps to zero, so generated sequences alias entries naturally. -/
def keyBank : List Word :=
  [Word.zero, Word.ofNatModulo 1, Word.ofNatModulo 6, Word.ofNatModulo 7, Word.ofNatModulo (2 ^ 255), Word.maximum]

/-- Complete contracts may exceed the step budget by the fixed Keccak closure. -/
def maxProgramNodes : Nat := 512 + hashNodes

def validTransactions (transactions : List Transaction) : Prop :=
  1 ≤ transactions.length ∧ transactions.length ≤ 3 ∧
    (transactions.map (·.id)).Nodup ∧ transactions.all (fun tx => Storage.validId tx.id) = true

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
  Solcore.Synthesis.Stateful.StorageMappingExecution.observedSlots scenario.transactions

def checkedScenario (plan : CheckedPlan) (transactions : List Transaction) : Except String CheckedScenario := do
  if valid : validTransactions transactions then
    if bounded : Wire.programNodes plan.program ≤ maxProgramNodes then
      return ⟨plan, transactions, valid, bounded⟩
    else throw "canonical mapping contract exceeds its case limit"
  else throw "mapping scenario requires 1..3 transactions with distinct valid IDs"

def transactionJson (tx : Transaction) : Json := Json.mkObj [
  ("id", toJson tx.id), ("flags", toJson (toString tx.flags.val)), ("key", toJson (toString tx.key.val)),
  ("input", toJson (toString tx.input.val)),
  ("calldata", toJson (Solcore.Synthesis.Stateful.StorageMappingExecution.calldata tx.flags tx.key tx.input)),
  ("value", toJson "0")]

def transactionsJson (transactions : List Transaction) : Json := toJson (transactions.map transactionJson)

private def wordField (row : Json) (key : String) : Except String Word := do
  let text ← row.getObjValAs? String key
  unless text.length ≤ 78 do throw ("transaction " ++ key ++ " exceeds a Word")
  Input.inputWord text

def decodeTransactions (json : Json) : Except String (List Transaction) := do
  let rows ← json.getArr?
  unless 1 ≤ rows.size && rows.size ≤ 3 do throw "transaction count must be between 1 and 3"
  let transactions ← rows.toList.mapM fun row => do
    let transaction : Transaction := ⟨← row.getObjValAs? String "id", ← wordField row "flags",
      ← wordField row "key", ← wordField row "input"⟩
    unless row == transactionJson transaction do
      throw "transaction differs from canonical ID, flags, key, input, calldata or zero-value metadata"
    return transaction
  unless validTransactions transactions do
    throw "mapping scenario requires distinct valid transaction IDs"
  return transactions

def planJson (plan : CheckedPlan) : Json := Json.mkObj [
  ("schema", toJson planSchema), ("stepProgram", Wire.encodeProgram plan.step.program)]

def checkedPlan (json : Json) : Except String CheckedPlan := do
  unless (← json.getObjValAs? String "schema") = planSchema do throw "unsupported mapping plan schema"
  let step ← Aggregate.checkedFunction (← json.getObjVal? "stepProgram")
  let some plan := CheckedPlan.ofStep? step | throw "mapping contract failed full host-Core admission"
  unless json == planJson plan do throw "mapping plan differs from its canonical checked representation"
  unless Wire.programNodes plan.program ≤ maxProgramNodes do throw "mapping contract exceeds its case limit"
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
    (revision : GeneratorRevision := .v1) : Json :=
  Json.mkObj [
    ("schema", toJson caseSchema), ("mappingPlan", planJson scenario.plan),
    ("program", Wire.encodeProgram scenario.program), ("source", toJson emitted.source),
    ("transactions", transactionsJson scenario.transactions),
    ("initialState", initialStateJson), ("observedSlots", observedSlotsJson scenario),
    ("provenance", Json.mkObj [
      ("origin", origin), ("profileVersion", toJson profileVersion),
      ("functionVersion", toJson Solcore.Synthesis.Core.StorageMapping.version),
      ("templateVersion", toJson templateVersion),
      ("stepProfileVersion", toJson Aggregate.profileVersion),
      ("stepFunctionVersion", toJson Aggregates.version),
      ("stepTemplateVersion", toJson Aggregate.templateVersion),
      ("generatorVersion", toJson revision.version),
      ("emitterVersion", toJson emitterVersion), ("wrapperVersion", toJson wrapperVersion),
      ("features", toJson scenario.plan.step.features)]),
    ("contract", contractJson emitted), ("executionFuel", toJson fuel)]

def emitCase (scenario : CheckedScenario) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
  let emitted ← (emit scenario.plan).mapError reprStr
  return makeCase scenario emitted origin fuel revision

/-- Every origin must reconstruct the fixed host contract, including imports and
reductions. An arbitrary well-typed program is not an admissible replacement. -/
def caseProgram (json : Json) : Except String CheckedScenario := do
  unless (← json.getObjValAs? String "schema") = caseSchema do throw "unsupported semantic mapping case schema"
  let plan ← checkedPlan (← json.getObjVal? "mappingPlan")
  let transactions ← decodeTransactions (← json.getObjVal? "transactions")
  let program ← (Wire.decodeProgramWithBudget
    {maxDepth := 512, maxNodes := maxProgramNodes, maxIntegerBytes := 4096}
    (← json.getObjVal? "program")).mapError (fun
      | .protocol error => error.toJson.compress
      | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)
  unless Wire.encodeProgram program == Wire.encodeProgram plan.program do
    throw "saved original Core program differs from the canonical mapping plan"
  unless (← json.getObjVal? "initialState") == initialStateJson do throw "initial storage must be empty"
  unless (← json.getObjValAs? Nat "executionFuel") ≤ 10000000 do throw "saved execution fuel exceeds limit"
  let scenario ← checkedScenario plan transactions
  unless (← json.getObjVal? "observedSlots") == observedSlotsJson scenario do
    throw "observed slots must be the counter and every key's and successor's entry slot"
  return scenario

def aliasCatalog : List String := ["repeated-key", "successor-key", "wrapped-successor"]

/-- Static entry aliasing among the transaction keys, in catalog order. This is
syntax of the sequence; it does not claim that an aliasing write committed. -/
def aliases (transactions : List Transaction) : List String :=
  let keys := transactions.map (·.key)
  let successor := fun (key : Word) => key.add (Word.ofNatModulo 1)
  aliasCatalog.filter fun kind =>
    if kind = "repeated-key" then keys.eraseDups.length < keys.length
    else if kind = "successor-key" then
      keys.zipIdx.any fun (left, i) => keys.zipIdx.any fun (right, j) => i != j && successor left == right
    else keys.contains Word.maximum

def observe (scenario : CheckedScenario) (bindings : Bindings) (fuel : Nat) : Json :=
  Solcore.Synthesis.Stateful.StorageMappingExecution.observe scenario.plan scenario.transactions bindings fuel

def reverts (tx : Transaction) : Bool := tx.flags.val % 2 == 1

def parityFlags (odd : Bool) : Word := if odd then Word.ofNatModulo 1 else Word.zero

/-- Revert positions of the four generated completion patterns. -/
def parityPatterns : List (List Bool) :=
  [[false, false, false], [false, true, false], [true, false, false], [false, false, true]]

/-- Three keys, three inputs, then the completion pattern. Each choice uses the
high half of one draw from a separate stream: the low bits of a power-of-two
LCG have short periods. -/
def sequenceChoices (seed : Seed) : List Nat := Id.run do
  let mut state := Seed.ofNat (seed.toNat ^^^ 0x6d617070696e672d)
  let mut values : Array Nat := #[]
  for bound in [6, 6, 6, 6, 6, 6, 4] do
    let (value, next) := state.draw
    values := values.push (value.toNat / 2 ^ 32 % bound)
    state := next
  return values.toList

def generatedParities (seed : Seed) : List Bool :=
  parityPatterns.getD ((sequenceChoices seed).getD 6 0) [false, false, false]

def generatedTransactions (seed : Seed) : List Transaction :=
  let choices := sequenceChoices seed
  (generatedParities seed).zipIdx.map fun (odd, index) =>
    ⟨"tx-" ++ toString index, parityFlags odd, keyBank.getD (choices.getD index 0) Word.zero,
      boundaryInputs.getD (choices.getD (3 + index) 0) Word.zero⟩

private def statusName (odd : Bool) : String := if odd then "reverted" else "returned"

/-- Reserve the measured protocol wrapper before generating its independent
step; the fixed Keccak closure lies outside the step budget, and the complete
contract is remeasured as the final budget authority. -/
def generatedScenario (seed : Seed) (nodes : Nat) (revision : GeneratorRevision := .v1) :
    Except String (CheckedScenario × Json) := do
  unless nodes ≤ 512 && Solcore.Synthesis.Core.StorageMapping.programOverhead < nodes do
    throw "node budget is too small for the mapping wrapper or exceeds 512"
  let (step, stepOrigin) ← Aggregate.generatedFunction seed
    (nodes - Solcore.Synthesis.Core.StorageMapping.programOverhead) revision
  let some plan := CheckedPlan.ofStep? step | throw "generated mapping plan failed full Core admission"
  let scenario ← checkedScenario plan (generatedTransactions seed)
  unless Wire.programNodes scenario.program ≤ nodes + hashNodes do
    throw "mapping contract exceeds its requested node budget"
  return (scenario, Json.mkObj [
    ("kind", toJson "mapping-generated"), ("seed", toJson (toString seed.toNat)),
    ("finalSeed", ← stepOrigin.getObjVal? "finalSeed"), ("maxProgramNodes", toJson nodes),
    ("stepOrigin", stepOrigin), ("sequenceChoices", toJson (sequenceChoices seed)),
    ("sequenceCompletions", toJson ((generatedParities seed).map statusName))])

private def decimal (row : Json) (key : String) : Except String Nat := do
  let some value := (← row.getObjValAs? String key).toNat? | throw ("invalid " ++ key)
  return value

private def slotValue (row : Json) (slot : Word) (field : String := "committedStorage") : Except String Nat := do
  let rows ← row.getObjValAs? (List Json) field
  let some entry := rows.find? (fun entry => (entry.getObjValAs? String "slot").toOption == some (toString slot.val)) |
    throw "committed slot missing"
  decimal entry "value"

/-- Original Core must complete every transaction with the prescribed
completion. A returned transaction increments the counter and returns the
committed entries of its key and successor plus the counter; a revert keeps
the prior slots. -/
def checkProtocol (scenario : CheckedScenario) (history : Json) : Except String (List String) := do
  unless (← history.getObjValAs? String "status") = "complete" do
    throw "mapping history exhausted Core fuel"
  let rows ← history.getObjValAs? (List Json) "transactions"
  unless rows.length == scenario.transactions.length do throw "mapping history length changed"
  let counter := Word.ofNatModulo Solcore.Synthesis.Core.StorageMapping.counterSlot
  let mut prior ← history.getObjVal? "initialStorage"
  let mut count ← slotValue history counter "initialStorage"
  let mut statuses : List String := []
  for (row, tx) in rows.zip scenario.transactions do
    let status ← row.getObjValAs? String "status"
    unless status == statusName (reverts tx) do throw "mapping history did not follow its flags parities"
    let committed ← row.getObjVal? "committedStorage"
    if status == "reverted" then
      unless committed == prior do throw "a reverted mapping transaction changed the committed slots"
    else
      let next ← slotValue row counter
      unless next == (count + 1) % 2 ^ 256 do throw "a returned mapping transaction did not increment the counter"
      let sum := ((← slotValue row (entrySlot tx.key)) + (← slotValue row (entrySlot (tx.key.add (Word.ofNatModulo 1)))) +
        next) % 2 ^ 256
      unless (← row.getObjValAs? String "output") ==
          Solcore.ContractRuntime.encodeBytesText (Solcore.ContractRuntime.encodeWordBytesBE (Word.ofNatModulo sum)) do
        throw "a returned mapping transaction did not return its committed entries and counter"
      count := next
    prior := committed
    statuses := statuses ++ [status]
  return statuses

def validateGenerated (scenario : CheckedScenario) (fuel : Nat) : Except String Unit := do
  Aggregate.inputSensitive scenario.plan.step fuel
  let observed := observe scenario Solcore.Synthesis.Stateful.StorageExecution.fixtureBindings fuel
  let statuses ← checkProtocol scenario observed
  unless statuses == scenario.transactions.map (fun tx => statusName (reverts tx)) do
    throw "mapping history did not follow its prescribed flags parities"

def generateCases (firstSeed : Seed) (nodes count attempts fuel : Nat)
    (revision : GeneratorRevision := .v1) : Json := Id.run do
  let mut cases : Array Json := #[]
  let mut excluded : Array Json := #[]
  let mut attempted := 0
  for index in List.range attempts do
    if cases.size < count then
      attempted := attempted + 1
      let seed := Seed.ofNat (firstSeed.toNat + index)
      let result := do
        unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
        let (scenario, origin) ← generatedScenario seed nodes revision
        let emitted ← (emit scenario.plan).mapError reprStr
        validateGenerated scenario fuel
        return (scenario, origin.setObjVal! "validationFuel" (toJson fuel), emitted)
      match result with
      | .error error =>
          let resource := error == "boundary observation exhausted Core fuel" ||
            error == "mapping history exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "mapping-profile"),
            ("reason", toJson error),
            ("code", toJson (if resource then "validation-out-of-fuel" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok (scenario, origin, emitted) =>
          cases := cases.push (makeCase scenario emitted origin fuel revision)
  return Json.mkObj [("schema", toJson mappingCorpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

/-- Flags, keys and inputs all contribute; a key reduction can remove aliasing. -/
def valueWeight (scenario : CheckedScenario) : Nat :=
  scenario.transactions.foldl (fun total transaction =>
    total + transaction.flags.val + transaction.key.val + transaction.input.val) 0

/-- Transaction count, complete program size/literals, then runtime flags, keys
and inputs. Every axis is a natural number and the comparison is
lexicographic. -/
def StrictlySmaller (candidate source : CheckedScenario) : Prop :=
  candidate.transactions.length < source.transactions.length ∨
  (candidate.transactions.length = source.transactions.length ∧
    ((complexity candidate.program.body).StrictlySmaller (complexity source.program.body) ∨
    (complexity candidate.program.body = complexity source.program.body ∧
      valueWeight candidate < valueWeight source)))

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

/-- Step reductions, then per transaction: removal, bank replacements of the
key and the input, and flags reduced to their parity or with the revert bit
cleared. Candidates still need execution to preserve a finding. -/
def reductions (source : CheckedScenario) : List (Reduction source) := Id.run do
  let step := source.plan.step
  let mut raw : List (Aggregates.CheckedDAG × List Transaction) := []
  for reduced in Aggregate.reductions ⟨step, Word.zero⟩ do
    raw := raw ++ [(reduced.candidate.function, source.transactions)]
  for index in List.range source.transactions.length do
    raw := raw ++ [(step, (source.transactions.zipIdx.filter (fun (_, current) => current != index)).map Prod.fst)]
    for key in keyBank do
      raw := raw ++ [(step, replaceAt source.transactions index fun tx => {tx with key := key})]
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
  for (name, expected) in [
      ("generatorVersion", revision.version), ("profileVersion", profileVersion),
      ("functionVersion", Solcore.Synthesis.Core.StorageMapping.version), ("templateVersion", templateVersion),
      ("stepProfileVersion", Aggregate.profileVersion), ("stepFunctionVersion", Aggregates.version),
      ("stepTemplateVersion", Aggregate.templateVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let emitted ← (emit admitted.plan).mapError reprStr
  unless (← json.getObjValAs? String "source") = emitted.source do throw "saved source differs from mapping plan emission"
  unless (← json.getObjVal? "contract") == contractJson emitted do throw "saved contract metadata differs from mapping wrapper"
  unless (← provenance.getObjVal? "features") == toJson admitted.plan.step.features do throw "saved features differ from checked step"
  let kind ← origin.getObjValAs? String "kind"
  if kind = "mapping-generated" then
    let seedText ← origin.getObjValAs? String "seed"
    unless seedText.length ≤ 20 do throw "invalid saved seed"
    let some seed := seedText.toNat? | throw "invalid saved seed"
    unless seed < 2 ^ 64 && toString seed = seedText do throw "noncanonical saved seed"
    let (expected, expectedOrigin) ← generatedScenario (Seed.ofNat seed) (← origin.getObjValAs? Nat "maxProgramNodes") revision
    let validationFuel ← origin.getObjValAs? Nat "validationFuel"
    unless validationFuel ≤ 10000000 do throw "saved validation fuel exceeds limit"
    unless origin == expectedOrigin.setObjVal! "validationFuel" (toJson validationFuel) do
      throw "saved origin differs from generated mapping provenance"
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
  else throw "unsupported mapping case origin"
  return makeCase admitted emitted origin fuel revision

def shrinkCases (json : Json) (limit fuel : Nat) : Except String Json := do
  let _ ← replayCase json fuel
  let source ← caseProgram json
  let origin := Json.mkObj [("kind", toJson "reduced"), ("parentPlan", planJson source.plan),
    ("parentTransactions", transactionsJson source.transactions)]
  -- Reductions inherit the parent case's recorded G0 revision.
  let revision := savedRevision (← json.getObjVal? "provenance")
  let cases ← ((reductions source).take limit).mapM fun reduced => emitCase reduced.candidate origin fuel revision
  return Json.mkObj [("schema", toJson mappingCorpusSchema), ("cases", toJson cases)]

end Solcore.Synthesis.Source.StorageMapping
