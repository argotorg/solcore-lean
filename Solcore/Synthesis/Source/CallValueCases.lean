import Solcore.Synthesis.Source.StorageCases
import Solcore.Synthesis.Source.CallValueEmitter
import Solcore.Synthesis.Stateful.CallValueExecution

/-! Call-value cases retain one original host-aware Core contract, the value it
holds after deployment and an ordered history of `(flags, input, value)`
transactions. Values are bounded so that the funded local sender can always pay
them. Saved outputs and balances are never an execution oracle. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.CallValue
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.Synthesis.Core.CallValue (CheckedPlan)
open Solcore.Synthesis.Stateful.CallValueExecution (Transaction Bindings)

def caseSchema : String := "solcore-lean.semantic-call-value-case.v1"
def planSchema : String := "solcore-lean.call-value-plan.v1"
def profileVersion : String := "stateful-call-value-v1/value-sequence-seed-v1"
def templateVersion : String := "slot-step-value-total-revert-odd-flags-v1"
def valueCorpusSchema : String := "solcore-lean.semantic-call-value-corpus.v1"

abbrev boundaryInputs := Storage.boundaryInputs

/-- Call values: zero, small values, both sides of the 64-bit boundary and a
large value the funded local sender can still pay three times. -/
def valueBank : List Word :=
  [Word.zero, Word.ofNatModulo 1, Word.ofNatModulo 7, Word.ofNatModulo (2 ^ 64 - 1),
    Word.ofNatModulo (2 ^ 64), Word.ofNatModulo (2 ^ 70)]

def deploymentBank : List Word := [Word.zero, Word.ofNatModulo 5]

/-- Every single value, including the deployment value, and the total a
scenario sends are bounded by the local sender's funds. -/
def maxValue : Nat := 2 ^ 70
def maxTotal : Nat := 2 ^ 72

def totalValue (deploymentValue : Word) (transactions : List Transaction) : Nat :=
  transactions.foldl (fun total tx => total + tx.value.val) deploymentValue.val

def validTransactions (deploymentValue : Word) (transactions : List Transaction) : Prop :=
  1 ≤ transactions.length ∧ transactions.length ≤ 3 ∧
    (transactions.map (·.id)).Nodup ∧ transactions.all (fun tx => Storage.validId tx.id) = true ∧
    transactions.all (fun tx => tx.value.val ≤ maxValue) = true ∧
    totalValue deploymentValue transactions ≤ maxTotal

instance (deploymentValue : Word) (transactions : List Transaction) :
    Decidable (validTransactions deploymentValue transactions) := by
  unfold validTransactions
  infer_instance

structure CheckedScenario where private mk ::
  plan : CheckedPlan
  transactions : List Transaction
  valid : validTransactions plan.deploymentValue transactions
  bounded : Wire.programNodes plan.program ≤ 512

def CheckedScenario.program (scenario : CheckedScenario) : Wire.Program := scenario.plan.program

def checkedScenario (plan : CheckedPlan) (transactions : List Transaction) : Except String CheckedScenario := do
  if valid : validTransactions plan.deploymentValue transactions then
    if bounded : Wire.programNodes plan.program ≤ 512 then
      return ⟨plan, transactions, valid, bounded⟩
    else throw "canonical call-value contract exceeds the 512-node case limit"
  else throw "call-value scenario requires 1..3 transactions with distinct valid IDs, values of at most 2^70 and at most 2^72 in total"

def transactionJson (tx : Transaction) : Json := Json.mkObj [
  ("id", toJson tx.id), ("flags", toJson (toString tx.flags.val)), ("input", toJson (toString tx.input.val)),
  ("value", toJson (toString tx.value.val)),
  ("calldata", toJson (Solcore.Synthesis.Stateful.CallValueExecution.calldata tx.flags tx.input))]

def transactionsJson (transactions : List Transaction) : Json := toJson (transactions.map transactionJson)

private def wordField (row : Json) (key : String) : Except String Word := do
  let text ← row.getObjValAs? String key
  unless text.length ≤ 78 do throw ("transaction " ++ key ++ " exceeds a Word")
  Input.inputWord text

def decodeTransactions (json : Json) : Except String (List Transaction) := do
  let rows ← json.getArr?
  unless 1 ≤ rows.size && rows.size ≤ 3 do throw "transaction count must be between 1 and 3"
  let transactions ← rows.toList.mapM fun row => do
    let transaction : Transaction :=
      ⟨← row.getObjValAs? String "id", ← wordField row "flags", ← wordField row "input", ← wordField row "value"⟩
    unless row == transactionJson transaction do
      throw "transaction differs from canonical ID, flags, input, value or calldata"
    return transaction
  unless decide ((transactions.map (·.id)).Nodup) && transactions.all (fun tx => Storage.validId tx.id) do
    throw "call-value scenario requires distinct valid transaction IDs"
  return transactions

def planJson (plan : CheckedPlan) : Json := Json.mkObj [
  ("schema", toJson planSchema), ("stepProgram", Wire.encodeProgram plan.step.program),
  ("deploymentValue", toJson (toString plan.deploymentValue.val))]

def checkedPlan (json : Json) : Except String CheckedPlan := do
  unless (← json.getObjValAs? String "schema") = planSchema do throw "unsupported call-value plan schema"
  let step ← Aggregate.checkedFunction (← json.getObjVal? "stepProgram")
  let deploymentValue ← wordField json "deploymentValue"
  unless deploymentValue.val ≤ maxValue do throw "deployment value exceeds 2^70"
  let some plan := CheckedPlan.ofParts? step deploymentValue | throw "call-value contract failed full host-Core admission"
  unless json == planJson plan do throw "call-value plan differs from its canonical checked representation"
  unless Wire.programNodes plan.program ≤ 512 do throw "call-value contract exceeds the 512-node case limit"
  return plan

def contractJson (emitted : EmittedProgram) : Json := Json.mkObj [
  ("name", toJson emitted.contractName), ("method", toJson emitted.methodName),
  ("signature", toJson emitted.methodSignature), ("selector", toJson selector),
  ("deployPath", toJson emitted.deployPath), ("runtimePath", toJson emitted.runtimePath),
  ("constructorCalldata", toJson "0x")]

def initialStateJson : Json := Json.mkObj [("storage", toJson ([] : List Json))]

def observedSlotsJson : Json :=
  Solcore.Synthesis.Stateful.KeyedStorageExecution.slotsJson Solcore.Synthesis.Stateful.CallValueExecution.observedSlots

def makeCase (scenario : CheckedScenario) (emitted : EmittedProgram) (origin : Json) (fuel : Nat) : Json :=
  Json.mkObj [
    ("schema", toJson caseSchema), ("callValuePlan", planJson scenario.plan),
    ("program", Wire.encodeProgram scenario.program), ("source", toJson emitted.source),
    ("transactions", transactionsJson scenario.transactions),
    ("initialState", initialStateJson), ("observedSlots", observedSlotsJson),
    ("provenance", Json.mkObj [
      ("origin", origin), ("profileVersion", toJson profileVersion),
      ("functionVersion", toJson Solcore.Synthesis.Core.CallValue.version),
      ("templateVersion", toJson templateVersion),
      ("stepProfileVersion", toJson Aggregate.profileVersion),
      ("stepFunctionVersion", toJson Aggregates.version),
      ("stepTemplateVersion", toJson Aggregate.templateVersion),
      ("generatorVersion", toJson generatorVersion),
      ("emitterVersion", toJson emitterVersion), ("wrapperVersion", toJson wrapperVersion),
      ("features", toJson scenario.plan.step.features)]),
    ("contract", contractJson emitted), ("executionFuel", toJson fuel)]

def emitCase (scenario : CheckedScenario) (origin : Json) (fuel : Nat) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
  let emitted ← (emit scenario.plan).mapError reprStr
  return makeCase scenario emitted origin fuel

/-- Every origin must reconstruct the fixed host contract, including imports and
reductions. An arbitrary well-typed program is not an admissible replacement. -/
def caseProgram (json : Json) : Except String CheckedScenario := do
  unless (← json.getObjValAs? String "schema") = caseSchema do throw "unsupported semantic call-value case schema"
  let plan ← checkedPlan (← json.getObjVal? "callValuePlan")
  let transactions ← decodeTransactions (← json.getObjVal? "transactions")
  let program ← (Wire.decodeProgramWithBudget
    {maxDepth := 512, maxNodes := 512, maxIntegerBytes := 4096}
    (← json.getObjVal? "program")).mapError (fun
      | .protocol error => error.toJson.compress
      | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)
  unless Wire.encodeProgram program == Wire.encodeProgram plan.program do
    throw "saved original Core program differs from the canonical call-value plan"
  unless (← json.getObjVal? "initialState") == initialStateJson do throw "initial storage must be empty"
  unless (← json.getObjVal? "observedSlots") == observedSlotsJson do throw "observed slots must be zero and one"
  unless (← json.getObjValAs? Nat "executionFuel") ≤ 10000000 do throw "saved execution fuel exceeds limit"
  checkedScenario plan transactions

def observe (scenario : CheckedScenario) (bindings : Bindings) (fuel : Nat) : Json :=
  Solcore.Synthesis.Stateful.CallValueExecution.observe scenario.plan scenario.transactions bindings fuel

def reverts (tx : Transaction) : Bool := tx.flags.val % 2 == 1

def parityFlags (odd : Bool) : Word := if odd then Word.ofNatModulo 1 else Word.zero

/-- Revert positions of the four generated completion patterns. -/
def parityPatterns : List (List Bool) :=
  [[false, false, false], [false, true, false], [true, false, false], [false, false, true]]

/-- A separate stream keeps sequence choices independent of the step seed's
helper-count and template digits. Each choice uses the high half of one draw:
the low bits of a power-of-two LCG have short periods. The draws are three
inputs, three values, the deployment value and the completion pattern. -/
def sequenceChoices (seed : Seed) : List Nat := Id.run do
  let mut state := Seed.ofNat (seed.toNat ^^^ 0x76616c75652d7478)
  let mut values : Array Nat := #[]
  for bound in [6, 6, 6, 6, 6, 6, 2, 4] do
    let (value, next) := state.draw
    values := values.push (value.toNat / 2 ^ 32 % bound)
    state := next
  return values.toList

def generatedParities (seed : Seed) : List Bool :=
  parityPatterns.getD ((sequenceChoices seed).getD 7 0) [false, false, false]

def generatedDeploymentValue (seed : Seed) : Word :=
  deploymentBank.getD ((sequenceChoices seed).getD 6 0) Word.zero

def generatedTransactions (seed : Seed) : List Transaction :=
  let choices := sequenceChoices seed
  (generatedParities seed).zipIdx.map fun (odd, index) =>
    ⟨"tx-" ++ toString index, parityFlags odd, boundaryInputs.getD (choices.getD index 0) Word.zero,
      valueBank.getD (choices.getD (3 + index) 0) Word.zero⟩

private def statusName (odd : Bool) : String := if odd then "reverted" else "returned"

/-- Reserve the measured host wrapper before generating its independent step;
the complete contract is remeasured as the final budget authority. -/
def generatedScenario (seed : Seed) (nodes : Nat) : Except String (CheckedScenario × Json) := do
  unless nodes ≤ 512 && Solcore.Synthesis.Core.CallValue.programOverhead < nodes do
    throw "node budget is too small for the call-value wrapper or exceeds 512"
  let (step, stepOrigin) ← Aggregate.generatedFunction seed
    (nodes - Solcore.Synthesis.Core.CallValue.programOverhead)
  let some plan := CheckedPlan.ofParts? step (generatedDeploymentValue seed) |
    throw "generated call-value plan failed full Core admission"
  let scenario ← checkedScenario plan (generatedTransactions seed)
  unless Wire.programNodes scenario.program ≤ nodes do throw "call-value contract exceeds its requested node budget"
  return (scenario, Json.mkObj [
    ("kind", toJson "call-value-generated"), ("seed", toJson (toString seed.toNat)),
    ("finalSeed", ← stepOrigin.getObjVal? "finalSeed"), ("maxProgramNodes", toJson nodes),
    ("stepOrigin", stepOrigin), ("sequenceChoices", toJson (sequenceChoices seed)),
    ("sequenceCompletions", toJson ((generatedParities seed).map statusName))])

private def decimal (row : Json) (key : String) : Except String Nat := do
  let some value := (← row.getObjValAs? String key).toNat? | throw ("invalid " ++ key)
  return value

private def slotValue (row : Json) (slot : String) (field : String := "committedStorage") : Except String Nat := do
  let rows ← row.getObjValAs? (List Json) field
  let some entry := rows.find? (fun entry => (entry.getObjValAs? String "slot").toOption == some slot) |
    throw "committed slot missing"
  decimal entry "value"

/-- Original Core must complete every transaction with the prescribed
completion; each committed balance must be the deployment value plus slot one,
and a revert must keep the prior slots and balance. -/
def checkBalances (scenario : CheckedScenario) (history : Json) : Except String (List String) := do
  unless (← history.getObjValAs? String "status") = "complete" do
    throw "call-value history exhausted Core fuel"
  let rows ← history.getObjValAs? (List Json) "transactions"
  unless rows.length == scenario.transactions.length do throw "call-value history length changed"
  let deployment := scenario.plan.deploymentValue.val
  unless (← decimal history "initialBalance") == deployment && (← slotValue history "1" "initialStorage") == 0 do
    throw "call-value deployment does not hold exactly its deployment value"
  let mut statuses : List String := []
  let mut priorBalance := deployment
  let mut priorStorage ← history.getObjVal? "initialStorage"
  for (row, tx) in rows.zip scenario.transactions do
    let status ← row.getObjValAs? String "status"
    unless status == statusName (reverts tx) do throw "call-value history did not follow its flags parities"
    let balance ← decimal row "committedBalance"
    unless balance == (deployment + (← slotValue row "1")) % 2 ^ 256 do
      throw "committed balance differs from the deployment value plus accepted value"
    if status == "reverted" then
      unless balance == priorBalance && (← row.getObjVal? "committedStorage") == priorStorage do
        throw "a reverted call-value transaction changed the committed balance or slots"
    priorBalance := balance
    priorStorage ← row.getObjVal? "committedStorage"
    statuses := statuses ++ [status]
  return statuses

def validateGenerated (scenario : CheckedScenario) (fuel : Nat) : Except String Unit := do
  Aggregate.inputSensitive scenario.plan.step fuel
  let observed := observe scenario Solcore.Synthesis.Stateful.StorageExecution.fixtureBindings fuel
  let statuses ← checkBalances scenario observed
  unless statuses == scenario.transactions.map (fun tx => statusName (reverts tx)) do
    throw "call-value history did not follow its prescribed flags parities"

def generateCases (firstSeed : Seed) (nodes count attempts fuel : Nat) : Json := Id.run do
  let mut cases : Array Json := #[]
  let mut excluded : Array Json := #[]
  let mut attempted := 0
  for index in List.range attempts do
    if cases.size < count then
      attempted := attempted + 1
      let seed := Seed.ofNat (firstSeed.toNat + index)
      let result := do
        unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
        let (scenario, origin) ← generatedScenario seed nodes
        let emitted ← (emit scenario.plan).mapError reprStr
        validateGenerated scenario fuel
        return (scenario, origin.setObjVal! "validationFuel" (toJson fuel), emitted)
      match result with
      | .error error =>
          let resource := error == "boundary observation exhausted Core fuel" ||
            error == "call-value history exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "call-value-profile"),
            ("reason", toJson error),
            ("code", toJson (if resource then "validation-out-of-fuel" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok (scenario, origin, emitted) =>
          cases := cases.push (makeCase scenario emitted origin fuel)
  return Json.mkObj [("schema", toJson valueCorpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

/-- Flags, inputs, values and the deployment value all contribute. -/
def valueWeight (scenario : CheckedScenario) : Nat :=
  scenario.transactions.foldl (fun total transaction =>
    total + transaction.flags.val + transaction.input.val + transaction.value.val) scenario.plan.deploymentValue.val

/-- Transaction count, complete program size/literals, then runtime flags,
inputs, values and the deployment value. Every axis is a natural number and
the comparison is lexicographic. -/
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

private def sealReduction (source : CheckedScenario) (step : Aggregates.CheckedDAG) (deploymentValue : Word)
    (transactions : List Transaction) : Option (Reduction source) := do
  let plan ← CheckedPlan.ofParts? step deploymentValue
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

/-- Step reductions and a zero deployment value, then per transaction:
removal, bank replacements of the input, smaller bank values, and flags reduced
to their parity or with the revert bit cleared. Candidates still need execution
to preserve a finding. -/
def reductions (source : CheckedScenario) : List (Reduction source) := Id.run do
  let step := source.plan.step
  let deployment := source.plan.deploymentValue
  let mut raw : List (Aggregates.CheckedDAG × Word × List Transaction) := []
  for reduced in Aggregate.reductions ⟨step, Word.zero⟩ do
    raw := raw ++ [(reduced.candidate.function, deployment, source.transactions)]
  raw := raw ++ [(step, Word.zero, source.transactions)]
  for (transaction, index) in source.transactions.zipIdx do
    raw := raw ++ [(step, deployment,
      (source.transactions.zipIdx.filter (fun (_, current) => current != index)).map Prod.fst)]
    for input in boundaryInputs do
      raw := raw ++ [(step, deployment, replaceAt source.transactions index fun tx => {tx with input := input})]
    for value in valueBank.filter (·.val < transaction.value.val) do
      raw := raw ++ [(step, deployment, replaceAt source.transactions index fun tx => {tx with value := value})]
    raw := raw ++ [(step, deployment, replaceAt source.transactions index fun tx =>
      {tx with flags := tx.flags.bitAnd (Word.ofNatModulo 1)})]
    raw := raw ++ [(step, deployment, replaceAt source.transactions index fun tx =>
      {tx with flags := tx.flags.bitAnd (Word.ofNatModulo 1).bitNot})]
  let mut seen : List String := []
  let mut result := []
  for (step, deploymentValue, transactions) in raw do
    if let some reduced := sealReduction source step deploymentValue transactions then
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
  for (name, expected) in [
      ("generatorVersion", generatorVersion), ("profileVersion", profileVersion),
      ("functionVersion", Solcore.Synthesis.Core.CallValue.version), ("templateVersion", templateVersion),
      ("stepProfileVersion", Aggregate.profileVersion), ("stepFunctionVersion", Aggregates.version),
      ("stepTemplateVersion", Aggregate.templateVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let emitted ← (emit admitted.plan).mapError reprStr
  unless (← json.getObjValAs? String "source") = emitted.source do throw "saved source differs from call-value plan emission"
  unless (← json.getObjVal? "contract") == contractJson emitted do throw "saved contract metadata differs from call-value wrapper"
  unless (← provenance.getObjVal? "features") == toJson admitted.plan.step.features do throw "saved features differ from checked step"
  let kind ← origin.getObjValAs? String "kind"
  if kind = "call-value-generated" then
    let seedText ← origin.getObjValAs? String "seed"
    unless seedText.length ≤ 20 do throw "invalid saved seed"
    let some seed := seedText.toNat? | throw "invalid saved seed"
    unless seed < 2 ^ 64 && toString seed = seedText do throw "noncanonical saved seed"
    let (expected, expectedOrigin) ← generatedScenario (Seed.ofNat seed) (← origin.getObjValAs? Nat "maxProgramNodes")
    let validationFuel ← origin.getObjValAs? Nat "validationFuel"
    unless validationFuel ≤ 10000000 do throw "saved validation fuel exceeds limit"
    unless origin == expectedOrigin.setObjVal! "validationFuel" (toJson validationFuel) do
      throw "saved origin differs from generated call-value provenance"
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
    unless (sealReduction parent admitted.plan.step admitted.plan.deploymentValue admitted.transactions).isSome do
      throw "reduction does not preserve bindings/IDs or decrease the complete scenario"
    unless origin == Json.mkObj [("kind", toJson "reduced"), ("parentPlan", planJson parent.plan),
        ("parentProgram", Wire.encodeProgram parent.program), ("parentTransactions", transactionsJson parent.transactions)] do
      throw "noncanonical reduced origin"
  else throw "unsupported call-value case origin"
  return makeCase admitted emitted origin fuel

def shrinkCases (json : Json) (limit fuel : Nat) : Except String Json := do
  let _ ← replayCase json fuel
  let source ← caseProgram json
  let origin := Json.mkObj [("kind", toJson "reduced"), ("parentPlan", planJson source.plan),
    ("parentProgram", Wire.encodeProgram source.program), ("parentTransactions", transactionsJson source.transactions)]
  let cases ← ((reductions source).take limit).mapM fun reduced => emitCase reduced.candidate origin fuel
  return Json.mkObj [("schema", toJson valueCorpusSchema), ("cases", toJson cases)]

end Solcore.Synthesis.Source.CallValue
