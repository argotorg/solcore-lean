import Solcore.Synthesis.Source.StorageCases
import Solcore.Synthesis.Source.ForwardedCallEmitter
import Solcore.Synthesis.Stateful.ForwardedCallExecution

/-! A forwarded-value case retains two original checked HostWire contracts and
a role-based sequence of `(input, value, amount)` transactions: the call value
the sender pays the parent and the amount the parent forwards to the child.
Every replay reconstructs both programs from the checked step. Saved outcomes
are never an oracle; the public balanced runtime and its nested scheduler
select committed worlds. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.ForwardedCall
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.Synthesis.Core.ForwardedCall (CheckedPlan)
open Solcore.Synthesis.Stateful.ForwardedCallExecution (Transaction Bindings parentEndowment)
open Solcore.Synthesis.Source.NestedCall (EmittedContracts)

def caseSchema : String := "solcore-lean.semantic-forward-case.v1"
def planSchema : String := "solcore-lean.forward-plan.v1"
def profileVersion : String := "stateful-forwarded-value-v1/forward-sequence-seed-v1"
def templateVersion : String := "forward-value-two-account-call-v1"
def forwardCorpusSchema : String := "solcore-lean.semantic-forward-corpus.v1"

/-- The parent/child call profile's inputs: zero to seven, the maximum and the
high bit. -/
def boundaryInputs : List Word :=
  (List.range 8).map Word.ofNatModulo ++ [Word.maximum, Word.ofNatModulo (2 ^ 255)]

/-- Call values and forwarded amounts: the call-value bank of zero, small
values, both sides of the 64-bit boundary and a value the endowment can
forward three times. -/
def valueBank : List Word :=
  [Word.zero, Word.ofNatModulo 1, Word.ofNatModulo 7, Word.ofNatModulo (2 ^ 64 - 1),
    Word.ofNatModulo (2 ^ 64), Word.ofNatModulo (2 ^ 70)]

def maxValue : Nat := 2 ^ 70

def validTransactions (transactions : List Transaction) : Prop :=
  1 ≤ transactions.length ∧ transactions.length ≤ 3 ∧
    (transactions.map (·.id)).Nodup ∧ transactions.all (fun tx => Storage.validId tx.id) = true ∧
    transactions.all (fun tx => tx.value.val ≤ maxValue && tx.amount.val ≤ maxValue) = true

instance (transactions : List Transaction) : Decidable (validTransactions transactions) := by
  unfold validTransactions
  infer_instance

structure CheckedScenario where private mk ::
  plan : CheckedPlan
  transactions : List Transaction
  valid : validTransactions transactions
  bounded : ForwardedCall.combinedNodes plan.step ≤ 512

def programsJson (plan : CheckedPlan) : Json := Json.mkObj [
  ("parent", Wire.encodeProgram plan.parentProgram), ("child", Wire.encodeProgram plan.childProgram)]

def checkedScenario (plan : CheckedPlan) (transactions : List Transaction) : Except String CheckedScenario := do
  if valid : validTransactions transactions then
    if bounded : ForwardedCall.combinedNodes plan.step ≤ 512 then
      return ⟨plan, transactions, valid, bounded⟩
    else throw "canonical forwarded-value contracts exceed the 512-node case limit"
  else throw "forwarded-value scenario requires 1..3 transactions with distinct valid IDs and values and amounts of at most 2^70"

def transactionJson (tx : Transaction) : Json := Json.mkObj [
  ("id", toJson tx.id), ("input", toJson (toString tx.input.val)),
  ("value", toJson (toString tx.value.val)), ("amount", toJson (toString tx.amount.val)),
  ("target", toJson "parent"), ("callee", toJson "child")]

def transactionsJson (transactions : List Transaction) : Json := toJson (transactions.map transactionJson)

private def wordField (row : Json) (key : String) : Except String Word := do
  let text ← row.getObjValAs? String key
  unless text.length ≤ 78 do throw ("transaction " ++ key ++ " exceeds a Word")
  Input.inputWord text

def decodeTransactions (json : Json) : Except String (List Transaction) := do
  let rows ← json.getArr?
  unless 1 ≤ rows.size && rows.size ≤ 3 do throw "transaction count must be between 1 and 3"
  let transactions ← rows.toList.mapM fun row => do
    let transaction : Transaction := ⟨← row.getObjValAs? String "id", ← wordField row "input",
      ← wordField row "value", ← wordField row "amount"⟩
    unless row == transactionJson transaction do
      throw "transaction differs from canonical ID, input, value, amount or role metadata"
    return transaction
  unless validTransactions transactions do
    throw "forwarded-value scenario requires distinct valid transaction IDs and values and amounts of at most 2^70"
  return transactions

def planJson (plan : CheckedPlan) : Json := Json.mkObj [
  ("schema", toJson planSchema), ("stepProgram", Wire.encodeProgram plan.step.program)]

def checkedPlan (json : Json) : Except String CheckedPlan := do
  unless (← json.getObjValAs? String "schema") = planSchema do throw "unsupported forwarded-value plan schema"
  let step ← Aggregate.checkedFunction (← json.getObjVal? "stepProgram")
  let some plan := CheckedPlan.ofStep? step | throw "forwarded-value contracts failed full host-Core admission"
  unless json == planJson plan do throw "forwarded-value plan differs from its canonical checked representation"
  unless ForwardedCall.combinedNodes plan.step ≤ 512 do throw "forwarded-value contracts exceed the 512-node case limit"
  return plan

def contractsJson (emitted : EmittedContracts) : Json := Json.mkObj [
  ("parent", Json.mkObj [("name", toJson emitted.parentContractName), ("method", toJson "run"),
    ("signature", toJson emitted.parentMethodSignature), ("selector", toJson emitted.selector),
    ("payable", toJson true), ("deployPath", toJson emitted.parentDeployPath),
    ("runtimePath", toJson emitted.parentRuntimePath),
    ("constructorCalldata", toJson "0x"), ("constructorValue", toJson emitted.parentConstructorValue)]),
  ("child", Json.mkObj [("name", toJson emitted.childContractName), ("entry", toJson "fallback"),
    ("payable", toJson true), ("inputBytes", toJson (32 : Nat)),
    ("deployPath", toJson emitted.childDeployPath), ("runtimePath", toJson emitted.childRuntimePath),
    ("constructorCalldata", toJson "0x"), ("constructorValue", toJson emitted.childConstructorValue)])]

def initialStateJson : Json := Json.mkObj [
  ("accounts", toJson [
    Json.mkObj [("role", toJson "parent"), ("balance", toJson (toString parentEndowment)),
      ("storage", toJson ([] : List Json))],
    Json.mkObj [("role", toJson "child"), ("balance", toJson "0"), ("storage", toJson ([] : List Json))]]),
  ("callerBalance", toJson (toString Solcore.Synthesis.Stateful.ForwardedCallExecution.callerFunds))]

abbrev observedSlotsJson := Storage.observedSlotsJson

def makeCase (scenario : CheckedScenario) (emitted : EmittedContracts) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1) : Json :=
  Json.mkObj [
    ("schema", toJson caseSchema), ("forwardPlan", planJson scenario.plan),
    ("programs", programsJson scenario.plan), ("source", toJson emitted.source),
    ("transactions", transactionsJson scenario.transactions),
    ("initialState", initialStateJson), ("observedSlots", observedSlotsJson),
    ("provenance", Json.mkObj [
      ("origin", origin), ("profileVersion", toJson profileVersion),
      ("functionVersion", toJson ForwardedCall.version), ("templateVersion", toJson templateVersion),
      ("stepProfileVersion", toJson Aggregate.profileVersion),
      ("stepFunctionVersion", toJson Aggregates.version),
      ("stepTemplateVersion", toJson Aggregate.templateVersion),
      ("generatorVersion", toJson revision.version),
      ("emitterVersion", toJson emitterVersion), ("wrapperVersion", toJson wrapperVersion),
      ("features", toJson scenario.plan.step.features)]),
    ("contracts", contractsJson emitted), ("executionFuel", toJson fuel)]

def emitCase (scenario : CheckedScenario) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
  let emitted ← (emit scenario.plan).mapError reprStr
  return makeCase scenario emitted origin fuel revision

/-- Every origin must reconstruct the fixed host contracts, including imports
and reductions. An arbitrary well-typed program is not an admissible
replacement. -/
def caseProgram (json : Json) : Except String CheckedScenario := do
  unless (← json.getObjValAs? String "schema") = caseSchema do throw "unsupported semantic forwarded-value case schema"
  let plan ← checkedPlan (← json.getObjVal? "forwardPlan")
  let transactions ← decodeTransactions (← json.getObjVal? "transactions")
  let originals ← json.getObjVal? "programs"
  for name in ["parent", "child"] do
    let program ← (Wire.decodeProgramWithBudget
      {maxDepth := 512, maxNodes := 512, maxIntegerBytes := 4096}
      (← originals.getObjVal? name)).mapError (fun
        | .protocol error => error.toJson.compress
        | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)
    let expected := if name == "parent" then plan.parentProgram else plan.childProgram
    unless Wire.encodeProgram program == Wire.encodeProgram expected do
      throw "saved original Core program differs from its canonical forwarded-value plan"
  unless originals == programsJson plan do throw "saved program roles are not canonical"
  unless (← json.getObjVal? "initialState") == initialStateJson do
    throw "initial accounts differ from the fixed endowment, caller funds and empty storage"
  unless (← json.getObjVal? "observedSlots") == observedSlotsJson do throw "observed storage slots must be 0 and 1"
  unless (← json.getObjValAs? Nat "executionFuel") ≤ 10000000 do throw "saved execution fuel exceeds limit"
  checkedScenario plan transactions

def observe (scenario : CheckedScenario) (bindings : Bindings) (fuel : Nat) : Json :=
  Solcore.Synthesis.Stateful.ForwardedCallExecution.observe scenario.plan scenario.transactions bindings fuel

def childReverts (tx : Transaction) : Bool := tx.input.val % 2 == 1
def rootReverts (tx : Transaction) : Bool := tx.input.val / 2 % 2 == 1

/-- Three inputs, three call modes, three call values and three amounts. Each
choice uses the high half of one draw from a separate stream: the low bits of a
power-of-two LCG have short periods. -/
def sequenceBounds : List Nat := [10, 10, 10, 4, 4, 4, 6, 6, 6, 6, 6, 6]

def sequenceChoices (seed : Seed) : List Nat := Id.run do
  let mut state := Seed.ofNat (seed.toNat ^^^ 0x666f72776172642d)
  let mut values : Array Nat := #[]
  for bound in sequenceBounds do
    let (value, next) := state.draw
    values := values.push (value.toNat / 2 ^ 32 % bound)
    state := next
  return values.toList

/-- A bank input whose low two bits are replaced by the call mode: bit one
makes the child revert and bit two the root. -/
def modeInput (input : Word) (mode : Nat) : Word :=
  (input.bitAnd (Word.ofNatModulo 3).bitNot).bitOr (Word.ofNatModulo mode)

def generatedTransactions (seed : Seed) : List Transaction :=
  let choices := sequenceChoices seed
  (List.range 3).map fun index =>
    ⟨"tx-" ++ toString index,
      modeInput (boundaryInputs.getD (choices.getD index 0) Word.zero) (choices.getD (3 + index) 0),
      valueBank.getD (choices.getD (6 + index) 0) Word.zero, valueBank.getD (choices.getD (9 + index) 0) Word.zero⟩

private def statusName (reverted : Bool) : String := if reverted then "reverted" else "returned"

/-- Reserve the measured host wrappers before generating the independent step;
the complete contracts are remeasured as the final budget authority. -/
def generatedScenario (seed : Seed) (nodes : Nat) (revision : GeneratorRevision := .v1) :
    Except String (CheckedScenario × Json) := do
  unless nodes ≤ 512 && ForwardedCall.programOverhead < nodes do
    throw "node budget is too small for the forwarded-value wrappers or exceeds 512"
  let (step, stepOrigin) ← Aggregate.generatedFunction seed (nodes - ForwardedCall.programOverhead) revision
  let some plan := CheckedPlan.ofStep? step | throw "generated forwarded-value plan failed full Core admission"
  let scenario ← checkedScenario plan (generatedTransactions seed)
  unless ForwardedCall.combinedNodes scenario.plan.step ≤ nodes do
    throw "forwarded-value contracts exceed their requested node budget"
  return (scenario, Json.mkObj [
    ("kind", toJson "forward-generated"), ("seed", toJson (toString seed.toNat)),
    ("finalSeed", ← stepOrigin.getObjVal? "finalSeed"), ("maxProgramNodes", toJson nodes),
    ("stepOrigin", stepOrigin), ("sequenceChoices", toJson (sequenceChoices seed)),
    ("sequenceCompletions", toJson (scenario.transactions.map fun tx => statusName (rootReverts tx)))])

private def decimal (row : Json) (key : String) : Except String Nat := do
  let some value := (← row.getObjValAs? String key).toNat? | throw ("invalid " ++ key)
  return value

/-- One account's committed balance and slots zero and one. -/
private def accountValues (accounts : Json) (role : String) : Except String (Nat × Nat × Nat) := do
  let rows ← accounts.getArr?
  let some account := rows.find? (fun row => (row.getObjValAs? String "role").toOption == some role) |
    throw ("committed " ++ role ++ " account missing")
  let slots ← account.getObjValAs? (List Json) "storage"
  let slot := fun (name : String) => do
    let some entry := slots.find? (fun entry => (entry.getObjValAs? String "slot").toOption == some name) |
      throw ("committed " ++ role ++ " slot missing")
    decimal entry "value"
  return (← decimal account "balance", ← slot "0", ← slot "1")

/-- Original Core must complete every transaction with the prescribed root
completion and no logs. A root revert keeps both accounts; a child revert under
a committed root keeps the child's account. In every committed state the child
holds exactly its slot one, and both balances sum to the endowment plus every
committed call value. -/
def checkProtocol (scenario : CheckedScenario) (history : Json) : Except String (List String) := do
  unless (← history.getObjValAs? String "status") = "complete" do
    throw "forwarded-value history exhausted Core fuel"
  let rows ← history.getObjValAs? (List Json) "transactions"
  unless rows.length == scenario.transactions.length do throw "forwarded-value history length changed"
  let mut prior ← history.getObjVal? "initialAccounts"
  unless (← accountValues prior "parent") == (parentEndowment, 0, 0) && (← accountValues prior "child") == (0, 0, 0) do
    throw "forwarded-value deployment does not hold exactly the endowment and empty storage"
  let mut accepted := 0
  let mut statuses : List String := []
  for (row, tx) in rows.zip scenario.transactions do
    let status ← row.getObjValAs? String "status"
    unless status == statusName (rootReverts tx) do throw "forwarded-value history did not follow its root parity"
    unless (← row.getObjVal? "logs") == toJson ([] : List Json) do throw "a forwarded-value transaction committed logs"
    let accounts ← row.getObjVal? "committedAccounts"
    if status == "reverted" then
      unless accounts == prior do throw "a reverted root changed a committed account"
    else
      if childReverts tx then
        unless (← accountValues accounts "child") == (← accountValues prior "child") do
          throw "a child revert changed the child's committed account"
      accepted := accepted + tx.value.val
    let (parentBalance, _, _) ← accountValues accounts "parent"
    let (childBalance, _, childAccepted) ← accountValues accounts "child"
    unless childBalance == childAccepted && parentBalance + childBalance == parentEndowment + accepted do
      throw "committed balances differ from the forwarded and accepted values"
    prior := accounts
    statuses := statuses ++ [status]
  return statuses

def validateGenerated (scenario : CheckedScenario) (fuel : Nat) : Except String Unit := do
  Aggregate.inputSensitive scenario.plan.step fuel
  let observed := observe scenario Solcore.Synthesis.Stateful.NestedCallExecution.fixtureBindings fuel
  let statuses ← checkProtocol scenario observed
  unless statuses == scenario.transactions.map (fun tx => statusName (rootReverts tx)) do
    throw "forwarded-value history did not follow its prescribed root parities"

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
            error == "forwarded-value history exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "forwarded-value-profile"),
            ("reason", toJson error),
            ("code", toJson (if resource then "validation-out-of-fuel" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok (scenario, origin, emitted) =>
          cases := cases.push (makeCase scenario emitted origin fuel revision)
  return Json.mkObj [("schema", toJson forwardCorpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

/-- Inputs, call values and amounts all contribute. -/
def valueWeight (scenario : CheckedScenario) : Nat :=
  scenario.transactions.foldl (fun total transaction =>
    total + transaction.input.val + transaction.value.val + transaction.amount.val) 0

/-- Both original programs, as for the parent/child call profile. -/
def scenarioComplexity (scenario : CheckedScenario) : Complexity := {
  exprNodes := (complexity scenario.plan.parentProgram.body).exprNodes +
    (complexity scenario.plan.childProgram.body).exprNodes
  literalWeight := (complexity scenario.plan.parentProgram.body).literalWeight +
    (complexity scenario.plan.childProgram.body).literalWeight
}

/-- Transaction count, complete program size/literals, then runtime inputs,
call values and amounts. Every axis is a natural number and the comparison is
lexicographic. -/
def StrictlySmaller (candidate source : CheckedScenario) : Prop :=
  candidate.transactions.length < source.transactions.length ∨
  (candidate.transactions.length = source.transactions.length ∧
    ((scenarioComplexity candidate).StrictlySmaller (scenarioComplexity source) ∨
    (scenarioComplexity candidate = scenarioComplexity source ∧
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
input, the input with its child or root revert bit cleared, and smaller bank
call values and amounts. Candidates still need execution to establish that they
preserve a finding. -/
def reductions (source : CheckedScenario) : List (Reduction source) := Id.run do
  let step := source.plan.step
  let mut raw : List (Aggregates.CheckedDAG × List Transaction) := []
  for reduced in Aggregate.reductions ⟨step, Word.zero⟩ do
    raw := raw ++ [(reduced.candidate.function, source.transactions)]
  for (transaction, index) in source.transactions.zipIdx do
    raw := raw ++ [(step, (source.transactions.zipIdx.filter (fun (_, current) => current != index)).map Prod.fst)]
    for input in boundaryInputs do
      raw := raw ++ [(step, replaceAt source.transactions index fun tx => {tx with input := input})]
    for bit in [1, 2] do
      raw := raw ++ [(step, replaceAt source.transactions index fun tx =>
        {tx with input := tx.input.bitAnd (Word.ofNatModulo bit).bitNot})]
    for value in valueBank.filter (·.val < transaction.value.val) do
      raw := raw ++ [(step, replaceAt source.transactions index fun tx => {tx with value := value})]
    for amount in valueBank.filter (·.val < transaction.amount.val) do
      raw := raw ++ [(step, replaceAt source.transactions index fun tx => {tx with amount := amount})]
  let mut seen : List String := []
  let mut result := []
  for (step, transactions) in raw do
    if let some reduced := sealReduction source step transactions then
      let identity := (Json.mkObj [("programs", programsJson reduced.candidate.plan),
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
      ("functionVersion", ForwardedCall.version), ("templateVersion", templateVersion),
      ("stepProfileVersion", Aggregate.profileVersion), ("stepFunctionVersion", Aggregates.version),
      ("stepTemplateVersion", Aggregate.templateVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let emitted ← (emit admitted.plan).mapError reprStr
  unless (← json.getObjValAs? String "source") = emitted.source do throw "saved source differs from forwarded-value plan emission"
  unless (← json.getObjVal? "contracts") == contractsJson emitted do throw "saved contract metadata differs from forwarded-value wrappers"
  unless (← provenance.getObjVal? "features") == toJson admitted.plan.step.features do throw "saved features differ from checked step"
  let kind ← origin.getObjValAs? String "kind"
  if kind = "forward-generated" then
    let seedText ← origin.getObjValAs? String "seed"
    unless seedText.length ≤ 20 do throw "invalid saved seed"
    let some seed := seedText.toNat? | throw "invalid saved seed"
    unless seed < 2 ^ 64 && toString seed = seedText do throw "noncanonical saved seed"
    let (expected, expectedOrigin) ← generatedScenario (Seed.ofNat seed) (← origin.getObjValAs? Nat "maxProgramNodes") revision
    let validationFuel ← origin.getObjValAs? Nat "validationFuel"
    unless validationFuel ≤ 10000000 do throw "saved validation fuel exceeds limit"
    unless origin == expectedOrigin.setObjVal! "validationFuel" (toJson validationFuel) do
      throw "saved origin differs from generated forwarded-value provenance"
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
    unless (← origin.getObjVal? "parentPrograms") == programsJson parent.plan do
      throw "reduction parent programs differ from their plan"
    unless (sealReduction parent admitted.plan.step admitted.transactions).isSome do
      throw "reduction does not preserve bindings/IDs or decrease the complete scenario"
    unless origin == Json.mkObj [("kind", toJson "reduced"), ("parentPlan", planJson parent.plan),
        ("parentPrograms", programsJson parent.plan), ("parentTransactions", transactionsJson parent.transactions)] do
      throw "noncanonical reduced origin"
  else throw "unsupported forwarded-value case origin"
  return makeCase admitted emitted origin fuel revision

def shrinkCases (json : Json) (limit fuel : Nat) : Except String Json := do
  let _ ← replayCase json fuel
  let source ← caseProgram json
  let origin := Json.mkObj [("kind", toJson "reduced"), ("parentPlan", planJson source.plan),
    ("parentPrograms", programsJson source.plan), ("parentTransactions", transactionsJson source.transactions)]
  -- Reductions inherit the parent case's recorded G0 revision.
  let revision := savedRevision (← json.getObjVal? "provenance")
  let cases ← ((reductions source).take limit).mapM fun reduced => emitCase reduced.candidate origin fuel revision
  return Json.mkObj [("schema", toJson forwardCorpusSchema), ("cases", toJson cases)]

end Solcore.Synthesis.Source.ForwardedCall
