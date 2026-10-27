import Solcore.Synthesis.Source.StorageCases
import Solcore.Synthesis.Source.NestedCallEmitter
import Solcore.Synthesis.Stateful.NestedCallExecution

/-! A call case retains two original checked HostWire contracts and a role-based
transaction sequence. Every replay reconstructs both programs from the checked
step. Saved outcomes are never an oracle; the public nested executor selects
committed worlds and ordered logs. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.NestedCall
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.Synthesis.Core.NestedCall (CheckedPlan)
open Solcore.Synthesis.Stateful.NestedCallExecution (Transaction Bindings)

def caseSchema : String := "solcore-lean.semantic-call-case.v1"
def planSchema : String := "solcore-lean.call-plan.v1"
def profileVersion : String := "stateful-calls-v2/sequence-seed-v1"
def templateVersion : String := "two-account-word-call-v1"
def callCorpusSchema : String := "solcore-lean.semantic-call-corpus.v1"

def boundaryInputs : List Word :=
  (List.range 8).map Word.ofNatModulo ++ [Word.maximum, Word.ofNatModulo (2 ^ 255)]
abbrev validId := Storage.validId
abbrev validTransactions := Storage.validTransactions

structure CheckedScenario where private mk ::
  plan : CheckedPlan
  transactions : List Transaction
  valid : validTransactions transactions
  bounded : NestedCall.combinedNodes plan.step ≤ 512

def programsJson (plan : CheckedPlan) : Json := Json.mkObj [
  ("parent", Wire.encodeProgram plan.parentProgram), ("child", Wire.encodeProgram plan.childProgram)]

def checkedScenario (plan : CheckedPlan) (transactions : List Transaction) : Except String CheckedScenario := do
  if valid : validTransactions transactions then
    if bounded : NestedCall.combinedNodes plan.step ≤ 512 then
      return ⟨plan, transactions, valid, bounded⟩
    else throw "canonical call contracts exceeds the 512-node case limit"
  else throw "call scenario requires 1..3 transactions with distinct valid IDs"

def transactionJson (tx : Transaction) : Json := Json.mkObj [
  ("id", toJson tx.id), ("input", toJson (toString tx.input.val)),
  ("value", toJson "0"), ("target", toJson "parent"), ("callee", toJson "child")]

def transactionsJson (transactions : List Transaction) : Json := toJson (transactions.map transactionJson)

def decodeTransactions (json : Json) : Except String (List Transaction) := do
  let rows ← json.getArr?
  unless 1 ≤ rows.size && rows.size ≤ 3 do throw "transaction count must be between 1 and 3"
  let transactions ← rows.toList.mapM fun row => do
    let id ← row.getObjValAs? String "id"
    let inputText ← row.getObjValAs? String "input"
    unless inputText.length ≤ 78 do throw "transaction input exceeds a Word"
    let input ← Input.inputWord inputText
    let transaction : Transaction := ⟨id, input⟩
    unless row == transactionJson transaction do throw "transaction differs from canonical ID, input or role metadata"
    return transaction
  unless validTransactions transactions do throw "call scenario requires distinct valid transaction IDs"
  return transactions

def planJson (plan : CheckedPlan) : Json := Json.mkObj [
  ("schema", toJson planSchema), ("stepProgram", Wire.encodeProgram plan.step.program)]

def checkedPlan (json : Json) : Except String CheckedPlan := do
  unless (← json.getObjValAs? String "schema") = planSchema do throw "unsupported call plan schema"
  let step ← Aggregate.checkedFunction (← json.getObjVal? "stepProgram")
  let some plan := CheckedPlan.ofStep? step | throw "call contracts failed full host-Core admission"
  unless json == planJson plan do throw "call plan differs from its canonical checked representation"
  unless NestedCall.combinedNodes plan.step ≤ 512 do throw "call contracts exceeds the 512-node case limit"
  return plan

def contractsJson (emitted : EmittedContracts) : Json := Json.mkObj [
  ("parent", Json.mkObj [("name", toJson emitted.parentContractName), ("method", toJson "run"),
    ("signature", toJson emitted.parentMethodSignature), ("selector", toJson emitted.selector),
    ("deployPath", toJson emitted.parentDeployPath), ("runtimePath", toJson emitted.parentRuntimePath),
    ("constructorCalldata", toJson "0x"), ("constructorValue", toJson emitted.parentConstructorValue)]),
  ("child", Json.mkObj [("name", toJson emitted.childContractName), ("entry", toJson "fallback"),
    ("payable", toJson true), ("inputBytes", toJson (32 : Nat)),
    ("deployPath", toJson emitted.childDeployPath), ("runtimePath", toJson emitted.childRuntimePath),
    ("constructorCalldata", toJson "0x"), ("constructorValue", toJson emitted.childConstructorValue)])]

def initialStateJson : Json := Json.mkObj [
  ("accounts", toJson [
    Json.mkObj [("role", toJson "parent"), ("balance", toJson "8"), ("storage", toJson ([] : List Json))],
    Json.mkObj [("role", toJson "child"), ("balance", toJson "0"), ("storage", toJson ([] : List Json))]]),
  ("callerBalance", toJson "0")]

abbrev observedSlotsJson := Storage.observedSlotsJson

def makeCase (scenario : CheckedScenario) (emitted : EmittedContracts) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1) : Json :=
  Json.mkObj [
    ("schema", toJson caseSchema), ("callPlan", planJson scenario.plan),
    ("programs", programsJson scenario.plan), ("source", toJson emitted.source),
    ("transactions", transactionsJson scenario.transactions),
    ("initialState", initialStateJson), ("observedSlots", observedSlotsJson),
    ("provenance", Json.mkObj [
      ("origin", origin), ("profileVersion", toJson profileVersion),
      ("functionVersion", toJson NestedCall.version), ("templateVersion", toJson templateVersion),
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

/-- Every origin must reconstruct the fixed host contract, including imports and
reductions. An arbitrary well-typed program is not an admissible replacement. -/
def caseProgram (json : Json) : Except String CheckedScenario := do
  unless (← json.getObjValAs? String "schema") = caseSchema do throw "unsupported semantic call case schema"
  let plan ← checkedPlan (← json.getObjVal? "callPlan")
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
      throw "saved original Core program differs from its canonical call plan"
  unless originals == programsJson plan do throw "saved program roles are not canonical"
  unless (← json.getObjVal? "initialState") == initialStateJson do throw "initial accounts differ from fixed balances and empty storage"
  unless (← json.getObjVal? "observedSlots") == observedSlotsJson do throw "observed storage slots must be 0 and 1"
  unless (← json.getObjValAs? Nat "executionFuel") ≤ 10000000 do throw "saved execution fuel exceeds limit"
  checkedScenario plan transactions

def observe (scenario : CheckedScenario) (bindings : Bindings) (fuel : Nat) : Json :=
  Solcore.Synthesis.Stateful.NestedCallExecution.observe scenario.plan scenario.transactions bindings fuel

def sequenceIndices (seed : Seed) : List Nat :=
  [seed.toNat % 10, seed.toNat / 10 % 10, seed.toNat / 100 % 10]

def generatedTransactions (seed : Seed) : List Transaction :=
  (sequenceIndices seed).zipIdx.map fun (inputIndex, index) =>
    ⟨"tx-" ++ toString index, boundaryInputs[inputIndex]?.getD Word.zero⟩

/-- Reserve the measured host wrapper before generating its independent step;
the complete contract is remeasured as the final budget authority. -/
def generatedScenario (seed : Seed) (nodes : Nat) (revision : GeneratorRevision := .v1) :
    Except String (CheckedScenario × Json) := do
  unless nodes ≤ 512 && NestedCall.programOverhead < nodes do
    throw "node budget is too small for the call wrapper or exceeds 512"
  let (step, stepOrigin) ← Aggregate.generatedFunction seed (nodes - NestedCall.programOverhead) revision
  let some plan := CheckedPlan.ofStep? step | throw "generated call plan failed full Core admission"
  let scenario ← checkedScenario plan (generatedTransactions seed)
  unless NestedCall.combinedNodes scenario.plan.step ≤ nodes do throw "call contracts exceeds its requested node budget"
  return (scenario, Json.mkObj [
    ("kind", toJson "call-generated"), ("seed", toJson (toString seed.toNat)),
    ("finalSeed", ← stepOrigin.getObjVal? "finalSeed"), ("maxProgramNodes", toJson nodes),
    ("stepOrigin", stepOrigin), ("sequenceIndices", toJson (sequenceIndices seed))])

def validateGenerated (scenario : CheckedScenario) (fuel : Nat) : Except String Unit := do
  Aggregate.inputSensitive scenario.plan.step fuel
  let observed := observe scenario Solcore.Synthesis.Stateful.NestedCallExecution.fixtureBindings fuel
  let rows ← observed.getObjValAs? (List Json) "transactions"
  unless (← observed.getObjValAs? String "status") = "complete" do
    if rows.any (fun row => (row.getObjValAs? String "status").toOption == some "out-of-fuel") then
      throw "call history exhausted Core fuel"
    else throw "call history stopped without a permitted root completion"
  unless rows.map (fun row => (row.getObjValAs? String "status").toOption) ==
      scenario.transactions.map (fun tx => some (if tx.input.val / 2 % 2 == 1 then "reverted" else "returned")) do
    throw "call history did not produce the prescribed root outcomes"

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
            error == "call history exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "call-profile"),
            ("reason", toJson error),
            ("code", toJson (if resource then "validation-out-of-fuel" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok (scenario, origin, emitted) =>
          cases := cases.push (makeCase scenario emitted origin fuel revision)
  return Json.mkObj [("schema", toJson callCorpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

def inputWeight (scenario : CheckedScenario) : Nat :=
  scenario.transactions.foldl (fun total transaction => total + transaction.input.val) 0

def scenarioComplexity (scenario : CheckedScenario) : Complexity := {
  exprNodes := (complexity scenario.plan.parentProgram.body).exprNodes +
    (complexity scenario.plan.childProgram.body).exprNodes
  literalWeight := (complexity scenario.plan.parentProgram.body).literalWeight +
    (complexity scenario.plan.childProgram.body).literalWeight
}

/-- Transaction count, complete program size/literals, then runtime inputs.
Every axis is a natural number and the comparison is strictly lexicographic. -/
def StrictlySmaller (candidate source : CheckedScenario) : Prop :=
  candidate.transactions.length < source.transactions.length ∨
  (candidate.transactions.length = source.transactions.length ∧
    ((scenarioComplexity candidate).StrictlySmaller (scenarioComplexity source) ∨
    (scenarioComplexity candidate = scenarioComplexity source ∧
      inputWeight candidate < inputWeight source)))

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

def reductions (source : CheckedScenario) : List (Reduction source) := Id.run do
  let mut raw : List (Aggregates.CheckedDAG × List Transaction) := []
  for reduced in Aggregate.reductions ⟨source.plan.step, Word.zero⟩ do
    raw := raw ++ [(reduced.candidate.function, source.transactions)]
  for index in List.range source.transactions.length do
    raw := raw ++ [(source.plan.step,
      (source.transactions.zipIdx.filter (fun (_, current) => current != index)).map Prod.fst)]
    for input in boundaryInputs do
      let transactions := source.transactions.zipIdx.map fun (transaction, current) =>
        if current == index then {transaction with input := input} else transaction
      raw := raw ++ [(source.plan.step, transactions)]
  let mut seen : List String := []
  let mut result := []
  for (step, transactions) in raw do
    if let some reduced := sealReduction source step transactions then
      let key := (Json.mkObj [("programs", programsJson reduced.candidate.plan),
        ("transactions", transactionsJson reduced.candidate.transactions)]).compress
      if !seen.contains key then
        seen := key :: seen
        result := result ++ [reduced]
  return result

def replayCase (json : Json) (fuel : Nat) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
  let admitted ← caseProgram json
  let provenance ← json.getObjVal? "provenance"
  let revision := savedRevision provenance
  for (name, expected) in [
      ("generatorVersion", revision.version), ("profileVersion", profileVersion),
      ("functionVersion", NestedCall.version), ("templateVersion", templateVersion),
      ("stepProfileVersion", Aggregate.profileVersion), ("stepFunctionVersion", Aggregates.version),
      ("stepTemplateVersion", Aggregate.templateVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let emitted ← (emit admitted.plan).mapError reprStr
  unless (← json.getObjValAs? String "source") = emitted.source do throw "saved source differs from call plan emission"
  unless (← json.getObjVal? "contracts") == contractsJson emitted do throw "saved contract metadata differs from call wrapper"
  unless (← provenance.getObjVal? "features") == toJson admitted.plan.step.features do throw "saved features differ from checked step"
  let kind ← origin.getObjValAs? String "kind"
  if kind = "call-generated" then
    let seedText ← origin.getObjValAs? String "seed"
    unless seedText.length ≤ 20 do throw "invalid saved seed"
    let some seed := seedText.toNat? | throw "invalid saved seed"
    unless seed < 2 ^ 64 && toString seed = seedText do throw "noncanonical saved seed"
    let (expected, expectedOrigin) ← generatedScenario (Seed.ofNat seed) (← origin.getObjValAs? Nat "maxProgramNodes") revision
    let validationFuel ← origin.getObjValAs? Nat "validationFuel"
    unless validationFuel ≤ 10000000 do throw "saved validation fuel exceeds limit"
    unless origin == expectedOrigin.setObjVal! "validationFuel" (toJson validationFuel) do
      throw "saved origin differs from generated call provenance"
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
    unless (← origin.getObjVal? "parentPrograms") == programsJson parent.plan do throw "reduction parent program differs from its plan"
    unless (sealReduction parent admitted.plan.step admitted.transactions).isSome do
      throw "reduction does not preserve bindings/IDs or decrease the complete scenario"
    unless origin == Json.mkObj [("kind", toJson "reduced"), ("parentPlan", planJson parent.plan),
        ("parentPrograms", programsJson parent.plan), ("parentTransactions", transactionsJson parent.transactions)] do
      throw "noncanonical reduced origin"
  else throw "unsupported call case origin"
  return makeCase admitted emitted origin fuel revision

def shrinkCases (json : Json) (limit fuel : Nat) : Except String Json := do
  let _ ← replayCase json fuel
  let source ← caseProgram json
  let origin := Json.mkObj [("kind", toJson "reduced"), ("parentPlan", planJson source.plan),
    ("parentPrograms", programsJson source.plan), ("parentTransactions", transactionsJson source.transactions)]
  -- Reductions inherit the parent case's recorded G0 revision.
  let revision := savedRevision (← json.getObjVal? "provenance")
  let cases ← ((reductions source).take limit).mapM fun reduced => emitCase reduced.candidate origin fuel revision
  return Json.mkObj [("schema", toJson callCorpusSchema), ("cases", toJson cases)]

end Solcore.Synthesis.Source.NestedCall
