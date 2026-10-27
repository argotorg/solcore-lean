import Solcore.Synthesis.Source.StorageCases
import Solcore.Synthesis.Source.EventLogEmitter
import Solcore.Synthesis.Stateful.EventLogExecution

/-! Event-log cases retain one original host-aware Core contract, its static
log sites and an ordered history of `(flags, input)` transactions. The plan
fixes each site's guard bit, topic count and data length, so the log shapes a
transaction may commit are known before execution; their topics and data are
not. Saved outputs and logs are never an execution oracle. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.EventLog
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.Synthesis.Core.EventLog (CheckedPlan Site validSites)
open Solcore.Synthesis.Stateful.EventLogExecution (Transaction Bindings)

def caseSchema : String := "solcore-lean.semantic-log-case.v1"
def planSchema : String := "solcore-lean.log-plan.v1"
def profileVersion : String := "stateful-logs-v1/log-sequence-seed-v1"
def templateVersion : String := "slot-counter-guarded-log-sites-revert-odd-flags-v1"
def logCorpusSchema : String := "solcore-lean.semantic-log-corpus.v1"

abbrev boundaryInputs := Storage.boundaryInputs

/-- Flags bits above the guards. Generated transactions may set them; the
contract must ignore them. -/
def flagsNoise : Word := Word.ofNatModulo (2 ^ 255 + 16)

def validTransactions (transactions : List Transaction) : Prop :=
  1 ≤ transactions.length ∧ transactions.length ≤ Stateful.Sequence.maxTransactions ∧
    (transactions.map (·.id)).Nodup ∧ transactions.all (fun tx => Storage.validId tx.id) = true

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
    else throw "canonical event-log contract exceeds the 512-node case limit"
  else throw s!"event-log scenario requires 1..{Stateful.Sequence.maxTransactions} transactions with distinct valid IDs"

def transactionJson (tx : Transaction) : Json := Json.mkObj [
  ("id", toJson tx.id), ("flags", toJson (toString tx.flags.val)), ("input", toJson (toString tx.input.val)),
  ("calldata", toJson (Solcore.Synthesis.Stateful.EventLogExecution.calldata tx.flags tx.input)),
  ("value", toJson "0")]

def transactionsJson (transactions : List Transaction) : Json := toJson (transactions.map transactionJson)

private def wordField (row : Json) (key : String) : Except String Word := do
  let text ← row.getObjValAs? String key
  unless text.length ≤ 78 do throw ("transaction " ++ key ++ " exceeds a Word")
  Input.inputWord text

def decodeTransactions (json : Json) : Except String (List Transaction) := do
  let rows ← json.getArr?
  unless 1 ≤ rows.size && rows.size ≤ Stateful.Sequence.maxTransactions do
    throw s!"transaction count must be between 1 and {Stateful.Sequence.maxTransactions}"
  let transactions ← rows.toList.mapM fun row => do
    let transaction : Transaction := ⟨← row.getObjValAs? String "id", ← wordField row "flags", ← wordField row "input"⟩
    unless row == transactionJson transaction do
      throw "transaction differs from canonical ID, flags, input, calldata or zero-value metadata"
    return transaction
  unless validTransactions transactions do
    throw "event-log scenario requires distinct valid transaction IDs"
  return transactions

def siteJson (site : Site) : Json := Json.mkObj [
  ("guard", toJson site.guard), ("topics", toJson site.topics), ("dataWords", toJson site.dataWords)]

def sitesJson (sites : List Site) : Json := toJson (sites.map siteJson)

def planJson (plan : CheckedPlan) : Json := Json.mkObj [
  ("schema", toJson planSchema), ("stepProgram", Wire.encodeProgram plan.step.program),
  ("sites", sitesJson plan.sites)]

private def decodeSites (json : Json) : Except String (List Site) := do
  let rows ← json.getArr?
  unless rows.size ≤ Solcore.Synthesis.Core.EventLog.maxSites do throw "an event-log plan has at most three sites"
  let sites ← rows.toList.mapM fun row => do
    let site : Site := ⟨← row.getObjValAs? Nat "guard", ← row.getObjValAs? Nat "topics",
      ← row.getObjValAs? Nat "dataWords"⟩
    unless row == siteJson site do throw "log site differs from its canonical guard, topics and dataWords"
    return site
  unless validSites sites do
    throw "log sites need increasing guards one to three, at most four topics and two data Words"
  return sites

def checkedPlan (json : Json) : Except String CheckedPlan := do
  unless (← json.getObjValAs? String "schema") = planSchema do throw "unsupported event-log plan schema"
  let step ← Aggregate.checkedFunction (← json.getObjVal? "stepProgram")
  let sites ← decodeSites (← json.getObjVal? "sites")
  let some plan := CheckedPlan.ofParts? step sites | throw "event-log contract failed full host-Core admission"
  unless json == planJson plan do throw "event-log plan differs from its canonical checked representation"
  unless Wire.programNodes plan.program ≤ 512 do throw "event-log contract exceeds the 512-node case limit"
  return plan

def contractJson (emitted : EmittedProgram) : Json := Json.mkObj [
  ("name", toJson emitted.contractName), ("method", toJson emitted.methodName),
  ("signature", toJson emitted.methodSignature), ("selector", toJson selector),
  ("deployPath", toJson emitted.deployPath), ("runtimePath", toJson emitted.runtimePath),
  ("constructorCalldata", toJson "0x")]

def initialStateJson : Json := Json.mkObj [("storage", toJson ([] : List Json))]

def observedSlotsJson : Json :=
  Solcore.Synthesis.Stateful.KeyedStorageExecution.slotsJson Solcore.Synthesis.Stateful.EventLogExecution.observedSlots

def makeCase (scenario : CheckedScenario) (emitted : EmittedProgram) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1) : Json :=
  Json.mkObj [
    ("schema", toJson caseSchema), ("logPlan", planJson scenario.plan),
    ("program", Wire.encodeProgram scenario.program), ("source", toJson emitted.source),
    ("transactions", transactionsJson scenario.transactions),
    ("initialState", initialStateJson), ("observedSlots", observedSlotsJson),
    ("provenance", Json.mkObj [
      ("origin", origin), ("profileVersion", toJson profileVersion),
      ("functionVersion", toJson Solcore.Synthesis.Core.EventLog.version),
      ("framingVersion", toJson Solcore.Synthesis.Core.EventLog.framingVersion),
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
  unless (← json.getObjValAs? String "schema") = caseSchema do throw "unsupported semantic event-log case schema"
  let plan ← checkedPlan (← json.getObjVal? "logPlan")
  let transactions ← decodeTransactions (← json.getObjVal? "transactions")
  let program ← (Wire.decodeProgramWithBudget
    {maxDepth := 512, maxNodes := 512, maxIntegerBytes := 4096}
    (← json.getObjVal? "program")).mapError (fun
      | .protocol error => error.toJson.compress
      | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)
  unless Wire.encodeProgram program == Wire.encodeProgram plan.program do
    throw "saved original Core program differs from the canonical event-log plan"
  unless (← json.getObjVal? "initialState") == initialStateJson do throw "initial storage must be empty"
  unless (← json.getObjVal? "observedSlots") == observedSlotsJson do throw "observed slots must be zero and one"
  unless (← json.getObjValAs? Nat "executionFuel") ≤ 10000000 do throw "saved execution fuel exceeds limit"
  checkedScenario plan transactions

def observe (scenario : CheckedScenario) (bindings : Bindings) (fuel : Nat) : Json :=
  Solcore.Synthesis.Stateful.EventLogExecution.observe scenario.plan scenario.transactions bindings fuel

private def bitSet (value : Word) (bit : Nat) : Bool :=
  value.bitAnd (Word.ofNatModulo (2 ^ bit)) == Word.ofNatModulo (2 ^ bit)

def reverts (tx : Transaction) : Bool := bitSet tx.flags 0

/-- Sites whose guard bit is set, in emission order. Whether their logs commit
depends on the completion. -/
def guardedSites (plan : CheckedPlan) (tx : Transaction) : List Site :=
  plan.sites.filter fun site => bitSet tx.flags site.guard

/-- The static topic counts and data lengths in bytes of the committed logs:
one per guarded site on return, none on revert. -/
def expectedShapes (plan : CheckedPlan) (tx : Transaction) : List (Nat × Nat) :=
  if reverts tx then [] else (guardedSites plan tx).map fun site => (site.topics, 32 * site.dataWords)

def parityFlags (odd : Bool) (flags : Word) : Word :=
  if odd then flags.bitOr (Word.ofNatModulo 1)
  else flags.bitAnd (Word.ofNatModulo (2 ^ 256 - 2))

/-- Revert positions of the four generated completion patterns. -/
def parityPatterns : List (List Bool) :=
  [[false, false, false], [false, true, false], [true, false, false], [false, false, true]]

/-- Guard sets for one and two sites; three sites use every guard. -/
private def guardChoices : Nat → List (List Nat)
  | 1 => [[1], [2], [3]]
  | 2 => [[1, 2], [1, 3], [2, 3]]
  | _ => [[1, 2, 3]]

/-- A separate stream keeps site and sequence choices independent of the step
seed's helper-count and template digits. Each choice uses the high half of one
draw: the low bits of a power-of-two LCG have short periods. The draws are the
site count, three topic counts and data lengths, the guard set, three inputs,
three guard masks, three noise choices and the completion pattern. -/
def sequenceChoices (seed : Seed) : List Nat := Id.run do
  let mut state := Seed.ofNat (seed.toNat ^^^ 0x6c6f672d73697465)
  let mut values : Array Nat := #[]
  for bound in [3, 5, 3, 5, 3, 5, 3, 3, 6, 6, 6, 8, 8, 8, 2, 2, 2, 4] do
    let (value, next) := state.draw
    values := values.push (value.toNat / 2 ^ 32 % bound)
    state := next
  return values.toList

def generatedSites (seed : Seed) : List Site :=
  let choices := sequenceChoices seed
  let count := 1 + choices.getD 0 0
  let guards := (guardChoices count).getD (choices.getD 7 0) [1, 2, 3]
  guards.zipIdx.map fun (guard, index) =>
    ⟨guard, choices.getD (1 + 2 * index) 0, choices.getD (2 + 2 * index) 0⟩

def generatedParities (seed : Seed) : List Bool :=
  parityPatterns.getD ((sequenceChoices seed).getD 17 0) [false, false, false]

def blockTransactions (seed : Seed) (first : Nat) : List Transaction :=
  let choices := sequenceChoices seed
  (generatedParities seed).zipIdx.map fun (odd, index) =>
    let mask := Word.ofNatModulo (2 * choices.getD (11 + index) 0)
    let noise := if choices.getD (14 + index) 0 = 1 then flagsNoise else Word.zero
    ⟨"tx-" ++ toString (first + index), parityFlags odd (mask.bitOr noise),
      boundaryInputs.getD (choices.getD (8 + index) 0) Word.zero⟩

/-- The first `count` transactions of the seed's consecutive blocks. -/
def generatedTransactions (seed : Seed) (count : Nat := 3) : List Transaction :=
  Stateful.Sequence.blocks blockTransactions seed count

private def statusName (odd : Bool) : String := if odd then "reverted" else "returned"

/-- Reserve the measured host wrapper of the chosen sites before generating the
independent step; the complete contract is remeasured as the final authority. -/
def generatedScenario (seed : Seed) (nodes : Nat) (revision : GeneratorRevision := .v1)
    (transactions : Nat := 3) : Except String (CheckedScenario × Json) := do
  Stateful.Sequence.checkCount transactions
  let sites := generatedSites seed
  let overhead := Solcore.Synthesis.Core.EventLog.programOverhead sites
  unless nodes ≤ 512 && overhead < nodes do
    throw "node budget is too small for the event-log wrapper or exceeds 512"
  let (step, stepOrigin) ← Aggregate.generatedFunction seed (nodes - overhead) revision
  let some plan := CheckedPlan.ofParts? step sites | throw "generated event-log plan failed full Core admission"
  let scenario ← checkedScenario plan (generatedTransactions seed transactions)
  unless Wire.programNodes scenario.program ≤ nodes do throw "event-log contract exceeds its requested node budget"
  return (scenario, Stateful.Sequence.recordCount (Json.mkObj [
    ("kind", toJson "log-generated"), ("seed", toJson (toString seed.toNat)),
    ("finalSeed", ← stepOrigin.getObjVal? "finalSeed"), ("maxProgramNodes", toJson nodes),
    ("stepOrigin", stepOrigin),
    ("sequenceChoices", toJson (Stateful.Sequence.blockChoices sequenceChoices seed transactions)),
    ("sequenceCompletions", toJson ((Stateful.Sequence.blocks (fun blockSeed _ => generatedParities blockSeed) seed
      transactions).map statusName))]) transactions)

private def shapes (logs : Json) : Except String (List (Nat × Nat)) := do
  let rows ← logs.getArr?
  rows.toList.mapM fun row => do
    let topics ← row.getObjValAs? (List String) "topics"
    let data ← row.getObjValAs? String "data"
    unless data.length ≥ 2 && data.length % 2 == 0 do throw "noncanonical log data"
    return (topics.length, (data.length - 2) / 2)

/-- Original Core must complete every transaction with a decodable journal
whose logs have the static shapes of the plan, and the given completions. -/
def checkShapes (scenario : CheckedScenario) (history : Json) : Except String (List String) := do
  unless (← history.getObjValAs? String "status") = "complete" do
    throw "event-log history exhausted Core fuel"
  let rows ← history.getObjValAs? (List Json) "transactions"
  unless rows.length == scenario.transactions.length do throw "event-log history length changed"
  let mut statuses : List String := []
  for (row, tx) in rows.zip scenario.transactions do
    let status ← row.getObjValAs? String "status"
    unless status == statusName (reverts tx) do throw "event-log history did not follow its flags parities"
    unless (← shapes (← row.getObjVal? "logs")) == expectedShapes scenario.plan tx do
      throw "event-log history differs from the static site shapes"
    statuses := statuses ++ [status]
  return statuses

def validateGenerated (scenario : CheckedScenario) (fuel : Nat) : Except String Unit := do
  Aggregate.inputSensitive scenario.plan.step fuel
  let observed := observe scenario Solcore.Synthesis.Stateful.StorageExecution.fixtureBindings fuel
  let statuses ← checkShapes scenario observed
  unless statuses == scenario.transactions.map (fun tx => statusName (reverts tx)) do
    throw "event-log history did not follow its prescribed flags parities"

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
            error == "event-log history exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "event-log-profile"),
            ("reason", toJson error),
            ("code", toJson (if resource then "validation-out-of-fuel" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok (scenario, origin, emitted) =>
          cases := cases.push (makeCase scenario emitted origin fuel revision)
  return Json.mkObj [("schema", toJson logCorpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

/-- Flags and inputs both contribute; clearing a flags bit lowers the weight. -/
def valueWeight (scenario : CheckedScenario) : Nat :=
  scenario.transactions.foldl (fun total transaction => total + transaction.flags.val + transaction.input.val) 0

/-- Transaction count, complete program size/literals, then runtime flags and
inputs. Removing or simplifying a site shrinks the program. Every axis is a
natural number and the comparison is lexicographic. -/
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

private def sealReduction (source : CheckedScenario) (step : Aggregates.CheckedDAG) (sites : List Site)
    (transactions : List Transaction) : Option (Reduction source) := do
  let plan ← CheckedPlan.ofParts? step sites
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

/-- Each site may be removed, or lose its last topic or last data Word. -/
private def siteReductions (sites : List Site) : List (List Site) :=
  (List.range sites.length).flatMap fun position =>
    let site := sites.getD position ⟨0, 0, 0⟩
    [sites.eraseIdx position] ++
      (if site.topics > 0 then [sites.set position {site with topics := site.topics - 1}] else []) ++
      (if site.dataWords > 0 then [sites.set position {site with dataWords := site.dataWords - 1}] else [])

/-- Step reductions, site removals and simplifications, then per transaction:
removal, bank replacements of the input, clearing one of flags bits zero to
three, and keeping only those four bits. Candidates still need execution to
preserve a finding. -/
def reductions (source : CheckedScenario) : List (Reduction source) := Id.run do
  let step := source.plan.step
  let sites := source.plan.sites
  let mut raw : List (Aggregates.CheckedDAG × List Site × List Transaction) := []
  -- Removing one transaction comes first, from the last back: a long
  -- sequence loses the tail beyond a difference before the candidate limit.
  for index in (List.range source.transactions.length).reverse do
    raw := raw ++ [(step, sites,
      (source.transactions.zipIdx.filter (fun (_, current) => current != index)).map Prod.fst)]
  for reduced in Aggregate.reductions ⟨step, Word.zero⟩ do
    raw := raw ++ [(reduced.candidate.function, sites, source.transactions)]
  for candidate in siteReductions sites do
    raw := raw ++ [(step, candidate, source.transactions)]
  for index in List.range source.transactions.length do
    for input in boundaryInputs do
      raw := raw ++ [(step, sites, replaceAt source.transactions index fun tx => {tx with input := input})]
    for bit in List.range 4 do
      raw := raw ++ [(step, sites, replaceAt source.transactions index fun tx =>
        {tx with flags := tx.flags.bitAnd (Word.ofNatModulo (2 ^ bit)).bitNot})]
    raw := raw ++ [(step, sites, replaceAt source.transactions index fun tx =>
      {tx with flags := tx.flags.bitAnd (Word.ofNatModulo 15)})]
  let mut seen : List String := []
  let mut result := []
  for (step, sites, transactions) in raw do
    if let some reduced := sealReduction source step sites transactions then
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
  for (name, expected) in [
      ("generatorVersion", revision.version), ("profileVersion", profileVersion),
      ("functionVersion", Solcore.Synthesis.Core.EventLog.version),
      ("framingVersion", Solcore.Synthesis.Core.EventLog.framingVersion), ("templateVersion", templateVersion),
      ("stepProfileVersion", Aggregate.profileVersion), ("stepFunctionVersion", Aggregates.version),
      ("stepTemplateVersion", Aggregate.templateVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let emitted ← (emit admitted.plan).mapError reprStr
  unless (← json.getObjValAs? String "source") = emitted.source do throw "saved source differs from event-log plan emission"
  unless (← json.getObjVal? "contract") == contractJson emitted do throw "saved contract metadata differs from event-log wrapper"
  unless (← provenance.getObjVal? "features") == toJson admitted.plan.step.features do throw "saved features differ from checked step"
  let kind ← origin.getObjValAs? String "kind"
  if kind = "log-generated" then
    let seedText ← origin.getObjValAs? String "seed"
    unless seedText.length ≤ 20 do throw "invalid saved seed"
    let some seed := seedText.toNat? | throw "invalid saved seed"
    unless seed < 2 ^ 64 && toString seed = seedText do throw "noncanonical saved seed"
    let (expected, expectedOrigin) ← generatedScenario (Seed.ofNat seed) (← origin.getObjValAs? Nat "maxProgramNodes") revision
      (← Stateful.Sequence.savedCount origin)
    let validationFuel ← origin.getObjValAs? Nat "validationFuel"
    unless validationFuel ≤ 10000000 do throw "saved validation fuel exceeds limit"
    unless origin == expectedOrigin.setObjVal! "validationFuel" (toJson validationFuel) do
      throw "saved origin differs from generated event-log provenance"
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
    unless (sealReduction parent admitted.plan.step admitted.plan.sites admitted.transactions).isSome do
      throw "reduction does not preserve bindings/IDs or decrease the complete scenario"
    unless origin == Json.mkObj [("kind", toJson "reduced"), ("parentPlan", planJson parent.plan),
        ("parentProgram", Wire.encodeProgram parent.program), ("parentTransactions", transactionsJson parent.transactions)] do
      throw "noncanonical reduced origin"
  else throw "unsupported event-log case origin"
  return makeCase admitted emitted origin fuel revision

def shrinkCases (json : Json) (limit fuel : Nat) : Except String Json := do
  let _ ← replayCase json fuel
  let source ← caseProgram json
  let origin := Json.mkObj [("kind", toJson "reduced"), ("parentPlan", planJson source.plan),
    ("parentProgram", Wire.encodeProgram source.program), ("parentTransactions", transactionsJson source.transactions)]
  -- Reductions inherit the parent case's recorded G0 revision.
  let revision := savedRevision (← json.getObjVal? "provenance")
  let cases ← ((reductions source).take limit).mapM fun reduced => emitCase reduced.candidate origin fuel revision
  return Json.mkObj [("schema", toJson logCorpusSchema), ("cases", toJson cases)]

end Solcore.Synthesis.Source.EventLog
