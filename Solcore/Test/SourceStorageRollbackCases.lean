import Solcore.Synthesis.Source.StorageRollbackCases

/-! Storage-case regressions exercise actual checked-contract execution, exact
replay, bounded generation and scenario reductions. Expected fixture values are
test goldens only; neither emitted cases nor the observer consume them. -/
set_option autoImplicit false

namespace Tests.SourceStorageRollbackCases
open Lean Solcore.Core Solcore.Synthesis.Core Solcore.Synthesis.Source
open Solcore.Synthesis.Core.StorageRollback (CheckedPlan)
open Solcore.Synthesis.Stateful.StorageExecution (Transaction Bindings)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def get {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)
private def rejected {α : Type} (result : Except String α) (message : String) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError message)
private def field (value : Json) (name : String) : IO Json := get (value.getObjVal? name)
private def string (value : Json) (name : String) : IO String := get (value.getObjValAs? String name)
private def natural (value : Json) (name : String) : IO Nat := get (value.getObjValAs? Nat name)
private def rows (value : Json) (name : String := "transactions") : IO (Array Json) :=
  get (value.getObjValAs? (Array Json) name)
private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)
private def entry : Wire.Expr := .apply (.var 1) (.var 0)
private def bindings : Bindings := ⟨⟨17, by decide⟩, ⟨101, by decide⟩⟩
private def makePlan (body : Wire.Expr) (result : Wire.Expr := entry) : IO CheckedPlan := do
  let some graph := Aggregates.CheckedDAG.ofParts? [body] result |
    throw (IO.userError "storage fixture failed step admission")
  let some plan := CheckedPlan.ofStep? graph | throw (IO.userError "storage wrapper failed host admission")
  return plan
private def transactions (inputs : List Word) : List Transaction :=
  inputs.zipIdx.map fun (input, index) => ⟨"call-" ++ toString index, input⟩
private def scenario (plan : CheckedPlan) (inputs : List Word) : IO Solcore.Synthesis.Source.StorageRollback.CheckedScenario :=
  get (Solcore.Synthesis.Source.StorageRollback.checkedScenario plan (transactions inputs))
private def imported (value : Solcore.Synthesis.Source.StorageRollback.CheckedScenario) (fuel : Nat := 10000) : IO Json :=
  get (Solcore.Synthesis.Source.StorageRollback.emitCase value (Json.mkObj [("kind", toJson "imported")]) fuel)
private def storage (first second : Word) : Json := toJson ([
  Json.mkObj [("slot", toJson "0"), ("value", toJson (toString first.val))],
  Json.mkObj [("slot", toJson "1"), ("value", toJson (toString second.val))]])

private def checkHistory (value : Solcore.Synthesis.Source.StorageRollback.CheckedScenario) (expected : List (String × Word × Word × Word)) : IO Unit := do
  let observed := Solcore.Synthesis.Source.StorageRollback.observe value bindings 10000
  ensure ((← string observed "status") == "complete") "storage fixture did not finish"
  ensure ((← field observed "initialStorage") == storage Word.zero Word.zero)
    "original Core did not start with empty storage"
  let result ← rows observed
  ensure (result.size == expected.length && result.size == value.transactions.length)
    "original Core changed transaction count"
  for ((status, output, first, second), index) in expected.zipIdx do
    let row := result[index]!
    ensure (some (← string row "id") == (value.transactions[index]?).map (·.id) && (← natural row "index") == index)
      "observer lost stable transaction identity"
    ensure ((← string row "status") == status &&
      (← string row "output") == Solcore.ContractRuntime.encodeBytesText
        (Solcore.ContractRuntime.encodeWordBytesBE output)) "storage return value differs from golden"
    ensure ((← field row "committedStorage") == storage first second)
      "original Core committed the wrong storage prefix"
  ensure ((← field observed "finalStorage") == (← field result[result.size - 1]! "committedStorage"))
    "final storage differs from the last committed prefix"
  ensure ((← rows observed "unexecuted").isEmpty && (← field observed "stoppedAt") == Json.null)
    "successful storage history retained unexecuted work"
  ensure (Solcore.Synthesis.Source.StorageRollback.observe value bindings 10000 == observed) "fresh observation reused a previous world"

private def referenceChecks : IO Json := do
  let identity ← makePlan (.var 0)
  let value ← scenario identity ([2, 3, 4].map Word.ofNatModulo)
  checkHistory value ([("returned", 3, 2, 1), ("reverted", 7, 2, 1), ("returned", 8, 6, 2)].map fun (status, out, a, b) =>
    (status, Word.ofNatModulo out, Word.ofNatModulo a, Word.ofNatModulo b))
  let odd ← scenario identity [Word.ofNatModulo 1, Word.ofNatModulo 3, Word.maximum]
  checkHistory odd [("reverted", Word.ofNatModulo 2, Word.zero, Word.zero),
    ("reverted", Word.ofNatModulo 4, Word.zero, Word.zero), ("reverted", Word.zero, Word.zero, Word.zero)]
  let even ← scenario identity ([0, 2, 2 ^ 256 - 2].map Word.ofNatModulo)
  checkHistory even ([("returned", 1, 0, 1), ("returned", 4, 2, 2), ("returned", 3, 0, 3)].map fun (status, out, a, b) =>
    (status, Word.ofNatModulo out, Word.ofNatModulo a, Word.ofNatModulo b))
  let wrap ← scenario identity [Word.maximum, Word.ofNatModulo 2]
  checkHistory wrap [("reverted", Word.zero, Word.zero, Word.zero),
    ("returned", Word.ofNatModulo 3, Word.ofNatModulo 2, Word.ofNatModulo 1)]
  let privateStep := Wire.Expr.letE (.newCell .word (word 0))
    (.letE (.storeCell (.var 0) (.binary .wordAdd (.loadCell (.var 0)) (word 2)))
      (.binary .wordAdd (.var 2) (.loadCell (.var 1))))
  let mutablePlan ← makePlan privateStep (.binary .wordSub entry (word 1))
  let mutableCase ← scenario mutablePlan ([0, 1, 2].map Word.ofNatModulo)
  -- Both computed-word parity and input+old0 parity differ from the original
  -- input in this sequence. Neither may select the rollback branch.
  checkHistory mutableCase ([("returned", 2, 1, 1), ("reverted", 5, 1, 1), ("returned", 6, 4, 2)].map fun (status, out, a, b) =>
    (status, Word.ofNatModulo out, Word.ofNatModulo a, Word.ofNatModulo b))
  let fresh := Solcore.Synthesis.Source.StorageRollback.observe value ⟨⟨33, by decide⟩, ⟨202, by decide⟩⟩ 10000
  ensure ((← rows fresh).map Solcore.Synthesis.Stateful.AccountStorage.unbound == (← rows (Solcore.Synthesis.Source.StorageRollback.observe value bindings 10000)).map Solcore.Synthesis.Stateful.AccountStorage.unbound &&
      (← rows fresh).all (Solcore.Synthesis.Stateful.AccountStorage.boundTo · [202]))
    "address-independent rollback profile changed with bindings"
  ensure (identity.program.check && identity.program.toCore.checkHost &&
    identity.program.resultType == .sum .word (.sum .word .word))
    "rollback original code lost outcomeV1 host admission"
  let saved ← imported value
  ensure ((← get (Solcore.Synthesis.Source.StorageRollback.replayCase saved 10000)) == saved)
    "imported rollback case did not replay"
  ensure ((← get (Solcore.Synthesis.Source.StorageRollback.replayCase (saved.setObjVal! "directCore" (toJson "forged")) 10000)) == saved)
    "rollback replay consumed a stored expected result"
  let changed ← imported (← scenario identity ([1, 2, 3].map Word.ofNatModulo))
  ensure ((← field saved "program") == (← field changed "program") &&
    (← string saved "source") == (← string changed "source"))
    "rollback runtime inputs were substituted into source or Core code"
  return saved

private def resourceChecks : IO Unit := do
  let slow := (List.range 12).foldl (fun body _ => Wire.Expr.letE (word 1) body) (word 1)
  let plan ← makePlan (.ifE (.binary .wordEq (.var 0) (word 2)) slow (word 0))
  let value ← scenario plan ([0, 1, 2].map Word.ofNatModulo)
  let low := Solcore.Synthesis.Source.StorageRollback.observe value bindings 0
  ensure ((← string low "status") == "incomplete" && (← string low "stoppedAt") == "call-0" &&
    (← rows low).size == 1 && (← rows low "unexecuted").size == 2 &&
    (← field low "finalStorage") == storage Word.zero Word.zero)
    "rollback exhaustion committed or continued work"
  let mut afterRevert := false
  for fuel in List.range 250 do
    let observed := Solcore.Synthesis.Source.StorageRollback.observe value bindings fuel
    let result ← rows observed
    if result.size == 3 then
      if (← string result[2]! "status") == "out-of-fuel" then
        afterRevert := true
        ensure ((← string result[0]! "status") == "returned" &&
          (← string result[1]! "status") == "reverted" &&
          (← field result[0]! "committedStorage") == (← field result[1]! "committedStorage") &&
          (← field observed "finalStorage") == storage Word.zero (Word.ofNatModulo 1))
          "out-of-fuel after revert lost the prior committed world"
  ensure afterRevert "resource regression did not reach a completed rollback prefix"

private def generationChecks : IO Json := do
  for seed in List.range 12 do
    let mut minimum : Option Nat := none
    for budget in List.range 385 do
      if minimum.isNone && (Solcore.Synthesis.Source.StorageRollback.generatedScenario (Seed.ofNat seed) budget).isOk then minimum := some budget
    let some budget := minimum | throw (IO.userError "storage template does not fit default384 budget")
    let (value, _) ← get (Solcore.Synthesis.Source.StorageRollback.generatedScenario (Seed.ofNat seed) budget)
    ensure (Wire.programNodes value.program ≤ budget && value.transactions.length == 3 &&
      value.plan.step.helpers.length == 1 + seed % 3) "storage recipe lost full node/transaction/helper bounds"
    rejected (Solcore.Synthesis.Source.StorageRollback.generatedScenario (Seed.ofNat seed) (budget - 1)) "undersized node budget accepted"
  rejected (Solcore.Synthesis.Source.StorageRollback.generatedScenario (Seed.ofNat 0) 513) "oversized node budget accepted"
  let corpus := Solcore.Synthesis.Source.StorageRollback.generateCases (Seed.ofNat 0) 384 4 256 10000
  ensure (corpus == Solcore.Synthesis.Source.StorageRollback.generateCases (Seed.ofNat 0) 384 4 256 10000) "storage generation nondeterministic"
  let generated ← rows corpus "cases"
  ensure (generated.size == 4 && (← natural corpus "attempted") ≤ 256)
    "storage count does not count complete scenarios"
  for saved in generated do
    let value ← get (Solcore.Synthesis.Source.StorageRollback.caseProgram saved)
    ensure ((value.transactions.map (fun tx => tx.input.val % 2)) == [0, 1, 0]) "generated rollback sequence lost parity recipe"
    ensure (value.transactions.length == 3 && Wire.programNodes value.program ≤ 384)
      "generated case escaped bounded storage profile"
    ensure ((← get (Solcore.Synthesis.Source.StorageRollback.replayCase saved 10000)) == saved) "generated history provenance did not replay"
    let low ← get (Solcore.Synthesis.Source.StorageRollback.replayCase saved 0)
    ensure ((← natural low "executionFuel") == 0 && (← field low "provenance") == (← field saved "provenance"))
      "fresh replay fuel changed the generation validation budget"
  let saved := generated[0]!
  let origin ← field (← field saved "provenance") "origin"
  let some seed := (← string origin "seed").toNat? | throw (IO.userError "invalid generated seed")
  let low := Solcore.Synthesis.Source.StorageRollback.generateCases (Seed.ofNat seed) 384 1 1 0
  let excluded ← rows low "excluded"
  ensure ((← rows low "cases").isEmpty && (← string excluded[0]! "category") == "inconclusive-resource")
    "storage generation resource exhaustion was not distinguished"
  ensure ((← rows (Solcore.Synthesis.Source.StorageRollback.generateCases (Seed.ofNat seed) 384 2 1 10000) "cases").size == 1 &&
    (← natural (Solcore.Synthesis.Source.StorageRollback.generateCases (Seed.ofNat seed) 384 0 10 10000) "attempted") == 0 &&
    (← rows (Solcore.Synthesis.Source.StorageRollback.generateCases (Seed.ofNat seed) 384 1 0 10000) "cases").isEmpty)
    "storage generator ignored count/attempt bounds"
  return saved

private def tamperingChecks (saved generated : Json) : IO Unit := do
  let transactionRows ← rows saved
  let first := transactionRows[0]!
  for (name, bad) in [("id", toJson ""), ("id", toJson "not valid"),
      ("id", toJson (String.ofList (List.replicate 65 'a'))), ("input", toJson "01"),
      ("input", toJson "7"), ("calldata", toJson "0x"), ("value", toJson "1"),
      ("extra", toJson true)] do
    rejected (Solcore.Synthesis.Source.StorageRollback.decodeTransactions (toJson [first.setObjVal! name bad]))
      "noncanonical storage transaction accepted"
  rejected (Solcore.Synthesis.Source.StorageRollback.decodeTransactions (toJson [first, first])) "duplicate transaction IDs accepted"
  rejected (Solcore.Synthesis.Source.StorageRollback.decodeTransactions (toJson ([] : List Json))) "empty transaction list accepted"
  rejected (Solcore.Synthesis.Source.StorageRollback.decodeTransactions (toJson (List.replicate 4 first))) "unbounded transaction count accepted"
  for (name, bad) in [("initialState", Json.mkObj [("storage", toJson [first])]),
      ("observedSlots", toJson (["1", "0"] : List String)), ("executionFuel", toJson (10000001 : Nat)),
      ("program", Wire.encodeProgram {resultType := .word, dataDefinitions := [], body := word 0})] do
    rejected (Solcore.Synthesis.Source.StorageRollback.caseProgram (saved.setObjVal! name bad)) "invalid storage case boundary accepted"
  let provenance ← field generated "provenance"
  let origin ← field provenance "origin"
  let withOrigin := fun changed => generated.setObjVal! "provenance" (provenance.setObjVal! "origin" changed)
  for name in ["generatorVersion", "profileVersion", "functionVersion", "templateVersion", "stepProfileVersion",
      "stepFunctionVersion", "stepTemplateVersion", "emitterVersion", "wrapperVersion", "features"] do
    rejected (Solcore.Synthesis.Source.StorageRollback.replayCase (generated.setObjVal! "provenance" (provenance.setObjVal! name Json.null)) 10000)
      "tampered storage provenance accepted"
  for (name, bad) in [("seed", toJson "00"), ("finalSeed", toJson "bad"),
      ("maxProgramNodes", toJson (513 : Nat)), ("stepOrigin", Json.null), ("sequenceIndices", Json.null), ("sequenceParities", Json.null),
      ("validationFuel", toJson (10000001 : Nat)), ("validationFuel", toJson (0 : Nat))] do
    rejected (Solcore.Synthesis.Source.StorageRollback.replayCase (withOrigin (origin.setObjVal! name bad)) 10000)
      "tampered generated storage recipe accepted"
  let plan ← field saved "storagePlan"
  rejected (Solcore.Synthesis.Source.StorageRollback.checkedPlan (plan.setObjVal! "extra" Json.null)) "noncanonical storage plan accepted"
  rejected (Solcore.Synthesis.Source.StorageRollback.replayCase (saved.setObjVal! "source" (toJson "stale")) 10000) "stale source accepted"
  let contract ← field saved "contract"
  rejected (Solcore.Synthesis.Source.StorageRollback.replayCase (saved.setObjVal! "contract" (contract.setObjVal! "selector" (toJson "0x00000000"))) 10000)
    "wrong storage ABI selector accepted"
  let bindingJson := Solcore.Synthesis.Stateful.StorageExecution.bindingsJson bindings
  ensure ((Solcore.Synthesis.Stateful.StorageExecution.decodeBindings bindingJson).isOk) "valid bindings rejected"
  for (name, value) in [("caller", "017"), ("address", "17"), ("caller", toString (2 ^ 160))] do
    rejected (Solcore.Synthesis.Stateful.StorageExecution.decodeBindings (bindingJson.setObjVal! name (toJson value)))
      "invalid execution bindings accepted"

private def shrinkChecks : IO Unit := do
  let plan ← makePlan (Aggregate.template 3 (word 2))
  let value ← scenario plan [Word.maximum, Word.ofNatModulo 7, Word.maximum]
  let saved ← imported value
  let candidates ← get (Solcore.Synthesis.Source.StorageRollback.shrinkCases saved 1000 10000)
  let result ← rows candidates "cases"
  ensure (!result.isEmpty && candidates == (← get (Solcore.Synthesis.Source.StorageRollback.shrinkCases saved 1000 10000)))
    "storage reductions were empty or nondeterministic"
  let mut removed := false
  let mut loweredInput := false
  let mut changedStep := false
  let mut seen : List String := []
  for row in result do
    let reduced ← get (Solcore.Synthesis.Source.StorageRollback.caseProgram row)
    ensure (decide (Solcore.Synthesis.Source.StorageRollback.StrictlySmaller reduced value) && reduced.program.check &&
      reduced.plan.step.helpers.length == value.plan.step.helpers.length &&
      Aggregate.bindingInventory reduced.plan.step == Aggregate.bindingInventory value.plan.step &&
      decide ((reduced.transactions.map (·.id)).Sublist (value.transactions.map (·.id))))
      "storage reduction lost strict complexity, host typing or stable scope/IDs"
    let key := (Json.mkObj [("program", Wire.encodeProgram reduced.program),
      ("transactions", Solcore.Synthesis.Source.StorageRollback.transactionsJson reduced.transactions)]).compress
    ensure (!seen.contains key) "duplicate storage reduction"
    seen := key :: seen
    removed := removed || reduced.transactions.length < value.transactions.length
    loweredInput := loweredInput || (reduced.transactions.length == value.transactions.length &&
      Solcore.Synthesis.Source.StorageRollback.inputWeight reduced < Solcore.Synthesis.Source.StorageRollback.inputWeight value)
    changedStep := changedStep || Wire.encodeProgram reduced.program != Wire.encodeProgram value.program
    ensure ((← get (Solcore.Synthesis.Source.StorageRollback.replayCase row 10000)) == row) "reduced storage case did not replay"
  ensure (removed && loweredInput && changedStep) "storage shrink omitted sequence/input/step axes"
  ensure ((← rows (← get (Solcore.Synthesis.Source.StorageRollback.shrinkCases saved 2 10000)) "cases") == result.extract 0 2 &&
    (← rows (← get (Solcore.Synthesis.Source.StorageRollback.shrinkCases saved 0 10000)) "cases").isEmpty) "storage shrink limit changed ordering"
  let first := result[0]!
  let reduced ← get (Solcore.Synthesis.Source.StorageRollback.caseProgram first)
  let badParent := Json.mkObj [("kind", toJson "reduced"), ("parentPlan", Solcore.Synthesis.Source.StorageRollback.planJson reduced.plan),
    ("parentProgram", Wire.encodeProgram reduced.program),
    ("parentTransactions", Solcore.Synthesis.Source.StorageRollback.transactionsJson reduced.transactions)]
  let provenance ← field first "provenance"
  rejected (Solcore.Synthesis.Source.StorageRollback.replayCase (first.setObjVal! "provenance" (provenance.setObjVal! "origin" badParent)) 10000)
    "non-strict reduction provenance accepted"

def testSourceStorageRollbackCases : IO Unit := do
  let imported ← referenceChecks
  resourceChecks
  let generated ← generationChecks
  tamperingChecks imported generated
  shrinkChecks

end Tests.SourceStorageRollbackCases
