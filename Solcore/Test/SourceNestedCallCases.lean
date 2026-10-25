import Solcore.Synthesis.Source.NestedCallCases

/-! Goldens consume only the real nested scheduler. Expected values below are
regression fixtures, never inputs to generation, replay, shrinking or execution. -/
set_option autoImplicit false

namespace Tests.SourceNestedCallCases
open Lean Solcore.Core Solcore.Synthesis.Core Solcore.Synthesis.Source
open Solcore.Synthesis.Core.NestedCall (CheckedPlan)
open Solcore.Synthesis.Stateful.NestedCallExecution (Transaction Bindings)

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
private def w := Word.ofNatModulo
private def word (value : Nat) : Wire.Expr := .word (w value)
private def entry : Wire.Expr := .apply (.var 1) (.var 0)
private def bindings : Bindings := ⟨⟨17, by decide⟩, ⟨101, by decide⟩, ⟨102, by decide⟩⟩
private def makePlan (body : Wire.Expr) (result : Wire.Expr := entry) : IO CheckedPlan := do
  let some graph := Aggregates.CheckedDAG.ofParts? [body] result |
    throw (IO.userError "call fixture failed step admission")
  let some plan := CheckedPlan.ofStep? graph | throw (IO.userError "call wrappers failed host admission")
  return plan
private def transactions (inputs : List Word) : List Transaction :=
  inputs.zipIdx.map fun (input, index) => ⟨"call-" ++ toString index, input⟩
private def scenario (plan : CheckedPlan) (inputs : List Word) : IO Solcore.Synthesis.Source.NestedCall.CheckedScenario :=
  get (Solcore.Synthesis.Source.NestedCall.checkedScenario plan (transactions inputs))
private def imported (value : Solcore.Synthesis.Source.NestedCall.CheckedScenario) (fuel : Nat := 20000) : IO Json :=
  get (Solcore.Synthesis.Source.NestedCall.emitCase value (Json.mkObj [("kind", toJson "imported")]) fuel)
private def encoded (value : Word) : String := Solcore.ContractRuntime.encodeBytesText
  (Solcore.ContractRuntime.encodeWordBytesBE value)
private def account (role : String) (address : Nat) (balance first second : Word) : Json := Json.mkObj [
  ("role", toJson role), ("address", toJson (toString address)), ("balance", toJson (toString balance.val)),
  ("storage", toJson ([Json.mkObj [("slot", toJson "0"), ("value", toJson (toString first.val))],
    Json.mkObj [("slot", toJson "1"), ("value", toJson (toString second.val))]]))]
private def accounts (p0 p1 c0 c1 : Word) (pb : Nat := 8) (cb : Nat := 0) : Json := toJson [
  account "parent" 101 (w pb) p0 p1, account "child" 102 (w cb) c0 c1]
private def logs (values : List (Nat × Nat × Word)) : Json := toJson (values.map fun (address, topic, value) =>
  Json.mkObj [("address", toJson (toString address)), ("topics", toJson [toString topic]), ("data", toJson (encoded value))])
private def committed (p0 p1 c0 : Nat) : Json := logs [(101, 1, w p0), (102, 2, w c0), (101, 3, w p1)]
private def childReverted (p0 p1 : Nat) : Json := logs [(101, 1, w p0), (101, 3, w p1)]
private def emptyAccounts : Json := accounts Word.zero Word.zero Word.zero Word.zero
private def emptyLogs : Json := logs []

private def checkHistory (value : Solcore.Synthesis.Source.NestedCall.CheckedScenario)
    (expected : List (String × Word × Json × Json)) : IO Json := do
  let observed := Solcore.Synthesis.Source.NestedCall.observe value bindings 20000
  ensure ((← string observed "status") == "complete" && (← field observed "initialAccounts") == emptyAccounts)
    "nested fixture did not start fresh and complete"
  let result ← rows observed
  ensure (result.size == expected.length && result.size == value.transactions.length) "nested transaction count changed"
  for ((status, output, state, events), index) in expected.zipIdx do
    let row := result[index]!
    ensure (some (← string row "id") == (value.transactions[index]?).map (·.id) &&
      (← natural row "index") == index) "stable transaction identity changed"
    ensure ((← string row "status") == status && (← string row "output") == encoded output)
      "nested root outcome/payload differs from golden"
    ensure ((← field row "committedAccounts") == state) "nested committed accounts differ from golden"
    ensure ((← field row "logs") == events) "nested log rollback/order differs from golden"
  ensure ((← field observed "finalAccounts") == (← field result[result.size - 1]! "committedAccounts") &&
    (← rows observed "unexecuted").isEmpty && (← field observed "stoppedAt") == Json.null)
    "nested final history metadata differs from committed prefixes"
  ensure (Solcore.Synthesis.Source.NestedCall.observe value bindings 20000 == observed) "observer reused a previous world"
  return observed

private def referenceChecks : IO Json := do
  let identity ← makePlan (.var 0)
  let singles : List (Nat × String × Nat × Json × Json) := [
    (0, "returned", 0, accounts (w 0) (w 0) (w 0) (w 1), committed 0 0 0),
    (1, "returned", 3, accounts (w 1) (w 2) (w 0) (w 0), childReverted 1 2),
    (2, "reverted", 4, emptyAccounts, emptyLogs),
    (3, "reverted", 7, emptyAccounts, emptyLogs),
    (4, "returned", 8, accounts (w 4) (w 4) (w 4) (w 1) 7 1, committed 4 4 4),
    (5, "returned", 11, accounts (w 5) (w 6) (w 0) (w 0), childReverted 5 6),
    (6, "reverted", 12, emptyAccounts, emptyLogs),
    (7, "reverted", 15, emptyAccounts, emptyLogs)]
  for (input, status, output, state, events) in singles do
    let _ ← checkHistory (← scenario identity [w input]) [(status, w output, state, events)]
  let _ ← checkHistory (← scenario identity [Word.maximum]) [("reverted", Word.maximum, emptyAccounts, emptyLogs)]
  let high := w (2 ^ 255)
  let _ ← checkHistory (← scenario identity [high]) [("returned", Word.zero,
    accounts high high high (w 1), logs [(101, 1, high), (102, 2, high), (101, 3, high)])]
  let mixed ← scenario identity ([4, 5, 4].map w)
  let history ← checkHistory mixed [
    ("returned", w 8, accounts (w 4) (w 4) (w 4) (w 1) 7 1, committed 4 4 4),
    ("returned", w 19, accounts (w 9) (w 10) (w 4) (w 1) 7 1, childReverted 9 10),
    ("returned", w 21, accounts (w 13) (w 8) (w 8) (w 2) 6 2, committed 13 8 8)]
  let _ ← checkHistory (← scenario identity ([4, 6, 0].map w)) [
    ("returned", w 8, accounts (w 4) (w 4) (w 4) (w 1) 7 1, committed 4 4 4),
    ("reverted", w 20, accounts (w 4) (w 4) (w 4) (w 1) 7 1, emptyLogs),
    ("returned", w 8, accounts (w 4) (w 4) (w 4) (w 2) 7 1, committed 4 4 4)]
  -- The same helper's fresh private cell is reset on each successful child call.
  let privateStep := Wire.Expr.letE (.newCell .word (word 0))
    (.letE (.storeCell (.var 0) (.binary .wordAdd (.loadCell (.var 0)) (word 2)))
      (.binary .wordAdd (.var 2) (.loadCell (.var 1))))
  let mutablePlan ← makePlan privateStep (.binary .wordSub entry (word 1))
  let _ ← checkHistory (← scenario mutablePlan ([0, 1, 0].map w)) [
    ("returned", w 1, accounts (w 0) (w 1) (w 1) (w 1), committed 0 1 1),
    ("returned", w 5, accounts (w 1) (w 4) (w 1) (w 1), childReverted 1 4),
    ("returned", w 3, accounts (w 1) (w 2) (w 2) (w 2), committed 1 2 2)]
  let changedBindings : Bindings := ⟨⟨33, by decide⟩, ⟨201, by decide⟩, ⟨202, by decide⟩⟩
  let relocated := Solcore.Synthesis.Source.NestedCall.observe mixed changedBindings 20000
  let originalRows ← rows history
  let relocatedRows ← rows relocated
  for index in List.range originalRows.size do
    ensure ((← string originalRows[index]! "output") == (← string relocatedRows[index]! "output"))
      "call payload depended on fixture addresses"
    let accountRows ← rows relocatedRows[index]! "committedAccounts"
    ensure ((← string accountRows[0]! "address") == "201" && (← string accountRows[1]! "address") == "202")
      "observer did not use actual role bindings"
  let input := Solcore.Synthesis.Stateful.NestedCallExecution.inputData bindings (w 4)
  ensure (input.bytes.size == 68 && input.wordBE? (w 4) == some (w 102) &&
    input.wordBE? (w 36) == some (w 4)) "parent ABI did not bind exact child/input words"
  ensure (identity.parentProgram.check && identity.childProgram.check &&
    identity.parentProgram.resultType == .sum .word (.sum .word .word) &&
    identity.childProgram.resultType == .sum .word (.sum .word .word)) "both contracts must retain outcomeV1 admission"
  let saved ← imported mixed
  ensure ((← get (Solcore.Synthesis.Source.NestedCall.replayCase saved 20000)) == saved) "imported call case did not replay"
  ensure ((← get (Solcore.Synthesis.Source.NestedCall.replayCase (saved.setObjVal! "directCore" (toJson "forged")) 20000)) == saved)
    "replay consumed a stored expected result"
  let changed ← imported (← scenario identity ([1, 2, 3].map w))
  ensure ((← field saved "programs") == (← field changed "programs") && (← string saved "source") == (← string changed "source"))
    "runtime inputs leaked into the original code or emitted source"
  return saved

private def resourceChecks : IO Unit := do
  let slow := (List.range 20).foldl (fun body _ => Wire.Expr.letE (word 1) body) (word 8)
  let plan ← makePlan (.ifE (.binary .wordEq (.var 0) (word 8)) slow (.var 0))
  let value ← scenario plan ([4, 5, 4].map w)
  let low := Solcore.Synthesis.Source.NestedCall.observe value bindings 0
  let first := (← rows low)[0]!
  ensure ((← string low "status") == "incomplete" && (← string first "status") == "out-of-fuel" &&
    (← field first "logs") == Json.null && (← rows low "unexecuted").size == 2 &&
    (← field low "finalAccounts") == emptyAccounts) "exhausted nested state/logs were committed"
  let mut afterPrefixes := false
  for fuel in List.range 700 do
    let observed := Solcore.Synthesis.Source.NestedCall.observe value bindings fuel
    let result ← rows observed
    if result.size == 3 then
      if (← string result[2]! "status") == "out-of-fuel" then
        afterPrefixes := true
        ensure ((← field result[2]! "logs") == Json.null &&
          (← field result[2]! "committedAccounts") == (← field result[1]! "committedAccounts") &&
          (← field observed "finalAccounts") == accounts (w 9) (w 10) (w 4) (w 1) 7 1)
          "nested fuel exhaustion after completed prefixes changed committed state"
  ensure afterPrefixes "resource regression did not retain a completed child-rollback prefix"

private def generationChecks : IO Json := do
  for seed in List.range 12 do
    let mut minimum : Option Nat := none
    for budget in List.range 513 do
      if minimum.isNone && (Solcore.Synthesis.Source.NestedCall.generatedScenario (Seed.ofNat seed) budget).isOk then minimum := some budget
    let some budget := minimum | throw (IO.userError "call template does not fit 512-node budget")
    let (value, _) ← get (Solcore.Synthesis.Source.NestedCall.generatedScenario (Seed.ofNat seed) budget)
    ensure (Solcore.Synthesis.Core.NestedCall.combinedNodes value.plan.step ≤ budget && value.transactions.length == 3 &&
      value.plan.step.helpers.length == 1 + seed % 3) "call recipe lost full node/transaction/helper bounds"
    rejected (Solcore.Synthesis.Source.NestedCall.generatedScenario (Seed.ofNat seed) (budget - 1)) "undersized node budget accepted"
  rejected (Solcore.Synthesis.Source.NestedCall.generatedScenario (Seed.ofNat 0) 513) "oversized node budget accepted"
  let corpus := Solcore.Synthesis.Source.NestedCall.generateCases (Seed.ofNat 0) 384 4 256 20000
  ensure (corpus == Solcore.Synthesis.Source.NestedCall.generateCases (Seed.ofNat 0) 384 4 256 20000) "call generation nondeterministic"
  let generated ← rows corpus "cases"
  ensure (generated.size == 4 && (← natural corpus "attempted") ≤ 256)
    "call count does not count complete scenarios"
  for saved in generated do
    let value ← get (Solcore.Synthesis.Source.NestedCall.caseProgram saved)

    ensure (value.transactions.length == 3 && Solcore.Synthesis.Core.NestedCall.combinedNodes value.plan.step ≤ 384)
      "generated case escaped bounded call profile"
    ensure ((← get (Solcore.Synthesis.Source.NestedCall.replayCase saved 20000)) == saved) "generated history provenance did not replay"
    let low ← get (Solcore.Synthesis.Source.NestedCall.replayCase saved 0)
    ensure ((← natural low "executionFuel") == 0 && (← field low "provenance") == (← field saved "provenance"))
      "fresh replay fuel changed the generation validation budget"
  let saved := generated[0]!
  let origin ← field (← field saved "provenance") "origin"
  let some seed := (← string origin "seed").toNat? | throw (IO.userError "invalid generated seed")
  let low := Solcore.Synthesis.Source.NestedCall.generateCases (Seed.ofNat seed) 384 1 1 0
  let excluded ← rows low "excluded"
  ensure ((← rows low "cases").isEmpty && (← string excluded[0]! "category") == "inconclusive-resource")
    "call generation resource exhaustion was not distinguished"
  ensure ((← rows (Solcore.Synthesis.Source.NestedCall.generateCases (Seed.ofNat seed) 384 2 1 20000) "cases").size == 1 &&
    (← natural (Solcore.Synthesis.Source.NestedCall.generateCases (Seed.ofNat seed) 384 0 10 20000) "attempted") == 0 &&
    (← rows (Solcore.Synthesis.Source.NestedCall.generateCases (Seed.ofNat seed) 384 1 0 20000) "cases").isEmpty)
    "call generator ignored count/attempt bounds"
  return saved

private def tamperingChecks (saved generated : Json) : IO Unit := do
  let transactionRows ← rows saved
  let first := transactionRows[0]!
  for (name, bad) in [("id", toJson ""), ("id", toJson "not valid"),
      ("id", toJson (String.ofList (List.replicate 65 'a'))), ("input", toJson "01"),
      ("target", toJson "child"), ("callee", toJson "parent"), ("value", toJson "1"),
      ("extra", toJson true)] do
    rejected (Solcore.Synthesis.Source.NestedCall.decodeTransactions (toJson [first.setObjVal! name bad]))
      "noncanonical call transaction accepted"
  rejected (Solcore.Synthesis.Source.NestedCall.decodeTransactions (toJson [first, first])) "duplicate transaction IDs accepted"
  rejected (Solcore.Synthesis.Source.NestedCall.decodeTransactions (toJson ([] : List Json))) "empty transaction list accepted"
  rejected (Solcore.Synthesis.Source.NestedCall.decodeTransactions (toJson (List.replicate 4 first))) "unbounded transaction count accepted"
  for (name, bad) in [("initialState", Json.mkObj [("call", toJson [first])]),
      ("observedSlots", toJson (["1", "0"] : List String)), ("executionFuel", toJson (10000001 : Nat)),
      ("programs", Json.mkObj [])] do
    rejected (Solcore.Synthesis.Source.NestedCall.caseProgram (saved.setObjVal! name bad)) "invalid call case boundary accepted"
  let programs ← field saved "programs"
  for name in ["parent", "child"] do
    let other ← field programs (if name == "parent" then "child" else "parent")
    rejected (Solcore.Synthesis.Source.NestedCall.caseProgram
      (saved.setObjVal! "programs" (programs.setObjVal! name other)))
      "a different fully checked contract replaced a canonical program"
  let provenance ← field generated "provenance"
  let origin ← field provenance "origin"
  let withOrigin := fun changed => generated.setObjVal! "provenance" (provenance.setObjVal! "origin" changed)
  for name in ["generatorVersion", "profileVersion", "functionVersion", "templateVersion", "stepProfileVersion",
      "stepFunctionVersion", "stepTemplateVersion", "emitterVersion", "wrapperVersion", "features"] do
    rejected (Solcore.Synthesis.Source.NestedCall.replayCase (generated.setObjVal! "provenance" (provenance.setObjVal! name Json.null)) 20000)
      "tampered call provenance accepted"
  for (name, bad) in [("seed", toJson "00"), ("finalSeed", toJson "bad"),
      ("maxProgramNodes", toJson (513 : Nat)), ("stepOrigin", Json.null), ("sequenceIndices", Json.null),
      ("validationFuel", toJson (10000001 : Nat)), ("validationFuel", toJson (0 : Nat))] do
    rejected (Solcore.Synthesis.Source.NestedCall.replayCase (withOrigin (origin.setObjVal! name bad)) 20000)
      "tampered generated call recipe accepted"
  let plan ← field saved "callPlan"
  rejected (Solcore.Synthesis.Source.NestedCall.checkedPlan (plan.setObjVal! "extra" Json.null)) "noncanonical call plan accepted"
  rejected (Solcore.Synthesis.Source.NestedCall.replayCase (saved.setObjVal! "source" (toJson "stale")) 20000) "stale source accepted"
  let contract ← field saved "contracts"
  for role in ["parent", "child"] do
    let metadata ← field contract role
    for (name, wrong) in [("constructorValue", toJson "1"), ("selector", toJson "0x00000000")] do
      rejected (Solcore.Synthesis.Source.NestedCall.replayCase
        (saved.setObjVal! "contracts" (contract.setObjVal! role (metadata.setObjVal! name wrong))) 20000)
        "wrong call constructor or ABI metadata accepted"
  let bindingJson := Solcore.Synthesis.Stateful.NestedCallExecution.bindingsJson bindings
  ensure ((Solcore.Synthesis.Stateful.NestedCallExecution.decodeBindings bindingJson).isOk) "valid bindings rejected"
  for (name, value) in [("caller", "017"), ("parent", "17"), ("child", "101"),
      ("parent", "9"), ("child", "0"), ("parent", "10"), ("child", "10"),
      ("child", "17"), ("parent", "256"), ("child", "256"), ("caller", toString (2 ^ 160))] do
    rejected (Solcore.Synthesis.Stateful.NestedCallExecution.decodeBindings (bindingJson.setObjVal! name (toJson value)))
      "invalid execution bindings accepted"

private def shrinkChecks : IO Unit := do
  let plan ← makePlan (Aggregate.template 3 (word 2))
  let value ← scenario plan [Word.maximum, w 7, Word.maximum]
  let saved ← imported value
  let candidates ← get (Solcore.Synthesis.Source.NestedCall.shrinkCases saved 1000 20000)
  let result ← rows candidates "cases"
  ensure (!result.isEmpty && candidates == (← get (Solcore.Synthesis.Source.NestedCall.shrinkCases saved 1000 20000)))
    "call reductions were empty or nondeterministic"
  let mut removed := false
  let mut loweredInput := false
  let mut changedStep := false
  let mut seen : List String := []
  for row in result do
    let reduced ← get (Solcore.Synthesis.Source.NestedCall.caseProgram row)
    ensure (decide (Solcore.Synthesis.Source.NestedCall.StrictlySmaller reduced value) && reduced.plan.parentProgram.check && reduced.plan.childProgram.check &&
      reduced.plan.step.helpers.length == value.plan.step.helpers.length &&
      Aggregate.bindingInventory reduced.plan.step == Aggregate.bindingInventory value.plan.step &&
      decide ((reduced.transactions.map (·.id)).Sublist (value.transactions.map (·.id))))
      "call reduction lost strict complexity, host typing or stable scope/IDs"
    let key := (Json.mkObj [("programs", Solcore.Synthesis.Source.NestedCall.programsJson reduced.plan),
      ("transactions", Solcore.Synthesis.Source.NestedCall.transactionsJson reduced.transactions)]).compress
    ensure (!seen.contains key) "duplicate call reduction"
    seen := key :: seen
    removed := removed || reduced.transactions.length < value.transactions.length
    loweredInput := loweredInput || (reduced.transactions.length == value.transactions.length &&
      Solcore.Synthesis.Source.NestedCall.inputWeight reduced < Solcore.Synthesis.Source.NestedCall.inputWeight value)
    changedStep := changedStep || Solcore.Synthesis.Source.NestedCall.programsJson reduced.plan != Solcore.Synthesis.Source.NestedCall.programsJson value.plan
    ensure ((← get (Solcore.Synthesis.Source.NestedCall.replayCase row 20000)) == row) "reduced call case did not replay"
  ensure (removed && loweredInput && changedStep) "call shrink omitted sequence/input/step axes"
  ensure ((← rows (← get (Solcore.Synthesis.Source.NestedCall.shrinkCases saved 2 20000)) "cases") == result.extract 0 2 &&
    (← rows (← get (Solcore.Synthesis.Source.NestedCall.shrinkCases saved 0 20000)) "cases").isEmpty) "call shrink limit changed ordering"
  let first := result[0]!
  let reduced ← get (Solcore.Synthesis.Source.NestedCall.caseProgram first)
  let badParent := Json.mkObj [("kind", toJson "reduced"), ("parentPlan", Solcore.Synthesis.Source.NestedCall.planJson reduced.plan),
    ("parentPrograms", Solcore.Synthesis.Source.NestedCall.programsJson reduced.plan),
    ("parentTransactions", Solcore.Synthesis.Source.NestedCall.transactionsJson reduced.transactions)]
  let provenance ← field first "provenance"
  rejected (Solcore.Synthesis.Source.NestedCall.replayCase (first.setObjVal! "provenance" (provenance.setObjVal! "origin" badParent)) 20000)
    "non-strict reduction provenance accepted"

def testSourceNestedCallCases : IO Unit := do
  let imported ← referenceChecks
  resourceChecks
  let generated ← generationChecks
  tamperingChecks imported generated
  shrinkChecks

end Tests.SourceNestedCallCases
