import Solcore.Synthesis.Source.StorageLedgerCases

/-! Sender-keyed ledger case regressions: exact replay, bounded generation from
an independent sequence stream, canonical transaction and declared-slot
boundaries, static alias kinds, the ledger protocol, and typed reductions over
steps, transactions, senders, recipients, amounts, inputs and flags. Expected
values here are test goldens only; cases and the observer never consume them. -/
set_option autoImplicit false

namespace Tests.SourceStorageLedgerCases
open Lean Solcore.Core Solcore.Synthesis.Core Solcore.Synthesis.Source
open Solcore.ContractRuntime (Address addressToWord)
open Solcore.Synthesis.Core.StorageLedger (CheckedPlan)
open Solcore.Synthesis.Stateful.StorageLedgerExecution (Transaction Bindings senders)

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
private def maximum : Nat := 2 ^ 256 - 1
private def sender (index : Nat) : Address := senders.getD index ⟨0, by decide⟩
private def key (index : Nat) : Nat := (addressToWord (sender index)).val

private def makePlan (body : Wire.Expr) (result : Wire.Expr := entry) : IO CheckedPlan := do
  let some graph := Aggregates.CheckedDAG.ofParts? [body] result |
    throw (IO.userError "ledger fixture failed step admission")
  let some plan := CheckedPlan.ofStep? graph | throw (IO.userError "ledger wrapper failed host admission")
  return plan
/-- Rows are `(sender position, flags, recipient, amount, input)`. -/
private def transactions (values : List (Nat × Nat × Nat × Nat × Nat)) : List Transaction :=
  values.zipIdx.map fun ((from_, flags, recipient, amount, input), index) =>
    ⟨"call-" ++ toString index, sender from_, Word.ofNatModulo flags, Word.ofNatModulo recipient,
      Word.ofNatModulo amount, Word.ofNatModulo input⟩
private def scenario (plan : CheckedPlan) (values : List (Nat × Nat × Nat × Nat × Nat)) :
    IO StorageLedger.CheckedScenario :=
  get (StorageLedger.checkedScenario plan (transactions values))
private def imported (value : StorageLedger.CheckedScenario) (fuel : Nat := 1000000) : IO Json :=
  get (StorageLedger.emitCase value (Json.mkObj [("kind", toJson "imported")]) fuel)

private def referenceChecks : IO Json := do
  let identity ← makePlan (.var 0)
  let value ← scenario identity [(0, 0, key 1, 1, 7), (1, 0, key 1, 2 ^ 64, 3), (2, 1, maximum, 7, 7)]
  let saved ← imported value
  ensure ((← field saved "observedSlots") == toJson ((value.observedSlots.map (·.val)).map toString) &&
    value.observedSlots.length == 5) "case did not declare the counter and every sender and recipient slot"
  ensure ((← get (StorageLedger.replayCase saved 1000000)) == saved) "imported ledger case did not replay"
  ensure ((← get (StorageLedger.replayCase (saved.setObjVal! "directCore" (toJson "forged")) 1000000)) == saved)
    "ledger replay consumed a stored expected result"
  let changed ← imported (← scenario identity [(1, 5, 0, 2, 9), (0, 2, key 2, 1, 1)])
  ensure ((← field saved "program") == (← field changed "program") &&
    (← string saved "source") == (← string changed "source"))
    "senders, recipients, amounts, inputs or flags were substituted into source or Core code"
  -- The first sender credits 7 and pays 1; the second sender's credit of 3 on
  -- top of the received 1 cannot pay 2^64; the third reverts on odd flags.
  let observed := StorageLedger.observe value bindings 1000000
  ensure ((← string observed "status") == "complete" &&
    ((← rows observed).map fun row => (row.getObjValAs? String "status").toOption) ==
      #[some "returned", some "reverted", some "reverted"])
    "ledger scenario did not follow its balances and flags"
  ensure ((← get (StorageLedger.checkProtocol value observed)) == ["returned", "reverted", "reverted"])
    "ledger history broke its protocol"
  ensure ((← rows (StorageLedger.observe value ⟨⟨33, by decide⟩, ⟨202, by decide⟩⟩ 1000000)) == (← rows observed))
    "ledger rows changed with the deployer binding"
  -- A forged history that pays more than the amount, wraps the sender or
  -- reports a sufficient balance as insufficient breaks the protocol.
  let history ← rows observed
  let first := history[0]!
  let firstStorage ← get (first.getObjValAs? (Array Json) "committedStorage")
  let recipient := (Solcore.Synthesis.Stateful.StorageMappingExecution.entrySlot (Word.ofNatModulo (key 1))).val
  let some position := firstStorage.findIdx? (fun row => (row.getObjValAs? String "slot").toOption ==
    some (toString recipient)) | throw (IO.userError "recipient slot missing")
  let overpaid := first.setObjVal! "committedStorage"
    (.arr (firstStorage.set! position (firstStorage[position]!.setObjVal! "value" (toJson "2"))))
  rejected (StorageLedger.checkProtocol value (observed.setObjVal! "transactions" (.arr (history.set! 0 overpaid))))
    "an overpaid recipient passed the ledger protocol"
  let insufficient := history[1]!.setObjVal! "output"
    (toJson ("0x" ++ String.ofList (List.replicate 46 '0') ++ "010000000000000000"))
  rejected (StorageLedger.checkProtocol value (observed.setObjVal! "transactions" (.arr (history.set! 1 insufficient))))
    "an insufficient-balance revert reporting the amount passed the ledger protocol"
  ensure (StorageLedger.aliases (transactions [(0, 0, key 0, 0, 0), (1, 0, key 2, 0, 0), (2, 0, 0, 0, 0)]) ==
      ["self-transfer", "received-then-sent"] &&
    StorageLedger.aliases (transactions [(1, 0, 0, 0, 0), (1, 0, maximum, 0, 0)]) == ["repeated-sender"] &&
    StorageLedger.aliases (transactions [(2, 0, key 0, 0, 0), (0, 0, 0, 0, 0)]) == ["received-then-sent"] &&
    StorageLedger.aliases (transactions [(0, 0, key 1, 0, 0), (1, 0, 0, 0, 0)]) == ["received-then-sent"] &&
    StorageLedger.aliases (transactions [(1, 0, key 0, 0, 0), (0, 0, 0, 0, 0)]) == ["received-then-sent"] &&
    StorageLedger.aliases (transactions [(0, 0, 0, 0, 0), (1, 0, key 0, 0, 0)]) == [])
    "static ledger aliases changed"
  return saved

private def generationChecks : IO Json := do
  for seed in List.range 8 do
    let choices := StorageLedger.sequenceChoices (Seed.ofNat seed)
    ensure (choices.length == 13 &&
      (choices.zip [3, 3, 3, 6, 6, 6, 6, 6, 6, 6, 6, 6, 4]).all (fun (value, bound) => value < bound))
      "sequence choices escaped their banks"
    match StorageLedger.generatedScenario (Seed.ofNat seed) 384 with
    | .error _ => pure ()
    | .ok (value, origin) =>
        ensure (value.transactions.length == 3 &&
          Wire.programNodes value.program ≤ 384 + StorageLedger.hashNodes &&
          value.plan.step.helpers.length == 1 + seed % 3) "ledger recipe lost node/transaction/helper bounds"
        ensure (value.transactions.all fun tx => senders.contains tx.sender &&
            StorageLedger.recipientBank.contains tx.recipient && StorageLedger.amountBank.contains tx.amount &&
            StorageLedger.boundaryInputs.contains tx.input)
          "generated sender, recipient, amount or input escaped its bank"
        ensure ((value.transactions.map fun tx => tx.flags.val % 2 == 1) == StorageLedger.generatedParities (Seed.ofNat seed) &&
          value.transactions.all (fun tx => tx.flags.val < 2))
          "generated flags are not exactly their prescribed parities"
        ensure ((origin.getObjValAs? (List Nat) "sequenceChoices").toOption == some choices)
          "generated origin lost its sequence choices"
  rejected (StorageLedger.generatedScenario (Seed.ofNat 0) 513) "oversized node budget accepted"
  rejected (StorageLedger.generatedScenario (Seed.ofNat 0) Solcore.Synthesis.Core.StorageLedger.programOverhead)
    "undersized node budget accepted"
  let corpus := StorageLedger.generateCases (Seed.ofNat 0) 384 2 64 1000000
  ensure (corpus == StorageLedger.generateCases (Seed.ofNat 0) 384 2 64 1000000) "ledger generation nondeterministic"
  let generated ← rows corpus "cases"
  ensure (generated.size == 2 && (← natural corpus "attempted") ≤ 64 && (← string corpus "status") == "complete")
    "ledger count does not count complete scenarios"
  for saved in generated do
    ensure ((← get (StorageLedger.replayCase saved 1000000)) == saved) "generated ledger provenance did not replay"
    let low ← get (StorageLedger.replayCase saved 0)
    ensure ((← natural low "executionFuel") == 0 && (← field low "provenance") == (← field saved "provenance"))
      "fresh replay fuel changed the generation validation budget"
  let saved := generated[0]!
  let origin ← field (← field saved "provenance") "origin"
  let some seed := (← string origin "seed").toNat? | throw (IO.userError "invalid generated seed")
  let low := StorageLedger.generateCases (Seed.ofNat seed) 384 1 1 1000
  let excluded ← rows low "excluded"
  ensure ((← rows low "cases").isEmpty && (← string excluded[0]! "category") == "inconclusive-resource")
    "ledger generation resource exhaustion was not distinguished"
  ensure ((← natural (StorageLedger.generateCases (Seed.ofNat seed) 384 0 10 1000000) "attempted") == 0 &&
    (← rows (StorageLedger.generateCases (Seed.ofNat seed) 384 1 0 1000000) "cases").isEmpty)
    "ledger generator ignored count/attempt bounds"
  return saved

private def tamperingChecks (saved generated : Json) : IO Unit := do
  let first := (← rows saved)[0]!
  for (name, bad) in [("id", toJson ""), ("id", toJson "not valid"), ("sender", toJson "1"),
      ("sender", toJson ("0" ++ toString (key 0))), ("sender", toJson (toString (key 0 + 2 ^ 160))),
      ("flags", toJson "01"), ("recipient", toJson (toString (2 ^ 256))), ("amount", toJson "01"),
      ("input", toJson "07"), ("calldata", toJson "0x"), ("value", toJson "1"), ("extra", toJson true)] do
    rejected (StorageLedger.decodeTransactions (toJson [first.setObjVal! name bad]))
      "noncanonical ledger transaction accepted"
  -- A consistently re-encoded calldata cannot carry a different recipient than the row.
  let otherCalldata := Solcore.Synthesis.Stateful.StorageLedgerExecution.calldata Word.zero (Word.ofNatModulo 5)
    Word.zero Word.zero
  rejected (StorageLedger.decodeTransactions (toJson [first.setObjVal! "calldata" (toJson otherCalldata)]))
    "calldata that differs from the row's Words accepted"
  rejected (StorageLedger.decodeTransactions (toJson [first, first])) "duplicate transaction IDs accepted"
  rejected (StorageLedger.decodeTransactions (toJson ([] : List Json))) "empty transaction list accepted"
  rejected (StorageLedger.decodeTransactions (toJson (List.replicate 4 first))) "unbounded transaction count accepted"
  let slots ← get (saved.getObjValAs? (Array Json) "observedSlots")
  for (name, bad) in [("initialState", Json.mkObj [("storage", toJson [first])]),
      ("observedSlots", .arr slots.pop), ("observedSlots", .arr (slots.push (toJson "1"))),
      ("observedSlots", .arr slots.reverse), ("executionFuel", toJson (10000001 : Nat)), ("ledgerPlan", Json.null),
      ("program", Wire.encodeProgram {resultType := .word, dataDefinitions := [], body := word 0})] do
    rejected (StorageLedger.caseProgram (saved.setObjVal! name bad)) "invalid ledger case boundary accepted"
  let provenance ← field generated "provenance"
  let origin ← field provenance "origin"
  let withOrigin := fun changed => generated.setObjVal! "provenance" (provenance.setObjVal! "origin" changed)
  for name in ["generatorVersion", "profileVersion", "functionVersion", "templateVersion", "stepProfileVersion",
      "stepFunctionVersion", "stepTemplateVersion", "emitterVersion", "wrapperVersion", "features"] do
    rejected (StorageLedger.replayCase (generated.setObjVal! "provenance" (provenance.setObjVal! name Json.null)) 1000000)
      "tampered ledger provenance accepted"
  for (name, bad) in [("seed", toJson "00"), ("finalSeed", toJson "bad"),
      ("maxProgramNodes", toJson (513 : Nat)), ("stepOrigin", Json.null), ("sequenceChoices", Json.null),
      ("sequenceFlags", Json.null), ("validationFuel", toJson (10000001 : Nat)), ("validationFuel", toJson (0 : Nat))] do
    rejected (StorageLedger.replayCase (withOrigin (origin.setObjVal! name bad)) 1000000)
      "tampered generated ledger recipe accepted"
  let plan ← field saved "ledgerPlan"
  rejected (StorageLedger.checkedPlan (plan.setObjVal! "extra" Json.null)) "noncanonical ledger plan accepted"
  rejected (StorageLedger.checkedPlan (plan.setObjVal! "schema" (toJson "solcore-lean.mapping-plan.v1")))
    "mapping plan schema accepted as a ledger plan"
  rejected (StorageLedger.replayCase (saved.setObjVal! "source" (toJson "stale")) 1000000) "stale source accepted"
  let contract ← field saved "contract"
  rejected (StorageLedger.replayCase (saved.setObjVal! "contract" (contract.setObjVal! "selector" (toJson "0x24b912e5"))) 1000000)
    "the mapping's three-Word selector accepted for the ledger ABI"
  rejected (StorageLedger.replayCase (saved.setObjVal! "schema" (toJson "solcore-lean.semantic-mapping-case.v1")) 1000000)
    "mapping case schema accepted by the ledger tool"

private def shrinkChecks : IO Unit := do
  let plan ← makePlan (Aggregate.template 3 (word 2))
  -- Moving the middle transaction to the first sender leaves one distinct sender.
  let value ← scenario plan [(0, 3, maximum, 2 ^ 70, 2 ^ 255), (2, 1, 2 ^ 160 - 1, 2 ^ 64, 3),
    (0, 2, key 1, 7, maximum)]
  let saved ← imported value
  let candidates ← get (StorageLedger.shrinkCases saved 2000 1000000)
  let result ← rows candidates "cases"
  ensure (!result.isEmpty && candidates == (← get (StorageLedger.shrinkCases saved 2000 1000000)))
    "ledger reductions were empty or nondeterministic"
  let mut removed := false
  let mut earlierSender := false
  let mut fewerSenders := false
  let mut loweredRecipient := false
  let mut loweredAmount := false
  let mut loweredInput := false
  let mut loweredFlags := false
  let mut changedStep := false
  let mut seen : List String := []
  for row in result do
    let reduced ← get (StorageLedger.caseProgram row)
    ensure (decide (StorageLedger.StrictlySmaller reduced value) && reduced.program.check &&
      reduced.plan.step.helpers.length == value.plan.step.helpers.length &&
      Aggregate.bindingInventory reduced.plan.step == Aggregate.bindingInventory value.plan.step &&
      decide ((reduced.transactions.map (·.id)).Sublist (value.transactions.map (·.id))))
      "ledger reduction lost strict complexity, host typing or stable scope/IDs"
    ensure ((← field row "observedSlots") == toJson ((reduced.observedSlots.map (·.val)).map toString))
      "a reduced ledger case did not rederive its declared slots"
    let identity := (Json.mkObj [("plan", StorageLedger.planJson reduced.plan),
      ("transactions", StorageLedger.transactionsJson reduced.transactions)]).compress
    ensure (!seen.contains identity) "duplicate ledger reduction"
    seen := identity :: seen
    removed := removed || reduced.transactions.length < value.transactions.length
    let pairs := reduced.transactions.zip value.transactions
    let sameCount := reduced.transactions.length == value.transactions.length
    ensure (pairs.all fun (left, right) => StorageLedger.senderPosition left.sender ≤ StorageLedger.senderPosition right.sender ||
      !sameCount) "a ledger reduction moved a transaction to a later sender"
    earlierSender := earlierSender || (sameCount && pairs.any fun (left, right) =>
      StorageLedger.senderPosition left.sender < StorageLedger.senderPosition right.sender)
    fewerSenders := fewerSenders || (sameCount &&
      StorageLedger.distinctSenders reduced.transactions < StorageLedger.distinctSenders value.transactions)
    loweredRecipient := loweredRecipient || (sameCount && pairs.any fun (left, right) => left.recipient.val < right.recipient.val)
    loweredAmount := loweredAmount || (sameCount && pairs.any fun (left, right) => left.amount.val < right.amount.val)
    loweredInput := loweredInput || (sameCount && pairs.any fun (left, right) => left.input.val < right.input.val)
    loweredFlags := loweredFlags || (sameCount && pairs.any fun (left, right) => left.flags.val < right.flags.val)
    changedStep := changedStep || StorageLedger.planJson reduced.plan != StorageLedger.planJson value.plan
  ensure (removed && earlierSender && fewerSenders && loweredRecipient && loweredAmount && loweredInput &&
    loweredFlags && changedStep)
    "ledger shrink omitted sequence/sender/recipient/amount/input/flags/step axes"
  for row in result.extract 0 3 do
    ensure ((← get (StorageLedger.replayCase row 1000000)) == row) "reduced ledger case did not replay"
  ensure ((← rows (← get (StorageLedger.shrinkCases saved 2 1000000)) "cases") == result.extract 0 2 &&
    (← rows (← get (StorageLedger.shrinkCases saved 0 1000000)) "cases").isEmpty) "ledger shrink limit changed ordering"
  let first := result[0]!
  let reduced ← get (StorageLedger.caseProgram first)
  let badParent := Json.mkObj [("kind", toJson "reduced"), ("parentPlan", StorageLedger.planJson reduced.plan),
    ("parentTransactions", StorageLedger.transactionsJson reduced.transactions)]
  let provenance ← field first "provenance"
  rejected (StorageLedger.replayCase (first.setObjVal! "provenance" (provenance.setObjVal! "origin" badParent)) 1000000)
    "non-strict ledger reduction provenance accepted"

def testSourceStorageLedgerCases : IO Unit := do
  let imported ← referenceChecks
  let generated ← generationChecks
  tamperingChecks imported generated
  shrinkChecks

end Tests.SourceStorageLedgerCases
