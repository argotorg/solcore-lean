import Solcore.Synthesis.Source.StorageLedgerCases

/-! The fixed sender-keyed ledger corpus checks actual original Core histories
against independently computed expectations: status, payload and every
declared committed slot after every transaction, where the declared slots are
the counter and the `keccak256(1 ++ k)` entry slots of every transaction's
sender and recipient. Coverage describes the checked step AST, the senders,
recipients, amounts and inputs, distinct-sender counts, both revert causes and
static key aliasing. Source/Rust/EVM agreement is a separate external
validation. -/
set_option autoImplicit false

namespace Tests.SourceStorageLedgerCorpus
open Lean Solcore.Core Solcore.ContractRuntime Solcore.Synthesis.Core Solcore.Synthesis.Source
open Solcore.Synthesis.Stateful.StorageLedgerExecution (senders)

private def require (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

private def string (value : Json) (key : String) : Except String String :=
  value.getObjValAs? String key

private def strings (value : Json) (key : String) : Except String (List String) := do
  let values ← value.getObjValAs? (List String) key
  require (values.eraseDups == values) (key ++ " contains duplicates")
  return values

private def sameMembers (left right : List String) : Bool :=
  left.all right.contains && right.all left.contains

private def versions : List (String × String) := [
  ("generatorVersion", generatorVersion), ("profileVersion", StorageLedger.profileVersion),
  ("functionVersion", Solcore.Synthesis.Core.StorageLedger.version),
  ("templateVersion", StorageLedger.templateVersion), ("stepProfileVersion", Aggregate.profileVersion),
  ("stepFunctionVersion", Aggregates.version), ("stepTemplateVersion", Aggregate.templateVersion),
  ("emitterVersion", StorageLedger.emitterVersion), ("wrapperVersion", StorageLedger.wrapperVersion)]

private def words (values : List Word) : List String := values.map fun value => toString value.val

/-- Imported entries are emitted from their saved plan and sequence; generated
entries are regenerated from their seed. Both are checked by full replay. -/
private def entryCase (entry : Json) (fuel : Nat) : Except String Json := do
  if let .ok request := entry.getObjVal? "generation" then
    let some seed := (← request.getObjValAs? String "seed").toNat? | throw "invalid generation seed"
    let corpus := StorageLedger.generateCases (Seed.ofNat seed) (← request.getObjValAs? Nat "maxProgramNodes") 1 1 fuel
    require ((← string corpus "status") == "complete") "generated entry was excluded"
    let some saved := (← corpus.getObjValAs? (Array Json) "cases")[0]? | throw "generated entry has no case"
    return saved
  let plan ← StorageLedger.checkedPlan (← entry.getObjVal? "ledgerPlan")
  let scenario ← StorageLedger.checkedScenario plan (← StorageLedger.decodeTransactions (← entry.getObjVal? "transactions"))
  StorageLedger.emitCase scenario (Json.mkObj [("kind", toJson "imported")]) fuel

private def templates (saved : Json) : Except String (List Nat) := do
  let origin ← (← saved.getObjVal? "provenance").getObjVal? "origin"
  if (← string origin "kind") != "ledger-generated" then return []
  let helpers ← (← origin.getObjVal? "stepOrigin").getObjValAs? (List Json) "helpers"
  helpers.mapM fun helper => helper.getObjValAs? Nat "template"

def validateManifest (manifest : Json) (fuel : Nat := 1000000) : Except String Json := do
  require ((← string manifest "schema") == "solcore-lean.semantic-storage-corpus-manifest.v1" &&
    (← string manifest "profile") == "stateful-ledger" &&
    (← string manifest "coverageKind") == "step-core-ast-features") "unexpected ledger manifest scope"
  for (key, expected) in versions do
    require ((← string manifest key) == expected) ("ledger manifest changed " ++ key)
  let requiredFeatures ← strings manifest "requiredFeatures"
  require (sameMembers (← strings manifest "requiredInputs") (words StorageLedger.boundaryInputs))
    "ledger corpus must require all six boundary inputs"
  require (sameMembers (← strings manifest "requiredSenders") (senders.map fun sender => toString sender.val))
    "ledger corpus must require all three senders"
  require (sameMembers (← strings manifest "requiredRecipients") (words StorageLedger.recipientBank))
    "ledger corpus must require the whole recipient bank"
  require (sameMembers (← strings manifest "requiredAmounts") (words StorageLedger.amountBank))
    "ledger corpus must require the whole amount bank"
  require ((← manifest.getObjValAs? (List Nat) "requiredSenderCounts") == [1, 2, 3])
    "ledger corpus must require one to three distinct senders"
  require ((← strings manifest "requiredRevertCauses") == ["odd-flags", "insufficient-balance"])
    "ledger corpus must require both revert causes"
  require ((← strings manifest "requiredAliases") == StorageLedger.aliasCatalog)
    "ledger corpus must require the canonical alias catalog"
  require ((← manifest.getObjValAs? (List Nat) "requiredHelperCounts") == [1, 2, 3] &&
    (← manifest.getObjValAs? (List Nat) "requiredTransactionCounts") == [1, 2, 3])
    "ledger corpus must require one to three helpers and transactions"
  require ((← (← manifest.getObjVal? "generationRecipeRequirements").getObjValAs? (List Nat) "templates") == [0, 1, 2, 3])
    "ledger corpus must require all four step templates"
  require ((← strings manifest "requiredOutcomes") == ["returned", "reverted"]) "ledger corpus must require both outcomes"
  let requiredPatterns ← strings manifest "requiredCompletionPatterns"
  require (!requiredPatterns.isEmpty) "ledger corpus must require completion patterns"
  let entries ← manifest.getObjValAs? (Array Json) "cases"
  require (0 < entries.size && entries.size ≤ 64) "ledger corpus must contain 1..64 scenarios"
  let mut identifiers : List String := []
  let mut features : List String := []
  let mut inputs : List String := []
  let mut senderValues : List String := []
  let mut recipients : List String := []
  let mut amounts : List String := []
  let mut senderCounts : List Nat := []
  let mut causes : List String := []
  let mut aliases : List String := []
  let mut helperCounts : List Nat := []
  let mut transactionCounts : List Nat := []
  let mut templateUnion : List Nat := []
  let mut outcomes : List String := []
  let mut patterns : List String := []
  let mut transactionTotal := 0
  let mut slotTotal := 0
  for entry in entries do
    let identifier ← string entry "id"
    require (!identifiers.contains identifier) ("duplicate ledger corpus id " ++ identifier)
    identifiers := identifier :: identifiers
    let saved ← entryCase entry fuel
    require ((← StorageLedger.replayCase saved fuel) == saved) ("ledger corpus entry did not replay: " ++ identifier)
    let scenario ← StorageLedger.caseProgram saved
    if !(entry.getObjVal? "generation").isOk then
      require ((← saved.getObjVal? "ledgerPlan") == (← entry.getObjVal? "ledgerPlan") &&
        (← saved.getObjVal? "transactions") == (← entry.getObjVal? "transactions"))
        ("imported ledger entry is not canonical: " ++ identifier)
    let caseFeatures := (← (← saved.getObjVal? "provenance").getObjValAs? (List String) "features").eraseDups
    require (sameMembers (← strings entry "expectedFeatures") caseFeatures)
      ("ledger corpus features changed: " ++ identifier)
    -- The independently derived declaration must equal the observer's; the
    -- observer's own slots come from the separate ABI Keccak.
    let expectedSlots ← entry.getObjValAs? (List String) "expectedSlots"
    require (expectedSlots == words scenario.observedSlots &&
      (← saved.getObjValAs? (List String) "observedSlots") == expectedSlots)
      ("ledger declared slots differ from the independent derivation: " ++ identifier)
    let history := StorageLedger.observe scenario Solcore.Synthesis.Stateful.StorageExecution.fixtureBindings fuel
    require ((← string history "status") == "complete") ("ledger corpus history incomplete: " ++ identifier)
    let statuses ← StorageLedger.checkProtocol scenario history
    let observed ← history.getObjValAs? (List Json) "transactions"
    let expected ← entry.getObjValAs? (List Json) "expectedHistory"
    require (observed.length == expected.length) ("ledger expected history length changed: " ++ identifier)
    for (row, golden) in observed.zip expected do
      let actual := Json.mkObj [("id", ← row.getObjVal? "id"), ("status", ← row.getObjVal? "status"),
        ("output", ← row.getObjVal? "output"), ("committedStorage", ← row.getObjVal? "committedStorage")]
      require (actual == golden) ("original Core differs from the independent history: " ++ identifier ++ " " ++ actual.compress)
    for (status, tx) in statuses.zip scenario.transactions do
      if status == "reverted" then
        causes := (causes ++ [if StorageLedger.reverts tx then "odd-flags" else "insufficient-balance"]).eraseDups
    transactionTotal := transactionTotal + observed.length
    slotTotal := slotTotal + expectedSlots.length
    features := (features ++ caseFeatures).eraseDups
    inputs := (inputs ++ scenario.transactions.map fun tx => toString tx.input.val).eraseDups
    senderValues := (senderValues ++ scenario.transactions.map fun tx => toString tx.sender.val).eraseDups
    recipients := (recipients ++ scenario.transactions.map fun tx => toString tx.recipient.val).eraseDups
    amounts := (amounts ++ scenario.transactions.map fun tx => toString tx.amount.val).eraseDups
    senderCounts := (senderCounts ++ [StorageLedger.distinctSenders scenario.transactions]).eraseDups
    aliases := (aliases ++ StorageLedger.aliases scenario.transactions).eraseDups
    helperCounts := (helperCounts ++ [scenario.plan.step.helpers.length]).eraseDups
    transactionCounts := (transactionCounts ++ [scenario.transactions.length]).eraseDups
    templateUnion := (templateUnion ++ (← templates saved)).eraseDups
    outcomes := (outcomes ++ statuses).eraseDups
    patterns := (patterns ++ [String.intercalate "," statuses]).eraseDups
  require (requiredFeatures.all features.contains) "ledger corpus misses a required step feature"
  require ((words StorageLedger.boundaryInputs).all inputs.contains) "ledger corpus misses an input"
  require ((senders.map fun sender => toString sender.val).all senderValues.contains &&
    (words StorageLedger.recipientBank).all recipients.contains && (words StorageLedger.amountBank).all amounts.contains)
    "ledger corpus misses a sender, recipient or amount"
  require ([1, 2, 3].all senderCounts.contains) "ledger corpus misses a distinct-sender count"
  require (["odd-flags", "insufficient-balance"].all causes.contains) "ledger corpus misses a revert cause"
  require (StorageLedger.aliasCatalog.all aliases.contains) "ledger corpus misses an alias kind"
  require ([1, 2, 3].all helperCounts.contains && [1, 2, 3].all transactionCounts.contains)
    "ledger corpus misses a helper or transaction count"
  require ([0, 1, 2, 3].all templateUnion.contains) "ledger corpus misses a generated template"
  require (["returned", "reverted"].all outcomes.contains && requiredPatterns.all patterns.contains)
    "ledger corpus misses an observed outcome or completion pattern"
  return Json.mkObj [("profile", toJson "stateful-ledger"), ("scenarios", toJson entries.size),
    ("transactions", toJson transactionTotal), ("declaredSlots", toJson slotTotal),
    ("causes", toJson causes), ("aliases", toJson aliases), ("patterns", toJson patterns)]

private def checked {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def rejects {α : Type} (result : Except String α) (message : String) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError ("invalid ledger corpus unexpectedly passed: " ++ message))

/-- Solidity's order, `keccak256(key ++ 1)`, which the pinned std does not use. -/
private def soliditySlot (key : Word) : String :=
  toString ((decodeWordBytesBE? (Solcore.Abi.V1.Keccak256.hash
    (encodeWordBytesBE key ++ encodeWordBytesBE (Word.ofNatModulo 1)))).getD Word.zero).val

def testSourceStorageLedgerCorpus : IO Unit := do
  let manifest ← checked (Json.parse (← IO.FS.readFile "scripts/semantic-ledger-corpus.json"))
  let summary ← checked (validateManifest manifest)
  let entries ← checked (manifest.getObjValAs? (Array Json) "cases")
  let some first := entries[0]? | throw (IO.userError "missing first ledger case")
  let some generatedEntry := entries.find? (fun entry => (entry.getObjVal? "generation").isOk) |
    throw (IO.userError "missing generated ledger case")
  -- A tampered entry goes first, so the validator rejects it before it
  -- replays the untouched entries; coverage does not depend on order.
  let replace := fun (original changed : Json) => manifest.setObjVal! "cases"
    (.arr (#[changed] ++ entries.filter (· != original)))
  let history ← checked (first.getObjValAs? (Array Json) "expectedHistory")
  let withRow := fun (index : Nat) (row : Json) =>
    replace first (first.setObjVal! "expectedHistory" (.arr (history.set! index row)))
  let row := history[0]!
  rejects (validateManifest (withRow 0 (row.setObjVal! "output" (toJson ("0x" ++ String.ofList (List.replicate 64 'f'))))))
    "changed output"
  let storage ← checked (row.getObjValAs? (Array Json) "committedStorage")
  rejects (validateManifest (withRow 0 (row.setObjVal! "committedStorage"
    (.arr (storage.set! 0 (storage[0]!.setObjVal! "value" (toJson "7"))))))) "changed counter"
  rejects (validateManifest (withRow 0 (row.setObjVal! "committedStorage"
    (.arr (storage.set! 1 (storage[1]!.setObjVal! "value" (toJson "8"))))))) "changed entry"
  rejects (validateManifest (withRow 0 (row.setObjVal! "committedStorage" (.arr storage.pop)))) "dropped slot"
  let transactions ← checked (first.getObjValAs? (Array Json) "transactions")
  let decoded ← checked (StorageLedger.decodeTransactions (.arr #[transactions[0]!]))
  let some tx := decoded.head? | throw (IO.userError "missing first ledger transaction")
  let slots ← checked (first.getObjValAs? (Array Json) "expectedSlots")
  let senderSlot := toString (Solcore.Synthesis.Stateful.StorageLedgerExecution.senderSlot tx.sender).val
  let some position := slots.findIdx? (· == toJson senderSlot) | throw (IO.userError "sender slot missing")
  let solidity := toJson (soliditySlot (addressToWord tx.sender))
  rejects (validateManifest (replace first (first.setObjVal! "expectedSlots" (.arr (slots.set! position solidity)))))
    "Solidity-order declared sender slot"
  let some committed := storage.findIdx? (fun entry => (entry.getObjVal? "slot").toOption == some (toJson senderSlot)) |
    throw (IO.userError "committed sender slot missing")
  rejects (validateManifest (withRow 0 (row.setObjVal! "committedStorage"
    (.arr (storage.set! committed (storage[committed]!.setObjVal! "slot" solidity)))))) "Solidity-order committed slot"
  rejects (validateManifest (replace first (first.setObjVal! "expectedSlots" (.arr slots.pop)))) "missing declared slot"
  rejects (validateManifest (replace first (first.setObjVal! "expectedSlots" (.arr (slots.push (toJson "2"))))))
    "undeclared extra slot"
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr history.pop)))) "popped history"
  let generatedHistory ← checked (generatedEntry.getObjValAs? (Array Json) "expectedHistory")
  let generatedStatus ← checked (string generatedHistory[0]! "status")
  rejects (validateManifest (replace generatedEntry (generatedEntry.setObjVal! "expectedHistory"
    (.arr (generatedHistory.set! 0 (generatedHistory[0]!.setObjVal! "status"
      (toJson (if generatedStatus == "returned" then "reverted" else "returned")))))))) "flipped status"
  rejects (validateManifest (replace first (first.setObjVal! "transactions"
    (.arr (transactions.set! 0 (transactions[0]!.setObjVal! "recipient" (toJson "4"))))))) "recipient without calldata"
  -- Another fixed sender is canonical but no longer matches the saved slots and history.
  let other := senders.getD ((senders.idxOf tx.sender + 1) % 3) tx.sender
  rejects (validateManifest (replace first (first.setObjVal! "transactions"
    (.arr (transactions.set! 0 (transactions[0]!.setObjVal! "sender" (toJson (toString other.val)))))))) "other sender"
  -- A consistent recipient change with its own calldata is canonical but no
  -- longer matches the saved slots and history.
  let changedRecipient := Word.ofNatModulo (tx.recipient.val + 2)
  rejects (validateManifest (replace first (first.setObjVal! "transactions"
    (.arr (transactions.set! 0 ((transactions[0]!.setObjVal! "recipient" (toJson (toString changedRecipient.val))).setObjVal!
      "calldata" (toJson (Solcore.Synthesis.Stateful.StorageLedgerExecution.calldata tx.flags changedRecipient tx.amount
        tx.input))))))))
    "consistent recipient change"
  rejects (validateManifest (replace first (first.setObjVal! "expectedFeatures" (toJson ([] : List String))))) "features"
  rejects (validateManifest (replace generatedEntry (generatedEntry.setObjVal! "generation"
    (Json.mkObj [("seed", toJson "13"), ("maxProgramNodes", toJson (384 : Nat))])))) "changed seed"
  rejects (validateManifest (manifest.setObjVal! "cases" (.arr (#[first] ++ entries)))) "duplicate entry"
  for (key, value) in [
      ("profile", toJson "stateful-mapping"), ("templateVersion", toJson "forged"),
      ("functionVersion", toJson "core-keccak-mapping-contract-v1"),
      ("cases", .arr #[]), ("requiredInputs", toJson ([] : List String)),
      ("requiredSenders", toJson (["1"] : List String)), ("requiredRecipients", toJson (["0"] : List String)),
      ("requiredAmounts", toJson (["0", "1"] : List String)), ("requiredSenderCounts", toJson [1, 2]),
      ("requiredRevertCauses", toJson (["odd-flags"] : List String)), ("requiredHelperCounts", toJson [1, 2]),
      ("requiredAliases", toJson StorageLedger.aliasCatalog.reverse),
      ("requiredAliases", toJson (["self-transfer"] : List String)),
      ("requiredCompletionPatterns", toJson (["returned,returned,returned,returned"] : List String))] do
    rejects (validateManifest (manifest.setObjVal! key value)) key
  rejects (validateManifest manifest 0) "zero fuel"
  IO.println summary.compress

end Tests.SourceStorageLedgerCorpus
