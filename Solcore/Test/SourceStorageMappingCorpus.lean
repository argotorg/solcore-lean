import Solcore.Synthesis.Source.StorageMappingCases

/-! The fixed Keccak-mapping corpus checks actual original Core histories
against independently computed expectations: status, payload and every
declared committed slot after every transaction, where the declared slots are
the counter and the `keccak256(1 ++ key)` entry slots of every key and wrapping
successor. Coverage describes the checked step AST, the transaction keys,
inputs and completions, and static key aliasing. Source/Rust/EVM agreement is
a separate external validation. -/
set_option autoImplicit false

namespace Tests.SourceStorageMappingCorpus
open Lean Solcore.Core Solcore.ContractRuntime Solcore.Synthesis.Core Solcore.Synthesis.Source

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
  ("generatorVersion", generatorVersion), ("profileVersion", StorageMapping.profileVersion),
  ("functionVersion", Solcore.Synthesis.Core.StorageMapping.version),
  ("templateVersion", StorageMapping.templateVersion), ("stepProfileVersion", Aggregate.profileVersion),
  ("stepFunctionVersion", Aggregates.version), ("stepTemplateVersion", Aggregate.templateVersion),
  ("emitterVersion", StorageMapping.emitterVersion), ("wrapperVersion", StorageMapping.wrapperVersion)]

private def words (values : List Word) : List String := values.map fun value => toString value.val

/-- Imported entries are emitted from their saved plan and sequence; generated
entries are regenerated from their seed. Both are checked by full replay. -/
private def entryCase (entry : Json) (fuel : Nat) : Except String Json := do
  if let .ok request := entry.getObjVal? "generation" then
    let some seed := (← request.getObjValAs? String "seed").toNat? | throw "invalid generation seed"
    let corpus := StorageMapping.generateCases (Seed.ofNat seed) (← request.getObjValAs? Nat "maxProgramNodes") 1 1 fuel
    require ((← string corpus "status") == "complete") "generated entry was excluded"
    let some saved := (← corpus.getObjValAs? (Array Json) "cases")[0]? | throw "generated entry has no case"
    return saved
  let plan ← StorageMapping.checkedPlan (← entry.getObjVal? "mappingPlan")
  let scenario ← StorageMapping.checkedScenario plan (← StorageMapping.decodeTransactions (← entry.getObjVal? "transactions"))
  StorageMapping.emitCase scenario (Json.mkObj [("kind", toJson "imported")]) fuel

private def templates (saved : Json) : Except String (List Nat) := do
  let origin ← (← saved.getObjVal? "provenance").getObjVal? "origin"
  if (← string origin "kind") != "mapping-generated" then return []
  let helpers ← (← origin.getObjVal? "stepOrigin").getObjValAs? (List Json) "helpers"
  helpers.mapM fun helper => helper.getObjValAs? Nat "template"

def validateManifest (manifest : Json) (fuel : Nat := 1000000) : Except String Json := do
  require ((← string manifest "schema") == "solcore-lean.semantic-storage-corpus-manifest.v1" &&
    (← string manifest "profile") == "stateful-mapping" &&
    (← string manifest "coverageKind") == "step-core-ast-features") "unexpected mapping manifest scope"
  for (key, expected) in versions do
    require ((← string manifest key) == expected) ("mapping manifest changed " ++ key)
  let requiredFeatures ← strings manifest "requiredFeatures"
  let requiredInputs ← strings manifest "requiredInputs"
  require (sameMembers requiredInputs (words StorageMapping.boundaryInputs))
    "mapping corpus must require all six boundary inputs"
  let requiredKeys ← strings manifest "requiredKeys"
  require (sameMembers requiredKeys (words StorageMapping.keyBank)) "mapping corpus must require the whole key bank"
  require ((← strings manifest "requiredAliases") == StorageMapping.aliasCatalog)
    "mapping corpus must require the canonical alias catalog"
  require ((← manifest.getObjValAs? (List Nat) "requiredHelperCounts") == [1, 2, 3] &&
    (← manifest.getObjValAs? (List Nat) "requiredTransactionCounts") == [1, 2, 3])
    "mapping corpus must require one to three helpers and transactions"
  require ((← (← manifest.getObjVal? "generationRecipeRequirements").getObjValAs? (List Nat) "templates") == [0, 1, 2, 3])
    "mapping corpus must require all four step templates"
  require ((← strings manifest "requiredOutcomes") == ["returned", "reverted"]) "mapping corpus must require both outcomes"
  let requiredPatterns ← strings manifest "requiredCompletionPatterns"
  require (!requiredPatterns.isEmpty) "mapping corpus must require completion patterns"
  let entries ← manifest.getObjValAs? (Array Json) "cases"
  require (0 < entries.size && entries.size ≤ 64) "mapping corpus must contain 1..64 scenarios"
  let mut identifiers : List String := []
  let mut features : List String := []
  let mut inputs : List String := []
  let mut keys : List String := []
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
    require (!identifiers.contains identifier) ("duplicate mapping corpus id " ++ identifier)
    identifiers := identifier :: identifiers
    let saved ← entryCase entry fuel
    require ((← StorageMapping.replayCase saved fuel) == saved) ("mapping corpus entry did not replay: " ++ identifier)
    let scenario ← StorageMapping.caseProgram saved
    if !(entry.getObjVal? "generation").isOk then
      require ((← saved.getObjVal? "mappingPlan") == (← entry.getObjVal? "mappingPlan") &&
        (← saved.getObjVal? "transactions") == (← entry.getObjVal? "transactions"))
        ("imported mapping entry is not canonical: " ++ identifier)
    let caseFeatures := (← (← saved.getObjVal? "provenance").getObjValAs? (List String) "features").eraseDups
    require (sameMembers (← strings entry "expectedFeatures") caseFeatures)
      ("mapping corpus features changed: " ++ identifier)
    -- The independently derived declaration must equal the observer's; the
    -- observer's own slots come from the separate ABI Keccak.
    let expectedSlots ← entry.getObjValAs? (List String) "expectedSlots"
    require (expectedSlots == words scenario.observedSlots &&
      (← saved.getObjValAs? (List String) "observedSlots") == expectedSlots)
      ("mapping declared slots differ from the independent derivation: " ++ identifier)
    let history := StorageMapping.observe scenario Solcore.Synthesis.Stateful.StorageExecution.fixtureBindings fuel
    require ((← string history "status") == "complete") ("mapping corpus history incomplete: " ++ identifier)
    let statuses ← StorageMapping.checkProtocol scenario history
    let observed ← history.getObjValAs? (List Json) "transactions"
    let expected ← entry.getObjValAs? (List Json) "expectedHistory"
    require (observed.length == expected.length) ("mapping expected history length changed: " ++ identifier)
    for (row, golden) in observed.zip expected do
      let actual := Json.mkObj [("id", ← row.getObjVal? "id"), ("status", ← row.getObjVal? "status"),
        ("output", ← row.getObjVal? "output"), ("committedStorage", ← row.getObjVal? "committedStorage")]
      require (actual == golden) ("original Core differs from the independent history: " ++ identifier ++ " " ++ actual.compress)
    transactionTotal := transactionTotal + observed.length
    slotTotal := slotTotal + expectedSlots.length
    features := (features ++ caseFeatures).eraseDups
    inputs := (inputs ++ scenario.transactions.map fun tx => toString tx.input.val).eraseDups
    keys := (keys ++ scenario.transactions.map fun tx => toString tx.key.val).eraseDups
    aliases := (aliases ++ StorageMapping.aliases scenario.transactions).eraseDups
    helperCounts := (helperCounts ++ [scenario.plan.step.helpers.length]).eraseDups
    transactionCounts := (transactionCounts ++ [scenario.transactions.length]).eraseDups
    templateUnion := (templateUnion ++ (← templates saved)).eraseDups
    outcomes := (outcomes ++ statuses).eraseDups
    patterns := (patterns ++ [String.intercalate "," statuses]).eraseDups
  require (requiredFeatures.all features.contains) "mapping corpus misses a required step feature"
  require (requiredInputs.all inputs.contains && requiredKeys.all keys.contains) "mapping corpus misses an input or key"
  require (StorageMapping.aliasCatalog.all aliases.contains) "mapping corpus misses an alias kind"
  require ([1, 2, 3].all helperCounts.contains && [1, 2, 3].all transactionCounts.contains)
    "mapping corpus misses a helper or transaction count"
  require ([0, 1, 2, 3].all templateUnion.contains) "mapping corpus misses a generated template"
  require (["returned", "reverted"].all outcomes.contains && requiredPatterns.all patterns.contains)
    "mapping corpus misses an observed outcome or completion pattern"
  return Json.mkObj [("profile", toJson "stateful-mapping"), ("scenarios", toJson entries.size),
    ("transactions", toJson transactionTotal), ("declaredSlots", toJson slotTotal),
    ("aliases", toJson aliases), ("patterns", toJson patterns)]

private def checked {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def rejects {α : Type} (result : Except String α) (message : String) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError ("invalid mapping corpus unexpectedly passed: " ++ message))

/-- Solidity's order, `keccak256(key ++ 1)`, which the pinned std does not use. -/
private def soliditySlot (key : Word) : String :=
  toString ((decodeWordBytesBE? (Solcore.Abi.V1.Keccak256.hash
    (encodeWordBytesBE key ++ encodeWordBytesBE (Word.ofNatModulo 1)))).getD Word.zero).val

def testSourceStorageMappingCorpus : IO Unit := do
  let manifest ← checked (Json.parse (← IO.FS.readFile "scripts/semantic-mapping-corpus.json"))
  let summary ← checked (validateManifest manifest)
  let entries ← checked (manifest.getObjValAs? (Array Json) "cases")
  let some first := entries[0]? | throw (IO.userError "missing first mapping case")
  let some generatedEntry := entries.find? (fun entry => (entry.getObjVal? "generation").isOk) |
    throw (IO.userError "missing generated mapping case")
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
  let firstTransaction ← checked (StorageMapping.decodeTransactions (.arr #[transactions[0]!]))
  let some tx := firstTransaction.head? | throw (IO.userError "missing first mapping transaction")
  let slots ← checked (first.getObjValAs? (Array Json) "expectedSlots")
  let solidity := toJson (soliditySlot tx.key)
  rejects (validateManifest (replace first (first.setObjVal! "expectedSlots"
    (.arr (slots.set! 1 solidity))))) "Solidity-order declared slot"
  rejects (validateManifest (withRow 0 (row.setObjVal! "committedStorage"
    (.arr (storage.set! 1 (storage[1]!.setObjVal! "slot" solidity)))))) "Solidity-order committed slot"
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
    (.arr (transactions.set! 0 (transactions[0]!.setObjVal! "key" (toJson "4"))))))) "key without calldata"
  -- A consistent key change with its own calldata is canonical but no longer
  -- matches the saved slots and history.
  let changedKey := Word.ofNatModulo (tx.key.val + 2)
  rejects (validateManifest (replace first (first.setObjVal! "transactions"
    (.arr (transactions.set! 0 ((transactions[0]!.setObjVal! "key" (toJson (toString changedKey.val))).setObjVal!
      "calldata" (toJson (Solcore.Synthesis.Stateful.StorageMappingExecution.calldata tx.flags changedKey tx.input))))))))
    "consistent key change"
  rejects (validateManifest (replace first (first.setObjVal! "expectedFeatures" (toJson ([] : List String))))) "features"
  rejects (validateManifest (replace generatedEntry (generatedEntry.setObjVal! "generation"
    (Json.mkObj [("seed", toJson "13"), ("maxProgramNodes", toJson (384 : Nat))])))) "changed seed"
  rejects (validateManifest (manifest.setObjVal! "cases" (.arr (#[first] ++ entries)))) "duplicate entry"
  for (key, value) in [
      ("profile", toJson "stateful-keyed-storage"), ("templateVersion", toJson "forged"),
      ("functionVersion", toJson "core-keyed-storage-contract-v1"),
      ("cases", .arr #[]), ("requiredInputs", toJson ([] : List String)),
      ("requiredKeys", toJson (["0"] : List String)), ("requiredHelperCounts", toJson [1, 2]),
      ("requiredAliases", toJson StorageMapping.aliasCatalog.reverse),
      ("requiredAliases", toJson (["repeated-key"] : List String)),
      ("requiredCompletionPatterns", toJson (["reverted,reverted,reverted"] : List String))] do
    rejects (validateManifest (manifest.setObjVal! key value)) key
  rejects (validateManifest manifest 0) "zero fuel"
  IO.println summary.compress

end Tests.SourceStorageMappingCorpus
