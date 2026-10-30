import Solcore.Synthesis.Source.DynamicBytesCases

/-! The fixed bytes corpus checks actual original Core histories against
independently computed expectations: status, payload and slots zero to four
after every transaction. Coverage describes the checked step AST, the chunk
Words the step folds, the payload lengths and the lengths of reverted payloads,
and the completions. Source/Rust/EVM agreement is a separate external
validation. -/
set_option autoImplicit false

namespace Tests.SourceDynamicBytesCorpus
open Lean Solcore.Core Solcore.Synthesis.Core Solcore.Synthesis.Source

private def require (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

private def string (value : Json) (key : String) : Except String String :=
  value.getObjValAs? String key

private def strings (value : Json) (key : String) : Except String (List String) := do
  let values ← value.getObjValAs? (List String) key
  require (values.eraseDups == values) (key ++ " contains duplicates")
  return values

private def naturals (value : Json) (key : String) : Except String (List Nat) := do
  let values ← value.getObjValAs? (List Nat) key
  require (values.eraseDups == values) (key ++ " contains duplicates")
  return values

private def sameMembers {α : Type} [BEq α] (left right : List α) : Bool :=
  left.all right.contains && right.all left.contains

private def versions : List (String × String) := [
  ("generatorVersion", generatorVersion), ("profileVersion", DynamicBytes.profileVersion),
  ("functionVersion", Solcore.Synthesis.Core.DynamicBytes.version),
  ("templateVersion", DynamicBytes.templateVersion), ("stepProfileVersion", Aggregate.profileVersion),
  ("stepFunctionVersion", Aggregates.version), ("stepTemplateVersion", Aggregate.templateVersion),
  ("emitterVersion", DynamicBytes.emitterVersion), ("wrapperVersion", DynamicBytes.wrapperVersion)]

private def words (values : List Word) : List String := values.map fun value => toString value.val

/-- The zero-padded 32-byte chunk Words of a payload, written independently of
the Core contract and the emitter. -/
private def chunks (payload : List UInt8) : List String :=
  (List.range ((payload.length + 31) / 32)).map fun index =>
    let bytes := (payload.drop (32 * index)).take 32
    toString ((bytes.map UInt8.toNat ++ List.replicate (32 - bytes.length) 0).foldl (fun total byte => total * 256 + byte) 0)

/-- Imported entries are emitted from their saved plan and sequence; generated
entries are regenerated from their seed. Both are checked by full replay. -/
private def entryCase (entry : Json) (fuel : Nat) : Except String Json := do
  if let .ok request := entry.getObjVal? "generation" then
    let some seed := (← request.getObjValAs? String "seed").toNat? | throw "invalid generation seed"
    let corpus := DynamicBytes.generateCases (Seed.ofNat seed) (← request.getObjValAs? Nat "maxProgramNodes") 1 1 fuel
    require ((← string corpus "status") == "complete") "generated entry was excluded"
    let some saved := (← corpus.getObjValAs? (Array Json) "cases")[0]? | throw "generated entry has no case"
    return saved
  let plan ← DynamicBytes.checkedPlan (← entry.getObjVal? "bytesPlan")
  let scenario ← DynamicBytes.checkedScenario plan (← DynamicBytes.decodeTransactions (← entry.getObjVal? "transactions"))
  DynamicBytes.emitCase scenario (Json.mkObj [("kind", toJson "imported")]) fuel

private def templates (saved : Json) : Except String (List Nat) := do
  let origin ← (← saved.getObjVal? "provenance").getObjVal? "origin"
  if (← string origin "kind") != "bytes-generated" then return []
  let helpers ← (← origin.getObjVal? "stepOrigin").getObjValAs? (List Json) "helpers"
  helpers.mapM fun helper => helper.getObjValAs? Nat "template"

def validateManifest (manifest : Json) (fuel : Nat := 1000000) : Except String Json := do
  require ((← string manifest "schema") == "solcore-lean.semantic-storage-corpus-manifest.v1" &&
    (← string manifest "profile") == "stateful-bytes" &&
    (← string manifest "coverageKind") == "step-core-ast-features") "unexpected bytes manifest scope"
  for (key, expected) in versions do
    require ((← string manifest key) == expected) ("bytes manifest changed " ++ key)
  let requiredFeatures ← strings manifest "requiredFeatures"
  let requiredInputs ← strings manifest "requiredInputs"
  require (sameMembers requiredInputs (words Storage.boundaryInputs))
    "bytes corpus must require all six boundary Words as chunks"
  require (sameMembers (← naturals manifest "requiredPayloadLengths") DynamicBytes.lengthBank)
    "bytes corpus must require the whole length bank"
  let requiredReverted ← naturals manifest "requiredRevertedPayloadLengths"
  require (requiredReverted.all DynamicBytes.lengthBank.contains && requiredReverted.contains 0 &&
      requiredReverted.any (fun length => 0 < length && length ≤ 32) && requiredReverted.any (· > 32))
    "bytes corpus must require reverted empty, one-chunk and two-chunk payloads from the bank"
  require ((← manifest.getObjValAs? (List Nat) "requiredHelperCounts") == [1, 2, 3] &&
    (← manifest.getObjValAs? (List Nat) "requiredTransactionCounts") == [1, 2, 3])
    "bytes corpus must require one to three helpers and transactions"
  require ((← (← manifest.getObjVal? "generationRecipeRequirements").getObjValAs? (List Nat) "templates") == [0, 1, 2, 3])
    "bytes corpus must require all four step templates"
  require ((← strings manifest "requiredOutcomes") == ["returned", "reverted"]) "bytes corpus must require both outcomes"
  let requiredPatterns ← strings manifest "requiredCompletionPatterns"
  require (!requiredPatterns.isEmpty) "bytes corpus must require completion patterns"
  let entries ← manifest.getObjValAs? (Array Json) "cases"
  require (0 < entries.size && entries.size ≤ 64) "bytes corpus must contain 1..64 scenarios"
  let mut identifiers : List String := []
  let mut features : List String := []
  let mut inputs : List String := []
  let mut lengths : List Nat := []
  let mut reverted : List Nat := []
  let mut helperCounts : List Nat := []
  let mut transactionCounts : List Nat := []
  let mut templateUnion : List Nat := []
  let mut outcomes : List String := []
  let mut patterns : List String := []
  let mut transactionTotal := 0
  for entry in entries do
    let identifier ← string entry "id"
    require (!identifiers.contains identifier) ("duplicate bytes corpus id " ++ identifier)
    identifiers := identifier :: identifiers
    let saved ← entryCase entry fuel
    require ((← DynamicBytes.replayCase saved fuel) == saved) ("bytes corpus entry did not replay: " ++ identifier)
    let scenario ← DynamicBytes.caseProgram saved
    if !(entry.getObjVal? "generation").isOk then
      require ((← saved.getObjVal? "bytesPlan") == (← entry.getObjVal? "bytesPlan") &&
        (← saved.getObjVal? "transactions") == (← entry.getObjVal? "transactions"))
        ("imported bytes entry is not canonical: " ++ identifier)
    let caseFeatures := (← (← saved.getObjVal? "provenance").getObjValAs? (List String) "features").eraseDups
    require (sameMembers (← strings entry "expectedFeatures") caseFeatures)
      ("bytes corpus features changed: " ++ identifier)
    let history := DynamicBytes.observe scenario Solcore.Synthesis.Stateful.StorageExecution.fixtureBindings fuel
    let statuses ← DynamicBytes.checkProtocol scenario history
    let observed ← history.getObjValAs? (List Json) "transactions"
    let expected ← entry.getObjValAs? (List Json) "expectedHistory"
    require (observed.length == expected.length) ("bytes expected history length changed: " ++ identifier)
    for ((row, golden), tx) in (observed.zip expected).zip scenario.transactions do
      let actual := Json.mkObj [("id", ← row.getObjVal? "id"), ("status", ← row.getObjVal? "status"),
        ("output", ← row.getObjVal? "output"), ("committedStorage", ← row.getObjVal? "committedStorage")]
      require (actual == golden) ("original Core differs from the independent history: " ++ identifier ++ " " ++ actual.compress)
      inputs := (inputs ++ chunks tx.payload).eraseDups
      lengths := (lengths ++ [tx.payload.length]).eraseDups
      if (← string row "status") == "reverted" then
        reverted := (reverted ++ [tx.payload.length]).eraseDups
    transactionTotal := transactionTotal + observed.length
    features := (features ++ caseFeatures).eraseDups
    helperCounts := (helperCounts ++ [scenario.plan.step.helpers.length]).eraseDups
    transactionCounts := (transactionCounts ++ [scenario.transactions.length]).eraseDups
    templateUnion := (templateUnion ++ (← templates saved)).eraseDups
    outcomes := (outcomes ++ statuses).eraseDups
    patterns := (patterns ++ [String.intercalate "," statuses]).eraseDups
  require (requiredFeatures.all features.contains) "bytes corpus misses a required step feature"
  require (requiredInputs.all inputs.contains) "bytes corpus misses a boundary chunk Word"
  require (DynamicBytes.lengthBank.all lengths.contains && requiredReverted.all reverted.contains)
    "bytes corpus misses a payload length or a reverted payload length"
  require ([1, 2, 3].all helperCounts.contains && [1, 2, 3].all transactionCounts.contains)
    "bytes corpus misses a helper or transaction count"
  require ([0, 1, 2, 3].all templateUnion.contains) "bytes corpus misses a generated template"
  require (["returned", "reverted"].all outcomes.contains && requiredPatterns.all patterns.contains)
    "bytes corpus misses an observed outcome or completion pattern"
  return Json.mkObj [("profile", toJson "stateful-bytes"), ("scenarios", toJson entries.size),
    ("transactions", toJson transactionTotal), ("lengths", toJson lengths), ("reverted", toJson reverted),
    ("patterns", toJson patterns)]

private def checked {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def rejects {α : Type} (result : Except String α) (message : String) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError ("invalid bytes corpus unexpectedly passed: " ++ message))

def testSourceDynamicBytesCorpus : IO Unit := do
  let manifest ← checked (Json.parse (← IO.FS.readFile "scripts/semantic-bytes-corpus.json"))
  let summary ← checked (validateManifest manifest)
  let entries ← checked (manifest.getObjValAs? (Array Json) "cases")
  let some first := entries[0]? | throw (IO.userError "missing first bytes case")
  let some generatedEntry := entries.find? (fun entry => (entry.getObjVal? "generation").isOk) |
    throw (IO.userError "missing generated bytes case")
  let replace := fun (original changed : Json) => manifest.setObjVal! "cases"
    (.arr (entries.map fun entry => if entry == original then changed else entry))
  let history ← checked (first.getObjValAs? (Array Json) "expectedHistory")
  let withRow := fun (index : Nat) (row : Json) =>
    replace first (first.setObjVal! "expectedHistory" (.arr (history.set! index row)))
  let row := history[0]!
  rejects (validateManifest (withRow 0 (row.setObjVal! "output" (toJson ("0x" ++ String.ofList (List.replicate 64 'f'))))))
    "changed output"
  let storage ← checked (row.getObjValAs? (Array Json) "committedStorage")
  rejects (validateManifest (withRow 0 (row.setObjVal! "committedStorage" (.arr (storage.set! 3 (storage[3]!.setObjVal! "value" (toJson "33")))))))
    "changed byte count"
  rejects (validateManifest (withRow 0 (row.setObjVal! "committedStorage" (.arr (storage.set! 4 (storage[4]!.setObjVal! "value" (toJson "2")))))))
    "changed last byte"
  -- The first scenario's second transaction reverts: committing its writes is wrong.
  let reverted := history[1]!
  let revertedStorage ← checked (reverted.getObjValAs? (Array Json) "committedStorage")
  rejects (validateManifest (withRow 1 (reverted.setObjVal! "committedStorage"
    (.arr (revertedStorage.set! 3 (revertedStorage[3]!.setObjVal! "value" (toJson "49"))))))) "a reverted length committed"
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr history.pop)))) "popped history"
  let generatedHistory ← checked (generatedEntry.getObjValAs? (Array Json) "expectedHistory")
  let generatedStatus ← checked (generatedHistory[0]!.getObjValAs? String "status")
  rejects (validateManifest (replace generatedEntry (generatedEntry.setObjVal! "expectedHistory"
    (.arr (generatedHistory.set! 0 (generatedHistory[0]!.setObjVal! "status"
      (toJson (if generatedStatus == "returned" then "reverted" else "returned")))))))) "flipped status"
  -- A consistently re-encoded payload with one changed byte no longer matches its history.
  let transactions ← checked (DynamicBytes.decodeTransactions (← checked (first.getObjVal? "transactions")))
  let some tx := transactions[0]? | throw (IO.userError "missing first bytes transaction")
  let changed := {tx with payload := tx.payload.set 0 (tx.payload.getD 0 0 + 1)}
  rejects (validateManifest (replace first (first.setObjVal! "transactions"
    (DynamicBytes.transactionsJson (changed :: transactions.drop 1))))) "changed payload byte"
  let longer := {tx with payload := tx.payload ++ [0]}
  rejects (validateManifest (replace first (first.setObjVal! "transactions"
    (DynamicBytes.transactionsJson (longer :: transactions.drop 1))))) "appended zero byte"
  rejects (validateManifest (replace first (first.setObjVal! "expectedFeatures" (toJson ([] : List String))))) "features"
  rejects (validateManifest (replace generatedEntry (generatedEntry.setObjVal! "generation"
    (Json.mkObj [("seed", toJson "13"), ("maxProgramNodes", toJson (384 : Nat))])))) "changed seed"
  rejects (validateManifest (manifest.setObjVal! "cases" (.arr (entries.push first)))) "duplicate entry"
  for (key, value) in [
      ("profile", toJson "stateful-dynamic-array"), ("wrapperVersion", toJson "forged"),
      ("cases", .arr #[]), ("requiredInputs", toJson ([] : List String)), ("requiredHelperCounts", toJson [1, 2]),
      ("requiredPayloadLengths", toJson ([0, 1] : List Nat)),
      ("requiredPayloadLengths", toJson ([0, 1, 17, 31, 32, 33, 48, 63, 64, 65] : List Nat)),
      ("requiredRevertedPayloadLengths", toJson ([17, 33] : List Nat)),
      ("requiredRevertedPayloadLengths", toJson ([0, 17, 33, 5] : List Nat)),
      ("requiredRevertedPayloadLengths", toJson ([0, 48, 64] : List Nat)),
      ("requiredCompletionPatterns", toJson (["reverted,reverted,reverted"] : List String))] do
    rejects (validateManifest (manifest.setObjVal! key value)) key
  rejects (validateManifest manifest 0) "zero fuel"
  IO.println summary.compress

end Tests.SourceDynamicBytesCorpus
