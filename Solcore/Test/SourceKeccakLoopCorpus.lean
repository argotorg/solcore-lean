import Solcore.Synthesis.Source.KeccakLoopCases

/-! The fixed Keccak-loop corpus checks actual original Core histories against
expectations computed without the guarded contract: the source-loop model, a
counter over a slot map with Keccak slots and a log list, in which each step
runs alone in Core. The expectations cover status, output, slot zero, every
addressed entry slot and every committed log's emitter, topics and data.
Coverage describes the checked steps' AST, the inputs, the loop and key masks,
the iteration counts, the carries within a transaction, across committed
transactions and through a rollback, and the completions. Source/Rust/EVM
agreement is a separate external validation. -/
set_option autoImplicit false

namespace Tests.SourceKeccakLoopCorpus
open Lean Solcore.Core Solcore.Synthesis.Core Solcore.Synthesis.Source

private def require (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

private def string (value : Json) (key : String) : Except String String :=
  value.getObjValAs? String key

private def strings (value : Json) (key : String) : Except String (List String) := do
  let values ← value.getObjValAs? (List String) key
  require (values.eraseDups == values) (key ++ " contains duplicates")
  return values

private def sameMembers {α : Type} [BEq α] (left right : List α) : Bool :=
  left.all right.contains && right.all left.contains

private def versions : List (String × String) := [
  ("generatorVersion", generatorVersion), ("profileVersion", KeccakLoop.profileVersion),
  ("functionVersion", Solcore.Synthesis.Core.KeccakLoop.version),
  ("framingVersion", Solcore.Synthesis.Core.EventLog.framingVersion),
  ("templateVersion", KeccakLoop.templateVersion), ("stepProfileVersion", Aggregate.profileVersion),
  ("stepFunctionVersion", Aggregates.version), ("stepTemplateVersion", Aggregate.templateVersion),
  ("emitterVersion", KeccakLoop.emitterVersion), ("wrapperVersion", KeccakLoop.wrapperVersion)]

private def words (values : List Word) : List String := values.map fun value => toString value.val

/-- Imported entries are emitted from their saved plan and sequence; generated
entries are regenerated from their seed. Both are checked by full replay. -/
private def entryCase (entry : Json) (fuel : Nat) : Except String Json := do
  if let .ok request := entry.getObjVal? "generation" then
    let some seed := (← request.getObjValAs? String "seed").toNat? | throw "invalid generation seed"
    let corpus := KeccakLoop.generateCases (Seed.ofNat seed) (← request.getObjValAs? Nat "maxProgramNodes") 1 1 fuel
    require ((← string corpus "status") == "complete") "generated entry was excluded"
    let some saved := (← corpus.getObjValAs? (Array Json) "cases")[0]? | throw "generated entry has no case"
    return saved
  let plan ← KeccakLoop.checkedPlan (← entry.getObjVal? "keccakLoopPlan")
  let scenario ← KeccakLoop.checkedScenario plan
    (← KeccakLoop.decodeTransactions plan.mask (← entry.getObjVal? "transactions"))
  KeccakLoop.emitCase scenario (Json.mkObj [("kind", toJson "imported")]) fuel

private def templates (saved : Json) : Except String (List Nat) := do
  let origin ← (← saved.getObjVal? "provenance").getObjVal? "origin"
  if (← string origin "kind") != "keccak-loop-generated" then return []
  let helpers ← (← origin.getObjVal? "stepOrigin").getObjValAs? (List Json) "helpers"
  helpers.mapM fun helper => helper.getObjValAs? Nat "template"

private def naturals (manifest : Json) (key : String) : Except String (List Nat) :=
  manifest.getObjValAs? (List Nat) key

/-- The carries of one scenario: `iteration` when an iteration reads the slot
zero the previous one wrote, `entry` when two iterations of a transaction
address one entry, `transaction` when an iteration reads an entry an earlier
committed transaction wrote, and `rollback` when a revert follows logged
iterations. -/
private def carries (keys : List (List Word)) (statuses : List String) : List String :=
  let trips := keys.map List.length
  (if trips.any (· ≥ 2) then ["iteration"] else []) ++
  (if keys.any (fun values => values.eraseDups.length < values.length) then ["entry"] else []) ++
  (if keys.zipIdx.any (fun (values, index) => values.any fun key =>
      ((keys.zip statuses).take index).any fun (earlier, status) => status == "returned" && earlier.contains key)
    then ["transaction"] else []) ++
  (if (trips.zip statuses).any (fun (count, status) => count ≥ 1 && status == "reverted") then ["rollback"] else [])

def validateManifest (manifest : Json) (fuel : Nat := 1000000) : Except String Json := do
  require ((← string manifest "schema") == "solcore-lean.semantic-storage-corpus-manifest.v1" &&
    (← string manifest "profile") == "stateful-keccak-loops" &&
    (← string manifest "coverageKind") == "step-core-ast-features") "unexpected Keccak-loop manifest scope"
  for (key, expected) in versions do
    require ((← string manifest key) == expected) ("Keccak-loop manifest changed " ++ key)
  let requiredFeatures ← strings manifest "requiredFeatures"
  let requiredInputs ← strings manifest "requiredInputs"
  require (sameMembers requiredInputs (words KeccakLoop.boundaryInputs))
    "Keccak-loop corpus must require all six boundary inputs"
  require ((← naturals manifest "requiredMasks") == [0, 1, 3, 7] &&
    (← naturals manifest "requiredKeyMasks") == [0, 1, 3, 7] &&
    (← naturals manifest "requiredIterationCounts") == List.range 8)
    "Keccak-loop corpus must require every loop mask, key mask and iteration count"
  require ((← strings manifest "requiredIterationCarries") == ["entry", "iteration", "rollback", "transaction"])
    "Keccak-loop corpus must require carries within a transaction, across transactions and through a rollback"
  require ((← naturals manifest "requiredHelperCounts") == [1, 2, 3] &&
    (← naturals manifest "requiredTransactionCounts") == [1, 2, 3])
    "Keccak-loop corpus must require one to three helpers and transactions"
  require ((← (← manifest.getObjVal? "generationRecipeRequirements").getObjValAs? (List Nat) "templates") == [0, 1, 2, 3])
    "Keccak-loop corpus must require all four step templates"
  require ((← strings manifest "requiredOutcomes") == ["returned", "reverted"])
    "Keccak-loop corpus must require both outcomes"
  let requiredPatterns ← strings manifest "requiredCompletionPatterns"
  require (!requiredPatterns.isEmpty) "Keccak-loop corpus must require completion patterns"
  let entries ← manifest.getObjValAs? (Array Json) "cases"
  require (0 < entries.size && entries.size ≤ 64) "Keccak-loop corpus must contain 1..64 scenarios"
  let mut identifiers : List String := []
  let mut features : List String := []
  let mut inputs : List String := []
  let mut masks : List Nat := []
  let mut keyMasks : List Nat := []
  let mut counts : List Nat := []
  let mut carried : List String := []
  let mut helperCounts : List Nat := []
  let mut transactionCounts : List Nat := []
  let mut templateUnion : List Nat := []
  let mut outcomes : List String := []
  let mut patterns : List String := []
  let mut transactionTotal := 0
  let mut logTotal := 0
  for entry in entries do
    let identifier ← string entry "id"
    require (!identifiers.contains identifier) ("duplicate Keccak-loop corpus id " ++ identifier)
    identifiers := identifier :: identifiers
    let saved ← entryCase entry fuel
    require ((← KeccakLoop.replayCase saved fuel) == saved) ("Keccak-loop corpus entry did not replay: " ++ identifier)
    let scenario ← KeccakLoop.caseProgram saved
    if !(entry.getObjVal? "generation").isOk then
      require ((← saved.getObjVal? "keccakLoopPlan") == (← entry.getObjVal? "keccakLoopPlan") &&
        (← saved.getObjVal? "transactions") == (← entry.getObjVal? "transactions"))
        ("imported Keccak-loop entry is not canonical: " ++ identifier)
    let caseFeatures := (← (← saved.getObjVal? "provenance").getObjValAs? (List String) "features").eraseDups
    require (sameMembers (← strings entry "expectedFeatures") caseFeatures)
      ("Keccak-loop corpus features changed: " ++ identifier)
    let history := KeccakLoop.observe scenario Solcore.Synthesis.Stateful.StorageExecution.fixtureBindings fuel
    require ((← string history "status") == "complete") ("Keccak-loop corpus history incomplete: " ++ identifier)
    let observed ← history.getObjValAs? (List Json) "transactions"
    let expected ← entry.getObjValAs? (List Json) "expectedHistory"
    require (observed.length == expected.length) ("Keccak-loop expected history length changed: " ++ identifier)
    let mut statuses : List String := []
    for (row, golden) in observed.zip expected do
      let actual := Json.mkObj [("id", ← row.getObjVal? "id"), ("status", ← row.getObjVal? "status"),
        ("output", ← row.getObjVal? "output"), ("committedStorage", ← row.getObjVal? "committedStorage"),
        ("logs", ← row.getObjVal? "logs")]
      require (actual == golden)
        ("original Core differs from the source-loop model: " ++ identifier ++ " " ++ actual.compress)
      statuses := statuses ++ [← string row "status"]
      logTotal := logTotal + (← row.getObjValAs? (List Json) "logs").length
    let mask := scenario.plan.mask
    let keys := scenario.transactions.map fun tx =>
      Solcore.Synthesis.Stateful.KeccakLoopExecution.keys mask scenario.plan.keyMask tx.input
    transactionTotal := transactionTotal + observed.length
    features := (features ++ caseFeatures).eraseDups
    inputs := (inputs ++ words (scenario.transactions.map (·.input))).eraseDups
    masks := (masks ++ [mask]).eraseDups
    keyMasks := (keyMasks ++ [scenario.plan.keyMask]).eraseDups
    counts := (counts ++ keys.map List.length).eraseDups
    carried := (carried ++ carries keys statuses).eraseDups
    helperCounts := (helperCounts ++ [scenario.plan.step.helpers.length]).eraseDups
    transactionCounts := (transactionCounts ++ [scenario.transactions.length]).eraseDups
    templateUnion := (templateUnion ++ (← templates saved)).eraseDups
    outcomes := (outcomes ++ statuses).eraseDups
    patterns := (patterns ++ [String.intercalate "," statuses]).eraseDups
  require (requiredFeatures.all features.contains) "Keccak-loop corpus misses a required step feature"
  require (requiredInputs.all inputs.contains) "Keccak-loop corpus misses a boundary input"
  require ([0, 1, 3, 7].all masks.contains && [0, 1, 3, 7].all keyMasks.contains && (List.range 8).all counts.contains)
    "Keccak-loop corpus misses a loop mask, a key mask or an iteration count"
  require (["entry", "iteration", "rollback", "transaction"].all carried.contains) "Keccak-loop corpus misses a carry"
  require ([1, 2, 3].all helperCounts.contains && [1, 2, 3].all transactionCounts.contains)
    "Keccak-loop corpus misses a helper or transaction count"
  require ([0, 1, 2, 3].all templateUnion.contains) "Keccak-loop corpus misses a generated template"
  require (["returned", "reverted"].all outcomes.contains && requiredPatterns.all patterns.contains)
    "Keccak-loop corpus misses an observed outcome or completion pattern"
  return Json.mkObj [("profile", toJson "stateful-keccak-loops"), ("scenarios", toJson entries.size),
    ("transactions", toJson transactionTotal), ("logs", toJson logTotal), ("masks", toJson masks),
    ("keyMasks", toJson keyMasks), ("iterationCounts", toJson counts), ("carries", toJson carried),
    ("patterns", toJson patterns)]

private def checked {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def rejects {α : Type} (result : Except String α) (reason : String) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError ("invalid Keccak-loop corpus unexpectedly passed: " ++ reason))

def testSourceKeccakLoopCorpus : IO Unit := do
  let manifest ← checked (Json.parse (← IO.FS.readFile "scripts/semantic-keccak-loop-corpus.json"))
  let summary ← checked (validateManifest manifest)
  let entries ← checked (manifest.getObjValAs? (Array Json) "cases")
  let some first := entries[0]? | throw (IO.userError "missing first Keccak-loop case")
  let some generatedEntry := entries.find? (fun entry => (entry.getObjVal? "generation").isOk) |
    throw (IO.userError "missing generated Keccak-loop case")
  let replace := fun (original changed : Json) => manifest.setObjVal! "cases"
    (.arr (entries.map fun entry => if entry == original then changed else entry))
  let history ← checked (first.getObjValAs? (Array Json) "expectedHistory")
  let row := history[0]!
  let withRow := fun (changed : Json) => replace first (first.setObjVal! "expectedHistory" (.arr (history.set! 0 changed)))
  -- An output, a slot, a log, a missing row and a status are all checked.
  rejects (validateManifest (withRow (row.setObjVal! "output" (toJson ("0x" ++ String.ofList (List.replicate 64 'f'))))))
    "changed output"
  let storage ← checked (row.getObjValAs? (Array Json) "committedStorage")
  let last := storage.size - 1
  rejects (validateManifest (withRow (row.setObjVal! "committedStorage"
    (.arr (storage.set! last (storage[last]!.setObjVal! "value" (toJson "7"))))))) "changed entry"
  rejects (validateManifest (withRow (row.setObjVal! "committedStorage" (.arr storage.pop)))) "dropped slot"
  let logs ← checked (row.getObjValAs? (Array Json) "logs")
  let some log := logs[0]? | throw (IO.userError "the first Keccak-loop history row commits no log")
  let topics ← checked (log.getObjValAs? (Array String) "topics")
  for (changed, reason) in [
      (logs.set! 0 (log.setObjVal! "topics" (toJson (topics.set! 1 "1"))), "changed key topic"),
      (logs.set! 0 (log.setObjVal! "topics" (toJson topics.reverse)), "reordered topics"),
      (logs.set! 0 (log.setObjVal! "data" (toJson "0x")), "removed data"),
      (logs.pop, "removed log"), (logs.push log, "duplicated log")] do
    rejects (validateManifest (withRow (row.setObjVal! "logs" (.arr changed)))) reason
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr history.pop)))) "popped history"
  let generatedHistory ← checked (generatedEntry.getObjValAs? (Array Json) "expectedHistory")
  let flipped := if (generatedHistory[0]!.getObjValAs? String "status").toOption == some "returned" then "reverted" else "returned"
  rejects (validateManifest (replace generatedEntry (generatedEntry.setObjVal! "expectedHistory"
    (.arr (generatedHistory.set! 0 (generatedHistory[0]!.setObjVal! "status" (toJson flipped))))))) "flipped status"
  -- A recorded iteration count, the loop mask and the key mask are all checked.
  let transactions ← checked (first.getObjValAs? (Array Json) "transactions")
  rejects (validateManifest (replace first (first.setObjVal! "transactions"
    (.arr (transactions.set! 0 (transactions[0]!.setObjVal! "iterations" (toJson 0))))))) "changed iterations"
  let plan ← checked (first.getObjVal? "keccakLoopPlan")
  rejects (validateManifest (replace first (first.setObjVal! "keccakLoopPlan" (plan.setObjVal! "mask" (toJson 3)))))
    "changed loop mask"
  let keyMask ← checked (plan.getObjValAs? Nat "keyMask")
  rejects (validateManifest (replace first (first.setObjVal! "keccakLoopPlan"
    (plan.setObjVal! "keyMask" (toJson (if keyMask == 7 then 3 else 7)))))) "changed key mask"
  rejects (validateManifest (replace first (first.setObjVal! "expectedFeatures" (toJson ([] : List String)))))
    "removed features"
  rejects (validateManifest (manifest.setObjVal! "cases" (.arr (entries.push first)))) "duplicated entry"
  for (key, value) in [
      ("profile", toJson "stateful-storage-loops"), ("templateVersion", toJson "forged"),
      ("framingVersion", toJson "forged"), ("cases", .arr #[]), ("requiredInputs", toJson ([] : List String)),
      ("requiredMasks", toJson [1, 3, 7]), ("requiredKeyMasks", toJson [0, 7]),
      ("requiredIterationCounts", toJson [0, 1, 7]),
      ("requiredIterationCarries", toJson (["iteration", "rollback"] : List String)),
      ("requiredHelperCounts", toJson [1, 2]),
      ("requiredCompletionPatterns", toJson (["returned,returned,returned,returned"] : List String))] do
    rejects (validateManifest (manifest.setObjVal! key value)) key
  rejects (validateManifest manifest 0) "no fuel"
  IO.println summary.compress

end Tests.SourceKeccakLoopCorpus
