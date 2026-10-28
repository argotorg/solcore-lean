import Solcore.Synthesis.Source.StorageLoopCases

/-! The fixed storage-loop corpus checks actual original Core histories against
expectations computed without the guarded contract: the source-loop model, a
counter over a slot map in which each step runs alone in Core. Coverage
describes the checked steps' AST, the inputs, the masks, the iteration counts,
the carries within a transaction and through a rollback, the iteration slots
carried across transactions and the completions. Source/Rust/EVM agreement is
a separate external validation. -/
set_option autoImplicit false

namespace Tests.SourceStorageLoopCorpus
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
  ("generatorVersion", generatorVersion), ("profileVersion", StorageLoop.profileVersion),
  ("functionVersion", Solcore.Synthesis.Core.StorageLoop.version),
  ("templateVersion", StorageLoop.templateVersion), ("stepProfileVersion", Aggregate.profileVersion),
  ("stepFunctionVersion", Aggregates.version), ("stepTemplateVersion", Aggregate.templateVersion),
  ("emitterVersion", StorageLoop.emitterVersion), ("wrapperVersion", StorageLoop.wrapperVersion)]

private def words (values : List Word) : List String := values.map fun value => toString value.val

/-- Imported entries are emitted from their saved plan and sequence; generated
entries are regenerated from their seed. Both are checked by full replay. -/
private def entryCase (entry : Json) (fuel : Nat) : Except String Json := do
  if let .ok request := entry.getObjVal? "generation" then
    let some seed := (← request.getObjValAs? String "seed").toNat? | throw "invalid generation seed"
    let corpus := StorageLoop.generateCases (Seed.ofNat seed) (← request.getObjValAs? Nat "maxProgramNodes") 1 1 fuel
    require ((← string corpus "status") == "complete") "generated entry was excluded"
    let some saved := (← corpus.getObjValAs? (Array Json) "cases")[0]? | throw "generated entry has no case"
    return saved
  let plan ← StorageLoop.checkedPlan (← entry.getObjVal? "storageLoopPlan")
  let scenario ← StorageLoop.checkedScenario plan
    (← StorageLoop.decodeTransactions plan.mask (← entry.getObjVal? "transactions"))
  StorageLoop.emitCase scenario (Json.mkObj [("kind", toJson "imported")]) fuel

private def templates (saved : Json) : Except String (List Nat) := do
  let origin ← (← saved.getObjVal? "provenance").getObjVal? "origin"
  if (← string origin "kind") != "storage-loop-generated" then return []
  let helpers ← (← origin.getObjVal? "stepOrigin").getObjValAs? (List Json) "helpers"
  helpers.mapM fun helper => helper.getObjValAs? Nat "template"

def validateManifest (manifest : Json) (fuel : Nat := 1000000) : Except String Json := do
  require ((← string manifest "schema") == "solcore-lean.semantic-storage-corpus-manifest.v1" &&
    (← string manifest "profile") == "stateful-storage-loops" &&
    (← string manifest "coverageKind") == "step-core-ast-features") "unexpected storage-loop manifest scope"
  for (key, expected) in versions do
    require ((← string manifest key) == expected) ("storage-loop manifest changed " ++ key)
  let requiredFeatures ← strings manifest "requiredFeatures"
  let requiredInputs ← strings manifest "requiredInputs"
  require (sameMembers requiredInputs (words StorageLoop.boundaryInputs))
    "storage-loop corpus must require all six boundary inputs"
  require ((← manifest.getObjValAs? (List Nat) "requiredMasks") == [0, 1, 3, 7] &&
    (← manifest.getObjValAs? (List Nat) "requiredIterationCounts") == List.range 8 &&
    (← manifest.getObjValAs? (List Nat) "requiredCarriedSlots") == (List.range 7).map (· + 2))
    "storage-loop corpus must require every mask, iteration count and carried slot"
  require ((← strings manifest "requiredIterationCarries") == ["iteration", "rollback"])
    "storage-loop corpus must require carries within a transaction and through a rollback"
  require ((← manifest.getObjValAs? (List Nat) "requiredHelperCounts") == [1, 2, 3] &&
    (← manifest.getObjValAs? (List Nat) "requiredTransactionCounts") == [1, 2, 3])
    "storage-loop corpus must require one to three helpers and transactions"
  require ((← (← manifest.getObjVal? "generationRecipeRequirements").getObjValAs? (List Nat) "templates") == [0, 1, 2, 3])
    "storage-loop corpus must require all four step templates"
  require ((← strings manifest "requiredOutcomes") == ["returned", "reverted"])
    "storage-loop corpus must require both outcomes"
  let requiredPatterns ← strings manifest "requiredCompletionPatterns"
  require (!requiredPatterns.isEmpty) "storage-loop corpus must require completion patterns"
  let entries ← manifest.getObjValAs? (Array Json) "cases"
  require (0 < entries.size && entries.size ≤ 64) "storage-loop corpus must contain 1..64 scenarios"
  let mut identifiers : List String := []
  let mut features : List String := []
  let mut inputs : List String := []
  let mut masks : List Nat := []
  let mut counts : List Nat := []
  let mut carries : List String := []
  let mut carried : List Nat := []
  let mut helperCounts : List Nat := []
  let mut transactionCounts : List Nat := []
  let mut templateUnion : List Nat := []
  let mut outcomes : List String := []
  let mut patterns : List String := []
  let mut transactionTotal := 0
  for entry in entries do
    let identifier ← string entry "id"
    require (!identifiers.contains identifier) ("duplicate storage-loop corpus id " ++ identifier)
    identifiers := identifier :: identifiers
    let saved ← entryCase entry fuel
    require ((← StorageLoop.replayCase saved fuel) == saved) ("storage-loop corpus entry did not replay: " ++ identifier)
    let scenario ← StorageLoop.caseProgram saved
    if !(entry.getObjVal? "generation").isOk then
      require ((← saved.getObjVal? "storageLoopPlan") == (← entry.getObjVal? "storageLoopPlan") &&
        (← saved.getObjVal? "transactions") == (← entry.getObjVal? "transactions"))
        ("imported storage-loop entry is not canonical: " ++ identifier)
    let caseFeatures := (← (← saved.getObjVal? "provenance").getObjValAs? (List String) "features").eraseDups
    require (sameMembers (← strings entry "expectedFeatures") caseFeatures)
      ("storage-loop corpus features changed: " ++ identifier)
    let history := StorageLoop.observe scenario Solcore.Synthesis.Stateful.StorageExecution.fixtureBindings fuel
    require ((← string history "status") == "complete") ("storage-loop corpus history incomplete: " ++ identifier)
    let observed ← history.getObjValAs? (List Json) "transactions"
    let expected ← entry.getObjValAs? (List Json) "expectedHistory"
    require (observed.length == expected.length) ("storage-loop expected history length changed: " ++ identifier)
    let mut statuses : List String := []
    for (row, golden) in observed.zip expected do
      let actual := Json.mkObj [("id", ← row.getObjVal? "id"), ("status", ← row.getObjVal? "status"),
        ("output", ← row.getObjVal? "output"), ("committedStorage", ← row.getObjVal? "committedStorage")]
      require (actual == golden)
        ("original Core differs from the source-loop model: " ++ identifier ++ " " ++ actual.compress)
      statuses := statuses ++ [← string row "status"]
    let mask := scenario.plan.mask
    let trips := scenario.transactions.map fun tx => Solcore.Synthesis.Stateful.StorageLoopExecution.iterations mask tx.input
    transactionTotal := transactionTotal + observed.length
    features := (features ++ caseFeatures).eraseDups
    inputs := (inputs ++ words (scenario.transactions.map (·.input))).eraseDups
    masks := (masks ++ [mask]).eraseDups
    counts := (counts ++ trips).eraseDups
    if trips.any (· ≥ 2) then carries := (carries ++ ["iteration"]).eraseDups
    if (trips.zip statuses).any (fun (count, status) => count ≥ 1 && status == "reverted") then
      carries := (carries ++ ["rollback"]).eraseDups
    for (count, index) in trips.zipIdx do
      for iteration in List.range count do
        if ((trips.zip statuses).take index).any (fun (earlier, status) => status == "returned" && earlier > iteration) then
          carried := (carried ++ [2 + iteration]).eraseDups
    helperCounts := (helperCounts ++ [scenario.plan.step.helpers.length]).eraseDups
    transactionCounts := (transactionCounts ++ [scenario.transactions.length]).eraseDups
    templateUnion := (templateUnion ++ (← templates saved)).eraseDups
    outcomes := (outcomes ++ statuses).eraseDups
    patterns := (patterns ++ [String.intercalate "," statuses]).eraseDups
  require (requiredFeatures.all features.contains) "storage-loop corpus misses a required step feature"
  require (requiredInputs.all inputs.contains) "storage-loop corpus misses a boundary input"
  require ([0, 1, 3, 7].all masks.contains && (List.range 8).all counts.contains)
    "storage-loop corpus misses a mask or an iteration count"
  require (["iteration", "rollback"].all carries.contains && ((List.range 7).map (· + 2)).all carried.contains)
    "storage-loop corpus misses a carry or a carried slot"
  require ([1, 2, 3].all helperCounts.contains && [1, 2, 3].all transactionCounts.contains)
    "storage-loop corpus misses a helper or transaction count"
  require ([0, 1, 2, 3].all templateUnion.contains) "storage-loop corpus misses a generated template"
  require (["returned", "reverted"].all outcomes.contains && requiredPatterns.all patterns.contains)
    "storage-loop corpus misses an observed outcome or completion pattern"
  return Json.mkObj [("profile", toJson "stateful-storage-loops"), ("scenarios", toJson entries.size),
    ("transactions", toJson transactionTotal), ("masks", toJson masks), ("iterationCounts", toJson counts),
    ("carriedSlots", toJson carried), ("patterns", toJson patterns)]

private def checked {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def rejects {α : Type} (result : Except String α) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "invalid storage-loop corpus unexpectedly passed")

def testSourceStorageLoopCorpus : IO Unit := do
  let manifest ← checked (Json.parse (← IO.FS.readFile "scripts/semantic-storage-loop-corpus.json"))
  let summary ← checked (validateManifest manifest)
  let entries ← checked (manifest.getObjValAs? (Array Json) "cases")
  let some first := entries[0]? | throw (IO.userError "missing first storage-loop case")
  let some generatedEntry := entries.find? (fun entry => (entry.getObjVal? "generation").isOk) |
    throw (IO.userError "missing generated storage-loop case")
  let replace := fun (original changed : Json) => manifest.setObjVal! "cases"
    (.arr (entries.map fun entry => if entry == original then changed else entry))
  let history ← checked (first.getObjValAs? (Array Json) "expectedHistory")
  let row := history[0]!
  -- An output, a slot, a missing row and a status are all checked.
  let changedOutput := row.setObjVal! "output" (toJson ("0x" ++ String.ofList (List.replicate 64 'f')))
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr (history.set! 0 changedOutput)))))
  let storage ← checked (row.getObjValAs? (Array Json) "committedStorage")
  let changedSlot := row.setObjVal! "committedStorage" (.arr (storage.set! 8 (storage[8]!.setObjVal! "value" (toJson "7"))))
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr (history.set! 0 changedSlot)))))
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr (history.pop)))))
  let generatedHistory ← checked (generatedEntry.getObjValAs? (Array Json) "expectedHistory")
  let flipped := if (generatedHistory[0]!.getObjValAs? String "status").toOption == some "returned" then "reverted" else "returned"
  rejects (validateManifest (replace generatedEntry (generatedEntry.setObjVal! "expectedHistory"
    (.arr (generatedHistory.set! 0 (generatedHistory[0]!.setObjVal! "status" (toJson flipped)))))))
  -- A recorded iteration count and the plan's mask are both checked.
  let transactions ← checked (first.getObjValAs? (Array Json) "transactions")
  rejects (validateManifest (replace first (first.setObjVal! "transactions"
    (.arr (transactions.set! 0 (transactions[0]!.setObjVal! "iterations" (toJson 0)))))))
  let plan ← checked (first.getObjVal? "storageLoopPlan")
  rejects (validateManifest (replace first (first.setObjVal! "storageLoopPlan" (plan.setObjVal! "mask" (toJson 3)))))
  rejects (validateManifest (replace first (first.setObjVal! "expectedFeatures" (toJson ([] : List String)))))
  rejects (validateManifest (manifest.setObjVal! "cases" (.arr (entries.push first))))
  for (key, value) in [
      ("profile", toJson "stateful-storage"), ("templateVersion", toJson "forged"),
      ("cases", .arr #[]), ("requiredInputs", toJson ([] : List String)),
      ("requiredMasks", toJson [1, 3, 7]), ("requiredIterationCounts", toJson [0, 1, 7]),
      ("requiredCarriedSlots", toJson [2, 3]), ("requiredIterationCarries", toJson (["iteration"] : List String)),
      ("requiredHelperCounts", toJson [1, 2]),
      ("requiredCompletionPatterns", toJson (["returned,returned,returned,returned"] : List String))] do
    rejects (validateManifest (manifest.setObjVal! key value))
  rejects (validateManifest manifest 0)
  IO.println summary.compress

end Tests.SourceStorageLoopCorpus
