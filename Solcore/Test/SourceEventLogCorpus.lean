import Solcore.Synthesis.Source.EventLogCases

/-! The fixed event-log corpus checks actual original Core histories against
independently computed expectations: status, payload, slots zero and one, and
every committed log's emitter, topics and data after every transaction.
Coverage describes the checked step AST, the inputs and completions, and the
committed log counts, topic arities, data lengths and the guarded sites that
reverted transactions discard. Source/Rust/EVM agreement is a separate
external validation. -/
set_option autoImplicit false

namespace Tests.SourceEventLogCorpus
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
  ("generatorVersion", generatorVersion), ("profileVersion", EventLog.profileVersion),
  ("functionVersion", Solcore.Synthesis.Core.EventLog.version),
  ("framingVersion", Solcore.Synthesis.Core.EventLog.framingVersion),
  ("templateVersion", EventLog.templateVersion), ("stepProfileVersion", Aggregate.profileVersion),
  ("stepFunctionVersion", Aggregates.version), ("stepTemplateVersion", Aggregate.templateVersion),
  ("emitterVersion", EventLog.emitterVersion), ("wrapperVersion", EventLog.wrapperVersion)]

private def words (values : List Word) : List String := values.map fun value => toString value.val

/-- Imported entries are emitted from their saved plan and sequence; generated
entries are regenerated from their seed. Both are checked by full replay. -/
private def entryCase (entry : Json) (fuel : Nat) : Except String Json := do
  if let .ok request := entry.getObjVal? "generation" then
    let some seed := (← request.getObjValAs? String "seed").toNat? | throw "invalid generation seed"
    let corpus := EventLog.generateCases (Seed.ofNat seed) (← request.getObjValAs? Nat "maxProgramNodes") 1 1 fuel
    require ((← string corpus "status") == "complete") "generated entry was excluded"
    let some saved := (← corpus.getObjValAs? (Array Json) "cases")[0]? | throw "generated entry has no case"
    return saved
  let plan ← EventLog.checkedPlan (← entry.getObjVal? "logPlan")
  let scenario ← EventLog.checkedScenario plan (← EventLog.decodeTransactions (← entry.getObjVal? "transactions"))
  EventLog.emitCase scenario (Json.mkObj [("kind", toJson "imported")]) fuel

private def templates (saved : Json) : Except String (List Nat) := do
  let origin ← (← saved.getObjVal? "provenance").getObjVal? "origin"
  if (← string origin "kind") != "log-generated" then return []
  let helpers ← (← origin.getObjVal? "stepOrigin").getObjValAs? (List Json) "helpers"
  helpers.mapM fun helper => helper.getObjValAs? Nat "template"

private def naturals (manifest : Json) (key : String) : Except String (List Nat) :=
  manifest.getObjValAs? (List Nat) key

def validateManifest (manifest : Json) (fuel : Nat := 1000000) : Except String Json := do
  require ((← string manifest "schema") == "solcore-lean.semantic-storage-corpus-manifest.v1" &&
    (← string manifest "profile") == "stateful-logs" &&
    (← string manifest "coverageKind") == "step-core-ast-features") "unexpected log manifest scope"
  for (key, expected) in versions do
    require ((← string manifest key) == expected) ("log manifest changed " ++ key)
  let requiredFeatures ← strings manifest "requiredFeatures"
  let requiredInputs ← strings manifest "requiredInputs"
  require (sameMembers requiredInputs (words EventLog.boundaryInputs))
    "log corpus must require all six boundary inputs"
  require ((← naturals manifest "requiredHelperCounts") == [1, 2, 3] &&
    (← naturals manifest "requiredTransactionCounts") == [1, 2, 3])
    "log corpus must require one to three helpers and transactions"
  require ((← (← manifest.getObjVal? "generationRecipeRequirements").getObjValAs? (List Nat) "templates") == [0, 1, 2, 3])
    "log corpus must require all four step templates"
  require ((← strings manifest "requiredOutcomes") == ["returned", "reverted"]) "log corpus must require both outcomes"
  let requiredPatterns ← strings manifest "requiredCompletionPatterns"
  require (!requiredPatterns.isEmpty) "log corpus must require completion patterns"
  require ((← naturals manifest "requiredLogCounts") == [0, 1, 2, 3] &&
    (← naturals manifest "requiredTopicArities") == [0, 1, 2, 3, 4] &&
    (← naturals manifest "requiredDataSizes") == [0, 32, 64] &&
    (← naturals manifest "requiredDiscardedLogCounts") == [0, 1, 2, 3])
    "log corpus must require every log count, topic arity, data length and discarded count"
  let entries ← manifest.getObjValAs? (Array Json) "cases"
  require (0 < entries.size && entries.size ≤ 64) "log corpus must contain 1..64 scenarios"
  let mut identifiers : List String := []
  let mut features : List String := []
  let mut inputs : List String := []
  let mut helperCounts : List Nat := []
  let mut transactionCounts : List Nat := []
  let mut templateUnion : List Nat := []
  let mut outcomes : List String := []
  let mut patterns : List String := []
  let mut logCounts : List Nat := []
  let mut arities : List Nat := []
  let mut sizes : List Nat := []
  let mut discarded : List Nat := []
  let mut transactionTotal := 0
  let mut logTotal := 0
  for entry in entries do
    let identifier ← string entry "id"
    require (!identifiers.contains identifier) ("duplicate log corpus id " ++ identifier)
    identifiers := identifier :: identifiers
    let saved ← entryCase entry fuel
    require ((← EventLog.replayCase saved fuel) == saved) ("log corpus entry did not replay: " ++ identifier)
    let scenario ← EventLog.caseProgram saved
    if !(entry.getObjVal? "generation").isOk then
      require ((← saved.getObjVal? "logPlan") == (← entry.getObjVal? "logPlan") &&
        (← saved.getObjVal? "transactions") == (← entry.getObjVal? "transactions"))
        ("imported log entry is not canonical: " ++ identifier)
    let caseFeatures := (← (← saved.getObjVal? "provenance").getObjValAs? (List String) "features").eraseDups
    require (sameMembers (← strings entry "expectedFeatures") caseFeatures)
      ("log corpus features changed: " ++ identifier)
    let history := EventLog.observe scenario Solcore.Synthesis.Stateful.StorageExecution.fixtureBindings fuel
    let statuses ← EventLog.checkShapes scenario history
    let observed ← history.getObjValAs? (List Json) "transactions"
    let expected ← entry.getObjValAs? (List Json) "expectedHistory"
    require (observed.length == expected.length) ("log expected history length changed: " ++ identifier)
    for ((row, golden), tx) in (observed.zip expected).zip scenario.transactions do
      let actual := Json.mkObj [("id", ← row.getObjVal? "id"), ("status", ← row.getObjVal? "status"),
        ("output", ← row.getObjVal? "output"), ("committedStorage", ← row.getObjVal? "committedStorage"),
        ("logs", ← row.getObjVal? "logs")]
      require (actual == golden) ("original Core differs from the independent history: " ++ identifier ++ " " ++ actual.compress)
      let logs ← row.getObjValAs? (List Json) "logs"
      logCounts := (logCounts ++ [logs.length]).eraseDups
      logTotal := logTotal + logs.length
      for log in logs do
        arities := (arities ++ [(← log.getObjValAs? (List String) "topics").length]).eraseDups
        sizes := (sizes ++ [((← string log "data").length - 2) / 2]).eraseDups
      if (← string row "status") == "reverted" then
        discarded := (discarded ++ [(EventLog.guardedSites scenario.plan tx).length]).eraseDups
    transactionTotal := transactionTotal + observed.length
    features := (features ++ caseFeatures).eraseDups
    inputs := (inputs ++ scenario.transactions.map fun tx => toString tx.input.val).eraseDups
    helperCounts := (helperCounts ++ [scenario.plan.step.helpers.length]).eraseDups
    transactionCounts := (transactionCounts ++ [scenario.transactions.length]).eraseDups
    templateUnion := (templateUnion ++ (← templates saved)).eraseDups
    outcomes := (outcomes ++ statuses).eraseDups
    patterns := (patterns ++ [String.intercalate "," statuses]).eraseDups
  require (requiredFeatures.all features.contains) "log corpus misses a required step feature"
  require (requiredInputs.all inputs.contains) "log corpus misses an input"
  require ([1, 2, 3].all helperCounts.contains && [1, 2, 3].all transactionCounts.contains)
    "log corpus misses a helper or transaction count"
  require ([0, 1, 2, 3].all templateUnion.contains) "log corpus misses a generated template"
  require (["returned", "reverted"].all outcomes.contains && requiredPatterns.all patterns.contains)
    "log corpus misses an observed outcome or completion pattern"
  require ([0, 1, 2, 3].all logCounts.contains && [0, 1, 2, 3, 4].all arities.contains &&
    [0, 32, 64].all sizes.contains && [0, 1, 2, 3].all discarded.contains)
    "log corpus misses a log count, topic arity, data length or discarded count"
  return Json.mkObj [("profile", toJson "stateful-logs"), ("scenarios", toJson entries.size),
    ("transactions", toJson transactionTotal), ("logs", toJson logTotal), ("patterns", toJson patterns)]

private def checked {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def rejects {α : Type} (result : Except String α) (message : String) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError ("invalid log corpus unexpectedly passed: " ++ message))

def testSourceEventLogCorpus : IO Unit := do
  let manifest ← checked (Json.parse (← IO.FS.readFile "scripts/semantic-log-corpus.json"))
  let summary ← checked (validateManifest manifest)
  let entries ← checked (manifest.getObjValAs? (Array Json) "cases")
  let some first := entries[0]? | throw (IO.userError "missing first log case")
  let some generatedEntry := entries.find? (fun entry => (entry.getObjVal? "generation").isOk) |
    throw (IO.userError "missing generated log case")
  let replace := fun (original changed : Json) => manifest.setObjVal! "cases"
    (.arr (entries.map fun entry => if entry == original then changed else entry))
  let history ← checked (first.getObjValAs? (Array Json) "expectedHistory")
  let withRow := fun (row : Json) => replace first (first.setObjVal! "expectedHistory" (.arr (history.set! 0 row)))
  let row := history[0]!
  rejects (validateManifest (withRow (row.setObjVal! "output" (toJson ("0x" ++ String.ofList (List.replicate 64 'f'))))))
    "changed output"
  let storage ← checked (row.getObjValAs? (Array Json) "committedStorage")
  rejects (validateManifest (withRow (row.setObjVal! "committedStorage" (.arr (storage.set! 0 (storage[0]!.setObjVal! "value" (toJson "7")))))))
    "changed slot"
  let logs ← checked (row.getObjValAs? (Array Json) "logs")
  let some log := logs[0]? | throw (IO.userError "first log history has no committed log")
  let topics ← checked (log.getObjValAs? (Array String) "topics")
  for (changed, reason) in [
      (logs.set! 0 (log.setObjVal! "topics" (toJson (topics.set! 0 "1"))), "changed topic"),
      (logs.set! 0 (log.setObjVal! "topics" (toJson topics.reverse)), "reordered topics"),
      (logs.set! 0 (log.setObjVal! "data" (toJson "0x")), "removed data"),
      (logs.set! 0 (log.setObjVal! "address" (toJson "3")), "changed emitter"),
      (logs.pop, "removed log"), (logs.push log, "duplicated log"), (logs.reverse, "reordered logs")] do
    rejects (validateManifest (withRow (row.setObjVal! "logs" (.arr changed)))) reason
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr history.pop)))) "popped history"
  let generatedHistory ← checked (generatedEntry.getObjValAs? (Array Json) "expectedHistory")
  rejects (validateManifest (replace generatedEntry (generatedEntry.setObjVal! "expectedHistory"
    (.arr (generatedHistory.set! 0 (generatedHistory[0]!.setObjVal! "status" (toJson "reverted"))))))) "flipped status"
  let transactions ← checked (first.getObjValAs? (Array Json) "transactions")
  rejects (validateManifest (replace first (first.setObjVal! "transactions"
    (.arr (transactions.set! 0 (transactions[0]!.setObjVal! "flags" (toJson "4"))))))) "changed flags"
  let plan ← checked (first.getObjVal? "logPlan")
  rejects (validateManifest (replace first (first.setObjVal! "logPlan" (plan.setObjVal! "sites" (toJson ([] : List Json))))))
    "removed sites"
  rejects (validateManifest (replace first (first.setObjVal! "expectedFeatures" (toJson ([] : List String))))) "features"
  rejects (validateManifest (replace generatedEntry (generatedEntry.setObjVal! "generation"
    (Json.mkObj [("seed", toJson "13"), ("maxProgramNodes", toJson (384 : Nat))])))) "changed seed"
  rejects (validateManifest (manifest.setObjVal! "cases" (.arr (entries.push first)))) "duplicate entry"
  for (key, value) in [
      ("profile", toJson "stateful-keyed-storage"), ("framingVersion", toJson "forged"),
      ("cases", .arr #[]), ("requiredInputs", toJson ([] : List String)), ("requiredHelperCounts", toJson [1, 2]),
      ("requiredTopicArities", toJson [0, 1, 2, 3]), ("requiredDataSizes", toJson [0, 32]),
      ("requiredLogCounts", toJson [1, 2, 3]), ("requiredDiscardedLogCounts", toJson [1, 2, 3]),
      ("requiredCompletionPatterns", toJson (["reverted,reverted,reverted"] : List String))] do
    rejects (validateManifest (manifest.setObjVal! key value)) key
  rejects (validateManifest manifest 0) "zero fuel"
  IO.println summary.compress

end Tests.SourceEventLogCorpus
