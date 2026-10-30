import Solcore.Synthesis.Source.NestedArrayCases

/-! The fixed nested-array corpus checks actual original Core histories against
independently computed expectations: status, payload and slots zero to eight
after every transaction. Coverage describes the checked step AST, the elements
the step folds, the outer lengths, the row lengths and the completions.
Source/Rust/EVM agreement is a separate external validation. -/
set_option autoImplicit false

namespace Tests.SourceNestedArrayCorpus
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
  ("generatorVersion", generatorVersion), ("profileVersion", NestedArray.profileVersion),
  ("functionVersion", Solcore.Synthesis.Core.NestedArray.version),
  ("templateVersion", NestedArray.templateVersion), ("stepProfileVersion", Aggregate.profileVersion),
  ("stepFunctionVersion", Aggregates.version), ("stepTemplateVersion", Aggregate.templateVersion),
  ("emitterVersion", NestedArray.emitterVersion), ("wrapperVersion", NestedArray.wrapperVersion)]

private def words (values : List Word) : List String := values.map fun value => toString value.val

/-- Imported entries are emitted from their saved plan and sequence; generated
entries are regenerated from their seed. Both are checked by full replay. -/
private def entryCase (entry : Json) (fuel : Nat) : Except String Json := do
  if let .ok request := entry.getObjVal? "generation" then
    let some seed := (← request.getObjValAs? String "seed").toNat? | throw "invalid generation seed"
    let corpus := NestedArray.generateCases (Seed.ofNat seed) (← request.getObjValAs? Nat "maxProgramNodes") 1 1 fuel
    require ((← string corpus "status") == "complete") "generated entry was excluded"
    let some saved := (← corpus.getObjValAs? (Array Json) "cases")[0]? | throw "generated entry has no case"
    return saved
  let plan ← NestedArray.checkedPlan (← entry.getObjVal? "nestedArrayPlan")
  let scenario ← NestedArray.checkedScenario plan (← NestedArray.decodeTransactions (← entry.getObjVal? "transactions"))
  NestedArray.emitCase scenario (Json.mkObj [("kind", toJson "imported")]) fuel

private def templates (saved : Json) : Except String (List Nat) := do
  let origin ← (← saved.getObjVal? "provenance").getObjVal? "origin"
  if (← string origin "kind") != "nested-array-generated" then return []
  let helpers ← (← origin.getObjVal? "stepOrigin").getObjValAs? (List Json) "helpers"
  helpers.mapM fun helper => helper.getObjValAs? Nat "template"

def validateManifest (manifest : Json) (fuel : Nat := 1000000) : Except String Json := do
  require ((← string manifest "schema") == "solcore-lean.semantic-storage-corpus-manifest.v1" &&
    (← string manifest "profile") == "stateful-nested-array" &&
    (← string manifest "coverageKind") == "step-core-ast-features") "unexpected nested-array manifest scope"
  for (key, expected) in versions do
    require ((← string manifest key) == expected) ("nested-array manifest changed " ++ key)
  let requiredFeatures ← strings manifest "requiredFeatures"
  let requiredInputs ← strings manifest "requiredInputs"
  require (sameMembers requiredInputs (words Storage.boundaryInputs))
    "nested-array corpus must require all six boundary Words as elements"
  require (sameMembers (← naturals manifest "requiredRowCounts") (List.range 4))
    "nested-array corpus must require outer lengths zero to three"
  require (sameMembers (← naturals manifest "requiredRowLengths") (List.range 3))
    "nested-array corpus must require row lengths zero to two"
  require ((← manifest.getObjValAs? (List Nat) "requiredHelperCounts") == [1, 2, 3] &&
    (← manifest.getObjValAs? (List Nat) "requiredTransactionCounts") == [1, 2, 3])
    "nested-array corpus must require one to three helpers and transactions"
  require ((← (← manifest.getObjVal? "generationRecipeRequirements").getObjValAs? (List Nat) "templates") == [0, 1, 2, 3])
    "nested-array corpus must require all four step templates"
  require ((← strings manifest "requiredOutcomes") == ["returned", "reverted"]) "nested-array corpus must require both outcomes"
  let requiredPatterns ← strings manifest "requiredCompletionPatterns"
  require (!requiredPatterns.isEmpty) "nested-array corpus must require completion patterns"
  let entries ← manifest.getObjValAs? (Array Json) "cases"
  require (0 < entries.size && entries.size ≤ 64) "nested-array corpus must contain 1..64 scenarios"
  let mut identifiers : List String := []
  let mut features : List String := []
  let mut inputs : List String := []
  let mut rowCounts : List Nat := []
  let mut rowLengths : List Nat := []
  let mut helperCounts : List Nat := []
  let mut transactionCounts : List Nat := []
  let mut templateUnion : List Nat := []
  let mut outcomes : List String := []
  let mut patterns : List String := []
  let mut transactionTotal := 0
  for entry in entries do
    let identifier ← string entry "id"
    require (!identifiers.contains identifier) ("duplicate nested-array corpus id " ++ identifier)
    identifiers := identifier :: identifiers
    let saved ← entryCase entry fuel
    require ((← NestedArray.replayCase saved fuel) == saved) ("nested-array corpus entry did not replay: " ++ identifier)
    let scenario ← NestedArray.caseProgram saved
    if !(entry.getObjVal? "generation").isOk then
      require ((← saved.getObjVal? "nestedArrayPlan") == (← entry.getObjVal? "nestedArrayPlan") &&
        (← saved.getObjVal? "transactions") == (← entry.getObjVal? "transactions"))
        ("imported nested-array entry is not canonical: " ++ identifier)
    let caseFeatures := (← (← saved.getObjVal? "provenance").getObjValAs? (List String) "features").eraseDups
    require (sameMembers (← strings entry "expectedFeatures") caseFeatures)
      ("nested-array corpus features changed: " ++ identifier)
    let history := NestedArray.observe scenario Solcore.Synthesis.Stateful.StorageExecution.fixtureBindings fuel
    let statuses ← NestedArray.checkProtocol scenario history
    let observed ← history.getObjValAs? (List Json) "transactions"
    let expected ← entry.getObjValAs? (List Json) "expectedHistory"
    require (observed.length == expected.length) ("nested-array expected history length changed: " ++ identifier)
    for ((row, golden), tx) in (observed.zip expected).zip scenario.transactions do
      let actual := Json.mkObj [("id", ← row.getObjVal? "id"), ("status", ← row.getObjVal? "status"),
        ("output", ← row.getObjVal? "output"), ("committedStorage", ← row.getObjVal? "committedStorage")]
      require (actual == golden) ("original Core differs from the independent history: " ++ identifier ++ " " ++ actual.compress)
      inputs := (inputs ++ words tx.values.flatten).eraseDups
      rowCounts := (rowCounts ++ [tx.values.length]).eraseDups
      rowLengths := (rowLengths ++ tx.values.map (·.length)).eraseDups
    transactionTotal := transactionTotal + observed.length
    features := (features ++ caseFeatures).eraseDups
    helperCounts := (helperCounts ++ [scenario.plan.step.helpers.length]).eraseDups
    transactionCounts := (transactionCounts ++ [scenario.transactions.length]).eraseDups
    templateUnion := (templateUnion ++ (← templates saved)).eraseDups
    outcomes := (outcomes ++ statuses).eraseDups
    patterns := (patterns ++ [String.intercalate "," statuses]).eraseDups
  require (requiredFeatures.all features.contains) "nested-array corpus misses a required step feature"
  require (requiredInputs.all inputs.contains) "nested-array corpus misses a boundary element"
  require ((List.range 4).all rowCounts.contains && (List.range 3).all rowLengths.contains)
    "nested-array corpus misses an outer length or a row length"
  require ([1, 2, 3].all helperCounts.contains && [1, 2, 3].all transactionCounts.contains)
    "nested-array corpus misses a helper or transaction count"
  require ([0, 1, 2, 3].all templateUnion.contains) "nested-array corpus misses a generated template"
  require (["returned", "reverted"].all outcomes.contains && requiredPatterns.all patterns.contains)
    "nested-array corpus misses an observed outcome or completion pattern"
  return Json.mkObj [("profile", toJson "stateful-nested-array"), ("scenarios", toJson entries.size),
    ("transactions", toJson transactionTotal), ("rowCounts", toJson rowCounts), ("rowLengths", toJson rowLengths),
    ("patterns", toJson patterns)]

private def checked {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def rejects {α : Type} (result : Except String α) (message : String) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError ("invalid nested-array corpus unexpectedly passed: " ++ message))

def testSourceNestedArrayCorpus : IO Unit := do
  let manifest ← checked (Json.parse (← IO.FS.readFile "scripts/semantic-nested-array-corpus.json"))
  let summary ← checked (validateManifest manifest)
  let entries ← checked (manifest.getObjValAs? (Array Json) "cases")
  let some first := entries[0]? | throw (IO.userError "missing first nested-array case")
  let some generatedEntry := entries.find? (fun entry => (entry.getObjVal? "generation").isOk) |
    throw (IO.userError "missing generated nested-array case")
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
  rejects (validateManifest (withRow 0 (row.setObjVal! "committedStorage" (.arr (storage.set! 7 (storage[7]!.setObjVal! "value" (toJson "2")))))))
    "changed row count"
  rejects (validateManifest (withRow 0 (row.setObjVal! "committedStorage" (.arr (storage.set! 8 (storage[8]!.setObjVal! "value" (toJson "4")))))))
    "changed element count"
  rejects (validateManifest (withRow 0 (row.setObjVal! "committedStorage" (.arr (storage.set! 5 (storage[5]!.setObjVal! "value" (toJson "0")))))))
    "changed element result"
  rejects (validateManifest (withRow 0 (row.setObjVal! "committedStorage" (.arr (storage.set! 3 (storage[3]!.setObjVal! "value" (toJson "4")))))))
    "an absent element's slot written"
  -- The first scenario's second transaction reverts: committing its writes is wrong.
  let reverted := history[1]!
  let revertedStorage ← checked (reverted.getObjValAs? (Array Json) "committedStorage")
  rejects (validateManifest (withRow 1 (reverted.setObjVal! "committedStorage"
    (.arr (revertedStorage.set! 7 (revertedStorage[7]!.setObjVal! "value" (toJson "5"))))))) "a reverted row count committed"
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr history.pop)))) "popped history"
  let generatedHistory ← checked (generatedEntry.getObjValAs? (Array Json) "expectedHistory")
  let generatedStatus ← checked (generatedHistory[0]!.getObjValAs? String "status")
  rejects (validateManifest (replace generatedEntry (generatedEntry.setObjVal! "expectedHistory"
    (.arr (generatedHistory.set! 0 (generatedHistory[0]!.setObjVal! "status"
      (toJson (if generatedStatus == "returned" then "reverted" else "returned")))))))) "flipped status"
  -- Consistently re-encoded values with one changed element, one more empty
  -- row or one row fewer no longer match their history.
  let transactions ← checked (NestedArray.decodeTransactions (← checked (first.getObjVal? "transactions")))
  let some tx := transactions[0]? | throw (IO.userError "missing first nested-array transaction")
  let changed := {tx with values := tx.values.set 0 ((tx.values.getD 0 []).set 0 (Word.ofNatModulo 2))}
  rejects (validateManifest (replace first (first.setObjVal! "transactions"
    (NestedArray.transactionsJson (changed :: transactions.drop 1))))) "changed element"
  let longer := {tx with values := tx.values.take 2 ++ [[]]}
  rejects (validateManifest (replace first (first.setObjVal! "transactions"
    (NestedArray.transactionsJson (longer :: transactions.drop 1))))) "replaced row by an empty row"
  let shorter := {tx with values := tx.values.take 2}
  rejects (validateManifest (replace first (first.setObjVal! "transactions"
    (NestedArray.transactionsJson (shorter :: transactions.drop 1))))) "dropped row"
  rejects (validateManifest (replace first (first.setObjVal! "expectedFeatures" (toJson ([] : List String))))) "features"
  rejects (validateManifest (replace generatedEntry (generatedEntry.setObjVal! "generation"
    (Json.mkObj [("seed", toJson "13"), ("maxProgramNodes", toJson (384 : Nat))])))) "changed seed"
  rejects (validateManifest (manifest.setObjVal! "cases" (.arr (#[first] ++ entries)))) "duplicate entry"
  for (key, value) in [
      ("profile", toJson "stateful-dynamic-array"), ("wrapperVersion", toJson "forged"),
      ("functionVersion", toJson "core-dynamic-array-contract-v2"),
      ("cases", .arr #[]), ("requiredInputs", toJson ([] : List String)), ("requiredHelperCounts", toJson [1, 2]),
      ("requiredRowCounts", toJson ([0, 1, 2] : List Nat)), ("requiredRowCounts", toJson ([0, 1, 2, 3, 4] : List Nat)),
      ("requiredRowLengths", toJson ([1, 2] : List Nat)), ("requiredRowLengths", toJson ([0, 1, 2, 3] : List Nat)),
      ("requiredCompletionPatterns", toJson (["reverted,reverted,reverted"] : List String))] do
    rejects (validateManifest (manifest.setObjVal! key value)) key
  rejects (validateManifest manifest 0) "zero fuel"
  IO.println summary.compress

end Tests.SourceNestedArrayCorpus
