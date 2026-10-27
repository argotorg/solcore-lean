import Solcore.Synthesis.Source.MalformedNestedArrayCases

/-! The fixed malformed-nested-array corpus checks actual original Core
histories against expectations computed without the std-modeling wrapper: a
prescribed std rejection reverts with its selector Word and keeps the slots; an
accepted transaction is the canonical nested-array contract on the Words std
decodes. Coverage describes the checked step AST, the canonical outer and row
lengths and element values, the malformation kinds and the rows they target,
the prescribed std outcomes and the completions. Source/Rust/EVM agreement is a
separate external validation. -/
set_option autoImplicit false

namespace Tests.SourceMalformedNestedArrayCorpus
open Lean Solcore.Core Solcore.Synthesis.Core Solcore.Synthesis.Source

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
  ("generatorVersion", generatorVersion), ("profileVersion", MalformedNestedArray.profileVersion),
  ("functionVersion", Solcore.Synthesis.Core.MalformedNestedArray.version),
  ("templateVersion", MalformedNestedArray.templateVersion), ("stepProfileVersion", Aggregate.profileVersion),
  ("stepFunctionVersion", Aggregates.version), ("stepTemplateVersion", Aggregate.templateVersion),
  ("emitterVersion", MalformedNestedArray.emitterVersion), ("wrapperVersion", MalformedNestedArray.wrapperVersion)]

private def words (values : List Word) : List String := values.map fun value => toString value.val

/-- The prescribed std outcomes, by name. -/
private def outcomeNames : List String :=
  ["0x4924aef0", "0x08638556", "accepted"]

/-- Imported entries are emitted from their saved plan and sequence; generated
entries are regenerated from their seed. Both are checked by full replay. -/
private def entryCase (entry : Json) (fuel : Nat) : Except String Json := do
  if let .ok request := entry.getObjVal? "generation" then
    let some seed := (← request.getObjValAs? String "seed").toNat? | throw "invalid generation seed"
    let corpus := MalformedNestedArray.generateCases (Seed.ofNat seed) (← request.getObjValAs? Nat "maxProgramNodes") 1 1 fuel
    require ((← string corpus "status") == "complete") "generated entry was excluded"
    let some saved := (← corpus.getObjValAs? (Array Json) "cases")[0]? | throw "generated entry has no case"
    return saved
  let plan ← MalformedNestedArray.checkedPlan (← entry.getObjVal? "malformedNestedArrayPlan")
  let scenario ← MalformedNestedArray.checkedScenario plan
    (← MalformedNestedArray.decodeTransactions (← entry.getObjVal? "transactions"))
  MalformedNestedArray.emitCase scenario (Json.mkObj [("kind", toJson "imported")]) fuel

private def templates (saved : Json) : Except String (List Nat) := do
  let origin ← (← saved.getObjVal? "provenance").getObjVal? "origin"
  if (← string origin "kind") != "malformed-nested-array-generated" then return []
  let helpers ← (← origin.getObjVal? "stepOrigin").getObjValAs? (List Json) "helpers"
  helpers.mapM fun helper => helper.getObjValAs? Nat "template"

def validateManifest (manifest : Json) (fuel : Nat := 1000000) : Except String Json := do
  require ((← string manifest "schema") == "solcore-lean.semantic-storage-corpus-manifest.v1" &&
    (← string manifest "profile") == "stateful-malformed-nested-array" &&
    (← string manifest "coverageKind") == "step-core-ast-features") "unexpected malformed-nested-array manifest scope"
  for (key, expected) in versions do
    require ((← string manifest key) == expected) ("malformed-nested-array manifest changed " ++ key)
  let requiredFeatures ← strings manifest "requiredFeatures"
  let requiredInputs ← strings manifest "requiredInputs"
  require (sameMembers requiredInputs (words MalformedNestedArray.boundaryInputs))
    "malformed-nested-array corpus must require all six boundary elements"
  require ((← manifest.getObjValAs? (List Nat) "requiredRowCounts") == [0, 1, 2, 3, 4] &&
    (← manifest.getObjValAs? (List Nat) "requiredRowLengths") == [0, 1, 2, 3])
    "malformed-nested-array corpus must require zero to four rows of zero to three elements"
  require ((← manifest.getObjValAs? (List Nat) "requiredMalformedRows") == [0, 1, 2, 3])
    "malformed-nested-array corpus must require row malformations of rows zero to three"
  require ((← strings manifest "requiredMalformations") == MalformedNestedArray.malformationKinds)
    "malformed-nested-array corpus must require every malformation kind"
  require ((← strings manifest "requiredRejections") == outcomeNames)
    "malformed-nested-array corpus must require both std rejections and acceptance"
  require ((← manifest.getObjValAs? (List Nat) "requiredHelperCounts") == [1, 2, 3] &&
    (← manifest.getObjValAs? (List Nat) "requiredTransactionCounts") == [1, 2, 3])
    "malformed-nested-array corpus must require one to three helpers and transactions"
  require ((← (← manifest.getObjVal? "generationRecipeRequirements").getObjValAs? (List Nat) "templates") == [0, 1, 2, 3])
    "malformed-nested-array corpus must require all four step templates"
  require ((← strings manifest "requiredOutcomes") == ["returned", "reverted"])
    "malformed-nested-array corpus must require both outcomes"
  let requiredPatterns ← strings manifest "requiredCompletionPatterns"
  require (!requiredPatterns.isEmpty) "malformed-nested-array corpus must require completion patterns"
  let entries ← manifest.getObjValAs? (Array Json) "cases"
  require (0 < entries.size && entries.size ≤ 64) "malformed-nested-array corpus must contain 1..64 scenarios"
  let mut identifiers : List String := []
  let mut features : List String := []
  let mut inputs : List String := []
  let mut rowCounts : List Nat := []
  let mut rowLengths : List Nat := []
  let mut malformedRows : List Nat := []
  let mut kinds : List String := []
  let mut rejections : List String := []
  let mut helperCounts : List Nat := []
  let mut transactionCounts : List Nat := []
  let mut templateUnion : List Nat := []
  let mut outcomes : List String := []
  let mut patterns : List String := []
  let mut transactionTotal := 0
  for entry in entries do
    let identifier ← string entry "id"
    require (!identifiers.contains identifier) ("duplicate malformed-nested-array corpus id " ++ identifier)
    identifiers := identifier :: identifiers
    let saved ← entryCase entry fuel
    require ((← MalformedNestedArray.replayCase saved fuel) == saved) ("malformed-nested-array corpus entry did not replay: " ++ identifier)
    let scenario ← MalformedNestedArray.caseProgram saved
    if !(entry.getObjVal? "generation").isOk then
      require ((← saved.getObjVal? "malformedNestedArrayPlan") == (← entry.getObjVal? "malformedNestedArrayPlan") &&
        (← saved.getObjVal? "transactions") == (← entry.getObjVal? "transactions"))
        ("imported malformed-nested-array entry is not canonical: " ++ identifier)
    let caseFeatures := (← (← saved.getObjVal? "provenance").getObjValAs? (List String) "features").eraseDups
    require (sameMembers (← strings entry "expectedFeatures") caseFeatures)
      ("malformed-nested-array corpus features changed: " ++ identifier)
    let history := MalformedNestedArray.observe scenario Solcore.Synthesis.Stateful.StorageExecution.fixtureBindings fuel
    require ((← string history "status") == "complete") ("malformed-nested-array corpus history incomplete: " ++ identifier)
    let observed ← history.getObjValAs? (List Json) "transactions"
    let expected ← entry.getObjValAs? (List Json) "expectedHistory"
    require (observed.length == expected.length) ("malformed-nested-array expected history length changed: " ++ identifier)
    let mut statuses : List String := []
    for (row, golden) in observed.zip expected do
      let actual := Json.mkObj [("id", ← row.getObjVal? "id"), ("status", ← row.getObjVal? "status"),
        ("output", ← row.getObjVal? "output"), ("committedStorage", ← row.getObjVal? "committedStorage")]
      require (actual == golden)
        ("original Core differs from the expectation without the std wrapper: " ++ identifier ++ " " ++ actual.compress)
      statuses := statuses ++ [← string row "status"]
    transactionTotal := transactionTotal + observed.length
    features := (features ++ caseFeatures).eraseDups
    inputs := (inputs ++ scenario.transactions.flatMap fun tx =>
      tx.values.flatMap fun row => row.map fun value => toString value.val).eraseDups
    rowCounts := (rowCounts ++ scenario.transactions.map (·.values.length)).eraseDups
    rowLengths := (rowLengths ++ scenario.transactions.flatMap fun tx => tx.values.map (·.length)).eraseDups
    malformedRows := (malformedRows ++ scenario.transactions.filterMap (MalformedNestedArray.rowOf ·.malformation)).eraseDups
    kinds := (kinds ++ scenario.transactions.map (MalformedNestedArray.kindOf ·.malformation)).eraseDups
    rejections := (rejections ++ scenario.transactions.map fun tx =>
      (MalformedNestedArray.prescribed tx).map MalformedNestedArray.selectorText |>.getD "accepted").eraseDups
    helperCounts := (helperCounts ++ [scenario.plan.step.helpers.length]).eraseDups
    transactionCounts := (transactionCounts ++ [scenario.transactions.length]).eraseDups
    templateUnion := (templateUnion ++ (← templates saved)).eraseDups
    outcomes := (outcomes ++ statuses).eraseDups
    patterns := (patterns ++ [String.intercalate "," statuses]).eraseDups
  require (requiredFeatures.all features.contains) "malformed-nested-array corpus misses a required step feature"
  require (requiredInputs.all inputs.contains) "malformed-nested-array corpus misses a boundary element"
  require ([0, 1, 2, 3, 4].all rowCounts.contains && [0, 1, 2, 3].all rowLengths.contains)
    "malformed-nested-array corpus misses an outer or row length"
  require ([0, 1, 2, 3].all malformedRows.contains) "malformed-nested-array corpus misses a malformed row"
  require (MalformedNestedArray.malformationKinds.all kinds.contains) "malformed-nested-array corpus misses a malformation kind"
  require (outcomeNames.all rejections.contains) "malformed-nested-array corpus misses a std outcome"
  require ([1, 2, 3].all helperCounts.contains && [1, 2, 3].all transactionCounts.contains)
    "malformed-nested-array corpus misses a helper or transaction count"
  require ([0, 1, 2, 3].all templateUnion.contains) "malformed-nested-array corpus misses a generated template"
  require (["returned", "reverted"].all outcomes.contains && requiredPatterns.all patterns.contains)
    "malformed-nested-array corpus misses an observed outcome or completion pattern"
  return Json.mkObj [("profile", toJson "stateful-malformed-nested-array"), ("scenarios", toJson entries.size),
    ("transactions", toJson transactionTotal), ("malformations", toJson kinds), ("rejections", toJson rejections),
    ("patterns", toJson patterns)]

private def checked {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def rejects {α : Type} (result : Except String α) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "invalid malformed-nested-array corpus unexpectedly passed")

def testSourceMalformedNestedArrayCorpus : IO Unit := do
  let manifest ← checked (Json.parse (← IO.FS.readFile "scripts/semantic-malformed-nested-array-corpus.json"))
  let summary ← checked (validateManifest manifest)
  let entries ← checked (manifest.getObjValAs? (Array Json) "cases")
  let some first := entries[0]? | throw (IO.userError "missing first malformed-nested-array case")
  let some generatedEntry := entries.find? (fun entry => (entry.getObjVal? "generation").isOk) |
    throw (IO.userError "missing generated malformed-nested-array case")
  let replace := fun (original changed : Json) => manifest.setObjVal! "cases"
    (.arr (entries.map fun entry => if entry == original then changed else entry))
  let history ← checked (first.getObjValAs? (Array Json) "expectedHistory")
  let row := history[0]!
  -- A std rejection's selector, a slot, a missing row and a status are all checked.
  let changedOutput := row.setObjVal! "output" (toJson ("0x" ++ String.ofList (List.replicate 64 'f')))
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr (history.set! 0 changedOutput)))))
  let storage ← checked (row.getObjValAs? (Array Json) "committedStorage")
  let changedSlot := row.setObjVal! "committedStorage" (.arr (storage.set! 0 (storage[0]!.setObjVal! "value" (toJson "7"))))
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr (history.set! 0 changedSlot)))))
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr (history.pop)))))
  let generatedHistory ← checked (generatedEntry.getObjValAs? (Array Json) "expectedHistory")
  let flipped := if (generatedHistory[0]!.getObjValAs? String "status").toOption == some "returned" then "reverted" else "returned"
  rejects (validateManifest (replace generatedEntry (generatedEntry.setObjVal! "expectedHistory"
    (.arr (generatedHistory.set! 0 (generatedHistory[0]!.setObjVal! "status" (toJson flipped)))))))
  let transactions ← checked (first.getObjValAs? (Array Json) "transactions")
  rejects (validateManifest (replace first (first.setObjVal! "transactions"
    (.arr (transactions.set! 0 (transactions[0]!.setObjVal! "malformation" (Json.mkObj [("kind", toJson "none")])))))))
  rejects (validateManifest (replace first (first.setObjVal! "expectedFeatures" (toJson ([] : List String)))))
  rejects (validateManifest (manifest.setObjVal! "cases" (.arr (entries.push first))))
  for (key, value) in [
      ("profile", toJson "stateful-nested-array"), ("templateVersion", toJson "forged"),
      ("cases", .arr #[]), ("requiredInputs", toJson ([] : List String)),
      ("requiredRowCounts", toJson [0, 1, 2, 3]), ("requiredMalformedRows", toJson [0, 1, 2]),
      ("requiredHelperCounts", toJson [1, 2]),
      ("requiredMalformations", toJson (["none"] : List String)),
      ("requiredRejections", toJson (["accepted"] : List String)),
      ("requiredCompletionPatterns", toJson (["returned,returned,returned,returned"] : List String))] do
    rejects (validateManifest (manifest.setObjVal! key value))
  rejects (validateManifest manifest 0)
  IO.println summary.compress

end Tests.SourceMalformedNestedArrayCorpus
