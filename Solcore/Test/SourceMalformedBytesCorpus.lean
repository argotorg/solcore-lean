import Solcore.Synthesis.Source.MalformedBytesCases

/-! The fixed malformed-bytes corpus checks actual original Core histories
against expectations computed without the std-modeling wrapper: a prescribed
std rejection reverts with its selector Word and keeps the slots; an accepted
transaction is the canonical long-bytes contract on the payload std decodes,
its result moved by the calldata size. Coverage describes the checked step
AST, the canonical payload lengths and chunk Words, the malformation kinds,
the prescribed std outcomes and the completions. Source/Rust/EVM agreement is a
separate external validation. -/
set_option autoImplicit false

namespace Tests.SourceMalformedBytesCorpus
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
  ("generatorVersion", generatorVersion), ("profileVersion", MalformedBytes.profileVersion),
  ("functionVersion", Solcore.Synthesis.Core.MalformedBytes.version),
  ("templateVersion", MalformedBytes.templateVersion), ("stepProfileVersion", Aggregate.profileVersion),
  ("stepFunctionVersion", Aggregates.version), ("stepTemplateVersion", Aggregate.templateVersion),
  ("emitterVersion", MalformedBytes.emitterVersion), ("wrapperVersion", MalformedBytes.wrapperVersion)]

private def words (values : List Word) : List String := values.map fun value => toString value.val

/-- The zero-padded 32-byte chunk Words of a payload, which the step folds. -/
private def chunks (payload : List UInt8) : List String :=
  (List.range ((payload.length + 31) / 32)).map fun index =>
    let chunk : List UInt8 := ((payload.drop (32 * index)).take 32 ++ List.replicate 32 0).take 32
    toString (chunk.foldl (fun total byte => total * 256 + byte.toNat) 0)

/-- The prescribed std outcomes, by name. -/
private def outcomeNames : List String :=
  ["0x4924aef0", "0x08638556", "accepted"]

/-- Imported entries are emitted from their saved plan and sequence; generated
entries are regenerated from their seed. Both are checked by full replay. -/
private def entryCase (entry : Json) (fuel : Nat) : Except String Json := do
  if let .ok request := entry.getObjVal? "generation" then
    let some seed := (← request.getObjValAs? String "seed").toNat? | throw "invalid generation seed"
    let corpus := MalformedBytes.generateCases (Seed.ofNat seed) (← request.getObjValAs? Nat "maxProgramNodes") 1 1 fuel
    require ((← string corpus "status") == "complete") "generated entry was excluded"
    let some saved := (← corpus.getObjValAs? (Array Json) "cases")[0]? | throw "generated entry has no case"
    return saved
  let plan ← MalformedBytes.checkedPlan (← entry.getObjVal? "malformedBytesPlan")
  let scenario ← MalformedBytes.checkedScenario plan
    (← MalformedBytes.decodeTransactions (← entry.getObjVal? "transactions"))
  MalformedBytes.emitCase scenario (Json.mkObj [("kind", toJson "imported")]) fuel

private def templates (saved : Json) : Except String (List Nat) := do
  let origin ← (← saved.getObjVal? "provenance").getObjVal? "origin"
  if (← string origin "kind") != "malformed-bytes-generated" then return []
  let helpers ← (← origin.getObjVal? "stepOrigin").getObjValAs? (List Json) "helpers"
  helpers.mapM fun helper => helper.getObjValAs? Nat "template"

def validateManifest (manifest : Json) (fuel : Nat := 1000000) : Except String Json := do
  require ((← string manifest "schema") == "solcore-lean.semantic-storage-corpus-manifest.v1" &&
    (← string manifest "profile") == "stateful-malformed-bytes" &&
    (← string manifest "coverageKind") == "step-core-ast-features") "unexpected malformed-bytes manifest scope"
  for (key, expected) in versions do
    require ((← string manifest key) == expected) ("malformed-bytes manifest changed " ++ key)
  let requiredFeatures ← strings manifest "requiredFeatures"
  let requiredInputs ← strings manifest "requiredInputs"
  require (sameMembers requiredInputs (words Storage.boundaryInputs))
    "malformed-bytes corpus must require all six boundary Words as chunks"
  require ((← manifest.getObjValAs? (List Nat) "requiredPayloadLengths") == MalformedBytes.lengthBank)
    "malformed-bytes corpus must require every bank payload length"
  require ((← strings manifest "requiredMalformations") == MalformedBytes.malformationKinds)
    "malformed-bytes corpus must require every malformation kind"
  require ((← strings manifest "requiredRejections") == outcomeNames)
    "malformed-bytes corpus must require both std rejections and acceptance"
  require ((← manifest.getObjValAs? (List Nat) "requiredHelperCounts") == [1, 2, 3] &&
    (← manifest.getObjValAs? (List Nat) "requiredTransactionCounts") == [1, 2, 3])
    "malformed-bytes corpus must require one to three helpers and transactions"
  require ((← (← manifest.getObjVal? "generationRecipeRequirements").getObjValAs? (List Nat) "templates") == [0, 1, 2, 3])
    "malformed-bytes corpus must require all four step templates"
  require ((← strings manifest "requiredOutcomes") == ["returned", "reverted"])
    "malformed-bytes corpus must require both outcomes"
  let requiredPatterns ← strings manifest "requiredCompletionPatterns"
  require (!requiredPatterns.isEmpty) "malformed-bytes corpus must require completion patterns"
  let entries ← manifest.getObjValAs? (Array Json) "cases"
  require (0 < entries.size && entries.size ≤ 64) "malformed-bytes corpus must contain 1..64 scenarios"
  let mut identifiers : List String := []
  let mut features : List String := []
  let mut inputs : List String := []
  let mut lengths : List Nat := []
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
    require (!identifiers.contains identifier) ("duplicate malformed-bytes corpus id " ++ identifier)
    identifiers := identifier :: identifiers
    let saved ← entryCase entry fuel
    require ((← MalformedBytes.replayCase saved fuel) == saved) ("malformed-bytes corpus entry did not replay: " ++ identifier)
    let scenario ← MalformedBytes.caseProgram saved
    if !(entry.getObjVal? "generation").isOk then
      require ((← saved.getObjVal? "malformedBytesPlan") == (← entry.getObjVal? "malformedBytesPlan") &&
        (← saved.getObjVal? "transactions") == (← entry.getObjVal? "transactions"))
        ("imported malformed-bytes entry is not canonical: " ++ identifier)
    let caseFeatures := (← (← saved.getObjVal? "provenance").getObjValAs? (List String) "features").eraseDups
    require (sameMembers (← strings entry "expectedFeatures") caseFeatures)
      ("malformed-bytes corpus features changed: " ++ identifier)
    let history := MalformedBytes.observe scenario Solcore.Synthesis.Stateful.StorageExecution.fixtureBindings fuel
    require ((← string history "status") == "complete") ("malformed-bytes corpus history incomplete: " ++ identifier)
    let observed ← history.getObjValAs? (List Json) "transactions"
    let expected ← entry.getObjValAs? (List Json) "expectedHistory"
    require (observed.length == expected.length) ("malformed-bytes expected history length changed: " ++ identifier)
    let mut statuses : List String := []
    for (row, golden) in observed.zip expected do
      let actual := Json.mkObj [("id", ← row.getObjVal? "id"), ("status", ← row.getObjVal? "status"),
        ("output", ← row.getObjVal? "output"), ("committedStorage", ← row.getObjVal? "committedStorage")]
      require (actual == golden)
        ("original Core differs from the expectation without the std wrapper: " ++ identifier ++ " " ++ actual.compress)
      statuses := statuses ++ [← string row "status"]
    transactionTotal := transactionTotal + observed.length
    features := (features ++ caseFeatures).eraseDups
    inputs := (inputs ++ scenario.transactions.flatMap fun tx => chunks tx.payload).eraseDups
    lengths := (lengths ++ scenario.transactions.map (·.payload.length)).eraseDups
    kinds := (kinds ++ scenario.transactions.map (MalformedBytes.kindOf ·.malformation)).eraseDups
    rejections := (rejections ++ scenario.transactions.map fun tx =>
      (MalformedBytes.prescribed tx).map MalformedBytes.selectorText |>.getD "accepted").eraseDups
    helperCounts := (helperCounts ++ [scenario.plan.step.helpers.length]).eraseDups
    transactionCounts := (transactionCounts ++ [scenario.transactions.length]).eraseDups
    templateUnion := (templateUnion ++ (← templates saved)).eraseDups
    outcomes := (outcomes ++ statuses).eraseDups
    patterns := (patterns ++ [String.intercalate "," statuses]).eraseDups
  require (requiredFeatures.all features.contains) "malformed-bytes corpus misses a required step feature"
  require (requiredInputs.all inputs.contains) "malformed-bytes corpus misses a boundary chunk Word"
  require (MalformedBytes.lengthBank.all lengths.contains) "malformed-bytes corpus misses a payload length"
  require (MalformedBytes.malformationKinds.all kinds.contains) "malformed-bytes corpus misses a malformation kind"
  require (outcomeNames.all rejections.contains) "malformed-bytes corpus misses a std outcome"
  require ([1, 2, 3].all helperCounts.contains && [1, 2, 3].all transactionCounts.contains)
    "malformed-bytes corpus misses a helper or transaction count"
  require ([0, 1, 2, 3].all templateUnion.contains) "malformed-bytes corpus misses a generated template"
  require (["returned", "reverted"].all outcomes.contains && requiredPatterns.all patterns.contains)
    "malformed-bytes corpus misses an observed outcome or completion pattern"
  return Json.mkObj [("profile", toJson "stateful-malformed-bytes"), ("scenarios", toJson entries.size),
    ("transactions", toJson transactionTotal), ("malformations", toJson kinds), ("rejections", toJson rejections),
    ("patterns", toJson patterns)]

private def checked {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def rejects {α : Type} (result : Except String α) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "invalid malformed-bytes corpus unexpectedly passed")

def testSourceMalformedBytesCorpus : IO Unit := do
  let manifest ← checked (Json.parse (← IO.FS.readFile "scripts/semantic-malformed-bytes-corpus.json"))
  let summary ← checked (validateManifest manifest)
  let entries ← checked (manifest.getObjValAs? (Array Json) "cases")
  let some first := entries[0]? | throw (IO.userError "missing first malformed-bytes case")
  let some generatedEntry := entries.find? (fun entry => (entry.getObjVal? "generation").isOk) |
    throw (IO.userError "missing generated malformed-bytes case")
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
      ("profile", toJson "stateful-long-bytes"), ("templateVersion", toJson "forged"),
      ("cases", .arr #[]), ("requiredInputs", toJson ([] : List String)),
      ("requiredPayloadLengths", toJson [0, 1, 64]),
      ("requiredHelperCounts", toJson [1, 2]),
      ("requiredMalformations", toJson (["none"] : List String)),
      ("requiredRejections", toJson (["accepted"] : List String)),
      ("requiredCompletionPatterns", toJson (["returned,returned,returned,returned"] : List String))] do
    rejects (validateManifest (manifest.setObjVal! key value))
  rejects (validateManifest manifest 0)
  IO.println summary.compress

end Tests.SourceMalformedBytesCorpus
