import Solcore.Synthesis.Source.BytesReturnCases

/-! The fixed bytes-return corpus checks actual original Core histories against
expectations computed without the Core contract: the source model, a slot map
and std's encoder, in which each step runs alone in Core. Coverage describes
the checked steps' AST, the inputs, the returned lengths, the length classes'
outcomes, the carries into a returned value from an earlier committed
transaction and past a revert, the node budgets of generated entries and the
completions. Source/Rust/EVM agreement is a separate external validation. -/
set_option autoImplicit false

namespace Tests.SourceBytesReturnCorpus
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
  ("generatorVersion", generatorVersion), ("profileVersion", BytesReturn.profileVersion),
  ("functionVersion", Solcore.Synthesis.Core.BytesReturn.version),
  ("templateVersion", BytesReturn.templateVersion), ("stepProfileVersion", Aggregate.profileVersion),
  ("stepFunctionVersion", Aggregates.version), ("stepTemplateVersion", Aggregate.templateVersion),
  ("emitterVersion", BytesReturn.emitterVersion), ("wrapperVersion", BytesReturn.wrapperVersion)]

private def words (values : List Word) : List String := values.map fun value => toString value.val

/-- Empty, a partial last Word, or whole Words. -/
def lengthClass (length : Nat) : String :=
  if length == 0 then "empty" else if length % 32 == 0 then "whole" else "partial"

private def lengthOutcomes : List String :=
  ["empty", "partial", "whole"].flatMap fun kind => ["returned", "reverted"].map fun status => s!"{kind}:{status}"

/-- Imported entries are emitted from their saved plan and sequence; generated
entries are regenerated from their seed. Both are checked by full replay. -/
private def entryCase (entry : Json) (fuel : Nat) : Except String Json := do
  if let .ok request := entry.getObjVal? "generation" then
    let some seed := (← request.getObjValAs? String "seed").toNat? | throw "invalid generation seed"
    let corpus := BytesReturn.generateCases (Seed.ofNat seed) (← request.getObjValAs? Nat "maxProgramNodes") 1 1 fuel
    require ((← string corpus "status") == "complete") "generated entry was excluded"
    let some saved := (← corpus.getObjValAs? (Array Json) "cases")[0]? | throw "generated entry has no case"
    return saved
  let plan ← BytesReturn.checkedPlan (← entry.getObjVal? "bytesReturnPlan")
  let scenario ← BytesReturn.checkedScenario plan (← BytesReturn.decodeTransactions (← entry.getObjVal? "transactions"))
  BytesReturn.emitCase scenario (Json.mkObj [("kind", toJson "imported")]) fuel

private def templates (saved : Json) : Except String (List Nat) := do
  let origin ← (← saved.getObjVal? "provenance").getObjVal? "origin"
  if (← string origin "kind") != "bytes-return-generated" then return []
  let helpers ← (← origin.getObjVal? "stepOrigin").getObjValAs? (List Json) "helpers"
  helpers.mapM fun helper => helper.getObjValAs? Nat "template"

/-- The source model's rows of a scenario, in the corpus's expected-row form. -/
def modelRows (scenario : BytesReturn.CheckedScenario) (fuel : Nat) : Except String (List Json) := do
  let some rows := Solcore.Synthesis.Stateful.BytesReturnExecution.model scenario.plan.step fuel
      scenario.transactions | throw "the source model failed"
  return (rows.zip scenario.transactions).map fun (row, transaction) => Json.mkObj [
    ("id", toJson transaction.id), ("status", toJson (if row.reverted then "reverted" else "returned")),
    ("output", toJson (Solcore.ContractRuntime.encodeBytesText row.output)),
    ("committedStorage", toJson (row.slots.zipIdx.map fun (value, slot) => Json.mkObj [
      ("slot", toJson (toString slot)), ("value", toJson (toString value.val))]))]

def validateManifest (manifest : Json) (fuel : Nat := 1000000) : Except String Json := do
  require ((← string manifest "schema") == "solcore-lean.semantic-storage-corpus-manifest.v1" &&
    (← string manifest "profile") == "stateful-bytes-returns" &&
    (← string manifest "coverageKind") == "step-core-ast-features") "unexpected bytes-return manifest scope"
  for (key, expected) in versions do
    require ((← string manifest key) == expected) ("bytes-return manifest changed " ++ key)
  let requiredFeatures ← strings manifest "requiredFeatures"
  let requiredInputs ← strings manifest "requiredInputs"
  require (sameMembers requiredInputs (words BytesReturn.boundaryInputs))
    "bytes-return corpus must require all six boundary inputs"
  require ((← manifest.getObjValAs? (List Nat) "requiredReturnedLengths") == BytesReturn.lengthBank &&
    (← strings manifest "requiredLengthOutcomes") == lengthOutcomes &&
    (← manifest.getObjValAs? (List Nat) "requiredReturnNodeBudgets") == [384, 512])
    "bytes-return corpus must require the bank's returned lengths, every length class with both outcomes and both node budgets"
  require ((← strings manifest "requiredReturnCarries") == ["committed", "rollback"])
    "bytes-return corpus must require carries from a committed transaction and past a revert"
  require ((← manifest.getObjValAs? (List Nat) "requiredHelperCounts") == [1, 2, 3] &&
    (← manifest.getObjValAs? (List Nat) "requiredTransactionCounts") == [1, 2, 3])
    "bytes-return corpus must require one to three helpers and transactions"
  require ((← (← manifest.getObjVal? "generationRecipeRequirements").getObjValAs? (List Nat) "templates") == [0, 1, 2, 3])
    "bytes-return corpus must require all four step templates"
  require ((← strings manifest "requiredOutcomes") == ["returned", "reverted"])
    "bytes-return corpus must require both outcomes"
  let requiredPatterns ← strings manifest "requiredCompletionPatterns"
  require (!requiredPatterns.isEmpty) "bytes-return corpus must require completion patterns"
  let entries ← manifest.getObjValAs? (Array Json) "cases"
  require (0 < entries.size && entries.size ≤ 64) "bytes-return corpus must contain 1..64 scenarios"
  let mut identifiers : List String := []
  let mut features : List String := []
  let mut inputs : List String := []
  let mut returnedLengths : List Nat := []
  let mut outcomesByClass : List String := []
  let mut carries : List String := []
  let mut budgets : List Nat := []
  let mut helperCounts : List Nat := []
  let mut transactionCounts : List Nat := []
  let mut templateUnion : List Nat := []
  let mut outcomes : List String := []
  let mut patterns : List String := []
  let mut transactionTotal := 0
  for entry in entries do
    let identifier ← string entry "id"
    require (!identifiers.contains identifier) ("duplicate bytes-return corpus id " ++ identifier)
    identifiers := identifier :: identifiers
    let saved ← entryCase entry fuel
    require ((← BytesReturn.replayCase saved fuel) == saved) ("bytes-return corpus entry did not replay: " ++ identifier)
    let scenario ← BytesReturn.caseProgram saved
    if let .ok request := entry.getObjVal? "generation" then
      budgets := (budgets ++ [← request.getObjValAs? Nat "maxProgramNodes"]).eraseDups
    else
      require ((← saved.getObjVal? "bytesReturnPlan") == (← entry.getObjVal? "bytesReturnPlan") &&
        (← saved.getObjVal? "transactions") == (← entry.getObjVal? "transactions"))
        ("imported bytes-return entry is not canonical: " ++ identifier)
    let caseFeatures := (← (← saved.getObjVal? "provenance").getObjValAs? (List String) "features").eraseDups
    require (sameMembers (← strings entry "expectedFeatures") caseFeatures)
      ("bytes-return corpus features changed: " ++ identifier)
    let expected ← entry.getObjValAs? (List Json) "expectedHistory"
    require (expected == (← modelRows scenario fuel))
      ("the expected history differs from the source model: " ++ identifier)
    let history := BytesReturn.observe scenario Solcore.Synthesis.Stateful.StorageExecution.fixtureBindings fuel
    require ((← string history "status") == "complete") ("bytes-return corpus history incomplete: " ++ identifier)
    let observed ← history.getObjValAs? (List Json) "transactions"
    require (observed.length == expected.length) ("bytes-return expected history length changed: " ++ identifier)
    let mut statuses : List String := []
    for (row, golden) in observed.zip expected do
      let actual := Json.mkObj [("id", ← row.getObjVal? "id"), ("status", ← row.getObjVal? "status"),
        ("output", ← row.getObjVal? "output"), ("committedStorage", ← row.getObjVal? "committedStorage")]
      require (actual == golden)
        ("original Core differs from the source model: " ++ identifier ++ " " ++ actual.compress)
      statuses := statuses ++ [← string row "status"]
    transactionTotal := transactionTotal + observed.length
    features := (features ++ caseFeatures).eraseDups
    inputs := (inputs ++ words (scenario.transactions.map (·.input))).eraseDups
    for (status, transaction) in statuses.zip scenario.transactions do
      let length := transaction.length.val
      if status == "returned" then
        returnedLengths := (returnedLengths ++ [length]).eraseDups
      outcomesByClass := (outcomesByClass ++ [s!"{lengthClass length}:{status}"]).eraseDups
    for (status, index) in statuses.zipIdx do
      if status == "returned" && (statuses.take index).contains "returned" then
        carries := (carries ++ ["committed"]).eraseDups
      if status == "returned" && (statuses.take index).contains "reverted" then
        carries := (carries ++ ["rollback"]).eraseDups
    helperCounts := (helperCounts ++ [scenario.plan.step.helpers.length]).eraseDups
    transactionCounts := (transactionCounts ++ [scenario.transactions.length]).eraseDups
    templateUnion := (templateUnion ++ (← templates saved)).eraseDups
    outcomes := (outcomes ++ statuses).eraseDups
    patterns := (patterns ++ [String.intercalate "," statuses]).eraseDups
  require (requiredFeatures.all features.contains) "bytes-return corpus misses a required step feature"
  require (requiredInputs.all inputs.contains) "bytes-return corpus misses a boundary input"
  require (BytesReturn.lengthBank.all returnedLengths.contains && lengthOutcomes.all outcomesByClass.contains)
    "bytes-return corpus misses a returned length or a length class's outcome"
  require (["committed", "rollback"].all carries.contains && [384, 512].all budgets.contains)
    "bytes-return corpus misses a carry or a node budget"
  require ([1, 2, 3].all helperCounts.contains && [1, 2, 3].all transactionCounts.contains)
    "bytes-return corpus misses a helper or transaction count"
  require ([0, 1, 2, 3].all templateUnion.contains) "bytes-return corpus misses a generated template"
  require (["returned", "reverted"].all outcomes.contains && requiredPatterns.all patterns.contains)
    "bytes-return corpus misses an observed outcome or completion pattern"
  return Json.mkObj [("profile", toJson "stateful-bytes-returns"), ("scenarios", toJson entries.size),
    ("transactions", toJson transactionTotal), ("returnedLengths", toJson returnedLengths),
    ("lengthOutcomes", toJson outcomesByClass), ("carries", toJson carries), ("nodeBudgets", toJson budgets),
    ("patterns", toJson patterns)]

private def checked {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def rejects {α : Type} (result : Except String α) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "invalid bytes-return corpus unexpectedly passed")

def testSourceBytesReturnCorpus : IO Unit := do
  let manifest ← checked (Json.parse (← IO.FS.readFile "scripts/semantic-bytes-return-corpus.json"))
  let summary ← checked (validateManifest manifest)
  let entries ← checked (manifest.getObjValAs? (Array Json) "cases")
  let some first := entries[0]? | throw (IO.userError "missing first bytes-return case")
  let some generatedEntry := entries.find? (fun entry => (entry.getObjVal? "generation").isOk) |
    throw (IO.userError "missing generated bytes-return case")
  let replace := fun (original changed : Json) => manifest.setObjVal! "cases"
    (.arr (entries.map fun entry => if entry == original then changed else entry))
  let history ← checked (first.getObjValAs? (Array Json) "expectedHistory")
  -- A changed head Word, a nonzero padding byte, a shorter output, a slot, a
  -- missing row and a status are all checked.
  let returnedIndex := (history.findIdx? fun row => (row.getObjValAs? String "status").toOption == some "returned").getD 0
  let row := history[returnedIndex]!
  let output ← checked (row.getObjValAs? String "output")
  let changedHead := row.setObjVal! "output" (toJson ("0x" ++ String.ofList (List.replicate 64 'f') ++ output.drop 66))
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr (history.set! returnedIndex changedHead)))))
  let changedPadding := row.setObjVal! "output" (toJson (String.ofList (output.toList.take (output.length - 2)) ++
    (if output.endsWith "01" then "02" else "01")))
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr (history.set! returnedIndex changedPadding)))))
  let shorterOutput := row.setObjVal! "output" (toJson (String.ofList (output.toList.take (output.length - 64))))
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr (history.set! returnedIndex shorterOutput)))))
  let storage ← checked (row.getObjValAs? (Array Json) "committedStorage")
  let slotTwo := (storage[2]!.getObjValAs? String "value").toOption
  let changedSlot := row.setObjVal! "committedStorage" (.arr (storage.set! 2
    (storage[2]!.setObjVal! "value" (toJson (if slotTwo == some "7" then "8" else "7")))))
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr (history.set! returnedIndex changedSlot)))))
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr (history.pop)))))
  let generatedHistory ← checked (generatedEntry.getObjValAs? (Array Json) "expectedHistory")
  let flipped := if (generatedHistory[0]!.getObjValAs? String "status").toOption == some "returned" then "reverted" else "returned"
  rejects (validateManifest (replace generatedEntry (generatedEntry.setObjVal! "expectedHistory"
    (.arr (generatedHistory.set! 0 (generatedHistory[0]!.setObjVal! "status" (toJson flipped)))))))
  -- A transaction's length is checked against its calldata and the bound.
  let transactions ← checked (first.getObjValAs? (Array Json) "transactions")
  let length ← checked (transactions[0]!.getObjValAs? String "length")
  rejects (validateManifest (replace first (first.setObjVal! "transactions" (.arr (transactions.set! 0
    (transactions[0]!.setObjVal! "length" (toJson (if length == "1" then "2" else "1"))))))))
  rejects (BytesReturn.decodeTransactions (toJson [Json.mkObj [
    ("id", toJson "tx-0"), ("flags", toJson "0"), ("input", toJson "0"), ("length", toJson "65"),
    ("calldata", toJson (Solcore.Synthesis.Stateful.BytesReturnExecution.calldata (Word.ofNatModulo 0)
      (Word.ofNatModulo 0) (Word.ofNatModulo 65))), ("value", toJson "0")]]))
  rejects (validateManifest (replace first (first.setObjVal! "expectedFeatures" (toJson ([] : List String)))))
  rejects (validateManifest (manifest.setObjVal! "cases" (.arr (entries.push first))))
  for (key, value) in [
      ("profile", toJson "stateful-storage"), ("templateVersion", toJson "forged"),
      ("cases", .arr #[]), ("requiredInputs", toJson ([] : List String)),
      ("requiredReturnedLengths", toJson [0, 1, 32]),
      ("requiredLengthOutcomes", toJson (["empty:returned"] : List String)),
      ("requiredReturnNodeBudgets", toJson [384]), ("requiredReturnCarries", toJson (["committed"] : List String)),
      ("requiredHelperCounts", toJson [1, 2]),
      ("requiredCompletionPatterns", toJson (["returned,returned,returned,returned"] : List String))] do
    rejects (validateManifest (manifest.setObjVal! key value))
  rejects (validateManifest manifest 0)
  IO.println summary.compress

end Tests.SourceBytesReturnCorpus
