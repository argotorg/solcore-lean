import Solcore.Synthesis.Source.TupleReturnCases

/-! The fixed tuple-return corpus checks actual original Core histories against
expectations computed without the Core contract: the source model, a slot map
in which each step runs alone in Core. Coverage describes the checked steps'
AST, the inputs, the arities and each arity's outcomes, the carries into a
returned tuple from an earlier committed transaction and past a revert, the
node budgets of generated entries and the completions. Source/Rust/EVM
agreement is a separate external validation. -/
set_option autoImplicit false

namespace Tests.SourceTupleReturnCorpus
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
  ("generatorVersion", generatorVersion), ("profileVersion", TupleReturn.profileVersion),
  ("functionVersion", Solcore.Synthesis.Core.TupleReturn.version),
  ("templateVersion", TupleReturn.templateVersion), ("stepProfileVersion", Aggregate.profileVersion),
  ("stepFunctionVersion", Aggregates.version), ("stepTemplateVersion", Aggregate.templateVersion),
  ("emitterVersion", TupleReturn.emitterVersion), ("wrapperVersion", TupleReturn.wrapperVersion)]

private def words (values : List Word) : List String := values.map fun value => toString value.val

private def arityOutcomes : List String :=
  [2, 3, 4].flatMap fun arity => ["returned", "reverted"].map fun status => s!"{arity}:{status}"

/-- Imported entries are emitted from their saved plan and sequence; generated
entries are regenerated from their seed. Both are checked by full replay. -/
private def entryCase (entry : Json) (fuel : Nat) : Except String Json := do
  if let .ok request := entry.getObjVal? "generation" then
    let some seed := (← request.getObjValAs? String "seed").toNat? | throw "invalid generation seed"
    let corpus := TupleReturn.generateCases (Seed.ofNat seed) (← request.getObjValAs? Nat "maxProgramNodes") 1 1 fuel
    require ((← string corpus "status") == "complete") "generated entry was excluded"
    let some saved := (← corpus.getObjValAs? (Array Json) "cases")[0]? | throw "generated entry has no case"
    return saved
  let plan ← TupleReturn.checkedPlan (← entry.getObjVal? "tupleReturnPlan")
  let scenario ← TupleReturn.checkedScenario plan (← TupleReturn.decodeTransactions (← entry.getObjVal? "transactions"))
  TupleReturn.emitCase scenario (Json.mkObj [("kind", toJson "imported")]) fuel

private def templates (saved : Json) : Except String (List Nat) := do
  let origin ← (← saved.getObjVal? "provenance").getObjVal? "origin"
  if (← string origin "kind") != "tuple-return-generated" then return []
  let helpers ← (← origin.getObjVal? "stepOrigin").getObjValAs? (List Json) "helpers"
  helpers.mapM fun helper => helper.getObjValAs? Nat "template"

/-- The source model's rows of a scenario, in the corpus's expected-row form. -/
private def modelRows (scenario : TupleReturn.CheckedScenario) (fuel : Nat) : Except String (List Json) := do
  let some rows := Solcore.Synthesis.Stateful.TupleReturnExecution.model scenario.plan.step fuel
      scenario.plan.arity scenario.transactions | throw "the source model failed"
  return (rows.zip scenario.transactions).map fun (row, transaction) => Json.mkObj [
    ("id", toJson transaction.id), ("status", toJson (if row.reverted then "reverted" else "returned")),
    ("output", toJson (Solcore.ContractRuntime.encodeBytesText
      (Solcore.Synthesis.Stateful.TupleReturnExecution.outputBytes row))),
    ("committedStorage", toJson (row.slots.zipIdx.map fun (value, slot) => Json.mkObj [
      ("slot", toJson (toString slot)), ("value", toJson (toString value.val))]))]

def validateManifest (manifest : Json) (fuel : Nat := 1000000) : Except String Json := do
  require ((← string manifest "schema") == "solcore-lean.semantic-storage-corpus-manifest.v1" &&
    (← string manifest "profile") == "stateful-tuple-returns" &&
    (← string manifest "coverageKind") == "step-core-ast-features") "unexpected tuple-return manifest scope"
  for (key, expected) in versions do
    require ((← string manifest key) == expected) ("tuple-return manifest changed " ++ key)
  let requiredFeatures ← strings manifest "requiredFeatures"
  let requiredInputs ← strings manifest "requiredInputs"
  require (sameMembers requiredInputs (words TupleReturn.boundaryInputs))
    "tuple-return corpus must require all six boundary inputs"
  require ((← manifest.getObjValAs? (List Nat) "requiredTupleArities") == [2, 3, 4] &&
    (← strings manifest "requiredArityOutcomes") == arityOutcomes &&
    (← manifest.getObjValAs? (List Nat) "requiredNodeBudgets") == [384, 512])
    "tuple-return corpus must require every arity with both outcomes and both node budgets"
  require ((← strings manifest "requiredTupleCarries") == ["committed", "rollback"])
    "tuple-return corpus must require carries from a committed transaction and past a revert"
  require ((← manifest.getObjValAs? (List Nat) "requiredHelperCounts") == [1, 2, 3] &&
    (← manifest.getObjValAs? (List Nat) "requiredTransactionCounts") == [1, 2, 3])
    "tuple-return corpus must require one to three helpers and transactions"
  require ((← (← manifest.getObjVal? "generationRecipeRequirements").getObjValAs? (List Nat) "templates") == [0, 1, 2, 3])
    "tuple-return corpus must require all four step templates"
  require ((← strings manifest "requiredOutcomes") == ["returned", "reverted"])
    "tuple-return corpus must require both outcomes"
  let requiredPatterns ← strings manifest "requiredCompletionPatterns"
  require (!requiredPatterns.isEmpty) "tuple-return corpus must require completion patterns"
  let entries ← manifest.getObjValAs? (Array Json) "cases"
  require (0 < entries.size && entries.size ≤ 64) "tuple-return corpus must contain 1..64 scenarios"
  let mut identifiers : List String := []
  let mut features : List String := []
  let mut inputs : List String := []
  let mut arities : List Nat := []
  let mut outcomesByArity : List String := []
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
    require (!identifiers.contains identifier) ("duplicate tuple-return corpus id " ++ identifier)
    identifiers := identifier :: identifiers
    let saved ← entryCase entry fuel
    require ((← TupleReturn.replayCase saved fuel) == saved) ("tuple-return corpus entry did not replay: " ++ identifier)
    let scenario ← TupleReturn.caseProgram saved
    if let .ok request := entry.getObjVal? "generation" then
      budgets := (budgets ++ [← request.getObjValAs? Nat "maxProgramNodes"]).eraseDups
    else
      require ((← saved.getObjVal? "tupleReturnPlan") == (← entry.getObjVal? "tupleReturnPlan") &&
        (← saved.getObjVal? "transactions") == (← entry.getObjVal? "transactions"))
        ("imported tuple-return entry is not canonical: " ++ identifier)
    let caseFeatures := (← (← saved.getObjVal? "provenance").getObjValAs? (List String) "features").eraseDups
    require (sameMembers (← strings entry "expectedFeatures") caseFeatures)
      ("tuple-return corpus features changed: " ++ identifier)
    let expected ← entry.getObjValAs? (List Json) "expectedHistory"
    require (expected == (← modelRows scenario fuel))
      ("the expected history differs from the source model: " ++ identifier)
    let history := TupleReturn.observe scenario Solcore.Synthesis.Stateful.StorageExecution.fixtureBindings fuel
    require ((← string history "status") == "complete") ("tuple-return corpus history incomplete: " ++ identifier)
    let observed ← history.getObjValAs? (List Json) "transactions"
    require (observed.length == expected.length) ("tuple-return expected history length changed: " ++ identifier)
    let mut statuses : List String := []
    for (row, golden) in observed.zip expected do
      let actual := Json.mkObj [("id", ← row.getObjVal? "id"), ("status", ← row.getObjVal? "status"),
        ("output", ← row.getObjVal? "output"), ("committedStorage", ← row.getObjVal? "committedStorage")]
      require (actual == golden)
        ("original Core differs from the source model: " ++ identifier ++ " " ++ actual.compress)
      statuses := statuses ++ [← string row "status"]
    let arity := scenario.plan.arity
    transactionTotal := transactionTotal + observed.length
    features := (features ++ caseFeatures).eraseDups
    inputs := (inputs ++ words (scenario.transactions.map (·.input))).eraseDups
    arities := (arities ++ [arity]).eraseDups
    outcomesByArity := (outcomesByArity ++ statuses.map fun status => s!"{arity}:{status}").eraseDups
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
  require (requiredFeatures.all features.contains) "tuple-return corpus misses a required step feature"
  require (requiredInputs.all inputs.contains) "tuple-return corpus misses a boundary input"
  require ([2, 3, 4].all arities.contains && arityOutcomes.all outcomesByArity.contains)
    "tuple-return corpus misses an arity or an arity's outcome"
  require (["committed", "rollback"].all carries.contains && [384, 512].all budgets.contains)
    "tuple-return corpus misses a carry or a node budget"
  require ([1, 2, 3].all helperCounts.contains && [1, 2, 3].all transactionCounts.contains)
    "tuple-return corpus misses a helper or transaction count"
  require ([0, 1, 2, 3].all templateUnion.contains) "tuple-return corpus misses a generated template"
  require (["returned", "reverted"].all outcomes.contains && requiredPatterns.all patterns.contains)
    "tuple-return corpus misses an observed outcome or completion pattern"
  return Json.mkObj [("profile", toJson "stateful-tuple-returns"), ("scenarios", toJson entries.size),
    ("transactions", toJson transactionTotal), ("arities", toJson arities), ("arityOutcomes", toJson outcomesByArity),
    ("carries", toJson carries), ("nodeBudgets", toJson budgets), ("patterns", toJson patterns)]

private def checked {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def rejects {α : Type} (result : Except String α) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "invalid tuple-return corpus unexpectedly passed")

def testSourceTupleReturnCorpus : IO Unit := do
  let manifest ← checked (Json.parse (← IO.FS.readFile "scripts/semantic-tuple-return-corpus.json"))
  let summary ← checked (validateManifest manifest)
  let entries ← checked (manifest.getObjValAs? (Array Json) "cases")
  let some first := entries[0]? | throw (IO.userError "missing first tuple-return case")
  let some generatedEntry := entries.find? (fun entry => (entry.getObjVal? "generation").isOk) |
    throw (IO.userError "missing generated tuple-return case")
  let replace := fun (original changed : Json) => manifest.setObjVal! "cases"
    (.arr (entries.map fun entry => if entry == original then changed else entry))
  let history ← checked (first.getObjValAs? (Array Json) "expectedHistory")
  let row := history[0]!
  -- An output, a shorter output, a slot, a missing row and a status are all checked.
  let output ← checked (row.getObjValAs? String "output")
  let changedOutput := row.setObjVal! "output" (toJson ("0x" ++ String.ofList (List.replicate 64 'f') ++ output.drop 66))
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr (history.set! 0 changedOutput)))))
  let shorterOutput := row.setObjVal! "output" (toJson (String.ofList (output.toList.take (output.length - 64))))
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr (history.set! 0 shorterOutput)))))
  let storage ← checked (row.getObjValAs? (Array Json) "committedStorage")
  let slotTwo := (storage[2]!.getObjValAs? String "value").toOption
  let changedSlot := row.setObjVal! "committedStorage" (.arr (storage.set! 2
    (storage[2]!.setObjVal! "value" (toJson (if slotTwo == some "7" then "8" else "7")))))
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr (history.set! 0 changedSlot)))))
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr (history.pop)))))
  let generatedHistory ← checked (generatedEntry.getObjValAs? (Array Json) "expectedHistory")
  let flipped := if (generatedHistory[0]!.getObjValAs? String "status").toOption == some "returned" then "reverted" else "returned"
  rejects (validateManifest (replace generatedEntry (generatedEntry.setObjVal! "expectedHistory"
    (.arr (generatedHistory.set! 0 (generatedHistory[0]!.setObjVal! "status" (toJson flipped)))))))
  -- The plan's arity is checked.
  let plan ← checked (first.getObjVal? "tupleReturnPlan")
  let arity ← checked (plan.getObjValAs? Nat "arity")
  rejects (validateManifest (replace first (first.setObjVal! "tupleReturnPlan"
    (plan.setObjVal! "arity" (toJson (if arity == 2 then 3 else 2))))))
  rejects (validateManifest (replace first (first.setObjVal! "expectedFeatures" (toJson ([] : List String)))))
  rejects (validateManifest (manifest.setObjVal! "cases" (.arr (entries.push first))))
  for (key, value) in [
      ("profile", toJson "stateful-storage"), ("templateVersion", toJson "forged"),
      ("cases", .arr #[]), ("requiredInputs", toJson ([] : List String)),
      ("requiredTupleArities", toJson [2, 3]), ("requiredArityOutcomes", toJson (["2:returned"] : List String)),
      ("requiredNodeBudgets", toJson [384]), ("requiredTupleCarries", toJson (["committed"] : List String)),
      ("requiredHelperCounts", toJson [1, 2]),
      ("requiredCompletionPatterns", toJson (["returned,returned,returned,returned"] : List String))] do
    rejects (validateManifest (manifest.setObjVal! key value))
  rejects (validateManifest manifest 0)
  IO.println summary.compress

end Tests.SourceTupleReturnCorpus
