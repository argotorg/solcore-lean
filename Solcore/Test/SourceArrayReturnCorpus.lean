import Solcore.Synthesis.Source.ArrayReturnCases

/-! The fixed array-return corpus checks actual original Core histories against
expectations computed without the Core contract: the source model, a slot map
and std's encoder run over the elements' memory, in which each step runs alone
in Core. Coverage describes the checked steps' AST, the inputs, every element
type with every count, each element type's outcomes, the returned `bytes` and
inner lengths, the carries into a returned array from an earlier committed
transaction and past a revert, the node budgets of generated entries and the
completions. Source/Rust/EVM agreement is a separate external validation. -/
set_option autoImplicit false

namespace Tests.SourceArrayReturnCorpus
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
  ("generatorVersion", generatorVersion), ("profileVersion", ArrayReturn.profileVersion),
  ("functionVersion", Solcore.Synthesis.Core.ArrayReturn.version),
  ("templateVersion", ArrayReturn.templateVersion), ("stepProfileVersion", Aggregate.profileVersion),
  ("stepFunctionVersion", Aggregates.version), ("stepTemplateVersion", Aggregate.templateVersion),
  ("emitterVersion", ArrayReturn.emitterVersion), ("wrapperVersion", ArrayReturn.wrapperVersion)]

private def words (values : List Word) : List String := values.map fun value => toString value.val

private def elementNames : List String := ArrayReturn.elementTypes.map (·.name)

/-- Every element type with every count from 0 to 3. -/
def shapeClasses : List String :=
  elementNames.flatMap fun element => (List.range 4).map fun count => s!"{element}:{count}"

/-- Every element type with both outcomes. -/
def outcomeClasses : List String :=
  elementNames.flatMap fun element => ["returned", "reverted"].map fun status => s!"{element}:{status}"

/-- Imported entries are emitted from their saved plan and sequence; generated
entries are regenerated from their seed. Both are checked by full replay. -/
private def entryCase (entry : Json) (fuel : Nat) : Except String Json := do
  if let .ok request := entry.getObjVal? "generation" then
    let some seed := (← request.getObjValAs? String "seed").toNat? | throw "invalid generation seed"
    let corpus := ArrayReturn.generateCases (Seed.ofNat seed) (← request.getObjValAs? Nat "maxProgramNodes") 1 1 fuel
    require ((← string corpus "status") == "complete") "generated entry was excluded"
    let some saved := (← corpus.getObjValAs? (Array Json) "cases")[0]? | throw "generated entry has no case"
    return saved
  let plan ← ArrayReturn.checkedPlan (← entry.getObjVal? "arrayReturnPlan")
  let scenario ← ArrayReturn.checkedScenario plan
    (← ArrayReturn.decodeTransactions plan.shape (← entry.getObjVal? "transactions"))
  ArrayReturn.emitCase scenario (Json.mkObj [("kind", toJson "imported")]) fuel

private def templates (saved : Json) : Except String (List Nat) := do
  let origin ← (← saved.getObjVal? "provenance").getObjVal? "origin"
  if (← string origin "kind") != "array-return-generated" then return []
  let helpers ← (← origin.getObjVal? "stepOrigin").getObjValAs? (List Json) "helpers"
  helpers.mapM fun helper => helper.getObjValAs? Nat "template"

/-- The source model's rows of a scenario, in the corpus's expected-row form. -/
def modelRows (scenario : ArrayReturn.CheckedScenario) (fuel : Nat) : Except String (List Json) := do
  let some rows := Solcore.Synthesis.Stateful.ArrayReturnExecution.model scenario.plan.step fuel
      scenario.plan.shape.element scenario.transactions | throw "the source model failed"
  return (rows.zip scenario.transactions).map fun (row, transaction) => Json.mkObj [
    ("id", toJson transaction.id), ("status", toJson (if row.reverted then "reverted" else "returned")),
    ("output", toJson (Solcore.ContractRuntime.encodeBytesText row.output)),
    ("committedStorage", toJson (row.slots.zipIdx.map fun (value, slot) => Json.mkObj [
      ("slot", toJson (toString slot)), ("value", toJson (toString value.val))]))]

def validateManifest (manifest : Json) (fuel : Nat := 1000000) : Except String Json := do
  require ((← string manifest "schema") == "solcore-lean.semantic-storage-corpus-manifest.v1" &&
    (← string manifest "profile") == "stateful-array-returns" &&
    (← string manifest "coverageKind") == "step-core-ast-features") "unexpected array-return manifest scope"
  for (key, expected) in versions do
    require ((← string manifest key) == expected) ("array-return manifest changed " ++ key)
  let requiredFeatures ← strings manifest "requiredFeatures"
  let requiredInputs ← strings manifest "requiredInputs"
  require (sameMembers requiredInputs (words ArrayReturn.boundaryInputs))
    "array-return corpus must require all six boundary inputs"
  require ((← strings manifest "requiredArrayReturnShapes") == shapeClasses &&
    (← strings manifest "requiredArrayReturnOutcomes") == outcomeClasses)
    "array-return corpus must require every element type with every count and both outcomes"
  require ((← manifest.getObjValAs? (List Nat) "requiredArrayReturnBytesLengths") == ArrayReturn.lengthBank &&
    (← manifest.getObjValAs? (List Nat) "requiredArrayReturnInnerLengths") == [0, 1, 2] &&
    (← manifest.getObjValAs? (List Nat) "requiredArrayReturnNodeBudgets") == [384, 512])
    "array-return corpus must require the bank's bytes lengths, every inner length and both node budgets"
  require ((← strings manifest "requiredArrayReturnCarries") == ["committed", "rollback"])
    "array-return corpus must require carries from a committed transaction and past a revert"
  require ((← manifest.getObjValAs? (List Nat) "requiredHelperCounts") == [1, 2, 3] &&
    (← manifest.getObjValAs? (List Nat) "requiredTransactionCounts") == [1, 2, 3])
    "array-return corpus must require one to three helpers and transactions"
  require ((← (← manifest.getObjVal? "generationRecipeRequirements").getObjValAs? (List Nat) "templates") == [0, 1, 2, 3])
    "array-return corpus must require all four step templates"
  require ((← strings manifest "requiredOutcomes") == ["returned", "reverted"])
    "array-return corpus must require both outcomes"
  let requiredPatterns ← strings manifest "requiredCompletionPatterns"
  require (!requiredPatterns.isEmpty) "array-return corpus must require completion patterns"
  let entries ← manifest.getObjValAs? (Array Json) "cases"
  require (0 < entries.size && entries.size ≤ 64) "array-return corpus must contain 1..64 scenarios"
  let mut identifiers : List String := []
  let mut features : List String := []
  let mut inputs : List String := []
  let mut shapes : List String := []
  let mut outcomesByElement : List String := []
  let mut bytesLengths : List Nat := []
  let mut innerLengths : List Nat := []
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
    require (!identifiers.contains identifier) ("duplicate array-return corpus id " ++ identifier)
    identifiers := identifier :: identifiers
    let saved ← entryCase entry fuel
    require ((← ArrayReturn.replayCase saved fuel) == saved) ("array-return corpus entry did not replay: " ++ identifier)
    let scenario ← ArrayReturn.caseProgram saved
    if let .ok request := entry.getObjVal? "generation" then
      budgets := (budgets ++ [← request.getObjValAs? Nat "maxProgramNodes"]).eraseDups
    else
      require ((← saved.getObjVal? "arrayReturnPlan") == (← entry.getObjVal? "arrayReturnPlan") &&
        (← saved.getObjVal? "transactions") == (← entry.getObjVal? "transactions"))
        ("imported array-return entry is not canonical: " ++ identifier)
    let caseFeatures := (← (← saved.getObjVal? "provenance").getObjValAs? (List String) "features").eraseDups
    require (sameMembers (← strings entry "expectedFeatures") caseFeatures)
      ("array-return corpus features changed: " ++ identifier)
    let expected ← entry.getObjValAs? (List Json) "expectedHistory"
    require (expected == (← modelRows scenario fuel))
      ("the expected history differs from the source model: " ++ identifier)
    let history := ArrayReturn.observe scenario Solcore.Synthesis.Stateful.StorageExecution.fixtureBindings fuel
    require ((← string history "status") == "complete") ("array-return corpus history incomplete: " ++ identifier)
    let observed ← history.getObjValAs? (List Json) "transactions"
    require (observed.length == expected.length) ("array-return expected history length changed: " ++ identifier)
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
    let shape := scenario.plan.shape
    for status in statuses do
      outcomesByElement := (outcomesByElement ++ [s!"{shape.element.name}:{status}"]).eraseDups
    if statuses.contains "returned" then
      shapes := (shapes ++ [s!"{shape.element.name}:{shape.count}"]).eraseDups
      if shape.element == .bytes then bytesLengths := (bytesLengths ++ shape.lengths).eraseDups
      if shape.element == .nested then innerLengths := (innerLengths ++ shape.lengths).eraseDups
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
  require (requiredFeatures.all features.contains) "array-return corpus misses a required step feature"
  require (requiredInputs.all inputs.contains) "array-return corpus misses a boundary input"
  require (shapeClasses.all shapes.contains && outcomeClasses.all outcomesByElement.contains)
    "array-return corpus misses a returned element type and count, or an element type's outcome"
  require (ArrayReturn.lengthBank.all bytesLengths.contains && [0, 1, 2].all innerLengths.contains)
    "array-return corpus misses a returned bytes length or inner length"
  require (["committed", "rollback"].all carries.contains && [384, 512].all budgets.contains)
    "array-return corpus misses a carry or a node budget"
  require ([1, 2, 3].all helperCounts.contains && [1, 2, 3].all transactionCounts.contains)
    "array-return corpus misses a helper or transaction count"
  require ([0, 1, 2, 3].all templateUnion.contains) "array-return corpus misses a generated template"
  require (["returned", "reverted"].all outcomes.contains && requiredPatterns.all patterns.contains)
    "array-return corpus misses an observed outcome or completion pattern"
  return Json.mkObj [("profile", toJson "stateful-array-returns"), ("scenarios", toJson entries.size),
    ("transactions", toJson transactionTotal), ("shapes", toJson shapes),
    ("bytesLengths", toJson bytesLengths), ("innerLengths", toJson innerLengths), ("carries", toJson carries),
    ("nodeBudgets", toJson budgets), ("patterns", toJson patterns)]

private def checked {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def rejects {α : Type} (result : Except String α) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "invalid array-return corpus unexpectedly passed")

def testSourceArrayReturnCorpus : IO Unit := do
  let manifest ← checked (Json.parse (← IO.FS.readFile "scripts/semantic-array-return-corpus.json"))
  let summary ← checked (validateManifest manifest)
  let entries ← checked (manifest.getObjValAs? (Array Json) "cases")
  let some generatedEntry := entries.find? (fun entry => (entry.getObjVal? "generation").isOk) |
    throw (IO.userError "missing generated array-return case")
  -- An imported `bytes` entry whose first transaction returns a partial last
  -- Word.
  let some first := entries.find? (fun entry => (entry.getObjVal? "arrayReturnPlan").toOption.any (fun plan =>
      (plan.getObjValAs? String "elements").toOption == some "bytes" &&
        (plan.getObjValAs? (List Nat) "lengths").toOption.any (·.any (· % 32 != 0))) &&
      (entry.getObjValAs? (Array Json) "expectedHistory").toOption.any (fun history =>
        history[0]?.any (fun row => (row.getObjValAs? String "status").toOption == some "returned"))) |
    throw (IO.userError "missing imported bytes case")
  let replace := fun (original changed : Json) => manifest.setObjVal! "cases"
    (.arr (entries.map fun entry => if entry == original then changed else entry))
  let history ← checked (first.getObjValAs? (Array Json) "expectedHistory")
  -- A changed head Word, a nonzero padding byte, a shorter output, a slot, a
  -- missing row and a status are all checked.
  let row := history[0]!
  let output ← checked (row.getObjValAs? String "output")
  let changedHead := row.setObjVal! "output" (toJson ("0x" ++ String.ofList (List.replicate 64 'f') ++ output.drop 66))
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr (history.set! 0 changedHead)))))
  let changedPadding := row.setObjVal! "output" (toJson (String.ofList (output.toList.take (output.length - 2)) ++
    (if output.endsWith "01" then "02" else "01")))
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr (history.set! 0 changedPadding)))))
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
  -- A transaction's choice and length are checked against its calldata and
  -- the plan's shape, and the plan's shape against every transaction.
  let transactions ← checked (first.getObjValAs? (Array Json) "transactions")
  let length ← checked (transactions[0]!.getObjValAs? String "length")
  rejects (validateManifest (replace first (first.setObjVal! "transactions" (.arr (transactions.set! 0
    (transactions[0]!.setObjVal! "length" (toJson (if length == "1" then "2" else "1"))))))))
  let flags ← checked (transactions[0]!.getObjValAs? String "flags")
  let input ← checked (transactions[0]!.getObjValAs? String "input")
  let choice ← checked (transactions[0]!.getObjValAs? String "choice")
  let some flagsValue := flags.toNat? | throw (IO.userError "invalid flags")
  let some inputValue := input.toNat? | throw (IO.userError "invalid input")
  let some choiceValue := choice.toNat? | throw (IO.userError "invalid choice")
  let some lengthValue := length.toNat? | throw (IO.userError "invalid length")
  let otherChoice := transactions[0]!.setObjVal! "choice" (toJson (toString (choiceValue + 1))) |>.setObjVal! "calldata"
    (toJson (Solcore.Synthesis.Stateful.ArrayReturnExecution.calldata (Word.ofNatModulo flagsValue)
      (Word.ofNatModulo inputValue) (Word.ofNatModulo (choiceValue + 1)) (Word.ofNatModulo lengthValue)))
  rejects (validateManifest (replace first (first.setObjVal! "transactions" (.arr (transactions.set! 0 otherChoice)))))
  let plan ← checked (first.getObjVal? "arrayReturnPlan")
  let count ← checked (plan.getObjValAs? Nat "count")
  let lengths ← checked (plan.getObjValAs? (List Nat) "lengths")
  rejects (validateManifest (replace first (first.setObjVal! "arrayReturnPlan" (plan.setObjVal! "count" (toJson (count - 1))
    |>.setObjVal! "lengths" (toJson lengths.dropLast)))))
  rejects (validateManifest (replace first (first.setObjVal! "expectedFeatures" (toJson ([] : List String)))))
  rejects (validateManifest (manifest.setObjVal! "cases" (.arr (entries.push first))))
  for (key, value) in [
      ("profile", toJson "stateful-storage"), ("templateVersion", toJson "forged"),
      ("cases", .arr #[]), ("requiredInputs", toJson ([] : List String)),
      ("requiredArrayReturnShapes", toJson (["uint256:0"] : List String)),
      ("requiredArrayReturnOutcomes", toJson (["uint256:returned"] : List String)),
      ("requiredArrayReturnBytesLengths", toJson [0, 1, 32]), ("requiredArrayReturnInnerLengths", toJson [0, 1]),
      ("requiredArrayReturnNodeBudgets", toJson [384]),
      ("requiredArrayReturnCarries", toJson (["committed"] : List String)),
      ("requiredHelperCounts", toJson [1, 2]),
      ("requiredCompletionPatterns", toJson (["returned,returned,returned,returned"] : List String))] do
    rejects (validateManifest (manifest.setObjVal! key value))
  rejects (validateManifest manifest 0)
  IO.println summary.compress

end Tests.SourceArrayReturnCorpus
