import Solcore.Synthesis.Source.MethodsCases

/-! The fixed several-methods corpus checks actual original Core histories
against expectations computed without the std-modeling wrapper: the byte-level
dispatch picks the method or the rejection, the method's step runs alone in
Core and the protocol's slot arithmetic is written out. Coverage describes the
checked steps' AST, the inputs, the method counts, the positions transactions
call, the selector orders, the arities, the prescribed std outcomes and the
completions. Source/Rust/EVM agreement is a separate external validation. -/
set_option autoImplicit false

namespace Tests.SourceMethodsCorpus
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
  ("generatorVersion", generatorVersion), ("profileVersion", Methods.profileVersion),
  ("functionVersion", Solcore.Synthesis.Core.ContractMethods.version),
  ("templateVersion", Methods.templateVersion), ("stepProfileVersion", Aggregate.profileVersion),
  ("stepFunctionVersion", Aggregates.version), ("stepTemplateVersion", Aggregate.templateVersion),
  ("emitterVersion", Methods.emitterVersion), ("wrapperVersion", Methods.wrapperVersion)]

private def words (values : List Word) : List String := values.map fun value => toString value.val

private def outcomeNames : List String := ["0x4924aef0", "accepted"]
private def orderNames : List String := ["ascending", "descending", "mixed"]

/-- Imported entries are emitted from their saved plan and sequence; generated
entries are regenerated from their seed. Both are checked by full replay. -/
private def entryCase (entry : Json) (fuel : Nat) : Except String Json := do
  if let .ok request := entry.getObjVal? "generation" then
    let some seed := (← request.getObjValAs? String "seed").toNat? | throw "invalid generation seed"
    let corpus := Methods.generateCases (Seed.ofNat seed) (← request.getObjValAs? Nat "maxProgramNodes") 1 1 fuel
    require ((← string corpus "status") == "complete") "generated entry was excluded"
    let some saved := (← corpus.getObjValAs? (Array Json) "cases")[0]? | throw "generated entry has no case"
    return saved
  let (plan, methods, missing) ← Methods.checkedPlan (← entry.getObjVal? "methodsPlan")
  let scenario ← Methods.checkedScenario plan methods missing
    (← Methods.decodeTransactions methods missing (← entry.getObjVal? "transactions"))
  Methods.emitCase scenario (Json.mkObj [("kind", toJson "imported")]) fuel

private def templates (saved : Json) : Except String (List Nat) := do
  let origin ← (← saved.getObjVal? "provenance").getObjVal? "origin"
  if (← string origin "kind") != "methods-generated" then return []
  let stepOrigins ← origin.getObjValAs? (List Json) "stepOrigins"
  let helpers ← stepOrigins.mapM fun stepOrigin => stepOrigin.getObjValAs? (List Json) "helpers"
  helpers.flatten.mapM fun helper => helper.getObjValAs? Nat "template"

def validateManifest (manifest : Json) (fuel : Nat := 1000000) : Except String Json := do
  require ((← string manifest "schema") == "solcore-lean.semantic-storage-corpus-manifest.v1" &&
    (← string manifest "profile") == "stateful-methods" &&
    (← string manifest "coverageKind") == "step-core-ast-features") "unexpected several-methods manifest scope"
  for (key, expected) in versions do
    require ((← string manifest key) == expected) ("several-methods manifest changed " ++ key)
  let requiredFeatures ← strings manifest "requiredFeatures"
  let requiredInputs ← strings manifest "requiredInputs"
  require (sameMembers requiredInputs (words Methods.boundaryInputs))
    "several-methods corpus must require all six boundary inputs"
  require ((← manifest.getObjValAs? (List Nat) "requiredMethodCounts") == [2, 3, 4] &&
    (← manifest.getObjValAs? (List Nat) "requiredMethodPositions") == [0, 1, 2, 3] &&
    (← manifest.getObjValAs? (List Nat) "requiredArities") == [0, 1, 2])
    "several-methods corpus must require two to four methods, every position and every arity"
  require ((← strings manifest "requiredSelectorOrders") == orderNames)
    "several-methods corpus must require ascending, descending and mixed selectors"
  require ((← strings manifest "requiredRejections") == outcomeNames)
    "several-methods corpus must require the missing-selector rejection and acceptance"
  require ((← manifest.getObjValAs? (List Nat) "requiredHelperCounts") == [1, 2, 3] &&
    (← manifest.getObjValAs? (List Nat) "requiredTransactionCounts") == [1, 2, 3])
    "several-methods corpus must require one to three helpers and transactions"
  require ((← (← manifest.getObjVal? "generationRecipeRequirements").getObjValAs? (List Nat) "templates") == [0, 1, 2, 3])
    "several-methods corpus must require all four step templates"
  require ((← strings manifest "requiredOutcomes") == ["returned", "reverted"])
    "several-methods corpus must require both outcomes"
  let requiredPatterns ← strings manifest "requiredCompletionPatterns"
  require (!requiredPatterns.isEmpty) "several-methods corpus must require completion patterns"
  let entries ← manifest.getObjValAs? (Array Json) "cases"
  require (0 < entries.size && entries.size ≤ 64) "several-methods corpus must contain 1..64 scenarios"
  let mut identifiers : List String := []
  let mut features : List String := []
  let mut inputs : List String := []
  let mut counts : List Nat := []
  let mut positions : List Nat := []
  let mut orders : List String := []
  let mut arities : List Nat := []
  let mut rejections : List String := []
  let mut helperCounts : List Nat := []
  let mut transactionCounts : List Nat := []
  let mut templateUnion : List Nat := []
  let mut outcomes : List String := []
  let mut patterns : List String := []
  let mut transactionTotal := 0
  for entry in entries do
    let identifier ← string entry "id"
    require (!identifiers.contains identifier) ("duplicate several-methods corpus id " ++ identifier)
    identifiers := identifier :: identifiers
    let saved ← entryCase entry fuel
    require ((← Methods.replayCase saved fuel) == saved) ("several-methods corpus entry did not replay: " ++ identifier)
    let scenario ← Methods.caseProgram saved
    if !(entry.getObjVal? "generation").isOk then
      require ((← saved.getObjVal? "methodsPlan") == (← entry.getObjVal? "methodsPlan") &&
        (← saved.getObjVal? "transactions") == (← entry.getObjVal? "transactions"))
        ("imported several-methods entry is not canonical: " ++ identifier)
    let caseFeatures := (← (← saved.getObjVal? "provenance").getObjValAs? (List String) "features").eraseDups
    require (sameMembers (← strings entry "expectedFeatures") caseFeatures)
      ("several-methods corpus features changed: " ++ identifier)
    let history := Methods.observe scenario Solcore.Synthesis.Stateful.StorageExecution.fixtureBindings fuel
    require ((← string history "status") == "complete") ("several-methods corpus history incomplete: " ++ identifier)
    let observed ← history.getObjValAs? (List Json) "transactions"
    let expected ← entry.getObjValAs? (List Json) "expectedHistory"
    require (observed.length == expected.length) ("several-methods expected history length changed: " ++ identifier)
    let mut statuses : List String := []
    for (row, golden) in observed.zip expected do
      let actual := Json.mkObj [("id", ← row.getObjVal? "id"), ("status", ← row.getObjVal? "status"),
        ("output", ← row.getObjVal? "output"), ("committedStorage", ← row.getObjVal? "committedStorage")]
      require (actual == golden)
        ("original Core differs from the expectation without the std wrapper: " ++ identifier ++ " " ++ actual.compress)
      statuses := statuses ++ [← string row "status"]
    transactionTotal := transactionTotal + observed.length
    features := (features ++ caseFeatures).eraseDups
    inputs := (inputs ++ scenario.transactions.flatMap fun tx => words tx.inputs).eraseDups
    counts := (counts ++ [scenario.methods.length]).eraseDups
    positions := (positions ++ scenario.transactions.filterMap (·.target)).eraseDups
    orders := (orders ++ [Methods.selectorOrder scenario.methods]).eraseDups
    arities := (arities ++ scenario.methods.map (·.arity)).eraseDups
    rejections := (rejections ++ scenario.transactions.map fun tx =>
      (Methods.prescribed scenario tx).map Methods.selectorText |>.getD "accepted").eraseDups
    helperCounts := (helperCounts ++ scenario.plan.steps.map (·.helpers.length)).eraseDups
    transactionCounts := (transactionCounts ++ [scenario.transactions.length]).eraseDups
    templateUnion := (templateUnion ++ (← templates saved)).eraseDups
    outcomes := (outcomes ++ statuses).eraseDups
    patterns := (patterns ++ [String.intercalate "," statuses]).eraseDups
  require (requiredFeatures.all features.contains) "several-methods corpus misses a required step feature"
  require (requiredInputs.all inputs.contains) "several-methods corpus misses a boundary input"
  require ([2, 3, 4].all counts.contains && [0, 1, 2, 3].all positions.contains && [0, 1, 2].all arities.contains)
    "several-methods corpus misses a method count, called position or arity"
  require (orderNames.all orders.contains) "several-methods corpus misses a selector order"
  require (outcomeNames.all rejections.contains) "several-methods corpus misses a std outcome"
  require ([1, 2, 3].all helperCounts.contains && [1, 2, 3].all transactionCounts.contains)
    "several-methods corpus misses a helper or transaction count"
  require ([0, 1, 2, 3].all templateUnion.contains) "several-methods corpus misses a generated template"
  require (["returned", "reverted"].all outcomes.contains && requiredPatterns.all patterns.contains)
    "several-methods corpus misses an observed outcome or completion pattern"
  return Json.mkObj [("profile", toJson "stateful-methods"), ("scenarios", toJson entries.size),
    ("transactions", toJson transactionTotal), ("methodCounts", toJson counts), ("orders", toJson orders),
    ("rejections", toJson rejections), ("patterns", toJson patterns)]

private def checked {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def rejects {α : Type} (result : Except String α) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "invalid several-methods corpus unexpectedly passed")

def testSourceMethodsCorpus : IO Unit := do
  let manifest ← checked (Json.parse (← IO.FS.readFile "scripts/semantic-methods-corpus.json"))
  let summary ← checked (validateManifest manifest)
  let entries ← checked (manifest.getObjValAs? (Array Json) "cases")
  let some first := entries[0]? | throw (IO.userError "missing first several-methods case")
  let some generatedEntry := entries.find? (fun entry => (entry.getObjVal? "generation").isOk) |
    throw (IO.userError "missing generated several-methods case")
  let replace := fun (original changed : Json) => manifest.setObjVal! "cases"
    (.arr (entries.map fun entry => if entry == original then changed else entry))
  let history ← checked (first.getObjValAs? (Array Json) "expectedHistory")
  let row := history[0]!
  -- An output, a slot, a missing row and a status are all checked.
  let changedOutput := row.setObjVal! "output" (toJson ("0x" ++ String.ofList (List.replicate 64 'f')))
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr (history.set! 0 changedOutput)))))
  let storage ← checked (row.getObjValAs? (Array Json) "committedStorage")
  let changedSlot := row.setObjVal! "committedStorage" (.arr (storage.set! 1 (storage[1]!.setObjVal! "value" (toJson "7"))))
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr (history.set! 0 changedSlot)))))
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr (history.pop)))))
  let generatedHistory ← checked (generatedEntry.getObjValAs? (Array Json) "expectedHistory")
  let flipped := if (generatedHistory[0]!.getObjValAs? String "status").toOption == some "returned" then "reverted" else "returned"
  rejects (validateManifest (replace generatedEntry (generatedEntry.setObjVal! "expectedHistory"
    (.arr (generatedHistory.set! 0 (generatedHistory[0]!.setObjVal! "status" (toJson flipped)))))))
  let transactions ← checked (first.getObjValAs? (Array Json) "transactions")
  rejects (validateManifest (replace first (first.setObjVal! "transactions"
    (.arr (transactions.set! 0 (transactions[0]!.setObjVal! "method" Json.null))))))
  rejects (validateManifest (replace first (first.setObjVal! "expectedFeatures" (toJson ([] : List String)))))
  rejects (validateManifest (manifest.setObjVal! "cases" (.arr (entries.push first))))
  for (key, value) in [
      ("profile", toJson "stateful-storage"), ("templateVersion", toJson "forged"),
      ("cases", .arr #[]), ("requiredInputs", toJson ([] : List String)),
      ("requiredMethodCounts", toJson [2, 3]), ("requiredMethodPositions", toJson [0, 1, 2]),
      ("requiredSelectorOrders", toJson (["mixed"] : List String)),
      ("requiredRejections", toJson (["accepted"] : List String)), ("requiredHelperCounts", toJson [1, 2]),
      ("requiredCompletionPatterns", toJson (["returned,returned,returned,returned"] : List String))] do
    rejects (validateManifest (manifest.setObjVal! key value))
  rejects (validateManifest manifest 0)
  IO.println summary.compress

end Tests.SourceMethodsCorpus
