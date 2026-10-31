import Solcore.Synthesis.Source.CallSequenceCases

/-! The fixed call-sequence corpus checks actual original Core histories, run
through the call chain, against expectations computed without the Core
contracts: the child's data cut to its class byte's length and the parent's
reads of the return-data buffer around each call, in which each step runs alone
in Core. Coverage describes the checked steps' AST, the inputs, both call
counts, every pair of consecutive call states, the bank's lengths for returned
and reverted data, windows inside, past the end and of width zero, the three
rollback patterns, the call modes, the node budgets of generated entries and
both outcomes. Source/Rust/EVM agreement is a separate external validation. -/
set_option autoImplicit false

namespace Tests.SourceCallSequenceCorpus
open Lean Solcore.Core Solcore.Synthesis.Core Solcore.Synthesis.Source
open Solcore.ContractRuntime (encodeBytesText)

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
  ("generatorVersion", generatorVersion), ("profileVersion", CallSequence.profileVersion),
  ("functionVersion", Solcore.Synthesis.Core.CallSequence.childVersion),
  ("templateVersion", CallSequence.templateVersion), ("stepProfileVersion", Aggregate.profileVersion),
  ("stepFunctionVersion", Aggregates.version), ("stepTemplateVersion", Aggregate.templateVersion),
  ("emitterVersion", CallSequence.emitterVersion), ("wrapperVersion", CallSequence.wrapperVersion)]

private def words (values : List Word) : List String := values.map fun value => toString value.val

/-- A call's state: its status and whether its data are empty. -/
def stateOf (row : Solcore.Synthesis.Stateful.CallSequenceExecution.CallRow) : String :=
  (if row.returned then "returned" else "reverted") ++ (if row.length == 0 then "-empty" else "-data")

def states : List String := ["returned-data", "returned-empty", "reverted-data", "reverted-empty"]
def transitions : List String := states.flatMap fun first => states.map (first ++ ":" ++ ·)
def lengthNames : List String := ["returned", "reverted"].flatMap fun status =>
  CallSequence.lengthBank.map fun length => status ++ ":" ++ toString length
def windowKinds : List String := ["empty", "inside", "outside"]
def rollbacks : List String := ["child-reverted-parent-returned", "child-reverted-parent-reverted",
  "children-returned-parent-reverted"]

/-- Imported entries are emitted from their saved plan and sequence;
generated entries are regenerated from their seed. Both are checked by full
replay. -/
def entryCase (entry : Json) (fuel : Nat) : Except String Json := do
  if let .ok request := entry.getObjVal? "generation" then
    let some seed := (← request.getObjValAs? String "seed").toNat? | throw "invalid generation seed"
    let corpus := CallSequence.generateCases (Seed.ofNat seed) (← request.getObjValAs? Nat "maxProgramNodes") 1 1 fuel
    require ((← string corpus "status") == "complete") "generated entry was excluded"
    let some saved := (← corpus.getObjValAs? (Array Json) "cases")[0]? | throw "generated entry has no case"
    return saved
  let plan ← CallSequence.checkedPlan (← entry.getObjVal? "callSequencePlan")
  let scenario ← CallSequence.checkedScenario plan (← CallReturn.decodeImportedSequence (← entry.getObjVal? "transactions"))
  CallSequence.emitCase scenario (Json.mkObj [("kind", toJson "imported")]) fuel

private def templates (saved : Json) : Except String (List Nat) := do
  let origin ← (← saved.getObjVal? "provenance").getObjVal? "origin"
  if (← string origin "kind") != "call-sequence-generated" then return []
  let helpers ← (← origin.getObjVal? "stepOrigin").getObjValAs? (List Json) "helpers"
  helpers.mapM fun helper => helper.getObjValAs? Nat "template"

/-- The source model's rows of a scenario, in the corpus's expected-row form:
the status, the output, every call's prescribed outcome, and the parent's and
child's committed slots. -/
def modelRows (scenario : CallSequence.CheckedScenario) (fuel : Nat) : Except String (List Json) := do
  let some rows := Solcore.Synthesis.Stateful.CallSequenceExecution.model scenario.plan fuel scenario.transactions
    | throw "the source model failed"
  return (rows.zip scenario.transactions).map fun (row, transaction) => Json.mkObj [
    ("id", toJson transaction.id), ("status", toJson (if row.reverted then "reverted" else "returned")),
    ("output", toJson (encodeBytesText row.output)), ("calls", toJson (row.calls.map CallSequence.callRowJson)),
    ("parent", toJson (words row.parent)), ("child", toJson (words row.child))]

private def slotValues (account : Json) : Except String (List String) := do
  (← account.getObjValAs? (List Json) "storage").mapM fun entry => entry.getObjValAs? String "value"

def validateManifest (manifest : Json) (fuel : Nat := 1000000) : Except String Json := do
  require ((← string manifest "schema") == "solcore-lean.semantic-call-corpus-manifest.v1" &&
    (← string manifest "profile") == "stateful-call-sequences" &&
    (← string manifest "coverageKind") == "step-core-ast-features") "unexpected call-sequence manifest scope"
  for (key, expected) in versions do
    require ((← string manifest key) == expected) ("call-sequence manifest changed " ++ key)
  let requiredFeatures ← strings manifest "requiredFeatures"
  let requiredInputs ← strings manifest "requiredInputs"
  require (sameMembers requiredInputs (words CallSequence.boundaryInputs))
    "call-sequence corpus must require every boundary input"
  require ((← manifest.getObjValAs? (List Nat) "requiredSequenceCalls") == [2, 3] &&
    sameMembers (← strings manifest "requiredSequenceTransitions") transitions &&
    sameMembers (← strings manifest "requiredSequenceLengths") lengthNames &&
    (← strings manifest "requiredSequenceWindows") == windowKinds &&
    (← strings manifest "requiredSequenceRollbacks") == rollbacks &&
    (← manifest.getObjValAs? (List Nat) "requiredSequenceNodeBudgets") == [384, 512])
    "call-sequence corpus must require both call counts, every transition, the bank's lengths, every window, every rollback and both node budgets"
  require ((← manifest.getObjValAs? (List Nat) "requiredHelperCounts") == [1, 2, 3] &&
    (← manifest.getObjValAs? (List Nat) "requiredTransactionCounts") == [1, 2, 3] &&
    (← manifest.getObjValAs? (List Nat) "requiredCallModes") == [0, 1])
    "call-sequence corpus must require one to three helpers and transactions and both call modes"
  require ((← (← manifest.getObjVal? "generationRecipeRequirements").getObjValAs? (List Nat) "templates") == [0, 1, 2, 3])
    "call-sequence corpus must require all four step templates"
  require ((← strings manifest "requiredOutcomes") == ["returned", "reverted"])
    "call-sequence corpus must require both transaction outcomes"
  let entries ← manifest.getObjValAs? (Array Json) "cases"
  require (0 < entries.size && entries.size ≤ 64) "call-sequence corpus must contain 1..64 scenarios"
  let mut identifiers : List String := []
  let mut features : List String := []
  let mut inputs : List String := []
  let mut counts : List Nat := []
  let mut seenTransitions : List String := []
  let mut seenLengths : List String := []
  let mut seenWindows : List String := []
  let mut rolled : List String := []
  let mut modes : List Nat := []
  let mut budgets : List Nat := []
  let mut helperCounts : List Nat := []
  let mut transactionCounts : List Nat := []
  let mut templateUnion : List Nat := []
  let mut statusesSeen : List String := []
  let mut transactionTotal := 0
  for entry in entries do
    let identifier ← string entry "id"
    require (!identifiers.contains identifier) ("duplicate call-sequence corpus id " ++ identifier)
    identifiers := identifier :: identifiers
    let saved ← entryCase entry fuel
    require ((← CallSequence.replayCase saved fuel) == saved) ("call-sequence corpus entry did not replay: " ++ identifier)
    let scenario ← CallSequence.caseProgram saved
    if let .ok request := entry.getObjVal? "generation" then
      budgets := (budgets ++ [← request.getObjValAs? Nat "maxProgramNodes"]).eraseDups
    else
      require ((← saved.getObjVal? "callSequencePlan") == (← entry.getObjVal? "callSequencePlan"))
        ("imported call-sequence entry is not canonical: " ++ identifier)
    let caseFeatures := (← (← saved.getObjVal? "provenance").getObjValAs? (List String) "features").eraseDups
    require (sameMembers (← strings entry "expectedFeatures") caseFeatures)
      ("call-sequence corpus features changed: " ++ identifier)
    let expected ← entry.getObjValAs? (List Json) "expectedHistory"
    require (expected == (← modelRows scenario fuel)) ("the expected history differs from the source model: " ++ identifier)
    let savedTransactions ← saved.getObjValAs? (List Json) "transactions"
    require (savedTransactions.map (·.getObjVal? "calls" |>.toOption) == expected.map (·.getObjVal? "calls" |>.toOption))
      ("a prescribed outcome differs from the expected history: " ++ identifier)
    let history := CallSequence.observe scenario Solcore.Synthesis.Stateful.NestedCallExecution.fixtureBindings fuel
    require ((← string history "status") == "complete") ("call-sequence corpus history incomplete: " ++ identifier)
    let observed ← history.getObjValAs? (List Json) "transactions"
    require (observed.length == expected.length) ("call-sequence expected history length changed: " ++ identifier)
    let mut statuses : List String := []
    for (row, golden) in observed.zip expected do
      let accounts ← row.getObjValAs? (List Json) "committedAccounts"
      let some parent := accounts[0]? | throw "missing parent account"
      let some child := accounts[1]? | throw "missing child account"
      let actual := Json.mkObj [("id", ← row.getObjVal? "id"), ("status", ← row.getObjVal? "status"),
        ("output", ← row.getObjVal? "output"), ("calls", ← golden.getObjVal? "calls"),
        ("parent", toJson (← slotValues parent)), ("child", toJson (← slotValues child))]
      require (actual == golden) ("original Core differs from the source model: " ++ identifier ++ " " ++ actual.compress)
      statuses := statuses ++ [← string row "status"]
    transactionTotal := transactionTotal + observed.length
    features := (features ++ caseFeatures).eraseDups
    inputs := (inputs ++ words (scenario.transactions.map (·.input))).eraseDups
    counts := (counts ++ [scenario.plan.calls]).eraseDups
    let some rows := Solcore.Synthesis.Stateful.CallSequenceExecution.model scenario.plan fuel scenario.transactions
      | throw "the source model failed"
    for (transaction, row) in scenario.transactions.zip rows do
      modes := (modes ++ [transaction.input.val % 2]).eraseDups
      let callStates := row.calls.map stateOf
      seenTransitions := (seenTransitions ++ (callStates.zip callStates.tail).map fun (a, b) => a ++ ":" ++ b).eraseDups
      seenLengths := (seenLengths ++ row.calls.map fun call =>
        (if call.returned then "returned:" else "reverted:") ++ toString call.length).eraseDups
      seenWindows := (seenWindows ++ (row.calls.zip scenario.plan.windows).map
        fun ((call, window) : Solcore.Synthesis.Stateful.CallSequenceExecution.CallRow × Solcore.Synthesis.Core.CallSequence.Window) =>
          if window.offset + window.width > call.length then "outside" else if window.width == 0 then "empty" else "inside").eraseDups
      let reverted := row.calls.any (!·.returned)
      if row.reverted then
        if reverted then rolled := (rolled ++ ["child-reverted-parent-reverted"]).eraseDups
        if row.calls.any (·.returned) then rolled := (rolled ++ ["children-returned-parent-reverted"]).eraseDups
      else if reverted then rolled := (rolled ++ ["child-reverted-parent-returned"]).eraseDups
    helperCounts := (helperCounts ++ [scenario.plan.step.helpers.length]).eraseDups
    transactionCounts := (transactionCounts ++ [scenario.transactions.length]).eraseDups
    templateUnion := (templateUnion ++ (← templates saved)).eraseDups
    statusesSeen := (statusesSeen ++ statuses).eraseDups
  require (requiredFeatures.all features.contains) "call-sequence corpus misses a required step feature"
  require (requiredInputs.all inputs.contains) "call-sequence corpus misses a boundary input"
  require ([2, 3].all counts.contains && transitions.all seenTransitions.contains && lengthNames.all seenLengths.contains)
    "call-sequence corpus misses a call count, a transition or a bank length"
  require (windowKinds.all seenWindows.contains && rollbacks.all rolled.contains && [0, 1].all modes.contains &&
      [384, 512].all budgets.contains)
    "call-sequence corpus misses a window, a rollback, a call mode or a node budget"
  require ([1, 2, 3].all helperCounts.contains && [1, 2, 3].all transactionCounts.contains)
    "call-sequence corpus misses a helper or transaction count"
  require ([0, 1, 2, 3].all templateUnion.contains) "call-sequence corpus misses a generated template"
  require (["returned", "reverted"].all statusesSeen.contains) "call-sequence corpus misses an observed outcome"
  return Json.mkObj [("profile", toJson "stateful-call-sequences"), ("scenarios", toJson entries.size),
    ("transactions", toJson transactionTotal), ("calls", toJson counts), ("transitions", toJson seenTransitions.length),
    ("lengths", toJson seenLengths.length), ("windows", toJson seenWindows), ("rollbacks", toJson rolled),
    ("nodeBudgets", toJson budgets)]

private def checked {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def rejects {α : Type} (result : Except String α) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "invalid call-sequence corpus unexpectedly passed")

def testSourceCallSequenceCorpus : IO Unit := do
  let manifest ← checked (Json.parse (← IO.FS.readFile "scripts/semantic-call-sequence-corpus.json"))
  let summary ← checked (validateManifest manifest)
  let entries ← checked (manifest.getObjValAs? (Array Json) "cases")
  let some generatedEntry := entries.find? (fun entry => (entry.getObjVal? "generation").isOk) |
    throw (IO.userError "missing generated call-sequence case")
  let firstStatus (entry : Json) : Option String :=
    (entry.getObjValAs? (Array Json) "expectedHistory").toOption.bind fun history =>
      history[0]?.bind fun row => (row.getObjValAs? String "status").toOption
  let some first := entries.find? (fun entry => (entry.getObjVal? "callSequencePlan").isOk &&
      firstStatus entry == some "returned") |
    throw (IO.userError "missing imported returned case")
  let replace := fun (original changed : Json) => manifest.setObjVal! "cases"
    (.arr (entries.map fun entry => if entry == original then changed else entry))
  -- A row's output, slots and prescribed calls, and a missing row, are all
  -- checked.
  let history ← checked (first.getObjValAs? (Array Json) "expectedHistory")
  let row := history[0]!
  let output ← checked (row.getObjValAs? String "output")
  let changedOutput := row.setObjVal! "output" (toJson (String.ofList (output.toList.take (output.length - 1)) ++
    (if output.endsWith "1" then "2" else "1")))
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr (history.set! 0 changedOutput)))))
  let parent ← checked (row.getObjValAs? (Array String) "parent")
  let changedSlot := row.setObjVal! "parent" (toJson (parent.set! 5 (if parent[5]! == "7" then "8" else "7")))
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr (history.set! 0 changedSlot)))))
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr (history.pop)))))
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory"
    (.arr (history.set! 0 (row.setObjVal! "calls" (toJson ([] : List Json))))))))
  let generatedHistory ← checked (generatedEntry.getObjValAs? (Array Json) "expectedHistory")
  if let some head := generatedHistory[0]? then
    let flipped := if (head.getObjValAs? String "status").toOption == some "returned" then "reverted" else "returned"
    rejects (validateManifest (replace generatedEntry (generatedEntry.setObjVal! "expectedHistory"
      (.arr (generatedHistory.set! 0 (head.setObjVal! "status" (toJson flipped)))))))
  -- The plan, the features, a duplicate entry and the requirements are checked.
  let plan ← checked (first.getObjVal? "callSequencePlan")
  rejects (validateManifest (replace first (first.setObjVal! "callSequencePlan" (plan.setObjVal! "calls" (toJson 9)))))
  rejects (validateManifest (replace first (first.setObjVal! "expectedFeatures" (toJson ([] : List String)))))
  rejects (validateManifest (manifest.setObjVal! "cases" (.arr (entries.push first))))
  for (key, value) in [
      ("profile", toJson "stateful-call-returns"), ("functionVersion", toJson "forged"),
      ("cases", .arr #[]), ("requiredInputs", toJson ([] : List String)),
      ("requiredSequenceCalls", toJson [2]),
      ("requiredSequenceTransitions", toJson (["returned-data:returned-data"] : List String)),
      ("requiredSequenceLengths", toJson (["returned:0"] : List String)),
      ("requiredSequenceWindows", toJson (["inside"] : List String)),
      ("requiredSequenceRollbacks", toJson (["child-reverted-parent-returned"] : List String)),
      ("requiredSequenceNodeBudgets", toJson [384]),
      ("requiredHelperCounts", toJson [1, 2]), ("requiredTransactionCounts", toJson [1, 2]),
      ("requiredCallModes", toJson [0])] do
    rejects (validateManifest (manifest.setObjVal! key value))
  rejects (validateManifest manifest 0)
  IO.println summary.compress

end Tests.SourceCallSequenceCorpus
