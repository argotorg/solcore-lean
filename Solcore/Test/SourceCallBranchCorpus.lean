import Solcore.Synthesis.Source.CallBranchCases

/-! The fixed call-branch corpus checks actual original Core histories, run
through the choice chain, against each entry's expected history, which must
also equal the byte-level model's rows: the child's data cut to its class
byte's length and the parent's reads of the return-data buffer before and
after each site and after each call, in which each step runs alone in Core.
Coverage describes the checked steps' AST, the inputs, one to three sites,
every loop bound, zero to three calls, the buffer at every position passed
without a call, every loop exit, the bank's lengths for returned and reverted
data, windows inside, past the end and of width zero, the three rollback
patterns, the call modes, the node budgets of generated entries and both
outcomes. Source/Rust/EVM agreement is a separate external validation. -/
set_option autoImplicit false

namespace Tests.SourceCallBranchCorpus
open Lean Solcore.Core Solcore.Synthesis.Core Solcore.Synthesis.Source
open Solcore.Synthesis.Core.CallBranch (Site Kind)
open Solcore.Synthesis.Core.CallSequence (Window)
open Solcore.Synthesis.Stateful.CallBranchExecution (CallRow)
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
  ("generatorVersion", generatorVersion), ("profileVersion", CallBranch.profileVersion),
  ("functionVersion", Solcore.Synthesis.Core.CallSequence.childVersion),
  ("templateVersion", CallBranch.templateVersion), ("stepProfileVersion", Aggregate.profileVersion),
  ("stepFunctionVersion", Aggregates.version), ("stepTemplateVersion", Aggregate.templateVersion),
  ("emitterVersion", CallBranch.emitterVersion), ("wrapperVersion", CallBranch.wrapperVersion)]

private def words (values : List Word) : List String := values.map fun value => toString value.val

def skipStates : List String := ["none", "returned-data", "returned-empty", "reverted-data", "reverted-empty"]
def loopExits : List String := ["stop-at-entry", "stop-after-call", "limit"]
def lengthNames : List String := ["returned", "reverted"].flatMap fun status =>
  CallBranch.lengthBank.map fun length => status ++ ":" ++ toString length
def windowKinds : List String := ["empty", "inside", "outside"]
def rollbacks : List String := ["child-reverted-parent-returned", "child-reverted-parent-reverted",
  "children-returned-parent-reverted"]

private def windowKind (window : Window) (size : Nat) : String :=
  if window.offset + window.width > size then "outside" else if window.width == 0 then "empty" else "inside"

/-- One transaction's branch values: the buffer at each position passed
without a call, each loop's exit and every window's place. -/
def transactionValues (sites : List Site) (input : Word) (calls : List CallRow) :
    List String × List String × List String := Id.run do
  let latest := fun (before : Nat) => (calls.filter (·.position < before)).getLast?
  let stateOf := fun (call : Option CallRow) => match call with
    | none => "none"
    | some call => (if call.returned then "returned" else "reverted") ++ (if call.length == 0 then "-empty" else "-data")
  let mut skips : List String := []
  let mut exits : List String := []
  let mut windows : List String := []
  for (site, index) in sites.zipIdx do
    let first := CallBranch.firstPosition sites index
    let positions := (List.range site.bound).map (first + ·)
    for position in positions do
      unless calls.any (·.position == position) do
        skips := skips ++ [stateOf (latest position)]
    if site.kind == .loop then
      let limit := Solcore.Synthesis.Stateful.CallBranchExecution.limitOf input index site.bound
      let made := (calls.filter fun call => positions.contains call.position).length
      exits := exits ++ [if made == limit then "limit" else if made == 0 then "stop-at-entry" else "stop-after-call"]
    windows := windows ++ [windowKind site.exitWindow ((latest (first + site.bound)).map (·.length) |>.getD 0)]
  for call in calls do
    let site := sites.getD (CallBranch.siteOf sites call.position) ⟨.branch, 1, 0, ⟨0, 0⟩, ⟨0, 0⟩⟩
    windows := windows ++ [windowKind site.callWindow call.length]
  return (skips, exits, windows)

/-- Imported entries are emitted from their saved plan and sequence;
generated entries are regenerated from their seed. Both are checked by full
replay. -/
def entryCase (entry : Json) (fuel : Nat) : Except String Json := do
  if let .ok request := entry.getObjVal? "generation" then
    let some seed := (← request.getObjValAs? String "seed").toNat? | throw "invalid generation seed"
    let corpus := CallBranch.generateCases (Seed.ofNat seed) (← request.getObjValAs? Nat "maxProgramNodes") 1 1 fuel
    require ((← string corpus "status") == "complete") "generated entry was excluded"
    let some saved := (← corpus.getObjValAs? (Array Json) "cases")[0]? | throw "generated entry has no case"
    return saved
  let plan ← CallBranch.checkedPlan (← entry.getObjVal? "callBranchPlan")
  let scenario ← CallBranch.checkedScenario plan (← CallReturn.decodeImportedSequence (← entry.getObjVal? "transactions"))
  CallBranch.emitCase scenario (Json.mkObj [("kind", toJson "imported")]) fuel

private def templates (saved : Json) : Except String (List Nat) := do
  let origin ← (← saved.getObjVal? "provenance").getObjVal? "origin"
  if (← string origin "kind") != "call-branch-generated" then return []
  let helpers ← (← origin.getObjVal? "stepOrigin").getObjValAs? (List Json) "helpers"
  helpers.mapM fun helper => helper.getObjValAs? Nat "template"

/-- The source model's rows of a scenario, in the corpus's expected-row form:
the status, the output, every call's prescribed outcome, and the parent's and
child's committed slots. -/
def modelRows (scenario : CallBranch.CheckedScenario) (fuel : Nat) : Except String (List Json) := do
  let some rows := Solcore.Synthesis.Stateful.CallBranchExecution.model scenario.plan fuel scenario.transactions
    | throw "the source model failed"
  return (rows.zip scenario.transactions).map fun (row, transaction) => Json.mkObj [
    ("id", toJson transaction.id), ("status", toJson (if row.reverted then "reverted" else "returned")),
    ("output", toJson (encodeBytesText row.output)), ("calls", toJson (row.calls.map CallBranch.callRowJson)),
    ("parent", toJson (words row.parent)), ("child", toJson (words row.child))]

private def slotValues (account : Json) : Except String (List String) := do
  (← account.getObjValAs? (List Json) "storage").mapM fun entry => entry.getObjValAs? String "value"

def validateManifest (manifest : Json) (fuel : Nat := 1000000) : Except String Json := do
  require ((← string manifest "schema") == "solcore-lean.semantic-call-corpus-manifest.v1" &&
    (← string manifest "profile") == "stateful-call-branches" &&
    (← string manifest "coverageKind") == "step-core-ast-features") "unexpected call-branch manifest scope"
  for (key, expected) in versions do
    require ((← string manifest key) == expected) ("call-branch manifest changed " ++ key)
  let requiredFeatures ← strings manifest "requiredFeatures"
  let requiredInputs ← strings manifest "requiredInputs"
  require (sameMembers requiredInputs (words NestedCall.boundaryInputs))
    "call-branch corpus must require every boundary input"
  require ((← manifest.getObjValAs? (List Nat) "requiredBranchSites") == [1, 2, 3] &&
    (← manifest.getObjValAs? (List Nat) "requiredBranchLoops") == [1, 2, 3] &&
    (← manifest.getObjValAs? (List Nat) "requiredBranchCalls") == [0, 1, 2, 3] &&
    (← strings manifest "requiredBranchSkips") == skipStates &&
    (← strings manifest "requiredBranchLoopExits") == loopExits &&
    sameMembers (← strings manifest "requiredBranchLengths") lengthNames &&
    (← strings manifest "requiredBranchWindows") == windowKinds &&
    (← strings manifest "requiredBranchRollbacks") == rollbacks &&
    (← manifest.getObjValAs? (List Nat) "requiredBranchNodeBudgets") == [384, 512])
    "call-branch corpus must require every site count, loop bound, call count, skip, loop exit, bank length, window, rollback and both node budgets"
  require ((← manifest.getObjValAs? (List Nat) "requiredHelperCounts") == [1, 2, 3] &&
    (← manifest.getObjValAs? (List Nat) "requiredTransactionCounts") == [1, 2, 3] &&
    (← manifest.getObjValAs? (List Nat) "requiredCallModes") == [0, 1])
    "call-branch corpus must require one to three helpers and transactions and both call modes"
  require ((← (← manifest.getObjVal? "generationRecipeRequirements").getObjValAs? (List Nat) "templates") == [0, 1, 2, 3])
    "call-branch corpus must require all four step templates"
  require ((← strings manifest "requiredOutcomes") == ["returned", "reverted"])
    "call-branch corpus must require both transaction outcomes"
  let entries ← manifest.getObjValAs? (Array Json) "cases"
  require (0 < entries.size && entries.size ≤ 64) "call-branch corpus must contain 1..64 scenarios"
  let mut identifiers : List String := []
  let mut features : List String := []
  let mut inputs : List String := []
  let mut siteCounts : List Nat := []
  let mut loopBounds : List Nat := []
  let mut callCounts : List Nat := []
  let mut seenSkips : List String := []
  let mut seenExits : List String := []
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
    require (!identifiers.contains identifier) ("duplicate call-branch corpus id " ++ identifier)
    identifiers := identifier :: identifiers
    let saved ← entryCase entry fuel
    require ((← CallBranch.replayCase saved fuel) == saved) ("call-branch corpus entry did not replay: " ++ identifier)
    let scenario ← CallBranch.caseProgram saved
    if let .ok request := entry.getObjVal? "generation" then
      budgets := (budgets ++ [← request.getObjValAs? Nat "maxProgramNodes"]).eraseDups
    else
      require ((← saved.getObjVal? "callBranchPlan") == (← entry.getObjVal? "callBranchPlan"))
        ("imported call-branch entry is not canonical: " ++ identifier)
    let caseFeatures := (← (← saved.getObjVal? "provenance").getObjValAs? (List String) "features").eraseDups
    require (sameMembers (← strings entry "expectedFeatures") caseFeatures)
      ("call-branch corpus features changed: " ++ identifier)
    let expected ← entry.getObjValAs? (List Json) "expectedHistory"
    require (expected == (← modelRows scenario fuel)) ("the expected history differs from the source model: " ++ identifier)
    let savedTransactions ← saved.getObjValAs? (List Json) "transactions"
    require (savedTransactions.map (·.getObjVal? "calls" |>.toOption) == expected.map (·.getObjVal? "calls" |>.toOption))
      ("a prescribed outcome differs from the expected history: " ++ identifier)
    let history := CallBranch.observe scenario Solcore.Synthesis.Stateful.NestedCallExecution.fixtureBindings fuel
    require ((← string history "status") == "complete") ("call-branch corpus history incomplete: " ++ identifier)
    let observed ← history.getObjValAs? (List Json) "transactions"
    require (observed.length == expected.length) ("call-branch expected history length changed: " ++ identifier)
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
    let sites := scenario.plan.sites
    siteCounts := (siteCounts ++ [sites.length]).eraseDups
    loopBounds := (loopBounds ++ (sites.filter (·.kind == .loop)).map (·.bound)).eraseDups
    let some rows := Solcore.Synthesis.Stateful.CallBranchExecution.model scenario.plan fuel scenario.transactions
      | throw "the source model failed"
    for (transaction, row) in scenario.transactions.zip rows do
      modes := (modes ++ [transaction.input.val % 2]).eraseDups
      callCounts := (callCounts ++ [row.calls.length]).eraseDups
      let (skips, exits, windows) := transactionValues sites transaction.input row.calls
      seenSkips := (seenSkips ++ skips).eraseDups
      seenExits := (seenExits ++ exits).eraseDups
      seenWindows := (seenWindows ++ windows).eraseDups
      seenLengths := (seenLengths ++ row.calls.map fun call =>
        (if call.returned then "returned:" else "reverted:") ++ toString call.length).eraseDups
      let reverted := row.calls.any (!·.returned)
      if row.reverted then
        if reverted then rolled := (rolled ++ ["child-reverted-parent-reverted"]).eraseDups
        if row.calls.any (·.returned) then rolled := (rolled ++ ["children-returned-parent-reverted"]).eraseDups
      else if reverted then rolled := (rolled ++ ["child-reverted-parent-returned"]).eraseDups
    helperCounts := (helperCounts ++ [scenario.plan.step.helpers.length]).eraseDups
    transactionCounts := (transactionCounts ++ [scenario.transactions.length]).eraseDups
    templateUnion := (templateUnion ++ (← templates saved)).eraseDups
    statusesSeen := (statusesSeen ++ statuses).eraseDups
  require (requiredFeatures.all features.contains) "call-branch corpus misses a required step feature"
  require (requiredInputs.all inputs.contains) "call-branch corpus misses a boundary input"
  require ([1, 2, 3].all siteCounts.contains && [1, 2, 3].all loopBounds.contains && [0, 1, 2, 3].all callCounts.contains)
    "call-branch corpus misses a site count, a loop bound or a call count"
  require (skipStates.all seenSkips.contains && loopExits.all seenExits.contains && lengthNames.all seenLengths.contains)
    "call-branch corpus misses a skip, a loop exit or a bank length"
  require (windowKinds.all seenWindows.contains && rollbacks.all rolled.contains && [0, 1].all modes.contains &&
      [384, 512].all budgets.contains)
    "call-branch corpus misses a window, a rollback, a call mode or a node budget"
  require ([1, 2, 3].all helperCounts.contains && [1, 2, 3].all transactionCounts.contains)
    "call-branch corpus misses a helper or transaction count"
  require ([0, 1, 2, 3].all templateUnion.contains) "call-branch corpus misses a generated template"
  require (["returned", "reverted"].all statusesSeen.contains) "call-branch corpus misses an observed outcome"
  return Json.mkObj [("profile", toJson "stateful-call-branches"), ("scenarios", toJson entries.size),
    ("transactions", toJson transactionTotal), ("sites", toJson siteCounts), ("loops", toJson loopBounds),
    ("calls", toJson callCounts), ("skips", toJson seenSkips), ("exits", toJson seenExits),
    ("lengths", toJson seenLengths.length), ("windows", toJson seenWindows), ("rollbacks", toJson rolled),
    ("nodeBudgets", toJson budgets)]

private def checked {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def rejects {α : Type} (result : Except String α) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "invalid call-branch corpus unexpectedly passed")

def testSourceCallBranchCorpus : IO Unit := do
  let manifest ← checked (Json.parse (← IO.FS.readFile "scripts/semantic-call-branch-corpus.json"))
  let summary ← checked (validateManifest manifest)
  let entries ← checked (manifest.getObjValAs? (Array Json) "cases")
  let some generatedEntry := entries.find? (fun entry => (entry.getObjVal? "generation").isOk) |
    throw (IO.userError "missing generated call-branch case")
  let some first := entries.find? (fun entry => (entry.getObjValAs? String "id").toOption == some "skips") |
    throw (IO.userError "missing the skips entry")
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
  let plan ← checked (first.getObjVal? "callBranchPlan")
  rejects (validateManifest (replace first (first.setObjVal! "callBranchPlan" (plan.setObjVal! "sites" (toJson ([] : List Json))))))
  rejects (validateManifest (replace first (first.setObjVal! "expectedFeatures" (toJson ([] : List String)))))
  rejects (validateManifest (manifest.setObjVal! "cases" (.arr (entries.push first))))
  for (key, value) in [
      ("profile", toJson "stateful-call-sequences"), ("functionVersion", toJson "forged"),
      ("cases", .arr #[]), ("requiredInputs", toJson ([] : List String)),
      ("requiredBranchSites", toJson [1]), ("requiredBranchLoops", toJson [3]), ("requiredBranchCalls", toJson [1]),
      ("requiredBranchSkips", toJson (["none"] : List String)),
      ("requiredBranchLoopExits", toJson (["limit"] : List String)),
      ("requiredBranchLengths", toJson (["returned:0"] : List String)),
      ("requiredBranchWindows", toJson (["inside"] : List String)),
      ("requiredBranchRollbacks", toJson (["child-reverted-parent-returned"] : List String)),
      ("requiredBranchNodeBudgets", toJson [384]),
      ("requiredHelperCounts", toJson [1, 2]), ("requiredTransactionCounts", toJson [1, 2]),
      ("requiredCallModes", toJson [0])] do
    rejects (validateManifest (manifest.setObjVal! key value))
  rejects (validateManifest manifest 0)
  IO.println summary.compress

end Tests.SourceCallBranchCorpus
