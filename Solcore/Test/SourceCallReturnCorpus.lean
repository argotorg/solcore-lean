import Solcore.Synthesis.Source.CallReturnCases

/-! The fixed call-return corpus checks actual original Core histories, run
through the call-and-resume convention, against expectations computed without
the Core contracts: the child's bytes, std's decision on them and the source
model, in which each step runs alone in Core. Coverage describes the checked
steps' AST, the inputs, every kind with static and dynamic enums apart, both
deliveries, every malformation kind, std's three decisions, the malformations
std accepted, the bank's `bytes` lengths, every decoded enum field kind, the
four rollback patterns, the call modes, the node budgets of generated entries
and both outcomes. Source/Rust/EVM agreement is a separate external
validation. -/
set_option autoImplicit false

namespace Tests.SourceCallReturnCorpus
open Lean Solcore.Core Solcore.Synthesis.Core Solcore.Synthesis.Source
open Solcore.Synthesis.Core.CallReturn (Kind Returned)
open Solcore.ContractRuntime (EnumPayload encodeBytesText)

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
  ("generatorVersion", generatorVersion), ("profileVersion", CallReturn.profileVersion),
  ("functionVersion", Solcore.Synthesis.Core.CallReturn.childVersion),
  ("templateVersion", CallReturn.templateVersion), ("stepProfileVersion", Aggregate.profileVersion),
  ("stepFunctionVersion", Aggregates.version), ("stepTemplateVersion", Aggregate.templateVersion),
  ("emitterVersion", CallReturn.emitterVersion), ("wrapperVersion", CallReturn.wrapperVersion)]

private def words (values : List Word) : List String := values.map fun value => toString value.val

/-- The kinds, a tuple by its arity and an enum by its class. -/
def kindName : Kind → String
  | .tuple extra => "tuple-" ++ toString (extra + 2)
  | .bytes => "bytes"
  | .enum shape => if shape.dynamic then "dynamic-enum" else "static-enum"

def kindNames : List String := ["bytes", "dynamic-enum", "static-enum", "tuple-2", "tuple-3", "tuple-4"]
def decisions : List String := ["0x", "0x08638556", "accepted"]

/-- The malformations std can accept; an unknown tag is never accepted. -/
def acceptedKinds : List String := ["length", "narrow", "offset", "tail", "trailing", "truncate"]

def fieldName : EnumPayload → String
  | .noWords => "none"
  | .oneWord => "uint256"
  | .twoWords => "uint256,uint256"
  | .boundedBytes => "bytes"

def fieldKinds : List String := ["bytes", "none", "uint256", "uint256,uint256"]
def rollbacks : List String := ["child-returned-parent-reverted", "child-reverted-parent-returned",
  "child-reverted-parent-reverted", "rejected"]

/-- Imported entries are emitted from their saved plan and sequence;
generated entries are regenerated from their seed. Both are checked by full
replay. -/
private def entryCase (entry : Json) (fuel : Nat) : Except String Json := do
  if let .ok request := entry.getObjVal? "generation" then
    let some seed := (← request.getObjValAs? String "seed").toNat? | throw "invalid generation seed"
    let corpus := CallReturn.generateCases (Seed.ofNat seed) (← request.getObjValAs? Nat "maxProgramNodes") 1 1 fuel
    require ((← string corpus "status") == "complete") "generated entry was excluded"
    let some saved := (← corpus.getObjValAs? (Array Json) "cases")[0]? | throw "generated entry has no case"
    return saved
  let plan ← CallReturn.checkedPlan (← entry.getObjVal? "callReturnPlan")
  let scenario ← CallReturn.checkedScenario plan (← CallReturn.decodeImportedSequence (← entry.getObjVal? "transactions"))
  CallReturn.emitCase scenario (Json.mkObj [("kind", toJson "imported")]) fuel

private def templates (saved : Json) : Except String (List Nat) := do
  let origin ← (← saved.getObjVal? "provenance").getObjVal? "origin"
  if (← string origin "kind") != "call-return-generated" then return []
  let helpers ← (← origin.getObjVal? "stepOrigin").getObjValAs? (List Json) "helpers"
  helpers.mapM fun helper => helper.getObjValAs? Nat "template"

/-- The source model's rows of a scenario, in the corpus's expected-row form:
the status, original Core's output, the prescribed rejection, and the
parent's and child's committed slots. -/
def modelRows (scenario : CallReturn.CheckedScenario) (fuel : Nat) : Except String (List Json) := do
  let some rows := Solcore.Synthesis.Stateful.CallReturnExecution.model scenario.plan fuel scenario.transactions
    | throw "the source model failed"
  return (rows.zip scenario.transactions).map fun (row, transaction) => Json.mkObj [
    ("id", toJson transaction.id), ("status", toJson (if row.reverted then "reverted" else "returned")),
    ("output", toJson (encodeBytesText row.output)), ("stdRejection", CallReturn.rejectionJson row.rejection),
    ("parent", toJson (words row.parent)), ("child", toJson (words row.child))]

private def slotValues (account : Json) : Except String (List String) := do
  (← account.getObjValAs? (List Json) "storage").mapM fun entry => entry.getObjValAs? String "value"

def validateManifest (manifest : Json) (fuel : Nat := 1000000) : Except String Json := do
  require ((← string manifest "schema") == "solcore-lean.semantic-call-corpus-manifest.v1" &&
    (← string manifest "profile") == "stateful-call-returns" &&
    (← string manifest "coverageKind") == "step-core-ast-features") "unexpected call-return manifest scope"
  for (key, expected) in versions do
    require ((← string manifest key) == expected) ("call-return manifest changed " ++ key)
  let requiredFeatures ← strings manifest "requiredFeatures"
  let requiredInputs ← strings manifest "requiredInputs"
  require (sameMembers requiredInputs (words CallReturn.boundaryInputs))
    "call-return corpus must require every boundary input"
  require ((← strings manifest "requiredReturnKinds") == kindNames &&
    (← strings manifest "requiredReturnDeliveries") == ["raw", "typed"] &&
    sameMembers (← strings manifest "requiredReturnMalformations") CallReturn.malformationKinds &&
    (← strings manifest "requiredReturnDecisions") == decisions &&
    (← strings manifest "requiredReturnAccepted") == acceptedKinds)
    "call-return corpus must require every kind, delivery, malformation, decision and accepted malformation"
  let lengths ← manifest.getObjValAs? (List Nat) "requiredReturnBytesLengths"
  require (CallReturn.lengthBank.all lengths.contains && lengths.all (· ≤ 64) &&
    (← strings manifest "requiredReturnEnumFields") == fieldKinds &&
    (← strings manifest "requiredReturnRollbacks") == rollbacks &&
    (← manifest.getObjValAs? (List Nat) "requiredReturnNodeBudgets") == [384, 512])
    "call-return corpus must require the bank's bytes lengths, every enum field kind, every rollback and both node budgets"
  require ((← manifest.getObjValAs? (List Nat) "requiredHelperCounts") == [1, 2, 3] &&
    (← manifest.getObjValAs? (List Nat) "requiredTransactionCounts") == [1, 2, 3] &&
    (← manifest.getObjValAs? (List Nat) "requiredCallModes") == [0, 1, 2, 3])
    "call-return corpus must require one to three helpers and transactions and every call mode"
  require ((← (← manifest.getObjVal? "generationRecipeRequirements").getObjValAs? (List Nat) "templates") == [0, 1, 2, 3])
    "call-return corpus must require all four step templates"
  require ((← strings manifest "requiredOutcomes") == ["returned", "reverted"])
    "call-return corpus must require both transaction outcomes"
  let entries ← manifest.getObjValAs? (Array Json) "cases"
  require (0 < entries.size && entries.size ≤ 64) "call-return corpus must contain 1..64 scenarios"
  let mut identifiers : List String := []
  let mut features : List String := []
  let mut inputs : List String := []
  let mut kinds : List String := []
  let mut deliveries : List String := []
  let mut malformations : List String := []
  let mut decided : List String := []
  let mut accepted : List String := []
  let mut bytesLengths : List Nat := []
  let mut fields : List String := []
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
    require (!identifiers.contains identifier) ("duplicate call-return corpus id " ++ identifier)
    identifiers := identifier :: identifiers
    let saved ← entryCase entry fuel
    require ((← CallReturn.replayCase saved fuel) == saved) ("call-return corpus entry did not replay: " ++ identifier)
    let scenario ← CallReturn.caseProgram saved
    if let .ok request := entry.getObjVal? "generation" then
      budgets := (budgets ++ [← request.getObjValAs? Nat "maxProgramNodes"]).eraseDups
    else
      require ((← saved.getObjVal? "callReturnPlan") == (← entry.getObjVal? "callReturnPlan"))
        ("imported call-return entry is not canonical: " ++ identifier)
    let caseFeatures := (← (← saved.getObjVal? "provenance").getObjValAs? (List String) "features").eraseDups
    require (sameMembers (← strings entry "expectedFeatures") caseFeatures)
      ("call-return corpus features changed: " ++ identifier)
    let expected ← entry.getObjValAs? (List Json) "expectedHistory"
    require (expected == (← modelRows scenario fuel)) ("the expected history differs from the source model: " ++ identifier)
    let savedTransactions ← saved.getObjValAs? (List Json) "transactions"
    require (savedTransactions.map (·.getObjVal? "stdRejection" |>.toOption) ==
        expected.map (·.getObjVal? "stdRejection" |>.toOption))
      ("a prescribed rejection differs from the expected history: " ++ identifier)
    let history := CallReturn.observe scenario Solcore.Synthesis.Stateful.NestedCallExecution.fixtureBindings fuel
    require ((← string history "status") == "complete") ("call-return corpus history incomplete: " ++ identifier)
    let observed ← history.getObjValAs? (List Json) "transactions"
    require (observed.length == expected.length) ("call-return expected history length changed: " ++ identifier)
    let mut statuses : List String := []
    for (row, golden) in observed.zip expected do
      let accounts ← row.getObjValAs? (List Json) "committedAccounts"
      let some parent := accounts[0]? | throw "missing parent account"
      let some child := accounts[1]? | throw "missing child account"
      let actual := Json.mkObj [("id", ← row.getObjVal? "id"), ("status", ← row.getObjVal? "status"),
        ("output", ← row.getObjVal? "output"), ("stdRejection", ← golden.getObjVal? "stdRejection"),
        ("parent", toJson (← slotValues parent)), ("child", toJson (← slotValues child))]
      require (actual == golden) ("original Core differs from the source model: " ++ identifier ++ " " ++ actual.compress)
      statuses := statuses ++ [← string row "status"]
    transactionTotal := transactionTotal + observed.length
    features := (features ++ caseFeatures).eraseDups
    inputs := (inputs ++ words (scenario.transactions.map (·.input))).eraseDups
    let returned := scenario.plan.returned
    kinds := (kinds ++ [kindName returned.kind]).eraseDups
    deliveries := (deliveries ++ [match returned.delivery with | .typed => "typed" | .raw _ => "raw"]).eraseDups
    if let .raw malformation := returned.delivery then
      malformations := (malformations ++ [CallReturn.kindOf malformation]).eraseDups
    for (transaction, golden) in scenario.transactions.zip expected do
      let x := transaction.input.val
      modes := (modes ++ [x % 4]).eraseDups
      if x % 2 == 1 then
        rolled := (rolled ++ [if x / 2 % 2 == 1 then "child-reverted-parent-reverted" else "child-reverted-parent-returned"]).eraseDups
      else
        match ← golden.getObjVal? "stdRejection" with
        | .null =>
            decided := (decided ++ ["accepted"]).eraseDups
            if let .raw malformation := returned.delivery then
              accepted := (accepted ++ [CallReturn.kindOf malformation]).eraseDups
            if returned.carriesBytes then bytesLengths := (bytesLengths ++ [returned.length]).eraseDups
            if let .enum shape := returned.kind then
              fields := (fields ++ [fieldName (Solcore.Synthesis.Core.CallReturn.chosen shape returned.choice).payload]).eraseDups
            if x / 2 % 2 == 1 then rolled := (rolled ++ ["child-returned-parent-reverted"]).eraseDups
        | rejection =>
            decided := (decided ++ [← rejection.getStr?]).eraseDups
            rolled := (rolled ++ ["rejected"]).eraseDups
    helperCounts := (helperCounts ++ [scenario.plan.step.helpers.length]).eraseDups
    transactionCounts := (transactionCounts ++ [scenario.transactions.length]).eraseDups
    templateUnion := (templateUnion ++ (← templates saved)).eraseDups
    statusesSeen := (statusesSeen ++ statuses).eraseDups
  require (requiredFeatures.all features.contains) "call-return corpus misses a required step feature"
  require (requiredInputs.all inputs.contains) "call-return corpus misses a boundary input"
  require (kindNames.all kinds.contains && ["raw", "typed"].all deliveries.contains &&
      CallReturn.malformationKinds.all malformations.contains) "call-return corpus misses a kind, delivery or malformation"
  require (decisions.all decided.contains && acceptedKinds.all accepted.contains)
    "call-return corpus misses a decision or an accepted malformation"
  require (CallReturn.lengthBank.all bytesLengths.contains && fieldKinds.all fields.contains)
    "call-return corpus misses an accepted bytes length or enum field kind"
  require (rollbacks.all rolled.contains && [0, 1, 2, 3].all modes.contains && [384, 512].all budgets.contains)
    "call-return corpus misses a rollback, a call mode or a node budget"
  require ([1, 2, 3].all helperCounts.contains && [1, 2, 3].all transactionCounts.contains)
    "call-return corpus misses a helper or transaction count"
  require ([0, 1, 2, 3].all templateUnion.contains) "call-return corpus misses a generated template"
  require (["returned", "reverted"].all statusesSeen.contains) "call-return corpus misses an observed outcome"
  return Json.mkObj [("profile", toJson "stateful-call-returns"), ("scenarios", toJson entries.size),
    ("transactions", toJson transactionTotal), ("kinds", toJson kinds), ("malformations", toJson malformations),
    ("decisions", toJson decided), ("accepted", toJson accepted), ("bytesLengths", toJson bytesLengths),
    ("fields", toJson fields), ("rollbacks", toJson rolled), ("nodeBudgets", toJson budgets)]

private def checked {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def rejects {α : Type} (result : Except String α) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "invalid call-return corpus unexpectedly passed")

def testSourceCallReturnCorpus : IO Unit := do
  let manifest ← checked (Json.parse (← IO.FS.readFile "scripts/semantic-call-return-corpus.json"))
  let summary ← checked (validateManifest manifest)
  let entries ← checked (manifest.getObjValAs? (Array Json) "cases")
  let some generatedEntry := entries.find? (fun entry => (entry.getObjVal? "generation").isOk) |
    throw (IO.userError "missing generated call-return case")
  -- An imported entry whose first transaction returns, and one whose first is
  -- rejected.
  let firstStatus (entry : Json) : Option String :=
    (entry.getObjValAs? (Array Json) "expectedHistory").toOption.bind fun history =>
      history[0]?.bind fun row => (row.getObjValAs? String "status").toOption
  let some first := entries.find? (fun entry => (entry.getObjVal? "callReturnPlan").isOk &&
      firstStatus entry == some "returned") |
    throw (IO.userError "missing imported returned case")
  let some rejected := entries.find? (fun entry => (entry.getObjVal? "callReturnPlan").isOk &&
      (entry.getObjValAs? (Array Json) "expectedHistory").toOption.any (fun history =>
        history[0]?.any (fun row => (row.getObjValAs? String "stdRejection").toOption == some "0x08638556"))) |
    throw (IO.userError "missing rejected case")
  let replace := fun (original changed : Json) => manifest.setObjVal! "cases"
    (.arr (entries.map fun entry => if entry == original then changed else entry))
  -- A row's output, slots, status and prescribed rejection, and a missing row,
  -- are all checked.
  let history ← checked (first.getObjValAs? (Array Json) "expectedHistory")
  let row := history[0]!
  let output ← checked (row.getObjValAs? String "output")
  let changedOutput := row.setObjVal! "output" (toJson (String.ofList (output.toList.take (output.length - 1)) ++
    (if output.endsWith "1" then "2" else "1")))
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr (history.set! 0 changedOutput)))))
  let parent ← checked (row.getObjValAs? (Array String) "parent")
  let changedSlot := row.setObjVal! "parent" (toJson (parent.set! 3 (if parent[3]! == "7" then "8" else "7")))
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr (history.set! 0 changedSlot)))))
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr (history.pop)))))
  let rejection ← checked (rejected.getObjValAs? (Array Json) "expectedHistory")
  rejects (validateManifest (replace rejected (rejected.setObjVal! "expectedHistory"
    (.arr (rejection.set! 0 (rejection[0]!.setObjVal! "stdRejection" (toJson "0x")))))))
  let generatedHistory ← checked (generatedEntry.getObjValAs? (Array Json) "expectedHistory")
  if let some head := generatedHistory[0]? then
    let flipped := if (head.getObjValAs? String "status").toOption == some "returned" then "reverted" else "returned"
    rejects (validateManifest (replace generatedEntry (generatedEntry.setObjVal! "expectedHistory"
      (.arr (generatedHistory.set! 0 (head.setObjVal! "status" (toJson flipped)))))))
  -- The plan, the features, a duplicate entry and the requirements are checked.
  let plan ← checked (first.getObjVal? "callReturnPlan")
  rejects (validateManifest (replace first (first.setObjVal! "callReturnPlan" (plan.setObjVal! "choice" (toJson 9)))))
  rejects (validateManifest (replace first (first.setObjVal! "expectedFeatures" (toJson ([] : List String)))))
  rejects (validateManifest (manifest.setObjVal! "cases" (.arr (entries.push first))))
  for (key, value) in [
      ("profile", toJson "stateful-calls"), ("functionVersion", toJson "forged"),
      ("cases", .arr #[]), ("requiredInputs", toJson ([] : List String)),
      ("requiredReturnKinds", toJson (["bytes"] : List String)),
      ("requiredReturnDeliveries", toJson (["typed"] : List String)),
      ("requiredReturnMalformations", toJson (["truncate"] : List String)),
      ("requiredReturnDecisions", toJson (["accepted"] : List String)),
      ("requiredReturnAccepted", toJson (["trailing"] : List String)),
      ("requiredReturnBytesLengths", toJson [0, 1, 32]),
      ("requiredReturnEnumFields", toJson (["none"] : List String)),
      ("requiredReturnRollbacks", toJson (["rejected"] : List String)),
      ("requiredReturnNodeBudgets", toJson [384]),
      ("requiredHelperCounts", toJson [1, 2]), ("requiredTransactionCounts", toJson [1, 2]),
      ("requiredCallModes", toJson [0, 1])] do
    rejects (validateManifest (manifest.setObjVal! key value))
  rejects (validateManifest manifest 0)
  IO.println summary.compress

end Tests.SourceCallReturnCorpus
