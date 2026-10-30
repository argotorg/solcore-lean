import Solcore.Synthesis.Source.ForwardedCallCases

/-! The fixed forwarded-value corpus checks actual original Core histories
against independently computed expectations: root status and payload, both
contracts' balances and slots zero and one, and empty logs after every
transaction. Coverage describes the checked step AST, the inputs and call
modes, the call values and forwarded amounts, the amounts child reverts keep
with the parent and the call values root reverts return. Source/Rust/EVM
agreement is a separate external validation. -/
set_option autoImplicit false

namespace Tests.SourceForwardedCallCorpus
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
  ("generatorVersion", generatorVersion), ("profileVersion", ForwardedCall.profileVersion),
  ("functionVersion", Solcore.Synthesis.Core.ForwardedCall.version),
  ("templateVersion", ForwardedCall.templateVersion), ("stepProfileVersion", Aggregate.profileVersion),
  ("stepFunctionVersion", Aggregates.version), ("stepTemplateVersion", Aggregate.templateVersion),
  ("emitterVersion", ForwardedCall.emitterVersion), ("wrapperVersion", ForwardedCall.wrapperVersion)]

private def words (values : List Word) : List String := values.map fun value => toString value.val

/-- Imported entries are emitted from their saved plan and sequence; generated
entries are regenerated from their seed. Both are checked by full replay. -/
private def entryCase (entry : Json) (fuel : Nat) : Except String Json := do
  if let .ok request := entry.getObjVal? "generation" then
    let some seed := (← request.getObjValAs? String "seed").toNat? | throw "invalid generation seed"
    let corpus := ForwardedCall.generateCases (Seed.ofNat seed) (← request.getObjValAs? Nat "maxProgramNodes") 1 1 fuel
    require ((← string corpus "status") == "complete") "generated entry was excluded"
    let some saved := (← corpus.getObjValAs? (Array Json) "cases")[0]? | throw "generated entry has no case"
    return saved
  let plan ← ForwardedCall.checkedPlan (← entry.getObjVal? "forwardPlan")
  let scenario ← ForwardedCall.checkedScenario plan (← ForwardedCall.decodeTransactions (← entry.getObjVal? "transactions"))
  ForwardedCall.emitCase scenario (Json.mkObj [("kind", toJson "imported")]) fuel

private def templates (saved : Json) : Except String (List Nat) := do
  let origin ← (← saved.getObjVal? "provenance").getObjVal? "origin"
  if (← string origin "kind") != "forward-generated" then return []
  let helpers ← (← origin.getObjVal? "stepOrigin").getObjValAs? (List Json) "helpers"
  helpers.mapM fun helper => helper.getObjValAs? Nat "template"

def validateManifest (manifest : Json) (fuel : Nat := 1000000) : Except String Json := do
  require ((← string manifest "schema") == "solcore-lean.semantic-call-corpus-manifest.v1" &&
    (← string manifest "profile") == "stateful-forwarded-value" &&
    (← string manifest "coverageKind") == "step-core-ast-features") "unexpected forwarded-value manifest scope"
  for (key, expected) in versions do
    require ((← string manifest key) == expected) ("forwarded-value manifest changed " ++ key)
  let requiredFeatures ← strings manifest "requiredFeatures"
  let requiredInputs ← strings manifest "requiredInputs"
  require (sameMembers requiredInputs (words ForwardedCall.boundaryInputs))
    "forwarded-value corpus must require all ten boundary inputs"
  require ((← manifest.getObjValAs? (List Nat) "requiredCallModes") == [0, 1, 2, 3])
    "forwarded-value corpus must require all four call modes"
  require (sameMembers (← strings manifest "requiredValues") (words ForwardedCall.valueBank) &&
      sameMembers (← strings manifest "requiredForwardedValues") (words ForwardedCall.valueBank))
    "forwarded-value corpus must require the whole bank as call values and amounts"
  let requiredRefunded ← strings manifest "requiredRefundedForwards"
  let requiredReverted ← strings manifest "requiredRevertedValues"
  require (requiredRefunded.length ≥ 3 && requiredRefunded.all ((words ForwardedCall.valueBank).contains ·) &&
      !requiredRefunded.contains "0")
    "forwarded-value corpus must require at least three nonzero forwards kept by child reverts"
  require (requiredReverted.length ≥ 3 && requiredReverted.all ((words ForwardedCall.valueBank).contains ·) &&
      requiredReverted.contains "0" && requiredReverted.any (· != "0"))
    "forwarded-value corpus must require root refunds of zero and of nonzero call values"
  require ((← manifest.getObjValAs? (List Nat) "requiredHelperCounts") == [1, 2, 3] &&
    (← manifest.getObjValAs? (List Nat) "requiredTransactionCounts") == [1, 2, 3])
    "forwarded-value corpus must require one to three helpers and transactions"
  require ((← (← manifest.getObjVal? "generationRecipeRequirements").getObjValAs? (List Nat) "templates") == [0, 1, 2, 3])
    "forwarded-value corpus must require all four step templates"
  require ((← strings manifest "requiredOutcomes") == ["returned", "reverted"]) "forwarded-value corpus must require both outcomes"
  let entries ← manifest.getObjValAs? (Array Json) "cases"
  require (0 < entries.size && entries.size ≤ 64) "forwarded-value corpus must contain 1..64 scenarios"
  let mut identifiers : List String := []
  let mut features : List String := []
  let mut inputs : List String := []
  let mut modes : List Nat := []
  let mut values : List String := []
  let mut amounts : List String := []
  let mut refunded : List String := []
  let mut reverted : List String := []
  let mut helperCounts : List Nat := []
  let mut transactionCounts : List Nat := []
  let mut templateUnion : List Nat := []
  let mut outcomes : List String := []
  let mut transactionTotal := 0
  for entry in entries do
    let identifier ← string entry "id"
    require (!identifiers.contains identifier) ("duplicate forwarded-value corpus id " ++ identifier)
    identifiers := identifier :: identifiers
    let saved ← entryCase entry fuel
    require ((← ForwardedCall.replayCase saved fuel) == saved) ("forwarded-value corpus entry did not replay: " ++ identifier)
    let scenario ← ForwardedCall.caseProgram saved
    if !(entry.getObjVal? "generation").isOk then
      require ((← saved.getObjVal? "forwardPlan") == (← entry.getObjVal? "forwardPlan") &&
        (← saved.getObjVal? "transactions") == (← entry.getObjVal? "transactions"))
        ("imported forwarded-value entry is not canonical: " ++ identifier)
    let caseFeatures := (← (← saved.getObjVal? "provenance").getObjValAs? (List String) "features").eraseDups
    require (sameMembers (← strings entry "expectedFeatures") caseFeatures)
      ("forwarded-value corpus features changed: " ++ identifier)
    let history := ForwardedCall.observe scenario Solcore.Synthesis.Stateful.NestedCallExecution.fixtureBindings fuel
    let statuses ← ForwardedCall.checkProtocol scenario history
    let observed ← history.getObjValAs? (List Json) "transactions"
    let expected ← entry.getObjValAs? (List Json) "expectedHistory"
    require (observed.length == expected.length) ("forwarded-value expected history length changed: " ++ identifier)
    for ((row, golden), tx) in (observed.zip expected).zip scenario.transactions do
      let actual := Json.mkObj [("id", ← row.getObjVal? "id"), ("status", ← row.getObjVal? "status"),
        ("output", ← row.getObjVal? "output"), ("committedAccounts", ← row.getObjVal? "committedAccounts"),
        ("logs", ← row.getObjVal? "logs")]
      require (actual == golden) ("original Core differs from the independent history: " ++ identifier ++ " " ++ actual.compress)
      inputs := (inputs ++ [toString tx.input.val]).eraseDups
      modes := (modes ++ [tx.input.val % 4]).eraseDups
      values := (values ++ [toString tx.value.val]).eraseDups
      amounts := (amounts ++ [toString tx.amount.val]).eraseDups
      let status ← string row "status"
      if status == "returned" && ForwardedCall.childReverts tx then
        refunded := (refunded ++ [toString tx.amount.val]).eraseDups
      if status == "reverted" then
        reverted := (reverted ++ [toString tx.value.val]).eraseDups
    transactionTotal := transactionTotal + observed.length
    features := (features ++ caseFeatures).eraseDups
    helperCounts := (helperCounts ++ [scenario.plan.step.helpers.length]).eraseDups
    transactionCounts := (transactionCounts ++ [scenario.transactions.length]).eraseDups
    templateUnion := (templateUnion ++ (← templates saved)).eraseDups
    outcomes := (outcomes ++ statuses).eraseDups
  require (requiredFeatures.all features.contains) "forwarded-value corpus misses a required step feature"
  require (requiredInputs.all inputs.contains && [0, 1, 2, 3].all modes.contains)
    "forwarded-value corpus misses an input or call mode"
  require ((words ForwardedCall.valueBank).all values.contains && (words ForwardedCall.valueBank).all amounts.contains)
    "forwarded-value corpus misses a call value or amount"
  require (requiredRefunded.all refunded.contains && requiredReverted.all reverted.contains)
    "forwarded-value corpus misses a child-revert or root-revert refund"
  require ([1, 2, 3].all helperCounts.contains && [1, 2, 3].all transactionCounts.contains)
    "forwarded-value corpus misses a helper or transaction count"
  require ([0, 1, 2, 3].all templateUnion.contains) "forwarded-value corpus misses a generated template"
  require (["returned", "reverted"].all outcomes.contains) "forwarded-value corpus misses an observed outcome"
  return Json.mkObj [("profile", toJson "stateful-forwarded-value"), ("scenarios", toJson entries.size),
    ("transactions", toJson transactionTotal), ("refundedForwards", toJson refunded), ("revertedValues", toJson reverted)]

private def checked {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def rejects {α : Type} (result : Except String α) (message : String) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError ("invalid forwarded-value corpus unexpectedly passed: " ++ message))

def testSourceForwardedCallCorpus : IO Unit := do
  let manifest ← checked (Json.parse (← IO.FS.readFile "scripts/semantic-forward-corpus.json"))
  let summary ← checked (validateManifest manifest)
  let entries ← checked (manifest.getObjValAs? (Array Json) "cases")
  let some first := entries[0]? | throw (IO.userError "missing first forwarded-value case")
  let some generatedEntry := entries.find? (fun entry => (entry.getObjVal? "generation").isOk) |
    throw (IO.userError "missing generated forwarded-value case")
  let replace := fun (original changed : Json) => manifest.setObjVal! "cases"
    (.arr (entries.map fun entry => if entry == original then changed else entry))
  let history ← checked (first.getObjValAs? (Array Json) "expectedHistory")
  let withRow := fun (index : Nat) (row : Json) =>
    replace first (first.setObjVal! "expectedHistory" (.arr (history.set! index row)))
  let row := history[0]!
  rejects (validateManifest (withRow 0 (row.setObjVal! "output" (toJson ("0x" ++ String.ofList (List.replicate 64 'f'))))))
    "changed output"
  let accounts ← checked (row.getObjValAs? (Array Json) "committedAccounts")
  let withAccount := fun (index : Nat) (row : Json) (role : Nat) (account : Json) => do
    let rowAccounts ← checked (row.getObjValAs? (Array Json) "committedAccounts")
    pure (withRow index (row.setObjVal! "committedAccounts" (.arr (rowAccounts.set! role account))))
  rejects (validateManifest (← withAccount 0 row 1 (accounts[1]!.setObjVal! "balance" (toJson "6")))) "changed child balance"
  rejects (validateManifest (← withAccount 0 row 0 (accounts[0]!.setObjVal! "balance" (toJson "8")))) "changed parent balance"
  rejects (validateManifest (withRow 0 (row.setObjVal! "logs" (toJson [Json.mkObj [("address", toJson "101")]])))) "invented log"
  -- The first scenario's second transaction reverts its child: committing the
  -- forwarded 2^70 to the child is wrong.
  let childRevert := history[1]!
  let childAccounts ← checked (childRevert.getObjValAs? (Array Json) "committedAccounts")
  rejects (validateManifest (← withAccount 1 childRevert 1 (childAccounts[1]!.setObjVal! "balance"
    (toJson (toString (5 + 2 ^ 70)))))) "a child-reverted forward committed"
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr history.pop)))) "popped history"
  let generatedHistory ← checked (generatedEntry.getObjValAs? (Array Json) "expectedHistory")
  let generatedStatus ← checked (generatedHistory[0]!.getObjValAs? String "status")
  rejects (validateManifest (replace generatedEntry (generatedEntry.setObjVal! "expectedHistory"
    (.arr (generatedHistory.set! 0 (generatedHistory[0]!.setObjVal! "status"
      (toJson (if generatedStatus == "returned" then "reverted" else "returned")))))))) "flipped status"
  let transactions ← checked (first.getObjValAs? (Array Json) "transactions")
  rejects (validateManifest (replace first (first.setObjVal! "transactions"
    (.arr (transactions.set! 0 (transactions[0]!.setObjVal! "amount" (toJson "7"))))))) "changed amount"
  rejects (validateManifest (replace first (first.setObjVal! "transactions"
    (.arr (transactions.set! 0 (transactions[0]!.setObjVal! "value" (toJson "1"))))))) "changed call value"
  rejects (validateManifest (replace first (first.setObjVal! "expectedFeatures" (toJson ([] : List String))))) "features"
  rejects (validateManifest (replace generatedEntry (generatedEntry.setObjVal! "generation"
    (Json.mkObj [("seed", toJson "13"), ("maxProgramNodes", toJson (384 : Nat))])))) "changed seed"
  rejects (validateManifest (manifest.setObjVal! "cases" (.arr (entries.push first)))) "duplicate entry"
  for (key, value) in [
      ("profile", toJson "stateful-calls"), ("wrapperVersion", toJson "forged"),
      ("cases", .arr #[]), ("requiredInputs", toJson ([] : List String)), ("requiredHelperCounts", toJson [1, 2]),
      ("requiredCallModes", toJson [0, 1, 2]), ("requiredValues", toJson (["0", "1"] : List String)),
      ("requiredForwardedValues", toJson (["0"] : List String)),
      ("requiredRefundedForwards", toJson (["0", "1", "7"] : List String)),
      ("requiredRevertedValues", toJson (["1", "7", "5"] : List String))] do
    rejects (validateManifest (manifest.setObjVal! key value)) key
  rejects (validateManifest manifest 0) "zero fuel"
  IO.println summary.compress

end Tests.SourceForwardedCallCorpus
