import Solcore.Synthesis.Source.ConstructorArgumentsCases

/-! The fixed constructor-argument corpus checks actual original Core histories
against expectations computed without the Core contracts: std's decision on
the argument bytes, the constructor's writes and the source model, in which
each step runs alone in Core. Coverage describes the checked steps' AST, the
inputs, every parameter kind with static and dynamic enums apart, every
malformation kind, the three deployment outcomes, the malformations std
accepted, the bank's `bytes` lengths and every decoded enum field kind of
accepted deployments, the runtime carries after a committed transaction and
past a revert, the node budgets of generated entries and the completions.
Source/Rust/EVM agreement is a separate external validation. -/
set_option autoImplicit false

namespace Tests.SourceConstructorArgumentCorpus
open Lean Solcore.Core Solcore.Synthesis.Core Solcore.Synthesis.Source
open Solcore.Synthesis.Core.ConstructorArguments (Parameters)
open Solcore.Synthesis.Core.EnumArgument (Payload)

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
  ("generatorVersion", generatorVersion), ("profileVersion", ConstructorArguments.profileVersion),
  ("functionVersion", Solcore.Synthesis.Core.ConstructorArguments.runtimeVersion),
  ("initializerVersion", Solcore.Synthesis.Core.ConstructorArguments.initializerVersion),
  ("templateVersion", ConstructorArguments.templateVersion), ("stepProfileVersion", Aggregate.profileVersion),
  ("stepFunctionVersion", Aggregates.version), ("stepTemplateVersion", Aggregate.templateVersion),
  ("emitterVersion", ConstructorArguments.emitterVersion), ("wrapperVersion", ConstructorArguments.wrapperVersion)]

private def words (values : List Word) : List String := values.map fun value => toString value.val

/-- The parameter kinds, an enum by its class. -/
def parameterClass : Parameters → String
  | .enum shape => if shape.dynamic then "dynamic" else "static"
  | parameters => parameters.name

def parameterClasses : List String := ["none", "uint256", "uint256,uint256", "uint256,bytes", "static", "dynamic"]

/-- std's three deployment outcomes. -/
def outcomes : List String := ["deployed", "0x08638556", "0x"]

/-- The malformations std can accept; an unknown tag never deploys. -/
def acceptedKinds : List String := ["truncate", "trailing", "offset", "length", "tail", "narrow"]

def fieldName : Payload → String
  | .noWords => "none"
  | .oneWord => "one"
  | .twoWords => "two"
  | .pair => "pair"
  | .bytes => "bytes"

/-- Static enums decode Word fields and the struct, dynamic ones any field. -/
def fieldKinds : List String :=
  ["static:none", "static:one", "static:two", "static:pair", "dynamic:none", "dynamic:one", "dynamic:two",
    "dynamic:pair", "dynamic:bytes"]

/-- Imported entries are emitted from their saved plan, deployment and
sequence; generated entries are regenerated from their seed. Both are checked
by full replay. -/
private def entryCase (entry : Json) (fuel : Nat) : Except String Json := do
  if let .ok request := entry.getObjVal? "generation" then
    let some seed := (← request.getObjValAs? String "seed").toNat? | throw "invalid generation seed"
    let corpus := ConstructorArguments.generateCases (Seed.ofNat seed) (← request.getObjValAs? Nat "maxProgramNodes") 1 1 fuel
    require ((← string corpus "status") == "complete") "generated entry was excluded"
    let some saved := (← corpus.getObjValAs? (Array Json) "cases")[0]? | throw "generated entry has no case"
    return saved
  let plan ← ConstructorArguments.checkedPlan (← entry.getObjVal? "constructorArgumentsPlan")
  let scenario ← ConstructorArguments.checkedScenario plan
    (← ConstructorArguments.decodeDeployment plan.parameters (← entry.getObjVal? "deployment"))
    (← ConstructorArguments.decodeTransactions (← entry.getObjVal? "transactions"))
  ConstructorArguments.emitCase scenario (Json.mkObj [("kind", toJson "imported")]) fuel

private def templates (saved : Json) : Except String (List Nat) := do
  let origin ← (← saved.getObjVal? "provenance").getObjVal? "origin"
  if (← string origin "kind") != "constructor-argument-generated" then return []
  let helpers ← (← origin.getObjVal? "stepOrigin").getObjValAs? (List Json) "helpers"
  helpers.mapM fun helper => helper.getObjValAs? Nat "template"

private def slotsJson (values : List Word) : Json :=
  toJson (values.zipIdx.map fun (value, slot) => Json.mkObj [
    ("slot", toJson (toString slot)), ("value", toJson (toString value.val))])

/-- The source model's rows of a scenario, in the corpus's expected-row form:
the deployment's status, std's revert data or null, and slots zero to five,
then each transaction's row. -/
def modelRows (scenario : ConstructorArguments.CheckedScenario) (fuel : Nat) : Except String (Json × List Json) := do
  let some (deployment, rows) := Solcore.Synthesis.Stateful.ConstructorArgumentsExecution.model scenario.plan.step fuel
      scenario.plan.parameters scenario.deployment scenario.transactions | throw "the source model failed"
  return (Json.mkObj [
      ("status", toJson (if deployment.reverted then "reverted" else "returned")),
      ("revertData", if deployment.reverted then toJson (Solcore.ContractRuntime.encodeBytesText deployment.output)
        else Json.null),
      ("committedStorage", slotsJson deployment.slots)],
    (rows.zip scenario.transactions).map fun (row, transaction) => Json.mkObj [
      ("id", toJson transaction.id), ("status", toJson (if row.reverted then "reverted" else "returned")),
      ("output", toJson (Solcore.ContractRuntime.encodeBytesText row.output)),
      ("committedStorage", slotsJson row.slots)])

/-- Original Core's output for an expected deployment row: the Word zero on
return, and on a revert the selector Word for std's four bytes or the Word
zero for none. -/
private def coreDeploymentOutput (expected : Json) : Except String String := do
  let zero := Solcore.ContractRuntime.encodeBytesText (Solcore.ContractRuntime.encodeWordBytesBE Word.zero)
  match ← expected.getObjVal? "revertData" with
  | .null => return zero
  | data => do
      let text ← data.getStr?
      if text == "0x" then return zero
      require (text.length == 10) "unexpected std revert data"
      return "0x" ++ String.ofList (List.replicate 56 '0') ++ text.drop 2

def validateManifest (manifest : Json) (fuel : Nat := 1000000) : Except String Json := do
  require ((← string manifest "schema") == "solcore-lean.semantic-storage-corpus-manifest.v1" &&
    (← string manifest "profile") == "stateful-constructor-arguments" &&
    (← string manifest "coverageKind") == "step-core-ast-features") "unexpected constructor-argument manifest scope"
  for (key, expected) in versions do
    require ((← string manifest key) == expected) ("constructor-argument manifest changed " ++ key)
  let requiredFeatures ← strings manifest "requiredFeatures"
  let requiredInputs ← strings manifest "requiredInputs"
  require (sameMembers requiredInputs (words ConstructorArguments.boundaryInputs))
    "constructor-argument corpus must require all six boundary inputs"
  require ((← strings manifest "requiredConstructorParameters") == parameterClasses &&
    (← strings manifest "requiredConstructorMalformations") == ConstructorArguments.malformationKinds &&
    (← strings manifest "requiredConstructorOutcomes") == outcomes &&
    (← strings manifest "requiredConstructorAccepted") == acceptedKinds)
    "constructor-argument corpus must require every parameter kind, malformation, outcome and accepted malformation"
  require ((← manifest.getObjValAs? (List Nat) "requiredConstructorBytesLengths") == ConstructorArguments.lengthBank &&
    (← strings manifest "requiredConstructorEnumFields") == fieldKinds &&
    (← manifest.getObjValAs? (List Nat) "requiredConstructorNodeBudgets") == [384, 512])
    "constructor-argument corpus must require the bank's bytes lengths, every enum field kind and both node budgets"
  require ((← strings manifest "requiredConstructorCarries") == ["committed", "rollback"])
    "constructor-argument corpus must require carries from a committed transaction and past a revert"
  require ((← manifest.getObjValAs? (List Nat) "requiredHelperCounts") == [1, 2, 3] &&
    (← manifest.getObjValAs? (List Nat) "requiredTransactionCounts") == [0, 1, 2, 3])
    "constructor-argument corpus must require one to three helpers and zero to three transactions"
  require ((← (← manifest.getObjVal? "generationRecipeRequirements").getObjValAs? (List Nat) "templates") == [0, 1, 2, 3])
    "constructor-argument corpus must require all four step templates"
  require ((← strings manifest "requiredOutcomes") == ["returned", "reverted"])
    "constructor-argument corpus must require both transaction outcomes"
  let requiredPatterns ← strings manifest "requiredCompletionPatterns"
  require (!requiredPatterns.isEmpty) "constructor-argument corpus must require completion patterns"
  let entries ← manifest.getObjValAs? (Array Json) "cases"
  require (0 < entries.size && entries.size ≤ 64) "constructor-argument corpus must contain 1..64 scenarios"
  let mut identifiers : List String := []
  let mut features : List String := []
  let mut inputs : List String := []
  let mut classes : List String := []
  let mut kinds : List String := []
  let mut deploymentOutcomes : List String := []
  let mut accepted : List String := []
  let mut bytesLengths : List Nat := []
  let mut fields : List String := []
  let mut carries : List String := []
  let mut budgets : List Nat := []
  let mut helperCounts : List Nat := []
  let mut transactionCounts : List Nat := []
  let mut templateUnion : List Nat := []
  let mut statusesSeen : List String := []
  let mut patterns : List String := []
  let mut transactionTotal := 0
  for entry in entries do
    let identifier ← string entry "id"
    require (!identifiers.contains identifier) ("duplicate constructor-argument corpus id " ++ identifier)
    identifiers := identifier :: identifiers
    let saved ← entryCase entry fuel
    require ((← ConstructorArguments.replayCase saved fuel) == saved)
      ("constructor-argument corpus entry did not replay: " ++ identifier)
    let scenario ← ConstructorArguments.caseProgram saved
    if let .ok request := entry.getObjVal? "generation" then
      budgets := (budgets ++ [← request.getObjValAs? Nat "maxProgramNodes"]).eraseDups
    else
      require ((← saved.getObjVal? "constructorArgumentsPlan") == (← entry.getObjVal? "constructorArgumentsPlan") &&
        (← saved.getObjVal? "deployment") == (← entry.getObjVal? "deployment") &&
        (← saved.getObjVal? "transactions") == (← entry.getObjVal? "transactions"))
        ("imported constructor-argument entry is not canonical: " ++ identifier)
    let caseFeatures := (← (← saved.getObjVal? "provenance").getObjValAs? (List String) "features").eraseDups
    require (sameMembers (← strings entry "expectedFeatures") caseFeatures)
      ("constructor-argument corpus features changed: " ++ identifier)
    let expectedDeployment ← entry.getObjVal? "expectedDeployment"
    let expected ← entry.getObjValAs? (List Json) "expectedHistory"
    require ((expectedDeployment, expected) == (← modelRows scenario fuel))
      ("the expected history differs from the source model: " ++ identifier)
    let history := ConstructorArguments.observe scenario Solcore.Synthesis.Stateful.StorageExecution.fixtureBindings fuel
    require ((← string history "status") == "complete") ("constructor-argument corpus history incomplete: " ++ identifier)
    let deployment ← history.getObjVal? "deployment"
    require ((← deployment.getObjVal? "status") == (← expectedDeployment.getObjVal? "status") &&
      (← string deployment "output") == (← coreDeploymentOutput expectedDeployment) &&
      (← deployment.getObjVal? "committedStorage") == (← expectedDeployment.getObjVal? "committedStorage"))
      ("original Core's deployment differs from std's decision: " ++ identifier ++ " " ++ deployment.compress)
    let observed ← history.getObjValAs? (List Json) "transactions"
    require (observed.length == expected.length)
      ("constructor-argument expected history length changed: " ++ identifier)
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
    let parameters := scenario.plan.parameters
    let record := scenario.deployment
    let outcome := (ConstructorArguments.prescribed parameters record).getD "deployed"
    let kind := ConstructorArguments.kindOf record.malformation
    classes := (classes ++ [parameterClass parameters]).eraseDups
    kinds := (kinds ++ [kind]).eraseDups
    deploymentOutcomes := (deploymentOutcomes ++ [outcome]).eraseDups
    if outcome == "deployed" then
      if kind != "none" then accepted := (accepted ++ [kind]).eraseDups
      if Solcore.Synthesis.Stateful.ConstructorArgumentsExecution.carriesBytes parameters record then
        bytesLengths := (bytesLengths ++ [record.length]).eraseDups
      if let .enum shape := parameters then
        let chosen := Solcore.Synthesis.Stateful.ConstructorArgumentsExecution.chosen shape record
        fields := (fields ++ [parameterClass parameters ++ ":" ++ fieldName chosen.payload]).eraseDups
    for (status, index) in statuses.zipIdx do
      if status == "returned" && (statuses.take index).contains "returned" then
        carries := (carries ++ ["committed"]).eraseDups
      if status == "returned" && (statuses.take index).contains "reverted" then
        carries := (carries ++ ["rollback"]).eraseDups
    helperCounts := (helperCounts ++ [scenario.plan.step.helpers.length]).eraseDups
    transactionCounts := (transactionCounts ++ [scenario.transactions.length]).eraseDups
    templateUnion := (templateUnion ++ (← templates saved)).eraseDups
    statusesSeen := (statusesSeen ++ statuses).eraseDups
    if !statuses.isEmpty then patterns := (patterns ++ [String.intercalate "," statuses]).eraseDups
  require (requiredFeatures.all features.contains) "constructor-argument corpus misses a required step feature"
  require (requiredInputs.all inputs.contains) "constructor-argument corpus misses a boundary input"
  require (parameterClasses.all classes.contains && ConstructorArguments.malformationKinds.all kinds.contains)
    "constructor-argument corpus misses a parameter kind or a malformation"
  require (outcomes.all deploymentOutcomes.contains && acceptedKinds.all accepted.contains)
    "constructor-argument corpus misses a deployment outcome or an accepted malformation"
  require (ConstructorArguments.lengthBank.all bytesLengths.contains && fieldKinds.all fields.contains)
    "constructor-argument corpus misses a deployed bytes length or enum field kind"
  require (["committed", "rollback"].all carries.contains && [384, 512].all budgets.contains)
    "constructor-argument corpus misses a carry or a node budget"
  require ([1, 2, 3].all helperCounts.contains && [0, 1, 2, 3].all transactionCounts.contains)
    "constructor-argument corpus misses a helper or transaction count"
  require ([0, 1, 2, 3].all templateUnion.contains) "constructor-argument corpus misses a generated template"
  require (["returned", "reverted"].all statusesSeen.contains && requiredPatterns.all patterns.contains)
    "constructor-argument corpus misses an observed outcome or completion pattern"
  return Json.mkObj [("profile", toJson "stateful-constructor-arguments"), ("scenarios", toJson entries.size),
    ("transactions", toJson transactionTotal), ("parameters", toJson classes),
    ("malformations", toJson kinds), ("outcomes", toJson deploymentOutcomes), ("accepted", toJson accepted),
    ("bytesLengths", toJson bytesLengths), ("fields", toJson fields), ("carries", toJson carries),
    ("nodeBudgets", toJson budgets), ("patterns", toJson patterns)]

private def checked {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def rejects {α : Type} (result : Except String α) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "invalid constructor-argument corpus unexpectedly passed")

def testSourceConstructorArgumentCorpus : IO Unit := do
  let manifest ← checked (Json.parse (← IO.FS.readFile "scripts/semantic-constructor-argument-corpus.json"))
  let summary ← checked (validateManifest manifest)
  let entries ← checked (manifest.getObjValAs? (Array Json) "cases")
  let some generatedEntry := entries.find? (fun entry => (entry.getObjVal? "generation").isOk) |
    throw (IO.userError "missing generated constructor-argument case")
  -- An imported deployed `bytes` entry whose first transaction returns, and a
  -- rejected one.
  let some first := entries.find? (fun entry => (entry.getObjVal? "constructorArgumentsPlan").toOption.any (fun plan =>
      (plan.getObjValAs? String "parameters").toOption == some "uint256,bytes") &&
      (entry.getObjVal? "expectedDeployment").toOption.any (fun row =>
        (row.getObjValAs? String "status").toOption == some "returned") &&
      (entry.getObjValAs? (Array Json) "expectedHistory").toOption.any (fun history =>
        history[0]?.any (fun row => (row.getObjValAs? String "status").toOption == some "returned"))) |
    throw (IO.userError "missing imported deployed bytes case")
  let some rejected := entries.find? (fun entry => (entry.getObjVal? "constructorArgumentsPlan").isOk &&
      (entry.getObjVal? "expectedDeployment").toOption.any (fun row =>
        (row.getObjValAs? String "revertData").toOption == some "0x08638556")) |
    throw (IO.userError "missing rejected case")
  let replace := fun (original changed : Json) => manifest.setObjVal! "cases"
    (.arr (entries.map fun entry => if entry == original then changed else entry))
  -- A deployment's status, revert data and slots, a transaction's output, slot
  -- and status, and a missing row are all checked.
  let deployment ← checked (first.getObjVal? "expectedDeployment")
  rejects (validateManifest (replace first (first.setObjVal! "expectedDeployment"
    (deployment.setObjVal! "status" (toJson "reverted")))))
  rejects (validateManifest (replace first (first.setObjVal! "expectedDeployment"
    (deployment.setObjVal! "revertData" (toJson "0x08638556")))))
  let storage ← checked (deployment.getObjValAs? (Array Json) "committedStorage")
  rejects (validateManifest (replace first (first.setObjVal! "expectedDeployment"
    (deployment.setObjVal! "committedStorage" (.arr (storage.set! 1 (storage[1]!.setObjVal! "value" (toJson "12345"))))))))
  let rejection ← checked (rejected.getObjVal? "expectedDeployment")
  rejects (validateManifest (replace rejected (rejected.setObjVal! "expectedDeployment"
    (rejection.setObjVal! "revertData" (toJson "0x")))))
  let history ← checked (first.getObjValAs? (Array Json) "expectedHistory")
  let row := history[0]!
  let output ← checked (row.getObjValAs? String "output")
  let changedOutput := row.setObjVal! "output" (toJson (String.ofList (output.toList.take (output.length - 1)) ++
    (if output.endsWith "1" then "2" else "1")))
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr (history.set! 0 changedOutput)))))
  let rowStorage ← checked (row.getObjValAs? (Array Json) "committedStorage")
  let slotTwo := (rowStorage[2]!.getObjValAs? String "value").toOption
  let changedSlot := row.setObjVal! "committedStorage" (.arr (rowStorage.set! 2
    (rowStorage[2]!.setObjVal! "value" (toJson (if slotTwo == some "7" then "8" else "7")))))
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr (history.set! 0 changedSlot)))))
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr (history.pop)))))
  let generatedHistory ← checked (generatedEntry.getObjValAs? (Array Json) "expectedHistory")
  if let some head := generatedHistory[0]? then
    let flipped := if (head.getObjValAs? String "status").toOption == some "returned" then "reverted" else "returned"
    rejects (validateManifest (replace generatedEntry (generatedEntry.setObjVal! "expectedHistory"
      (.arr (generatedHistory.set! 0 (head.setObjVal! "status" (toJson flipped)))))))
  -- The record is checked against its arguments, and a rejected deployment
  -- against any transaction after it.
  let record ← checked (first.getObjVal? "deployment")
  rejects (validateManifest (replace first (first.setObjVal! "deployment" (record.setObjVal! "a" (toJson "12345")))))
  rejects (validateManifest (replace rejected (rejected.setObjVal! "transactions" (first.getObjValD "transactions"))))
  rejects (validateManifest (replace first (first.setObjVal! "expectedFeatures" (toJson ([] : List String)))))
  rejects (validateManifest (manifest.setObjVal! "cases" (.arr (entries.push first))))
  for (key, value) in [
      ("profile", toJson "stateful-storage"), ("initializerVersion", toJson "forged"),
      ("cases", .arr #[]), ("requiredInputs", toJson ([] : List String)),
      ("requiredConstructorParameters", toJson (["none"] : List String)),
      ("requiredConstructorMalformations", toJson (["none"] : List String)),
      ("requiredConstructorOutcomes", toJson (["deployed"] : List String)),
      ("requiredConstructorAccepted", toJson (["trailing"] : List String)),
      ("requiredConstructorBytesLengths", toJson [0, 1, 32]),
      ("requiredConstructorEnumFields", toJson (["static:none"] : List String)),
      ("requiredConstructorNodeBudgets", toJson [384]),
      ("requiredConstructorCarries", toJson (["committed"] : List String)),
      ("requiredHelperCounts", toJson [1, 2]), ("requiredTransactionCounts", toJson [1, 2, 3]),
      ("requiredCompletionPatterns", toJson (["returned,returned,returned,returned"] : List String))] do
    rejects (validateManifest (manifest.setObjVal! key value))
  rejects (validateManifest manifest 0)
  IO.println summary.compress

end Tests.SourceConstructorArgumentCorpus
