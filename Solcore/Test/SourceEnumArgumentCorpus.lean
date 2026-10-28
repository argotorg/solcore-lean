import Solcore.Synthesis.Source.EnumArgumentCases

/-! The fixed enum-argument corpus checks actual original Core histories against
expectations computed without the Core contract: the Lean model, std's decision
over the calldata bytes and the protocol, in which each step runs alone in
Core. Coverage describes the checked steps' AST, the field Words, the decoded
constructors' positions and fields, the decoded `bytes` lengths, the shapes'
`bytes` constructor counts, every malformation kind with the accepted ones,
every std rejection, the carries into a decoded value from an earlier
committed, reverted or rejected transaction, the node budgets of generated
entries and the completions. Source/Rust/EVM agreement is a separate external
validation. -/
set_option autoImplicit false

namespace Tests.SourceEnumArgumentCorpus
open Lean Solcore.Core Solcore.Synthesis.Core Solcore.Synthesis.Source
open Solcore.Synthesis.Core.EnumArgument (Payload Shape)

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
  ("generatorVersion", generatorVersion), ("profileVersion", EnumArgument.profileVersion),
  ("functionVersion", Solcore.Synthesis.Core.EnumArgument.version),
  ("templateVersion", EnumArgument.templateVersion), ("stepProfileVersion", Aggregate.profileVersion),
  ("stepFunctionVersion", Aggregates.version), ("stepTemplateVersion", Aggregate.templateVersion),
  ("emitterVersion", EnumArgument.emitterVersion), ("wrapperVersion", EnumArgument.wrapperVersion)]

private def words (values : List Word) : List String := values.map fun value => toString value.val

/-- Every position of every constructor count. -/
def positions : List String :=
  [2, 3, 4].flatMap fun count => (List.range count).map fun position => s!"{count}:{position}"

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

/-- std's three rejections: the fallback, a truncated read, an unknown tag. -/
def rejections : List String := ["0x4924aef0", "0x08638556", "0x"]

/-- The malformations that std accepts in some case. -/
def acceptedKinds : List String := ["trailing", "unused", "truncate", "padding", "retag", "aliased", "length"]

/-- A decoded value after an earlier committed transaction, body revert or
rejection. -/
def carries : List String := ["committed", "rollback", "rejection"]

private def kind (shape : Shape) : String := if shape.dynamic then "dynamic" else "static"

/-- Imported entries are emitted from their saved plan and sequence; generated
entries are regenerated from their seed. Both are checked by full replay. -/
private def entryCase (entry : Json) (fuel : Nat) : Except String Json := do
  if let .ok request := entry.getObjVal? "generation" then
    let some seed := (← request.getObjValAs? String "seed").toNat? | throw "invalid generation seed"
    let corpus := EnumArgument.generateCases (Seed.ofNat seed) (← request.getObjValAs? Nat "maxProgramNodes") 1 1 fuel
    require ((← string corpus "status") == "complete") "generated entry was excluded"
    let some saved := (← corpus.getObjValAs? (Array Json) "cases")[0]? | throw "generated entry has no case"
    return saved
  let plan ← EnumArgument.checkedPlan (← entry.getObjVal? "enumArgumentPlan")
  let scenario ← EnumArgument.checkedScenario plan
    (← EnumArgument.decodeTransactions plan.shape (← entry.getObjVal? "transactions"))
  EnumArgument.emitCase scenario (Json.mkObj [("kind", toJson "imported")]) fuel

private def templates (saved : Json) : Except String (List Nat) := do
  let origin ← (← saved.getObjVal? "provenance").getObjVal? "origin"
  if (← string origin "kind") != "enum-argument-generated" then return []
  let helpers ← (← origin.getObjVal? "stepOrigin").getObjValAs? (List Json) "helpers"
  helpers.mapM fun helper => helper.getObjValAs? Nat "template"

/-- Original Core's output for std's data: the selector Word for four bytes,
the Word zero for none. -/
private def coreOutput (output : ByteArray) : String :=
  if output.size == 4 then
    Solcore.ContractRuntime.encodeBytesText (Solcore.ContractRuntime.encodeWordBytesBE
      (Word.ofNatModulo (Solcore.Synthesis.Stateful.StdCalldata.bigEndian output 0 4)))
  else if output.size == 0 then
    Solcore.ContractRuntime.encodeBytesText (Solcore.ContractRuntime.encodeWordBytesBE Word.zero)
  else Solcore.ContractRuntime.encodeBytesText output

/-- The Lean model's rows of a scenario, in the corpus's expected-row form:
original Core's revert Word for a rejection. -/
def modelRows (scenario : EnumArgument.CheckedScenario) (fuel : Nat) : Except String (List Json) := do
  let some rows := Solcore.Synthesis.Stateful.EnumArgumentExecution.model scenario.plan.step
      scenario.plan.shape fuel scenario.transactions | throw "the Lean model failed"
  return (rows.zip scenario.transactions).map fun (row, transaction) => Json.mkObj [
    ("id", toJson transaction.id), ("status", toJson (if row.reverted then "reverted" else "returned")),
    ("output", toJson (coreOutput row.output)),
    ("committedStorage", toJson (row.slots.zipIdx.map fun (value, slot) => Json.mkObj [
      ("slot", toJson (toString slot)), ("value", toJson (toString value.val))]))]

def validateManifest (manifest : Json) (fuel : Nat := 1000000) : Except String Json := do
  require ((← string manifest "schema") == "solcore-lean.semantic-storage-corpus-manifest.v1" &&
    (← string manifest "profile") == "stateful-enum-arguments" &&
    (← string manifest "coverageKind") == "step-core-ast-features") "unexpected enum-argument manifest scope"
  for (key, expected) in versions do
    require ((← string manifest key) == expected) ("enum-argument manifest changed " ++ key)
  let requiredFeatures ← strings manifest "requiredFeatures"
  require (sameMembers (← strings manifest "requiredInputs") (words EnumArgument.boundaryInputs))
    "enum-argument corpus must require all six boundary Words as fields"
  require ((← strings manifest "requiredArgumentPositions") == positions &&
    (← strings manifest "requiredArgumentFields") == fieldKinds)
    "enum-argument corpus must require every decoded position and field kind"
  require ((← manifest.getObjValAs? (List Nat) "requiredArgumentBytesLengths") == EnumArgument.lengthBank &&
    (← manifest.getObjValAs? (List Nat) "requiredArgumentBytesConstructors") == [0, 1, 2] &&
    (← manifest.getObjValAs? (List Nat) "requiredArgumentNodeBudgets") == [384, 512])
    "enum-argument corpus must require the bank's bytes lengths, zero to two bytes constructors and both node budgets"
  require ((← strings manifest "requiredArgumentMalformations") == EnumArgument.malformationKinds &&
    (← strings manifest "requiredArgumentRejections") == rejections &&
    (← strings manifest "requiredArgumentAccepted") == acceptedKinds)
    "enum-argument corpus must require every malformation kind, every rejection and the accepted malformations"
  require ((← strings manifest "requiredArgumentCarries") == carries)
    "enum-argument corpus must require carries from a committed, a reverted and a rejected transaction"
  require ((← manifest.getObjValAs? (List Nat) "requiredHelperCounts") == [1, 2, 3] &&
    (← manifest.getObjValAs? (List Nat) "requiredTransactionCounts") == [1, 2, 3])
    "enum-argument corpus must require one to three helpers and transactions"
  require ((← (← manifest.getObjVal? "generationRecipeRequirements").getObjValAs? (List Nat) "templates") == [0, 1, 2, 3])
    "enum-argument corpus must require all four step templates"
  require ((← strings manifest "requiredOutcomes") == ["returned", "reverted"])
    "enum-argument corpus must require both outcomes"
  let requiredPatterns ← strings manifest "requiredCompletionPatterns"
  require (!requiredPatterns.isEmpty) "enum-argument corpus must require completion patterns"
  let entries ← manifest.getObjValAs? (Array Json) "cases"
  require (0 < entries.size && entries.size ≤ 64) "enum-argument corpus must contain 1..64 scenarios"
  let mut identifiers : List String := []
  let mut features : List String := []
  let mut fieldWords : List String := []
  let mut decodedPositions : List String := []
  let mut decodedFields : List String := []
  let mut bytesLengths : List Nat := []
  let mut bytesConstructors : List Nat := []
  let mut kinds : List String := []
  let mut rejected : List String := []
  let mut accepted : List String := []
  let mut carried : List String := []
  let mut budgets : List Nat := []
  let mut helperCounts : List Nat := []
  let mut transactionCounts : List Nat := []
  let mut templateUnion : List Nat := []
  let mut outcomes : List String := []
  let mut patterns : List String := []
  let mut transactionTotal := 0
  for entry in entries do
    let identifier ← string entry "id"
    require (!identifiers.contains identifier) ("duplicate enum-argument corpus id " ++ identifier)
    identifiers := identifier :: identifiers
    let saved ← entryCase entry fuel
    require ((← EnumArgument.replayCase saved fuel) == saved) ("enum-argument corpus entry did not replay: " ++ identifier)
    let scenario ← EnumArgument.caseProgram saved
    if let .ok request := entry.getObjVal? "generation" then
      budgets := (budgets ++ [← request.getObjValAs? Nat "maxProgramNodes"]).eraseDups
    else
      require ((← saved.getObjVal? "enumArgumentPlan") == (← entry.getObjVal? "enumArgumentPlan") &&
        (← saved.getObjVal? "transactions") == (← entry.getObjVal? "transactions"))
        ("imported enum-argument entry is not canonical: " ++ identifier)
    let caseFeatures := (← (← saved.getObjVal? "provenance").getObjValAs? (List String) "features").eraseDups
    require (sameMembers (← strings entry "expectedFeatures") caseFeatures)
      ("enum-argument corpus features changed: " ++ identifier)
    let expected ← entry.getObjValAs? (List Json) "expectedHistory"
    require (expected == (← modelRows scenario fuel))
      ("the expected history differs from the Lean model: " ++ identifier)
    let history := EnumArgument.observe scenario Solcore.Synthesis.Stateful.StorageExecution.fixtureBindings fuel
    require ((← string history "status") == "complete") ("enum-argument corpus history incomplete: " ++ identifier)
    let observed ← history.getObjValAs? (List Json) "transactions"
    require (observed.length == expected.length) ("enum-argument expected history length changed: " ++ identifier)
    let mut statuses : List String := []
    for (row, golden) in observed.zip expected do
      let actual := Json.mkObj [("id", ← row.getObjVal? "id"), ("status", ← row.getObjVal? "status"),
        ("output", ← row.getObjVal? "output"), ("committedStorage", ← row.getObjVal? "committedStorage")]
      require (actual == golden)
        ("original Core differs from the Lean model: " ++ identifier ++ " " ++ actual.compress)
      statuses := statuses ++ [← string row "status"]
    transactionTotal := transactionTotal + observed.length
    features := (features ++ caseFeatures).eraseDups
    let shape := scenario.plan.shape
    bytesConstructors := (bytesConstructors ++ [(shape.payloads.filter (· == .bytes)).length]).eraseDups
    -- Each transaction's decision, and what came before it.
    let mut before : List String := []
    for transaction in scenario.transactions do
      let malformation := EnumArgument.kindOf transaction.malformation
      kinds := (kinds ++ [malformation]).eraseDups
      let payload := (shape.payloads[transaction.choice]?).getD .noWords
      if payload != .bytes && payload != .noWords then
        fieldWords := (fieldWords ++ words [transaction.first] ++
          (if payload == .oneWord then [] else words [transaction.second])).eraseDups
      let input := Solcore.Synthesis.Stateful.EnumArgumentExecution.inputBytes shape transaction
      match Solcore.Synthesis.Stateful.EnumArgumentExecution.stdDecode shape input with
      | .error data =>
          rejected := (rejected ++ [Solcore.ContractRuntime.encodeBytesText data]).eraseDups
          before := before ++ ["rejection"]
      | .ok decoded =>
          let index := decoded.index - 1
          let decodedPayload := (shape.payloads[index]?).getD .noWords
          decodedPositions := (decodedPositions ++ [s!"{shape.constructors.length}:{index}"]).eraseDups
          decodedFields := (decodedFields ++ [kind shape ++ ":" ++ fieldName decodedPayload]).eraseDups
          if decodedPayload == .bytes then
            bytesLengths := (bytesLengths ++ [decoded.words.1.val]).eraseDups
          if malformation != "none" then accepted := (accepted ++ [malformation]).eraseDups
          if decoded.flags.val % 2 == 0 then
            carried := (carried ++ (["committed", "rollback", "rejection"].filter fun carry =>
              before.contains (if carry == "rollback" then "revert" else carry))).eraseDups
          before := before ++ [if decoded.flags.val % 2 == 0 then "committed" else "revert"]
    helperCounts := (helperCounts ++ [scenario.plan.step.helpers.length]).eraseDups
    transactionCounts := (transactionCounts ++ [scenario.transactions.length]).eraseDups
    templateUnion := (templateUnion ++ (← templates saved)).eraseDups
    outcomes := (outcomes ++ statuses).eraseDups
    patterns := (patterns ++ [String.intercalate "," statuses]).eraseDups
  require (requiredFeatures.all features.contains) "enum-argument corpus misses a required step feature"
  require ((words EnumArgument.boundaryInputs).all fieldWords.contains) "enum-argument corpus misses a boundary Word field"
  require (positions.all decodedPositions.contains && fieldKinds.all decodedFields.contains)
    "enum-argument corpus misses a decoded position or field kind"
  require (EnumArgument.lengthBank.all bytesLengths.contains && [0, 1, 2].all bytesConstructors.contains)
    "enum-argument corpus misses a decoded bytes length or a bytes constructor count"
  require (EnumArgument.malformationKinds.all kinds.contains && rejections.all rejected.contains &&
      acceptedKinds.all accepted.contains)
    "enum-argument corpus misses a malformation kind, a rejection or an accepted malformation"
  require (carries.all carried.contains && [384, 512].all budgets.contains)
    "enum-argument corpus misses a carry or a node budget"
  require ([1, 2, 3].all helperCounts.contains && [1, 2, 3].all transactionCounts.contains)
    "enum-argument corpus misses a helper or transaction count"
  require ([0, 1, 2, 3].all templateUnion.contains) "enum-argument corpus misses a generated template"
  require (["returned", "reverted"].all outcomes.contains && requiredPatterns.all patterns.contains)
    "enum-argument corpus misses an observed outcome or completion pattern"
  return Json.mkObj [("profile", toJson "stateful-enum-arguments"), ("scenarios", toJson entries.size),
    ("transactions", toJson transactionTotal), ("positions", toJson decodedPositions),
    ("fields", toJson decodedFields), ("bytesLengths", toJson bytesLengths),
    ("bytesConstructors", toJson bytesConstructors), ("malformations", toJson kinds),
    ("rejections", toJson rejected), ("accepted", toJson accepted), ("carries", toJson carried),
    ("nodeBudgets", toJson budgets), ("patterns", toJson patterns)]

private def checked {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def rejects {α : Type} (result : Except String α) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "invalid enum-argument corpus unexpectedly passed")

def testSourceEnumArgumentCorpus : IO Unit := do
  let manifest ← checked (Json.parse (← IO.FS.readFile "scripts/semantic-enum-argument-corpus.json"))
  let summary ← checked (validateManifest manifest)
  let entries ← checked (manifest.getObjValAs? (Array Json) "cases")
  let some first := entries[0]? | throw (IO.userError "missing first enum-argument case")
  let some generatedEntry := entries.find? (fun entry => (entry.getObjVal? "generation").isOk) |
    throw (IO.userError "missing generated enum-argument case")
  let replace := fun (original changed : Json) => manifest.setObjVal! "cases"
    (.arr (entries.map fun entry => if entry == original then changed else entry))
  let history ← checked (first.getObjValAs? (Array Json) "expectedHistory")
  -- A changed output Word, a slot, a missing row and a status are all checked.
  let row := history[0]!
  let output ← checked (row.getObjValAs? String "output")
  let changedOutput := row.setObjVal! "output" (toJson (String.ofList (output.toList.take (output.length - 2)) ++
    (if output.endsWith "01" then "02" else "01")))
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr (history.set! 0 changedOutput)))))
  let storage ← checked (row.getObjValAs? (Array Json) "committedStorage")
  let slotOne := (storage[1]!.getObjValAs? String "value").toOption
  let changedSlot := row.setObjVal! "committedStorage" (.arr (storage.set! 1
    (storage[1]!.setObjVal! "value" (toJson (if slotOne == some "1" then "2" else "1")))))
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr (history.set! 0 changedSlot)))))
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr (history.pop)))))
  let generatedHistory ← checked (generatedEntry.getObjValAs? (Array Json) "expectedHistory")
  let flipped := if (generatedHistory[0]!.getObjValAs? String "status").toOption == some "returned" then "reverted" else "returned"
  rejects (validateManifest (replace generatedEntry (generatedEntry.setObjVal! "expectedHistory"
    (.arr (generatedHistory.set! 0 (generatedHistory[0]!.setObjVal! "status" (toJson flipped)))))))
  -- A transaction's choice and malformation are checked against its calldata,
  -- and a constructor's name and fields against the plan.
  let transactions ← checked (first.getObjValAs? (Array Json) "transactions")
  let choice ← checked (transactions[0]!.getObjValAs? Nat "choice")
  rejects (validateManifest (replace first (first.setObjVal! "transactions" (.arr (transactions.set! 0
    (transactions[0]!.setObjVal! "choice" (toJson (if choice == 1 then 0 else 1))))))))
  rejects (validateManifest (replace first (first.setObjVal! "transactions" (.arr (transactions.set! 0
    (transactions[0]!.setObjVal! "malformation" (Json.mkObj [("kind", toJson "short"), ("bytes", toJson 2)])))))))
  let plan ← checked (first.getObjVal? "enumArgumentPlan")
  let constructors ← checked (plan.getObjValAs? (Array Json) "constructors")
  let renamed := constructors.set! 0 (constructors[0]!.setObjVal! "name" (toJson "Rejected"))
  -- The struct and two Words are the same on the wire and in Core, so the
  -- changed fields change the tag: none and one Word.
  let refielded := constructors.set! 0 (constructors[0]!.setObjVal! "fields"
    (toJson (if (constructors[0]!.getObjValAs? String "fields").toOption == some "" then "uint256" else "")))
  for changed in [renamed, refielded] do
    rejects (validateManifest (replace first (first.setObjVal! "enumArgumentPlan"
      (plan.setObjVal! "constructors" (.arr changed)))))
  rejects (validateManifest (replace first (first.setObjVal! "expectedFeatures" (toJson ([] : List String)))))
  rejects (validateManifest (manifest.setObjVal! "cases" (.arr (entries.push first))))
  for (key, value) in [
      ("profile", toJson "stateful-storage"), ("templateVersion", toJson "forged"),
      ("cases", .arr #[]), ("requiredInputs", toJson ([] : List String)),
      ("requiredArgumentPositions", toJson (["2:0"] : List String)),
      ("requiredArgumentFields", toJson (["static:none"] : List String)),
      ("requiredArgumentBytesLengths", toJson [0, 1, 32]), ("requiredArgumentBytesConstructors", toJson [1, 2]),
      ("requiredArgumentNodeBudgets", toJson [384]), ("requiredArgumentCarries", toJson (["committed"] : List String)),
      ("requiredArgumentMalformations", toJson (["none", "short"] : List String)),
      ("requiredArgumentRejections", toJson (["0x"] : List String)),
      ("requiredArgumentAccepted", toJson (["trailing"] : List String)),
      ("requiredHelperCounts", toJson [1, 2]),
      ("requiredCompletionPatterns", toJson (["returned,returned,returned,returned"] : List String))] do
    rejects (validateManifest (manifest.setObjVal! key value))
  rejects (validateManifest manifest 0)
  IO.println summary.compress

end Tests.SourceEnumArgumentCorpus
