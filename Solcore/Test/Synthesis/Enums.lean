import Solcore.Synthesis.Internal.EnumAbi
import Solcore.Synthesis.Internal.Enums

/-!
# Enum profile tests

Runtime enums: arguments, arrays and returns.
-/

section
-- leanmerge: from Solcore.Test.SourceEnumArgumentCases
/-! Generated enum-argument cases. The Core contract must equal the Lean model,
std's decision over the calldata bytes and the protocol, on every transaction
of the generated sequences, under the selector and empty-revert rules; each
case must replay to itself; the wrapper's node counts must be the ones the
definitions fix; generation must draw every constructor count, static and
dynamic shapes, every field kind, two `bytes` constructors, every position of
each count, every bank length, every malformation kind and every std outcome;
and every reduction must be a strictly smaller sealed case that replays. -/
set_option autoImplicit false

namespace Tests.SourceEnumArgumentCases

open Lean
open Solcore.Core (Word)
open Solcore.ContractRuntime
open Solcore.Synthesis.Core
open Solcore.Synthesis.Core.EnumArgument (Constructor Payload Shape)
open Solcore.Synthesis.Stateful
open Solcore.Synthesis.Stateful.EnumArgumentExecution (Transaction Malformation)

private abbrev Cases := Solcore.Synthesis.Source.EnumArgument.CheckedScenario

private def get {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def slots (values : List Word) : Json :=
  toJson ((values.zipIdx).map fun (value, slot) => Json.mkObj [
    ("slot", toJson (toString slot)), ("value", toJson (toString value.val))])

/-- Original Core's revert Word for std's revert data: the selector Word for
four bytes, the Word zero for none. -/
private def coreOutput (output : ByteArray) : String :=
  if output.size == 4 then
    encodeBytesText (encodeWordBytesBE (Word.ofNatModulo (StdCalldata.bigEndian output 0 4)))
  else if output.size == 0 then encodeBytesText (encodeWordBytesBE Word.zero)
  else encodeBytesText output

/-- The std outcome a model row stands for. -/
private def outcome (row : EnumArgumentExecution.ModelRow) : String :=
  if row.output.size == 4 then encodeBytesText row.output
  else if row.output.size == 0 then "empty"
  else if row.reverted then "body-revert" else "returned"

/-- The Core rows of a scenario equal the model's, transaction by transaction,
and each model row is std's prescribed outcome. -/
private def sameAsModel (scenario : Cases) (fuel : Nat) (name : String) : IO (List String) := do
  let history := Solcore.Synthesis.Source.EnumArgument.observe scenario StorageExecution.fixtureBindings fuel
  ensure ((history.getObjValAs? String "status").toOption == some "complete") s!"{name}: history incomplete"
  let rows ← get (history.getObjValAs? (Array Json) "transactions")
  let shape := scenario.plan.shape
  let some modelled := EnumArgumentExecution.model scenario.plan.step shape fuel scenario.transactions
    | throw (IO.userError s!"{name}: the Lean model failed")
  ensure (rows.size == modelled.length) s!"{name}: a row is missing"
  for ((row, model), transaction) in (rows.toList.zip modelled).zip scenario.transactions do
    ensure ((row.getObjValAs? String "status").toOption == some (if model.reverted then "reverted" else "returned") &&
        (row.getObjValAs? String "output").toOption == some (coreOutput model.output) &&
        (row.getObjVal? "committedStorage").toOption == some (slots model.slots))
      s!"{name}: the Core row differs from the Lean model: {row.compress}"
    let prescribed := Solcore.Synthesis.Source.EnumArgument.prescribed shape transaction
    ensure (prescribed == (if model.output.size == 32 then none else some (encodeBytesText model.output)))
      s!"{name}: the prescribed std outcome differs from the model"
  return modelled.map outcome

private def shapeOf (constructors : List Constructor) : Shape :=
  (Solcore.Synthesis.Source.EnumArgument.Shape.ofList? constructors).getD ⟨⟨"Idle", .noWords⟩, ⟨"Ready", .noWords⟩, []⟩

private def payloads : List Payload := [.noWords, .oneWord, .twoWords, .pair, .bytes]

/-- Every field list of `count` constructors. -/
private def fieldLists : Nat → List (List Payload)
  | 0 => [[]]
  | count + 1 => (fieldLists count).flatMap fun rest => payloads.map (· :: rest)

def testSourceEnumArgumentCases : IO Unit := do
  let fuel := 1000000
  -- The wrapper's fixed part and every shape class's decoder, as the
  -- definitions fix them.
  let names := ["Idle", "Ready", "Pair", "Blob"]
  for (count, staticRange, dynamicRange) in [(2, (33, 53), (245, 416)), (3, (46, 76), (258, 458)),
      (4, (59, 99), (271, 500))] do
    let shapes := (fieldLists count).filterMap fun fields =>
      if (fields.filter (· == .bytes)).length ≤ 2 then
        Solcore.Synthesis.Source.EnumArgument.Shape.ofList? ((names.zip fields).map fun (name, payload) => ⟨name, payload⟩)
      else none
    ensure (shapes.all (EnumArgument.programOverhead · == 168)) "the wrapper's fixed part is not 168 nodes"
    for (dynamic, (low, high)) in [(false, staticRange), (true, dynamicRange)] do
      let sizes := (shapes.filter (·.dynamic == dynamic)).map EnumArgument.decoderNodes
      ensure (sizes.foldl min 1000000 == low && sizes.foldl max 0 == high)
        s!"the decoders of {count} constructors (dynamic {dynamic}) take {sizes.foldl min 1000000} to {sizes.foldl max 0} nodes"
  ensure (Solcore.Synthesis.Source.EnumArgument.maxDecoderNodes == 500 &&
      Solcore.Synthesis.Source.EnumArgument.maxProgramNodes == 1012) "the case limit changed"
  -- Random generation: revision three with eight transactions, and the fixed
  -- corpora's revision one with three.
  let mut lengths : List Nat := []
  let mut counts : List Nat := []
  let mut fields : List String := []
  let mut positions : List String := []
  let mut kinds : List String := []
  let mut outcomes : List String := []
  let mut twoBytes := false
  let mut cases : Array Json := #[]
  for (revision, transactions, count, nodes) in
      [(GeneratorRevision.v3, 8, 40, 384), (GeneratorRevision.v1, 3, 24, 384), (GeneratorRevision.v3, 4, 12, 512)] do
    let corpus := Solcore.Synthesis.Source.EnumArgument.generateCases (Seed.ofNat 1) nodes count 512 fuel revision
      transactions
    ensure ((corpus.getObjValAs? String "status").toOption == some "complete") s!"{revision.version}: generation exhausted"
    let generated ← get (corpus.getObjValAs? (Array Json) "cases")
    for (json, index) in generated.zipIdx do
      let name := s!"{revision.version} at {nodes} case {index}"
      ensure ((Solcore.Synthesis.Source.EnumArgument.replayCase json fuel).toOption == some json) s!"{name}: replay differs"
      let scenario ← get (Solcore.Synthesis.Source.EnumArgument.caseProgram json)
      ensure (scenario.transactions.length == transactions) s!"{name}: wrong sequence length"
      outcomes := (outcomes ++ (← sameAsModel scenario fuel name)).eraseDups
      let source ← get (json.getObjValAs? String "source")
      ensure ((source.splitOn "(flags: uint256, value: SynthesizedEnum) public returns (uint256) {").length == 2 &&
          (source.splitOn "import * from std.ABIGeneric;").length == 2)
        s!"{name}: the emitted method differs"
      let shape := scenario.plan.shape
      let kind := if shape.dynamic then "dynamic" else "static"
      counts := (counts ++ [shape.constructors.length]).eraseDups
      fields := (fields ++ shape.payloads.map fun payload => kind ++ ":" ++ reprStr payload).eraseDups
      twoBytes := twoBytes || (shape.payloads.filter (· == .bytes)).length == 2
      for transaction in scenario.transactions do
        positions := (positions ++ [s!"{shape.constructors.length}:{transaction.choice}"]).eraseDups
        kinds := (kinds ++ [Solcore.Synthesis.Source.EnumArgument.kindOf transaction.malformation]).eraseDups
        if shape.payloads[transaction.choice]? == some .bytes then
          lengths := (lengths ++ [transaction.length]).eraseDups
      cases := cases.push json
  ensure (counts.length == 3) s!"generation drew the constructor counts {counts}"
  ensure (fields.length == 9) s!"generation drew the fields {fields}"
  ensure twoBytes "generation never drew two bytes constructors"
  ensure (positions.length == 9) s!"generation chose the positions {positions}"
  ensure (kinds.length == Solcore.Synthesis.Source.EnumArgument.malformationKinds.length)
    s!"generation drew the malformations {kinds}"
  ensure (outcomes.length == 5) s!"generation reached the outcomes {outcomes}"
  for length in Solcore.Synthesis.Source.EnumArgument.lengthBank do
    ensure (lengths.contains length) s!"generation never drew length {length}"
  ensure (lengths.all (· ≤ 64) && lengths.any (fun length => length % 32 != 0 &&
      !Solcore.Synthesis.Source.EnumArgument.lengthBank.contains length))
    "generation drew a length above 64 or no uniform partial-Word length"
  -- Reductions: a narrower or dropped constructor comes with every shape that
  -- has one, and every emitted candidate replays as a strictly smaller sealed
  -- case.
  for json in cases.toList.take 8 do
    let source ← get (Solcore.Synthesis.Source.EnumArgument.caseProgram json)
    let reduced := Solcore.Synthesis.Source.EnumArgument.reductions source
    ensure (!reduced.isEmpty) "a case has no reduction"
    ensure (source.plan.shape.payloads.all (· == .noWords) || reduced.any (fun candidate =>
        candidate.candidate.transactions.length == source.transactions.length &&
        Solcore.Synthesis.Source.EnumArgument.shapeWeight candidate.candidate.plan.shape <
          Solcore.Synthesis.Source.EnumArgument.shapeWeight source.plan.shape))
      "no narrower constructor"
    let shrunk ← get (Solcore.Synthesis.Source.EnumArgument.shrinkCases json 64 fuel)
    for candidate in ← get (shrunk.getObjValAs? (Array Json) "cases") do
      ensure ((Solcore.Synthesis.Source.EnumArgument.replayCase candidate fuel).toOption == some candidate)
        "a reduction does not replay"
      let _ ← sameAsModel (← get (Solcore.Synthesis.Source.EnumArgument.caseProgram candidate)) fuel "reduction"
  -- Refusals: a choice beyond the constructors, a length for a constructor
  -- without `bytes`, a length above 64, a malformation that does not apply, and
  -- metadata that differs from the calldata or std's decision.
  let some json := cases.toList.find? (fun json => match Solcore.Synthesis.Source.EnumArgument.caseProgram json with
      | .ok scenario => scenario.plan.shape.payloads.any (· == .noWords) &&
          scenario.plan.shape.payloads.any (· == .bytes)
      | .error _ => false) | throw (IO.userError "no mixed case")
  let scenario ← get (Solcore.Synthesis.Source.EnumArgument.caseProgram json)
  let shape := scenario.plan.shape
  let transactions ← get (json.getObjValAs? (Array Json) "transactions")
  let some transaction := scenario.transactions.head? | throw (IO.userError "no transaction")
  let rebuilt (choice length : Nat) (malformation : Malformation) : Json :=
    Solcore.Synthesis.Source.EnumArgument.transactionJson shape
      {transaction with choice, length, malformation}
  let count := shape.constructors.length
  let some bytesIndex := shape.payloads.findIdx? (· == .bytes) | throw (IO.userError "no bytes")
  let some noneIndex := shape.payloads.findIdx? (· == .noWords) | throw (IO.userError "no field-less constructor")
  ensure (Solcore.Synthesis.Source.EnumArgument.caseProgram
      (json.setObjVal! "transactions" (.arr (transactions.set! 0 (rebuilt bytesIndex 3 (.padding 1)))))).toOption.isSome
    "a padded bytes transaction was refused"
  for (choice, length, malformation, label) in [(count, 0, Malformation.none, "a choice beyond the constructors"),
      (noneIndex, 1, .none, "a length for a constructor without bytes"), (bytesIndex, 65, .none, "a length above 64"),
      (noneIndex, 0, .tail (Word.ofNatModulo 3), "a tail offset without bytes"),
      (bytesIndex, 32, .padding 0, "padding of a whole Word"),
      (noneIndex, 0, .retag noneIndex, "a retag of the chosen constructor"),
      (noneIndex, 0, .tag (EnumArgument.tag (shape.constructors.getD 0 shape.first)), "a known tag as unknown"),
      (noneIndex, 0, .truncate 3, "a cut inside the selector"), (noneIndex, 0, .trailing 65 0, "65 trailing bytes")] do
    ensure (Solcore.Synthesis.Source.EnumArgument.caseProgram
        (json.setObjVal! "transactions" (.arr (transactions.set! 0 (rebuilt choice length malformation))))).toOption.isNone
      s!"{label} was admitted"
  for (key, value, label) in [("length", toJson 4, "a length that differs from its calldata"),
      ("stdRejection", toJson "0x08638556", "a std outcome that differs from std's decision"),
      ("calldata", toJson "0x00", "calldata that differs from its encoding")] do
    ensure (Solcore.Synthesis.Source.EnumArgument.caseProgram (json.setObjVal! "transactions" (.arr (transactions.set! 0
        ((rebuilt bytesIndex 3 .none).setObjVal! key value))))).toOption.isNone
      s!"{label} was admitted"
  -- Plans: the struct is admitted; an extra field, a repeated or unknown name,
  -- three bytes constructors, one or five constructors and three Words are
  -- refused.
  let plan ← get (json.getObjVal? "enumArgumentPlan")
  let step ← get (plan.getObjVal? "stepProgram")
  let planOf (constructors : List (String × String)) : Json := Json.mkObj [
    ("schema", toJson Solcore.Synthesis.Source.EnumArgument.planSchema),
    ("constructors", toJson (constructors.map fun (name, fields) =>
      Json.mkObj [("name", toJson name), ("fields", toJson fields)])),
    ("stepProgram", step)]
  ensure (Solcore.Synthesis.Source.EnumArgument.checkedPlan
      (planOf [("Idle", ""), ("Ready", "ScPair")])).toOption.isSome
    "a plan with the struct was refused"
  for (constructors, label) in [
      ([("Idle", ""), ("Idle", "uint256")], "a repeated name"),
      ([("Idle", ""), ("Other", "uint256")], "a name outside the bank"),
      ([("Idle", "bytes"), ("Ready", "bytes"), ("Pair", "bytes")], "three bytes constructors"),
      ([("Idle", "")], "one constructor"),
      ([("Idle", ""), ("Ready", ""), ("Pair", ""), ("Blob", ""), ("Q", "")], "five constructors"),
      ([("Idle", ""), ("Ready", "uint256,uint256,uint256")], "three Words")] do
    ensure (Solcore.Synthesis.Source.EnumArgument.checkedPlan (planOf constructors)).toOption.isNone
      s!"a plan with {label} was admitted"
  ensure (Solcore.Synthesis.Source.EnumArgument.checkedPlan (plan.setObjVal! "arity" (toJson 2))).toOption.isNone
    "a plan with an extra field was admitted"

end Tests.SourceEnumArgumentCases
end

section
-- leanmerge: from Solcore.Test.SourceEnumArgumentCorpus
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
end

section
-- leanmerge: from Solcore.Test.SourceEnumArgumentGolden
/-! Golden cases for the enum-argument profile: the decoder's exact acceptance
and refusals. Every expected row is written out as hexadecimal text computed
outside Lean from the definitions and the probe's reading of std's decoder, not
by either model, with tags and selectors from `cast keccak`. The steps add a
known constant `c`, so an accepted transaction computes
`r = slot 0 + index + w0 + w1 + w2 + c`, writes `r`, the one-based index and the
decoded Words to slots 0 to 4, and returns `r`; odd decoded flags revert with
`r` and keep the prior slots. A rejection is std's revert data: an error
selector, or nothing for an unknown tag. The scenarios cover static and
dynamic shapes, every field kind with the struct, `bytes` lengths 0, 1, 17, 31,
32, 33, 63 and 64, every malformation kind with accepted and rejected entries,
and the order of the checks. Original Core gives each row under the selector
and empty-revert rules, and the Lean model gives it exactly. -/
set_option autoImplicit false

namespace Tests.SourceEnumArgumentGolden

open Lean
open Solcore.Core (Word)
open Solcore.ContractRuntime
open Solcore.Synthesis.Core
open Solcore.Synthesis.Core.EnumArgument (Constructor Shape)
open Solcore.Synthesis.Stateful
open Solcore.Synthesis.Stateful.EnumArgumentExecution (Transaction Malformation)

private def get {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def w (value : Nat) : Word := Word.ofNatModulo value

/-- The step `x ↦ x + c`: aggregate template 0 around the constant scalar. -/
private def step (c : Nat) : IO Aggregates.CheckedDAG := do
  let some dag := Aggregates.CheckedDAG.ofParts? [Solcore.Synthesis.Source.Aggregate.template 0 (.word (w c))]
      (.apply (.var 1) (.var 0)) | throw (IO.userError "constant step failed admission")
  return dag

/-- The expected row: status, std's whole return or revert data as hexadecimal
text, empty for an unknown tag, and slots zero to four. -/
private structure Expected where
  status : String
  output : String
  values : List Nat

private def slots (values : List Nat) : Json :=
  toJson ((List.range EnumArgument.slotCount).map fun slot => Json.mkObj [
    ("slot", toJson (toString slot)), ("value", toJson (toString (values.getD slot 0)))])

private def tx (index flags choice first second length : Nat) (malformation : Malformation) : Transaction :=
  ⟨"tx-" ++ toString index, w flags, choice, w first, w second, length, malformation⟩

-- The tags `keccak256("Name(fields)")`, as `cast keccak` writes them.
-- Blob(bytes)
private def tagBlobBytes : String := "d05ce3dc4caf4a4b252e3323bde615dc3b9d54623e1859c892f0b4ecf5e45164"
-- Idle()
private def tagIdleUnit : String := "ae897c555b7596dee56949d599aa959af71416324ac27ef76dd898923ab34d4f"
-- OverflowedAccumulator(bytes)
private def tagOverflowedAccumulatorBytes : String := "1d021c79c75f3d483321c073ba0acaa5b4589d7a6ad132e8b5fe27d9b76d678b"
-- Pair(uint256,uint256)
private def tagPairPair : String := "2d3b57dedfada8371bdae932a6881ace0dec34c90dd19fd49b2164124e699e2d"
-- Q(bytes)
private def tagQBytes : String := "ceddd0f6fa798287ec511a63a42164c8eb23d85a7f6355be56c0e9119d5f93b4"
-- Q(uint256)
private def tagQWord : String := "5dcad53f88dc9d20c351c1bb58593dde38a673b5308c8751aaeb91edd8c97952"
-- Ready()
private def tagReadyUnit : String := "6e12fa0ff1c6b8acb2181ba65fc2867fd8d895d0af9f39674b64abc5ff79275b"
-- Ready(uint256)
private def tagReadyWord : String := "0b217ad5c70346c7cd952bd2463c6684a56f9ed229f5780947586625781b4770"
-- Ready(uint256,uint256)
private def tagReadyStruct : String := "1ee0fddb687f7d726adbdd32a0b3afe38d0593fe9dc00a18a5f4acd116e8b7c9"
-- Rejected()
private def tagRejectedUnit : String := "efde6dcf3c2196c5705e848c09f0659d33de3ca0248be3ab40852d1bafc0f1e3"
-- Settled(uint256,uint256)
private def tagSettledPair : String := "f5b268a3ff315cc44ccceeef86259c9e8eef81ceecb14001543809115380dd62"

-- The selectors of `run(uint256,sum(...))`, as `cast keccak` writes them.
-- run(uint256,sum(uint256,uint256,sum(,uint256)))
private def selectorStaticWords : String := "0x4461c0ed"
-- run(uint256,sum(bytes,sum(uint256,sum(uint256,uint256,))))
private def selectorDynamicWords : String := "0x62de7816"
-- run(uint256,sum(bytes,bytes))
private def selectorTwoBytes : String := "0xf5cc4c83"
-- run(uint256,sum(uint256,uint256,sum(,bytes)))
private def selectorStructFields : String := "0x89fd1ec1"
-- run(uint256,sum(,))
private def selectorTagsOnly : String := "0x9350d233"

private def staticWordsRows : List (Transaction × Expected) := [
  (tx 0 0 0 7 9 0 .none, ⟨"returned",
      "0000000000000000000000000000000000000000000000000000000000000016",
      [22, 1, 7, 9, 0]⟩),
  (tx 1 1 1 0 0 0 .none, ⟨"reverted",
      "000000000000000000000000000000000000000000000000000000000000001d",
      [22, 1, 7, 9, 0]⟩),
  (tx 2 0 2 (2 ^ 256 - 1) 0 0 (.unused (w (2 ^ 256 - 1))), ⟨"returned",
      "000000000000000000000000000000000000000000000000000000000000001d",
      [29, 3, (2 ^ 256 - 1), 0, 0]⟩),
  (tx 3 0 2 3 0 0 (.tag (w 0)), ⟨"reverted",
      "",
      [29, 3, (2 ^ 256 - 1), 0, 0]⟩),
  (tx 4 0 0 1 2 0 (.truncate 131), ⟨"reverted",
      "08638556",
      [29, 3, (2 ^ 256 - 1), 0, 0]⟩),
  (tx 5 0 1 0 0 0 (.short 3), ⟨"reverted",
      "4924aef0",
      [29, 3, (2 ^ 256 - 1), 0, 0]⟩),
  (tx 6 0 2 4 0 0 (.selector 1), ⟨"reverted",
      "4924aef0",
      [29, 3, (2 ^ 256 - 1), 0, 0]⟩),
  (tx 7 2 0 6 8 0 (.retag 1), ⟨"returned",
      "0000000000000000000000000000000000000000000000000000000000000024",
      [36, 2, 0, 0, 0]⟩)]

private def dynamicWordsRows : List (Transaction × Expected) := [
  (tx 0 0 0 1 2 33 .none, ⟨"returned",
      "da3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18eb8",
      [0xda3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18eb8, 1, 33, 0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95, 0x3c00000000000000000000000000000000000000000000000000000000000000]⟩),
  (tx 1 0 1 (2 ^ 255) 0 0 .none, ⟨"returned",
      "5a3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18ebb",
      [0x5a3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18ebb, 2, (2 ^ 255), 0, 0]⟩),
  (tx 2 0 2 3 7 0 (.offset (w 160)), ⟨"reverted",
      "08638556",
      [0x5a3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18ebb, 2, (2 ^ 255), 0, 0]⟩),
  (tx 3 0 3 0 0 0 (.aliased 1), ⟨"returned",
      "5a3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18ebe",
      [0x5a3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18ebe, 2, 0, 0, 0]⟩),
  (tx 4 0 0 1 1 1 (.tail (w 0)), ⟨"reverted",
      "08638556",
      [0x5a3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18ebe, 2, 0, 0, 0]⟩),
  (tx 5 0 0 3 1 1 (.length (w 32)), ⟨"returned",
      "343779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18ee0",
      [0x343779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18ee0, 1, 32, 0xda00000000000000000000000000000000000000000000000000000000000000, 0]⟩),
  (tx 6 0 2 5 5 0 (.truncate 100), ⟨"reverted",
      "08638556",
      [0x343779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18ee0, 1, 32, 0xda00000000000000000000000000000000000000000000000000000000000000, 0]⟩),
  (tx 7 0 1 9 0 0 (.truncate 132), ⟨"returned",
      "343779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18eec",
      [0x343779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18eec, 2, 9, 0, 0]⟩)]

private def twoBytesRows : List (Transaction × Expected) := [
  (tx 0 0 1 1 0 1 .none, ⟨"returned",
      "9e00000000000000000000000000000000000000000000000000000000000005",
      [0x9e00000000000000000000000000000000000000000000000000000000000005, 2, 1, 0x9e00000000000000000000000000000000000000000000000000000000000000, 0]⟩),
  (tx 1 0 0 2 3 31 .none, ⟨"returned",
      "da6ef372fe94f82be73980c0b9db906821044ed7e744e4a3f0d8d423a1831d27",
      [0xda6ef372fe94f82be73980c0b9db906821044ed7e744e4a3f0d8d423a1831d27, 1, 31, 0x3c6ef372fe94f82be73980c0b9db906821044ed7e744e4a3f0d8d423a1831d00, 0]⟩),
  (tx 2 0 1 3 4 32 .none, ⟨"returned",
      "b515609f7c746c6dc20fc1e1d0a4e904528ac51bc22c3b99da1e125913c7c90a",
      [0xb515609f7c746c6dc20fc1e1d0a4e904528ac51bc22c3b99da1e125913c7c90a, 2, 32, 0xdaa66d2c7ddf7441dad6412116c9589c31867643dae756f5e9453e357244abbf, 0]⟩),
  (tx 3 0 0 4 5 63 (.truncate 227), ⟨"returned",
      "4508a824f612c933529285451500f2d8e71e27e752e2407b95edccf96a95cba0",
      [0x4508a824f612c933529285451500f2d8e71e27e752e2407b95edccf96a95cba0, 1, 63, 0x78dde6e5fd29f057ce73018173b720d042089dafce89c947e1b1a84743063a54, 0x1715609f7c746c6dc20fc1e1d0a4e904528ac51bc22c3b99da1e125913c7c800]⟩),
  (tx 4 0 1 5 6 64 .none, ⟨"returned",
      "116ae31d6e461e24ca4ec96913388d159cb5d98acadd2a0142965bbd62e6ec4b",
      [0x116ae31d6e461e24ca4ec96913388d159cb5d98acadd2a0142965bbd62e6ec4b, 2, 64, 0x1715609f7c746c6dc20fc1e1d0a4e904528ac51bc22c3b99da1e125913c7c8e9, 0xb54cda58fbbee883b5ac82422d92b138630cec87b5ceadebd28a7c6ae489577e]⟩),
  (tx 5 0 0 6 7 0 .none, ⟨"returned",
      "116ae31d6e461e24ca4ec96913388d159cb5d98acadd2a0142965bbd62e6ec4e",
      [0x116ae31d6e461e24ca4ec96913388d159cb5d98acadd2a0142965bbd62e6ec4e, 1, 0, 0, 0]⟩),
  (tx 6 0 1 7 8 17 (.padding 1), ⟨"returned",
      "64ef372fe94f82be73980c0b9db906820fb5d98acadd2a0142965bbd62e6ec63",
      [0x64ef372fe94f82be73980c0b9db906820fb5d98acadd2a0142965bbd62e6ec63, 2, 17, 0x538454127b096499a94942a28a80796c73000000000000000000000000000000, 0]⟩),
  (tx 7 0 0 8 9 17 (.length (w 18)), ⟨"returned",
      "56ab04fbe3a3636e107e0f0e8527482293b5d98acadd2a0142965bbd62e6ec78",
      [0x56ab04fbe3a3636e107e0f0e8527482293b5d98acadd2a0142965bbd62e6ec78, 1, 18, 0xf1bbcdcbfa53e0af9ce60302e76e41a084000000000000000000000000000000, 0]⟩)]

private def structFieldsRows : List (Transaction × Expected) := [
  (tx 0 0 0 11 12 0 .none, ⟨"returned",
      "000000000000000000000000000000000000000000000000000000000000001b",
      [27, 1, 11, 12, 0]⟩),
  (tx 1 0 2 0 0 0 .none, ⟨"returned",
      "0000000000000000000000000000000000000000000000000000000000000021",
      [33, 3, 0, 0, 0]⟩),
  (tx 2 0 1 0 0 0 (.trailing 33 1), ⟨"returned",
      "0000000000000000000000000000000000000000000000000000000000000026",
      [38, 2, 0, 0, 0]⟩),
  (tx 3 0 0 13 14 0 (.retag 2), ⟨"reverted",
      "08638556",
      [38, 2, 0, 0, 0]⟩),
  (tx 4 0 1 0 0 0 (.offset (w 32)), ⟨"reverted",
      "",
      [38, 2, 0, 0, 0]⟩),
  (tx 5 0 0 1 1 0 (.tag (w 99)), ⟨"reverted",
      "",
      [38, 2, 0, 0, 0]⟩)]

private def tagsOnlyRows : List (Transaction × Expected) := [
  (tx 0 0 1 0 0 0 .none, ⟨"returned",
      "0000000000000000000000000000000000000000000000000000000000000006",
      [6, 2, 0, 0, 0]⟩),
  (tx 1 0 0 0 0 0 (.trailing 1 0), ⟨"returned",
      "000000000000000000000000000000000000000000000000000000000000000b",
      [11, 1, 0, 0, 0]⟩),
  (tx 2 3 1 0 0 0 .none, ⟨"reverted",
      "0000000000000000000000000000000000000000000000000000000000000011",
      [11, 1, 0, 0, 0]⟩),
  (tx 3 0 0 0 0 0 (.truncate 67), ⟨"reverted",
      "08638556",
      [11, 1, 0, 0, 0]⟩),
  (tx 4 0 1 0 0 0 (.tag (w (2 ^ 255))), ⟨"reverted",
      "",
      [11, 1, 0, 0, 0]⟩)]

private def scenarios : List (String × Nat × List Constructor × String × String × List (Transaction × Expected)) := [
    ("static-words", 5, [⟨"Pair", .twoWords⟩, ⟨"Idle", .noWords⟩, ⟨"Q", .oneWord⟩],
      "run(uint256,sum(uint256,uint256,sum(,uint256)))", selectorStaticWords, staticWordsRows),
    ("dynamic-words", 1, [⟨"Blob", .bytes⟩, ⟨"Ready", .oneWord⟩, ⟨"Settled", .twoWords⟩, ⟨"Rejected", .noWords⟩],
      "run(uint256,sum(bytes,sum(uint256,sum(uint256,uint256,))))", selectorDynamicWords, dynamicWordsRows),
    ("two-bytes", 2, [⟨"OverflowedAccumulator", .bytes⟩, ⟨"Q", .bytes⟩],
      "run(uint256,sum(bytes,bytes))", selectorTwoBytes, twoBytesRows),
    ("struct-fields", 3, [⟨"Ready", .pair⟩, ⟨"Idle", .noWords⟩, ⟨"Blob", .bytes⟩],
      "run(uint256,sum(uint256,uint256,sum(,bytes)))", selectorStructFields, structFieldsRows),
    ("tags-only", 4, [⟨"Idle", .noWords⟩, ⟨"Ready", .noWords⟩],
      "run(uint256,sum(,))", selectorTagsOnly, tagsOnlyRows)]

/-- Original Core reverts with one Word: an error selector stands for std's
four bytes and the Word zero for its empty revert data. -/
private def coreOutput (output : String) : String :=
  "0x" ++ if output.length == 8 then String.ofList (List.replicate 56 '0') ++ output
    else if output.isEmpty then String.ofList (List.replicate 64 '0') else output

private def check (name : String) (row : Json) (model : EnumArgumentExecution.ModelRow) (expected : Expected) :
    IO Unit := do
  ensure ((row.getObjValAs? String "status").toOption == some expected.status &&
      (row.getObjValAs? String "output").toOption == some (coreOutput expected.output) &&
      (row.getObjVal? "committedStorage").toOption == some (slots expected.values))
    s!"{name}: original Core differs from the expected row {row.compress}"
  ensure (model.reverted == (expected.status == "reverted") &&
      encodeBytesText model.output == "0x" ++ expected.output &&
      model.slots == (List.range EnumArgument.slotCount).map (fun slot => w (expected.values.getD slot 0)))
    s!"{name}: the Lean model differs from the expected row"

/-- Original Core's status and output on raw calldata from empty storage. -/
private def runRaw (contract : CheckedCoreContract) (bytes : ByteArray) : IO (String × String) := do
  let bindings := StorageExecution.fixtureBindings
  let registry : CheckedContractRegistry := {
    lookup := fun target => if target = bindings.address then some contract else none }
  let world := StorageExecution.initialWorldForContract contract bindings
  if bounded : bytes.size < Solcore.Core.wordModulus then
    let some ⟨resolved, installed⟩ := registry.resolve? world bindings.address
      | throw (IO.userError "the contract did not resolve")
    let invocation : TopLevelInvocation := {
      target := bindings.address, caller := bindings.caller, callValue := Word.zero,
      inputData := ⟨bytes, bounded⟩ }
    match TopLevelExecution.run resolved invocation installed 1000000 with
    | .completed terminal =>
        match terminal.outcome with
        | .returned out => return ("returned", encodeBytesText out)
        | .reverted out => return ("reverted", encodeBytesText out)
        | .trapped _ => return ("trapped", "")
    | .outOfFuel .. => return ("out-of-fuel", "")
  else throw (IO.userError "calldata exceeds the Word bound")

/-- std's decisions that one malformation cannot reach, on raw calldata of the
second scenario's `Settled(3, 7)`: the selector is checked before the head, the
offset before the tag, and the tag before any field is read. -/
private def orderRows (shape : Shape) : List (String × ByteArray × String) :=
  let canonical := EnumArgumentExecution.inputBytes shape (tx 0 0 2 3 7 0 .none)
  let unknown := StdCalldata.replaceWord canonical 68 (w 7)
  let wrong := StdCalldata.Change.apply canonical (.selector 1)
  [("unknown tag, fields cut", unknown.extract 0 100, ""),
    ("unknown tag, offset past the end", StdCalldata.replaceWord unknown 36 (w (unknown.size - 3)), "08638556"),
    ("wrong selector, head cut", wrong.extract 0 40, "4924aef0"),
    ("known tag, fields cut", canonical.extract 0 131, "08638556"),
    ("known tag, unread padding cut", canonical.extract 0 164, "")]

def testSourceEnumArgumentGolden : IO Unit := do
  let fuel := 1000000
  -- Lean's Keccak-256 tags equal the ones written out; a struct's tag is its fields'.
  ensure (encodeBytesText (encodeWordBytesBE (EnumArgument.tag ⟨"Ready", .pair⟩)) == "0x" ++ tagReadyStruct &&
      EnumArgument.tag ⟨"Ready", .pair⟩ == EnumArgument.tag ⟨"Ready", .twoWords⟩ &&
      encodeBytesText (encodeWordBytesBE (EnumArgument.tag ⟨"Q", .bytes⟩)) == "0x" ++ tagQBytes &&
      encodeBytesText (encodeWordBytesBE (EnumArgument.tag ⟨"Idle", .noWords⟩)) == "0x" ++ tagIdleUnit)
    "a constructor tag differs from keccak256 of its signature"
  for (name, constant, constructors, signature, selector, rows) in scenarios do
    let step ← step constant
    let some shape := Solcore.Synthesis.Source.EnumArgument.Shape.ofList? constructors
      | throw (IO.userError s!"{name}: the shape has fewer than two constructors")
    ensure (shape.signature == signature && Solcore.Synthesis.Source.EnumArgument.selectorText shape == selector)
      s!"{name}: the signature or selector differs from std's structural signature"
    let some plan := EnumArgument.CheckedPlan.ofParts? step shape
      | throw (IO.userError s!"{name}: the enum-argument wrapper failed admission")
    let transactions := rows.map Prod.fst
    for (transaction, expected) in rows do
      let rejected := expected.status == "reverted" && expected.output.length != 64
      ensure (Solcore.Synthesis.Source.EnumArgument.prescribed shape transaction ==
          (if rejected then some ("0x" ++ expected.output) else none))
        s!"{name} {transaction.id}: the prescribed std outcome differs from the expected row"
    let history := EnumArgumentExecution.observe plan transactions StorageExecution.fixtureBindings fuel
    ensure ((history.getObjValAs? String "status").toOption == some "complete") s!"{name}: the history is incomplete"
    let observed ← get (history.getObjValAs? (Array Json) "transactions")
    let some modelled := EnumArgumentExecution.model step shape fuel transactions
      | throw (IO.userError s!"{name}: the Lean model failed")
    ensure (observed.size == rows.length && modelled.length == rows.length) s!"{name}: a row is missing"
    for ((row, model), (transaction, expected)) in (observed.toList.zip modelled).zip rows do
      check s!"{name} {transaction.id}" row model expected
  -- The order of std's checks, on raw calldata, for Core and the Lean model alike.
  let some (_, _, constructors, _, _, _) := scenarios[1]? | throw (IO.userError "no dynamic scenario")
  let some shape := Solcore.Synthesis.Source.EnumArgument.Shape.ofList? constructors | throw (IO.userError "no shape")
  let some plan := EnumArgument.CheckedPlan.ofParts? (← step 1) shape | throw (IO.userError "no plan")
  for (label, bytes, expected) in orderRows shape do
    let (status, output) ← runRaw plan.contract bytes
    let decided := match EnumArgumentExecution.stdDecode shape bytes with
      | .error data => some (encodeBytesText data)
      | .ok _ => none
    if expected.isEmpty && label.endsWith "padding cut" then
      ensure (status == "returned" && decided.isNone) s!"{label}: the cut padding was not accepted"
    else
      ensure (status == "reverted" && output == coreOutput expected && decided == some ("0x" ++ expected))
        s!"{label}: std's order of checks differs ({status} {output})"
  -- A changed expectation fails: the first static row read as a rejection.
  let some (transaction, expected) := staticWordsRows.head? | throw (IO.userError "no static row")
  ensure (Solcore.Synthesis.Source.EnumArgument.prescribed (← (Solcore.Synthesis.Source.EnumArgument.Shape.ofList?
        [⟨"Pair", .twoWords⟩, ⟨"Idle", .noWords⟩, ⟨"Q", .oneWord⟩]).getDM
        (throw (IO.userError "no shape"))) transaction == none &&
      coreOutput expected.output != coreOutput "08638556")
    "a changed expectation is not detected"

end Tests.SourceEnumArgumentGolden
end

section
-- leanmerge: from Solcore.Test.SourceEnumArrayCases
/-! Generated enum-array cases. The Core contract must equal the Lean model,
std's decision over the calldata bytes and the protocol, on every transaction
of the generated sequences, under the selector and empty-revert rules; each
case must replay to itself; the wrapper's and decoders' node counts must be the
ones the definitions fix; generation must draw every constructor count, static
and dynamic shapes, every field kind, two `bytes` constructors, every element
count, both indices reading every position, every bank length, every
malformation kind and every std outcome; and every reduction must be a strictly
smaller sealed case that replays. -/
set_option autoImplicit false

namespace Tests.SourceEnumArrayCases

open Lean
open Solcore.Core (Word)
open Solcore.ContractRuntime
open Solcore.Synthesis.Core
open Solcore.Synthesis.Core.EnumArgument (Constructor Payload Shape)
open Solcore.Synthesis.Stateful
open Solcore.Synthesis.Stateful.EnumArrayExecution (Element Transaction Malformation)

private abbrev Cases := Solcore.Synthesis.Source.EnumArray.CheckedScenario

private def get {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def slots (values : List Word) : Json :=
  toJson ((values.zipIdx).map fun (value, slot) => Json.mkObj [
    ("slot", toJson (toString slot)), ("value", toJson (toString value.val))])

/-- std's revert data with a selector: an error's four bytes, or a panic's
selector and code. -/
private def selected (output : ByteArray) : Bool := output.size == 4 || output.size == 36

/-- Original Core's revert Word for std's revert data: the selector Word for
an error or a panic, the Word zero for none. -/
private def coreOutput (output : ByteArray) : String :=
  if selected output then
    encodeBytesText (encodeWordBytesBE (Word.ofNatModulo (StdCalldata.bigEndian output 0 4)))
  else if output.size == 0 then encodeBytesText (encodeWordBytesBE Word.zero)
  else encodeBytesText output

/-- The std outcome a model row stands for. -/
private def outcome (row : EnumArrayExecution.ModelRow) : String :=
  if selected row.output then encodeBytesText row.output
  else if row.output.size == 0 then "empty"
  else if row.reverted then "body-revert" else "returned"

/-- The Core rows of a scenario equal the model's, transaction by transaction,
and each model row is std's prescribed outcome. -/
private def sameAsModel (scenario : Cases) (fuel : Nat) (name : String) : IO (List String) := do
  let history := Solcore.Synthesis.Source.EnumArray.observe scenario StorageExecution.fixtureBindings fuel
  ensure ((history.getObjValAs? String "status").toOption == some "complete") s!"{name}: history incomplete"
  let rows ← get (history.getObjValAs? (Array Json) "transactions")
  let shape := scenario.plan.shape
  let some modelled := EnumArrayExecution.model scenario.plan.step shape fuel scenario.transactions
    | throw (IO.userError s!"{name}: the Lean model failed")
  ensure (rows.size == modelled.length) s!"{name}: a row is missing"
  for ((row, model), transaction) in (rows.toList.zip modelled).zip scenario.transactions do
    ensure ((row.getObjValAs? String "status").toOption == some (if model.reverted then "reverted" else "returned") &&
        (row.getObjValAs? String "output").toOption == some (coreOutput model.output) &&
        (row.getObjVal? "committedStorage").toOption == some (slots model.slots))
      s!"{name}: the Core row differs from the Lean model: {row.compress}"
    let prescribed := Solcore.Synthesis.Source.EnumArray.prescribed shape transaction
    ensure (prescribed == (if model.output.size == 32 then none else some (encodeBytesText model.output)))
      s!"{name}: the prescribed std outcome differs from the model"
  return modelled.map outcome

private def payloads : List Payload := [.noWords, .oneWord, .twoWords, .pair, .bytes]

/-- Every field list of `count` constructors. -/
private def fieldLists : Nat → List (List Payload)
  | 0 => [[]]
  | count + 1 => (fieldLists count).flatMap fun rest => payloads.map (· :: rest)

/-- The `length:index` of both elements std decoded, for lengths up to three. -/
private def readPositions (shape : Shape) (tx : Transaction) : List String :=
  match EnumArrayExecution.stdDecode shape (EnumArrayExecution.inputBytes shape tx) with
  | .ok decoded =>
      if decoded.length.val ≤ 3 then
        [s!"{decoded.length.val}:{tx.first.val}", s!"{decoded.length.val}:{tx.second.val}"]
      else []
  | .error _ => []

def testSourceEnumArrayCases : IO Unit := do
  let fuel := 1000000
  -- The wrapper and every shape class's decoder, as the definitions fix them.
  let names := ["Idle", "Ready", "Pair", "Blob"]
  for (count, staticRange, dynamicRange) in [(2, (26, 54), (197, 368)), (3, (39, 81), (210, 410)),
      (4, (52, 108), (223, 452))] do
    let shapes := (fieldLists count).filterMap fun fields =>
      if (fields.filter (· == .bytes)).length ≤ 2 then
        Solcore.Synthesis.Source.EnumArgument.Shape.ofList? ((names.zip fields).map fun (name, payload) => ⟨name, payload⟩)
      else none
    ensure (shapes.all fun shape => EnumArray.wrapperNodes shape == if shape.dynamic then 397 else 358)
      "the array wrapper is not 358 nodes static and 397 dynamic"
    for (dynamic, (low, high)) in [(false, staticRange), (true, dynamicRange)] do
      let sizes := (shapes.filter (·.dynamic == dynamic)).map EnumArray.decoderNodes
      ensure (sizes.foldl min 1000000 == low && sizes.foldl max 0 == high)
        s!"the decoders of {count} constructors (dynamic {dynamic}) take {sizes.foldl min 1000000} to {sizes.foldl max 0} nodes"
  ensure (EnumArray.reservedNodes == 168 && Solcore.Synthesis.Source.EnumArray.maxDecoderNodes == 452 &&
      Solcore.Synthesis.Source.EnumArray.maxWrapperNodes == 397 &&
      Solcore.Synthesis.Source.EnumArray.maxProgramNodes == 1193) "the case limit changed"
  ensure (EnumArgument.programOverhead ⟨⟨"Idle", .noWords⟩, ⟨"Ready", .noWords⟩, []⟩ == EnumArray.reservedNodes)
    "the reservation differs from the enum-argument wrapper"
  -- Random generation: revision three with eight transactions, and the fixed
  -- corpora's revision one with three.
  let mut lengths : List Nat := []
  let mut counts : List Nat := []
  let mut fields : List String := []
  let mut elementCounts : List Nat := []
  let mut positions : List String := []
  let mut kinds : List String := []
  let mut outcomes : List String := []
  let mut twoBytes := false
  let mut cases : Array Json := #[]
  for (revision, transactions, count, nodes) in
      [(GeneratorRevision.v3, 8, 40, 384), (GeneratorRevision.v1, 3, 24, 384), (GeneratorRevision.v3, 4, 12, 512)] do
    let corpus := Solcore.Synthesis.Source.EnumArray.generateCases (Seed.ofNat 1) nodes count 512 fuel revision
      transactions
    ensure ((corpus.getObjValAs? String "status").toOption == some "complete") s!"{revision.version}: generation exhausted"
    let generated ← get (corpus.getObjValAs? (Array Json) "cases")
    for (json, index) in generated.zipIdx do
      let name := s!"{revision.version} at {nodes} case {index}"
      ensure ((Solcore.Synthesis.Source.EnumArray.replayCase json fuel).toOption == some json) s!"{name}: replay differs"
      let scenario ← get (Solcore.Synthesis.Source.EnumArray.caseProgram json)
      ensure (scenario.transactions.length == transactions) s!"{name}: wrong sequence length"
      outcomes := (outcomes ++ (← sameAsModel scenario fuel name)).eraseDups
      let source ← get (json.getObjValAs? String "source")
      ensure ((source.splitOn ("(flags: uint256, items: calldata<array<SynthesizedEnum>>, first: uint256, " ++
            "second: uint256) public returns (uint256) {")).length == 2 &&
          (source.splitOn "= items[first];").length == 2 && (source.splitOn "= items[second];").length == 2)
        s!"{name}: the emitted method differs"
      let shape := scenario.plan.shape
      let kind := if shape.dynamic then "dynamic" else "static"
      counts := (counts ++ [shape.constructors.length]).eraseDups
      fields := (fields ++ shape.payloads.map fun payload => kind ++ ":" ++ reprStr payload).eraseDups
      twoBytes := twoBytes || (shape.payloads.filter (· == .bytes)).length == 2
      for transaction in scenario.transactions do
        elementCounts := (elementCounts ++ [transaction.elements.length]).eraseDups
        positions := (positions ++ readPositions shape transaction).eraseDups
        kinds := (kinds ++ [Solcore.Synthesis.Source.EnumArray.kindOf transaction.malformation]).eraseDups
        for element in transaction.elements do
          if shape.payloads[element.choice]? == some .bytes then
            lengths := (lengths ++ [element.length]).eraseDups
      cases := cases.push json
  ensure (counts.length == 3) s!"generation drew the constructor counts {counts}"
  ensure (fields.length == 9) s!"generation drew the fields {fields}"
  ensure twoBytes "generation never drew two bytes constructors"
  ensure (elementCounts.length == 4) s!"generation drew the element counts {elementCounts}"
  ensure ([1, 2, 3].all fun count => (List.range count).all fun index => positions.contains s!"{count}:{index}")
    s!"generation read the positions {positions}"
  ensure (kinds.length == Solcore.Synthesis.Source.EnumArray.malformationKinds.length)
    s!"generation drew the malformations {kinds}"
  ensure (outcomes.length == 6) s!"generation reached the outcomes {outcomes}"
  for length in Solcore.Synthesis.Source.EnumArray.lengthBank do
    ensure (lengths.contains length) s!"generation never drew length {length}"
  ensure (lengths.all (· ≤ 64) && lengths.any (fun length => length % 32 != 0 &&
      !Solcore.Synthesis.Source.EnumArray.lengthBank.contains length))
    "generation drew a length above 64 or no uniform partial-Word length"
  -- Reductions: a dropped element or a narrower constructor comes with every
  -- case that has one, and every emitted candidate replays as a strictly
  -- smaller sealed case.
  for json in cases.toList.take 8 do
    let source ← get (Solcore.Synthesis.Source.EnumArray.caseProgram json)
    let reduced := Solcore.Synthesis.Source.EnumArray.reductions source
    ensure (!reduced.isEmpty) "a case has no reduction"
    ensure (Solcore.Synthesis.Source.EnumArray.elementCount source == 0 || reduced.any (fun candidate =>
        candidate.candidate.transactions.length == source.transactions.length &&
        Solcore.Synthesis.Source.EnumArray.elementCount candidate.candidate <
          Solcore.Synthesis.Source.EnumArray.elementCount source))
      "no dropped element"
    let shrunk ← get (Solcore.Synthesis.Source.EnumArray.shrinkCases json 64 fuel)
    for candidate in ← get (shrunk.getObjValAs? (Array Json) "cases") do
      ensure ((Solcore.Synthesis.Source.EnumArray.replayCase candidate fuel).toOption == some candidate)
        "a reduction does not replay"
      let _ ← sameAsModel (← get (Solcore.Synthesis.Source.EnumArray.caseProgram candidate)) fuel "reduction"
  -- Refusals: a choice beyond the constructors, a length for a constructor
  -- without `bytes`, a length above 64, four elements, a malformation that does
  -- not apply, and metadata that differs from the calldata or std's decision.
  let some json := cases.toList.find? (fun json => match Solcore.Synthesis.Source.EnumArray.caseProgram json with
      | .ok scenario => scenario.plan.shape.dynamic && scenario.plan.shape.payloads.any (· == .noWords)
      | .error _ => false) | throw (IO.userError "no mixed dynamic case")
  let scenario ← get (Solcore.Synthesis.Source.EnumArray.caseProgram json)
  let shape := scenario.plan.shape
  let transactions ← get (json.getObjValAs? (Array Json) "transactions")
  let some transaction := scenario.transactions.head? | throw (IO.userError "no transaction")
  let count := shape.constructors.length
  let some bytesIndex := shape.payloads.findIdx? (· == .bytes) | throw (IO.userError "no bytes")
  let some noneIndex := shape.payloads.findIdx? (· == .noWords) | throw (IO.userError "no field-less constructor")
  let element := fun (choice length : Nat) => (⟨choice, Word.zero, Word.zero, length⟩ : Element)
  let rebuilt (elements : List Element) (malformation : Malformation) : Json :=
    Solcore.Synthesis.Source.EnumArray.transactionJson shape
      {transaction with elements, first := Word.zero, second := Word.zero, malformation}
  ensure (Solcore.Synthesis.Source.EnumArray.caseProgram (json.setObjVal! "transactions" (.arr (transactions.set! 0
      (rebuilt [element bytesIndex 3, element noneIndex 0] (.padding 0 1)))))).toOption.isSome
    "a padded bytes element was refused"
  for (elements, malformation, label) in [
      ([element count 0], Malformation.none, "a choice beyond the constructors"),
      ([element noneIndex 1], .none, "a length for a constructor without bytes"),
      ([element bytesIndex 65], .none, "a length above 64"),
      ([element noneIndex 0, element noneIndex 0, element noneIndex 0, element noneIndex 0], .none, "four elements"),
      ([element noneIndex 0], .tail 0 (Word.ofNatModulo 3), "a tail offset without bytes"),
      ([element bytesIndex 32], .padding 0 0, "padding of a whole Word"),
      ([element noneIndex 0], .retag 0 noneIndex, "a retag of the element's constructor"),
      ([element noneIndex 0], .tag 0 (EnumArgument.tag (shape.constructors.getD 0 shape.first)), "a known tag as unknown"),
      ([element noneIndex 0], .tag 1 Word.zero, "a target past the elements"),
      ([element noneIndex 0, element noneIndex 0], .share 1 1, "an element sharing its own body"),
      ([element noneIndex 0], .entry 0 (Word.ofNatModulo 32), "an element's own canonical offset"),
      ([element noneIndex 0], .count (Word.ofNatModulo 1), "the canonical length"),
      ([element noneIndex 0], .offset (Word.ofNatModulo 128), "the canonical array offset"),
      ([element noneIndex 0], .truncate 3, "a cut inside the selector"),
      ([element noneIndex 0], .trailing 65 0, "65 trailing bytes")] do
    ensure (Solcore.Synthesis.Source.EnumArray.caseProgram
        (json.setObjVal! "transactions" (.arr (transactions.set! 0 (rebuilt elements malformation))))).toOption.isNone
      s!"{label} was admitted"
  let changedElement := Json.arr #[Solcore.Synthesis.Source.EnumArray.elementJson (element bytesIndex 4)]
  for (key, value, label) in [("elements", changedElement, "an element that differs from its calldata"),
      ("first", toJson "1", "an index that differs from its calldata"),
      ("stdRejection", toJson "0x08638556", "a std outcome that differs from std's decision"),
      ("calldata", toJson "0x00", "calldata that differs from its encoding")] do
    ensure (Solcore.Synthesis.Source.EnumArray.caseProgram (json.setObjVal! "transactions" (.arr (transactions.set! 0
        ((rebuilt [element bytesIndex 3] .none).setObjVal! key value))))).toOption.isNone
      s!"{label} was admitted"
  -- Plans: the struct is admitted; an extra field, a repeated or unknown name,
  -- three bytes constructors, one or five constructors and three Words are
  -- refused.
  let plan ← get (json.getObjVal? "enumArrayPlan")
  let step ← get (plan.getObjVal? "stepProgram")
  let planOf (constructors : List (String × String)) : Json := Json.mkObj [
    ("schema", toJson Solcore.Synthesis.Source.EnumArray.planSchema),
    ("constructors", toJson (constructors.map fun (name, fields) =>
      Json.mkObj [("name", toJson name), ("fields", toJson fields)])),
    ("stepProgram", step)]
  ensure (Solcore.Synthesis.Source.EnumArray.checkedPlan
      (planOf [("Idle", ""), ("Ready", "ScPair")])).toOption.isSome
    "a plan with the struct was refused"
  for (constructors, label) in [
      ([("Idle", ""), ("Idle", "uint256")], "a repeated name"),
      ([("Idle", ""), ("Other", "uint256")], "a name outside the bank"),
      ([("Idle", "bytes"), ("Ready", "bytes"), ("Pair", "bytes")], "three bytes constructors"),
      ([("Idle", "")], "one constructor"),
      ([("Idle", ""), ("Ready", ""), ("Pair", ""), ("Blob", ""), ("Q", "")], "five constructors"),
      ([("Idle", ""), ("Ready", "uint256,uint256,uint256")], "three Words")] do
    ensure (Solcore.Synthesis.Source.EnumArray.checkedPlan (planOf constructors)).toOption.isNone
      s!"a plan with {label} was admitted"
  ensure (Solcore.Synthesis.Source.EnumArray.checkedPlan (plan.setObjVal! "arity" (toJson 2))).toOption.isNone
    "a plan with an extra field was admitted"

end Tests.SourceEnumArrayCases
end

section
-- leanmerge: from Solcore.Test.SourceEnumArrayCorpus
/-! The fixed enum-array corpus checks actual original Core histories against
expectations computed without the Core contract: the Lean model, std's decision
over the calldata bytes and the protocol, in which each step runs alone in
Core. Coverage describes the checked steps' AST, the elements' field Words, the
canonical element counts, the decoded elements' positions and fields, the
decoded `bytes` lengths, the shapes' `bytes` constructor counts, every
malformation kind with the accepted ones, every std rejection, the carries into
decoded elements from an earlier committed, reverted or rejected transaction,
the node budgets of generated entries and the completions. Source/Rust/EVM
agreement is a separate external validation. -/
set_option autoImplicit false

namespace Tests.SourceEnumArrayCorpus
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
  ("generatorVersion", generatorVersion), ("profileVersion", EnumArray.profileVersion),
  ("functionVersion", Solcore.Synthesis.Core.EnumArray.version),
  ("templateVersion", EnumArray.templateVersion), ("stepProfileVersion", Aggregate.profileVersion),
  ("stepFunctionVersion", Aggregates.version), ("stepTemplateVersion", Aggregate.templateVersion),
  ("emitterVersion", EnumArray.emitterVersion), ("wrapperVersion", EnumArray.wrapperVersion)]

private def words (values : List Word) : List String := values.map fun value => toString value.val

/-- Every position of an array of one to three elements. -/
def positions : List String :=
  [1, 2, 3].flatMap fun count => (List.range count).map fun position => s!"{count}:{position}"

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

/-- std's four rejections: the fallback, a truncated read, an index past the
length and an unknown tag. -/
def rejections : List String := ["0x4924aef0", "0x08638556", "0x4e487b710000000000000000000000000000000000000000000000000000000000000032", "0x"]

/-- The malformations that std accepts in some case: changes it never reads,
another constructor's tag, a shared body, a longer length that still fits. -/
def acceptedKinds : List String := ["trailing", "count", "tag", "retag", "entry", "share", "unused", "length", "padding"]

/-- Decoded elements after an earlier committed transaction, body revert or
rejection. -/
def carries : List String := ["committed", "rollback", "rejection"]

private def kind (shape : Shape) : String := if shape.dynamic then "dynamic" else "static"

/-- Imported entries are emitted from their saved plan and sequence; generated
entries are regenerated from their seed. Both are checked by full replay. -/
private def entryCase (entry : Json) (fuel : Nat) : Except String Json := do
  if let .ok request := entry.getObjVal? "generation" then
    let some seed := (← request.getObjValAs? String "seed").toNat? | throw "invalid generation seed"
    let corpus := EnumArray.generateCases (Seed.ofNat seed) (← request.getObjValAs? Nat "maxProgramNodes") 1 1 fuel
    require ((← string corpus "status") == "complete") "generated entry was excluded"
    let some saved := (← corpus.getObjValAs? (Array Json) "cases")[0]? | throw "generated entry has no case"
    return saved
  let plan ← EnumArray.checkedPlan (← entry.getObjVal? "enumArrayPlan")
  let scenario ← EnumArray.checkedScenario plan
    (← EnumArray.decodeTransactions plan.shape (← entry.getObjVal? "transactions"))
  EnumArray.emitCase scenario (Json.mkObj [("kind", toJson "imported")]) fuel

private def templates (saved : Json) : Except String (List Nat) := do
  let origin ← (← saved.getObjVal? "provenance").getObjVal? "origin"
  if (← string origin "kind") != "enum-array-generated" then return []
  let helpers ← (← origin.getObjVal? "stepOrigin").getObjValAs? (List Json) "helpers"
  helpers.mapM fun helper => helper.getObjValAs? Nat "template"

/-- Original Core's output for std's data: the selector Word for an error's
four bytes or a panic's selector and code, the Word zero for none. -/
private def coreOutput (output : ByteArray) : String :=
  if output.size == 4 || output.size == 36 then
    Solcore.ContractRuntime.encodeBytesText (Solcore.ContractRuntime.encodeWordBytesBE
      (Word.ofNatModulo (Solcore.Synthesis.Stateful.StdCalldata.bigEndian output 0 4)))
  else if output.size == 0 then
    Solcore.ContractRuntime.encodeBytesText (Solcore.ContractRuntime.encodeWordBytesBE Word.zero)
  else Solcore.ContractRuntime.encodeBytesText output

/-- The Lean model's rows of a scenario, in the corpus's expected-row form:
original Core's revert Word for a rejection. -/
def modelRows (scenario : EnumArray.CheckedScenario) (fuel : Nat) : Except String (List Json) := do
  let some rows := Solcore.Synthesis.Stateful.EnumArrayExecution.model scenario.plan.step
      scenario.plan.shape fuel scenario.transactions | throw "the Lean model failed"
  return (rows.zip scenario.transactions).map fun (row, transaction) => Json.mkObj [
    ("id", toJson transaction.id), ("status", toJson (if row.reverted then "reverted" else "returned")),
    ("output", toJson (coreOutput row.output)),
    ("committedStorage", toJson (row.slots.zipIdx.map fun (value, slot) => Json.mkObj [
      ("slot", toJson (toString slot)), ("value", toJson (toString value.val))]))]

def validateManifest (manifest : Json) (fuel : Nat := 1000000) : Except String Json := do
  require ((← string manifest "schema") == "solcore-lean.semantic-storage-corpus-manifest.v1" &&
    (← string manifest "profile") == "stateful-enum-array-arguments" &&
    (← string manifest "coverageKind") == "step-core-ast-features") "unexpected enum-array manifest scope"
  for (key, expected) in versions do
    require ((← string manifest key) == expected) ("enum-array manifest changed " ++ key)
  let requiredFeatures ← strings manifest "requiredFeatures"
  require (sameMembers (← strings manifest "requiredInputs") (words EnumArray.boundaryInputs))
    "enum-array corpus must require all six boundary Words as element fields"
  require ((← manifest.getObjValAs? (List Nat) "requiredArrayElementCounts") == [0, 1, 2, 3] &&
    (← strings manifest "requiredArrayPositions") == positions &&
    (← strings manifest "requiredArrayFields") == fieldKinds)
    "enum-array corpus must require every element count, decoded position and field kind"
  require ((← manifest.getObjValAs? (List Nat) "requiredArrayBytesLengths") == EnumArray.lengthBank &&
    (← manifest.getObjValAs? (List Nat) "requiredArrayBytesConstructors") == [0, 1, 2] &&
    (← manifest.getObjValAs? (List Nat) "requiredArrayNodeBudgets") == [384, 512])
    "enum-array corpus must require the bank's bytes lengths, zero to two bytes constructors and both node budgets"
  require ((← strings manifest "requiredArrayMalformations") == EnumArray.malformationKinds &&
    (← strings manifest "requiredArrayRejections") == rejections &&
    (← strings manifest "requiredArrayAccepted") == acceptedKinds)
    "enum-array corpus must require every malformation kind, every rejection and the accepted malformations"
  require ((← strings manifest "requiredArrayCarries") == carries)
    "enum-array corpus must require carries from a committed, a reverted and a rejected transaction"
  require ((← manifest.getObjValAs? (List Nat) "requiredHelperCounts") == [1, 2, 3] &&
    (← manifest.getObjValAs? (List Nat) "requiredTransactionCounts") == [1, 2, 3])
    "enum-array corpus must require one to three helpers and transactions"
  require ((← (← manifest.getObjVal? "generationRecipeRequirements").getObjValAs? (List Nat) "templates") == [0, 1, 2, 3])
    "enum-array corpus must require all four step templates"
  require ((← strings manifest "requiredOutcomes") == ["returned", "reverted"])
    "enum-array corpus must require both outcomes"
  let requiredPatterns ← strings manifest "requiredCompletionPatterns"
  require (!requiredPatterns.isEmpty) "enum-array corpus must require completion patterns"
  let entries ← manifest.getObjValAs? (Array Json) "cases"
  require (0 < entries.size && entries.size ≤ 64) "enum-array corpus must contain 1..64 scenarios"
  let mut identifiers : List String := []
  let mut features : List String := []
  let mut fieldWords : List String := []
  let mut elementCounts : List Nat := []
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
    require (!identifiers.contains identifier) ("duplicate enum-array corpus id " ++ identifier)
    identifiers := identifier :: identifiers
    let saved ← entryCase entry fuel
    require ((← EnumArray.replayCase saved fuel) == saved) ("enum-array corpus entry did not replay: " ++ identifier)
    let scenario ← EnumArray.caseProgram saved
    if let .ok request := entry.getObjVal? "generation" then
      budgets := (budgets ++ [← request.getObjValAs? Nat "maxProgramNodes"]).eraseDups
    else
      require ((← saved.getObjVal? "enumArrayPlan") == (← entry.getObjVal? "enumArrayPlan") &&
        (← saved.getObjVal? "transactions") == (← entry.getObjVal? "transactions"))
        ("imported enum-array entry is not canonical: " ++ identifier)
    let caseFeatures := (← (← saved.getObjVal? "provenance").getObjValAs? (List String) "features").eraseDups
    require (sameMembers (← strings entry "expectedFeatures") caseFeatures)
      ("enum-array corpus features changed: " ++ identifier)
    let expected ← entry.getObjValAs? (List Json) "expectedHistory"
    require (expected == (← modelRows scenario fuel))
      ("the expected history differs from the Lean model: " ++ identifier)
    let history := EnumArray.observe scenario Solcore.Synthesis.Stateful.StorageExecution.fixtureBindings fuel
    require ((← string history "status") == "complete") ("enum-array corpus history incomplete: " ++ identifier)
    let observed ← history.getObjValAs? (List Json) "transactions"
    require (observed.length == expected.length) ("enum-array expected history length changed: " ++ identifier)
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
      let malformation := EnumArray.kindOf transaction.malformation
      kinds := (kinds ++ [malformation]).eraseDups
      elementCounts := (elementCounts ++ [transaction.elements.length]).eraseDups
      for element in transaction.elements do
        let payload := (shape.payloads[element.choice]?).getD .noWords
        if payload != .bytes && payload != .noWords then
          fieldWords := (fieldWords ++ words [element.a] ++
            (if payload == .oneWord then [] else words [element.b])).eraseDups
      let input := Solcore.Synthesis.Stateful.EnumArrayExecution.inputBytes shape transaction
      match Solcore.Synthesis.Stateful.EnumArrayExecution.stdDecode shape input with
      | .error data =>
          rejected := (rejected ++ [Solcore.ContractRuntime.encodeBytesText data]).eraseDups
          before := before ++ ["rejection"]
      | .ok decoded =>
          for (element, read) in [(decoded.first, transaction.first), (decoded.second, transaction.second)] do
            let decodedPayload := (shape.payloads[element.index - 1]?).getD .noWords
            if decoded.length.val ≤ 3 then
              decodedPositions := (decodedPositions ++ [s!"{decoded.length.val}:{read.val}"]).eraseDups
            decodedFields := (decodedFields ++ [kind shape ++ ":" ++ fieldName decodedPayload]).eraseDups
            if decodedPayload == .bytes then
              bytesLengths := (bytesLengths ++ [element.words.1.val]).eraseDups
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
  require (requiredFeatures.all features.contains) "enum-array corpus misses a required step feature"
  require ((words EnumArray.boundaryInputs).all fieldWords.contains) "enum-array corpus misses a boundary Word field"
  require ([0, 1, 2, 3].all elementCounts.contains && positions.all decodedPositions.contains &&
      fieldKinds.all decodedFields.contains)
    "enum-array corpus misses an element count, a decoded position or a field kind"
  require (EnumArray.lengthBank.all bytesLengths.contains && [0, 1, 2].all bytesConstructors.contains)
    "enum-array corpus misses a decoded bytes length or a bytes constructor count"
  require (EnumArray.malformationKinds.all kinds.contains && rejections.all rejected.contains &&
      acceptedKinds.all accepted.contains)
    "enum-array corpus misses a malformation kind, a rejection or an accepted malformation"
  require (carries.all carried.contains && [384, 512].all budgets.contains)
    "enum-array corpus misses a carry or a node budget"
  require ([1, 2, 3].all helperCounts.contains && [1, 2, 3].all transactionCounts.contains)
    "enum-array corpus misses a helper or transaction count"
  require ([0, 1, 2, 3].all templateUnion.contains) "enum-array corpus misses a generated template"
  require (["returned", "reverted"].all outcomes.contains && requiredPatterns.all patterns.contains)
    "enum-array corpus misses an observed outcome or completion pattern"
  return Json.mkObj [("profile", toJson "stateful-enum-array-arguments"), ("scenarios", toJson entries.size),
    ("transactions", toJson transactionTotal), ("elementCounts", toJson elementCounts),
    ("positions", toJson decodedPositions), ("fields", toJson decodedFields), ("bytesLengths", toJson bytesLengths),
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
  | .ok _ => throw (IO.userError "invalid enum-array corpus unexpectedly passed")

def testSourceEnumArrayCorpus : IO Unit := do
  let manifest ← checked (Json.parse (← IO.FS.readFile "scripts/semantic-enum-array-corpus.json"))
  let summary ← checked (validateManifest manifest)
  let entries ← checked (manifest.getObjValAs? (Array Json) "cases")
  let some first := entries[0]? | throw (IO.userError "missing first enum-array case")
  let some generatedEntry := entries.find? (fun entry => (entry.getObjVal? "generation").isOk) |
    throw (IO.userError "missing generated enum-array case")
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
  -- A transaction's elements, indices and malformation are checked against its
  -- calldata, and a constructor's name and fields against the plan.
  let transactions ← checked (first.getObjValAs? (Array Json) "transactions")
  let elements ← checked (transactions[0]!.getObjValAs? (Array Json) "elements")
  rejects (validateManifest (replace first (first.setObjVal! "transactions" (.arr (transactions.set! 0
    (transactions[0]!.setObjVal! "elements" (.arr elements.pop)))))))
  rejects (validateManifest (replace first (first.setObjVal! "transactions" (.arr (transactions.set! 0
    (transactions[0]!.setObjVal! "second" (toJson "7")))))))
  rejects (validateManifest (replace first (first.setObjVal! "transactions" (.arr (transactions.set! 0
    (transactions[0]!.setObjVal! "malformation" (Json.mkObj [("kind", toJson "short"), ("bytes", toJson 2)])))))))
  let plan ← checked (first.getObjVal? "enumArrayPlan")
  let constructors ← checked (plan.getObjValAs? (Array Json) "constructors")
  let renamed := constructors.set! 0 (constructors[0]!.setObjVal! "name" (toJson "Rejected"))
  -- The struct and two Words are the same on the wire and in Core, so the
  -- changed fields change the tag: none and one Word.
  let refielded := constructors.set! 0 (constructors[0]!.setObjVal! "fields"
    (toJson (if (constructors[0]!.getObjValAs? String "fields").toOption == some "" then "uint256" else "")))
  for changed in [renamed, refielded] do
    rejects (validateManifest (replace first (first.setObjVal! "enumArrayPlan"
      (plan.setObjVal! "constructors" (.arr changed)))))
  rejects (validateManifest (replace first (first.setObjVal! "expectedFeatures" (toJson ([] : List String)))))
  rejects (validateManifest (manifest.setObjVal! "cases" (.arr (entries.push first))))
  for (key, value) in [
      ("profile", toJson "stateful-storage"), ("templateVersion", toJson "forged"),
      ("cases", .arr #[]), ("requiredInputs", toJson ([] : List String)),
      ("requiredArrayElementCounts", toJson [1, 2, 3]),
      ("requiredArrayPositions", toJson (["1:0"] : List String)),
      ("requiredArrayFields", toJson (["static:none"] : List String)),
      ("requiredArrayBytesLengths", toJson [0, 1, 32]), ("requiredArrayBytesConstructors", toJson [1, 2]),
      ("requiredArrayNodeBudgets", toJson [384]), ("requiredArrayCarries", toJson (["committed"] : List String)),
      ("requiredArrayMalformations", toJson (["none", "short"] : List String)),
      ("requiredArrayRejections", toJson (["0x"] : List String)),
      ("requiredArrayAccepted", toJson (["trailing"] : List String)),
      ("requiredHelperCounts", toJson [1, 2]),
      ("requiredCompletionPatterns", toJson (["returned,returned,returned,returned"] : List String))] do
    rejects (validateManifest (manifest.setObjVal! key value))
  rejects (validateManifest manifest 0)
  IO.println summary.compress

end Tests.SourceEnumArrayCorpus
end

section
-- leanmerge: from Solcore.Test.SourceEnumArrayGolden
/-! Golden cases for the enum-array profile: std's exact acceptance and
refusals of calldata arrays of a user enum. Every expected row is written out
as hexadecimal text computed outside Lean from the definitions, by the probe's
independent model of std's decoder, which equalled imported Hull and Sonatina
O0, O2 and Yul on Anvil on every probe transaction, not by either Lean model;
tags and selectors come from `cast keccak`. The steps add a known constant `c`,
so an accepted transaction computes `r = slot 0 + L + both elements' index and
Words + c`, writes `r`, the length and both elements to slots 0 to 9, and
returns `r`; odd decoded flags revert with `r` and keep the prior slots. A
rejection is std's revert data: an error selector, `Panic(0x32)` among
them, or nothing for an unknown tag. The scenarios cover static and dynamic
element types, every field kind with the struct, empty and three-element
arrays, indices past the length and at `2^256 - 1`, unread malformed elements,
shared bodies, every malformation kind with accepted and rejected entries, and
the order of the checks. Original Core gives each row under the selector and
empty-revert rules, and the Lean model gives it exactly. -/
set_option autoImplicit false

namespace Tests.SourceEnumArrayGolden

open Lean
open Solcore.Core (Word)
open Solcore.ContractRuntime
open Solcore.Synthesis.Core
open Solcore.Synthesis.Core.EnumArgument (Constructor Shape)
open Solcore.Synthesis.Stateful
open Solcore.Synthesis.Stateful.EnumArrayExecution (Element Transaction Malformation)

private def get {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def w (value : Nat) : Word := Word.ofNatModulo value

/-- The step `x ↦ x + c`: aggregate template 0 around the constant scalar. -/
private def step (c : Nat) : IO Aggregates.CheckedDAG := do
  let some dag := Aggregates.CheckedDAG.ofParts? [Solcore.Synthesis.Source.Aggregate.template 0 (.word (w c))]
      (.apply (.var 1) (.var 0)) | throw (IO.userError "constant step failed admission")
  return dag

/-- The expected row: status, std's whole return or revert data as hexadecimal
text, empty for an unknown tag, and slots zero to nine. An index past the
length is std's `Panic(0x32)`. -/
private structure Expected where
  status : String
  output : String
  values : List Nat

private def slots (values : List Nat) : Json :=
  toJson ((List.range EnumArray.slotCount).map fun slot => Json.mkObj [
    ("slot", toJson (toString slot)), ("value", toJson (toString (values.getD slot 0)))])

private def el (choice a b length : Nat) : Element := ⟨choice, w a, w b, length⟩

private def tx (index flags : Nat) (elements : List Element) (first second : Nat) (malformation : Malformation) :
    Transaction :=
  ⟨"tx-" ++ toString index, w flags, elements, w first, w second, malformation⟩

-- The tags `keccak256("Name(fields)")`, as `cast keccak` writes them.
-- Blob(bytes)
private def tagBlobBytes : String := "d05ce3dc4caf4a4b252e3323bde615dc3b9d54623e1859c892f0b4ecf5e45164"
-- Idle()
private def tagIdleUnit : String := "ae897c555b7596dee56949d599aa959af71416324ac27ef76dd898923ab34d4f"
-- Ready()
private def tagReadyUnit : String := "6e12fa0ff1c6b8acb2181ba65fc2867fd8d895d0af9f39674b64abc5ff79275b"
-- Ready(uint256,uint256)
private def tagReadyStruct : String := "1ee0fddb687f7d726adbdd32a0b3afe38d0593fe9dc00a18a5f4acd116e8b7c9"
-- Rejected()
private def tagRejectedUnit : String := "efde6dcf3c2196c5705e848c09f0659d33de3ca0248be3ab40852d1bafc0f1e3"

-- The selectors of `run(uint256,S[],uint256,uint256)`, as `cast keccak` writes them.
-- run(uint256,sum(uint256,uint256,sum(,uint256))[],uint256,uint256)
private def selectorStaticWords : String := "0x7b340d0f"
-- run(uint256,sum(bytes,sum(uint256,sum(uint256,uint256,)))[],uint256,uint256)
private def selectorDynamicWords : String := "0x6c89cba6"
-- run(uint256,sum(bytes,bytes)[],uint256,uint256)
private def selectorTwoBytes : String := "0xbde4b3a9"
-- run(uint256,sum(uint256,uint256,sum(,bytes))[],uint256,uint256)
private def selectorStructFields : String := "0x7608c09b"
-- run(uint256,sum(,)[],uint256,uint256)
private def selectorTagsOnly : String := "0x2dde7185"

private def staticWordsRows : List (Transaction × Expected) := [
  (tx 0 0 [el 0 7 9 0, el 2 3 0 0] 0 1 .none,
    ⟨"returned", "000000000000000000000000000000000000000000000000000000000000001e", [30, 2, 1, 7, 9, 0, 3, 3, 0, 0]⟩),
  (tx 1 1 [el 1 0 0 0] 0 0 .none,
    ⟨"reverted", "0000000000000000000000000000000000000000000000000000000000000028", [30, 2, 1, 7, 9, 0, 3, 3, 0, 0]⟩),
  (tx 2 0 [el 2 (2 ^ 256 - 1) 0 0, el 1 0 0 0] 0 1 (.unused 1 (w (2 ^ 256 - 1))),
    ⟨"returned", "0000000000000000000000000000000000000000000000000000000000000029", [41, 2, 3, (2 ^ 256 - 1), 0, 0, 2, 0, 0, 0]⟩),
  (tx 3 0 [el 0 1 2 0, el 2 4 0 0] 1 0 (.tag 0 (w 0)),
    ⟨"reverted", "", [41, 2, 3, (2 ^ 256 - 1), 0, 0, 2, 0, 0, 0]⟩),
  (tx 4 0 [el 0 1 2 0, el 2 4 0 0] 1 1 (.tag 0 (w 0)),
    ⟨"returned", "000000000000000000000000000000000000000000000000000000000000003e", [62, 2, 3, 4, 0, 0, 3, 4, 0, 0]⟩),
  (tx 5 0 [el 2 5 0 0] 0 0 (.count (w 2)),
    ⟨"reverted", "08638556", [62, 2, 3, 4, 0, 0, 3, 4, 0, 0]⟩),
  (tx 6 0 [] 0 0 .none,
    ⟨"reverted", "4e487b710000000000000000000000000000000000000000000000000000000000000032", [62, 2, 3, 4, 0, 0, 3, 4, 0, 0]⟩),
  (tx 7 2 [el 0 6 8 0] 0 0 (.retag 0 2),
    ⟨"returned", "0000000000000000000000000000000000000000000000000000000000000056", [86, 1, 3, 6, 0, 0, 3, 6, 0, 0]⟩),
  (tx 8 0 [el 0 1 2 0] 0 0 (.truncate 131),
    ⟨"reverted", "08638556", [86, 1, 3, 6, 0, 0, 3, 6, 0, 0]⟩),
  (tx 9 0 [el 1 0 0 0] 0 0 (.short 3),
    ⟨"reverted", "4924aef0", [86, 1, 3, 6, 0, 0, 3, 6, 0, 0]⟩),
  (tx 10 0 [el 2 4 0 0, el 0 1 1 0] 1 (2 ^ 256 - 1) .none,
    ⟨"reverted", "4e487b710000000000000000000000000000000000000000000000000000000000000032", [86, 1, 3, 6, 0, 0, 3, 6, 0, 0]⟩)]

private def dynamicWordsRows : List (Transaction × Expected) := [
  (tx 0 0 [el 0 1 2 33, el 2 3 7 0, el 3 0 0 0] 0 1 .none,
    ⟨"returned", "da3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18ec8", [(2 ^ 256 - 17089871545297914264645409054526021057658525754966106959376225893052256776504), 3, 1, 33, (2 ^ 256 - 44228642460293897567044858665937249460768678410975614156124097144906896535915), 27138770914995983302399449611411228403110152656009507196747871251854639759360, 3, 3, 7, 0]⟩),
  (tx 1 0 [el 1 5 0 0, el 3 0 0 0] 0 1 (.entry 1 (w 0)),
    ⟨"reverted", "", [(2 ^ 256 - 17089871545297914264645409054526021057658525754966106959376225893052256776504), 3, 1, 33, (2 ^ 256 - 44228642460293897567044858665937249460768678410975614156124097144906896535915), 27138770914995983302399449611411228403110152656009507196747871251854639759360, 3, 3, 7, 0]⟩),
  (tx 2 0 [el 1 5 0 0, el 2 6 7 0] 0 1 (.share 1 0),
    ⟨"returned", "da3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18ed9", [(2 ^ 256 - 17089871545297914264645409054526021057658525754966106959376225893052256776487), 2, 2, 5, 0, 0, 2, 5, 0, 0]⟩),
  (tx 3 0 [el 1 5 0 0] 0 0 (.entry 0 (w 129)),
    ⟨"reverted", "08638556", [(2 ^ 256 - 17089871545297914264645409054526021057658525754966106959376225893052256776487), 2, 2, 5, 0, 0, 2, 5, 0, 0]⟩),
  (tx 4 0 [el 0 4 5 1] 0 0 (.length 0 (w 32)),
    ⟨"returned", "ca3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18f1d", [(2 ^ 256 - 24326877122630176478618595617569015298487899796568642211842324893546827378915), 1, 1, 32, 54277541829991966604798899222822456806220305312019014393495742503709279518720, 0, 1, 32, 54277541829991966604798899222822456806220305312019014393495742503709279518720, 0]⟩),
  (tx 5 0 [el 0 4 5 1] 0 0 (.length 0 (w 33)),
    ⟨"reverted", "08638556", [(2 ^ 256 - 24326877122630176478618595617569015298487899796568642211842324893546827378915), 1, 1, 32, 54277541829991966604798899222822456806220305312019014393495742503709279518720, 0, 1, 32, 54277541829991966604798899222822456806220305312019014393495742503709279518720, 0]⟩),
  (tx 6 0 [el 0 1 2 32] 0 0 (.tail 0 (w 0)),
    ⟨"reverted", "08638556", [(2 ^ 256 - 24326877122630176478618595617569015298487899796568642211842324893546827378915), 1, 1, 32, 54277541829991966604798899222822456806220305312019014393495742503709279518720, 0, 1, 32, 54277541829991966604798899222822456806220305312019014393495742503709279518720, 0]⟩),
  (tx 7 0 [el 0 1 1 1] 0 0 (.padding 0 0),
    ⟨"returned", "063779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18f23", [2811893792365806823780853993842213104622252859440864984905546358307812380451, 1, 1, 1, (2 ^ 256 - 44326659161160106060585767698638339725079916004815528421354856378029244940288), 0, 1, 1, (2 ^ 256 - 44326659161160106060585767698638339725079916004815528421354856378029244940288), 0]⟩),
  (tx 8 0 [el 2 1 2 0] 0 0 (.offset (w 57896044618658097711785492504343953926634992332820282019728792003956564819968)),
    ⟨"reverted", "08638556", [2811893792365806823780853993842213104622252859440864984905546358307812380451, 1, 1, 1, (2 ^ 256 - 44326659161160106060585767698638339725079916004815528421354856378029244940288), 0, 1, 1, (2 ^ 256 - 44326659161160106060585767698638339725079916004815528421354856378029244940288), 0]⟩),
  (tx 9 0 [el 1 9 0 0, el 1 8 0 0] 0 1 (.count (w 3)),
    ⟨"returned", "063779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18f3c", [2811893792365806823780853993842213104622252859440864984905546358307812380476, 3, 2, 9, 0, 0, 2, 8, 0, 0]⟩)]

private def twoBytesRows : List (Transaction × Expected) := [
  (tx 0 0 [el 0 1 2 64, el 1 3 4 31] 1 0 .none,
    ⟨"returned", "b54cda58fbbee883b5ac82422d92b138630cec87b5ceadebd28a7c6ae4895725", [(2 ^ 256 - 33787676287130994555127181978247681058072101134572556857829414853615119935707), 2, 2, 31, (2 ^ 256 - 16893838143565497277563590989123840529036050567286278428914707426807559968000), 0, 1, 64, (2 ^ 256 - 44228642460293897567044858665937249460768678410975614156124097144906896535915), 27334804316728400289481267676813408931732627843689335727209389718099336568106]⟩),
  (tx 1 1 [el 1 (2 ^ 256 - 1) 1 32] 0 0 .none,
    ⟨"reverted", "78dde6e5fd29f057ce73018173b720d042089dafce89c947e1b1a84743063a42", [(2 ^ 256 - 33787676287130994555127181978247681058072101134572556857829414853615119935707), 2, 2, 31, (2 ^ 256 - 16893838143565497277563590989123840529036050567286278428914707426807559968000), 0, 1, 64, (2 ^ 256 - 44228642460293897567044858665937249460768678410975614156124097144906896535915), 27334804316728400289481267676813408931732627843689335727209389718099336568106]⟩),
  (tx 2 0 [el 1 2 3 0] 0 0 (.trailing 64 2),
    ⟨"returned", "b54cda58fbbee883b5ac82422d92b138630cec87b5ceadebd28a7c6ae489572c", [(2 ^ 256 - 33787676287130994555127181978247681058072101134572556857829414853615119935700), 1, 2, 0, 0, 0, 2, 0, 0, 0]⟩),
  (tx 3 0 [el 0 2 3 63] 0 0 (.selector 2147483648),
    ⟨"reverted", "4924aef0", [(2 ^ 256 - 33787676287130994555127181978247681058072101134572556857829414853615119935700), 1, 2, 0, 0, 0, 2, 0, 0, 0]⟩),
  (tx 4 2 [el 0 1 1 33, el 1 1 1 1] 0 1 (.offset (w 0)),
    ⟨"reverted", "", [(2 ^ 256 - 33787676287130994555127181978247681058072101134572556857829414853615119935700), 1, 2, 0, 0, 0, 2, 0, 0, 0]⟩),
  (tx 5 0 [el 0 7 7 17] 0 0 (.retag 0 1),
    ⟨"returned", "5c55827df1d1b1b7083f07874293a411490cec87b5ceadebd28a7c6ae4895755", [41763864692651612047670706750758273610784823299369356856714969782160273790805, 1, 2, 17, 37775770489891303301398944364502977334428462216970956857272192317887696863232, 0, 2, 17, 37775770489891303301398944364502977334428462216970956857272192317887696863232, 0]⟩)]

private def structFieldsRows : List (Transaction × Expected) := [
  (tx 0 0 [el 0 11 12 0, el 2 5 6 17, el 1 0 0 0] 0 1 .none,
    ⟨"returned", "1715609f7c746c6dc20fc1e1d0a4e90452000000000000000000000000000032", [10440966173162903011917676687689568402695856741602633618718639110637867761714, 3, 1, 11, 12, 0, 3, 17, 10440966173162903011917676687689568402695856741602633618718639110637867761664, 0]⟩),
  (tx 1 0 [el 0 1 1 0] 0 0 (.retag 0 1),
    ⟨"returned", "1715609f7c746c6dc20fc1e1d0a4e9045200000000000000000000000000003a", [10440966173162903011917676687689568402695856741602633618718639110637867761722, 1, 2, 0, 0, 0, 2, 0, 0, 0]⟩),
  (tx 2 0 [el 2 1 2 0] 0 0 .none,
    ⟨"returned", "1715609f7c746c6dc20fc1e1d0a4e90452000000000000000000000000000044", [10440966173162903011917676687689568402695856741602633618718639110637867761732, 1, 3, 0, 0, 0, 3, 0, 0, 0]⟩),
  (tx 3 0 [el 0 3 4 0] 0 0 (.truncate 244),
    ⟨"reverted", "08638556", [10440966173162903011917676687689568402695856741602633618718639110637867761732, 1, 3, 0, 0, 0, 3, 0, 0, 0]⟩),
  (tx 4 0 [el 1 0 0 0] 1 0 .none,
    ⟨"reverted", "4e487b710000000000000000000000000000000000000000000000000000000000000032", [10440966173162903011917676687689568402695856741602633618718639110637867761732, 1, 3, 0, 0, 0, 3, 0, 0, 0]⟩)]

private def tagsOnlyRows : List (Transaction × Expected) := [
  (tx 0 0 [el 0 0 0 0, el 1 0 0 0, el 0 0 0 0] 2 1 .none,
    ⟨"returned", "000000000000000000000000000000000000000000000000000000000000000a", [10, 3, 1, 0, 0, 0, 2, 0, 0, 0]⟩),
  (tx 1 0 [el 1 0 0 0] 0 0 (.count (w 3618502788666131106986593281521497120414687020801267626233049500247285301248)),
    ⟨"reverted", "08638556", [10, 3, 1, 0, 0, 0, 2, 0, 0, 0]⟩),
  (tx 2 0 [el 1 0 0 0] 0 0 (.count (w 0)),
    ⟨"reverted", "4e487b710000000000000000000000000000000000000000000000000000000000000032", [10, 3, 1, 0, 0, 0, 2, 0, 0, 0]⟩),
  (tx 3 0 [el 1 0 0 0, el 0 0 0 0] 1 0 (.tag 0 (w (2 ^ 256 - 8108102160884874896242699696681862164538485728477310456048732216610957744293))),
    ⟨"reverted", "", [10, 3, 1, 0, 0, 0, 2, 0, 0, 0]⟩),
  (tx 4 0 [el 0 0 0 0] 0 0 (.offset (w 32)),
    ⟨"reverted", "08638556", [10, 3, 1, 0, 0, 0, 2, 0, 0, 0]⟩)]

private def scenarios : List (String × Nat × List Constructor × String × String × List (Transaction × Expected)) := [
    ("static-words", 5, [⟨"Pair", .twoWords⟩, ⟨"Idle", .noWords⟩, ⟨"Q", .oneWord⟩],
      "run(uint256,sum(uint256,uint256,sum(,uint256))[],uint256,uint256)", selectorStaticWords, staticWordsRows),
    ("dynamic-words", 1, [⟨"Blob", .bytes⟩, ⟨"Ready", .oneWord⟩, ⟨"Settled", .twoWords⟩, ⟨"Rejected", .noWords⟩],
      "run(uint256,sum(bytes,sum(uint256,sum(uint256,uint256,)))[],uint256,uint256)", selectorDynamicWords, dynamicWordsRows),
    ("two-bytes", 2, [⟨"OverflowedAccumulator", .bytes⟩, ⟨"Q", .bytes⟩],
      "run(uint256,sum(bytes,bytes)[],uint256,uint256)", selectorTwoBytes, twoBytesRows),
    ("struct-fields", 3, [⟨"Ready", .pair⟩, ⟨"Idle", .noWords⟩, ⟨"Blob", .bytes⟩],
      "run(uint256,sum(uint256,uint256,sum(,bytes))[],uint256,uint256)", selectorStructFields, structFieldsRows),
    ("tags-only", 4, [⟨"Idle", .noWords⟩, ⟨"Ready", .noWords⟩],
      "run(uint256,sum(,)[],uint256,uint256)", selectorTagsOnly, tagsOnlyRows)]

/-- Original Core reverts with one Word: an error selector stands for std's
four bytes, the panic's selector for its selector and code, and the Word zero
for its empty revert data. -/
private def coreOutput (output : String) : String :=
  "0x" ++ if output.length == 8 || output.length == 72 then
      String.ofList (List.replicate 56 '0') ++ String.ofList (output.toList.take 8)
    else if output.isEmpty then String.ofList (List.replicate 64 '0') else output

private def check (name : String) (row : Json) (model : EnumArrayExecution.ModelRow) (expected : Expected) :
    IO Unit := do
  ensure ((row.getObjValAs? String "status").toOption == some expected.status &&
      (row.getObjValAs? String "output").toOption == some (coreOutput expected.output) &&
      (row.getObjVal? "committedStorage").toOption == some (slots expected.values))
    s!"{name}: original Core differs from the expected row {row.compress}"
  ensure (model.reverted == (expected.status == "reverted") &&
      encodeBytesText model.output == "0x" ++ expected.output &&
      model.slots == (List.range EnumArray.slotCount).map (fun slot => w (expected.values.getD slot 0)))
    s!"{name}: the Lean model differs from the expected row"

/-- Original Core's status and output on raw calldata from empty storage. -/
private def runRaw (contract : CheckedCoreContract) (bytes : ByteArray) : IO (String × String) := do
  let bindings := StorageExecution.fixtureBindings
  let registry : CheckedContractRegistry := {
    lookup := fun target => if target = bindings.address then some contract else none }
  let world := StorageExecution.initialWorldForContract contract bindings
  if bounded : bytes.size < Solcore.Core.wordModulus then
    let some ⟨resolved, installed⟩ := registry.resolve? world bindings.address
      | throw (IO.userError "the contract did not resolve")
    let invocation : TopLevelInvocation := {
      target := bindings.address, caller := bindings.caller, callValue := Word.zero,
      inputData := ⟨bytes, bounded⟩ }
    match TopLevelExecution.run resolved invocation installed 1000000 with
    | .completed terminal =>
        match terminal.outcome with
        | .returned out => return ("returned", encodeBytesText out)
        | .reverted out => return ("reverted", encodeBytesText out)
        | .trapped _ => return ("trapped", "")
    | .outOfFuel .. => return ("out-of-fuel", "")
  else throw (IO.userError "calldata exceeds the Word bound")

/-- Decisions that one malformation cannot reach, on raw calldata of the second
scenario's `[Ready(5), Rejected]` read at 0 and 1, whose region starts at 164
and whose bodies at 228 and 324: an aliased table entry, the first index
before the second element, the tag before the fields, the array's head before
the indices, the selector before the head, and an unread element's offset. -/
private def orderRows (shape : Shape) : List (String × ByteArray × String × String) :=
  let canonical := EnumArrayExecution.inputBytes shape (tx 0 0 [el 1 5 0 0, el 3 0 0 0] 0 1 .none)
  let put := StdCalldata.replaceWord
  let rejected := EnumArgument.tag ⟨"Rejected", .noWords⟩
  let wrong := StdCalldata.Change.apply canonical (.selector 1)
  [("aliased table entry", put (put (put (put canonical (164 + 32) rejected) 164 (w 32)) 68 (w 0)) 100 (w 0),
      "returned", "000000000000000000000000000000000000000000000000000000000000000b"),
    ("first out of bounds before the second's unknown tag", put (put canonical 68 (w 2)) 324 (w 7),
      "reverted", "4e487b710000000000000000000000000000000000000000000000000000000000000032"),
    ("unknown tag, fields cut", (put canonical 228 (w 7)).extract 0 276, "reverted", ""),
    ("array offset past the end, index out of bounds", put (put canonical 36 (w (canonical.size - 3))) 68 (w 5),
      "reverted", "08638556"),
    ("wrong selector, head cut", wrong.extract 0 40, "reverted", "4924aef0"),
    ("unread element offset past the end", put (put canonical (164 + 32) (w (2 ^ 256 - 1))) 100 (w 0),
      "returned", "0000000000000000000000000000000000000000000000000000000000000011")]

def testSourceEnumArrayGolden : IO Unit := do
  let fuel := 1000000
  -- Lean's Keccak-256 tags equal the ones written out; a struct's tag is its fields'.
  ensure (encodeBytesText (encodeWordBytesBE (EnumArgument.tag ⟨"Ready", .pair⟩)) == "0x" ++ tagReadyStruct &&
      encodeBytesText (encodeWordBytesBE (EnumArgument.tag ⟨"Blob", .bytes⟩)) == "0x" ++ tagBlobBytes &&
      encodeBytesText (encodeWordBytesBE (EnumArgument.tag ⟨"Ready", .noWords⟩)) == "0x" ++ tagReadyUnit &&
      encodeBytesText (encodeWordBytesBE (EnumArgument.tag ⟨"Rejected", .noWords⟩)) == "0x" ++ tagRejectedUnit &&
      encodeBytesText (encodeWordBytesBE (EnumArgument.tag ⟨"Idle", .noWords⟩)) == "0x" ++ tagIdleUnit)
    "a constructor tag differs from keccak256 of its signature"
  for (name, constant, constructors, signature, selector, rows) in scenarios do
    let step ← step constant
    let some shape := Solcore.Synthesis.Source.EnumArgument.Shape.ofList? constructors
      | throw (IO.userError s!"{name}: the shape has fewer than two constructors")
    ensure (EnumArray.signature shape == signature && Solcore.Synthesis.Source.EnumArray.selectorText shape == selector)
      s!"{name}: the signature or selector differs from std's structural signature"
    let some plan := EnumArray.CheckedPlan.ofParts? step shape
      | throw (IO.userError s!"{name}: the enum-array wrapper failed admission")
    let transactions := rows.map Prod.fst
    ensure (transactions.all (Solcore.Synthesis.Source.EnumArray.admits shape)) s!"{name}: a transaction is not admitted"
    for (transaction, expected) in rows do
      let rejected := expected.status == "reverted" && expected.output.length != 64
      ensure (Solcore.Synthesis.Source.EnumArray.prescribed shape transaction ==
          (if rejected then some ("0x" ++ expected.output) else none))
        s!"{name} {transaction.id}: the prescribed std outcome differs from the expected row"
    let history := EnumArrayExecution.observe plan transactions StorageExecution.fixtureBindings fuel
    ensure ((history.getObjValAs? String "status").toOption == some "complete") s!"{name}: the history is incomplete"
    let observed ← get (history.getObjValAs? (Array Json) "transactions")
    let some modelled := EnumArrayExecution.model step shape fuel transactions
      | throw (IO.userError s!"{name}: the Lean model failed")
    ensure (observed.size == rows.length && modelled.length == rows.length) s!"{name}: a row is missing"
    for ((row, model), (transaction, expected)) in (observed.toList.zip modelled).zip rows do
      check s!"{name} {transaction.id}" row model expected
  -- The order of std's checks, on raw calldata, for Core and the Lean model alike.
  let some (_, _, constructors, _, _, _) := scenarios[1]? | throw (IO.userError "no dynamic scenario")
  let some shape := Solcore.Synthesis.Source.EnumArgument.Shape.ofList? constructors | throw (IO.userError "no shape")
  let some plan := EnumArray.CheckedPlan.ofParts? (← step 1) shape | throw (IO.userError "no plan")
  for (label, bytes, status, output) in orderRows shape do
    let (actual, data) ← runRaw plan.contract bytes
    let decided := match EnumArrayExecution.stdDecode shape bytes with
      | .error data => some (encodeBytesText data)
      | .ok _ => none
    ensure (actual == status && data == coreOutput output &&
        decided == (if status == "returned" then none else some ("0x" ++ output)))
      s!"{label}: std's order of checks differs ({actual} {data})"
  -- A changed expectation fails: the first static row read as a rejection.
  let some (transaction, expected) := staticWordsRows.head? | throw (IO.userError "no static row")
  ensure (Solcore.Synthesis.Source.EnumArray.prescribed (← (Solcore.Synthesis.Source.EnumArgument.Shape.ofList?
        [⟨"Pair", .twoWords⟩, ⟨"Idle", .noWords⟩, ⟨"Q", .oneWord⟩]).getDM
        (throw (IO.userError "no shape"))) transaction == none &&
      coreOutput expected.output != coreOutput "08638556")
    "a changed expectation is not detected"

end Tests.SourceEnumArrayGolden
end

section
-- leanmerge: from Solcore.Test.SourceEnumCases
/-! The `runtime-enums` profile. Its Core reference compiles every match to
nested `caseE` with fall-through thunks; it agrees with a direct interpreter
of the plan's first-match semantics and scoping on generated plans, and a
fixture's source and results are golden, the results from a separate Python
model. Admission refuses unreachable arms, non-exhaustive matches and
ill-formed plans; generation draws every shape and replays exactly; tampering
is refused, and reductions are strictly smaller and replay. -/
set_option autoImplicit false

namespace Tests.SourceEnumCases

open Lean
open Solcore.Core (Word)
open Solcore.Synthesis.Core (Seed)
open Solcore.Synthesis.Core.Enums
open Solcore.Synthesis.Source

private def get {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def errorOf {α : Type} : Except String α → Option String
  | .error error => some error
  | .ok _ => none

private def fuel : Nat := 1000000

private def modulus : Nat := 2 ^ 256

private def cases (corpus : Json) : IO (Array Json) :=
  get (corpus.getObjValAs? (Array Json) "cases")

private def excluded (corpus : Json) : IO (Array Json) :=
  get (corpus.getObjValAs? (Array Json) "excluded")

private def provenance (case : Json) : IO Json := get (case.getObjVal? "provenance")

private def run (program : Solcore.Core.Wire.Program) : IO Nat :=
  match program.toCore.runStateful fuel with
  | .done (.word value) _ => pure value.val
  | _ => throw (IO.userError "a reference program did not return a Word")

/-! A direct interpreter of a plan: values as trees, the first arm whose
patterns accept them, names by their innermost binding. It shares no code
with the Core compilation. -/

private inductive Runtime where
  | word (value : Nat)
  | tuple (left right : Runtime)
  | ctor (index : Nat) (fields : List Runtime)
  deriving Inhabited

private def evaluate (input : Nat) : Value → Runtime
  | .leaf .input _ => .word input
  | .leaf .add constant => .word ((input + constant) % modulus)
  | .leaf .xor constant => .word (input ^^^ constant)
  | .leaf .mul constant => .word ((input * constant) % modulus)
  | .tuple left right => .tuple (evaluate input left) (evaluate input right)
  | .ctor0 index _ => .ctor index []
  | .ctor1 index field _ => .ctor index [evaluate input field]
  | .ctor2 index first second _ => .ctor index [evaluate input first, evaluate input second]

private def bind : Pat → Runtime → Option (List (Nat × Runtime))
  | .wild, _ => some []
  | .var name, value => some [(name, value)]
  | .tuple left right, .tuple first second => do return (← bind left first) ++ (← bind right second)
  | .ctor0 index _, .ctor other [] => if index = other then some [] else none
  | .ctor1 index field _, .ctor other [value] => if index = other then bind field value else none
  | .ctor2 index left right _, .ctor other [first, second] =>
      if index = other then do return (← bind left first) ++ (← bind right second) else none
  | _, _ => none

private def bindRow (patterns : List Pat) (values : List Runtime) : Option (List (Nat × Runtime)) :=
  if patterns.isEmpty then some []
  else (patterns.zip values).foldlM (fun bound (pattern, value) => do return bound ++ (← bind pattern value)) []

private def termValue (scope : List (Nat × Runtime)) : Solcore.Synthesis.Core.Enums.Term → Option Nat
  | .constant value => some value
  | .name name => match scope.find? (·.1 = name) with
      | some (_, .word value) => some value
      | _ => none

private def operate : Op → Nat → Nat → Nat
  | .add, left, right => (left + right) % modulus
  | .sub, left, right => (left + modulus - right) % modulus
  | .xor, left, right => left ^^^ right
  | .mul, left, right => (left * right) % modulus

private def bodyValue (scope : List (Nat × Runtime)) (body : Body) : Option Nat := do
  let first ← termValue scope body.first
  let folded ← body.rest.foldlM (fun accumulated (op, term) => do
    return operate op accumulated (← termValue scope term)) first
  return (folded + body.constant) % modulus

private def matchArms (arms : List Arm) (values : List Runtime) (w : Nat) : Option Nat := do
  let (bound, arm) ← arms.findSome? fun arm => (bindRow arm.patterns values).map (·, arm)
  let scope := bound.reverse ++ [(parameterName, Runtime.word w)]
  match arm.body with
  | .expr body => bodyValue scope body
  | .nested scrutinee inner =>
      let (_, value) ← scope.find? (·.1 = scrutinee)
      let (innerBound, innerArm) ← inner.findSome? fun innerArm =>
        (bindRow innerArm.patterns [value]).map (·, innerArm)
      bodyValue (innerBound.reverse ++ scope) innerArm.body

private def selected (builder : Builder) (input : Nat) : Value :=
  builder.trees.getD (min ((input + builder.offset) % 4) (builder.trees.length - 1)) default

private def interpret (plan : Plan) (input : Nat) : Option Nat := do
  let results ← plan.views.flatMap (fun view =>
      let w := (input + view.wordOffset) % modulus
      let values := view.builders.map fun builder => evaluate input (selected builder input)
      match view.kind with
      | .generic => values.map fun value => matchArms view.arms [value] w
      | _ => [matchArms view.arms values w]) |>.mapM id
  return results.zipIdx.foldl (fun accumulated (result, index) =>
    (accumulated + result * (2 * index + 1)) % modulus) 0

private def boundary : List Nat := [0, 1, 2, 255, 256, 2 ^ 256 - 1, 2 ^ 255, 2 ^ 255 - 1]

/-- The reference agrees with the interpreter on 240 generated plans at the
eight boundary inputs and four others. -/
private def modelChecks : IO Unit := do
  let mut compared := 0
  for seed in List.range 240 do
    match Enums.generatedPlan (Seed.ofNat (seed + 1)) Enums.defaultNodes with
    | .error _ => pure ()
    | .ok checked =>
        for input in boundary ++ [3, 1001, 0x1234567890abcdef, 2 ^ 200 + 77] do
          let core ← run (checked.program (Word.ofNatModulo input))
          ensure (interpret checked.plan input == some core)
            s!"seed {seed + 1} input {input}: the reference differs from the interpreter"
          compared := compared + 1
  ensure (compared ≥ 2400) "fewer than 200 generated plans compared with the interpreter"

/-! A fixture with every view kind, both generic instances, a pair view, a
nested match and the dot and same-name forms. -/

private def fixtureDecls : List Decl := [
  {generic := false, sameName := false, constructors := [[], [.word], [.word, .tuple .word .word]]},
  {generic := true, sameName := true, constructors := [[.param, .word], [], [.enum 0]]}]

private def body (first : Solcore.Synthesis.Core.Enums.Term) (rest : List (Op × Solcore.Synthesis.Core.Enums.Term)) (constant : Nat) : Body := {first, rest, constant}

private def fixtureViews : List View := [
  {kind := .single, scrutinees := [.enum 0], instances := [], wordOffset := 13,
   arms := [
     {patterns := [.ctor2 2 (.var 0) (.tuple (.var 1) .wild) .qualified],
      body := .expr (body (.name 0) [(.sub, .name 1)] 5)},
     {patterns := [.ctor1 1 (.var 4) .dot], body := .expr (body (.name 4) [(.mul, .constant 3)] 7)},
     {patterns := [], body := .expr (body (.name 4) [] 11)}],
   builders := [{offset := 1, trees := [.ctor0 0 .qualified, .ctor1 1 (.leaf .add 2) .qualified,
     .ctor2 2 (.leaf .input 0) (.tuple (.leaf .mul 3) (.leaf .xor 5)) .qualified]}]},
  {kind := .generic, scrutinees := [.applied 1 .param], instances := [.word, .tuple .word .word], wordOffset := 37,
   arms := [
     {patterns := [.ctor2 0 .wild (.var 2) .sameName], body := .expr (body (.name 2) [] 17)},
     {patterns := [.ctor1 2 (.var 0) .qualified], body := .nested 0 [
       {patterns := [.ctor1 1 (.var 0) .qualified], body := body (.name 0) [(.xor, .name 4)] 19},
       {patterns := [.wild], body := body (.name 4) [] 23}]},
     {patterns := [.var 3], body := .expr (body (.name 4) [(.mul, .constant 29)] 31)}],
   builders := [
     {offset := 0, trees := [.ctor2 0 (.leaf .input 0) (.leaf .add 7) .sameName, .ctor0 1 .qualified,
       .ctor1 2 (.ctor1 1 (.leaf .mul 9) .qualified) .qualified]},
     {offset := 2, trees := [.ctor2 0 (.tuple (.leaf .input 0) (.leaf .input 0)) (.leaf .xor 3) .qualified,
       .ctor1 2 (.ctor0 0 .qualified) .dot]}]},
  {kind := .pair, scrutinees := [.enum 0, .applied 1 .word], instances := [], wordOffset := 53,
   arms := [
     {patterns := [.ctor1 1 (.var 0) .qualified, .ctor2 0 (.var 1) .wild .sameName],
      body := .expr (body (.name 0) [(.add, .name 1)] 41)},
     {patterns := [.wild, .ctor0 1 .qualified], body := .expr (body (.name 4) [] 43)},
     {patterns := [.var 2, .wild], body := .expr (body (.name 4) [(.xor, .constant 47)] 0)}],
   builders := [
     {offset := 3, trees := [.ctor1 1 (.leaf .input 0) .qualified, .ctor0 0 .qualified]},
     {offset := 0, trees := [.ctor2 0 (.leaf .add 1) (.leaf .input 0) .qualified, .ctor0 1 .qualified]}]}]

private def fixturePlan : Plan := {decls := fixtureDecls, views := fixtureViews}

/-- Golden results of `scratchpad/u12/fixture_model.py`, a separate Python
model of the fixture. -/
private def fixtureResults : List (Nat × Nat) := [(0, 567), (1, 4386), (2, 993), (3, 1245), (255, 11913),
  (2 ^ 255, 567), (2 ^ 256 - 1, 905)]

private def fixtureSource : String := String.intercalate "\n" [
  "pragma solcore;", "import * from std;",
  "import * from std.dispatch;",
  "",
  "enum Sc_T0 {",
  "    Sc_T0_0,",
  "    Sc_T0_1(word),",
  "    Sc_T0_2(word, (word, word))",
  "}",
  "",
  "enum Sc_T1<a> {",
  "    Sc_T1(a, word),",
  "    Sc_T1_1,",
  "    Sc_T1_2(Sc_T0)",
  "}",
  "",
  "function sc_view0(sc_e: Sc_T0, sc_w: word) returns (word) {",
  "    match (sc_e) {",
  "        case Sc_T0.Sc_T0_2(sc_a, (sc_b, _)) {",
  "            return ((sc_a - sc_b) + 5);",
  "        }",
  "        case .Sc_T0_1(sc_w) {",
  "            return ((sc_w * 3) + 7);",
  "        }",
  "        default {",
  "            return (sc_w + 11);",
  "        }",
  "    }",
  "}",
  "",
  "function sc_make0_0(sc_x: word) returns (Sc_T0) {",
  "    let sc_k: word = ((sc_x + 1) & 3);",
  "    if (sc_k == 0) {",
  "        return Sc_T0.Sc_T0_0;",
  "    }",
  "    if (sc_k == 1) {",
  "        return Sc_T0.Sc_T0_1((sc_x + 2));",
  "    }",
  "    return Sc_T0.Sc_T0_2(sc_x, ((sc_x * 3), (sc_x ^ 5)));",
  "}",
  "",
  "function sc_view1<a>(sc_e: Sc_T1<a>, sc_w: word) returns (word) {",
  "    match (sc_e) {",
  "        case Sc_T1(_, sc_c) {",
  "            return (sc_c + 17);",
  "        }",
  "        case Sc_T1.Sc_T1_2(sc_a) {",
  "            match (sc_a) {",
  "                case Sc_T0.Sc_T0_1(sc_a) {",
  "                    return ((sc_a ^ sc_w) + 19);",
  "                }",
  "                case _ {",
  "                    return (sc_w + 23);",
  "                }",
  "            }",
  "        }",
  "        case sc_d {",
  "            return ((sc_w * 29) + 31);",
  "        }",
  "    }",
  "}",
  "",
  "function sc_make1_0(sc_x: word) returns (Sc_T1<word>) {",
  "    let sc_k: word = ((sc_x + 0) & 3);",
  "    if (sc_k == 0) {",
  "        return Sc_T1(sc_x, (sc_x + 7));",
  "    }",
  "    if (sc_k == 1) {",
  "        return Sc_T1.Sc_T1_1;",
  "    }",
  "    return Sc_T1.Sc_T1_2(Sc_T0.Sc_T0_1((sc_x * 9)));",
  "}",
  "",
  "function sc_make1_1(sc_x: word) returns (Sc_T1<(word, word)>) {",
  "    let sc_k: word = ((sc_x + 2) & 3);",
  "    if (sc_k == 0) {",
  "        return Sc_T1.Sc_T1((sc_x, sc_x), (sc_x ^ 3));",
  "    }",
  "    return .Sc_T1_2(Sc_T0.Sc_T0_0);",
  "}",
  "",
  "function sc_view2(sc_e: Sc_T0, sc_f: Sc_T1<word>, sc_w: word) returns (word) {",
  "    match (sc_e, sc_f) {",
  "        case (Sc_T0.Sc_T0_1(sc_a), Sc_T1(sc_b, _)) {",
  "            return ((sc_a + sc_b) + 41);",
  "        }",
  "        case (_, Sc_T1.Sc_T1_1) {",
  "            return (sc_w + 43);",
  "        }",
  "        case (sc_c, _) {",
  "            return ((sc_w ^ 47) + 0);",
  "        }",
  "    }",
  "}",
  "",
  "function sc_make2_0(sc_x: word) returns (Sc_T0) {",
  "    let sc_k: word = ((sc_x + 3) & 3);",
  "    if (sc_k == 0) {",
  "        return Sc_T0.Sc_T0_1(sc_x);",
  "    }",
  "    return Sc_T0.Sc_T0_0;",
  "}",
  "",
  "function sc_make2_1(sc_x: word) returns (Sc_T1<word>) {",
  "    let sc_k: word = ((sc_x + 0) & 3);",
  "    if (sc_k == 0) {",
  "        return Sc_T1.Sc_T1((sc_x + 1), sc_x);",
  "    }",
  "    return Sc_T1.Sc_T1_1;",
  "}",
  "",
  "contract SynthesizedEnums {",
  "    function run(input: uint256) public returns (uint256) {",
  "        let sc_input: word = Typedef.rep(input);",
  "        let sc_r0: word = sc_view0(sc_make0_0(sc_input), (sc_input + 13));",
  "        let sc_r1: word = sc_view1(sc_make1_0(sc_input), (sc_input + 37));",
  "        let sc_r2: word = sc_view1(sc_make1_1(sc_input), (sc_input + 37));",
  "        let sc_r3: word = sc_view2(sc_make2_0(sc_input), sc_make2_1(sc_input), (sc_input + 53));",
  "        return uint256((((sc_r0 + (sc_r1 * 3)) + (sc_r2 * 5)) + (sc_r3 * 7)));",
  "    }",
  "}", ""]

private def fixtureChecks : IO Unit := do
  ensure fixturePlan.admitted "the fixture plan is not admitted"
  let some checked := Enums.CheckedPlan.ofPlan? fixturePlan | throw (IO.userError "the fixture failed the checker")
  ensure ((Solcore.Synthesis.Source.Enums.emit fixturePlan).source == fixtureSource) "the fixture source changed"
  for (input, expected) in fixtureResults do
    ensure ((← run (checked.program (Word.ofNatModulo input))) == expected) s!"fixture input {input}: Core result"
    ensure (interpret fixturePlan input == some expected) s!"fixture input {input}: interpreter result"
  let shapes := fixturePlan.shapes
  let has := fun (dimension value : String) => ((shapes.find? (·.1 == dimension)).map (·.2.contains value)).getD false
  for (dimension, value) in [("views", "single"), ("views", "pair"), ("views", "generic"), ("patterns", "dot"),
      ("patterns", "same-name"), ("patterns", "nested"), ("patterns", "shadow"), ("patterns", "rebound"),
      ("patterns", "default"), ("patterns", "nullary"), ("wildcards", "column"), ("wildcards", "component"),
      ("wildcards", "field"), ("wildcards", "arm"), ("depths", "2"), ("declarations", "argument:tuple")] do
    ensure (has dimension value) s!"the fixture lacks {dimension}:{value}"

/-- Admission refuses what the compiler or the reference cannot take. -/
private def admissionChecks : IO Unit := do
  let views := fixtureViews
  let withArms := fun (index : Nat) (arms : List Arm) =>
    ({fixturePlan with views := views.set index {(views.getD index default) with arms}} : Plan)
  let armsOf := fun (index : Nat) => (views.getD index default).arms
  let withPatterns := fun (index arm : Nat) (patterns : List Pat) =>
    withArms index ((armsOf index).set arm {((armsOf index).getD arm default) with patterns})
  let withBody := fun (index arm : Nat) (body : ArmBody) =>
    withArms index ((armsOf index).set arm {((armsOf index).getD arm default) with body})
  let refused := fun (label : String) (plan : Plan) => ensure (!plan.admitted) s!"admitted {label}"
  let catchAll : Arm := {patterns := [.wild], body := .expr (body (.constant 1) [] 1)}
  -- An arm after the default, an unreachable arm, a non-exhaustive match.
  refused "an arm after default" (withArms 0 (armsOf 0 ++ [catchAll]))
  refused "an unreachable arm" (withArms 0 ((armsOf 0).take 1 ++ [(armsOf 0).headD default] ++ (armsOf 0).drop 1))
  refused "a non-exhaustive match" (withArms 0 ((armsOf 0).take 2))
  -- A constructor out of range, a same-name form of another constructor, a nested dot value.
  refused "a constructor out of range" (withPatterns 0 1 [.ctor1 3 (.var 4) .qualified])
  refused "a misplaced same-name pattern" (withPatterns 0 1 [.ctor1 1 (.var 4) .sameName])
  let genericView := views.getD 1 default
  let nestedDot : Builder := {offset := 0, trees := [.ctor1 2 (.ctor1 1 (.leaf .mul 9) .dot) .qualified]}
  refused "a nested dot value"
    {fixturePlan with views := views.set 1 {genericView with builders := genericView.builders.set 0 nestedDot}}
  -- A name bound twice in a row, a body naming a non-Word, a nested match on a Word.
  refused "a repeated name in one row" (withPatterns 0 0 [.ctor2 2 (.var 0) (.tuple (.var 0) .wild) .qualified])
  refused "a body naming a non-Word" (withBody 2 2 (.expr (body (.name 2) [] 0)))
  refused "a nested match on a Word" (withBody 0 1 (.nested 4 [{patterns := [], body := body (.constant 0) [] 0}]))
  -- A generic view inspecting its parameter, a declaration referring to a later one.
  refused "a generic view inspecting its parameter" (withPatterns 1 0 [.ctor2 0 (.ctor0 0 .qualified) (.var 2) .sameName])
  let firstDecl := fixtureDecls.headD default
  refused "a forward declaration reference"
    {fixturePlan with decls := fixtureDecls.set 0 {firstDecl with constructors := [[], [.enum 1], [.word]]}}
  -- A same-name declaration whose constructor 0 has no field.
  refused "a nullary same-name constructor"
    {fixturePlan with decls := fixtureDecls.set 0 {firstDecl with sameName := true}}

private def shapeValues : List (String × List String) := [
  ("constructors", ["2", "3", "4"]),
  ("fields", ["count:0", "count:1", "count:2", "type:applied", "type:enum", "type:param", "type:tuple", "type:word"]),
  ("declarations", ["argument:enum", "argument:param", "argument:tuple", "argument:word", "generic", "plain",
    "same-name"]),
  ("views", ["generic", "pair", "single"]),
  ("patterns", ["default", "dot", "exhaustive", "nested", "nullary", "qualified", "rebound", "repeated",
    "same-name", "shadow", "tuple", "variable", "wildcard"]),
  ("wildcards", ["arm", "column", "component", "deep", "field"]),
  ("depths", ["1", "2", "3"])]

/-- Generation is deterministic, draws every shape within 600 seeds,
replays exactly and drops views to fit a smaller budget. -/
private def generationChecks : IO Unit := do
  let mut seen : List (String × String) := []
  for seed in List.range 600 do
    let plan := generate (UInt64.ofNat (seed + 1))
    ensure (planJsonEq plan (generate (UInt64.ofNat (seed + 1)))) "generation is not deterministic"
    for (dimension, values) in plan.shapes do
      for value in values do
        unless seen.contains (dimension, value) do seen := (dimension, value) :: seen
  for (dimension, values) in shapeValues do
    for value in values do
      ensure (seen.contains (dimension, value)) s!"600 seeds never drew {dimension}:{value}"
  let corpus := Enums.generateCases (Seed.ofNat 1) Enums.defaultNodes 64 64 fuel
  let all ← cases corpus
  ensure (all.size = 64) "generation from seed 1 did not return 64 cases"
  for case in all do
    ensure ((← get (Enums.replayCase case fuel)) == case) "a generated case failed exact replay"
  -- Seeded inputs and the identity filter are recorded and replay.
  let seeded ← cases (Enums.generateCases (Seed.ofNat 7) Enums.defaultNodes 12 4 fuel .seeded .nonIdentity)
  ensure (seeded.size = 12) "seeded generation did not return twelve inputs"
  for case in seeded do
    ensure ((← get (Enums.replayCase case fuel)) == case) "a seeded case failed exact replay"
  -- Constant plans are excluded, and a 256-node budget drops views.
  let mut constant := false
  for seed in List.range 120 do
    if let .ok plan := Enums.generatedPlan (Seed.ofNat (seed + 1)) Enums.defaultNodes then
      if errorOf (Enums.inputSensitive plan fuel) == some "all eight boundary inputs returned the same Word" then
        constant := true
  ensure constant "no constant plan was excluded in 120 seeds"
  let mut dropped := false
  for seed in List.range 40 do
    if let .ok small := Enums.generatedPlan (Seed.ofNat (seed + 1)) Enums.minimumNodes then
      ensure (small.plan.nodes ≤ Enums.minimumNodes) "a fitted plan exceeds its budget"
      if small.plan.views.length < (generate (UInt64.ofNat (seed + 1))).views.length then dropped := true
  ensure dropped "a 256-node budget never dropped a view"
where
  planJsonEq (left right : Plan) : Bool := Enums.planJson left == Enums.planJson right

/-- Tampering is refused; reductions are admitted, strictly smaller and
replay, and a shrink response stays below its byte cap. -/
private def tamperChecks : IO Unit := do
  let all ← cases (Enums.generateCases (Seed.ofNat 1) Enums.defaultNodes 8 4 fuel)
  let case := all[0]!
  let plan ← get (case.getObjVal? "enumPlan")
  ensure (Enums.replayCase (case.setObjVal! "source" (toJson "contract C {}")) fuel matches .error _)
    "a changed source replayed"
  ensure (Enums.replayCase (case.setObjVal! "program" (Solcore.Core.Wire.encodeProgram
      {resultType := .word, dataDefinitions := [], body := .word Word.zero})) fuel matches .error _)
    "a changed reference replayed"
  ensure (errorOf (Enums.replayCase (case.setObjVal! "provenance" ((← provenance case).setObjVal!
      "generatorVersion" (toJson "core-enum-match-v0"))) fuel) == some "generatorVersion changed")
    "a changed generator version replayed"
  ensure (Enums.replayCase (case.setObjVal! "provenance" ((← provenance case).setObjVal!
      "enumShapes" (Json.mkObj []))) fuel matches .error _) "changed enum shapes replayed"
  ensure (Enums.replayCase (case.setObjVal! "enumPlan" (plan.setObjVal! "views" (.arr #[]))) fuel matches .error _)
    "a plan without views replayed"
  let origin ← get ((← provenance case).getObjVal? "origin")
  ensure (Enums.replayCase (case.setObjVal! "provenance" ((← provenance case).setObjVal!
      "origin" (origin.setObjVal! "seed" (toJson "2")))) fuel matches .error _) "a changed seed replayed"
  let shrunk ← get (Enums.shrinkCases case 4096 fuel)
  let reduced ← cases shrunk
  ensure (!reduced.isEmpty) "no reduction of the first generated case"
  ensure (shrunk.compress.utf8ByteSize ≤ 2 * 1024 * 1024) "a shrink response exceeds 2 MiB"
  for candidate in reduced do
    ensure ((← get (Enums.replayCase candidate fuel)) == candidate) "a reduction failed exact replay"
  let parent ← get (Enums.caseProgram case)
  let all := Enums.reductions parent
  for reduction in all do
    ensure (decide (reduction.candidate.measure.StrictlySmaller parent.measure)) "a reduction is not strictly smaller"
  -- Every kind of plan reduction applies somewhere in the first 40 plans.
  let mut kinds : List String := []
  for seed in List.range 40 do
    if let .ok checked := Enums.generatedPlan (Seed.ofNat (seed + 1)) Enums.defaultNodes then
      let source : Enums.CheckedInput := ⟨checked, Word.ofNatModulo 5⟩
      for reduction in Enums.reductions source do
        let next := reduction.candidate.plan.plan
        let kind := if next.views.length < checked.plan.views.length then "view"
          else if next.decls.length < checked.plan.decls.length then "declaration"
          else if (next.decls.map (·.constructors.length)) != (checked.plan.decls.map (·.constructors.length)) then
            "constructor"
          else if (next.decls.map Decl.size) != (checked.plan.decls.map Decl.size) then "field"
          else if reduction.candidate.input != source.input then "input" else "view-part"
        unless kinds.contains kind do kinds := kind :: kinds
  for kind in ["view", "declaration", "constructor", "field", "input", "view-part"] do
    ensure (kinds.contains kind) s!"no {kind} reduction in 40 plans"
  let reducedOrigin ← get ((← provenance reduced[0]!).getObjVal? "origin")
  ensure (Enums.replayCase (reduced[0]!.setObjVal! "provenance" ((← provenance reduced[0]!).setObjVal!
      "origin" (reducedOrigin.setObjVal! "parentPlan" (← get (reduced[0]!.getObjVal? "enumPlan"))))) fuel
      matches .error _)
    "a reduction claiming itself as its parent replayed"

def testSourceEnumCases : IO Unit := do
  fixtureChecks
  admissionChecks
  modelChecks
  generationChecks
  tamperChecks

end Tests.SourceEnumCases
end

section
-- leanmerge: from Solcore.Test.SourceEnumReturnCases
/-! Generated enum-return cases. The Core contract must equal the source model,
a slot map and std's encoder, on every transaction of the generated sequences;
each case must replay to itself; the shell node counts must be the ones the
definitions fix; generation must draw every constructor count, static and
dynamic shapes, every field kind, two `bytes` constructors, every position of
each count and every bank length; and every reduction must be a strictly
smaller sealed case that replays. -/
set_option autoImplicit false

namespace Tests.SourceEnumReturnCases

open Lean
open Solcore.Core (Word)
open Solcore.ContractRuntime
open Solcore.Synthesis.Core
open Solcore.Synthesis.Core.EnumReturn (Constructor Shape)
open Solcore.Synthesis.Stateful
open Solcore.Synthesis.Stateful.EnumReturnExecution (Transaction)

private abbrev Cases := Solcore.Synthesis.Source.EnumReturn.CheckedScenario

private def get {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def slots (values : List Word) : Json :=
  toJson ((values.zipIdx).map fun (value, slot) => Json.mkObj [
    ("slot", toJson (toString slot)), ("value", toJson (toString value.val))])

/-- The widest constructor's field head: 0, 32 or 64 bytes, `bytes` counting 32. -/
private def widest (shape : Shape) : Nat :=
  shape.payloads.foldl (fun widest payload => max widest (match payload with
    | .noWords => 0
    | .twoWords => 64
    | _ => 32)) 0

/-- The adapter's output rule for a returned constructor. -/
private def returnedSize (shape : Shape) (transaction : Transaction) : Nat :=
  let payload := (shape.payloads[transaction.choice.val]?).getD .noWords
  if !shape.dynamic then 32 + widest shape
  else 64 + widest shape +
    if payload == .boundedBytes then 32 + 32 * ((transaction.length.val + 31) / 32) else 0

/-- The Core rows of a scenario equal the model's, transaction by transaction. -/
private def sameAsModel (scenario : Cases) (fuel : Nat) (name : String) : IO Unit := do
  let history := Solcore.Synthesis.Source.EnumReturn.observe scenario StorageExecution.fixtureBindings fuel
  ensure ((history.getObjValAs? String "status").toOption == some "complete") s!"{name}: history incomplete"
  let rows ← get (history.getObjValAs? (Array Json) "transactions")
  let some modelled := EnumReturnExecution.model scenario.plan.step scenario.plan.shape.constructors fuel
      scenario.transactions
    | throw (IO.userError s!"{name}: the source model failed")
  ensure (rows.size == modelled.length) s!"{name}: a row is missing"
  for ((row, model), transaction) in (rows.toList.zip modelled).zip scenario.transactions do
    ensure ((row.getObjValAs? String "status").toOption == some (if model.reverted then "reverted" else "returned") &&
        (row.getObjValAs? String "output").toOption == some (encodeBytesText model.output) &&
        (row.getObjVal? "committedStorage").toOption == some (slots model.slots))
      s!"{name}: the Core row differs from the source model: {row.compress}"
    ensure (model.output.size == if model.reverted then 32 else returnedSize scenario.plan.shape transaction)
      s!"{name}: the output has the wrong size"

private def shape (constructors : List Constructor) : Shape :=
  (Solcore.Synthesis.Source.EnumReturn.Shape.ofList? constructors).getD ⟨⟨"Idle", .noWords⟩, ⟨"Ready", .noWords⟩, []⟩

def testSourceEnumReturnCases : IO Unit := do
  let fuel := 1000000
  -- The shells of the definitions: 130 to 291 nodes.
  ensure (EnumReturn.shellNodes (shape [⟨"Idle", .noWords⟩, ⟨"Ready", .noWords⟩]) == 130 &&
      EnumReturn.shellNodes (shape [⟨"Idle", .noWords⟩, ⟨"Ready", .oneWord⟩, ⟨"Pair", .twoWords⟩,
        ⟨"Blob", .boundedBytes⟩]) == 255 &&
      EnumReturn.shellNodes (shape [⟨"Idle", .twoWords⟩, ⟨"Ready", .twoWords⟩, ⟨"Pair", .boundedBytes⟩,
        ⟨"Blob", .boundedBytes⟩]) == 291)
    "the shells differ from the definitions"
  ensure (Solcore.Synthesis.Source.EnumReturn.maxProgramNodes == 512) "the case limit changed"
  -- Random generation: revision three with eight transactions, and the fixed
  -- corpora's revision one with three.
  let mut lengths : List Nat := []
  let mut counts : List Nat := []
  let mut fields : List String := []
  let mut positions : List String := []
  let mut twoBytes := false
  let mut cases : Array Json := #[]
  for (revision, transactions, count, nodes) in
      [(GeneratorRevision.v3, 8, 40, 384), (GeneratorRevision.v1, 3, 24, 384), (GeneratorRevision.v3, 4, 12, 512)] do
    let corpus := Solcore.Synthesis.Source.EnumReturn.generateCases (Seed.ofNat 1) nodes count 512 fuel revision
      transactions
    ensure ((corpus.getObjValAs? String "status").toOption == some "complete") s!"{revision.version}: generation exhausted"
    let generated ← get (corpus.getObjValAs? (Array Json) "cases")
    for (json, index) in generated.zipIdx do
      let name := s!"{revision.version} at {nodes} case {index}"
      ensure ((Solcore.Synthesis.Source.EnumReturn.replayCase json fuel).toOption == some json) s!"{name}: replay differs"
      let scenario ← get (Solcore.Synthesis.Source.EnumReturn.caseProgram json)
      ensure (scenario.transactions.length == transactions) s!"{name}: wrong sequence length"
      sameAsModel scenario fuel name
      let source ← get (json.getObjValAs? String "source")
      ensure ((source.splitOn "public returns (SynthesizedEnum) {").length == 2 &&
          (source.splitOn "import * from std.ABIGeneric;").length == 2)
        s!"{name}: the emitted method differs"
      let shape := scenario.plan.shape
      let kind := if shape.dynamic then "dynamic" else "static"
      counts := (counts ++ [shape.constructors.length]).eraseDups
      fields := (fields ++ shape.payloads.map fun payload => kind ++ ":" ++ reprStr payload).eraseDups
      twoBytes := twoBytes || (shape.payloads.filter (· == .boundedBytes)).length == 2
      for transaction in scenario.transactions do
        positions := (positions ++ [s!"{shape.constructors.length}:{transaction.choice.val}"]).eraseDups
        if shape.payloads[transaction.choice.val]? == some .boundedBytes then
          lengths := (lengths ++ [transaction.length.val]).eraseDups
      cases := cases.push json
  ensure (counts.length == 3) s!"generation drew the constructor counts {counts}"
  ensure (fields.length == 7) s!"generation drew the fields {fields}"
  ensure twoBytes "generation never drew two bytes constructors"
  ensure (positions.length == 9) s!"generation chose the positions {positions}"
  for length in Solcore.Synthesis.Source.EnumReturn.lengthBank do
    ensure (lengths.contains length) s!"generation never drew length {length}"
  ensure (lengths.all (· ≤ 64) && lengths.any (fun length => length % 32 != 0 &&
      !Solcore.Synthesis.Source.EnumReturn.lengthBank.contains length))
    "generation drew a length above 64 or no uniform partial-Word length"
  -- Reductions: a narrower or dropped constructor comes with every shape that
  -- has one, and every emitted candidate replays as a strictly smaller sealed
  -- case.
  for json in cases.toList.take 8 do
    let source ← get (Solcore.Synthesis.Source.EnumReturn.caseProgram json)
    let reduced := Solcore.Synthesis.Source.EnumReturn.reductions source
    ensure (!reduced.isEmpty) "a case has no reduction"
    ensure (source.plan.shape.payloads.all (· == .noWords) || reduced.any (fun candidate =>
        candidate.candidate.transactions.length == source.transactions.length &&
        Solcore.Synthesis.Source.EnumReturn.shapeWeight candidate.candidate.plan.shape <
          Solcore.Synthesis.Source.EnumReturn.shapeWeight source.plan.shape))
      "no narrower constructor"
    let shrunk ← get (Solcore.Synthesis.Source.EnumReturn.shrinkCases json 64 fuel)
    for candidate in ← get (shrunk.getObjValAs? (Array Json) "cases") do
      ensure ((Solcore.Synthesis.Source.EnumReturn.replayCase candidate fuel).toOption == some candidate)
        "a reduction does not replay"
      sameAsModel (← get (Solcore.Synthesis.Source.EnumReturn.caseProgram candidate)) fuel "reduction"
  -- Refusals: a choice beyond the constructors, a length for a constructor
  -- without `bytes`, a length above 64, and a length that differs from its
  -- calldata.
  let some json := cases.toList.find? (fun json => match Solcore.Synthesis.Source.EnumReturn.caseProgram json with
      | .ok scenario => scenario.plan.shape.payloads.any (· != .boundedBytes) &&
          scenario.plan.shape.payloads.any (· == .boundedBytes)
      | .error _ => false) | throw (IO.userError "no mixed case")
  let scenario ← get (Solcore.Synthesis.Source.EnumReturn.caseProgram json)
  let transactions ← get (json.getObjValAs? (Array Json) "transactions")
  let some transaction := scenario.transactions.head? | throw (IO.userError "no transaction")
  let rebuilt (choice length : Nat) : Json := Solcore.Synthesis.Source.EnumReturn.transactionJson
    {transaction with choice := Word.ofNatModulo choice, length := Word.ofNatModulo length}
  let count := scenario.plan.shape.constructors.length
  let some bytesIndex := scenario.plan.shape.payloads.findIdx? (· == .boundedBytes) | throw (IO.userError "no bytes")
  let some wordIndex := scenario.plan.shape.payloads.findIdx? (· != .boundedBytes) | throw (IO.userError "no word")
  for (choice, length, label) in [(count, 0, "a choice beyond the constructors"),
      (wordIndex, 1, "a length for a constructor without bytes"), (bytesIndex, 65, "a length above 64")] do
    ensure (Solcore.Synthesis.Source.EnumReturn.caseProgram
        (json.setObjVal! "transactions" (.arr (transactions.set! 0 (rebuilt choice length))))).toOption.isNone
      s!"{label} was admitted"
  ensure (Solcore.Synthesis.Source.EnumReturn.caseProgram (json.setObjVal! "transactions" (.arr (transactions.set! 0
      ((rebuilt bytesIndex 3).setObjVal! "length" (toJson "4")))))).toOption.isNone
    "a length that differs from its calldata was admitted"
  -- Plans: an extra field, a repeated or unknown name, three bytes
  -- constructors, one constructor and five constructors are refused.
  let plan ← get (json.getObjVal? "enumReturnPlan")
  let step ← get (plan.getObjVal? "stepProgram")
  let planOf (constructors : List (String × String)) : Json := Json.mkObj [
    ("schema", toJson Solcore.Synthesis.Source.EnumReturn.planSchema),
    ("constructors", toJson (constructors.map fun (name, fields) =>
      Json.mkObj [("name", toJson name), ("fields", toJson fields)])),
    ("stepProgram", step)]
  ensure (Solcore.Synthesis.Source.EnumReturn.checkedPlan
      (planOf [("Idle", ""), ("Ready", "uint256")])).toOption.isSome
    "a plain plan was refused"
  for (constructors, label) in [
      ([("Idle", ""), ("Idle", "uint256")], "a repeated name"),
      ([("Idle", ""), ("Other", "uint256")], "a name outside the bank"),
      ([("Idle", "bytes"), ("Ready", "bytes"), ("Pair", "bytes")], "three bytes constructors"),
      ([("Idle", "")], "one constructor"),
      ([("Idle", ""), ("Ready", ""), ("Pair", ""), ("Blob", ""), ("Q", "")], "five constructors"),
      ([("Idle", ""), ("Ready", "uint256,uint256,uint256")], "three Words")] do
    ensure (Solcore.Synthesis.Source.EnumReturn.checkedPlan (planOf constructors)).toOption.isNone
      s!"a plan with {label} was admitted"
  ensure (Solcore.Synthesis.Source.EnumReturn.checkedPlan (plan.setObjVal! "arity" (toJson 2))).toOption.isNone
    "a plan with an extra field was admitted"

end Tests.SourceEnumReturnCases
end

section
-- leanmerge: from Solcore.Test.SourceEnumReturnCorpus
/-! The fixed enum-return corpus checks actual original Core histories against
expectations computed without the Core contract: the source model, a slot map
and std's encoder, in which each step runs alone in Core. Coverage describes
the checked steps' AST, the inputs, the returned constructors' positions and
fields, padded and full-width returns, the returned `bytes` lengths, the
shapes' `bytes` constructor counts, the carries into a returned value from an
earlier committed transaction and past a revert, the node budgets of generated
entries and the completions. Source/Rust/EVM agreement is a separate external
validation. -/
set_option autoImplicit false

namespace Tests.SourceEnumReturnCorpus
open Lean Solcore.Core Solcore.Synthesis.Core Solcore.Synthesis.Source
open Solcore.ContractRuntime (EnumPayload)
open Solcore.Synthesis.Core.EnumReturn (Shape)

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
  ("generatorVersion", generatorVersion), ("profileVersion", EnumReturn.profileVersion),
  ("functionVersion", Solcore.Synthesis.Core.EnumReturn.version),
  ("templateVersion", EnumReturn.templateVersion), ("stepProfileVersion", Aggregate.profileVersion),
  ("stepFunctionVersion", Aggregates.version), ("stepTemplateVersion", Aggregate.templateVersion),
  ("emitterVersion", EnumReturn.emitterVersion), ("wrapperVersion", EnumReturn.wrapperVersion)]

private def words (values : List Word) : List String := values.map fun value => toString value.val

/-- Every position of every constructor count. -/
def positions : List String :=
  [2, 3, 4].flatMap fun count => (List.range count).map fun position => s!"{count}:{position}"

def fieldName : EnumPayload → String
  | .noWords => "none"
  | .oneWord => "one"
  | .twoWords => "two"
  | .boundedBytes => "bytes"

/-- Static enums return none, one or two Words, dynamic ones any field. -/
def fieldKinds : List String :=
  ["static:none", "static:one", "static:two", "dynamic:none", "dynamic:one", "dynamic:two", "dynamic:bytes"]

def paddings : List String := ["static:padded", "static:full", "dynamic:padded", "dynamic:full"]

private def headSize : EnumPayload → Nat
  | .noWords => 0
  | .twoWords => 64
  | _ => 32

private def kind (shape : Shape) : String := if shape.dynamic then "dynamic" else "static"

/-- Imported entries are emitted from their saved plan and sequence; generated
entries are regenerated from their seed. Both are checked by full replay. -/
private def entryCase (entry : Json) (fuel : Nat) : Except String Json := do
  if let .ok request := entry.getObjVal? "generation" then
    let some seed := (← request.getObjValAs? String "seed").toNat? | throw "invalid generation seed"
    let corpus := EnumReturn.generateCases (Seed.ofNat seed) (← request.getObjValAs? Nat "maxProgramNodes") 1 1 fuel
    require ((← string corpus "status") == "complete") "generated entry was excluded"
    let some saved := (← corpus.getObjValAs? (Array Json) "cases")[0]? | throw "generated entry has no case"
    return saved
  let plan ← EnumReturn.checkedPlan (← entry.getObjVal? "enumReturnPlan")
  let scenario ← EnumReturn.checkedScenario plan
    (← EnumReturn.decodeTransactions plan.shape (← entry.getObjVal? "transactions"))
  EnumReturn.emitCase scenario (Json.mkObj [("kind", toJson "imported")]) fuel

private def templates (saved : Json) : Except String (List Nat) := do
  let origin ← (← saved.getObjVal? "provenance").getObjVal? "origin"
  if (← string origin "kind") != "enum-return-generated" then return []
  let helpers ← (← origin.getObjVal? "stepOrigin").getObjValAs? (List Json) "helpers"
  helpers.mapM fun helper => helper.getObjValAs? Nat "template"

/-- The source model's rows of a scenario, in the corpus's expected-row form. -/
def modelRows (scenario : EnumReturn.CheckedScenario) (fuel : Nat) : Except String (List Json) := do
  let some rows := Solcore.Synthesis.Stateful.EnumReturnExecution.model scenario.plan.step
      scenario.plan.shape.constructors fuel scenario.transactions | throw "the source model failed"
  return (rows.zip scenario.transactions).map fun (row, transaction) => Json.mkObj [
    ("id", toJson transaction.id), ("status", toJson (if row.reverted then "reverted" else "returned")),
    ("output", toJson (Solcore.ContractRuntime.encodeBytesText row.output)),
    ("committedStorage", toJson (row.slots.zipIdx.map fun (value, slot) => Json.mkObj [
      ("slot", toJson (toString slot)), ("value", toJson (toString value.val))]))]

def validateManifest (manifest : Json) (fuel : Nat := 1000000) : Except String Json := do
  require ((← string manifest "schema") == "solcore-lean.semantic-storage-corpus-manifest.v1" &&
    (← string manifest "profile") == "stateful-enum-returns" &&
    (← string manifest "coverageKind") == "step-core-ast-features") "unexpected enum-return manifest scope"
  for (key, expected) in versions do
    require ((← string manifest key) == expected) ("enum-return manifest changed " ++ key)
  let requiredFeatures ← strings manifest "requiredFeatures"
  let requiredInputs ← strings manifest "requiredInputs"
  require (sameMembers requiredInputs (words EnumReturn.boundaryInputs))
    "enum-return corpus must require all six boundary inputs"
  require ((← strings manifest "requiredEnumPositions") == positions &&
    (← strings manifest "requiredEnumFields") == fieldKinds &&
    (← strings manifest "requiredEnumPadding") == paddings)
    "enum-return corpus must require every position, every field kind and padded and full returns of both kinds"
  require ((← manifest.getObjValAs? (List Nat) "requiredEnumBytesLengths") == EnumReturn.lengthBank &&
    (← manifest.getObjValAs? (List Nat) "requiredEnumBytesConstructors") == [0, 1, 2] &&
    (← manifest.getObjValAs? (List Nat) "requiredEnumNodeBudgets") == [384, 512])
    "enum-return corpus must require the bank's bytes lengths, zero to two bytes constructors and both node budgets"
  require ((← strings manifest "requiredEnumCarries") == ["committed", "rollback"])
    "enum-return corpus must require carries from a committed transaction and past a revert"
  require ((← manifest.getObjValAs? (List Nat) "requiredHelperCounts") == [1, 2, 3] &&
    (← manifest.getObjValAs? (List Nat) "requiredTransactionCounts") == [1, 2, 3])
    "enum-return corpus must require one to three helpers and transactions"
  require ((← (← manifest.getObjVal? "generationRecipeRequirements").getObjValAs? (List Nat) "templates") == [0, 1, 2, 3])
    "enum-return corpus must require all four step templates"
  require ((← strings manifest "requiredOutcomes") == ["returned", "reverted"])
    "enum-return corpus must require both outcomes"
  let requiredPatterns ← strings manifest "requiredCompletionPatterns"
  require (!requiredPatterns.isEmpty) "enum-return corpus must require completion patterns"
  let entries ← manifest.getObjValAs? (Array Json) "cases"
  require (0 < entries.size && entries.size ≤ 64) "enum-return corpus must contain 1..64 scenarios"
  let mut identifiers : List String := []
  let mut features : List String := []
  let mut inputs : List String := []
  let mut returnedPositions : List String := []
  let mut returnedFields : List String := []
  let mut padding : List String := []
  let mut bytesLengths : List Nat := []
  let mut bytesConstructors : List Nat := []
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
    require (!identifiers.contains identifier) ("duplicate enum-return corpus id " ++ identifier)
    identifiers := identifier :: identifiers
    let saved ← entryCase entry fuel
    require ((← EnumReturn.replayCase saved fuel) == saved) ("enum-return corpus entry did not replay: " ++ identifier)
    let scenario ← EnumReturn.caseProgram saved
    if let .ok request := entry.getObjVal? "generation" then
      budgets := (budgets ++ [← request.getObjValAs? Nat "maxProgramNodes"]).eraseDups
    else
      require ((← saved.getObjVal? "enumReturnPlan") == (← entry.getObjVal? "enumReturnPlan") &&
        (← saved.getObjVal? "transactions") == (← entry.getObjVal? "transactions"))
        ("imported enum-return entry is not canonical: " ++ identifier)
    let caseFeatures := (← (← saved.getObjVal? "provenance").getObjValAs? (List String) "features").eraseDups
    require (sameMembers (← strings entry "expectedFeatures") caseFeatures)
      ("enum-return corpus features changed: " ++ identifier)
    let expected ← entry.getObjValAs? (List Json) "expectedHistory"
    require (expected == (← modelRows scenario fuel))
      ("the expected history differs from the source model: " ++ identifier)
    let history := EnumReturn.observe scenario Solcore.Synthesis.Stateful.StorageExecution.fixtureBindings fuel
    require ((← string history "status") == "complete") ("enum-return corpus history incomplete: " ++ identifier)
    let observed ← history.getObjValAs? (List Json) "transactions"
    require (observed.length == expected.length) ("enum-return expected history length changed: " ++ identifier)
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
    let widest := shape.payloads.foldl (fun widest payload => max widest (headSize payload)) 0
    bytesConstructors := (bytesConstructors ++ [(shape.payloads.filter (· == .boundedBytes)).length]).eraseDups
    for (status, transaction) in statuses.zip scenario.transactions do
      if status == "returned" then
        let choice := transaction.choice.val
        let payload := (shape.payloads[choice]?).getD .noWords
        returnedPositions := (returnedPositions ++ [s!"{shape.constructors.length}:{choice}"]).eraseDups
        returnedFields := (returnedFields ++ [kind shape ++ ":" ++ fieldName payload]).eraseDups
        padding := (padding ++ [kind shape ++ ":" ++ if headSize payload < widest then "padded" else "full"]).eraseDups
        if payload == .boundedBytes then
          bytesLengths := (bytesLengths ++ [transaction.length.val]).eraseDups
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
  require (requiredFeatures.all features.contains) "enum-return corpus misses a required step feature"
  require (requiredInputs.all inputs.contains) "enum-return corpus misses a boundary input"
  require (positions.all returnedPositions.contains && fieldKinds.all returnedFields.contains &&
      paddings.all padding.contains)
    "enum-return corpus misses a returned position, field kind or padding"
  require (EnumReturn.lengthBank.all bytesLengths.contains && [0, 1, 2].all bytesConstructors.contains)
    "enum-return corpus misses a returned bytes length or a bytes constructor count"
  require (["committed", "rollback"].all carries.contains && [384, 512].all budgets.contains)
    "enum-return corpus misses a carry or a node budget"
  require ([1, 2, 3].all helperCounts.contains && [1, 2, 3].all transactionCounts.contains)
    "enum-return corpus misses a helper or transaction count"
  require ([0, 1, 2, 3].all templateUnion.contains) "enum-return corpus misses a generated template"
  require (["returned", "reverted"].all outcomes.contains && requiredPatterns.all patterns.contains)
    "enum-return corpus misses an observed outcome or completion pattern"
  return Json.mkObj [("profile", toJson "stateful-enum-returns"), ("scenarios", toJson entries.size),
    ("transactions", toJson transactionTotal), ("positions", toJson returnedPositions),
    ("fields", toJson returnedFields), ("padding", toJson padding), ("bytesLengths", toJson bytesLengths),
    ("bytesConstructors", toJson bytesConstructors), ("carries", toJson carries), ("nodeBudgets", toJson budgets),
    ("patterns", toJson patterns)]

private def checked {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def rejects {α : Type} (result : Except String α) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "invalid enum-return corpus unexpectedly passed")

def testSourceEnumReturnCorpus : IO Unit := do
  let manifest ← checked (Json.parse (← IO.FS.readFile "scripts/semantic-enum-return-corpus.json"))
  let summary ← checked (validateManifest manifest)
  let entries ← checked (manifest.getObjValAs? (Array Json) "cases")
  let some first := entries[0]? | throw (IO.userError "missing first enum-return case")
  let some generatedEntry := entries.find? (fun entry => (entry.getObjVal? "generation").isOk) |
    throw (IO.userError "missing generated enum-return case")
  let replace := fun (original changed : Json) => manifest.setObjVal! "cases"
    (.arr (entries.map fun entry => if entry == original then changed else entry))
  let history ← checked (first.getObjValAs? (Array Json) "expectedHistory")
  -- A changed tag Word, a nonzero padding byte, a shorter output, a slot, a
  -- missing row and a status are all checked.
  let returnedIndex := (history.findIdx? fun row => (row.getObjValAs? String "status").toOption == some "returned").getD 0
  let row := history[returnedIndex]!
  let output ← checked (row.getObjValAs? String "output")
  let changedTag := row.setObjVal! "output" (toJson ("0x" ++ String.ofList (List.replicate 64 'f') ++ output.drop 66))
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr (history.set! returnedIndex changedTag)))))
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
  -- A transaction's choice is checked against its calldata, and a constructor's
  -- name and fields against the plan.
  let transactions ← checked (first.getObjValAs? (Array Json) "transactions")
  let choice ← checked (transactions[0]!.getObjValAs? String "choice")
  rejects (validateManifest (replace first (first.setObjVal! "transactions" (.arr (transactions.set! 0
    (transactions[0]!.setObjVal! "choice" (toJson (if choice == "1" then "0" else "1"))))))))
  let plan ← checked (first.getObjVal? "enumReturnPlan")
  let constructors ← checked (plan.getObjValAs? (Array Json) "constructors")
  let renamed := constructors.set! 0 (constructors[0]!.setObjVal! "name" (toJson "Rejected"))
  let refielded := constructors.set! 0 (constructors[0]!.setObjVal! "fields"
    (toJson (if (constructors[0]!.getObjValAs? String "fields").toOption == some "" then "uint256" else "")))
  for changed in [renamed, refielded] do
    rejects (validateManifest (replace first (first.setObjVal! "enumReturnPlan"
      (plan.setObjVal! "constructors" (.arr changed)))))
  rejects (validateManifest (replace first (first.setObjVal! "expectedFeatures" (toJson ([] : List String)))))
  rejects (validateManifest (manifest.setObjVal! "cases" (.arr (entries.push first))))
  for (key, value) in [
      ("profile", toJson "stateful-storage"), ("templateVersion", toJson "forged"),
      ("cases", .arr #[]), ("requiredInputs", toJson ([] : List String)),
      ("requiredEnumPositions", toJson (["2:0"] : List String)),
      ("requiredEnumFields", toJson (["static:none"] : List String)),
      ("requiredEnumPadding", toJson (["static:full"] : List String)),
      ("requiredEnumBytesLengths", toJson [0, 1, 32]), ("requiredEnumBytesConstructors", toJson [1, 2]),
      ("requiredEnumNodeBudgets", toJson [384]), ("requiredEnumCarries", toJson (["committed"] : List String)),
      ("requiredHelperCounts", toJson [1, 2]),
      ("requiredCompletionPatterns", toJson (["returned,returned,returned,returned"] : List String))] do
    rejects (validateManifest (manifest.setObjVal! key value))
  rejects (validateManifest manifest 0)
  IO.println summary.compress

end Tests.SourceEnumReturnCorpus
end

section
-- leanmerge: from Solcore.Test.SourceEnumReturnGolden
/-! Golden cases for the enum-return profile. Every expected row is written out
as hexadecimal text computed from the protocol and std's encoding, not by
either model, with the tags from `cast keccak`. The steps add a known constant
`c`, so a transaction computes `r = slot 0 + input + c`, writes `r` to slot 0,
slot 1 plus one to slot 1 and the input to slot 2, and returns constructor
`choice` with its fields: none, `d0 = r · K`, `(d0, d1)` with
`d1 = (slot 1 · K) xor (prior slot 2)`, or the first `length` bytes of `d0` and
`d1`. A static enum is its tag, fields and zero Words up to the widest
constructor; a dynamic one is the offset 32, then that body and a `bytes`
field's tail. Odd flags revert with `r` and keep the prior slots. The scenarios
cover static and dynamic shapes, every field kind, padding, the lengths 0, 1,
31, 32, 33, 63 and 64, both outcomes, values carried past a revert, and
wrapping sums. Both the Core contract and the source model must give each row. -/
set_option autoImplicit false

namespace Tests.SourceEnumReturnGolden

open Lean
open Solcore.Core (Word)
open Solcore.ContractRuntime
open Solcore.Synthesis.Core
open Solcore.Synthesis.Core.EnumReturn (Constructor Shape)
open Solcore.Synthesis.Stateful
open Solcore.Synthesis.Stateful.EnumReturnExecution (Transaction)

private def get {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def w (value : Nat) : Word := Word.ofNatModulo value

/-- The step `x ↦ x + c`: aggregate template 0 around the constant scalar. -/
private def step (c : Nat) : IO Aggregates.CheckedDAG := do
  let some dag := Aggregates.CheckedDAG.ofParts? [Solcore.Synthesis.Source.Aggregate.template 0 (.word (w c))]
      (.apply (.var 1) (.var 0)) | throw (IO.userError "constant step failed admission")
  return dag

/-- The expected row: status, the whole output as hexadecimal text and slots
zero to two. -/
private structure Expected where
  status : String
  output : String
  values : List Nat

private def slots (values : List Nat) : Json :=
  toJson ((List.range EnumReturn.slotCount).map fun slot => Json.mkObj [
    ("slot", toJson (toString slot)), ("value", toJson (toString (values.getD slot 0)))])

private def tx (index flags input choice length : Nat) : Transaction :=
  ⟨"tx-" ++ toString index, w flags, w input, w choice, w length⟩

/-- One Word's 64 hexadecimal digits, written as the digits after a run of zeros. -/
private def hexWord (digits : String) : String :=
  String.ofList (List.replicate (64 - digits.length) '0') ++ digits

private def zeroWord : String := hexWord ""

-- The tags `keccak256("Name(fields)")`, as `cast keccak` writes them.
-- Blob(bytes)
private def tagBlobBytes : String := "d05ce3dc4caf4a4b252e3323bde615dc3b9d54623e1859c892f0b4ecf5e45164"
-- Idle()
private def tagIdleUnit : String := "ae897c555b7596dee56949d599aa959af71416324ac27ef76dd898923ab34d4f"
-- OverflowedAccumulator(bytes)
private def tagOverflowedAccumulatorBytes : String := "1d021c79c75f3d483321c073ba0acaa5b4589d7a6ad132e8b5fe27d9b76d678b"
-- Pair(uint256,uint256)
private def tagPairPair : String := "2d3b57dedfada8371bdae932a6881ace0dec34c90dd19fd49b2164124e699e2d"
-- Q(bytes)
private def tagQBytes : String := "ceddd0f6fa798287ec511a63a42164c8eb23d85a7f6355be56c0e9119d5f93b4"
-- Q(uint256)
private def tagQWord : String := "5dcad53f88dc9d20c351c1bb58593dde38a673b5308c8751aaeb91edd8c97952"
-- Ready()
private def tagReadyUnit : String := "6e12fa0ff1c6b8acb2181ba65fc2867fd8d895d0af9f39674b64abc5ff79275b"
-- Ready(uint256)
private def tagReadyWord : String := "0b217ad5c70346c7cd952bd2463c6684a56f9ed229f5780947586625781b4770"
-- Rejected()
private def tagRejectedUnit : String := "efde6dcf3c2196c5705e848c09f0659d33de3ca0248be3ab40852d1bafc0f1e3"
-- Settled(uint256,uint256)
private def tagSettledPair : String := "f5b268a3ff315cc44ccceeef86259c9e8eef81ceecb14001543809115380dd62"

/-- `Pair(uint256, uint256) | Idle | Q(uint256)`, static with a three-Word head,
`c = 5`. A revert between two returns, then a sum that wraps: 26 + (2^256 -
1) + 5 = 30. -/
private def staticRows : List (Transaction × Expected) := [
  (tx 0 0 7 0 0, ⟨"returned",
      tagPairPair ++
      "6a99b4b1f77dd1076b5904845b256270c619d90f6b9d5bd7a514f8d5c912aefc" ++
      "9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95",
      [12, 1, 7]⟩),
  (tx 1 1 3 1 0, ⟨"reverted",
      hexWord "14",
      [12, 1, 7]⟩),
  (tx 2 2 9 1 0, ⟨"returned",
      tagIdleUnit ++
      zeroWord ++
      zeroWord,
      [26, 2, 9]⟩),
  (tx 3 0 (2 ^ 256 - 1) 2 0, ⟨"returned",
      tagQWord ++
      "8a8043bceaba8a928c5e8b4ae3dd7619ef409ea68d09659b1cb46e1676aeb576" ++
      zeroWord,
      [30, 3, (2 ^ 256 - 1)]⟩)]

/-- `Blob(bytes) | Ready(uint256) | Settled(uint256, uint256) | Rejected`,
dynamic with a three-Word body head, `c = 1`: a `bytes` field's offset is
0x60 and one zero Word precedes its tail. -/
private def dynamicRows : List (Transaction × Expected) := [
  (tx 0 0 4 0 33, ⟨"returned",
      hexWord "20" ++
      tagBlobBytes ++
      hexWord "60" ++
      zeroWord ++
      hexWord "21" ++
      "1715609f7c746c6dc20fc1e1d0a4e904528ac51bc22c3b99da1e125913c7c8e9" ++
      "9e00000000000000000000000000000000000000000000000000000000000000",
      [5, 1, 4]⟩),
  (tx 1 0 6 3 0, ⟨"returned",
      hexWord "20" ++
      tagRejectedUnit ++
      zeroWord ++
      zeroWord,
      [12, 2, 6]⟩),
  (tx 2 3 8 0 64, ⟨"reverted",
      hexWord "15",
      [12, 2, 6]⟩),
  (tx 3 0 (2 ^ 255) 1 0, ⟨"returned",
      hexWord "20" ++
      tagReadyWord ++
      "88d12e6b76c84d1d5ef5c4e4b8132aa4d69c007b5f3fce299d8162e799d43d91" ++
      zeroWord,
      [(2 ^ 255 + 13), 3, (2 ^ 255)]⟩),
  (tx 4 0 0 2 0, ⟨"returned",
      hexWord "20" ++
      tagSettledPair ++
      "2708a824f612c933529285451500f2d8e71e27e752e2407b95edccf96a95cc26" ++
      "f8dde6e5fd29f057ce73018173b720d042089dafce89c947e1b1a84743063a54",
      [(2 ^ 255 + 14), 4, 0]⟩),
  (tx 5 0 1 0 0, ⟨"returned",
      hexWord "20" ++
      tagBlobBytes ++
      hexWord "60" ++
      zeroWord ++
      zeroWord,
      [(2 ^ 255 + 16), 5, 1]⟩)]

/-- `OverflowedAccumulator(bytes) | Q(bytes)`, two `bytes` constructors behind a
two-Word body head, `c = 2`, over the lengths 1, 31, 32, 63 and 64. -/
private def bytesRows : List (Transaction × Expected) := [
  (tx 0 0 1 1 1, ⟨"returned",
      hexWord "20" ++
      tagQBytes ++
      hexWord "40" ++
      hexWord "1" ++
      "da00000000000000000000000000000000000000000000000000000000000000",
      [3, 1, 1]⟩),
  (tx 1 0 2 0 31, ⟨"returned",
      hexWord "20" ++
      tagOverflowedAccumulatorBytes ++
      hexWord "40" ++
      hexWord "1f" ++
      "538454127b096499a94942a28a80796c738f13f3a971203dcaf6e67cb54ae600",
      [7, 2, 2]⟩),
  (tx 2 0 3 1 32, ⟨"returned",
      hexWord "20" ++
      tagQBytes ++
      hexWord "40" ++
      hexWord "20" ++
      "6a99b4b1f77dd1076b5904845b256270c619d90f6b9d5bd7a514f8d5c912aefc",
      [12, 3, 3]⟩),
  (tx 3 0 4 0 63, ⟨"returned",
      hexWord "20" ++
      tagOverflowedAccumulatorBytes ++
      hexWord "40" ++
      hexWord "3f" ++
      "1fe68f0af33cb98b210586c688b813a92926c597216c09c3779f7540ad9c067a" ++
      "78dde6e5fd29f057ce73018173b720d042089dafce89c947e1b1a84743063a00",
      [18, 4, 4]⟩),
  (tx 4 0 5 1 64, ⟨"returned",
      hexWord "20" ++
      tagQBytes ++
      hexWord "40" ++
      hexWord "40" ++
      "736ae31d6e461e24ca4ec96913388d159cb5d98acadd2a0142965bbd62e6ec8d" ++
      "1715609f7c746c6dc20fc1e1d0a4e904528ac51bc22c3b99da1e125913c7c8ed",
      [25, 5, 5]⟩)]

/-- `Idle | Ready`, static and field-less: each value is its one tag Word, `c = 3`. -/
private def tagRows : List (Transaction × Expected) := [
  (tx 0 0 0 1 0, ⟨"returned",
      tagReadyUnit,
      [3, 1, 0]⟩),
  (tx 1 0 1 0 0, ⟨"returned",
      tagIdleUnit,
      [7, 2, 1]⟩),
  (tx 2 1 2 0 0, ⟨"reverted",
      hexWord "c",
      [7, 2, 1]⟩),
  (tx 3 0 5 1 0, ⟨"returned",
      tagReadyUnit,
      [15, 3, 5]⟩)]

private def scenarios : List (String × Nat × List Constructor × List (Transaction × Expected)) := [
    ("static-carried", 5, [⟨"Pair", .twoWords⟩, ⟨"Idle", .noWords⟩, ⟨"Q", .oneWord⟩], staticRows),
    ("dynamic-wide", 1, [⟨"Blob", .boundedBytes⟩, ⟨"Ready", .oneWord⟩, ⟨"Settled", .twoWords⟩, ⟨"Rejected", .noWords⟩], dynamicRows),
    ("two-bytes", 2, [⟨"OverflowedAccumulator", .boundedBytes⟩, ⟨"Q", .boundedBytes⟩], bytesRows),
    ("tags-only", 3, [⟨"Idle", .noWords⟩, ⟨"Ready", .noWords⟩], tagRows)]

private def check (name : String) (row : Json) (model : EnumReturnExecution.ModelRow) (expected : Expected) : IO Unit := do
  ensure ((row.getObjValAs? String "status").toOption == some expected.status &&
      (row.getObjValAs? String "output").toOption == some ("0x" ++ expected.output) &&
      (row.getObjVal? "committedStorage").toOption == some (slots expected.values))
    s!"{name}: original Core differs from the expected row {row.compress}"
  ensure (model.reverted == (expected.status == "reverted") &&
      encodeBytesText model.output == "0x" ++ expected.output &&
      model.slots == (List.range EnumReturn.slotCount).map (fun slot => w (expected.values.getD slot 0)))
    s!"{name}: the source model differs from the expected row"

def testSourceEnumReturnGolden : IO Unit := do
  let fuel := 1000000
  ensure (Solcore.Synthesis.Source.EnumReturn.multiplierLiteral ==
      "0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95")
    "the emitted multiplier differs from the defined constant"
  -- Lean's Keccak-256 tags equal the ones written out.
  ensure (encodeBytesText (encodeWordBytesBE (EnumReturn.tag ⟨"Pair", .twoWords⟩)) == "0x" ++ tagPairPair &&
      encodeBytesText (encodeWordBytesBE (EnumReturn.tag ⟨"Q", .boundedBytes⟩)) == "0x" ++ tagQBytes &&
      encodeBytesText (encodeWordBytesBE (EnumReturn.tag ⟨"Idle", .noWords⟩)) == "0x" ++ tagIdleUnit)
    "a constructor tag differs from keccak256 of its signature"
  for (name, constant, constructors, rows) in scenarios do
    let step ← step constant
    let some shape := Solcore.Synthesis.Source.EnumReturn.Shape.ofList? constructors
      | throw (IO.userError s!"{name}: the shape has fewer than two constructors")
    let some plan := EnumReturn.CheckedPlan.ofParts? step shape
      | throw (IO.userError s!"{name}: the enum-return wrapper failed admission")
    ensure (plan.contract.entryProfile == shape.profile)
      s!"{name}: the contract does not use the shape's enum convention"
    let transactions := rows.map Prod.fst
    let history := EnumReturnExecution.observe plan transactions StorageExecution.fixtureBindings fuel
    ensure ((history.getObjValAs? String "status").toOption == some "complete") s!"{name}: the history is incomplete"
    let observed ← get (history.getObjValAs? (Array Json) "transactions")
    let some modelled := EnumReturnExecution.model step constructors fuel transactions
      | throw (IO.userError s!"{name}: the source model failed")
    ensure (observed.size == rows.length && modelled.length == rows.length) s!"{name}: a row is missing"
    for ((row, model), (transaction, expected)) in (observed.toList.zip modelled).zip rows do
      check s!"{name} {transaction.id}" row model expected
  -- A changed Word fails: the second scenario's first row with another tag.
  let some (transaction, expected) := dynamicRows.head? | throw (IO.userError "no dynamic row")
  let some shape := Solcore.Synthesis.Source.EnumReturn.Shape.ofList?
      [⟨"Blob", .boundedBytes⟩, ⟨"Ready", .oneWord⟩, ⟨"Settled", .twoWords⟩, ⟨"Rejected", .noWords⟩]
    | throw (IO.userError "no shape")
  let some plan := EnumReturn.CheckedPlan.ofParts? (← step 1) shape | throw (IO.userError "no plan")
  let history := EnumReturnExecution.observe plan [transaction] StorageExecution.fixtureBindings fuel
  let observed ← get (history.getObjValAs? (Array Json) "transactions")
  ensure ((observed[0]?.bind fun row => (row.getObjValAs? String "output").toOption) ==
      some ("0x" ++ expected.output) &&
    (observed[0]?.bind fun row => (row.getObjValAs? String "output").toOption) !=
      some ("0x" ++ (expected.output.replace tagBlobBytes tagQBytes)))
    "a changed tag is not detected"

end Tests.SourceEnumReturnGolden
end
