import Solcore.Synthesis.Source.EnumArgumentCases

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
