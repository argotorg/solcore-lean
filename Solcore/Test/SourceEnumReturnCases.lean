import Solcore.Synthesis.Source.EnumReturnCases

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
