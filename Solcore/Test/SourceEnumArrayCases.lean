import Solcore.Synthesis.Source.EnumArrayCases

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

/-- Original Core's revert Word for std's revert data: the selector Word for
four bytes, the Word zero for none. -/
private def coreOutput (output : ByteArray) : String :=
  if output.size == 4 then
    encodeBytesText (encodeWordBytesBE (Word.ofNatModulo (StdCalldata.bigEndian output 0 4)))
  else if output.size == 0 then encodeBytesText (encodeWordBytesBE Word.zero)
  else encodeBytesText output

/-- The std outcome a model row stands for. -/
private def outcome (row : EnumArrayExecution.ModelRow) : String :=
  if row.output.size == 4 then encodeBytesText row.output
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
