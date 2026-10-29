import Solcore.Synthesis.Source.ArrayReturnCases

/-! Generated array-return cases. The Core contract must equal the source model,
a slot map and std's encoder run over the elements' memory, on every
transaction of the generated sequences; each case must replay to itself; the
shell node counts must be the ones the definitions fix; generation must draw
every element type and count, every bank length and inner length; every reduction must
be a strictly smaller sealed case that replays; and a transaction that does not
carry its plan's shape must be refused. -/
set_option autoImplicit false

namespace Tests.SourceArrayReturnCases

open Lean
open Solcore.Core (Word)
open Solcore.ContractRuntime
open Solcore.Synthesis.Core
open Solcore.Synthesis.Core.ArrayReturn (Element Shape)
open Solcore.Synthesis.Stateful
open Solcore.Synthesis.Stateful.ArrayReturnExecution (Transaction)

private def get {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def slots (values : List Word) : Json :=
  toJson ((values.zipIdx).map fun (value, slot) => Json.mkObj [
    ("slot", toJson (toString slot)), ("value", toJson (toString value.val))])

/-- The Core rows of a scenario equal the model's, transaction by transaction. -/
private def sameAsModel (scenario : Solcore.Synthesis.Source.ArrayReturn.CheckedScenario) (fuel : Nat) (name : String) :
    IO Unit := do
  let history := Solcore.Synthesis.Source.ArrayReturn.observe scenario StorageExecution.fixtureBindings fuel
  ensure ((history.getObjValAs? String "status").toOption == some "complete") s!"{name}: history incomplete"
  let rows ← get (history.getObjValAs? (Array Json) "transactions")
  let some modelled := ArrayReturnExecution.model scenario.plan.step fuel scenario.plan.shape.element
      scenario.transactions | throw (IO.userError s!"{name}: the source model failed")
  ensure (rows.size == modelled.length) s!"{name}: a row is missing"
  for (row, model) in rows.toList.zip modelled do
    ensure ((row.getObjValAs? String "status").toOption == some (if model.reverted then "reverted" else "returned") &&
        (row.getObjValAs? String "output").toOption == some (encodeBytesText model.output) &&
        (row.getObjVal? "committedStorage").toOption == some (slots model.slots))
      s!"{name}: the Core row differs from the source model: {row.compress}"
    -- A return carries the encoding's Words, a revert one Word.
    ensure (model.output.size == if model.reverted then 32 else 32 * scenario.plan.shape.wordCount)
      s!"{name}: the output has the wrong size"

private def shape (element : Element) (lengths : List Nat) (count : Nat := lengths.length) : Shape :=
  ⟨element, count, if element.dynamic then lengths else []⟩

def testSourceArrayReturnCases : IO Unit := do
  let fuel := 1000000
  -- The shells the definitions fix: 89 nodes for an empty array, 175 for three
  -- `bytes` elements whose second data Words are masked.
  for (element, lengths, count, nodes) in [(Element.words, [], 0, 89), (.words, [], 3, 111), (.fourBytes, [], 3, 123),
      (.bytes, [64, 64, 64], 3, 169), (.bytes, [63, 63, 63], 3, 175), (.bytes, [0, 0, 0], 3, 125),
      (.nested, [2, 2, 2], 3, 169), (.nested, [0], 1, 101)] do
    ensure (ArrayReturn.shellNodes (shape element lengths count) == nodes)
      s!"the {element.name} shell of {lengths} has {ArrayReturn.shellNodes (shape element lengths count)} nodes"
  let mut minimum := 1000
  let mut maximum := 0
  for element in Solcore.Synthesis.Source.ArrayReturn.elementTypes do
    for count in List.range 4 do
      for length in (if element.dynamic then List.range (element.maxLength + 1) else [0]) do
        let nodes := ArrayReturn.shellNodes (shape element (List.replicate count length) count)
        minimum := min minimum nodes
        maximum := max maximum nodes
  ensure (minimum == 89 && maximum == 175) s!"the shells range over {minimum}..{maximum} nodes"
  ensure (Solcore.Synthesis.Source.ArrayReturn.maxProgramNodes == 512) "the case limit changed"
  -- Random generation: revision three with eight transactions at both budgets,
  -- and the fixed corpora's revision one with three.
  let mut elements : List String := []
  let mut counts : List String := []
  let mut bytesLengths : List Nat := []
  let mut innerLengths : List Nat := []
  let mut cases : Array Json := #[]
  for (revision, transactions, count, nodes) in [(GeneratorRevision.v3, 8, 40, 384), (GeneratorRevision.v1, 3, 24, 384),
      (GeneratorRevision.v3, 4, 12, 512)] do
    let corpus := Solcore.Synthesis.Source.ArrayReturn.generateCases (Seed.ofNat 1) nodes count 512 fuel revision transactions
    ensure ((corpus.getObjValAs? String "status").toOption == some "complete") s!"{revision.version}: generation exhausted"
    let generated ← get (corpus.getObjValAs? (Array Json) "cases")
    for (json, index) in generated.zipIdx do
      let name := s!"{revision.version} {nodes} case {index}"
      ensure ((Solcore.Synthesis.Source.ArrayReturn.replayCase json fuel).toOption == some json) s!"{name}: replay differs"
      let scenario ← get (Solcore.Synthesis.Source.ArrayReturn.caseProgram json)
      ensure (scenario.transactions.length == transactions) s!"{name}: wrong sequence length"
      sameAsModel scenario fuel name
      let source ← get (json.getObjValAs? String "source")
      ensure ((source.splitOn "public returns (uint256) {").length == 2 &&
          (source.splitOn "abi_encode(sc_items)").length == 2 && (source.splitOn "return_((sc_encoded + 32)").length == 2)
        s!"{name}: the emitted method differs"
      let current := scenario.plan.shape
      elements := (elements ++ [current.element.name]).eraseDups
      counts := (counts ++ [s!"{current.count}"]).eraseDups
      cases := cases.push json
  ensure (sameMembers elements ["uint256", "bytes4", "bytes", "uint256[]"]) s!"generation drew the element types {elements}"
  ensure (sameMembers counts ["0", "1", "2", "3"]) s!"generation drew the counts {counts}"
  -- The shape draws alone, over the first 256 seeds: every element type with
  -- every count, every bank length, a uniform partial-Word length and every
  -- inner length.
  let mut pairs : List String := []
  for index in List.range 256 do
    let current := Solcore.Synthesis.Source.ArrayReturn.generatedShape (Seed.ofNat (1 + index))
    pairs := (pairs ++ [s!"{current.element.name}:{current.count}"]).eraseDups
    if current.element == .bytes then bytesLengths := (bytesLengths ++ current.lengths).eraseDups
    if current.element == .nested then innerLengths := (innerLengths ++ current.lengths).eraseDups
  ensure ([0, 1, 2, 3].all fun count => ["uint256", "bytes4", "bytes", "uint256[]"].all fun element =>
      pairs.contains s!"{element}:{count}") s!"the shape draws missed an element type's count: {pairs}"
  for length in Solcore.Synthesis.Source.ArrayReturn.lengthBank do
    ensure (bytesLengths.contains length) s!"generation never drew bytes length {length}"
  ensure (bytesLengths.all (· ≤ 64) && bytesLengths.any (fun length => length % 32 != 0 &&
      !Solcore.Synthesis.Source.ArrayReturn.lengthBank.contains length))
    "generation drew a bytes length above 64 or no uniform partial-Word length"
  ensure (sameMembers innerLengths [0, 1, 2]) s!"generation drew the inner lengths {innerLengths}"
  -- Reductions: a dropped element, `uint256` elements and a shorter length
  -- come whenever they apply, and every emitted candidate replays as a
  -- strictly smaller sealed case that equals the model.
  for json in cases.toList.take 8 do
    let source ← get (Solcore.Synthesis.Source.ArrayReturn.caseProgram json)
    let current := source.plan.shape
    let reduced := Solcore.Synthesis.Source.ArrayReturn.reductions source
    ensure (!reduced.isEmpty) "a case has no reduction"
    let same := fun (candidate : Solcore.Synthesis.Source.ArrayReturn.Reduction source) =>
      candidate.candidate.transactions.length == source.transactions.length
    ensure (current.count == 0 || reduced.any fun candidate => same candidate &&
        candidate.candidate.plan.shape.count + 1 == current.count) "no dropped element"
    ensure (current.element == .words || reduced.any fun candidate => same candidate &&
        candidate.candidate.plan.shape == ⟨.words, current.count, []⟩) "no uint256 elements"
    ensure (Solcore.Synthesis.Source.ArrayReturn.totalLength current == 0 || reduced.any fun candidate =>
        same candidate && candidate.candidate.plan.shape.element == current.element &&
        Solcore.Synthesis.Source.ArrayReturn.totalLength candidate.candidate.plan.shape <
          Solcore.Synthesis.Source.ArrayReturn.totalLength current) "no shorter inner length"
    ensure (reduced.all fun candidate => candidate.candidate.transactions.all
        (Solcore.Synthesis.Source.ArrayReturn.admits candidate.candidate.plan.shape))
      "a reduction left a transaction off its plan's shape"
    let shrunk ← get (Solcore.Synthesis.Source.ArrayReturn.shrinkCases json 64 fuel)
    for candidate in ← get (shrunk.getObjValAs? (Array Json) "cases") do
      ensure ((Solcore.Synthesis.Source.ArrayReturn.replayCase candidate fuel).toOption == some candidate)
        "a reduction does not replay"
      sameAsModel (← get (Solcore.Synthesis.Source.ArrayReturn.caseProgram candidate)) fuel "reduction"
  -- A transaction off its plan's shape is refused even with its own calldata:
  -- another length, another choice, or another digit of an inner length.
  let some json := cases.toList.find? (fun json => (json.getObjVal? "arrayReturnPlan").toOption.any
      fun plan => (plan.getObjValAs? String "elements").toOption == some "bytes" &&
        (plan.getObjValAs? Nat "count").toOption.any (· ≥ 2)) | throw (IO.userError "no bytes case")
  let scenario ← get (Solcore.Synthesis.Source.ArrayReturn.caseProgram json)
  let transactions ← get (json.getObjValAs? (Array Json) "transactions")
  let first := transactions[0]!
  let some tx := scenario.transactions.head? | throw (IO.userError "no transaction")
  for (choice, length) in [(tx.choice, tx.length + Word.ofNatModulo 4), (tx.choice + Word.ofNatModulo 1, tx.length),
      (tx.choice + Word.ofNatModulo 65, tx.length), (tx.choice, Word.ofNatModulo 0)] do
    let changed := first.setObjVal! "choice" (toJson (toString choice.val)) |>.setObjVal! "length"
      (toJson (toString length.val)) |>.setObjVal! "calldata"
      (toJson (ArrayReturnExecution.calldata tx.flags tx.input choice length))
    ensure (Solcore.Synthesis.Source.ArrayReturn.caseProgram
        (json.setObjVal! "transactions" (.arr (transactions.set! 0 changed)))).toOption.isNone
      s!"a transaction with choice {choice.val} and length {length.val} was admitted"
  ensure (Solcore.Synthesis.Source.ArrayReturn.caseProgram (json.setObjVal! "transactions" (.arr (transactions.set! 0
      (first.setObjVal! "length" (toJson "7")))))).toOption.isNone
    "a length that differs from its calldata was admitted"
  -- Plans outside the shapes are refused.
  let plan ← get (json.getObjVal? "arrayReturnPlan")
  ensure (Solcore.Synthesis.Source.ArrayReturn.checkedPlan (plan.setObjVal! "arity" (toJson 2))).toOption.isNone
    "a plan with an extra field was admitted"
  for (element, count, lengths) in [("bytes", 4, [0, 0, 0, 0]), ("bytes", 2, [0]), ("bytes", 1, [65]),
      ("uint256[]", 1, [3]), ("uint256", 1, [0]), ("bytes32", 1, []), ("SynthesizedEnum", 1, [])] do
    ensure (Solcore.Synthesis.Source.ArrayReturn.checkedPlan (plan.setObjVal! "elements" (toJson element)
        |>.setObjVal! "count" (toJson count) |>.setObjVal! "lengths" (toJson lengths))).toOption.isNone
      s!"the plan {element} {count} {lengths} was admitted"
where
  sameMembers {α : Type} [BEq α] (left right : List α) : Bool := left.all right.contains && right.all left.contains

end Tests.SourceArrayReturnCases
