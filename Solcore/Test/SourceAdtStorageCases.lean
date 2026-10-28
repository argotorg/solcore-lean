import Solcore.Synthesis.Source.AdtStorageCases

/-! Generated enum and struct storage cases. Original Core must equal the
slot-map model on every transaction of the generated sequences: status, output
and every observed slot. Each case must replay to itself; the shell, closure,
method and case-limit node counts must be those the definitions fix; every
variant count, enum position, Word type and method must be drawn; and every
reduction must be a strictly smaller sealed case that replays. Decoding refuses
keys, fields, variants and methods outside the case, changed observed slots,
and shapes or method lists the definitions exclude. -/
set_option autoImplicit false

namespace Tests.SourceAdtStorageCases

open Lean
open Solcore.Core (Word)
open Solcore.ContractRuntime
open Solcore.Synthesis.Core
open Solcore.Synthesis.Core.AdtStorage (Method Shape Payload)
open Solcore.Synthesis.Stateful

private def get {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def storageJson (slots values : List Word) : Json :=
  toJson ((slots.zip values).map fun (slot, value) => Json.mkObj [
    ("slot", toJson (toString slot.val)), ("value", toJson (toString value.val))])

/-- The Core rows of a scenario equal the model's, transaction by transaction. -/
private def sameAsModel (scenario : Solcore.Synthesis.Source.AdtStorage.CheckedScenario) (fuel : Nat) (name : String) :
    IO Unit := do
  let history := Solcore.Synthesis.Source.AdtStorage.observe scenario StorageExecution.fixtureBindings fuel
  ensure ((history.getObjValAs? String "status").toOption == some "complete") s!"{name}: history incomplete"
  let rows ← get (history.getObjValAs? (Array Json) "transactions")
  let slots := scenario.observedSlots
  let some modelled := AdtStorageExecution.model scenario.plan fuel scenario.transactions
    | throw (IO.userError s!"{name}: the slot-map model failed")
  ensure (rows.size == modelled.length) s!"{name}: a row is missing"
  for (row, model) in rows.toList.zip modelled do
    ensure ((row.getObjValAs? String "status").toOption == some (if model.reverted then "reverted" else "returned") &&
        (row.getObjValAs? String "output").toOption == some (encodeBytesText (encodeWordBytesBE model.result)) &&
        (row.getObjVal? "committedStorage").toOption == some (storageJson slots (AdtStorageExecution.modelSlots model slots)))
      s!"{name}: the Core row differs from the slot-map model: {row.compress}"

/-- The decode of a case with one changed field is refused. -/
private def refused (name : String) (json : Json) : IO Unit :=
  ensure (Solcore.Synthesis.Source.AdtStorage.caseProgram json).toOption.isNone s!"{name} was admitted"

private def withTransaction (json : Json) (index : Nat) (change : Json → Json) : IO Json := do
  let rows ← get (json.getObjValAs? (Array Json) "transactions")
  return json.setObjVal! "transactions" (.arr (rows.modify index change))

private def withShape (json : Json) (shape : Json) : IO Json := do
  let plan ← get (json.getObjVal? "adtStoragePlan")
  return json.setObjVal! "adtStoragePlan" (plan.setObjVal! "shape" shape)

def testSourceAdtStorageCases : IO Unit := do
  let fuel := 1000000
  ensure (AdtStorage.hashNodes == 2654) s!"the Keccak closure has {AdtStorage.hashNodes} nodes"
  ensure (AdtStorage.shellNodes == 52) s!"the shell has {AdtStorage.shellNodes} nodes"
  ensure ([2, 3, 4].map (fun count => (AdtStorage.variantLists count).length) == [9, 44, 68])
    "the variant lists changed"
  ensure (AdtStorage.allShapes.length == 726 && AdtStorage.allShapes.all Shape.valid) "the shapes changed"
  let closures := AdtStorage.allShapes.map AdtStorage.closureNodes
  ensure (closures.foldl min 1000 == 59 && closures.foldl max 0 == 255) "the enum closures changed size"
  ensure (AdtStorage.allShapes.all fun shape => AdtStorage.methodNodes shape Method.all == 1008)
    "the methods changed size"
  ensure (AdtStorage.maxOutsideNodes == AdtStorage.allShapes.foldl
      (fun largest shape => max largest (AdtStorage.closureNodes shape + AdtStorage.methodNodes shape Method.all)) 0)
    "the outside bound differs from the largest shape"
  ensure (Solcore.Synthesis.Source.AdtStorage.maxProgramNodes == 4429) "the case limit changed"
  ensure ((Method.all.map (·.selector)).Nodup) "two method selectors collide"
  -- Random generation: revision three with eight transactions, and the fixed
  -- corpora's revision one with three.
  let mut counts : List Nat := []
  let mut positions : List Nat := []
  let mut types : List String := []
  let mut methods : List String := []
  let mut cases : Array Json := #[]
  for (revision, transactions, count) in [(GeneratorRevision.v3, 8, 12), (GeneratorRevision.v1, 3, 8)] do
    let corpus := Solcore.Synthesis.Source.AdtStorage.generateCases (Seed.ofNat 1) 384 count 512 fuel revision transactions
    ensure ((corpus.getObjValAs? String "status").toOption == some "complete") s!"{revision.version}: generation exhausted"
    let generated ← get (corpus.getObjValAs? (Array Json) "cases")
    for (json, index) in generated.zipIdx do
      let name := s!"{revision.version} case {index}"
      ensure ((Solcore.Synthesis.Source.AdtStorage.replayCase json fuel).toOption == some json) s!"{name}: replay differs"
      let scenario ← get (Solcore.Synthesis.Source.AdtStorage.caseProgram json)
      ensure (scenario.transactions.length == transactions) s!"{name}: wrong sequence length"
      ensure (scenario.plan.methods == Solcore.Synthesis.Source.AdtStorage.calledMethods scenario.transactions)
        s!"{name}: the declared methods are not the called ones"
      let slots := scenario.observedSlots
      ensure (slots.length ≤ 31 && (slots.zip slots.tail).all (fun (lower, upper) => lower.val < upper.val))
        s!"{name}: the observed slots exceed 31 or are unordered"
      ensure (Solcore.Core.Wire.programNodes scenario.program ≤ 384 + AdtStorage.hashNodes + AdtStorage.closureNodes scenario.plan.shape +
          AdtStorage.methodNodes scenario.plan.shape scenario.plan.methods) s!"{name}: the contract exceeds its budget"
      sameAsModel scenario fuel name
      cases := cases.push json
  -- Every variant count, enum position, Word type and method is drawn among
  -- sixty-four generated cases.
  let drawn := Solcore.Synthesis.Source.AdtStorage.generateCases (Seed.ofNat 1) 384 64 128 fuel .v3 3
  for json in ← get (drawn.getObjValAs? (Array Json) "cases") do
    let shape ← get ((← get (json.getObjVal? "adtStoragePlan")).getObjVal? "shape")
    counts := counts ++ [(← get (shape.getObjValAs? (List String) "variants")).length]
    positions := positions ++ [← get (shape.getObjValAs? Nat "position")]
    types := types ++ [← get (shape.getObjValAs? String "wordType")]
    for row in ← get (json.getObjValAs? (Array Json) "transactions") do
      methods := methods ++ [← get (row.getObjValAs? String "method")]
  ensure ([2, 3, 4].all counts.contains && [0, 1, 2].all positions.contains && ["word", "uint256"].all types.contains)
    "a variant count, enum position or Word type was never drawn"
  ensure (Method.all.all fun method => methods.contains method.name) "a method was never drawn"
  -- Reductions keep a case's keys and the step's bindings, and replay.
  for json in cases.toList.take 2 do
    let source ← get (Solcore.Synthesis.Source.AdtStorage.caseProgram json)
    let reductions := Solcore.Synthesis.Source.AdtStorage.reductions source
    ensure (!reductions.isEmpty) "a case has no reduction"
    let shrunk ← get (Solcore.Synthesis.Source.AdtStorage.shrinkCases json 12 fuel)
    let candidates ← get (shrunk.getObjValAs? (Array Json) "cases")
    ensure (candidates.size == min 12 reductions.length) "the shrink response differs from the reductions"
    for candidate in candidates do
      ensure ((Solcore.Synthesis.Source.AdtStorage.replayCase candidate fuel).toOption == some candidate)
        "a reduced case does not replay"
  -- Decoding refuses arguments, methods, slots and shapes outside the case.
  let json := cases[0]!
  let scenario ← get (Solcore.Synthesis.Source.AdtStorage.caseProgram json)
  let keyed := scenario.transactions.findIdx? (·.method.keyed)
  let variant := scenario.transactions.findIdx? (·.method.takesVariant)
  match keyed with
  | some index => refused "a key outside the case" (← withTransaction json index fun row => row.setObjVal! "key" (toJson "5"))
  | none => pure ()
  match variant with
  | some index =>
      refused "a variant outside the shape"
        (← withTransaction json index fun row => row.setObjVal! "variant" (toJson scenario.plan.shape.count))
  | none => pure ()
  refused "an undeclared method" (← withTransaction json 0 fun row =>
    row.setObjVal! "method" (toJson (if scenario.plan.methods.contains .getChoice then "putChoiceAt" else "getChoice")))
  refused "changed observed slots" (json.setObjVal! "observedSlots" (toJson ["0"]))
  refused "a shape without a payload-free variant"
    (← withShape json (Json.mkObj [("variants", toJson ["words1", "words1"]), ("position", toJson 0), ("wordType", toJson "word")]))
  refused "a shape of five enum slots"
    (← withShape json (Json.mkObj [("variants", toJson ["words0", "words1", "words3"]), ("position", toJson 0),
      ("wordType", toJson "word")]))
  refused "an unknown payload"
    (← withShape json (Json.mkObj [("variants", toJson ["words0", "words4"]), ("position", toJson 0), ("wordType", toJson "word")]))
  let plan ← get (json.getObjVal? "adtStoragePlan")
  ensure (scenario.plan.methods.length ≥ 2) "the first case declares one method"
  refused "methods out of declaration order"
    (json.setObjVal! "adtStoragePlan" (plan.setObjVal! "methods" (toJson (scenario.plan.methods.reverse.map (·.name)))))

end Tests.SourceAdtStorageCases
