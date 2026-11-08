import Solcore.Synthesis.Internal.AdtStorage
import Solcore.Synthesis.Internal.Storage
import Solcore.ContractRuntime.Internal.ContractLaws
import Solcore.ContractRuntime.Internal.TopLevelLaws

/-!
# Storage profile tests

Storage, ledgers, mappings, keyed storage, rollback, and enum and struct storage.
-/

section
-- leanmerge: from Solcore.Test.SourceAdtStorageCases
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
end

section
-- leanmerge: from Solcore.Test.SourceAdtStorageCorpus
/-! The fixed enum and struct storage corpus checks actual original Core
histories against expectations computed without the Core contract: the
slot-map model, in which each step runs alone in Core. The expectations cover
status, output and every observed slot, stale payload slots included.
Coverage describes the checked steps' AST, the inputs, the shapes' variant
counts, payload kinds, payload-free and enum positions and Word types, the
methods, the overwrites of one committed variant by another at one location,
the field updates, the reads whose enum slots keep a Word outside the decoded
variant, both keys of each mapping and across the wrap, the reverted writes
and the completions. Source/Rust/EVM agreement is a separate external
validation. -/
set_option autoImplicit false

namespace Tests.SourceAdtStorageCorpus
open Lean Solcore.Core Solcore.Synthesis.Core Solcore.Synthesis.Source
open Solcore.Synthesis.Core.AdtStorage (Method Shape Payload tagWrites payloadOffset)
open Solcore.Synthesis.Stateful.AdtStorageExecution (Transaction)

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
  ("generatorVersion", generatorVersion), ("profileVersion", AdtStorage.profileVersion),
  ("functionVersion", Solcore.Synthesis.Core.AdtStorage.version),
  ("templateVersion", AdtStorage.templateVersion), ("stepProfileVersion", Aggregate.profileVersion),
  ("stepFunctionVersion", Aggregates.version), ("stepTemplateVersion", Aggregate.templateVersion),
  ("emitterVersion", AdtStorage.emitterVersion), ("wrapperVersion", AdtStorage.wrapperVersion)]

private def words (values : List Word) : List String := values.map fun value => toString value.val

/-- Imported entries are emitted from their saved plan and sequence; generated
entries are regenerated from their seed. Both are checked by full replay. -/
private def entryCase (entry : Json) (fuel : Nat) : Except String Json := do
  if let .ok request := entry.getObjVal? "generation" then
    let some seed := (← request.getObjValAs? String "seed").toNat? | throw "invalid generation seed"
    let corpus := AdtStorage.generateCases (Seed.ofNat seed) (← request.getObjValAs? Nat "maxProgramNodes") 1 1 fuel
    require ((← string corpus "status") == "complete") "generated entry was excluded"
    let some saved := (← corpus.getObjValAs? (Array Json) "cases")[0]? | throw "generated entry has no case"
    return saved
  let plan ← AdtStorage.checkedPlan (← entry.getObjVal? "adtStoragePlan")
  let scenario ← AdtStorage.checkedScenario plan (← AdtStorage.decodeTransactions plan (← entry.getObjVal? "transactions"))
  AdtStorage.emitCase scenario (Json.mkObj [("kind", toJson "imported")]) fuel

private def templates (saved : Json) : Except String (List Nat) := do
  let origin ← (← saved.getObjVal? "provenance").getObjVal? "origin"
  if (← string origin "kind") != "adt-storage-generated" then return []
  let helpers ← (← origin.getObjVal? "stepOrigin").getObjValAs? (List Json) "helpers"
  helpers.mapM fun helper => helper.getObjValAs? Nat "template"

private def naturals (manifest : Json) (key : String) : Except String (List Nat) :=
  manifest.getObjValAs? (List Nat) key

/-- The enum offsets variant `variant` of the shape occupies: the tags its
decoding reads and its payload. -/
private def occupied (shape : Shape) (variant : Nat) : List Nat :=
  (tagWrites shape.count variant).map Prod.fst ++
    (List.range (shape.width variant)).map (payloadOffset shape.count variant + ·)

/-- One scenario's coverage values by dimension, over its committed
transactions in order: overwrites `count:old>new` at each enum location,
updates `target:kind`, stale reads, both keys of a mapping, the wrap, and the
writing methods that reverted. -/
private def coverage (scenario : AdtStorage.CheckedScenario) (statuses : List String) : List (String × String) := Id.run do
  let shape := scenario.plan.shape
  let mut variants : List ((Bool × Option Nat) × Nat) := []
  let mut written : List ((Bool × Option Nat) × List Nat) := []
  let mut values : List (String × String) := []
  let mut keyed : List (Bool × Nat) := []
  for (tx, status) in scenario.transactions.zip statuses do
    let method := tx.method
    if status == "reverted" && !method.reads then
      values := values ++ [("AdtRevertedWrites", method.name)]
    if status == "returned" then
      let location := (method.record, if method.keyed then some tx.key.val else none)
      let previous := (variants.find? (·.1 == location)).map Prod.snd
      let slots := ((written.find? (·.1 == location)).map Prod.snd).getD []
      if method.reads then
        if let some variant := previous then
          if slots.any fun offset => !(occupied shape variant).contains offset then
            values := values ++ [("AdtStaleReads", method.name)]
      else
        if method.keyed then keyed := keyed ++ [(method.record, tx.key.val)]
        if method.updates then
          values := values ++ [("AdtFieldUpdates", (if method.keyed then "entry:" else "record:") ++
            (if tx.field == shape.position then "choice" else "word"))]
        if !method.updates || tx.field == shape.position then
          let variant := if method.clears then shape.clearVariant else tx.variant
          if let some old := previous then
            if old != variant then
              values := values ++ [("AdtOverwrites", s!"{shape.count}:{old}>{variant}")]
          variants := (location, variant) :: variants.filter (·.1 != location)
          written := (location, (slots ++ occupied shape variant).eraseDups) :: written.filter (·.1 != location)
  let keys := scenario.plan.keys.map (·.val)
  for (record, name) in [(false, "choices"), (true, "records")] do
    if keys.all fun key => keyed.contains (record, key) then
      values := values ++ [("AdtNeighbourKeys", name)] ++
        (if scenario.plan.keyBase.val == 2 ^ 256 - 1 then [("AdtNeighbourKeys", "wrap")] else [])
  let clear := shape.clearVariant
  return values ++ [("AdtVariantCounts", toString shape.count),
    ("AdtClearPositions", if clear == 0 then "first" else if clear + 1 == shape.count then "last" else "middle"),
    ("AdtChoicePositions", toString shape.position), ("AdtWordTypes", shape.wordType.name)] ++
    shape.variants.map (fun payload => ("AdtPayloads", payload.name)) ++
    scenario.transactions.map (fun tx => ("AdtMethods", tx.method.name))

/-- Every value of each coverage dimension, as the manifest spells it. -/
private def dimensions : List (String × List String) := [
  ("AdtVariantCounts", ["2", "3", "4"]), ("AdtPayloads", Payload.all.map Payload.name),
  ("AdtClearPositions", ["first", "middle", "last"]), ("AdtChoicePositions", ["0", "1", "2"]),
  ("AdtWordTypes", ["word", "uint256"]), ("AdtMethods", Method.all.map (·.name)),
  ("AdtOverwrites", [2, 3, 4].flatMap fun count => (List.range count).flatMap fun old =>
    ((List.range count).filter (· != old)).map fun new => s!"{count}:{old}>{new}"),
  ("AdtFieldUpdates", ["record:word", "record:choice", "entry:word", "entry:choice"]),
  ("AdtStaleReads", ["getChoice", "getChoiceAt", "getRecord", "getRecordAt"]),
  ("AdtNeighbourKeys", ["choices", "records", "wrap"]),
  ("AdtRevertedWrites", (Method.all.filter (!·.reads)).map (·.name))]

/-- A required dimension as strings: the integer dimensions are written as numbers. -/
private def required (manifest : Json) (dimension : String) : Except String (List String) := do
  if dimension == "AdtVariantCounts" || dimension == "AdtChoicePositions" then
    return (← naturals manifest ("required" ++ dimension)).map toString
  strings manifest ("required" ++ dimension)

def validateManifest (manifest : Json) (fuel : Nat := 1000000) : Except String Json := do
  require ((← string manifest "schema") == "solcore-lean.semantic-storage-corpus-manifest.v1" &&
    (← string manifest "profile") == "stateful-adt-storage" &&
    (← string manifest "coverageKind") == "step-core-ast-features") "unexpected enum and struct storage manifest scope"
  for (key, expected) in versions do
    require ((← string manifest key) == expected) ("enum and struct storage manifest changed " ++ key)
  let requiredFeatures ← strings manifest "requiredFeatures"
  let requiredInputs ← strings manifest "requiredInputs"
  require (sameMembers requiredInputs (words AdtStorage.boundaryInputs))
    "enum and struct storage corpus must require all six boundary inputs"
  for (dimension, values) in dimensions do
    require (sameMembers (← required manifest dimension) values)
      ("enum and struct storage corpus must require every value of " ++ dimension)
  require ((← naturals manifest "requiredHelperCounts") == [1, 2, 3] &&
    (← naturals manifest "requiredTransactionCounts") == [1, 2, 3])
    "enum and struct storage corpus must require one to three helpers and transactions"
  require ((← (← manifest.getObjVal? "generationRecipeRequirements").getObjValAs? (List Nat) "templates") == [0, 1, 2, 3])
    "enum and struct storage corpus must require all four step templates"
  require ((← strings manifest "requiredOutcomes") == ["returned", "reverted"])
    "enum and struct storage corpus must require both outcomes"
  let requiredPatterns ← strings manifest "requiredCompletionPatterns"
  require (!requiredPatterns.isEmpty) "enum and struct storage corpus must require completion patterns"
  let entries ← manifest.getObjValAs? (Array Json) "cases"
  require (0 < entries.size && entries.size ≤ 64) "enum and struct storage corpus must contain 1..64 scenarios"
  let mut identifiers : List String := []
  let mut features : List String := []
  let mut inputs : List String := []
  let mut covered : List (String × String) := []
  let mut helperCounts : List Nat := []
  let mut transactionCounts : List Nat := []
  let mut templateUnion : List Nat := []
  let mut outcomes : List String := []
  let mut patterns : List String := []
  let mut transactionTotal := 0
  for entry in entries do
    let identifier ← string entry "id"
    require (!identifiers.contains identifier) ("duplicate enum and struct storage corpus id " ++ identifier)
    identifiers := identifier :: identifiers
    let saved ← entryCase entry fuel
    require ((← AdtStorage.replayCase saved fuel) == saved) ("enum and struct storage corpus entry did not replay: " ++ identifier)
    let scenario ← AdtStorage.caseProgram saved
    if !(entry.getObjVal? "generation").isOk then
      require ((← saved.getObjVal? "adtStoragePlan") == (← entry.getObjVal? "adtStoragePlan") &&
        (← saved.getObjVal? "transactions") == (← entry.getObjVal? "transactions"))
        ("imported enum and struct storage entry is not canonical: " ++ identifier)
    let caseFeatures := (← (← saved.getObjVal? "provenance").getObjValAs? (List String) "features").eraseDups
    require (sameMembers (← strings entry "expectedFeatures") caseFeatures)
      ("enum and struct storage corpus features changed: " ++ identifier)
    let history := AdtStorage.observe scenario Solcore.Synthesis.Stateful.StorageExecution.fixtureBindings fuel
    require ((← string history "status") == "complete") ("enum and struct storage corpus history incomplete: " ++ identifier)
    let observed ← history.getObjValAs? (List Json) "transactions"
    let expected ← entry.getObjValAs? (List Json) "expectedHistory"
    require (observed.length == expected.length) ("enum and struct storage expected history length changed: " ++ identifier)
    let mut statuses : List String := []
    for (row, golden) in observed.zip expected do
      let actual := Json.mkObj [("id", ← row.getObjVal? "id"), ("status", ← row.getObjVal? "status"),
        ("output", ← row.getObjVal? "output"), ("committedStorage", ← row.getObjVal? "committedStorage")]
      require (actual == golden)
        ("original Core differs from the slot-map model: " ++ identifier ++ " " ++ actual.compress)
      statuses := statuses ++ [← string row "status"]
    transactionTotal := transactionTotal + observed.length
    features := (features ++ caseFeatures).eraseDups
    inputs := (inputs ++ words ((scenario.transactions.filter (!·.method.reads)).map (·.input))).eraseDups
    covered := (covered ++ coverage scenario statuses).eraseDups
    helperCounts := (helperCounts ++ [scenario.plan.step.helpers.length]).eraseDups
    transactionCounts := (transactionCounts ++ [scenario.transactions.length]).eraseDups
    templateUnion := (templateUnion ++ (← templates saved)).eraseDups
    outcomes := (outcomes ++ statuses).eraseDups
    patterns := (patterns ++ [String.intercalate "," statuses]).eraseDups
  require (requiredFeatures.all features.contains) "enum and struct storage corpus misses a required step feature"
  require (requiredInputs.all inputs.contains) "enum and struct storage corpus misses a boundary input"
  for (dimension, values) in dimensions do
    require (values.all fun value => covered.contains (dimension, value))
      ("enum and struct storage corpus misses a value of " ++ dimension)
  require ([1, 2, 3].all helperCounts.contains && [1, 2, 3].all transactionCounts.contains)
    "enum and struct storage corpus misses a helper or transaction count"
  require ([0, 1, 2, 3].all templateUnion.contains) "enum and struct storage corpus misses a generated template"
  require (["returned", "reverted"].all outcomes.contains && requiredPatterns.all patterns.contains)
    "enum and struct storage corpus misses an observed outcome or completion pattern"
  return Json.mkObj [("profile", toJson "stateful-adt-storage"), ("scenarios", toJson entries.size),
    ("transactions", toJson transactionTotal), ("patterns", toJson patterns),
    ("overwrites", toJson ((covered.filter (·.1 == "AdtOverwrites")).map Prod.snd))]

private def checked {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def rejects {α : Type} (result : Except String α) (reason : String) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError ("invalid enum and struct storage corpus unexpectedly passed: " ++ reason))

def testSourceAdtStorageCorpus : IO Unit := do
  let manifest ← checked (Json.parse (← IO.FS.readFile "scripts/semantic-adt-storage-corpus.json"))
  let summary ← checked (validateManifest manifest)
  let entries ← checked (manifest.getObjValAs? (Array Json) "cases")
  let some first := entries[0]? | throw (IO.userError "missing first enum and struct storage case")
  let some generatedEntry := entries.find? (fun entry => (entry.getObjVal? "generation").isOk) |
    throw (IO.userError "missing generated enum and struct storage case")
  let replace := fun (original changed : Json) => manifest.setObjVal! "cases"
    (.arr (entries.map fun entry => if entry == original then changed else entry))
  let history ← checked (first.getObjValAs? (Array Json) "expectedHistory")
  let row := history[0]!
  let withRow := fun (changed : Json) => replace first (first.setObjVal! "expectedHistory" (.arr (history.set! 0 changed)))
  -- An output, a slot, a stale slot, a missing row and a status are all checked.
  rejects (validateManifest (withRow (row.setObjVal! "output" (toJson ("0x" ++ String.ofList (List.replicate 64 'f'))))))
    "changed output"
  let storage ← checked (row.getObjValAs? (Array Json) "committedStorage")
  let some written := storage.findIdx? fun cell => (cell.getObjValAs? String "value").toOption != some "0"
    | throw (IO.userError "the first row writes no slot")
  let changedValue := if (storage[written]!.getObjValAs? String "value").toOption == some "7" then "8" else "7"
  rejects (validateManifest (withRow (row.setObjVal! "committedStorage"
    (.arr (storage.set! written (storage[written]!.setObjVal! "value" (toJson changedValue))))))) "changed slot"
  rejects (validateManifest (withRow (row.setObjVal! "committedStorage" (.arr storage.pop)))) "dropped slot"
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr history.pop)))) "popped history"
  let generatedHistory ← checked (generatedEntry.getObjValAs? (Array Json) "expectedHistory")
  let flipped := if (generatedHistory[0]!.getObjValAs? String "status").toOption == some "returned" then "reverted" else "returned"
  rejects (validateManifest (replace generatedEntry (generatedEntry.setObjVal! "expectedHistory"
    (.arr (generatedHistory.set! 0 (generatedHistory[0]!.setObjVal! "status" (toJson flipped))))))) "flipped status"
  -- A transaction's variant, the shape and the key base are all checked.
  let transactions ← checked (first.getObjValAs? (Array Json) "transactions")
  rejects (validateManifest (replace first (first.setObjVal! "transactions"
    (.arr (transactions.set! 0 (transactions[0]!.setObjVal! "variant" (toJson 1))))))) "changed variant"
  let plan ← checked (first.getObjVal? "adtStoragePlan")
  let shape ← checked (plan.getObjVal? "shape")
  rejects (validateManifest (replace first (first.setObjVal! "adtStoragePlan"
    (plan.setObjVal! "shape" (shape.setObjVal! "variants" (toJson ["words1", "words0"])))))) "narrowed payload"
  rejects (validateManifest (replace first (first.setObjVal! "adtStoragePlan" (plan.setObjVal! "keyBase" (toJson "5")))))
    "changed key base"
  rejects (validateManifest (replace first (first.setObjVal! "expectedFeatures" (toJson ([] : List String)))))
    "removed features"
  rejects (validateManifest (manifest.setObjVal! "cases" (.arr (entries.push first)))) "duplicated entry"
  for (key, value) in [
      ("profile", toJson "stateful-keccak-loops"), ("templateVersion", toJson "forged"),
      ("cases", .arr #[]), ("requiredInputs", toJson ([] : List String)),
      ("requiredAdtVariantCounts", toJson [2, 3]), ("requiredAdtOverwrites", toJson ["2:0>1"]),
      ("requiredAdtStaleReads", toJson ["getChoice"]), ("requiredHelperCounts", toJson [1, 2]),
      ("requiredCompletionPatterns", toJson (["returned,returned,returned,returned"] : List String))] do
    rejects (validateManifest (manifest.setObjVal! key value)) key
  rejects (validateManifest manifest 0) "no fuel"
  IO.println summary.compress

end Tests.SourceAdtStorageCorpus
end

section
-- leanmerge: from Solcore.Test.SourceAdtStorageGolden
/-! Golden cases for the enum and struct storage profile. Each emitted contract
is written out in full. Every expected row is written out by hand from the
layout: which slot holds a tag, a payload Word `r + o·K` or a record Word, and
which slot keeps a stale Word, with only the additions, the products with
`K` and Horner's rule evaluated here; the mappings' entry slots come from the
independent `Solcore.Abi.V1.Keccak256`. The steps add a known constant `c`, so
a writing method's `r` is its input plus the accumulator plus `c`. The three
shapes cover two, three and four variants, a pair payload, the payload-free
variant first, between others and last, the enum at record positions 0, 1
and 2, both Word types and both keys of a wrapping key base; the sequences
cover every method, overwrites of longer variants by shorter ones and the
reverse, clears, field updates of the enum and of Words, stale payload and
tag Words a later read must ignore, and reverts of a write, an update and a
read. Both original Core and the slot-map model must give each row. -/
set_option autoImplicit false

namespace Tests.SourceAdtStorageGolden

open Lean
open Solcore.Core (Word)
open Solcore.ContractRuntime
open Solcore.Synthesis.Core
open Solcore.Synthesis.Core.AdtStorage (CheckedPlan Method Shape)
open Solcore.Synthesis.Stateful
open Solcore.Synthesis.Stateful.AdtStorageExecution (Transaction)

private def get {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def w (value : Nat) : Word := Word.ofNatModulo value

/-- The step `x ↦ x + c`: aggregate template 0 around the constant scalar. -/
def step (c : Nat) : IO Aggregates.CheckedDAG := do
  let some dag := Aggregates.CheckedDAG.ofParts? [Solcore.Synthesis.Source.Aggregate.template 0 (.word (w c))]
      (.apply (.var 1) (.var 0)) | throw (IO.userError "constant step failed admission")
  return dag

/-- The multiplier, written out. -/
def K : Nat := 0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95

def plus (left right : Nat) : Nat := (left + right) % 2 ^ 256

/-- The Word written at offset `o` of a value written with `r`. -/
def kv (r o : Nat) : Nat := (r + o * K) % 2 ^ 256

/-- Horner's rule with `K` over decoded Words, from zero. -/
def horner (tokens : List Nat) : Nat := tokens.foldl (fun total token => (total * K + token) % 2 ^ 256) 0

/-- Slot `offset` of the entry of `key` in the mapping at slot `base`. -/
def entry (base key offset : Nat) : Nat := ((AdtStorageExecution.entrySlot base (w key)).val + offset) % 2 ^ 256

def maxKey : Nat := 2 ^ 256 - 1

/-- The expected row: status, output Word and every nonzero observed slot. -/
structure Expected where
  status : String
  output : Nat
  slots : List (Nat × Nat)

private def tx (index : Nat) (method : Method) (flags key field variant input : Nat := 0) : Transaction :=
  ⟨"tx-" ++ toString index, method, w flags, w key, field, variant, w input⟩

/-- `None | Some(word)` with the enum first in the record: the accumulator at
slot 0, the enum at 1 and 2, the record at 3 to 6 (its enum at 3 and 4, its
Words at 5 and 6), `c = 5`. -/
def g1Shape : Shape := {variants := [.words 0, .words 1], position := 0, wordType := .word}
def g1Methods : List Method := [.putChoice, .clearChoice, .getChoice, .putRecord, .setRecord, .getRecord]

/-- `Some(7 + K)`, read back; cleared, which leaves the payload at slot 2;
read as `None`; a whole record reverted, then written with `None`; its enum
field updated to `Some`, the Words kept; and the record read. -/
def g1Rows : List (Transaction × Expected) :=
  let read := horner [1, kv 7 1]
  let record := horner [1, kv 13 1, kv 8 2, kv 8 3]
  [ -- r = 2 + 0 + 5: tag one at slot 1, the payload at offset 1.
    (tx 0 .putChoice (variant := 1) (input := 2), ⟨"returned", 7, [(0, 7), (1, 1), (2, kv 7 1)]⟩),
    (tx 1 .getChoice, ⟨"returned", read, [(0, read), (1, 1), (2, kv 7 1)]⟩),
    -- r = 1 + read + 5: tag zero at slot 1; slot 2 keeps its stale payload.
    (tx 2 .clearChoice (input := 1), ⟨"returned", plus read 6, [(0, plus read 6), (2, kv 7 1)]⟩),
    (tx 3 .getChoice, ⟨"returned", 0, [(2, kv 7 1)]⟩),
    -- r = 3 + 0 + 5, reverted with the prior slots.
    (tx 4 .putRecord 1 (variant := 1) (input := 3), ⟨"reverted", 8, [(2, kv 7 1)]⟩),
    -- `ScRecord(None, 8 + 2K, 8 + 3K)`: the enum's tag zero, the Words at offsets 2 and 3.
    (tx 5 .putRecord (variant := 0) (input := 3), ⟨"returned", 8, [(0, 8), (2, kv 7 1), (5, kv 8 2), (6, kv 8 3)]⟩),
    -- r = 0 + 8 + 5: `record.f0 = Some(13 + K)` at slots 3 and 4; slots 5 and 6 kept.
    (tx 6 .setRecord (field := 0) (variant := 1), ⟨"returned", 13,
      [(0, 13), (2, kv 7 1), (3, 1), (4, kv 13 1), (5, kv 8 2), (6, kv 8 3)]⟩),
    (tx 7 .getRecord, ⟨"returned", record, [(0, record), (2, kv 7 1), (3, 1), (4, kv 13 1), (5, kv 8 2), (6, kv 8 3)]⟩)]

/-- `V0(ScPair) | V1 | V2(uint256, uint256)` with the enum last in the record:
the enum at 1 to 4, the record at 5 to 10 (its Words at 5 and 6, its enum at 7
to 10), `choices` at 11 and `records` at 12, keys `2^256 - 1` and 0, `c = 3`. -/
def g2Shape : Shape := {variants := [.pair, .words 0, .words 2], position := 2, wordType := .uint256}
def g2Methods : List Method := [.putChoiceAt, .clearChoiceAt, .getChoiceAt, .putRecordAt, .setRecordAt, .getRecordAt]

/-- A pair at the top key and the last variant at key 0, each at its payload
offset; the top key cleared to the middle variant, which leaves the pair's
second Word; read; a record at key 0 with a pair, whose enum field is updated
to the last variant through the entry's read-modify-write; an update of its
first Word reverted; and the record read. -/
def g2Rows : List (Transaction × Expected) :=
  let top := fun offset => entry 11 maxKey offset
  let zero := fun offset => entry 11 0 offset
  let record := fun offset => entry 12 0 offset
  let choices := [(zero 0, 1), (zero 1, 1), (zero 2, kv 9 2), (zero 3, kv 9 3)]
  let cleared := [(top 0, 1), (top 2, kv 4 2)] ++ choices
  let digest := horner [9, kv 9 1, 2, kv 12 4, kv 12 5]
  let updated := [(record 0, 9), (record 1, kv 9 1), (record 2, 1), (record 3, 1), (record 4, kv 12 4), (record 5, kv 12 5)]
  [ -- r = 1 + 0 + 3: tag zero, the pair at offsets 1 and 2.
    (tx 0 .putChoiceAt (key := maxKey) (variant := 0) (input := 1), ⟨"returned", 4, [(0, 4), (top 1, kv 4 1), (top 2, kv 4 2)]⟩),
    -- r = 2 + 4 + 3: tags one and one, the payload at offsets 2 and 3.
    (tx 1 .putChoiceAt (key := 0) (variant := 2) (input := 2), ⟨"returned", 9,
      [(0, 9), (top 1, kv 4 1), (top 2, kv 4 2)] ++ choices⟩),
    -- r = 0 + 9 + 3: tags one and zero over the pair's tag and first Word.
    (tx 2 .clearChoiceAt (key := maxKey), ⟨"returned", 12, [(0, 12)] ++ cleared⟩),
    (tx 3 .getChoiceAt (key := maxKey), ⟨"returned", 1, [(0, 1)] ++ cleared⟩),
    -- r = 5 + 1 + 3: `ScRecord(9, 9 + K, V0(ScPair(9 + 3K, 9 + 4K)))`.
    (tx 4 .putRecordAt (key := 0) (variant := 0) (input := 5), ⟨"returned", 9,
      [(0, 9)] ++ cleared ++ [(record 0, 9), (record 1, kv 9 1), (record 3, kv 9 3), (record 4, kv 9 4)]⟩),
    -- r = 0 + 9 + 3: the last variant's tags over the pair's tag and first
    -- Word, its payload at record offsets 4 and 5; the Words kept.
    (tx 5 .setRecordAt (key := 0) (field := 2) (variant := 2), ⟨"returned", 12, [(0, 12)] ++ cleared ++ updated⟩),
    -- r = 7 + 12 + 3, reverted with the prior slots.
    (tx 6 .setRecordAt 1 (key := 0) (field := 0) (input := 7), ⟨"reverted", 22, [(0, 12)] ++ cleared ++ updated⟩),
    (tx 7 .getRecordAt (key := 0), ⟨"returned", digest, [(0, digest)] ++ cleared ++ updated⟩)]

/-- `V0(word) | V1 | V2 | V3(word)` with the enum between the record's Words:
the enum at 1 to 4, the record at 5 to 10 (its first Word at 5, its enum at 6
to 9, its last Word at 10), `records` at 12, keys 1 and 2, `c = 1`. -/
def g3Shape : Shape := {variants := [.words 1, .words 0, .words 0, .words 1], position := 1, wordType := .word}
def g3Methods : List Method := [.putChoice, .getChoice, .putRecordAt, .setRecord, .getRecordAt]

/-- The last variant's three tags and payload; the first variant over it,
which leaves the third tag and the last payload; read; the third variant,
whose zero tag at level two the read must reach; that read reverted; a record
at key 2 with the last variant; read; and the record field's last Word
updated. -/
def g3Rows : List (Transaction × Expected) :=
  let first := kv 2 1
  let third := plus first 1
  let r5 := plus first 6
  let entryRow := fun offset => entry 12 2 offset
  let record := horner [r5, 3, kv r5 4, kv r5 5]
  let r7 := plus record 2
  let written := [(entryRow 0, r5), (entryRow 1, 1), (entryRow 2, 1), (entryRow 3, 1), (entryRow 4, kv r5 4),
    (entryRow 5, kv r5 5)]
  [ -- r = 0 + 0 + 1: tags one at slots 1 to 3, the payload at offset 3.
    (tx 0 .putChoice (variant := 3), ⟨"returned", 1, [(0, 1), (1, 1), (2, 1), (3, 1), (4, kv 1 3)]⟩),
    -- r = 0 + 1 + 1: tag zero at slot 1, the payload at offset 1 over a tag.
    (tx 1 .putChoice (variant := 0), ⟨"returned", 2, [(0, 2), (2, first), (3, 1), (4, kv 1 3)]⟩),
    (tx 2 .getChoice, ⟨"returned", first, [(0, first), (2, first), (3, 1), (4, kv 1 3)]⟩),
    -- r = 0 + first + 1: tags one, one and zero; slot 4 keeps its payload.
    (tx 3 .putChoice (variant := 2), ⟨"returned", third, [(0, third), (1, 1), (2, 1), (4, kv 1 3)]⟩),
    (tx 4 .getChoice 1, ⟨"reverted", 2, [(0, third), (1, 1), (2, 1), (4, kv 1 3)]⟩),
    -- r = 4 + third + 1: `ScRecord(r, V3(r + 4K), r + 5K)` at key 2.
    (tx 5 .putRecordAt (key := 2) (variant := 3) (input := 4), ⟨"returned", r5,
      [(0, r5), (1, 1), (2, 1), (4, kv 1 3)] ++ written⟩),
    (tx 6 .getRecordAt (key := 2), ⟨"returned", record, [(0, record), (1, 1), (2, 1), (4, kv 1 3)] ++ written⟩),
    -- r = 1 + record + 1: `record.f2` at offset 5, slot 10.
    (tx 7 .setRecord (field := 2) (input := 1), ⟨"returned", r7,
      [(0, r7), (1, 1), (2, 1), (4, kv 1 3)] ++ written ++ [(10, kv r7 5)]⟩)]

private def wordText (value : Nat) : String := encodeBytesText (encodeWordBytesBE (w value))

private def valueAt (expected : Expected) (slot : Word) : Nat :=
  ((expected.slots.find? fun (candidate, _) => w candidate == slot).map Prod.snd).getD 0

private def storageJson (slots : List Word) (expected : Expected) : Json :=
  toJson (slots.map fun slot => Json.mkObj [
    ("slot", toJson (toString slot.val)), ("value", toJson (toString (valueAt expected slot)))])

def check (name : String) (slots : List Word) (row : Json) (model : AdtStorageExecution.ModelRow)
    (expected : Expected) : IO Unit := do
  ensure (expected.slots.all fun (slot, value) => value != 0 && slots.contains (w slot))
    s!"{name}: an expected slot is zero or not observed"
  ensure ((row.getObjValAs? String "status").toOption == some expected.status &&
      (row.getObjValAs? String "output").toOption == some (wordText expected.output) &&
      (row.getObjVal? "committedStorage").toOption == some (storageJson slots expected))
    s!"{name}: original Core differs from the expected row {row.compress}"
  ensure (model.reverted == (expected.status == "reverted") && model.result == w expected.output &&
      AdtStorageExecution.modelSlots model slots == slots.map (fun slot => w (valueAt expected slot)))
    s!"{name}: the slot-map model differs from the expected row"

/-- Each golden sequence's name, shape, methods, key base, step constant and rows. -/
def goldenPlans : List (String × Shape × List Method × Nat × Nat × List (Transaction × Expected)) := [
  ("two variants", g1Shape, g1Methods, maxKey, 5, g1Rows),
  ("three variants", g2Shape, g2Methods, maxKey, 3, g2Rows),
  ("four variants", g3Shape, g3Methods, 1, 1, g3Rows)]

/-- The emitted contract of the first shape with its six field methods and
`c = 5`, written out. -/
def g1Source : String := "import * from std;
import * from std.dispatch;
import * from std.Generic;
import * from std.StorageGeneric;
import {mstore, revert_} from std.opcodes;

enum ScChoice {
    V0,
    V1(word)
}

struct ScRecord {
    f0: ScChoice;
    f1: word;
    f2: word;
}

function sc_fn0(sc_arg: word) returns (word) {
    let sc_v0: word = 5;
    let sc_v1: word = sc_v0;
    let sc_c2: word = sc_arg;
    let sc_v3: word = sc_c2;
    sc_c2 = sc_v1;
    let sc_v4: word = sc_c2;
    let sc_v5: (word, word) = (sc_v3, sc_v4);
    let sc_v6: (word, word) = sc_v5;
    let sc_v7: word = 0;
    match (sc_v6) {
        case (sc_p8, sc_p9) {
            sc_v7 = sc_p8;
        }
    }
    let sc_v10: word = 0;
    match (sc_v6) {
        case (sc_p11, sc_p12) {
            sc_v10 = sc_p12;
        }
    }
    let sc_v13: word = (sc_v7 + sc_v10);
    return sc_v13;
}

function sc_step(sc_arg: word) returns (word) {
    let sc_v0: word = sc_fn0(sc_arg);
    return sc_v0;
}

contract SynthesizedAdtStorage {
    acc: word;
    choice: ScChoice;
    record: ScRecord;
    choices: mapping(word => ScChoice);
    records: mapping(word => ScRecord);

    function putChoice(flags: uint256, variant: uint256, input: uint256) public returns (uint256) {
        let sc_flags: word = Typedef.rep(flags);
        let sc_variant: word = Typedef.rep(variant);
        let sc_r: word = sc_step((Typedef.rep(input) + acc));
        if (sc_variant == 0) {
            choice = ScChoice.V0;
        } else {
            choice = ScChoice.V1((sc_r + 0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95));
        }
        acc = sc_r;
        if ((sc_flags & 1) == 1) {
            mstore(0, sc_r);
            revert_(0, 32);
        }
        return uint256(sc_r);
    }

    function clearChoice(flags: uint256, input: uint256) public returns (uint256) {
        let sc_flags: word = Typedef.rep(flags);
        let sc_r: word = sc_step((Typedef.rep(input) + acc));
        choice = ScChoice.V0;
        acc = sc_r;
        if ((sc_flags & 1) == 1) {
            mstore(0, sc_r);
            revert_(0, 32);
        }
        return uint256(sc_r);
    }

    function getChoice(flags: uint256) public returns (uint256) {
        let sc_flags: word = Typedef.rep(flags);
        let sc_digest: word = 0;
        match (choice) {
            case ScChoice.V0 {
                sc_digest = 0;
            }
            case ScChoice.V1(sc_a0) {
                sc_digest = ((1 * 0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95) + sc_a0);
            }
        }
        acc = sc_digest;
        if ((sc_flags & 1) == 1) {
            mstore(0, sc_digest);
            revert_(0, 32);
        }
        return uint256(sc_digest);
    }

    function putRecord(flags: uint256, variant: uint256, input: uint256) public returns (uint256) {
        let sc_flags: word = Typedef.rep(flags);
        let sc_variant: word = Typedef.rep(variant);
        let sc_r: word = sc_step((Typedef.rep(input) + acc));
        if (sc_variant == 0) {
            record = ScRecord(ScChoice.V0, (sc_r + 0x3c6ef372fe94f82be73980c0b9db906821044ed7e744e4a3f0d8d423a1831d2a), (sc_r + 0xdaa66d2c7ddf7441dad6412116c9589c31867643dae756f5e9453e357244abbf));
        } else {
            record = ScRecord(ScChoice.V1((sc_r + 0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95)), (sc_r + 0x3c6ef372fe94f82be73980c0b9db906821044ed7e744e4a3f0d8d423a1831d2a), (sc_r + 0xdaa66d2c7ddf7441dad6412116c9589c31867643dae756f5e9453e357244abbf));
        }
        acc = sc_r;
        if ((sc_flags & 1) == 1) {
            mstore(0, sc_r);
            revert_(0, 32);
        }
        return uint256(sc_r);
    }

    function setRecord(flags: uint256, field: uint256, variant: uint256, input: uint256) public returns (uint256) {
        let sc_flags: word = Typedef.rep(flags);
        let sc_field: word = Typedef.rep(field);
        let sc_variant: word = Typedef.rep(variant);
        let sc_r: word = sc_step((Typedef.rep(input) + acc));
        if (sc_field == 0) {
            if (sc_variant == 0) {
                record.f0 = ScChoice.V0;
            } else {
                record.f0 = ScChoice.V1((sc_r + 0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95));
            }
        } else {
            if (sc_field == 1) {
                record.f1 = (sc_r + 0x3c6ef372fe94f82be73980c0b9db906821044ed7e744e4a3f0d8d423a1831d2a);
            } else {
                record.f2 = (sc_r + 0xdaa66d2c7ddf7441dad6412116c9589c31867643dae756f5e9453e357244abbf);
            }
        }
        acc = sc_r;
        if ((sc_flags & 1) == 1) {
            mstore(0, sc_r);
            revert_(0, 32);
        }
        return uint256(sc_r);
    }

    function getRecord(flags: uint256) public returns (uint256) {
        let sc_flags: word = Typedef.rep(flags);
        let sc_digest: word = 0;
        match (record) {
            case ScRecord(ScChoice.V0, sc_x1, sc_x2) {
                sc_digest = ((((0 * 0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95) + sc_x1) * 0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95) + sc_x2);
            }
            case ScRecord(ScChoice.V1(sc_a0), sc_x1, sc_x2) {
                sc_digest = ((((((1 * 0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95) + sc_a0) * 0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95) + sc_x1) * 0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95) + sc_x2);
            }
        }
        acc = sc_digest;
        if ((sc_flags & 1) == 1) {
            mstore(0, sc_digest);
            revert_(0, 32);
        }
        return uint256(sc_digest);
    }
}
"

/-- The emitted contract of the second shape with its six keyed methods and
`c = 5`, written out. -/
def g2Source : String := "import * from std;
import * from std.dispatch;
import * from std.Generic;
import * from std.StorageGeneric;
import {mstore, revert_} from std.opcodes;

struct ScPair {
    a: uint256;
    b: uint256;
}

enum ScChoice {
    V0(ScPair),
    V1,
    V2(uint256, uint256)
}

struct ScRecord {
    f0: uint256;
    f1: uint256;
    f2: ScChoice;
}

function sc_fn0(sc_arg: word) returns (word) {
    let sc_v0: word = 5;
    let sc_v1: word = sc_v0;
    let sc_c2: word = sc_arg;
    let sc_v3: word = sc_c2;
    sc_c2 = sc_v1;
    let sc_v4: word = sc_c2;
    let sc_v5: (word, word) = (sc_v3, sc_v4);
    let sc_v6: (word, word) = sc_v5;
    let sc_v7: word = 0;
    match (sc_v6) {
        case (sc_p8, sc_p9) {
            sc_v7 = sc_p8;
        }
    }
    let sc_v10: word = 0;
    match (sc_v6) {
        case (sc_p11, sc_p12) {
            sc_v10 = sc_p12;
        }
    }
    let sc_v13: word = (sc_v7 + sc_v10);
    return sc_v13;
}

function sc_step(sc_arg: word) returns (word) {
    let sc_v0: word = sc_fn0(sc_arg);
    return sc_v0;
}

contract SynthesizedAdtStorage {
    acc: word;
    choice: ScChoice;
    record: ScRecord;
    choices: mapping(word => ScChoice);
    records: mapping(word => ScRecord);

    function putChoiceAt(flags: uint256, key: uint256, variant: uint256, input: uint256) public returns (uint256) {
        let sc_flags: word = Typedef.rep(flags);
        let sc_key: word = Typedef.rep(key);
        let sc_variant: word = Typedef.rep(variant);
        let sc_r: word = sc_step((Typedef.rep(input) + acc));
        if (sc_variant == 0) {
            choices[sc_key] = ScChoice.V0(ScPair(uint256((sc_r + 0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95)), uint256((sc_r + 0x3c6ef372fe94f82be73980c0b9db906821044ed7e744e4a3f0d8d423a1831d2a))));
        } else {
            if (sc_variant == 1) {
                choices[sc_key] = ScChoice.V1;
            } else {
                choices[sc_key] = ScChoice.V2(uint256((sc_r + 0x3c6ef372fe94f82be73980c0b9db906821044ed7e744e4a3f0d8d423a1831d2a)), uint256((sc_r + 0xdaa66d2c7ddf7441dad6412116c9589c31867643dae756f5e9453e357244abbf)));
            }
        }
        acc = sc_r;
        if ((sc_flags & 1) == 1) {
            mstore(0, sc_r);
            revert_(0, 32);
        }
        return uint256(sc_r);
    }

    function clearChoiceAt(flags: uint256, key: uint256, input: uint256) public returns (uint256) {
        let sc_flags: word = Typedef.rep(flags);
        let sc_key: word = Typedef.rep(key);
        let sc_r: word = sc_step((Typedef.rep(input) + acc));
        choices[sc_key] = ScChoice.V1;
        acc = sc_r;
        if ((sc_flags & 1) == 1) {
            mstore(0, sc_r);
            revert_(0, 32);
        }
        return uint256(sc_r);
    }

    function getChoiceAt(flags: uint256, key: uint256) public returns (uint256) {
        let sc_flags: word = Typedef.rep(flags);
        let sc_key: word = Typedef.rep(key);
        let sc_digest: word = 0;
        match (choices[sc_key]) {
            case ScChoice.V0(ScPair(sc_a0, sc_a1)) {
                sc_digest = ((((0 * 0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95) + Typedef.rep(sc_a0)) * 0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95) + Typedef.rep(sc_a1));
            }
            case ScChoice.V1 {
                sc_digest = 1;
            }
            case ScChoice.V2(sc_a0, sc_a1) {
                sc_digest = ((((2 * 0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95) + Typedef.rep(sc_a0)) * 0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95) + Typedef.rep(sc_a1));
            }
        }
        acc = sc_digest;
        if ((sc_flags & 1) == 1) {
            mstore(0, sc_digest);
            revert_(0, 32);
        }
        return uint256(sc_digest);
    }

    function putRecordAt(flags: uint256, key: uint256, variant: uint256, input: uint256) public returns (uint256) {
        let sc_flags: word = Typedef.rep(flags);
        let sc_key: word = Typedef.rep(key);
        let sc_variant: word = Typedef.rep(variant);
        let sc_r: word = sc_step((Typedef.rep(input) + acc));
        if (sc_variant == 0) {
            records[sc_key] = ScRecord(uint256(sc_r), uint256((sc_r + 0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95)), ScChoice.V0(ScPair(uint256((sc_r + 0xdaa66d2c7ddf7441dad6412116c9589c31867643dae756f5e9453e357244abbf)), uint256((sc_r + 0x78dde6e5fd29f057ce73018173b720d042089dafce89c947e1b1a84743063a54)))));
        } else {
            if (sc_variant == 1) {
                records[sc_key] = ScRecord(uint256(sc_r), uint256((sc_r + 0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95)), ScChoice.V1);
            } else {
                records[sc_key] = ScRecord(uint256(sc_r), uint256((sc_r + 0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95)), ScChoice.V2(uint256((sc_r + 0x78dde6e5fd29f057ce73018173b720d042089dafce89c947e1b1a84743063a54)), uint256((sc_r + 0x1715609f7c746c6dc20fc1e1d0a4e904528ac51bc22c3b99da1e125913c7c8e9))));
            }
        }
        acc = sc_r;
        if ((sc_flags & 1) == 1) {
            mstore(0, sc_r);
            revert_(0, 32);
        }
        return uint256(sc_r);
    }

    function setRecordAt(flags: uint256, key: uint256, field: uint256, variant: uint256, input: uint256) public returns (uint256) {
        let sc_flags: word = Typedef.rep(flags);
        let sc_key: word = Typedef.rep(key);
        let sc_field: word = Typedef.rep(field);
        let sc_variant: word = Typedef.rep(variant);
        let sc_r: word = sc_step((Typedef.rep(input) + acc));
        match (records[sc_key]) {
            case ScRecord(sc_x0, sc_x1, sc_x2) {
                if (sc_field == 0) {
                    records[sc_key] = ScRecord(uint256(sc_r), sc_x1, sc_x2);
                } else {
                    if (sc_field == 1) {
                        records[sc_key] = ScRecord(sc_x0, uint256((sc_r + 0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95)), sc_x2);
                    } else {
                        if (sc_variant == 0) {
                            records[sc_key] = ScRecord(sc_x0, sc_x1, ScChoice.V0(ScPair(uint256((sc_r + 0xdaa66d2c7ddf7441dad6412116c9589c31867643dae756f5e9453e357244abbf)), uint256((sc_r + 0x78dde6e5fd29f057ce73018173b720d042089dafce89c947e1b1a84743063a54)))));
                        } else {
                            if (sc_variant == 1) {
                                records[sc_key] = ScRecord(sc_x0, sc_x1, ScChoice.V1);
                            } else {
                                records[sc_key] = ScRecord(sc_x0, sc_x1, ScChoice.V2(uint256((sc_r + 0x78dde6e5fd29f057ce73018173b720d042089dafce89c947e1b1a84743063a54)), uint256((sc_r + 0x1715609f7c746c6dc20fc1e1d0a4e904528ac51bc22c3b99da1e125913c7c8e9))));
                            }
                        }
                    }
                }
            }
        }
        acc = sc_r;
        if ((sc_flags & 1) == 1) {
            mstore(0, sc_r);
            revert_(0, 32);
        }
        return uint256(sc_r);
    }

    function getRecordAt(flags: uint256, key: uint256) public returns (uint256) {
        let sc_flags: word = Typedef.rep(flags);
        let sc_key: word = Typedef.rep(key);
        let sc_digest: word = 0;
        match (records[sc_key]) {
            case ScRecord(sc_x0, sc_x1, ScChoice.V0(ScPair(sc_a0, sc_a1))) {
                sc_digest = ((((((((Typedef.rep(sc_x0) * 0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95) + Typedef.rep(sc_x1)) * 0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95) + 0) * 0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95) + Typedef.rep(sc_a0)) * 0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95) + Typedef.rep(sc_a1));
            }
            case ScRecord(sc_x0, sc_x1, ScChoice.V1) {
                sc_digest = ((((Typedef.rep(sc_x0) * 0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95) + Typedef.rep(sc_x1)) * 0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95) + 1);
            }
            case ScRecord(sc_x0, sc_x1, ScChoice.V2(sc_a0, sc_a1)) {
                sc_digest = ((((((((Typedef.rep(sc_x0) * 0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95) + Typedef.rep(sc_x1)) * 0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95) + 2) * 0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95) + Typedef.rep(sc_a0)) * 0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95) + Typedef.rep(sc_a1));
            }
        }
        acc = sc_digest;
        if ((sc_flags & 1) == 1) {
            mstore(0, sc_digest);
            revert_(0, 32);
        }
        return uint256(sc_digest);
    }
}
"

def testSourceAdtStorageGolden : IO Unit := do
  let fuel := 1000000
  let five ← step 5
  for (name, shape, methods, expected) in [("two variants", g1Shape, g1Methods, g1Source),
      ("three variants", g2Shape, g2Methods, g2Source)] do
    let some plan := CheckedPlan.ofParts? shape methods (w maxKey) five
      | throw (IO.userError s!"{name}: the contract failed admission")
    let emitted ← get (Solcore.Synthesis.Source.AdtStorage.emitted plan)
    ensure (emitted.source == expected) s!"{name}: the emitted contract differs from the hand-written text"
  for (name, shape, methods, keyBase, constant, rows) in goldenPlans do
    let some plan := CheckedPlan.ofParts? shape methods (w keyBase) (← step constant)
      | throw (IO.userError s!"{name}: the contract failed admission")
    let transactions := rows.map Prod.fst
    ensure (transactions.all (·.valid plan)) s!"{name}: a transaction lies outside the plan"
    let slots := AdtStorageExecution.planSlots plan
    let history := AdtStorageExecution.observe plan transactions StorageExecution.fixtureBindings fuel
    ensure ((history.getObjValAs? String "status").toOption == some "complete") s!"{name}: the history is incomplete"
    let observed ← get (history.getObjValAs? (Array Json) "transactions")
    let some modelled := AdtStorageExecution.model plan fuel transactions
      | throw (IO.userError s!"{name}: the slot-map model failed")
    ensure (observed.size == rows.length && modelled.length == rows.length) s!"{name}: a row is missing"
    for ((row, model), (transaction, expected)) in (observed.toList.zip modelled).zip rows do
      check s!"{name} {transaction.id}" slots row model expected
  -- A changed expectation fails: one payload Word off by one.
  let some plan := CheckedPlan.ofParts? g1Shape g1Methods (w maxKey) five | throw (IO.userError "admission")
  let transaction := (g1Rows.head?.map Prod.fst).getD (tx 0 .getChoice)
  let history := AdtStorageExecution.observe plan [transaction] StorageExecution.fixtureBindings fuel
  let rows ← get (history.getObjValAs? (Array Json) "transactions")
  let some modelled := AdtStorageExecution.model plan fuel [transaction] | throw (IO.userError "model")
  let changed : Expected := ⟨"returned", 7, [(0, 7), (1, 1), (2, plus (kv 7 1) 1)]⟩
  let (some row, some model) := (rows[0]?, modelled[0]?) | throw (IO.userError "no row")
  let failed ← tryCatch (do
      check "changed" (AdtStorageExecution.planSlots plan) row model changed
      pure false) (fun _ => pure true)
  ensure failed "a changed expectation passed"

end Tests.SourceAdtStorageGolden
end

section
-- leanmerge: from Solcore.Test.SourceKeyedStorageCases
/-! Keyed-storage case regressions: exact replay, bounded generation from an
independent sequence stream, canonical transaction/slot boundaries and typed
scenario reductions over steps, transactions, inputs and keys. Expected values
here are test goldens only; emitted cases and the observer never consume them. -/
set_option autoImplicit false

namespace Tests.SourceKeyedStorageCases
open Lean Solcore.Core Solcore.Synthesis.Core Solcore.Synthesis.Source
open Solcore.Synthesis.Core.KeyedStorage (CheckedPlan)
open Solcore.Synthesis.Stateful.KeyedStorageExecution (Transaction Bindings)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def get {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)
private def rejected {α : Type} (result : Except String α) (message : String) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError message)
private def field (value : Json) (name : String) : IO Json := get (value.getObjVal? name)
private def string (value : Json) (name : String) : IO String := get (value.getObjValAs? String name)
private def natural (value : Json) (name : String) : IO Nat := get (value.getObjValAs? Nat name)
private def rows (value : Json) (name : String := "transactions") : IO (Array Json) :=
  get (value.getObjValAs? (Array Json) name)
private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)
private def entry : Wire.Expr := .apply (.var 1) (.var 0)
private def bindings : Bindings := ⟨⟨17, by decide⟩, ⟨101, by decide⟩⟩

private def makePlan (body : Wire.Expr) (result : Wire.Expr := entry) : IO CheckedPlan := do
  let some graph := Aggregates.CheckedDAG.ofParts? [body] result |
    throw (IO.userError "keyed fixture failed step admission")
  let some plan := CheckedPlan.ofStep? graph | throw (IO.userError "keyed wrapper failed host admission")
  return plan
private def transactions (values : List (Nat × Nat)) : List Transaction :=
  values.zipIdx.map fun ((key, input), index) =>
    ⟨"call-" ++ toString index, Word.ofNatModulo key, Word.ofNatModulo input⟩
private def scenario (plan : CheckedPlan) (values : List (Nat × Nat)) : IO KeyedStorage.CheckedScenario :=
  get (KeyedStorage.checkedScenario plan (transactions values))
private def imported (value : KeyedStorage.CheckedScenario) (fuel : Nat := 10000) : IO Json :=
  get (KeyedStorage.emitCase value (Json.mkObj [("kind", toJson "imported")]) fuel)

private def referenceChecks : IO Json := do
  let identity ← makePlan (.var 0)
  let value ← scenario identity [(5, 2), (0, 4), (2 ^ 256 - 1, 3)]
  let saved ← imported value
  ensure ((← field saved "observedSlots") == toJson (["0", "1", "5", "6", toString (2 ^ 256 - 1)] : List String))
    "case did not declare the derived observed slots"
  ensure ((← get (KeyedStorage.replayCase saved 10000)) == saved) "imported keyed case did not replay"
  ensure ((← get (KeyedStorage.replayCase (saved.setObjVal! "directCore" (toJson "forged")) 10000)) == saved)
    "keyed replay consumed a stored expected result"
  let changed ← imported (← scenario identity [(1, 2), (2 ^ 255, 3)])
  ensure ((← field saved "program") == (← field changed "program") &&
    (← string saved "source") == (← string changed "source"))
    "keys or inputs were substituted into source or Core code"
  let observed := KeyedStorage.observe value bindings 10000
  ensure ((← string observed "status") == "complete" &&
    ((← rows observed).map fun row => (row.getObjValAs? String "status").toOption) ==
      #[some "returned", some "returned", some "reverted"])
    "keyed scenario did not follow its input parities"
  let rebound ← rows (KeyedStorage.observe value ⟨⟨33, by decide⟩, ⟨202, by decide⟩⟩ 10000)
  ensure (rebound.map Solcore.Synthesis.Stateful.AccountStorage.unbound == (← rows observed).map Solcore.Synthesis.Stateful.AccountStorage.unbound &&
      rebound.all (Solcore.Synthesis.Stateful.AccountStorage.boundTo · [202]))
    "address-independent keyed profile changed with bindings"
  -- The maximum key's wrapping successor is both the counter and another key.
  ensure (KeyedStorage.aliases value.transactions == ["key-counter", "successor-counter", "successor-key"] &&
    KeyedStorage.aliases (transactions [(7, 0), (8, 0), (7, 0)]) == ["repeated-key", "successor-key"] &&
    KeyedStorage.aliases (transactions [(3, 0)]) == [])
    "static alias inventory changed"
  return saved

private def generationChecks : IO Json := do
  for seed in List.range 8 do
    let choices := KeyedStorage.sequenceChoices (Seed.ofNat seed)
    ensure (choices.length == 7 && (choices.take 6).all (· < 6) && choices.getD 6 0 < 4)
      "sequence choices escaped their banks"
    match KeyedStorage.generatedScenario (Seed.ofNat seed) 384 with
    | .error _ => pure ()
    | .ok (value, origin) =>
        ensure (value.transactions.length == 3 && Wire.programNodes value.program ≤ 384 &&
          value.plan.step.helpers.length == 1 + seed % 3) "keyed recipe lost node/transaction/helper bounds"
        ensure (value.transactions.all (fun tx => KeyedStorage.keyBank.contains tx.key)) "generated key escaped its bank"
        ensure ((value.transactions.map fun tx => tx.input.val % 2 == 1) == KeyedStorage.generatedParities (Seed.ofNat seed))
          "generated inputs lost their prescribed parities"
        ensure ((origin.getObjValAs? (List Nat) "sequenceChoices").toOption == some choices)
          "generated origin lost its sequence choices"
  rejected (KeyedStorage.generatedScenario (Seed.ofNat 0) 513) "oversized node budget accepted"
  rejected (KeyedStorage.generatedScenario (Seed.ofNat 0) KeyedStorage.programOverhead) "undersized node budget accepted"
  let corpus := KeyedStorage.generateCases (Seed.ofNat 0) 384 4 512 10000
  ensure (corpus == KeyedStorage.generateCases (Seed.ofNat 0) 384 4 512 10000) "keyed generation nondeterministic"
  let generated ← rows corpus "cases"
  ensure (generated.size == 4 && (← natural corpus "attempted") ≤ 512 && (← string corpus "status") == "complete")
    "keyed count does not count complete scenarios"
  for saved in generated do
    ensure ((← get (KeyedStorage.replayCase saved 10000)) == saved) "generated keyed provenance did not replay"
    let low ← get (KeyedStorage.replayCase saved 0)
    ensure ((← natural low "executionFuel") == 0 && (← field low "provenance") == (← field saved "provenance"))
      "fresh replay fuel changed the generation validation budget"
  let saved := generated[0]!
  let origin ← field (← field saved "provenance") "origin"
  let some seed := (← string origin "seed").toNat? | throw (IO.userError "invalid generated seed")
  let low := KeyedStorage.generateCases (Seed.ofNat seed) 384 1 1 0
  let excluded ← rows low "excluded"
  ensure ((← rows low "cases").isEmpty && (← string excluded[0]! "category") == "inconclusive-resource")
    "keyed generation resource exhaustion was not distinguished"
  ensure ((← rows (KeyedStorage.generateCases (Seed.ofNat seed) 384 2 1 10000) "cases").size == 1 &&
    (← natural (KeyedStorage.generateCases (Seed.ofNat seed) 384 0 10 10000) "attempted") == 0 &&
    (← rows (KeyedStorage.generateCases (Seed.ofNat seed) 384 1 0 10000) "cases").isEmpty)
    "keyed generator ignored count/attempt bounds"
  return saved

private def tamperingChecks (saved generated : Json) : IO Unit := do
  let first := (← rows saved)[0]!
  for (name, bad) in [("id", toJson ""), ("id", toJson "not valid"), ("key", toJson "05"),
      ("key", toJson (toString (2 ^ 256))), ("key", toJson "6"), ("input", toJson "01"), ("input", toJson "7"),
      ("calldata", toJson "0x"), ("value", toJson "1"), ("extra", toJson true)] do
    rejected (KeyedStorage.decodeTransactions (toJson [first.setObjVal! name bad]))
      "noncanonical keyed transaction accepted"
  rejected (KeyedStorage.decodeTransactions (toJson [first, first])) "duplicate transaction IDs accepted"
  rejected (KeyedStorage.decodeTransactions (toJson ([] : List Json))) "empty transaction list accepted"
  rejected (KeyedStorage.decodeTransactions
    (toJson (List.replicate (Solcore.Synthesis.Stateful.Sequence.maxTransactions + 1) first)))
    "unbounded transaction count accepted"
  for (name, bad) in [("initialState", Json.mkObj [("storage", toJson [first])]),
      ("observedSlots", toJson (["0", "1"] : List String)),
      ("observedSlots", toJson (["1", "0", "5", "6", toString (2 ^ 256 - 1)] : List String)),
      ("executionFuel", toJson (10000001 : Nat)), ("keyedStoragePlan", Json.null),
      ("program", Wire.encodeProgram {resultType := .word, dataDefinitions := [], body := word 0})] do
    rejected (KeyedStorage.caseProgram (saved.setObjVal! name bad)) "invalid keyed case boundary accepted"
  let provenance ← field generated "provenance"
  let origin ← field provenance "origin"
  let withOrigin := fun changed => generated.setObjVal! "provenance" (provenance.setObjVal! "origin" changed)
  for name in ["generatorVersion", "profileVersion", "functionVersion", "templateVersion", "stepProfileVersion",
      "stepFunctionVersion", "stepTemplateVersion", "emitterVersion", "wrapperVersion", "features"] do
    rejected (KeyedStorage.replayCase (generated.setObjVal! "provenance" (provenance.setObjVal! name Json.null)) 10000)
      "tampered keyed provenance accepted"
  for (name, bad) in [("seed", toJson "00"), ("finalSeed", toJson "bad"),
      ("maxProgramNodes", toJson (513 : Nat)), ("stepOrigin", Json.null), ("sequenceChoices", Json.null),
      ("sequenceCompletions", Json.null), ("validationFuel", toJson (10000001 : Nat)), ("validationFuel", toJson (0 : Nat))] do
    rejected (KeyedStorage.replayCase (withOrigin (origin.setObjVal! name bad)) 10000)
      "tampered generated keyed recipe accepted"
  let plan ← field saved "keyedStoragePlan"
  rejected (KeyedStorage.checkedPlan (plan.setObjVal! "extra" Json.null)) "noncanonical keyed plan accepted"
  rejected (KeyedStorage.checkedPlan (plan.setObjVal! "schema" (toJson "solcore-lean.storage-plan.v1")))
    "two-slot plan schema accepted as a keyed plan"
  rejected (KeyedStorage.replayCase (saved.setObjVal! "source" (toJson "stale")) 10000) "stale source accepted"
  let contract ← field saved "contract"
  rejected (KeyedStorage.replayCase (saved.setObjVal! "contract" (contract.setObjVal! "selector" (toJson "0xa444f5e9"))) 10000)
    "single-Word storage selector accepted for the keyed ABI"
  rejected (KeyedStorage.replayCase (saved.setObjVal! "schema" (toJson "solcore-lean.semantic-storage-case.v1")) 10000)
    "two-slot case schema accepted by the keyed tool"

private def shrinkChecks : IO Unit := do
  let plan ← makePlan (Aggregate.template 3 (word 2))
  let value ← scenario plan [(2 ^ 256 - 1, 2), (2 ^ 255, 7), (2 ^ 256 - 1, 2 ^ 255)]
  let saved ← imported value
  let candidates ← get (KeyedStorage.shrinkCases saved 1000 10000)
  let result ← rows candidates "cases"
  ensure (!result.isEmpty && candidates == (← get (KeyedStorage.shrinkCases saved 1000 10000)))
    "keyed reductions were empty or nondeterministic"
  let mut removed := false
  let mut loweredInput := false
  let mut loweredKey := false
  let mut changedStep := false
  let mut seen : List String := []
  for row in result do
    let reduced ← get (KeyedStorage.caseProgram row)
    ensure (decide (KeyedStorage.StrictlySmaller reduced value) && reduced.program.check &&
      reduced.plan.step.helpers.length == value.plan.step.helpers.length &&
      Aggregate.bindingInventory reduced.plan.step == Aggregate.bindingInventory value.plan.step &&
      decide ((reduced.transactions.map (·.id)).Sublist (value.transactions.map (·.id))))
      "keyed reduction lost strict complexity, host typing or stable scope/IDs"
    let identity := (Json.mkObj [("program", Wire.encodeProgram reduced.program),
      ("transactions", KeyedStorage.transactionsJson reduced.transactions)]).compress
    ensure (!seen.contains identity) "duplicate keyed reduction"
    seen := identity :: seen
    removed := removed || reduced.transactions.length < value.transactions.length
    let sameCount := reduced.transactions.length == value.transactions.length
    loweredInput := loweredInput || (sameCount && (reduced.transactions.zip value.transactions).any
      fun (left, right) => left.input.val < right.input.val)
    loweredKey := loweredKey || (sameCount && (reduced.transactions.zip value.transactions).any
      fun (left, right) => left.key.val < right.key.val)
    changedStep := changedStep || Wire.encodeProgram reduced.program != Wire.encodeProgram value.program
    ensure ((← field row "observedSlots") == KeyedStorage.observedSlotsJson reduced)
      "reduced case did not rederive its observed slots"
    ensure ((← get (KeyedStorage.replayCase row 10000)) == row) "reduced keyed case did not replay"
  ensure (removed && loweredInput && loweredKey && changedStep) "keyed shrink omitted sequence/input/key/step axes"
  ensure ((← rows (← get (KeyedStorage.shrinkCases saved 2 10000)) "cases") == result.extract 0 2 &&
    (← rows (← get (KeyedStorage.shrinkCases saved 0 10000)) "cases").isEmpty) "keyed shrink limit changed ordering"
  let first := result[0]!
  let reduced ← get (KeyedStorage.caseProgram first)
  let badParent := Json.mkObj [("kind", toJson "reduced"), ("parentPlan", KeyedStorage.planJson reduced.plan),
    ("parentProgram", Wire.encodeProgram reduced.program),
    ("parentTransactions", KeyedStorage.transactionsJson reduced.transactions)]
  let provenance ← field first "provenance"
  rejected (KeyedStorage.replayCase (first.setObjVal! "provenance" (provenance.setObjVal! "origin" badParent)) 10000)
    "non-strict keyed reduction provenance accepted"

def testSourceKeyedStorageCases : IO Unit := do
  let imported ← referenceChecks
  let generated ← generationChecks
  tamperingChecks imported generated
  shrinkChecks

end Tests.SourceKeyedStorageCases
end

section
-- leanmerge: from Solcore.Test.SourceKeyedStorageCorpus
/-! The fixed keyed-storage corpus checks actual original Core histories against
independently computed expectations: status, payload and every declared
committed slot after every transaction. Coverage describes the checked step
AST, the transaction keys, inputs and completions, and static slot aliasing.
Source/Rust/EVM agreement is a separate external validation. -/
set_option autoImplicit false

namespace Tests.SourceKeyedStorageCorpus
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
  ("generatorVersion", generatorVersion), ("profileVersion", KeyedStorage.profileVersion),
  ("functionVersion", Solcore.Synthesis.Core.KeyedStorage.version),
  ("templateVersion", KeyedStorage.templateVersion), ("stepProfileVersion", Aggregate.profileVersion),
  ("stepFunctionVersion", Aggregates.version), ("stepTemplateVersion", Aggregate.templateVersion),
  ("emitterVersion", KeyedStorage.emitterVersion), ("wrapperVersion", KeyedStorage.wrapperVersion)]

private def words (values : List Word) : List String := values.map fun value => toString value.val

/-- Imported entries are emitted from their saved plan and sequence; generated
entries are regenerated from their seed. Both are checked by full replay. -/
private def entryCase (entry : Json) (fuel : Nat) : Except String Json := do
  if let .ok request := entry.getObjVal? "generation" then
    let some seed := (← request.getObjValAs? String "seed").toNat? | throw "invalid generation seed"
    let corpus := KeyedStorage.generateCases (Seed.ofNat seed) (← request.getObjValAs? Nat "maxProgramNodes") 1 1 fuel
    require ((← string corpus "status") == "complete") "generated entry was excluded"
    let some saved := (← corpus.getObjValAs? (Array Json) "cases")[0]? | throw "generated entry has no case"
    return saved
  let plan ← KeyedStorage.checkedPlan (← entry.getObjVal? "keyedStoragePlan")
  let scenario ← KeyedStorage.checkedScenario plan (← KeyedStorage.decodeTransactions (← entry.getObjVal? "transactions"))
  KeyedStorage.emitCase scenario (Json.mkObj [("kind", toJson "imported")]) fuel

private def templates (saved : Json) : Except String (List Nat) := do
  let origin ← (← saved.getObjVal? "provenance").getObjVal? "origin"
  if (← string origin "kind") != "keyed-storage-generated" then return []
  let helpers ← (← origin.getObjVal? "stepOrigin").getObjValAs? (List Json) "helpers"
  helpers.mapM fun helper => helper.getObjValAs? Nat "template"

def validateManifest (manifest : Json) (fuel : Nat := 1000000) : Except String Json := do
  require ((← string manifest "schema") == "solcore-lean.semantic-storage-corpus-manifest.v1" &&
    (← string manifest "profile") == "stateful-keyed-storage" &&
    (← string manifest "coverageKind") == "step-core-ast-features") "unexpected keyed-storage manifest scope"
  for (key, expected) in versions do
    require ((← string manifest key) == expected) ("keyed-storage manifest changed " ++ key)
  let requiredFeatures ← strings manifest "requiredFeatures"
  let requiredInputs ← strings manifest "requiredInputs"
  require (sameMembers requiredInputs (words KeyedStorage.boundaryInputs))
    "keyed corpus must require all six boundary inputs"
  let requiredKeys ← strings manifest "requiredKeys"
  require (sameMembers requiredKeys (words KeyedStorage.keyBank)) "keyed corpus must require the whole key bank"
  require ((← strings manifest "requiredAliases") == KeyedStorage.aliasCatalog)
    "keyed corpus must require the canonical alias catalog"
  require ((← manifest.getObjValAs? (List Nat) "requiredHelperCounts") == [1, 2, 3] &&
    (← manifest.getObjValAs? (List Nat) "requiredTransactionCounts") == [1, 2, 3])
    "keyed corpus must require one to three helpers and transactions"
  require ((← (← manifest.getObjVal? "generationRecipeRequirements").getObjValAs? (List Nat) "templates") == [0, 1, 2, 3])
    "keyed corpus must require all four step templates"
  require ((← strings manifest "requiredOutcomes") == ["returned", "reverted"]) "keyed corpus must require both outcomes"
  let requiredPatterns ← strings manifest "requiredCompletionPatterns"
  require (!requiredPatterns.isEmpty) "keyed corpus must require completion patterns"
  let entries ← manifest.getObjValAs? (Array Json) "cases"
  require (0 < entries.size && entries.size ≤ 64) "keyed corpus must contain 1..64 scenarios"
  let mut identifiers : List String := []
  let mut features : List String := []
  let mut inputs : List String := []
  let mut keys : List String := []
  let mut aliases : List String := []
  let mut helperCounts : List Nat := []
  let mut transactionCounts : List Nat := []
  let mut templateUnion : List Nat := []
  let mut outcomes : List String := []
  let mut patterns : List String := []
  let mut transactionTotal := 0
  for entry in entries do
    let identifier ← string entry "id"
    require (!identifiers.contains identifier) ("duplicate keyed corpus id " ++ identifier)
    identifiers := identifier :: identifiers
    let saved ← entryCase entry fuel
    require ((← KeyedStorage.replayCase saved fuel) == saved) ("keyed corpus entry did not replay: " ++ identifier)
    let scenario ← KeyedStorage.caseProgram saved
    if !(entry.getObjVal? "generation").isOk then
      require ((← saved.getObjVal? "keyedStoragePlan") == (← entry.getObjVal? "keyedStoragePlan") &&
        (← saved.getObjVal? "transactions") == (← entry.getObjVal? "transactions"))
        ("imported keyed entry is not canonical: " ++ identifier)
    let caseFeatures := (← (← saved.getObjVal? "provenance").getObjValAs? (List String) "features").eraseDups
    require (sameMembers (← strings entry "expectedFeatures") caseFeatures)
      ("keyed corpus features changed: " ++ identifier)
    let history := KeyedStorage.observe scenario Solcore.Synthesis.Stateful.StorageExecution.fixtureBindings fuel
    require ((← string history "status") == "complete") ("keyed corpus history incomplete: " ++ identifier)
    let observed ← history.getObjValAs? (List Json) "transactions"
    let expected ← entry.getObjValAs? (List Json) "expectedHistory"
    require (observed.length == expected.length) ("keyed expected history length changed: " ++ identifier)
    let mut statuses : List String := []
    for (row, golden) in observed.zip expected do
      let actual := Json.mkObj [("id", ← row.getObjVal? "id"), ("status", ← row.getObjVal? "status"),
        ("output", ← row.getObjVal? "output"), ("committedStorage", ← row.getObjVal? "committedStorage")]
      require (actual == golden) ("original Core differs from the independent history: " ++ identifier ++ " " ++ actual.compress)
      statuses := statuses ++ [← string row "status"]
    transactionTotal := transactionTotal + observed.length
    features := (features ++ caseFeatures).eraseDups
    inputs := (inputs ++ scenario.transactions.map fun tx => toString tx.input.val).eraseDups
    keys := (keys ++ scenario.transactions.map fun tx => toString tx.key.val).eraseDups
    aliases := (aliases ++ KeyedStorage.aliases scenario.transactions).eraseDups
    helperCounts := (helperCounts ++ [scenario.plan.step.helpers.length]).eraseDups
    transactionCounts := (transactionCounts ++ [scenario.transactions.length]).eraseDups
    templateUnion := (templateUnion ++ (← templates saved)).eraseDups
    outcomes := (outcomes ++ statuses).eraseDups
    patterns := (patterns ++ [String.intercalate "," statuses]).eraseDups
  require (requiredFeatures.all features.contains) "keyed corpus misses a required step feature"
  require (requiredInputs.all inputs.contains && requiredKeys.all keys.contains) "keyed corpus misses an input or key"
  require (KeyedStorage.aliasCatalog.all aliases.contains) "keyed corpus misses an alias kind"
  require ([1, 2, 3].all helperCounts.contains && [1, 2, 3].all transactionCounts.contains)
    "keyed corpus misses a helper or transaction count"
  require ([0, 1, 2, 3].all templateUnion.contains) "keyed corpus misses a generated template"
  require (["returned", "reverted"].all outcomes.contains && requiredPatterns.all patterns.contains)
    "keyed corpus misses an observed outcome or completion pattern"
  return Json.mkObj [("profile", toJson "stateful-keyed-storage"), ("scenarios", toJson entries.size),
    ("transactions", toJson transactionTotal), ("aliases", toJson aliases), ("patterns", toJson patterns)]

private def checked {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def rejects {α : Type} (result : Except String α) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "invalid keyed-storage corpus unexpectedly passed")

def testSourceKeyedStorageCorpus : IO Unit := do
  let manifest ← checked (Json.parse (← IO.FS.readFile "scripts/semantic-keyed-storage-corpus.json"))
  let summary ← checked (validateManifest manifest)
  let entries ← checked (manifest.getObjValAs? (Array Json) "cases")
  let some first := entries[0]? | throw (IO.userError "missing first keyed case")
  let some generatedEntry := entries.find? (fun entry => (entry.getObjVal? "generation").isOk) |
    throw (IO.userError "missing generated keyed case")
  let replace := fun (original changed : Json) => manifest.setObjVal! "cases"
    (.arr (entries.map fun entry => if entry == original then changed else entry))
  let history ← checked (first.getObjValAs? (Array Json) "expectedHistory")
  let row := history[0]!
  let changedOutput := row.setObjVal! "output" (toJson ("0x" ++ String.ofList (List.replicate 64 'f')))
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr (history.set! 0 changedOutput)))))
  let storage ← checked (row.getObjValAs? (Array Json) "committedStorage")
  let changedSlot := row.setObjVal! "committedStorage" (.arr (storage.set! 0 (storage[0]!.setObjVal! "value" (toJson "7"))))
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr (history.set! 0 changedSlot)))))
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr (history.pop)))))
  let generatedHistory ← checked (generatedEntry.getObjValAs? (Array Json) "expectedHistory")
  let generatedStatus ← checked (generatedHistory[0]!.getObjValAs? String "status")
  rejects (validateManifest (replace generatedEntry (generatedEntry.setObjVal! "expectedHistory"
    (.arr (generatedHistory.set! 0 (generatedHistory[0]!.setObjVal! "status"
      (toJson (if generatedStatus == "returned" then "reverted" else "returned"))))))))
  let transactions ← checked (first.getObjValAs? (Array Json) "transactions")
  rejects (validateManifest (replace first (first.setObjVal! "transactions"
    (.arr (transactions.set! 0 (transactions[0]!.setObjVal! "key" (toJson "4")))))))
  rejects (validateManifest (replace first (first.setObjVal! "expectedFeatures" (toJson ([] : List String)))))
  rejects (validateManifest (replace generatedEntry (generatedEntry.setObjVal! "generation"
    (Json.mkObj [("seed", toJson "13"), ("maxProgramNodes", toJson (384 : Nat))]))))
  rejects (validateManifest (manifest.setObjVal! "cases" (.arr (entries.push first))))
  for (key, value) in [
      ("profile", toJson "stateful-storage"), ("templateVersion", toJson "forged"),
      ("cases", .arr #[]), ("requiredInputs", toJson ([] : List String)),
      ("requiredKeys", toJson (["0"] : List String)), ("requiredHelperCounts", toJson [1, 2]),
      ("requiredAliases", toJson KeyedStorage.aliasCatalog.reverse),
      ("requiredCompletionPatterns", toJson (["reverted,reverted,reverted"] : List String))] do
    rejects (validateManifest (manifest.setObjVal! key value))
  rejects (validateManifest manifest 0)
  IO.println summary.compress

end Tests.SourceKeyedStorageCorpus
end

section
-- leanmerge: from Solcore.Test.SourceKeyedStorageEmitter
/-! Keyed-storage protocol regressions through actual installed ContractRuntime
code. Golden histories are hand-computed: they cover the write order key, key + 1,
counter, aliasing of keys zero and maximum with the counter, wrapping successor
slots, zero writes as deletions and rollback of tentative keyed writes. -/
set_option autoImplicit false

namespace Tests.SourceKeyedStorageEmitter

open Lean Solcore.Core Solcore.ContractRuntime Solcore.Synthesis.Core
open Solcore.Synthesis.Core.KeyedStorage (CheckedPlan)
open Solcore.Synthesis.Source (EmittedProgram)
open Solcore.Synthesis.Stateful

private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)
private def entry : Wire.Expr := .apply (.var 1) (.var 0)
private def increment : Wire.Expr := .binary .wordAdd (.var 0) (word 1)
private def maximum : Nat := 2 ^ 256 - 1

private def privateStep : Wire.Expr :=
  .letE (.newCell .word (word 0))
    (.letE (.storeCell (.var 0) (.binary .wordAdd (.loadCell (.var 0)) (word 2)))
      (.binary .wordAdd (.var 2) (.loadCell (.var 1))))

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def checked (helpers : List Wire.Expr) (body : Wire.Expr := entry) : IO CheckedPlan := do
  let some step := Aggregates.CheckedDAG.ofParts? helpers body |
    throw (IO.userError "keyed step did not pass the checked aggregate profile")
  let some plan := CheckedPlan.ofStep? step |
    throw (IO.userError "keyed wrapper did not pass the full Wire host checker")
  return plan

private def emitted (plan : CheckedPlan) : IO EmittedProgram :=
  match Solcore.Synthesis.Source.KeyedStorage.emit plan with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"keyed source emission failed: {reprStr error}")

private def transactions (rows : List (Nat × Nat)) : List KeyedStorageExecution.Transaction :=
  rows.zipIdx.map fun ((key, input), index) =>
    ⟨"tx-" ++ toString index, Word.ofNatModulo key, Word.ofNatModulo input⟩

private def slotRows (values : List (Nat × Nat)) : Json := toJson (values.map fun (slot, value) =>
  Json.mkObj [("slot", toJson (toString slot)), ("value", toJson (toString value))])

/-- One hand-computed history row: status, payload and the complete committed
values of the declared slots after the transaction. -/
private def historyCheck (plan : CheckedPlan) (rows : List (Nat × Nat))
    (expected : List (String × Nat × List (Nat × Nat))) : IO Unit := do
  let history := KeyedStorageExecution.observeContract plan.contract (transactions rows)
    StorageExecution.fixtureBindings 10000
  let observed := (history.getObjValAs? (List Json) "transactions").toOption.getD []
  ensure ((history.getObjValAs? String "status").toOption == some "complete" && observed.length == expected.length)
    "keyed golden history did not complete"
  for (row, (status, payload, committed)) in observed.zip expected do
    ensure ((row.getObjValAs? String "status").toOption == some status &&
      (row.getObjValAs? String "output").toOption == some (encodeBytesText (encodeWordBytesBE (Word.ofNatModulo payload))) &&
      (row.getObjVal? "committedStorage").toOption == some (slotRows committed))
      s!"keyed golden row changed: {row.compress}"

private def goldenChecks : IO Unit := do
  let identity ← checked [.var 0]
  -- Key zero reads the counter as old and is overwritten by the counter write;
  -- key maximum's successor wraps to the counter and is also overwritten.
  historyCheck identity [(5, 2), (0, 4), (maximum, 3)] [
    ("returned", 3, [(0, 1), (1, 0), (5, 2), (6, 0), (maximum, 0)]),
    ("returned", 5, [(0, 2), (1, 1), (5, 2), (6, 0), (maximum, 0)]),
    ("reverted", 9, [(0, 2), (1, 1), (5, 2), (6, 0), (maximum, 0)])]
  -- The successor of maximum minus one is maximum, read by the next key.
  historyCheck identity [(maximum - 1, 0), (maximum, 2), (maximum - 1, 6)] [
    ("returned", 1, [(0, 1), (maximum - 1, 0), (maximum, 0)]),
    ("returned", 6, [(0, 2), (maximum - 1, 0), (maximum, 2)]),
    ("returned", 9, [(0, 3), (maximum - 1, 6), (maximum, 0)])]
  -- Zero results delete; the reverted deletion of slot one is not committed.
  historyCheck (← checked [.var 0] (word 0)) [(1, 0), (0, 0), (1, 1)] [
    ("returned", 1, [(0, 1), (1, 0), (2, 0)]),
    ("returned", 5, [(0, 2), (1, 1), (2, 0)]),
    ("reverted", 4, [(0, 2), (1, 1), (2, 0)])]
  -- A fresh private cell per invocation; arbitrary entries remain the step.
  historyCheck (← checked [privateStep] (.binary .wordSub entry (word 1))) [(2 ^ 255, 7), (2 ^ 255, 2)] [
    ("reverted", 9, [(0, 0), (2 ^ 255, 0), (2 ^ 255 + 1, 0)]),
    ("returned", 4, [(0, 1), (2 ^ 255, 3), (2 ^ 255 + 1, 0)])]

/-- The reverted aliasing call's tentative world shows the exact write order. -/
private def tentativeChecks : IO Unit := do
  let plan ← checked [.var 0]
  let bindings := StorageExecution.fixtureBindings
  let world := StorageExecution.initialWorldForContract plan.contract bindings
  let registry : CheckedContractRegistry :=
    ⟨fun address => if address == bindings.address then some plan.contract else none⟩
  let some ⟨contract, installed⟩ := registry.resolve? world bindings.address |
    throw (IO.userError "keyed contract did not resolve")
  let invocation : TopLevelInvocation := {
    target := bindings.address, caller := bindings.caller, callValue := Word.zero,
    inputData := KeyedStorageExecution.inputData Word.maximum (Word.ofNatModulo 3) }
  match TopLevelExecution.run contract invocation installed 0 with
  | .outOfFuel _ _ _ _ _ _ => pure ()
  | .completed _ => throw (IO.userError "zero fuel completed a keyed call")
  match TopLevelExecution.run contract invocation installed 10000 with
  | .outOfFuel _ _ _ _ _ _ => throw (IO.userError "keyed golden call exhausted fuel")
  | .completed result =>
      ensure (result.outcome == .reverted (encodeWordBytesBE (Word.ofNatModulo 5)))
        "odd keyed input did not revert with the tentative sum"
      let some working := result.terminalContext.context.values.working.1.account? bindings.address |
        throw (IO.userError "working account missing")
      ensure (working.storageRead Word.maximum == Word.ofNatModulo 3 &&
        working.storageRead Word.zero == Word.ofNatModulo 1)
        "keyed writes did not apply key, wrapped successor, then counter"
      let some committed := result.finalWorld.account? bindings.address |
        throw (IO.userError "committed account missing")
      ensure (committed.storageRead Word.maximum == Word.zero && (committed.storageValue? Word.zero).isNone &&
        committed.balance == Word.zero && result.committedJournal.logList.isEmpty)
        "reverted keyed writes or unrelated effects were committed"

private def admissionChecks : IO Unit := do
  for plan in [← checked [increment], ← checked [privateStep] (.binary .wordSub entry (word 1))] do
    ensure (plan.program.check && plan.program.toCore.checkHost &&
      plan.program.resultType == .sum .word (.sum .word .word) && plan.contract.entryProfile == .wordOutcomeV1)
      "keyed plan lost full host checking or the typed outcome convention"
    ensure (plan.contract.code.program == plan.program.toCore) "admission replaced the original contract"
    ensure (KeyedStorage.canonicalNodes plan.step == Wire.programNodes plan.program &&
      Wire.programNodes plan.program == Wire.programNodes plan.step.program + KeyedStorage.programOverhead)
      "keyed wrapper overhead differs from the complete original Core"
    match plan.program.body with
    | .letE saved _ =>
        ensure (Wire.encodeExpr saved == Wire.encodeExpr plan.step.program.body)
          "keyed wrapper ignored its arbitrary entry closure"
    | _ => throw (IO.userError "keyed wrapper lost its initial closure binding")
    ensure ((← emitted plan) == (← emitted plan)) "keyed emission is nondeterministic"
  -- Raw primitives join the existing opcode import only when a step uses them.
  let divided ← checked [.binary .wordDiv (.var 0) (word 1)]
  match Solcore.Synthesis.Source.KeyedStorage.emit divided with
  | .ok emitted => unless (emitted.source.splitOn "import {sload, sstore, mstore, revert_, div as sc_div, ").length == 2 && (emitted.source.splitOn "    let sc_v3: word = sc_div(sc_v0, sc_v2);").length == 2 do
      throw (IO.userError "KeyedStorage emission lost the merged raw division alias or its snapshots")
  | .error error => throw (IO.userError s!"KeyedStorage raw division was rejected: {reprStr error}")

private def expectedBasic : String := String.intercalate "\n" [
  "import * from std;", "import * from std.dispatch;",
  "import {sload, sstore, mstore, revert_} from std.opcodes;", "",
  "function sc_fn0(sc_arg: word) returns (word) {",
  "    let sc_v0: word = 1;", "    let sc_v1: word = (sc_arg + sc_v0);",
  "    return sc_v1;", "}", "",
  "function sc_step(sc_arg: word) returns (word) {",
  "    let sc_v0: word = sc_fn0(sc_arg);", "    return sc_v0;", "}", "",
  "contract SynthesizedKeyedStorage {",
  "    function run(key: uint256, input: uint256) public returns (uint256) {",
  "        let sc_key: word = Typedef.rep(key);",
  "        let sc_input: word = Typedef.rep(input);",
  "        let sc_old: word = sload(sc_key);", "        let sc_count: word = sload(0);",
  "        let sc_computed: word = sc_step(sc_input + sc_old);",
  "        sstore(sc_key, sc_computed);", "        sstore(sc_key + 1, sc_old);",
  "        sstore(0, sc_count + 1);",
  "        let sc_final_key: word = sload(sc_key);",
  "        let sc_final_next: word = sload(sc_key + 1);",
  "        let sc_final_count: word = sload(0);",
  "        let sc_result: word = sc_final_key + sc_final_next + sc_final_count;",
  "        if ((sc_input & 1) == 1) {", "            mstore(0, sc_result);",
  "            revert_(0, 32);", "        }",
  "        return uint256(sc_result);", "    }", "}", ""]

private def formattingChecks : IO Unit := do
  let source ← emitted (← checked [increment])
  ensure (source.source == expectedBasic) "keyed protocol source changed"
  ensure (source.contractName == "SynthesizedKeyedStorage" && source.methodSignature == "run(uint256,uint256)" &&
    source.deployPath == ["SynthesizedKeyedStorageDeploy"] &&
    source.runtimePath == ["SynthesizedKeyedStorageDeploy", "SynthesizedKeyedStorage"])
    "keyed wrapper metadata changed"
  ensure (Solcore.Synthesis.Source.KeyedStorage.emitterVersion == "solcore-source-keyed-storage-v2" &&
    Solcore.Synthesis.Source.KeyedStorage.wrapperVersion == "solcore-word-keyed-storage-contract-v1" &&
    Solcore.Synthesis.Source.KeyedStorage.selector == "0x7357f5d2" &&
    KeyedStorage.version == "core-keyed-storage-contract-v1" && KeyedStorage.counterSlot == 0)
    "keyed provenance changed"

private def observerChecks : IO Unit := do
  let slots := KeyedStorageExecution.observedSlots (transactions [(maximum, 1), (0, 2), (maximum, 3)])
  ensure (slots.map (·.val) == [0, 1, maximum]) "observed slots are not the sorted unique counter/key/successor set"
  ensure ((KeyedStorageExecution.observedSlots (transactions [(7, 0)])).map (·.val) == [0, 7, 8])
    "observed slots omitted the counter or successor"
  ensure (KeyedStorageExecution.calldata (Word.ofNatModulo 2) Word.maximum ==
    "0x7357f5d2" ++ String.ofList (List.replicate 63 '0') ++ "2" ++ String.ofList (List.replicate 64 'f'))
    "keyed calldata is not selector, key and input Words"
  let plan ← checked [.var 0]
  let calls := transactions [(3, 2), (4, 1), (5, 0)]
  let exhausted := KeyedStorageExecution.observeContract plan.contract calls StorageExecution.fixtureBindings 0
  ensure ((exhausted.getObjValAs? String "status").toOption == some "incomplete" &&
    (exhausted.getObjValAs? (List String) "unexecuted").toOption == some ["tx-1", "tx-2"] &&
    (exhausted.getObjVal? "finalStorage").toOption == (exhausted.getObjVal? "initialStorage").toOption)
    "keyed observer conflated fuel exhaustion with completion"
  let complete := KeyedStorageExecution.observeContract plan.contract calls StorageExecution.fixtureBindings 10000
  ensure ((complete.getObjVal? "observedSlots").toOption ==
    some (toJson (["0", "3", "4", "5", "6"] : List String))) "history did not declare its observed slots"

def testSourceKeyedStorageEmitter : IO Unit := do
  admissionChecks
  goldenChecks
  tentativeChecks
  formattingChecks
  observerChecks

end Tests.SourceKeyedStorageEmitter
end

section
-- leanmerge: from Solcore.Test.SourceStorageCases
/-! Storage-case regressions exercise actual checked-contract execution, exact
replay, bounded generation and scenario reductions. Expected fixture values are
test goldens only; neither emitted cases nor the observer consume them. -/
set_option autoImplicit false

namespace Tests.SourceStorageCases
open Lean Solcore.Core Solcore.Synthesis.Core Solcore.Synthesis.Source
open Solcore.Synthesis.Core.StorageContract (CheckedPlan)
open Solcore.Synthesis.Stateful.StorageExecution (Transaction Bindings)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def get {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)
private def rejected {α : Type} (result : Except String α) (message : String) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError message)
private def field (value : Json) (name : String) : IO Json := get (value.getObjVal? name)
private def string (value : Json) (name : String) : IO String := get (value.getObjValAs? String name)
private def natural (value : Json) (name : String) : IO Nat := get (value.getObjValAs? Nat name)
private def rows (value : Json) (name : String := "transactions") : IO (Array Json) :=
  get (value.getObjValAs? (Array Json) name)
private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)
private def entry : Wire.Expr := .apply (.var 1) (.var 0)
private def bindings : Bindings := ⟨⟨17, by decide⟩, ⟨101, by decide⟩⟩
private def makePlan (body : Wire.Expr) (result : Wire.Expr := entry) : IO CheckedPlan := do
  let some graph := Aggregates.CheckedDAG.ofParts? [body] result |
    throw (IO.userError "storage fixture failed step admission")
  let some plan := CheckedPlan.ofStep? graph | throw (IO.userError "storage wrapper failed host admission")
  return plan
private def transactions (inputs : List Word) : List Transaction :=
  inputs.zipIdx.map fun (input, index) => ⟨"call-" ++ toString index, input⟩
private def scenario (plan : CheckedPlan) (inputs : List Word) : IO Storage.CheckedScenario :=
  get (Storage.checkedScenario plan (transactions inputs))
private def imported (value : Storage.CheckedScenario) (fuel : Nat := 10000) : IO Json :=
  get (Storage.emitCase value (Json.mkObj [("kind", toJson "imported")]) fuel)
private def storage (first second : Word) : Json := toJson ([
  Json.mkObj [("slot", toJson "0"), ("value", toJson (toString first.val))],
  Json.mkObj [("slot", toJson "1"), ("value", toJson (toString second.val))]])

private def checkHistory (value : Storage.CheckedScenario) (expected : List (Word × Word × Word)) : IO Unit := do
  let observed := Storage.observe value bindings 10000
  ensure ((← string observed "status") == "complete") "storage fixture did not finish"
  ensure ((← field observed "initialStorage") == storage Word.zero Word.zero)
    "original Core did not start with empty storage"
  let result ← rows observed
  ensure (result.size == expected.length && result.size == value.transactions.length)
    "original Core changed transaction count"
  for ((output, first, second), index) in expected.zipIdx do
    let row := result[index]!
    ensure (some (← string row "id") == (value.transactions[index]?).map (·.id) && (← natural row "index") == index)
      "observer lost stable transaction identity"
    ensure ((← string row "status") == "returned" &&
      (← string row "output") == Solcore.ContractRuntime.encodeBytesText
        (Solcore.ContractRuntime.encodeWordBytesBE output)) "storage return value differs from golden"
    ensure ((← field row "committedStorage") == storage first second)
      "original Core committed the wrong storage prefix"
  ensure ((← field observed "finalStorage") == (← field result[result.size - 1]! "committedStorage"))
    "final storage differs from the last committed prefix"
  ensure ((← rows observed "unexecuted").isEmpty && (← field observed "stoppedAt") == Json.null)
    "successful storage history retained unexecuted work"
  ensure (Storage.observe value bindings 10000 == observed) "fresh observation reused a previous world"

private def referenceChecks : IO Json := do
  let identity ← makePlan (.var 0)
  let value ← scenario identity ([1, 2, 3].map Word.ofNatModulo)
  checkHistory value ([(2, 1, 1), (5, 3, 2), (9, 6, 3)].map fun (out, a, b) =>
    (Word.ofNatModulo out, Word.ofNatModulo a, Word.ofNatModulo b))
  let wrap ← scenario identity [Word.maximum, Word.ofNatModulo 1, Word.zero]
  checkHistory wrap [(Word.zero, Word.maximum, Word.ofNatModulo 1),
    (Word.ofNatModulo 2, Word.zero, Word.ofNatModulo 2),
    (Word.ofNatModulo 3, Word.zero, Word.ofNatModulo 3)]
  let privateStep := Wire.Expr.letE (.newCell .word (word 0))
    (.letE (.storeCell (.var 0) (.binary .wordAdd (.loadCell (.var 0)) (word 2)))
      (.binary .wordAdd (.var 2) (.loadCell (.var 1))))
  let mutablePlan ← makePlan privateStep (.binary .wordSub entry (word 1))
  let mutableCase ← scenario mutablePlan ([1, 2, 3].map Word.ofNatModulo)
  checkHistory mutableCase ([(3, 2, 1), (7, 5, 2), (12, 9, 3)].map fun (out, a, b) =>
    (Word.ofNatModulo out, Word.ofNatModulo a, Word.ofNatModulo b))
  let fresh := Storage.observe value ⟨⟨33, by decide⟩, ⟨202, by decide⟩⟩ 10000
  ensure ((← rows fresh).map Solcore.Synthesis.Stateful.AccountStorage.unbound == (← rows (Storage.observe value bindings 10000)).map Solcore.Synthesis.Stateful.AccountStorage.unbound &&
      (← rows fresh).all (Solcore.Synthesis.Stateful.AccountStorage.boundTo · [202]))
    "address-independent profile observed a different bound target"
  ensure (identity.program.check && identity.program.toCore.checkHost)
    "canonical storage code lost frozen Wire host admission"
  for input in Storage.boundaryInputs do
    let inputData := Solcore.Synthesis.Stateful.StorageExecution.inputData input
    ensure (inputData.bytes.size == 36 && inputData.wordBE? (Word.ofNatModulo 4) == some input &&
      Solcore.Synthesis.Stateful.StorageExecution.calldata input == Input.calldata input)
      "native observer input differs from emitted canonical ABI"
  let saved ← imported value
  ensure ((← get (Storage.replayCase saved 10000)) == saved) "storage imported replay changed case"
  ensure ((← get (Storage.replayCase (saved.setObjVal! "directCore" (toJson "forged")) 10000)) == saved)
    "storage replay trusted an inserted expected output"
  let changedInput ← scenario identity ([3, 2, 1].map Word.ofNatModulo)
  let changed ← imported changedInput
  ensure ((← field saved "program") == (← field changed "program") &&
    (← string saved "source") == (← string changed "source"))
    "runtime inputs were substituted into source or installed Core code"
  return saved

private def resourceChecks : IO Unit := do
  let slow := (List.range 12).foldl (fun body _ => Wire.Expr.letE (word 1) body) (word 1)
  let plan ← makePlan (.ifE (.binary .wordEq (.var 0) (word 0)) (word 0) slow)
  let value ← scenario plan ([0, 1, 1].map Word.ofNatModulo)
  let empty := storage Word.zero Word.zero
  let low := Storage.observe value bindings 0
  ensure ((← string low "status") == "incomplete" && (← string low "stoppedAt") == "call-0" &&
    (← rows low).size == 1 && (← rows low "unexecuted").size == 2 &&
    (← field low "finalStorage") == empty) "out-of-fuel did not stop the history without committing"
  let mut afterCommit := false
  for fuel in List.range 200 do
    let observed := Storage.observe value bindings fuel
    let result ← rows observed
    if result.size == 2 then
      if (← string result[1]! "status") == "out-of-fuel" then
        afterCommit := true
        ensure ((← string result[0]! "status") == "returned" &&
          (← field result[1]! "committedStorage") == (← field result[0]! "committedStorage") &&
          (← field observed "finalStorage") == storage Word.zero (Word.ofNatModulo 1) &&
          (← field observed "unexecuted") == toJson (["call-2"] : List String))
          "suspended transaction committed speculative state or executed later work"
  ensure afterCommit "resource regression never reached exhaustion after a committed prefix"

private def generationChecks : IO Json := do
  for seed in List.range 12 do
    let mut minimum : Option Nat := none
    for budget in List.range 385 do
      if minimum.isNone && (Storage.generatedScenario (Seed.ofNat seed) budget).isOk then minimum := some budget
    let some budget := minimum | throw (IO.userError "storage template does not fit default384 budget")
    let (value, _) ← get (Storage.generatedScenario (Seed.ofNat seed) budget)
    ensure (Wire.programNodes value.program ≤ budget && value.transactions.length == 3 &&
      value.plan.step.helpers.length == 1 + seed % 3) "storage recipe lost full node/transaction/helper bounds"
    rejected (Storage.generatedScenario (Seed.ofNat seed) (budget - 1)) "undersized node budget accepted"
  rejected (Storage.generatedScenario (Seed.ofNat 0) 513) "oversized node budget accepted"
  let corpus := Storage.generateCases (Seed.ofNat 0) 384 4 256 10000
  ensure (corpus == Storage.generateCases (Seed.ofNat 0) 384 4 256 10000) "storage generation nondeterministic"
  let generated ← rows corpus "cases"
  ensure (generated.size == 4 && (← natural corpus "attempted") ≤ 256)
    "storage count does not count complete scenarios"
  for saved in generated do
    let value ← get (Storage.caseProgram saved)
    ensure (value.transactions.length == 3 && Wire.programNodes value.program ≤ 384)
      "generated case escaped bounded storage profile"
    ensure ((← get (Storage.replayCase saved 10000)) == saved) "generated history provenance did not replay"
    let low ← get (Storage.replayCase saved 0)
    ensure ((← natural low "executionFuel") == 0 && (← field low "provenance") == (← field saved "provenance"))
      "fresh replay fuel changed the generation validation budget"
  let saved := generated[0]!
  let origin ← field (← field saved "provenance") "origin"
  let some seed := (← string origin "seed").toNat? | throw (IO.userError "invalid generated seed")
  let low := Storage.generateCases (Seed.ofNat seed) 384 1 1 0
  let excluded ← rows low "excluded"
  ensure ((← rows low "cases").isEmpty && (← string excluded[0]! "category") == "inconclusive-resource")
    "storage generation resource exhaustion was not distinguished"
  ensure ((← rows (Storage.generateCases (Seed.ofNat seed) 384 2 1 10000) "cases").size == 1 &&
    (← natural (Storage.generateCases (Seed.ofNat seed) 384 0 10 10000) "attempted") == 0 &&
    (← rows (Storage.generateCases (Seed.ofNat seed) 384 1 0 10000) "cases").isEmpty)
    "storage generator ignored count/attempt bounds"
  return saved

private def tamperingChecks (saved generated : Json) : IO Unit := do
  let transactionRows ← rows saved
  let first := transactionRows[0]!
  for (name, bad) in [("id", toJson ""), ("id", toJson "not valid"),
      ("id", toJson (String.ofList (List.replicate 65 'a'))), ("input", toJson "01"),
      ("input", toJson "2"), ("calldata", toJson "0x"), ("value", toJson "1"),
      ("extra", toJson true)] do
    rejected (Storage.decodeTransactions (toJson [first.setObjVal! name bad]))
      "noncanonical storage transaction accepted"
  rejected (Storage.decodeTransactions (toJson [first, first])) "duplicate transaction IDs accepted"
  rejected (Storage.decodeTransactions (toJson ([] : List Json))) "empty transaction list accepted"
  rejected (Storage.decodeTransactions
    (toJson (List.replicate (Solcore.Synthesis.Stateful.Sequence.maxTransactions + 1) first)))
    "unbounded transaction count accepted"
  for (name, bad) in [("initialState", Json.mkObj [("storage", toJson [first])]),
      ("observedSlots", toJson (["1", "0"] : List String)), ("executionFuel", toJson (10000001 : Nat)),
      ("program", Wire.encodeProgram {resultType := .word, dataDefinitions := [], body := word 0})] do
    rejected (Storage.caseProgram (saved.setObjVal! name bad)) "invalid storage case boundary accepted"
  let provenance ← field generated "provenance"
  let origin ← field provenance "origin"
  let withOrigin := fun changed => generated.setObjVal! "provenance" (provenance.setObjVal! "origin" changed)
  for name in ["generatorVersion", "profileVersion", "functionVersion", "templateVersion", "stepProfileVersion",
      "stepFunctionVersion", "stepTemplateVersion", "emitterVersion", "wrapperVersion", "features"] do
    rejected (Storage.replayCase (generated.setObjVal! "provenance" (provenance.setObjVal! name Json.null)) 10000)
      "tampered storage provenance accepted"
  for (name, bad) in [("seed", toJson "00"), ("finalSeed", toJson "bad"),
      ("maxProgramNodes", toJson (513 : Nat)), ("stepOrigin", Json.null), ("sequenceIndices", Json.null),
      ("validationFuel", toJson (10000001 : Nat)), ("validationFuel", toJson (0 : Nat))] do
    rejected (Storage.replayCase (withOrigin (origin.setObjVal! name bad)) 10000)
      "tampered generated storage recipe accepted"
  let plan ← field saved "storagePlan"
  rejected (Storage.checkedPlan (plan.setObjVal! "extra" Json.null)) "noncanonical storage plan accepted"
  rejected (Storage.replayCase (saved.setObjVal! "source" (toJson "stale")) 10000) "stale source accepted"
  let contract ← field saved "contract"
  rejected (Storage.replayCase (saved.setObjVal! "contract" (contract.setObjVal! "selector" (toJson "0x00000000"))) 10000)
    "wrong storage ABI selector accepted"
  let bindingJson := Solcore.Synthesis.Stateful.StorageExecution.bindingsJson bindings
  ensure ((Solcore.Synthesis.Stateful.StorageExecution.decodeBindings bindingJson).isOk) "valid bindings rejected"
  for (name, value) in [("caller", "017"), ("address", "17"), ("caller", toString (2 ^ 160))] do
    rejected (Solcore.Synthesis.Stateful.StorageExecution.decodeBindings (bindingJson.setObjVal! name (toJson value)))
      "invalid execution bindings accepted"

private def shrinkChecks : IO Unit := do
  let plan ← makePlan (Aggregate.template 3 (word 2))
  let value ← scenario plan [Word.maximum, Word.ofNatModulo 7, Word.maximum]
  let saved ← imported value
  let candidates ← get (Storage.shrinkCases saved 1000 10000)
  let result ← rows candidates "cases"
  ensure (!result.isEmpty && candidates == (← get (Storage.shrinkCases saved 1000 10000)))
    "storage reductions were empty or nondeterministic"
  let mut removed := false
  let mut loweredInput := false
  let mut changedStep := false
  let mut seen : List String := []
  for row in result do
    let reduced ← get (Storage.caseProgram row)
    ensure (decide (Storage.StrictlySmaller reduced value) && reduced.program.check &&
      reduced.plan.step.helpers.length == value.plan.step.helpers.length &&
      Aggregate.bindingInventory reduced.plan.step == Aggregate.bindingInventory value.plan.step &&
      decide ((reduced.transactions.map (·.id)).Sublist (value.transactions.map (·.id))))
      "storage reduction lost strict complexity, host typing or stable scope/IDs"
    let key := (Json.mkObj [("program", Wire.encodeProgram reduced.program),
      ("transactions", Storage.transactionsJson reduced.transactions)]).compress
    ensure (!seen.contains key) "duplicate storage reduction"
    seen := key :: seen
    removed := removed || reduced.transactions.length < value.transactions.length
    loweredInput := loweredInput || (reduced.transactions.length == value.transactions.length &&
      Storage.inputWeight reduced < Storage.inputWeight value)
    changedStep := changedStep || Wire.encodeProgram reduced.program != Wire.encodeProgram value.program
    ensure ((← get (Storage.replayCase row 10000)) == row) "reduced storage case did not replay"
  ensure (removed && loweredInput && changedStep) "storage shrink omitted sequence/input/step axes"
  ensure ((← rows (← get (Storage.shrinkCases saved 2 10000)) "cases") == result.extract 0 2 &&
    (← rows (← get (Storage.shrinkCases saved 0 10000)) "cases").isEmpty) "storage shrink limit changed ordering"
  let first := result[0]!
  let reduced ← get (Storage.caseProgram first)
  let badParent := Json.mkObj [("kind", toJson "reduced"), ("parentPlan", Storage.planJson reduced.plan),
    ("parentProgram", Wire.encodeProgram reduced.program),
    ("parentTransactions", Storage.transactionsJson reduced.transactions)]
  let provenance ← field first "provenance"
  rejected (Storage.replayCase (first.setObjVal! "provenance" (provenance.setObjVal! "origin" badParent)) 10000)
    "non-strict reduction provenance accepted"

def testSourceStorageCases : IO Unit := do
  let imported ← referenceChecks
  resourceChecks
  let generated ← generationChecks
  tamperingChecks imported generated
  shrinkChecks

end Tests.SourceStorageCases
end

section
-- leanmerge: from Solcore.Test.SourceStorageEmitter
/-! Fixed-storage source emission and real checked ContractRuntime invocations.
The tests resolve the installed contract again after every committed call and
compare the returned Word plus both slots with a separate recurrence. Input
bytes always use the exact run(uint256) selector and one complete ABI Word. -/
set_option autoImplicit false

namespace Tests.SourceStorageEmitter

open Solcore.Core
open Solcore.ContractRuntime
open Solcore.Synthesis.Core
open Solcore.Synthesis.Source
open Solcore.Synthesis.Core.StorageContract (CheckedPlan)

private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)
def entry : Wire.Expr := .apply (.var 1) (.var 0)
def increment : Wire.Expr := .binary .wordAdd (.var 0) (word 1)

/-- Private memory begins at zero on every invocation; the arbitrary entry
subtracts one, so invoking this helper directly would also be observably wrong. -/
def privateStep : Wire.Expr :=
  .letE (.newCell .word (word 0))
    (.letE (.storeCell (.var 0) (.binary .wordAdd (.loadCell (.var 0)) (word 2)))
      (.binary .wordAdd (.var 2) (.loadCell (.var 1))))

def pairStep : Wire.Expr :=
  .letE (.newCell .word (.var 0))
    (.letE (.pair (.loadCell (.var 0))
      (.letE (.storeCell (.var 0) (word 2)) (.loadCell (.var 1))))
      (.binary .wordAdd (.first (.var 0)) (.second (.var 0))))

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def checked (helpers : List Wire.Expr) (body : Wire.Expr := entry) : IO CheckedPlan := do
  let some step := Aggregates.CheckedDAG.ofParts? helpers body |
    throw (IO.userError "storage step did not pass the checked aggregate profile")
  let some plan := CheckedPlan.ofParts? step |
    throw (IO.userError "storage wrapper did not pass the full Wire host checker")
  return plan

private def emitted (plan : CheckedPlan) : IO EmittedProgram :=
  match Storage.emit plan with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"storage source emission failed: {reprStr error}")

private def selectorBytes : Bytes := [0xa4, 0x44, 0xf5, 0xe9].toByteArray

private def inputData (input : Word) : HostStorageDriver.InputData := {
  bytes := selectorBytes ++ encodeWordBytesBE input
  size_lt_wordModulus := by
    simp only [ByteArray.size_append, encodeWordBytesBE_size]
    change 36 < wordModulus
    decide
}

private def target : Address := ⟨100, by decide⟩
private def caller : Address := ⟨200, by decide⟩

private def invocation (input : Word) : TopLevelInvocation := {
  target, caller, callValue := Word.zero, inputData := inputData input
}

private def sequenceCheck (plan : CheckedPlan) (inputs : List Word)
    (stepResult : Word → Word) (privateCells : Nat) : IO Unit := do
  let registry : CheckedContractRegistry :=
    ⟨fun address => if address == target then some plan.contract else none⟩
  let mut world := WorldState.empty.putAccount target (Account.empty.withCode plan.code)
  let mut expected0 := Word.zero
  let mut expected1 := Word.zero
  for input in inputs do
    ensure ((inputData input).bytes.size == 36 &&
      (inputData input).wordBE? (Word.ofNatModulo 4) == some input)
      "canonical ABI input did not decode to the original Word"
    let some ⟨contract, installed⟩ := registry.resolve? world target |
      throw (IO.userError "committed world no longer resolves the original checked contract")
    let call := invocation input
    match TopLevelExecution.run contract call installed 0 with
    | .outOfFuel _ _ _ _ _ _ => pure ()
    | .completed _ => throw (IO.userError "zero fuel was treated as a completed storage call")
    let next0 := stepResult (input.add expected0)
    let next1 := expected1.add (Word.ofNatModulo 1)
    match TopLevelExecution.run contract call installed 4000 with
    | .outOfFuel _ _ _ _ _ _ => throw (IO.userError "checked storage call exhausted the completion budget")
    | .completed result =>
        let expected := next0.add next1
        ensure (result.coreValue == .word expected && result.outcome == .returned (encodeWordBytesBE expected))
          "checked storage call returned the wrong recurrence or ABI bytes"
        ensure (result.coreStore.length == privateCells)
          "private helper cells survived across contract invocations"
        for cell in result.coreStore do
          ensure (cell == .word (Word.ofNatModulo 2)) "private helper cell contents changed"
        let some account := result.finalWorld.account? target |
          throw (IO.userError "committed storage account disappeared")
        ensure (account.storageRead Word.zero == next0 &&
          account.storageRead (Word.ofNatModulo 1) == next1 &&
          account.storageRead (Word.ofNatModulo 2) == Word.zero)
          "committed slots differ from the independent two-slot recurrence"
        ensure (account.balance == Word.zero && account.nonce == Word.zero)
          "storage-only invocation changed balance or nonce"
        if next0 == Word.zero then
          ensure ((account.storageValue? Word.zero).isNone) "zero storage write was not represented as deletion"
        ensure ((registry.resolve? result.finalWorld target).isSome)
          "storage commit changed the installed checked program"
        world := result.finalWorld
        expected0 := next0
        expected1 := next1

private def admissionChecks : IO Unit := do
  let basic ← checked [increment]
  let arbitrary ← checked [privateStep] (.binary .wordSub entry (word 1))
  let mixed ← checked [increment, pairStep] (.apply (.var 1) (.apply (.var 2) (.var 0)))
  for plan in [basic, arbitrary, mixed] do
    ensure (plan.program.check && plan.program.toCore.checkHost &&
      plan.program.resultType == .word && plan.contract.entryProfile == .returnWord)
      "storage plan escaped Wire/current host checking or changed its completion profile"
    ensure (plan.contract.code.program == plan.program.toCore) "contract admission replaced the original Core"
    ensure (StorageContract.canonicalNodes plan.step == Wire.programNodes plan.program &&
      Wire.programNodes plan.program == Wire.programNodes plan.step.program + StorageContract.programOverhead)
      "storage wrapper node overhead differs from the complete original Core"
    match plan.program.body with
    | .letE saved _ =>
        ensure (Wire.encodeExpr saved == Wire.encodeExpr plan.step.program.body)
          "storage wrapper did not capture the complete arbitrary entry once"
    | _ => throw (IO.userError "storage wrapper lost its initial entry-closure binding")
    let source ← emitted plan
    ensure (source == (← emitted plan)) "storage emission is nondeterministic"
    ensure (source.contractName == "SynthesizedStorage" && source.methodSignature == "run(uint256)" &&
      source.deployPath == ["SynthesizedStorageDeploy"] &&
      source.runtimePath == ["SynthesizedStorageDeploy", "SynthesizedStorage"])
      "storage wrapper metadata changed"
  -- Raw primitives join the existing opcode import only when a step uses them.
  let divided ← checked [.binary .wordDiv (.var 0) (word 1)]
  match Storage.emit divided with
  | .ok emitted => unless (emitted.source.splitOn "import {sload, sstore, div as sc_div, mod as sc_mod, ").length == 2 && (emitted.source.splitOn "    let sc_v3: word = sc_div(sc_v0, sc_v2);").length == 2 do
      throw (IO.userError "Storage emission lost the merged raw division alias or its snapshots")
  | .error error => throw (IO.userError s!"Storage raw division was rejected: {reprStr error}")

private def executionChecks : IO Unit := do
  let inputs := [Word.zero, Word.ofNatModulo 1, Word.ofNatModulo 3, Word.maximum,
    Word.zero, Word.ofNatModulo (2 ^ 255), Word.ofNatModulo 7]
  sequenceCheck (← checked [increment]) inputs (fun input => input.add (Word.ofNatModulo 1)) 0
  sequenceCheck (← checked [privateStep] (.binary .wordSub entry (word 1)))
    inputs (fun input => input.add (Word.ofNatModulo 1)) 1
  sequenceCheck (← checked [increment, pairStep] (.apply (.var 1) (.apply (.var 2) (.var 0))))
    inputs (fun input => input.add (Word.ofNatModulo 3)) 1
  sequenceCheck (← checked [increment] (.var 0))
    [Word.ofNatModulo 5, Word.ofNatModulo (wordModulus - 5), Word.zero] id 0
  sequenceCheck (← checked [increment] (word 0)) inputs (fun _ => Word.zero) 0

private def expectedBasic : String := String.intercalate "\n" [
  "import * from std;", "import * from std.dispatch;",
  "import {sload, sstore} from std.opcodes;", "",
  "function sc_fn0(sc_arg: word) returns (word) {",
  "    let sc_v0: word = 1;",
  "    let sc_v1: word = (sc_arg + sc_v0);",
  "    return sc_v1;", "}", "",
  "function sc_step(sc_arg: word) returns (word) {",
  "    let sc_v0: word = sc_fn0(sc_arg);",
  "    return sc_v0;", "}", "",
  "contract SynthesizedStorage {",
  "    function run(input: uint256) public returns (uint256) {",
  "        let sc_input: word = Typedef.rep(input);",
  "        let sc_old0: word = sload(0);",
  "        let sc_old1: word = sload(1);",
  "        let sc_computed: word = sc_step(sc_input + sc_old0);",
  "        sstore(0, sc_computed);",
  "        sstore(1, sc_old1 + 1);",
  "        let sc_final0: word = sload(0);",
  "        let sc_final1: word = sload(1);",
  "        return uint256(sc_final0 + sc_final1);", "    }", "}", ""]

private def contains (source fragment : String) : Bool := (source.splitOn fragment).length > 1

private def formattingChecks : IO Unit := do
  ensure ((← emitted (← checked [increment])).source == expectedBasic)
    "fixed storage protocol or source wrapper changed"
  let arbitrary ← emitted (← checked [increment] (.binary .wordAdd entry (word 10)))
  ensure (contains arbitrary.source (String.intercalate "\n" [
    "function sc_step(sc_arg: word) returns (word) {",
    "    let sc_v0: word = sc_fn0(sc_arg);", "    let sc_v1: word = 10;",
    "    let sc_v2: word = (sc_v0 + sc_v1);", "    return sc_v2;", "}"]))
    "storage wrapper ignored the arbitrary checked entry"
  ensure (Storage.emitterVersion == "solcore-source-storage-v2" &&
    Storage.wrapperVersion == "solcore-word-storage-contract-v1" &&
    Storage.selector == "0xa444f5e9" && StorageContract.version == "core-storage-contract-v1")
    "storage provenance changed"

def testSourceStorageEmitter : IO Unit := do
  admissionChecks
  executionChecks
  formattingChecks

end Tests.SourceStorageEmitter
end

section
-- leanmerge: from Solcore.Test.SourceStorageLedgerCases
/-! Sender-keyed ledger case regressions: exact replay, bounded generation from
an independent sequence stream, canonical transaction and declared-slot
boundaries, static alias kinds, the ledger protocol, and typed reductions over
steps, transactions, senders, recipients, amounts, inputs and flags. Expected
values here are test goldens only; cases and the observer never consume them. -/
set_option autoImplicit false

namespace Tests.SourceStorageLedgerCases
open Lean Solcore.Core Solcore.Synthesis.Core Solcore.Synthesis.Source
open Solcore.ContractRuntime (Address addressToWord)
open Solcore.Synthesis.Core.StorageLedger (CheckedPlan)
open Solcore.Synthesis.Stateful.StorageLedgerExecution (Transaction Bindings senders)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def get {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)
private def rejected {α : Type} (result : Except String α) (message : String) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError message)
private def field (value : Json) (name : String) : IO Json := get (value.getObjVal? name)
private def string (value : Json) (name : String) : IO String := get (value.getObjValAs? String name)
private def natural (value : Json) (name : String) : IO Nat := get (value.getObjValAs? Nat name)
private def rows (value : Json) (name : String := "transactions") : IO (Array Json) :=
  get (value.getObjValAs? (Array Json) name)
private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)
private def entry : Wire.Expr := .apply (.var 1) (.var 0)
private def bindings : Bindings := ⟨⟨17, by decide⟩, ⟨101, by decide⟩⟩
private def maximum : Nat := 2 ^ 256 - 1
private def sender (index : Nat) : Address := senders.getD index ⟨0, by decide⟩
private def key (index : Nat) : Nat := (addressToWord (sender index)).val

private def makePlan (body : Wire.Expr) (result : Wire.Expr := entry) : IO CheckedPlan := do
  let some graph := Aggregates.CheckedDAG.ofParts? [body] result |
    throw (IO.userError "ledger fixture failed step admission")
  let some plan := CheckedPlan.ofStep? graph | throw (IO.userError "ledger wrapper failed host admission")
  return plan
/-- Rows are `(sender position, flags, recipient, amount, input)`. -/
private def transactions (values : List (Nat × Nat × Nat × Nat × Nat)) : List Transaction :=
  values.zipIdx.map fun ((from_, flags, recipient, amount, input), index) =>
    ⟨"call-" ++ toString index, sender from_, Word.ofNatModulo flags, Word.ofNatModulo recipient,
      Word.ofNatModulo amount, Word.ofNatModulo input⟩
private def scenario (plan : CheckedPlan) (values : List (Nat × Nat × Nat × Nat × Nat)) :
    IO StorageLedger.CheckedScenario :=
  get (StorageLedger.checkedScenario plan (transactions values))
private def imported (value : StorageLedger.CheckedScenario) (fuel : Nat := 1000000) : IO Json :=
  get (StorageLedger.emitCase value (Json.mkObj [("kind", toJson "imported")]) fuel)

private def referenceChecks : IO Json := do
  let identity ← makePlan (.var 0)
  let value ← scenario identity [(0, 0, key 1, 1, 7), (1, 0, key 1, 2 ^ 64, 3), (2, 1, maximum, 7, 7)]
  let saved ← imported value
  ensure ((← field saved "observedSlots") == toJson ((value.observedSlots.map (·.val)).map toString) &&
    value.observedSlots.length == 5) "case did not declare the counter and every sender and recipient slot"
  ensure ((← get (StorageLedger.replayCase saved 1000000)) == saved) "imported ledger case did not replay"
  ensure ((← get (StorageLedger.replayCase (saved.setObjVal! "directCore" (toJson "forged")) 1000000)) == saved)
    "ledger replay consumed a stored expected result"
  let changed ← imported (← scenario identity [(1, 5, 0, 2, 9), (0, 2, key 2, 1, 1)])
  ensure ((← field saved "program") == (← field changed "program") &&
    (← string saved "source") == (← string changed "source"))
    "senders, recipients, amounts, inputs or flags were substituted into source or Core code"
  -- The first sender credits 7 and pays 1; the second sender's credit of 3 on
  -- top of the received 1 cannot pay 2^64; the third reverts on odd flags.
  let observed := StorageLedger.observe value bindings 1000000
  ensure ((← string observed "status") == "complete" &&
    ((← rows observed).map fun row => (row.getObjValAs? String "status").toOption) ==
      #[some "returned", some "reverted", some "reverted"])
    "ledger scenario did not follow its balances and flags"
  ensure ((← get (StorageLedger.checkProtocol value observed)) == ["returned", "reverted", "reverted"])
    "ledger history broke its protocol"
  let rebound ← rows (StorageLedger.observe value ⟨⟨33, by decide⟩, ⟨202, by decide⟩⟩ 1000000)
  ensure (rebound.map Solcore.Synthesis.Stateful.AccountStorage.unbound == (← rows observed).map Solcore.Synthesis.Stateful.AccountStorage.unbound &&
      rebound.all (Solcore.Synthesis.Stateful.AccountStorage.boundTo · [202]))
    "ledger rows changed with the deployer binding"
  -- A forged history that pays more than the amount, wraps the sender or
  -- reports a sufficient balance as insufficient breaks the protocol.
  let history ← rows observed
  let first := history[0]!
  let firstStorage ← get (first.getObjValAs? (Array Json) "committedStorage")
  let recipient := (Solcore.Synthesis.Stateful.StorageMappingExecution.entrySlot (Word.ofNatModulo (key 1))).val
  let some position := firstStorage.findIdx? (fun row => (row.getObjValAs? String "slot").toOption ==
    some (toString recipient)) | throw (IO.userError "recipient slot missing")
  let overpaid := first.setObjVal! "committedStorage"
    (.arr (firstStorage.set! position (firstStorage[position]!.setObjVal! "value" (toJson "2"))))
  rejected (StorageLedger.checkProtocol value (observed.setObjVal! "transactions" (.arr (history.set! 0 overpaid))))
    "an overpaid recipient passed the ledger protocol"
  let insufficient := history[1]!.setObjVal! "output"
    (toJson ("0x" ++ String.ofList (List.replicate 46 '0') ++ "010000000000000000"))
  rejected (StorageLedger.checkProtocol value (observed.setObjVal! "transactions" (.arr (history.set! 1 insufficient))))
    "an insufficient-balance revert reporting the amount passed the ledger protocol"
  ensure (StorageLedger.aliases (transactions [(0, 0, key 0, 0, 0), (1, 0, key 2, 0, 0), (2, 0, 0, 0, 0)]) ==
      ["self-transfer", "received-then-sent"] &&
    StorageLedger.aliases (transactions [(1, 0, 0, 0, 0), (1, 0, maximum, 0, 0)]) == ["repeated-sender"] &&
    StorageLedger.aliases (transactions [(2, 0, key 0, 0, 0), (0, 0, 0, 0, 0)]) == ["received-then-sent"] &&
    StorageLedger.aliases (transactions [(0, 0, key 1, 0, 0), (1, 0, 0, 0, 0)]) == ["received-then-sent"] &&
    StorageLedger.aliases (transactions [(1, 0, key 0, 0, 0), (0, 0, 0, 0, 0)]) == ["received-then-sent"] &&
    StorageLedger.aliases (transactions [(0, 0, 0, 0, 0), (1, 0, key 0, 0, 0)]) == [])
    "static ledger aliases changed"
  return saved

private def generationChecks : IO Json := do
  for seed in List.range 8 do
    let choices := StorageLedger.sequenceChoices (Seed.ofNat seed)
    ensure (choices.length == 13 &&
      (choices.zip [3, 3, 3, 6, 6, 6, 6, 6, 6, 6, 6, 6, 4]).all (fun (value, bound) => value < bound))
      "sequence choices escaped their banks"
    match StorageLedger.generatedScenario (Seed.ofNat seed) 384 with
    | .error _ => pure ()
    | .ok (value, origin) =>
        ensure (value.transactions.length == 3 &&
          Wire.programNodes value.program ≤ 384 + StorageLedger.hashNodes &&
          value.plan.step.helpers.length == 1 + seed % 3) "ledger recipe lost node/transaction/helper bounds"
        ensure (value.transactions.all fun tx => senders.contains tx.sender &&
            StorageLedger.recipientBank.contains tx.recipient && StorageLedger.amountBank.contains tx.amount &&
            StorageLedger.boundaryInputs.contains tx.input)
          "generated sender, recipient, amount or input escaped its bank"
        ensure ((value.transactions.map fun tx => tx.flags.val % 2 == 1) == StorageLedger.generatedParities (Seed.ofNat seed) &&
          value.transactions.all (fun tx => tx.flags.val < 2))
          "generated flags are not exactly their prescribed parities"
        ensure ((origin.getObjValAs? (List Nat) "sequenceChoices").toOption == some choices)
          "generated origin lost its sequence choices"
  rejected (StorageLedger.generatedScenario (Seed.ofNat 0) 513) "oversized node budget accepted"
  rejected (StorageLedger.generatedScenario (Seed.ofNat 0) Solcore.Synthesis.Core.StorageLedger.programOverhead)
    "undersized node budget accepted"
  let corpus := StorageLedger.generateCases (Seed.ofNat 0) 384 2 64 1000000
  ensure (corpus == StorageLedger.generateCases (Seed.ofNat 0) 384 2 64 1000000) "ledger generation nondeterministic"
  let generated ← rows corpus "cases"
  ensure (generated.size == 2 && (← natural corpus "attempted") ≤ 64 && (← string corpus "status") == "complete")
    "ledger count does not count complete scenarios"
  for saved in generated do
    ensure ((← get (StorageLedger.replayCase saved 1000000)) == saved) "generated ledger provenance did not replay"
    let low ← get (StorageLedger.replayCase saved 0)
    ensure ((← natural low "executionFuel") == 0 && (← field low "provenance") == (← field saved "provenance"))
      "fresh replay fuel changed the generation validation budget"
  let saved := generated[0]!
  let origin ← field (← field saved "provenance") "origin"
  let some seed := (← string origin "seed").toNat? | throw (IO.userError "invalid generated seed")
  let low := StorageLedger.generateCases (Seed.ofNat seed) 384 1 1 1000
  let excluded ← rows low "excluded"
  ensure ((← rows low "cases").isEmpty && (← string excluded[0]! "category") == "inconclusive-resource")
    "ledger generation resource exhaustion was not distinguished"
  ensure ((← natural (StorageLedger.generateCases (Seed.ofNat seed) 384 0 10 1000000) "attempted") == 0 &&
    (← rows (StorageLedger.generateCases (Seed.ofNat seed) 384 1 0 1000000) "cases").isEmpty)
    "ledger generator ignored count/attempt bounds"
  return saved

private def tamperingChecks (saved generated : Json) : IO Unit := do
  let first := (← rows saved)[0]!
  for (name, bad) in [("id", toJson ""), ("id", toJson "not valid"), ("sender", toJson "1"),
      ("sender", toJson ("0" ++ toString (key 0))), ("sender", toJson (toString (key 0 + 2 ^ 160))),
      ("flags", toJson "01"), ("recipient", toJson (toString (2 ^ 256))), ("amount", toJson "01"),
      ("input", toJson "07"), ("calldata", toJson "0x"), ("value", toJson "1"), ("extra", toJson true)] do
    rejected (StorageLedger.decodeTransactions (toJson [first.setObjVal! name bad]))
      "noncanonical ledger transaction accepted"
  -- A consistently re-encoded calldata cannot carry a different recipient than the row.
  let otherCalldata := Solcore.Synthesis.Stateful.StorageLedgerExecution.calldata Word.zero (Word.ofNatModulo 5)
    Word.zero Word.zero
  rejected (StorageLedger.decodeTransactions (toJson [first.setObjVal! "calldata" (toJson otherCalldata)]))
    "calldata that differs from the row's Words accepted"
  rejected (StorageLedger.decodeTransactions (toJson [first, first])) "duplicate transaction IDs accepted"
  rejected (StorageLedger.decodeTransactions (toJson ([] : List Json))) "empty transaction list accepted"
  rejected (StorageLedger.decodeTransactions
    (toJson (List.replicate (Solcore.Synthesis.Stateful.Sequence.maxTransactions + 1) first)))
    "unbounded transaction count accepted"
  let slots ← get (saved.getObjValAs? (Array Json) "observedSlots")
  for (name, bad) in [("initialState", Json.mkObj [("storage", toJson [first])]),
      ("observedSlots", .arr slots.pop), ("observedSlots", .arr (slots.push (toJson "1"))),
      ("observedSlots", .arr slots.reverse), ("executionFuel", toJson (10000001 : Nat)), ("ledgerPlan", Json.null),
      ("program", Wire.encodeProgram {resultType := .word, dataDefinitions := [], body := word 0})] do
    rejected (StorageLedger.caseProgram (saved.setObjVal! name bad)) "invalid ledger case boundary accepted"
  let provenance ← field generated "provenance"
  let origin ← field provenance "origin"
  let withOrigin := fun changed => generated.setObjVal! "provenance" (provenance.setObjVal! "origin" changed)
  for name in ["generatorVersion", "profileVersion", "functionVersion", "templateVersion", "stepProfileVersion",
      "stepFunctionVersion", "stepTemplateVersion", "emitterVersion", "wrapperVersion", "features"] do
    rejected (StorageLedger.replayCase (generated.setObjVal! "provenance" (provenance.setObjVal! name Json.null)) 1000000)
      "tampered ledger provenance accepted"
  for (name, bad) in [("seed", toJson "00"), ("finalSeed", toJson "bad"),
      ("maxProgramNodes", toJson (513 : Nat)), ("stepOrigin", Json.null), ("sequenceChoices", Json.null),
      ("sequenceFlags", Json.null), ("validationFuel", toJson (10000001 : Nat)), ("validationFuel", toJson (0 : Nat))] do
    rejected (StorageLedger.replayCase (withOrigin (origin.setObjVal! name bad)) 1000000)
      "tampered generated ledger recipe accepted"
  let plan ← field saved "ledgerPlan"
  rejected (StorageLedger.checkedPlan (plan.setObjVal! "extra" Json.null)) "noncanonical ledger plan accepted"
  rejected (StorageLedger.checkedPlan (plan.setObjVal! "schema" (toJson "solcore-lean.mapping-plan.v1")))
    "mapping plan schema accepted as a ledger plan"
  rejected (StorageLedger.replayCase (saved.setObjVal! "source" (toJson "stale")) 1000000) "stale source accepted"
  let contract ← field saved "contract"
  rejected (StorageLedger.replayCase (saved.setObjVal! "contract" (contract.setObjVal! "selector" (toJson "0x24b912e5"))) 1000000)
    "the mapping's three-Word selector accepted for the ledger ABI"
  rejected (StorageLedger.replayCase (saved.setObjVal! "schema" (toJson "solcore-lean.semantic-mapping-case.v1")) 1000000)
    "mapping case schema accepted by the ledger tool"

private def shrinkChecks : IO Unit := do
  let plan ← makePlan (Aggregate.template 3 (word 2))
  -- Moving the middle transaction to the first sender leaves one distinct sender.
  let value ← scenario plan [(0, 3, maximum, 2 ^ 70, 2 ^ 255), (2, 1, 2 ^ 160 - 1, 2 ^ 64, 3),
    (0, 2, key 1, 7, maximum)]
  let saved ← imported value
  let candidates ← get (StorageLedger.shrinkCases saved 2000 1000000)
  let result ← rows candidates "cases"
  ensure (!result.isEmpty && candidates == (← get (StorageLedger.shrinkCases saved 2000 1000000)))
    "ledger reductions were empty or nondeterministic"
  let mut removed := false
  let mut earlierSender := false
  let mut fewerSenders := false
  let mut loweredRecipient := false
  let mut loweredAmount := false
  let mut loweredInput := false
  let mut loweredFlags := false
  let mut changedStep := false
  let mut seen : List String := []
  for row in result do
    let reduced ← get (StorageLedger.caseProgram row)
    ensure (decide (StorageLedger.StrictlySmaller reduced value) && reduced.program.check &&
      reduced.plan.step.helpers.length == value.plan.step.helpers.length &&
      Aggregate.bindingInventory reduced.plan.step == Aggregate.bindingInventory value.plan.step &&
      decide ((reduced.transactions.map (·.id)).Sublist (value.transactions.map (·.id))))
      "ledger reduction lost strict complexity, host typing or stable scope/IDs"
    ensure ((← field row "observedSlots") == toJson ((reduced.observedSlots.map (·.val)).map toString))
      "a reduced ledger case did not rederive its declared slots"
    let identity := (Json.mkObj [("plan", StorageLedger.planJson reduced.plan),
      ("transactions", StorageLedger.transactionsJson reduced.transactions)]).compress
    ensure (!seen.contains identity) "duplicate ledger reduction"
    seen := identity :: seen
    removed := removed || reduced.transactions.length < value.transactions.length
    let pairs := reduced.transactions.zip value.transactions
    let sameCount := reduced.transactions.length == value.transactions.length
    ensure (pairs.all fun (left, right) => StorageLedger.senderPosition left.sender ≤ StorageLedger.senderPosition right.sender ||
      !sameCount) "a ledger reduction moved a transaction to a later sender"
    earlierSender := earlierSender || (sameCount && pairs.any fun (left, right) =>
      StorageLedger.senderPosition left.sender < StorageLedger.senderPosition right.sender)
    fewerSenders := fewerSenders || (sameCount &&
      StorageLedger.distinctSenders reduced.transactions < StorageLedger.distinctSenders value.transactions)
    loweredRecipient := loweredRecipient || (sameCount && pairs.any fun (left, right) => left.recipient.val < right.recipient.val)
    loweredAmount := loweredAmount || (sameCount && pairs.any fun (left, right) => left.amount.val < right.amount.val)
    loweredInput := loweredInput || (sameCount && pairs.any fun (left, right) => left.input.val < right.input.val)
    loweredFlags := loweredFlags || (sameCount && pairs.any fun (left, right) => left.flags.val < right.flags.val)
    changedStep := changedStep || StorageLedger.planJson reduced.plan != StorageLedger.planJson value.plan
  ensure (removed && earlierSender && fewerSenders && loweredRecipient && loweredAmount && loweredInput &&
    loweredFlags && changedStep)
    "ledger shrink omitted sequence/sender/recipient/amount/input/flags/step axes"
  for row in result.extract 0 3 do
    ensure ((← get (StorageLedger.replayCase row 1000000)) == row) "reduced ledger case did not replay"
  ensure ((← rows (← get (StorageLedger.shrinkCases saved 2 1000000)) "cases") == result.extract 0 2 &&
    (← rows (← get (StorageLedger.shrinkCases saved 0 1000000)) "cases").isEmpty) "ledger shrink limit changed ordering"
  let first := result[0]!
  let reduced ← get (StorageLedger.caseProgram first)
  let badParent := Json.mkObj [("kind", toJson "reduced"), ("parentPlan", StorageLedger.planJson reduced.plan),
    ("parentTransactions", StorageLedger.transactionsJson reduced.transactions)]
  let provenance ← field first "provenance"
  rejected (StorageLedger.replayCase (first.setObjVal! "provenance" (provenance.setObjVal! "origin" badParent)) 1000000)
    "non-strict ledger reduction provenance accepted"

def testSourceStorageLedgerCases : IO Unit := do
  let imported ← referenceChecks
  let generated ← generationChecks
  tamperingChecks imported generated
  shrinkChecks

end Tests.SourceStorageLedgerCases
end

section
-- leanmerge: from Solcore.Test.SourceStorageLedgerCorpus
/-! The fixed sender-keyed ledger corpus checks actual original Core histories
against independently computed expectations: status, payload and every
declared committed slot after every transaction, where the declared slots are
the counter and the `keccak256(1 ++ k)` entry slots of every transaction's
sender and recipient. Coverage describes the checked step AST, the senders,
recipients, amounts and inputs, distinct-sender counts, both revert causes and
static key aliasing. Source/Rust/EVM agreement is a separate external
validation. -/
set_option autoImplicit false

namespace Tests.SourceStorageLedgerCorpus
open Lean Solcore.Core Solcore.ContractRuntime Solcore.Synthesis.Core Solcore.Synthesis.Source
open Solcore.Synthesis.Stateful.StorageLedgerExecution (senders)

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
  ("generatorVersion", generatorVersion), ("profileVersion", StorageLedger.profileVersion),
  ("functionVersion", Solcore.Synthesis.Core.StorageLedger.version),
  ("templateVersion", StorageLedger.templateVersion), ("stepProfileVersion", Aggregate.profileVersion),
  ("stepFunctionVersion", Aggregates.version), ("stepTemplateVersion", Aggregate.templateVersion),
  ("emitterVersion", StorageLedger.emitterVersion), ("wrapperVersion", StorageLedger.wrapperVersion)]

private def words (values : List Word) : List String := values.map fun value => toString value.val

/-- Imported entries are emitted from their saved plan and sequence; generated
entries are regenerated from their seed. Both are checked by full replay. -/
private def entryCase (entry : Json) (fuel : Nat) : Except String Json := do
  if let .ok request := entry.getObjVal? "generation" then
    let some seed := (← request.getObjValAs? String "seed").toNat? | throw "invalid generation seed"
    let corpus := StorageLedger.generateCases (Seed.ofNat seed) (← request.getObjValAs? Nat "maxProgramNodes") 1 1 fuel
    require ((← string corpus "status") == "complete") "generated entry was excluded"
    let some saved := (← corpus.getObjValAs? (Array Json) "cases")[0]? | throw "generated entry has no case"
    return saved
  let plan ← StorageLedger.checkedPlan (← entry.getObjVal? "ledgerPlan")
  let scenario ← StorageLedger.checkedScenario plan (← StorageLedger.decodeTransactions (← entry.getObjVal? "transactions"))
  StorageLedger.emitCase scenario (Json.mkObj [("kind", toJson "imported")]) fuel

private def templates (saved : Json) : Except String (List Nat) := do
  let origin ← (← saved.getObjVal? "provenance").getObjVal? "origin"
  if (← string origin "kind") != "ledger-generated" then return []
  let helpers ← (← origin.getObjVal? "stepOrigin").getObjValAs? (List Json) "helpers"
  helpers.mapM fun helper => helper.getObjValAs? Nat "template"

def validateManifest (manifest : Json) (fuel : Nat := 1000000) : Except String Json := do
  require ((← string manifest "schema") == "solcore-lean.semantic-storage-corpus-manifest.v1" &&
    (← string manifest "profile") == "stateful-ledger" &&
    (← string manifest "coverageKind") == "step-core-ast-features") "unexpected ledger manifest scope"
  for (key, expected) in versions do
    require ((← string manifest key) == expected) ("ledger manifest changed " ++ key)
  let requiredFeatures ← strings manifest "requiredFeatures"
  require (sameMembers (← strings manifest "requiredInputs") (words StorageLedger.boundaryInputs))
    "ledger corpus must require all six boundary inputs"
  require (sameMembers (← strings manifest "requiredSenders") (senders.map fun sender => toString sender.val))
    "ledger corpus must require all three senders"
  require (sameMembers (← strings manifest "requiredRecipients") (words StorageLedger.recipientBank))
    "ledger corpus must require the whole recipient bank"
  require (sameMembers (← strings manifest "requiredAmounts") (words StorageLedger.amountBank))
    "ledger corpus must require the whole amount bank"
  require ((← manifest.getObjValAs? (List Nat) "requiredSenderCounts") == [1, 2, 3])
    "ledger corpus must require one to three distinct senders"
  require ((← strings manifest "requiredRevertCauses") == ["odd-flags", "insufficient-balance"])
    "ledger corpus must require both revert causes"
  require ((← strings manifest "requiredAliases") == StorageLedger.aliasCatalog)
    "ledger corpus must require the canonical alias catalog"
  require ((← manifest.getObjValAs? (List Nat) "requiredHelperCounts") == [1, 2, 3] &&
    (← manifest.getObjValAs? (List Nat) "requiredTransactionCounts") == [1, 2, 3])
    "ledger corpus must require one to three helpers and transactions"
  require ((← (← manifest.getObjVal? "generationRecipeRequirements").getObjValAs? (List Nat) "templates") == [0, 1, 2, 3])
    "ledger corpus must require all four step templates"
  require ((← strings manifest "requiredOutcomes") == ["returned", "reverted"]) "ledger corpus must require both outcomes"
  let requiredPatterns ← strings manifest "requiredCompletionPatterns"
  require (!requiredPatterns.isEmpty) "ledger corpus must require completion patterns"
  let entries ← manifest.getObjValAs? (Array Json) "cases"
  require (0 < entries.size && entries.size ≤ 64) "ledger corpus must contain 1..64 scenarios"
  let mut identifiers : List String := []
  let mut features : List String := []
  let mut inputs : List String := []
  let mut senderValues : List String := []
  let mut recipients : List String := []
  let mut amounts : List String := []
  let mut senderCounts : List Nat := []
  let mut causes : List String := []
  let mut aliases : List String := []
  let mut helperCounts : List Nat := []
  let mut transactionCounts : List Nat := []
  let mut templateUnion : List Nat := []
  let mut outcomes : List String := []
  let mut patterns : List String := []
  let mut transactionTotal := 0
  let mut slotTotal := 0
  for entry in entries do
    let identifier ← string entry "id"
    require (!identifiers.contains identifier) ("duplicate ledger corpus id " ++ identifier)
    identifiers := identifier :: identifiers
    let saved ← entryCase entry fuel
    require ((← StorageLedger.replayCase saved fuel) == saved) ("ledger corpus entry did not replay: " ++ identifier)
    let scenario ← StorageLedger.caseProgram saved
    if !(entry.getObjVal? "generation").isOk then
      require ((← saved.getObjVal? "ledgerPlan") == (← entry.getObjVal? "ledgerPlan") &&
        (← saved.getObjVal? "transactions") == (← entry.getObjVal? "transactions"))
        ("imported ledger entry is not canonical: " ++ identifier)
    let caseFeatures := (← (← saved.getObjVal? "provenance").getObjValAs? (List String) "features").eraseDups
    require (sameMembers (← strings entry "expectedFeatures") caseFeatures)
      ("ledger corpus features changed: " ++ identifier)
    -- The independently derived declaration must equal the observer's; the
    -- observer's own slots come from the separate ABI Keccak.
    let expectedSlots ← entry.getObjValAs? (List String) "expectedSlots"
    require (expectedSlots == words scenario.observedSlots &&
      (← saved.getObjValAs? (List String) "observedSlots") == expectedSlots)
      ("ledger declared slots differ from the independent derivation: " ++ identifier)
    let history := StorageLedger.observe scenario Solcore.Synthesis.Stateful.StorageExecution.fixtureBindings fuel
    require ((← string history "status") == "complete") ("ledger corpus history incomplete: " ++ identifier)
    let statuses ← StorageLedger.checkProtocol scenario history
    let observed ← history.getObjValAs? (List Json) "transactions"
    let expected ← entry.getObjValAs? (List Json) "expectedHistory"
    require (observed.length == expected.length) ("ledger expected history length changed: " ++ identifier)
    for (row, golden) in observed.zip expected do
      let actual := Json.mkObj [("id", ← row.getObjVal? "id"), ("status", ← row.getObjVal? "status"),
        ("output", ← row.getObjVal? "output"), ("committedStorage", ← row.getObjVal? "committedStorage")]
      require (actual == golden) ("original Core differs from the independent history: " ++ identifier ++ " " ++ actual.compress)
    for (status, tx) in statuses.zip scenario.transactions do
      if status == "reverted" then
        causes := (causes ++ [if StorageLedger.reverts tx then "odd-flags" else "insufficient-balance"]).eraseDups
    transactionTotal := transactionTotal + observed.length
    slotTotal := slotTotal + expectedSlots.length
    features := (features ++ caseFeatures).eraseDups
    inputs := (inputs ++ scenario.transactions.map fun tx => toString tx.input.val).eraseDups
    senderValues := (senderValues ++ scenario.transactions.map fun tx => toString tx.sender.val).eraseDups
    recipients := (recipients ++ scenario.transactions.map fun tx => toString tx.recipient.val).eraseDups
    amounts := (amounts ++ scenario.transactions.map fun tx => toString tx.amount.val).eraseDups
    senderCounts := (senderCounts ++ [StorageLedger.distinctSenders scenario.transactions]).eraseDups
    aliases := (aliases ++ StorageLedger.aliases scenario.transactions).eraseDups
    helperCounts := (helperCounts ++ [scenario.plan.step.helpers.length]).eraseDups
    transactionCounts := (transactionCounts ++ [scenario.transactions.length]).eraseDups
    templateUnion := (templateUnion ++ (← templates saved)).eraseDups
    outcomes := (outcomes ++ statuses).eraseDups
    patterns := (patterns ++ [String.intercalate "," statuses]).eraseDups
  require (requiredFeatures.all features.contains) "ledger corpus misses a required step feature"
  require ((words StorageLedger.boundaryInputs).all inputs.contains) "ledger corpus misses an input"
  require ((senders.map fun sender => toString sender.val).all senderValues.contains &&
    (words StorageLedger.recipientBank).all recipients.contains && (words StorageLedger.amountBank).all amounts.contains)
    "ledger corpus misses a sender, recipient or amount"
  require ([1, 2, 3].all senderCounts.contains) "ledger corpus misses a distinct-sender count"
  require (["odd-flags", "insufficient-balance"].all causes.contains) "ledger corpus misses a revert cause"
  require (StorageLedger.aliasCatalog.all aliases.contains) "ledger corpus misses an alias kind"
  require ([1, 2, 3].all helperCounts.contains && [1, 2, 3].all transactionCounts.contains)
    "ledger corpus misses a helper or transaction count"
  require ([0, 1, 2, 3].all templateUnion.contains) "ledger corpus misses a generated template"
  require (["returned", "reverted"].all outcomes.contains && requiredPatterns.all patterns.contains)
    "ledger corpus misses an observed outcome or completion pattern"
  return Json.mkObj [("profile", toJson "stateful-ledger"), ("scenarios", toJson entries.size),
    ("transactions", toJson transactionTotal), ("declaredSlots", toJson slotTotal),
    ("causes", toJson causes), ("aliases", toJson aliases), ("patterns", toJson patterns)]

private def checked {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def rejects {α : Type} (result : Except String α) (message : String) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError ("invalid ledger corpus unexpectedly passed: " ++ message))

/-- Solidity's order, `keccak256(key ++ 1)`, which the pinned std does not use. -/
private def soliditySlot (key : Word) : String :=
  toString ((decodeWordBytesBE? (Solcore.Abi.V1.Keccak256.hash
    (encodeWordBytesBE key ++ encodeWordBytesBE (Word.ofNatModulo 1)))).getD Word.zero).val

def testSourceStorageLedgerCorpus : IO Unit := do
  let manifest ← checked (Json.parse (← IO.FS.readFile "scripts/semantic-ledger-corpus.json"))
  let summary ← checked (validateManifest manifest)
  let entries ← checked (manifest.getObjValAs? (Array Json) "cases")
  let some first := entries[0]? | throw (IO.userError "missing first ledger case")
  let some generatedEntry := entries.find? (fun entry => (entry.getObjVal? "generation").isOk) |
    throw (IO.userError "missing generated ledger case")
  -- A tampered entry goes first, so the validator rejects it before it
  -- replays the untouched entries; coverage does not depend on order.
  let replace := fun (original changed : Json) => manifest.setObjVal! "cases"
    (.arr (#[changed] ++ entries.filter (· != original)))
  let history ← checked (first.getObjValAs? (Array Json) "expectedHistory")
  let withRow := fun (index : Nat) (row : Json) =>
    replace first (first.setObjVal! "expectedHistory" (.arr (history.set! index row)))
  let row := history[0]!
  rejects (validateManifest (withRow 0 (row.setObjVal! "output" (toJson ("0x" ++ String.ofList (List.replicate 64 'f'))))))
    "changed output"
  let storage ← checked (row.getObjValAs? (Array Json) "committedStorage")
  rejects (validateManifest (withRow 0 (row.setObjVal! "committedStorage"
    (.arr (storage.set! 0 (storage[0]!.setObjVal! "value" (toJson "7"))))))) "changed counter"
  rejects (validateManifest (withRow 0 (row.setObjVal! "committedStorage"
    (.arr (storage.set! 1 (storage[1]!.setObjVal! "value" (toJson "8"))))))) "changed entry"
  rejects (validateManifest (withRow 0 (row.setObjVal! "committedStorage" (.arr storage.pop)))) "dropped slot"
  let transactions ← checked (first.getObjValAs? (Array Json) "transactions")
  let decoded ← checked (StorageLedger.decodeTransactions (.arr #[transactions[0]!]))
  let some tx := decoded.head? | throw (IO.userError "missing first ledger transaction")
  let slots ← checked (first.getObjValAs? (Array Json) "expectedSlots")
  let senderSlot := toString (Solcore.Synthesis.Stateful.StorageLedgerExecution.senderSlot tx.sender).val
  let some position := slots.findIdx? (· == toJson senderSlot) | throw (IO.userError "sender slot missing")
  let solidity := toJson (soliditySlot (addressToWord tx.sender))
  rejects (validateManifest (replace first (first.setObjVal! "expectedSlots" (.arr (slots.set! position solidity)))))
    "Solidity-order declared sender slot"
  let some committed := storage.findIdx? (fun entry => (entry.getObjVal? "slot").toOption == some (toJson senderSlot)) |
    throw (IO.userError "committed sender slot missing")
  rejects (validateManifest (withRow 0 (row.setObjVal! "committedStorage"
    (.arr (storage.set! committed (storage[committed]!.setObjVal! "slot" solidity)))))) "Solidity-order committed slot"
  rejects (validateManifest (replace first (first.setObjVal! "expectedSlots" (.arr slots.pop)))) "missing declared slot"
  rejects (validateManifest (replace first (first.setObjVal! "expectedSlots" (.arr (slots.push (toJson "2"))))))
    "undeclared extra slot"
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr history.pop)))) "popped history"
  let generatedHistory ← checked (generatedEntry.getObjValAs? (Array Json) "expectedHistory")
  let generatedStatus ← checked (string generatedHistory[0]! "status")
  rejects (validateManifest (replace generatedEntry (generatedEntry.setObjVal! "expectedHistory"
    (.arr (generatedHistory.set! 0 (generatedHistory[0]!.setObjVal! "status"
      (toJson (if generatedStatus == "returned" then "reverted" else "returned")))))))) "flipped status"
  rejects (validateManifest (replace first (first.setObjVal! "transactions"
    (.arr (transactions.set! 0 (transactions[0]!.setObjVal! "recipient" (toJson "4"))))))) "recipient without calldata"
  -- Another fixed sender is canonical but no longer matches the saved slots and history.
  let other := senders.getD ((senders.idxOf tx.sender + 1) % 3) tx.sender
  rejects (validateManifest (replace first (first.setObjVal! "transactions"
    (.arr (transactions.set! 0 (transactions[0]!.setObjVal! "sender" (toJson (toString other.val)))))))) "other sender"
  -- A consistent recipient change with its own calldata is canonical but no
  -- longer matches the saved slots and history.
  let changedRecipient := Word.ofNatModulo (tx.recipient.val + 2)
  rejects (validateManifest (replace first (first.setObjVal! "transactions"
    (.arr (transactions.set! 0 ((transactions[0]!.setObjVal! "recipient" (toJson (toString changedRecipient.val))).setObjVal!
      "calldata" (toJson (Solcore.Synthesis.Stateful.StorageLedgerExecution.calldata tx.flags changedRecipient tx.amount
        tx.input))))))))
    "consistent recipient change"
  rejects (validateManifest (replace first (first.setObjVal! "expectedFeatures" (toJson ([] : List String))))) "features"
  rejects (validateManifest (replace generatedEntry (generatedEntry.setObjVal! "generation"
    (Json.mkObj [("seed", toJson "13"), ("maxProgramNodes", toJson (384 : Nat))])))) "changed seed"
  rejects (validateManifest (manifest.setObjVal! "cases" (.arr (#[first] ++ entries)))) "duplicate entry"
  for (key, value) in [
      ("profile", toJson "stateful-mapping"), ("templateVersion", toJson "forged"),
      ("functionVersion", toJson "core-keccak-mapping-contract-v1"),
      ("cases", .arr #[]), ("requiredInputs", toJson ([] : List String)),
      ("requiredSenders", toJson (["1"] : List String)), ("requiredRecipients", toJson (["0"] : List String)),
      ("requiredAmounts", toJson (["0", "1"] : List String)), ("requiredSenderCounts", toJson [1, 2]),
      ("requiredRevertCauses", toJson (["odd-flags"] : List String)), ("requiredHelperCounts", toJson [1, 2]),
      ("requiredAliases", toJson StorageLedger.aliasCatalog.reverse),
      ("requiredAliases", toJson (["self-transfer"] : List String)),
      ("requiredCompletionPatterns", toJson (["returned,returned,returned,returned"] : List String))] do
    rejects (validateManifest (manifest.setObjVal! key value)) key
  rejects (validateManifest manifest 0) "zero fuel"
  IO.println summary.compress

end Tests.SourceStorageLedgerCorpus
end

section
-- leanmerge: from Solcore.Test.SourceStorageLedgerEmitter
/-! Sender-keyed ledger protocol regressions through actual installed
ContractRuntime code. Every sender and recipient slot is checked against
Foundry's `cast keccak`. Golden histories are hand-computed: they cover two
senders, a sender spending what it received, an insufficient balance that
reverts with the credited balance, an odd-flags revert after a sufficient
transfer, a self-transfer and a wrapping payload. -/
set_option autoImplicit false

namespace Tests.SourceStorageLedgerEmitter

open Lean Solcore.Core Solcore.ContractRuntime Solcore.Synthesis.Core
open Solcore.Synthesis.Core.StorageLedger (CheckedPlan)
open Solcore.Synthesis.Source (EmittedProgram)
open Solcore.Synthesis.Stateful

private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)
private def entry : Wire.Expr := .apply (.var 1) (.var 0)
private def increment : Wire.Expr := .binary .wordAdd (.var 0) (word 1)
private def maximum : Nat := 2 ^ 256 - 1

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

/-- Anvil's first three default accounts, as decimal addresses. -/
private def s0 : Nat := 1390849295786071768276380950238675083608645509734
private def s1 : Nat := 642829559307850963015472508762062935916233390536
private def s2 : Nat := 344073830386746567427978432078835137280280269756

/-- `cast keccak` of the base slot one followed by each key, as decimal Words. -/
private def castSlots : List (Nat × Nat) := [
  (s0, 78570585682356430730071959328554860354235701529430903318287531160901974441362),
  (s1, 20716297545289759526027067151373890095476849666992757577977631027685962156767),
  (s2, 41239936133192089133110966148978916085433226010267689210672645629181891175976),
  (0, 78541660797044910968829902406342334108369226379826116161446442989268089806461),
  (2 ^ 160 - 1, 43383778025841973631710988075798902187352068724127397131308783529513977091473),
  (maximum, 71124947674796991739310909576881207026731009306364129481614628957978744178186)]

private def castSlot (key : Nat) : Nat := ((castSlots.find? (·.1 == key)).map (·.2)).getD 0

private def sender (address : Nat) : IO Address := do
  let some value := StorageLedgerExecution.senders.find? (·.val == address) |
    throw (IO.userError s!"{address} is not a fixed sender")
  return value

private def checked (helpers : List Wire.Expr) : IO CheckedPlan := do
  let some step := Aggregates.CheckedDAG.ofParts? helpers entry |
    throw (IO.userError "ledger step did not pass the checked aggregate profile")
  let some plan := CheckedPlan.ofStep? step |
    throw (IO.userError "ledger wrapper did not pass the full Wire host checker")
  return plan

private def emitted (plan : CheckedPlan) : IO EmittedProgram :=
  match Solcore.Synthesis.Source.StorageLedger.emit plan with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"ledger source emission failed: {reprStr error}")

private def slotChecks : IO Unit := do
  ensure ((StorageLedgerExecution.senders.map (·.val)) == [s0, s1, s2]) "the fixed senders changed"
  for (key, expected) in castSlots do
    ensure ((StorageMappingExecution.entrySlot (Word.ofNatModulo key)).val == expected)
      s!"entry slot of key {key} differs from cast keccak"
  for address in [s0, s1, s2] do
    ensure ((StorageLedgerExecution.senderSlot (← sender address)).val == castSlot address)
      s!"sender slot of {address} differs from cast keccak"
  ensure (StorageLedger.hashNodes == 2654 && StorageLedger.programOverhead == 115)
    "the Keccak closure or the ledger wrapper changed size"

private def transactions (rows : List (Nat × Nat × Nat × Nat × Nat)) : IO (List StorageLedgerExecution.Transaction) :=
  rows.zipIdx.mapM fun ((from_, flags, recipient, amount, input), index) => do
    return ⟨"tx-" ++ toString index, ← sender from_, Word.ofNatModulo flags, Word.ofNatModulo recipient,
      Word.ofNatModulo amount, Word.ofNatModulo input⟩

/-- Sixty-four lowercase hexadecimal digits, written without the observer's
byte encoder. -/
private def hexWord (value : Nat) : String :=
  let digits := Nat.toDigits 16 value
  "0x" ++ String.ofList (List.replicate (64 - digits.length) '0' ++ digits)

/-- The declared slots in increasing order with the values the golden assigns. -/
private def slotRows (slots : List Nat) (values : List (Nat × Nat)) : Json :=
  toJson ((slots.mergeSort (· ≤ ·)).map fun slot => Json.mkObj [("slot", toJson (toString slot)),
    ("value", toJson (toString (((values.find? (·.1 == slot)).map (·.2)).getD 0)))])

private def historyCheck (plan : CheckedPlan) (rows : List (Nat × Nat × Nat × Nat × Nat)) (slots : List Nat)
    (expected : List (String × Nat × List (Nat × Nat))) : IO Unit := do
  let history := StorageLedgerExecution.observe plan (← transactions rows) StorageExecution.fixtureBindings 1000000
  let observed := (history.getObjValAs? (List Json) "transactions").toOption.getD []
  ensure ((history.getObjValAs? String "status").toOption == some "complete" && observed.length == expected.length &&
    (history.getObjVal? "observedSlots").toOption == some (toJson ((slots.mergeSort (· ≤ ·)).map toString)) &&
    (history.getObjVal? "initialStorage").toOption == some (slotRows slots []))
    "ledger golden history did not complete from empty declared slots"
  for (row, (status, payload, values)) in observed.zip expected do
    ensure ((row.getObjValAs? String "status").toOption == some status &&
      (row.getObjValAs? String "output").toOption == some (hexWord payload) &&
      (row.getObjVal? "committedStorage").toOption == some (slotRows slots values))
      s!"ledger golden row changed: {row.compress}"

private def goldenChecks : IO Unit := do
  -- step(x) = x + 1. The first sender credits 8 and pays 1 to the second; a
  -- transfer of 2^64 from the credited 8 reverts with 8; the second sender
  -- spends what it received and its odd flags revert the sufficient transfer.
  let slots := [0, castSlot s0, castSlot s1, castSlot s2]
  historyCheck (← checked [increment]) [(s0, 0, s1, 1, 7), (s0, 0, s1, 2 ^ 64, 0), (s1, 1, s2, 1, 0)] slots [
    ("returned", 9, [(0, 1), (castSlot s0, 7), (castSlot s1, 1)]),
    ("reverted", 8, [(0, 1), (castSlot s0, 7), (castSlot s1, 1)]),
    ("reverted", 4, [(0, 1), (castSlot s0, 7), (castSlot s1, 1)])]
  -- The same transfer with even flags commits.
  historyCheck (← checked [increment]) [(s0, 0, s1, 1, 7), (s1, 0, s2, 1, 0)] [0, castSlot s0, castSlot s1, castSlot s2] [
    ("returned", 9, [(0, 1), (castSlot s0, 7), (castSlot s1, 1)]),
    ("returned", 4, [(0, 2), (castSlot s0, 7), (castSlot s1, 1), (castSlot s2, 1)])]
  -- step(x) = x. A self-transfer of the whole credit leaves it; crediting the
  -- maximum and paying 2^70 to the largest key wraps the returned sum to one.
  historyCheck (← checked [.var 0]) [(s2, 0, s2, 7, 7), (s1, 0, maximum, 2 ^ 70, maximum)]
    [0, castSlot s2, castSlot s1, castSlot maximum] [
    ("returned", 15, [(0, 1), (castSlot s2, 7)]),
    ("returned", 1, [(0, 2), (castSlot s2, 7), (castSlot s1, maximum - 2 ^ 70), (castSlot maximum, 2 ^ 70)])]

private def admissionChecks : IO Unit := do
  for plan in [← checked [increment], ← checked [.var 0]] do
    ensure (plan.program.check && plan.program.toCore.checkHost &&
      plan.program.resultType == .sum .word (.sum .word .word) && plan.contract.entryProfile == .wordOutcomeV1)
      "ledger plan lost full host checking or the typed outcome convention"
    ensure (plan.contract.code.program == plan.program.toCore) "admission replaced the original contract"
    ensure (StorageLedger.canonicalNodes plan.step == Wire.programNodes plan.program &&
      Wire.programNodes plan.program ==
        Wire.programNodes plan.step.program + StorageLedger.programOverhead + StorageLedger.hashNodes)
      "ledger wrapper overhead differs from the complete original Core"
    match plan.program.body with
    | .letE hash (.letE saved _) =>
        ensure (Wire.encodeExpr hash == Wire.encodeExpr StorageMapping.hashClosure &&
          Wire.encodeExpr saved == Wire.encodeExpr plan.step.program.body)
          "ledger wrapper lost its hash closure or ignored its arbitrary entry closure"
    | _ => throw (IO.userError "ledger wrapper lost its initial closure bindings")
    ensure ((← emitted plan) == (← emitted plan)) "ledger emission is nondeterministic"

private def expectedBasic : String := String.intercalate "\n" [
  "import * from std;", "import * from std.dispatch;",
  "import {caller, mstore, revert_} from std.opcodes;", "",
  "function sc_fn0(sc_arg: word) returns (word) {",
  "    let sc_v0: word = 1;", "    let sc_v1: word = (sc_arg + sc_v0);",
  "    return sc_v1;", "}", "",
  "function sc_step(sc_arg: word) returns (word) {",
  "    let sc_v0: word = sc_fn0(sc_arg);", "    return sc_v0;", "}", "",
  "contract SynthesizedLedger {",
  "    counter: word;",
  "    entries: mapping(word => word);",
  "",
  "    function run(flags: uint256, recipient: uint256, amount: uint256, input: uint256) public returns (uint256) {",
  "        let sc_flags: word = Typedef.rep(flags);",
  "        let sc_recipient: word = Typedef.rep(recipient);",
  "        let sc_amount: word = Typedef.rep(amount);",
  "        let sc_input: word = Typedef.rep(input);",
  "        let sc_sender: word = caller();",
  "        let sc_balance: word = entries[sc_sender] + sc_step(sc_input);",
  "        if (sc_amount > sc_balance) {", "            mstore(0, sc_balance);",
  "            revert_(0, 32);", "        }",
  "        entries[sc_sender] = sc_balance - sc_amount;",
  "        entries[sc_recipient] = entries[sc_recipient] + sc_amount;",
  "        counter = counter + 1;",
  "        let sc_result: word = entries[sc_sender] + entries[sc_recipient] + counter;",
  "        if ((sc_flags & 1) == 1) {", "            mstore(0, sc_result);",
  "            revert_(0, 32);", "        }",
  "        return uint256(sc_result);", "    }", "}", ""]

private def formattingChecks : IO Unit := do
  let source ← emitted (← checked [increment])
  ensure (source.source == expectedBasic) "ledger protocol source changed"
  ensure (source.contractName == "SynthesizedLedger" &&
    source.methodSignature == "run(uint256,uint256,uint256,uint256)" &&
    source.deployPath == ["SynthesizedLedgerDeploy"] &&
    source.runtimePath == ["SynthesizedLedgerDeploy", "SynthesizedLedger"])
    "ledger wrapper metadata changed"
  -- Raw primitives join the same opcode import only when a step uses them.
  let divided ← emitted (← checked [.binary .wordDiv (.var 0) (word 1)])
  ensure ((divided.source.splitOn "import {caller, mstore, revert_, div as sc_div, ").length == 2)
    "ledger emission lost the merged raw division alias"
  ensure (Solcore.Synthesis.Source.StorageLedger.emitterVersion == "solcore-source-sender-ledger-v1" &&
    Solcore.Synthesis.Source.StorageLedger.wrapperVersion == "solcore-word-sender-ledger-contract-v1" &&
    Solcore.Synthesis.Source.StorageLedger.selector == "0x15509d2b" &&
    StorageLedger.version == "core-sender-ledger-contract-v1") "ledger provenance changed"

private def observerChecks : IO Unit := do
  -- `cast calldata "run(uint256,uint256,uint256,uint256)" 1 <second sender> 7 9`
  ensure (StorageLedgerExecution.calldata (Word.ofNatModulo 1) (Word.ofNatModulo s1) (Word.ofNatModulo 7)
      (Word.ofNatModulo 9) ==
    "0x15509d2b" ++ String.ofList (List.replicate 63 '0') ++ "1" ++ String.ofList (List.replicate 24 '0') ++
      "70997970c51812dc3a010c7d01b50e0d17dc79c8" ++ String.ofList (List.replicate 63 '0') ++ "7" ++
      String.ofList (List.replicate 63 '0') ++ "9")
    "ledger calldata is not the selector and four Words"
  let calls ← transactions [(s0, 0, s1, 1, 7), (s1, 0, 0, 1, 3), (s0, 1, s0, 0, 0)]
  let declared := (StorageLedgerExecution.observedSlots calls).map (·.val)
  ensure (declared == [0, castSlot s0, castSlot s1, castSlot 0].mergeSort (· ≤ ·))
    "declared slots are not the counter and every sender's and recipient's entry slot in order"
  let plan ← checked [.var 0]
  -- The deployer in the bindings never acts; each transaction's sender does.
  let first := StorageLedgerExecution.observe plan calls StorageExecution.fixtureBindings 1000000
  let other := StorageLedgerExecution.observe plan calls ⟨⟨33, by decide⟩, ⟨202, by decide⟩⟩ 1000000
  let unbound := fun (history : Json) => ((history.getObjValAs? (List Json) "transactions").toOption.getD []).map
    Solcore.Synthesis.Stateful.AccountStorage.unbound
  ensure (unbound first == unbound other && !(unbound first).isEmpty &&
    (first.getObjValAs? String "status").toOption == some "complete")
    "ledger rows depended on the deployer instead of the senders"
  let moved ← transactions [(s2, 0, s1, 1, 7), (s1, 0, 0, 1, 3), (s0, 1, s0, 0, 0)]
  let swapped := StorageLedgerExecution.observe plan moved StorageExecution.fixtureBindings 1000000
  ensure ((swapped.getObjVal? "observedSlots").toOption != (first.getObjVal? "observedSlots").toOption)
    "a different sender kept the same declared slots"
  let exhausted := StorageLedgerExecution.observe plan calls StorageExecution.fixtureBindings 1000
  let rows := (exhausted.getObjValAs? (List Json) "transactions").toOption.getD []
  ensure ((exhausted.getObjValAs? String "status").toOption == some "incomplete" &&
    (exhausted.getObjValAs? (List String) "unexecuted").toOption == some ["tx-1", "tx-2"] && rows.length == 1 &&
    (rows[0]!.getObjValAs? String "status").toOption == some "out-of-fuel" &&
    (exhausted.getObjVal? "finalStorage").toOption == (exhausted.getObjVal? "initialStorage").toOption)
    "ledger observer conflated fuel exhaustion with completion"
  ensure ((first.getObjValAs? String "schema").toOption == some "solcore-lean.ledger-history.v2")
    "history did not declare its schema"

def testSourceStorageLedgerEmitter : IO Unit := do
  slotChecks
  admissionChecks
  goldenChecks
  formattingChecks
  observerChecks

end Tests.SourceStorageLedgerEmitter
end

section
-- leanmerge: from Solcore.Test.SourceStorageMappingCases
/-! Keccak-mapping case regressions: exact replay, bounded generation from an
independent sequence stream, canonical transaction and declared-slot
boundaries, static alias kinds, and typed reductions over steps,
transactions, keys, inputs and flags. Expected values here are test goldens
only; cases and the observer never consume them. -/
set_option autoImplicit false

namespace Tests.SourceStorageMappingCases
open Lean Solcore.Core Solcore.Synthesis.Core Solcore.Synthesis.Source
open Solcore.Synthesis.Core.StorageMapping (CheckedPlan)
open Solcore.Synthesis.Stateful.StorageMappingExecution (Transaction Bindings)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def get {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)
private def rejected {α : Type} (result : Except String α) (message : String) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError message)
private def field (value : Json) (name : String) : IO Json := get (value.getObjVal? name)
private def string (value : Json) (name : String) : IO String := get (value.getObjValAs? String name)
private def natural (value : Json) (name : String) : IO Nat := get (value.getObjValAs? Nat name)
private def rows (value : Json) (name : String := "transactions") : IO (Array Json) :=
  get (value.getObjValAs? (Array Json) name)
private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)
private def entry : Wire.Expr := .apply (.var 1) (.var 0)
private def bindings : Bindings := ⟨⟨17, by decide⟩, ⟨101, by decide⟩⟩
private def maximum : Nat := 2 ^ 256 - 1

private def makePlan (body : Wire.Expr) (result : Wire.Expr := entry) : IO CheckedPlan := do
  let some graph := Aggregates.CheckedDAG.ofParts? [body] result |
    throw (IO.userError "mapping fixture failed step admission")
  let some plan := CheckedPlan.ofStep? graph | throw (IO.userError "mapping wrapper failed host admission")
  return plan
private def transactions (values : List (Nat × Nat × Nat)) : List Transaction :=
  values.zipIdx.map fun ((flags, key, input), index) =>
    ⟨"call-" ++ toString index, Word.ofNatModulo flags, Word.ofNatModulo key, Word.ofNatModulo input⟩
private def scenario (plan : CheckedPlan) (values : List (Nat × Nat × Nat)) : IO StorageMapping.CheckedScenario :=
  get (StorageMapping.checkedScenario plan (transactions values))
private def imported (value : StorageMapping.CheckedScenario) (fuel : Nat := 1000000) : IO Json :=
  get (StorageMapping.emitCase value (Json.mkObj [("kind", toJson "imported")]) fuel)

private def referenceChecks : IO Json := do
  let identity ← makePlan (.var 0)
  let value ← scenario identity [(0, 6, 1), (1, 7, 3), (2, maximum, 7)]
  let saved ← imported value
  ensure ((← field saved "observedSlots") == toJson ((value.observedSlots.map (·.val)).map toString) &&
    value.observedSlots.length == 6) "case did not declare the counter and six entry slots"
  ensure ((← get (StorageMapping.replayCase saved 1000000)) == saved) "imported mapping case did not replay"
  ensure ((← get (StorageMapping.replayCase (saved.setObjVal! "directCore" (toJson "forged")) 1000000)) == saved)
    "mapping replay consumed a stored expected result"
  let changed ← imported (← scenario identity [(5, 0, 2), (2, 1, 9)])
  ensure ((← field saved "program") == (← field changed "program") &&
    (← string saved "source") == (← string changed "source"))
    "keys, inputs or flags were substituted into source or Core code"
  let observed := StorageMapping.observe value bindings 1000000
  ensure ((← string observed "status") == "complete" &&
    ((← rows observed).map fun row => (row.getObjValAs? String "status").toOption) ==
      #[some "returned", some "reverted", some "returned"])
    "mapping scenario did not follow its flags parities"
  ensure ((← get (StorageMapping.checkProtocol value observed)) == ["returned", "reverted", "returned"])
    "mapping history broke its counter or sum protocol"
  let rebound ← rows (StorageMapping.observe value ⟨⟨33, by decide⟩, ⟨202, by decide⟩⟩ 1000000)
  ensure (rebound.map Solcore.Synthesis.Stateful.AccountStorage.unbound == (← rows observed).map Solcore.Synthesis.Stateful.AccountStorage.unbound &&
      rebound.all (Solcore.Synthesis.Stateful.AccountStorage.boundTo · [202]))
    "address-independent mapping profile changed with bindings"
  ensure (StorageMapping.aliases (transactions [(0, 6, 0), (0, 7, 0), (0, 6, 0)]) == ["repeated-key", "successor-key"] &&
    StorageMapping.aliases (transactions [(0, maximum, 0)]) == ["wrapped-successor"] &&
    StorageMapping.aliases (transactions [(0, 0, 0), (0, 2 ^ 255, 0)]) == [])
    "static mapping aliases changed"
  return saved

private def generationChecks : IO Json := do
  for seed in List.range 8 do
    let choices := StorageMapping.sequenceChoices (Seed.ofNat seed)
    ensure (choices.length == 7 && (choices.zip [6, 6, 6, 6, 6, 6, 4]).all (fun (value, bound) => value < bound))
      "sequence choices escaped their banks"
    match StorageMapping.generatedScenario (Seed.ofNat seed) 384 with
    | .error _ => pure ()
    | .ok (value, origin) =>
        ensure (value.transactions.length == 3 &&
          Wire.programNodes value.program ≤ 384 + StorageMapping.hashNodes &&
          value.plan.step.helpers.length == 1 + seed % 3) "mapping recipe lost node/transaction/helper bounds"
        ensure (value.transactions.all fun tx => StorageMapping.keyBank.contains tx.key && StorageMapping.boundaryInputs.contains tx.input)
          "generated key or input escaped its bank"
        ensure ((value.transactions.map fun tx => tx.flags.val % 2 == 1) == StorageMapping.generatedParities (Seed.ofNat seed) &&
          value.transactions.all (fun tx => tx.flags.val < 2))
          "generated flags are not exactly their prescribed parities"
        ensure ((origin.getObjValAs? (List Nat) "sequenceChoices").toOption == some choices)
          "generated origin lost its sequence choices"
  rejected (StorageMapping.generatedScenario (Seed.ofNat 0) 513) "oversized node budget accepted"
  rejected (StorageMapping.generatedScenario (Seed.ofNat 0) Solcore.Synthesis.Core.StorageMapping.programOverhead)
    "undersized node budget accepted"
  let corpus := StorageMapping.generateCases (Seed.ofNat 0) 384 2 64 1000000
  ensure (corpus == StorageMapping.generateCases (Seed.ofNat 0) 384 2 64 1000000) "mapping generation nondeterministic"
  let generated ← rows corpus "cases"
  ensure (generated.size == 2 && (← natural corpus "attempted") ≤ 64 && (← string corpus "status") == "complete")
    "mapping count does not count complete scenarios"
  for saved in generated do
    ensure ((← get (StorageMapping.replayCase saved 1000000)) == saved) "generated mapping provenance did not replay"
    let low ← get (StorageMapping.replayCase saved 0)
    ensure ((← natural low "executionFuel") == 0 && (← field low "provenance") == (← field saved "provenance"))
      "fresh replay fuel changed the generation validation budget"
  let saved := generated[0]!
  let origin ← field (← field saved "provenance") "origin"
  let some seed := (← string origin "seed").toNat? | throw (IO.userError "invalid generated seed")
  let low := StorageMapping.generateCases (Seed.ofNat seed) 384 1 1 1000
  let excluded ← rows low "excluded"
  ensure ((← rows low "cases").isEmpty && (← string excluded[0]! "category") == "inconclusive-resource")
    "mapping generation resource exhaustion was not distinguished"
  ensure ((← natural (StorageMapping.generateCases (Seed.ofNat seed) 384 0 10 1000000) "attempted") == 0 &&
    (← rows (StorageMapping.generateCases (Seed.ofNat seed) 384 1 0 1000000) "cases").isEmpty)
    "mapping generator ignored count/attempt bounds"
  return saved

private def tamperingChecks (saved generated : Json) : IO Unit := do
  let first := (← rows saved)[0]!
  for (name, bad) in [("id", toJson ""), ("id", toJson "not valid"), ("flags", toJson "01"),
      ("key", toJson "06"), ("key", toJson (toString (2 ^ 256))), ("input", toJson "01"),
      ("calldata", toJson "0x"), ("value", toJson "1"), ("extra", toJson true)] do
    rejected (StorageMapping.decodeTransactions (toJson [first.setObjVal! name bad]))
      "noncanonical mapping transaction accepted"
  rejected (StorageMapping.decodeTransactions (toJson [first, first])) "duplicate transaction IDs accepted"
  rejected (StorageMapping.decodeTransactions (toJson ([] : List Json))) "empty transaction list accepted"
  rejected (StorageMapping.decodeTransactions
    (toJson (List.replicate (Solcore.Synthesis.Stateful.Sequence.maxTransactions + 1) first)))
    "unbounded transaction count accepted"
  let slots ← get (saved.getObjValAs? (Array Json) "observedSlots")
  for (name, bad) in [("initialState", Json.mkObj [("storage", toJson [first])]),
      ("observedSlots", .arr slots.pop), ("observedSlots", .arr (slots.push (toJson "1"))),
      ("observedSlots", .arr slots.reverse), ("executionFuel", toJson (10000001 : Nat)), ("mappingPlan", Json.null),
      ("program", Wire.encodeProgram {resultType := .word, dataDefinitions := [], body := word 0})] do
    rejected (StorageMapping.caseProgram (saved.setObjVal! name bad)) "invalid mapping case boundary accepted"
  let provenance ← field generated "provenance"
  let origin ← field provenance "origin"
  let withOrigin := fun changed => generated.setObjVal! "provenance" (provenance.setObjVal! "origin" changed)
  for name in ["generatorVersion", "profileVersion", "functionVersion", "templateVersion", "stepProfileVersion",
      "stepFunctionVersion", "stepTemplateVersion", "emitterVersion", "wrapperVersion", "features"] do
    rejected (StorageMapping.replayCase (generated.setObjVal! "provenance" (provenance.setObjVal! name Json.null)) 1000000)
      "tampered mapping provenance accepted"
  for (name, bad) in [("seed", toJson "00"), ("finalSeed", toJson "bad"),
      ("maxProgramNodes", toJson (513 : Nat)), ("stepOrigin", Json.null), ("sequenceChoices", Json.null),
      ("sequenceCompletions", Json.null), ("validationFuel", toJson (10000001 : Nat)), ("validationFuel", toJson (0 : Nat))] do
    rejected (StorageMapping.replayCase (withOrigin (origin.setObjVal! name bad)) 1000000)
      "tampered generated mapping recipe accepted"
  let plan ← field saved "mappingPlan"
  rejected (StorageMapping.checkedPlan (plan.setObjVal! "extra" Json.null)) "noncanonical mapping plan accepted"
  rejected (StorageMapping.checkedPlan (plan.setObjVal! "schema" (toJson "solcore-lean.keyed-storage-plan.v1")))
    "keyed plan schema accepted as a mapping plan"
  rejected (StorageMapping.replayCase (saved.setObjVal! "source" (toJson "stale")) 1000000) "stale source accepted"
  let contract ← field saved "contract"
  rejected (StorageMapping.replayCase (saved.setObjVal! "contract" (contract.setObjVal! "selector" (toJson "0x7357f5d2"))) 1000000)
    "the keyed two-Word selector accepted for the mapping ABI"
  rejected (StorageMapping.replayCase (saved.setObjVal! "schema" (toJson "solcore-lean.semantic-keyed-storage-case.v1")) 1000000)
    "keyed case schema accepted by the mapping tool"

private def shrinkChecks : IO Unit := do
  let plan ← makePlan (Aggregate.template 3 (word 2))
  let value ← scenario plan [(3, 7, 2 ^ 255), (1, maximum, 3), (2, 2 ^ 255, maximum)]
  let saved ← imported value
  let candidates ← get (StorageMapping.shrinkCases saved 2000 1000000)
  let result ← rows candidates "cases"
  ensure (!result.isEmpty && candidates == (← get (StorageMapping.shrinkCases saved 2000 1000000)))
    "mapping reductions were empty or nondeterministic"
  let mut removed := false
  let mut loweredKey := false
  let mut loweredInput := false
  let mut loweredFlags := false
  let mut changedStep := false
  let mut seen : List String := []
  for row in result do
    let reduced ← get (StorageMapping.caseProgram row)
    ensure (decide (StorageMapping.StrictlySmaller reduced value) && reduced.program.check &&
      reduced.plan.step.helpers.length == value.plan.step.helpers.length &&
      Aggregate.bindingInventory reduced.plan.step == Aggregate.bindingInventory value.plan.step &&
      decide ((reduced.transactions.map (·.id)).Sublist (value.transactions.map (·.id))))
      "mapping reduction lost strict complexity, host typing or stable scope/IDs"
    ensure ((← field row "observedSlots") == toJson ((reduced.observedSlots.map (·.val)).map toString))
      "a reduced mapping case did not rederive its declared slots"
    let identity := (Json.mkObj [("plan", StorageMapping.planJson reduced.plan),
      ("transactions", StorageMapping.transactionsJson reduced.transactions)]).compress
    ensure (!seen.contains identity) "duplicate mapping reduction"
    seen := identity :: seen
    removed := removed || reduced.transactions.length < value.transactions.length
    let pairs := reduced.transactions.zip value.transactions
    let sameCount := reduced.transactions.length == value.transactions.length
    loweredKey := loweredKey || (sameCount && pairs.any fun (left, right) => left.key.val < right.key.val)
    loweredInput := loweredInput || (sameCount && pairs.any fun (left, right) => left.input.val < right.input.val)
    loweredFlags := loweredFlags || (sameCount && pairs.any fun (left, right) => left.flags.val < right.flags.val)
    changedStep := changedStep || StorageMapping.planJson reduced.plan != StorageMapping.planJson value.plan
  ensure (removed && loweredKey && loweredInput && loweredFlags && changedStep)
    "mapping shrink omitted sequence/key/input/flags/step axes"
  for row in result.extract 0 3 do
    ensure ((← get (StorageMapping.replayCase row 1000000)) == row) "reduced mapping case did not replay"
  ensure ((← rows (← get (StorageMapping.shrinkCases saved 2 1000000)) "cases") == result.extract 0 2 &&
    (← rows (← get (StorageMapping.shrinkCases saved 0 1000000)) "cases").isEmpty) "mapping shrink limit changed ordering"
  let first := result[0]!
  let reduced ← get (StorageMapping.caseProgram first)
  let badParent := Json.mkObj [("kind", toJson "reduced"), ("parentPlan", StorageMapping.planJson reduced.plan),
    ("parentTransactions", StorageMapping.transactionsJson reduced.transactions)]
  let provenance ← field first "provenance"
  rejected (StorageMapping.replayCase (first.setObjVal! "provenance" (provenance.setObjVal! "origin" badParent)) 1000000)
    "non-strict mapping reduction provenance accepted"

def testSourceStorageMappingCases : IO Unit := do
  let imported ← referenceChecks
  let generated ← generationChecks
  tamperingChecks imported generated
  shrinkChecks

end Tests.SourceStorageMappingCases
end

section
-- leanmerge: from Solcore.Test.SourceStorageMappingCorpus
/-! The fixed Keccak-mapping corpus checks actual original Core histories
against independently computed expectations: status, payload and every
declared committed slot after every transaction, where the declared slots are
the counter and the `keccak256(1 ++ key)` entry slots of every key and wrapping
successor. Coverage describes the checked step AST, the transaction keys,
inputs and completions, and static key aliasing. Source/Rust/EVM agreement is
a separate external validation. -/
set_option autoImplicit false

namespace Tests.SourceStorageMappingCorpus
open Lean Solcore.Core Solcore.ContractRuntime Solcore.Synthesis.Core Solcore.Synthesis.Source

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
  ("generatorVersion", generatorVersion), ("profileVersion", StorageMapping.profileVersion),
  ("functionVersion", Solcore.Synthesis.Core.StorageMapping.version),
  ("templateVersion", StorageMapping.templateVersion), ("stepProfileVersion", Aggregate.profileVersion),
  ("stepFunctionVersion", Aggregates.version), ("stepTemplateVersion", Aggregate.templateVersion),
  ("emitterVersion", StorageMapping.emitterVersion), ("wrapperVersion", StorageMapping.wrapperVersion)]

private def words (values : List Word) : List String := values.map fun value => toString value.val

/-- Imported entries are emitted from their saved plan and sequence; generated
entries are regenerated from their seed. Both are checked by full replay. -/
private def entryCase (entry : Json) (fuel : Nat) : Except String Json := do
  if let .ok request := entry.getObjVal? "generation" then
    let some seed := (← request.getObjValAs? String "seed").toNat? | throw "invalid generation seed"
    let corpus := StorageMapping.generateCases (Seed.ofNat seed) (← request.getObjValAs? Nat "maxProgramNodes") 1 1 fuel
    require ((← string corpus "status") == "complete") "generated entry was excluded"
    let some saved := (← corpus.getObjValAs? (Array Json) "cases")[0]? | throw "generated entry has no case"
    return saved
  let plan ← StorageMapping.checkedPlan (← entry.getObjVal? "mappingPlan")
  let scenario ← StorageMapping.checkedScenario plan (← StorageMapping.decodeTransactions (← entry.getObjVal? "transactions"))
  StorageMapping.emitCase scenario (Json.mkObj [("kind", toJson "imported")]) fuel

private def templates (saved : Json) : Except String (List Nat) := do
  let origin ← (← saved.getObjVal? "provenance").getObjVal? "origin"
  if (← string origin "kind") != "mapping-generated" then return []
  let helpers ← (← origin.getObjVal? "stepOrigin").getObjValAs? (List Json) "helpers"
  helpers.mapM fun helper => helper.getObjValAs? Nat "template"

def validateManifest (manifest : Json) (fuel : Nat := 1000000) : Except String Json := do
  require ((← string manifest "schema") == "solcore-lean.semantic-storage-corpus-manifest.v1" &&
    (← string manifest "profile") == "stateful-mapping" &&
    (← string manifest "coverageKind") == "step-core-ast-features") "unexpected mapping manifest scope"
  for (key, expected) in versions do
    require ((← string manifest key) == expected) ("mapping manifest changed " ++ key)
  let requiredFeatures ← strings manifest "requiredFeatures"
  let requiredInputs ← strings manifest "requiredInputs"
  require (sameMembers requiredInputs (words StorageMapping.boundaryInputs))
    "mapping corpus must require all six boundary inputs"
  let requiredKeys ← strings manifest "requiredKeys"
  require (sameMembers requiredKeys (words StorageMapping.keyBank)) "mapping corpus must require the whole key bank"
  require ((← strings manifest "requiredAliases") == StorageMapping.aliasCatalog)
    "mapping corpus must require the canonical alias catalog"
  require ((← manifest.getObjValAs? (List Nat) "requiredHelperCounts") == [1, 2, 3] &&
    (← manifest.getObjValAs? (List Nat) "requiredTransactionCounts") == [1, 2, 3])
    "mapping corpus must require one to three helpers and transactions"
  require ((← (← manifest.getObjVal? "generationRecipeRequirements").getObjValAs? (List Nat) "templates") == [0, 1, 2, 3])
    "mapping corpus must require all four step templates"
  require ((← strings manifest "requiredOutcomes") == ["returned", "reverted"]) "mapping corpus must require both outcomes"
  let requiredPatterns ← strings manifest "requiredCompletionPatterns"
  require (!requiredPatterns.isEmpty) "mapping corpus must require completion patterns"
  let entries ← manifest.getObjValAs? (Array Json) "cases"
  require (0 < entries.size && entries.size ≤ 64) "mapping corpus must contain 1..64 scenarios"
  let mut identifiers : List String := []
  let mut features : List String := []
  let mut inputs : List String := []
  let mut keys : List String := []
  let mut aliases : List String := []
  let mut helperCounts : List Nat := []
  let mut transactionCounts : List Nat := []
  let mut templateUnion : List Nat := []
  let mut outcomes : List String := []
  let mut patterns : List String := []
  let mut transactionTotal := 0
  let mut slotTotal := 0
  for entry in entries do
    let identifier ← string entry "id"
    require (!identifiers.contains identifier) ("duplicate mapping corpus id " ++ identifier)
    identifiers := identifier :: identifiers
    let saved ← entryCase entry fuel
    require ((← StorageMapping.replayCase saved fuel) == saved) ("mapping corpus entry did not replay: " ++ identifier)
    let scenario ← StorageMapping.caseProgram saved
    if !(entry.getObjVal? "generation").isOk then
      require ((← saved.getObjVal? "mappingPlan") == (← entry.getObjVal? "mappingPlan") &&
        (← saved.getObjVal? "transactions") == (← entry.getObjVal? "transactions"))
        ("imported mapping entry is not canonical: " ++ identifier)
    let caseFeatures := (← (← saved.getObjVal? "provenance").getObjValAs? (List String) "features").eraseDups
    require (sameMembers (← strings entry "expectedFeatures") caseFeatures)
      ("mapping corpus features changed: " ++ identifier)
    -- The independently derived declaration must equal the observer's; the
    -- observer's own slots come from the separate ABI Keccak.
    let expectedSlots ← entry.getObjValAs? (List String) "expectedSlots"
    require (expectedSlots == words scenario.observedSlots &&
      (← saved.getObjValAs? (List String) "observedSlots") == expectedSlots)
      ("mapping declared slots differ from the independent derivation: " ++ identifier)
    let history := StorageMapping.observe scenario Solcore.Synthesis.Stateful.StorageExecution.fixtureBindings fuel
    require ((← string history "status") == "complete") ("mapping corpus history incomplete: " ++ identifier)
    let statuses ← StorageMapping.checkProtocol scenario history
    let observed ← history.getObjValAs? (List Json) "transactions"
    let expected ← entry.getObjValAs? (List Json) "expectedHistory"
    require (observed.length == expected.length) ("mapping expected history length changed: " ++ identifier)
    for (row, golden) in observed.zip expected do
      let actual := Json.mkObj [("id", ← row.getObjVal? "id"), ("status", ← row.getObjVal? "status"),
        ("output", ← row.getObjVal? "output"), ("committedStorage", ← row.getObjVal? "committedStorage")]
      require (actual == golden) ("original Core differs from the independent history: " ++ identifier ++ " " ++ actual.compress)
    transactionTotal := transactionTotal + observed.length
    slotTotal := slotTotal + expectedSlots.length
    features := (features ++ caseFeatures).eraseDups
    inputs := (inputs ++ scenario.transactions.map fun tx => toString tx.input.val).eraseDups
    keys := (keys ++ scenario.transactions.map fun tx => toString tx.key.val).eraseDups
    aliases := (aliases ++ StorageMapping.aliases scenario.transactions).eraseDups
    helperCounts := (helperCounts ++ [scenario.plan.step.helpers.length]).eraseDups
    transactionCounts := (transactionCounts ++ [scenario.transactions.length]).eraseDups
    templateUnion := (templateUnion ++ (← templates saved)).eraseDups
    outcomes := (outcomes ++ statuses).eraseDups
    patterns := (patterns ++ [String.intercalate "," statuses]).eraseDups
  require (requiredFeatures.all features.contains) "mapping corpus misses a required step feature"
  require (requiredInputs.all inputs.contains && requiredKeys.all keys.contains) "mapping corpus misses an input or key"
  require (StorageMapping.aliasCatalog.all aliases.contains) "mapping corpus misses an alias kind"
  require ([1, 2, 3].all helperCounts.contains && [1, 2, 3].all transactionCounts.contains)
    "mapping corpus misses a helper or transaction count"
  require ([0, 1, 2, 3].all templateUnion.contains) "mapping corpus misses a generated template"
  require (["returned", "reverted"].all outcomes.contains && requiredPatterns.all patterns.contains)
    "mapping corpus misses an observed outcome or completion pattern"
  return Json.mkObj [("profile", toJson "stateful-mapping"), ("scenarios", toJson entries.size),
    ("transactions", toJson transactionTotal), ("declaredSlots", toJson slotTotal),
    ("aliases", toJson aliases), ("patterns", toJson patterns)]

private def checked {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def rejects {α : Type} (result : Except String α) (message : String) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError ("invalid mapping corpus unexpectedly passed: " ++ message))

/-- Solidity's order, `keccak256(key ++ 1)`, which the pinned std does not use. -/
private def soliditySlot (key : Word) : String :=
  toString ((decodeWordBytesBE? (Solcore.Abi.V1.Keccak256.hash
    (encodeWordBytesBE key ++ encodeWordBytesBE (Word.ofNatModulo 1)))).getD Word.zero).val

def testSourceStorageMappingCorpus : IO Unit := do
  let manifest ← checked (Json.parse (← IO.FS.readFile "scripts/semantic-mapping-corpus.json"))
  let summary ← checked (validateManifest manifest)
  let entries ← checked (manifest.getObjValAs? (Array Json) "cases")
  let some first := entries[0]? | throw (IO.userError "missing first mapping case")
  let some generatedEntry := entries.find? (fun entry => (entry.getObjVal? "generation").isOk) |
    throw (IO.userError "missing generated mapping case")
  -- A tampered entry goes first, so the validator rejects it before it
  -- replays the untouched entries; coverage does not depend on order.
  let replace := fun (original changed : Json) => manifest.setObjVal! "cases"
    (.arr (#[changed] ++ entries.filter (· != original)))
  let history ← checked (first.getObjValAs? (Array Json) "expectedHistory")
  let withRow := fun (index : Nat) (row : Json) =>
    replace first (first.setObjVal! "expectedHistory" (.arr (history.set! index row)))
  let row := history[0]!
  rejects (validateManifest (withRow 0 (row.setObjVal! "output" (toJson ("0x" ++ String.ofList (List.replicate 64 'f'))))))
    "changed output"
  let storage ← checked (row.getObjValAs? (Array Json) "committedStorage")
  rejects (validateManifest (withRow 0 (row.setObjVal! "committedStorage"
    (.arr (storage.set! 0 (storage[0]!.setObjVal! "value" (toJson "7"))))))) "changed counter"
  rejects (validateManifest (withRow 0 (row.setObjVal! "committedStorage"
    (.arr (storage.set! 1 (storage[1]!.setObjVal! "value" (toJson "8"))))))) "changed entry"
  rejects (validateManifest (withRow 0 (row.setObjVal! "committedStorage" (.arr storage.pop)))) "dropped slot"
  let transactions ← checked (first.getObjValAs? (Array Json) "transactions")
  let firstTransaction ← checked (StorageMapping.decodeTransactions (.arr #[transactions[0]!]))
  let some tx := firstTransaction.head? | throw (IO.userError "missing first mapping transaction")
  let slots ← checked (first.getObjValAs? (Array Json) "expectedSlots")
  let solidity := toJson (soliditySlot tx.key)
  rejects (validateManifest (replace first (first.setObjVal! "expectedSlots"
    (.arr (slots.set! 1 solidity))))) "Solidity-order declared slot"
  rejects (validateManifest (withRow 0 (row.setObjVal! "committedStorage"
    (.arr (storage.set! 1 (storage[1]!.setObjVal! "slot" solidity)))))) "Solidity-order committed slot"
  rejects (validateManifest (replace first (first.setObjVal! "expectedSlots" (.arr slots.pop)))) "missing declared slot"
  rejects (validateManifest (replace first (first.setObjVal! "expectedSlots" (.arr (slots.push (toJson "2"))))))
    "undeclared extra slot"
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr history.pop)))) "popped history"
  let generatedHistory ← checked (generatedEntry.getObjValAs? (Array Json) "expectedHistory")
  let generatedStatus ← checked (string generatedHistory[0]! "status")
  rejects (validateManifest (replace generatedEntry (generatedEntry.setObjVal! "expectedHistory"
    (.arr (generatedHistory.set! 0 (generatedHistory[0]!.setObjVal! "status"
      (toJson (if generatedStatus == "returned" then "reverted" else "returned")))))))) "flipped status"
  rejects (validateManifest (replace first (first.setObjVal! "transactions"
    (.arr (transactions.set! 0 (transactions[0]!.setObjVal! "key" (toJson "4"))))))) "key without calldata"
  -- A consistent key change with its own calldata is canonical but no longer
  -- matches the saved slots and history.
  let changedKey := Word.ofNatModulo (tx.key.val + 2)
  rejects (validateManifest (replace first (first.setObjVal! "transactions"
    (.arr (transactions.set! 0 ((transactions[0]!.setObjVal! "key" (toJson (toString changedKey.val))).setObjVal!
      "calldata" (toJson (Solcore.Synthesis.Stateful.StorageMappingExecution.calldata tx.flags changedKey tx.input))))))))
    "consistent key change"
  rejects (validateManifest (replace first (first.setObjVal! "expectedFeatures" (toJson ([] : List String))))) "features"
  rejects (validateManifest (replace generatedEntry (generatedEntry.setObjVal! "generation"
    (Json.mkObj [("seed", toJson "13"), ("maxProgramNodes", toJson (384 : Nat))])))) "changed seed"
  rejects (validateManifest (manifest.setObjVal! "cases" (.arr (#[first] ++ entries)))) "duplicate entry"
  for (key, value) in [
      ("profile", toJson "stateful-keyed-storage"), ("templateVersion", toJson "forged"),
      ("functionVersion", toJson "core-keyed-storage-contract-v1"),
      ("cases", .arr #[]), ("requiredInputs", toJson ([] : List String)),
      ("requiredKeys", toJson (["0"] : List String)), ("requiredHelperCounts", toJson [1, 2]),
      ("requiredAliases", toJson StorageMapping.aliasCatalog.reverse),
      ("requiredAliases", toJson (["repeated-key"] : List String)),
      ("requiredCompletionPatterns", toJson (["reverted,reverted,reverted"] : List String))] do
    rejects (validateManifest (manifest.setObjVal! key value)) key
  rejects (validateManifest manifest 0) "zero fuel"
  IO.println summary.compress

end Tests.SourceStorageMappingCorpus
end

section
-- leanmerge: from Solcore.Test.SourceStorageMappingEmitter
/-! Keccak-mapping protocol regressions through actual installed
ContractRuntime code. The Wire hash closure, built from the proved Core
Keccak builders, is checked against Foundry's `cast keccak` and the separate
`Solcore.Abi.V1.Keccak256`. Golden histories are hand-computed: they cover a
successor key reading the entry its predecessor wrote, the maximum key whose
successor wraps to zero, wrapping arithmetic and a revert that keeps every
declared slot. -/
set_option autoImplicit false

namespace Tests.SourceStorageMappingEmitter

open Lean Solcore.Core Solcore.ContractRuntime Solcore.Synthesis.Core
open Solcore.Synthesis.Core.StorageMapping (CheckedPlan)
open Solcore.Synthesis.Source (EmittedProgram)
open Solcore.Synthesis.Stateful

private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)
private def entry : Wire.Expr := .apply (.var 1) (.var 0)
private def increment : Wire.Expr := .binary .wordAdd (.var 0) (word 1)
private def maximum : Nat := 2 ^ 256 - 1

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

/-- `cast keccak` of the base slot one followed by each key, as decimal Words. -/
private def castSlots : List (Nat × Nat) := [
  (0, 78541660797044910968829902406342334108369226379826116161446442989268089806461),
  (1, 92458281274488595289803937127152923398167637295201432141969818930235769911599),
  (5, 9247535584797915451057180664748820695544591120644449140157971996739901653371),
  (6, 28212876883947467128917703474378516019173305230661588919942657668795042982449),
  (7, 81222191986226809103279119994707868322855741819905904417953092666699096963112),
  (maximum, 71124947674796991739310909576881207026731009306364129481614628957978744178186)]

private def castSlot (key : Nat) : Nat := ((castSlots.find? (·.1 == key)).map (·.2)).getD 0

private def checked (helpers : List Wire.Expr) : IO CheckedPlan := do
  let some step := Aggregates.CheckedDAG.ofParts? helpers entry |
    throw (IO.userError "mapping step did not pass the checked aggregate profile")
  let some plan := CheckedPlan.ofStep? step |
    throw (IO.userError "mapping wrapper did not pass the full Wire host checker")
  return plan

private def emitted (plan : CheckedPlan) : IO EmittedProgram :=
  match Solcore.Synthesis.Source.StorageMapping.emit plan with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"mapping source emission failed: {reprStr error}")

/-- Evaluate the Wire hash closure on two Words through the checked Core machine. -/
private def wireHash (first second : Nat) : IO Nat := do
  let program : Wire.Program := {
    resultType := .word
    dataDefinitions := []
    body := .apply StorageMapping.hashClosure (.pair (word first) (word second))
  }
  ensure program.check "the applied Wire hash closure failed checking"
  match program.toCore.runStateful 1000000 with
  | .done (.word value) _ => pure value.val
  | _ => throw (IO.userError "the Wire hash closure did not return a Word")

private def abiHash (first second : Nat) : Nat :=
  ((decodeWordBytesBE? (Solcore.Abi.V1.Keccak256.hash
    (encodeWordBytesBE (Word.ofNatModulo first) ++ encodeWordBytesBE (Word.ofNatModulo second)))).map (·.val)).getD 0

private def hashChecks : IO Unit := do
  ensure (Wire.Expr.ofCore? StorageMapping.coreHash).isSome "the proved Keccak builders did not convert to Wire"
  ensure (StorageMapping.hashNodes == 2654 && StorageMapping.programOverhead == 93)
    "the Keccak closure or the protocol wrapper changed size"
  for (key, expected) in castSlots do
    ensure ((← wireHash 1 key) == expected && abiHash 1 key == expected &&
      (StorageMappingExecution.entrySlot (Word.ofNatModulo key)).val == expected)
      s!"entry slot of key {key} differs from cast keccak"
  -- keccak256 of 64 zero bytes, and of 2^255 followed by seven, from `cast keccak`.
  ensure ((← wireHash 0 0) == 0xad3228b676f7d3cd4284a5443f17f1962b36e491b30a40b2405849e597ba5fb5 &&
    (← wireHash (2 ^ 255) 7) == 0x5f0acbee363d0168b89f839cbed5de97ddcefff3f3ffbd6a1aef60457f15f108 &&
    abiHash (2 ^ 255) 7 == 0x5f0acbee363d0168b89f839cbed5de97ddcefff3f3ffbd6a1aef60457f15f108)
    "the Wire hash closure differs from cast keccak"

private def transactions (rows : List (Nat × Nat × Nat)) : List StorageMappingExecution.Transaction :=
  rows.zipIdx.map fun ((flags, key, input), index) =>
    ⟨"tx-" ++ toString index, Word.ofNatModulo flags, Word.ofNatModulo key, Word.ofNatModulo input⟩

/-- Sixty-four lowercase hexadecimal digits, written without the observer's
byte encoder. -/
private def hexWord (value : Nat) : String :=
  let digits := Nat.toDigits 16 value
  "0x" ++ String.ofList (List.replicate (64 - digits.length) '0' ++ digits)

/-- The declared slots in increasing order with the values the golden assigns. -/
private def slotRows (slots : List Nat) (values : List (Nat × Nat)) : Json :=
  toJson ((slots.mergeSort (· ≤ ·)).map fun slot => Json.mkObj [("slot", toJson (toString slot)),
    ("value", toJson (toString (((values.find? (·.1 == slot)).map (·.2)).getD 0)))])

private def historyCheck (plan : CheckedPlan) (rows : List (Nat × Nat × Nat)) (slots : List Nat)
    (expected : List (String × Nat × List (Nat × Nat))) : IO Unit := do
  let history := StorageMappingExecution.observe plan (transactions rows) StorageExecution.fixtureBindings 1000000
  let observed := (history.getObjValAs? (List Json) "transactions").toOption.getD []
  ensure ((history.getObjValAs? String "status").toOption == some "complete" && observed.length == expected.length &&
    (history.getObjVal? "observedSlots").toOption == some (toJson ((slots.mergeSort (· ≤ ·)).map toString)) &&
    (history.getObjVal? "initialStorage").toOption == some (slotRows slots []))
    "mapping golden history did not complete from empty declared slots"
  for (row, (status, payload, values)) in observed.zip expected do
    ensure ((row.getObjValAs? String "status").toOption == some status &&
      (row.getObjValAs? String "output").toOption == some (hexWord payload) &&
      (row.getObjVal? "committedStorage").toOption == some (slotRows slots values))
      s!"mapping golden row changed: {row.compress}"

private def goldenChecks : IO Unit := do
  -- step(x) = x: key six reads the entry key five wrote as its successor, and a
  -- reverted maximum key keeps every slot, including its wrapped successor zero.
  let slots := [0, castSlot 5, castSlot 6, castSlot 7, castSlot maximum, castSlot 0]
  historyCheck (← checked [.var 0]) [(0, 5, 7), (0, 6, 3), (1, maximum, 1)] slots [
    ("returned", 9, [(0, 1), (castSlot 5, 7), (castSlot 6, 1)]),
    ("returned", 8, [(0, 2), (castSlot 5, 7), (castSlot 6, 4), (castSlot 7, 2)]),
    ("reverted", 5, [(0, 2), (castSlot 5, 7), (castSlot 6, 4), (castSlot 7, 2)])]
  -- step(x) = x + 1 wraps the maximum input; the maximum key's successor is key zero.
  historyCheck (← checked [increment]) [(0, maximum, maximum), (2, 0, 1)]
    [0, castSlot maximum, castSlot 0, castSlot 1] [
    ("returned", 2, [(0, 1), (castSlot maximum, 0), (castSlot 0, 1)]),
    ("returned", 7, [(0, 2), (castSlot maximum, 0), (castSlot 0, 3), (castSlot 1, 2)])]

private def admissionChecks : IO Unit := do
  for plan in [← checked [increment], ← checked [.var 0]] do
    ensure (plan.program.check && plan.program.toCore.checkHost &&
      plan.program.resultType == .sum .word (.sum .word .word) && plan.contract.entryProfile == .wordOutcomeV1)
      "mapping plan lost full host checking or the typed outcome convention"
    ensure (plan.contract.code.program == plan.program.toCore) "admission replaced the original contract"
    ensure (StorageMapping.canonicalNodes plan.step == Wire.programNodes plan.program &&
      Wire.programNodes plan.program ==
        Wire.programNodes plan.step.program + StorageMapping.programOverhead + StorageMapping.hashNodes)
      "mapping wrapper overhead differs from the complete original Core"
    match plan.program.body with
    | .letE hash (.letE saved _) =>
        ensure (Wire.encodeExpr hash == Wire.encodeExpr StorageMapping.hashClosure &&
          Wire.encodeExpr saved == Wire.encodeExpr plan.step.program.body)
          "mapping wrapper lost its hash closure or ignored its arbitrary entry closure"
    | _ => throw (IO.userError "mapping wrapper lost its initial closure bindings")
    ensure ((← emitted plan) == (← emitted plan)) "mapping emission is nondeterministic"

private def expectedBasic : String := String.intercalate "\n" [
  "import * from std;", "import * from std.dispatch;",
  "import {mstore, revert_} from std.opcodes;", "",
  "function sc_fn0(sc_arg: word) returns (word) {",
  "    let sc_v0: word = 1;", "    let sc_v1: word = (sc_arg + sc_v0);",
  "    return sc_v1;", "}", "",
  "function sc_step(sc_arg: word) returns (word) {",
  "    let sc_v0: word = sc_fn0(sc_arg);", "    return sc_v0;", "}", "",
  "contract SynthesizedMapping {",
  "    counter: word;",
  "    entries: mapping(word => word);",
  "",
  "    function run(flags: uint256, key: uint256, input: uint256) public returns (uint256) {",
  "        let sc_flags: word = Typedef.rep(flags);",
  "        let sc_key: word = Typedef.rep(key);",
  "        let sc_input: word = Typedef.rep(input);",
  "        let sc_old: word = entries[sc_key];",
  "        entries[sc_key] = sc_step(sc_input + sc_old);",
  "        entries[sc_key + 1] = sc_old + 1;",
  "        counter = counter + 1;",
  "        let sc_result: word = entries[sc_key] + entries[sc_key + 1] + counter;",
  "        if ((sc_flags & 1) == 1) {", "            mstore(0, sc_result);",
  "            revert_(0, 32);", "        }",
  "        return uint256(sc_result);", "    }", "}", ""]

private def formattingChecks : IO Unit := do
  let source ← emitted (← checked [increment])
  ensure (source.source == expectedBasic) "mapping protocol source changed"
  ensure (source.contractName == "SynthesizedMapping" && source.methodSignature == "run(uint256,uint256,uint256)" &&
    source.deployPath == ["SynthesizedMappingDeploy"] &&
    source.runtimePath == ["SynthesizedMappingDeploy", "SynthesizedMapping"])
    "mapping wrapper metadata changed"
  -- Raw primitives join the same opcode import only when a step uses them.
  let divided ← emitted (← checked [.binary .wordDiv (.var 0) (word 1)])
  ensure ((divided.source.splitOn "import {mstore, revert_, div as sc_div, ").length == 2)
    "mapping emission lost the merged raw division alias"
  ensure (Solcore.Synthesis.Source.StorageMapping.emitterVersion == "solcore-source-keccak-mapping-v1" &&
    Solcore.Synthesis.Source.StorageMapping.wrapperVersion == "solcore-word-keccak-mapping-contract-v1" &&
    Solcore.Synthesis.Source.StorageMapping.selector == "0x24b912e5" &&
    StorageMapping.version == "core-keccak-mapping-contract-v1") "mapping provenance changed"

private def observerChecks : IO Unit := do
  -- `cast calldata "run(uint256,uint256,uint256)" 1 5 7`
  ensure (StorageMappingExecution.calldata (Word.ofNatModulo 1) (Word.ofNatModulo 5) (Word.ofNatModulo 7) ==
    "0x24b912e5" ++ String.ofList (List.replicate 63 '0') ++ "1" ++ String.ofList (List.replicate 63 '0') ++ "5" ++
      String.ofList (List.replicate 63 '0') ++ "7")
    "mapping calldata is not the selector and three Words"
  let calls := transactions [(0, 5, 7), (0, 6, 3), (1, 7, 0)]
  let declared := (StorageMappingExecution.observedSlots calls).map (·.val)
  ensure (declared.length == 5 && [0, castSlot 5, castSlot 6, castSlot 7].all declared.contains &&
    declared == declared.mergeSort (· ≤ ·))
    "declared slots are not the counter and every key's and successor's entry slot in order"
  let plan ← checked [.var 0]
  let exhausted := StorageMappingExecution.observe plan calls StorageExecution.fixtureBindings 1000
  let rows := (exhausted.getObjValAs? (List Json) "transactions").toOption.getD []
  ensure ((exhausted.getObjValAs? String "status").toOption == some "incomplete" &&
    (exhausted.getObjValAs? (List String) "unexecuted").toOption == some ["tx-1", "tx-2"] && rows.length == 1 &&
    (rows[0]!.getObjValAs? String "status").toOption == some "out-of-fuel" &&
    (exhausted.getObjVal? "finalStorage").toOption == (exhausted.getObjVal? "initialStorage").toOption)
    "mapping observer conflated fuel exhaustion with completion"
  let complete := StorageMappingExecution.observe plan calls StorageExecution.fixtureBindings 1000000
  ensure ((complete.getObjValAs? String "schema").toOption == some "solcore-lean.mapping-history.v2" &&
    (complete.getObjValAs? String "status").toOption == some "complete")
    "history did not declare its schema or complete"

def testSourceStorageMappingEmitter : IO Unit := do
  hashChecks
  admissionChecks
  goldenChecks
  formattingChecks
  observerChecks

end Tests.SourceStorageMappingEmitter
end

section
-- leanmerge: from Solcore.Test.SourceStorageRollbackCases
/-! Storage-case regressions exercise actual checked-contract execution, exact
replay, bounded generation and scenario reductions. Expected fixture values are
test goldens only; neither emitted cases nor the observer consume them. -/
set_option autoImplicit false

namespace Tests.SourceStorageRollbackCases
open Lean Solcore.Core Solcore.Synthesis.Core Solcore.Synthesis.Source
open Solcore.Synthesis.Core.StorageRollback (CheckedPlan)
open Solcore.Synthesis.Stateful.StorageExecution (Transaction Bindings)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def get {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)
private def rejected {α : Type} (result : Except String α) (message : String) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError message)
private def field (value : Json) (name : String) : IO Json := get (value.getObjVal? name)
private def string (value : Json) (name : String) : IO String := get (value.getObjValAs? String name)
private def natural (value : Json) (name : String) : IO Nat := get (value.getObjValAs? Nat name)
private def rows (value : Json) (name : String := "transactions") : IO (Array Json) :=
  get (value.getObjValAs? (Array Json) name)
private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)
private def entry : Wire.Expr := .apply (.var 1) (.var 0)
private def bindings : Bindings := ⟨⟨17, by decide⟩, ⟨101, by decide⟩⟩
private def makePlan (body : Wire.Expr) (result : Wire.Expr := entry) : IO CheckedPlan := do
  let some graph := Aggregates.CheckedDAG.ofParts? [body] result |
    throw (IO.userError "storage fixture failed step admission")
  let some plan := CheckedPlan.ofStep? graph | throw (IO.userError "storage wrapper failed host admission")
  return plan
private def transactions (inputs : List Word) : List Transaction :=
  inputs.zipIdx.map fun (input, index) => ⟨"call-" ++ toString index, input⟩
private def scenario (plan : CheckedPlan) (inputs : List Word) : IO Solcore.Synthesis.Source.StorageRollback.CheckedScenario :=
  get (Solcore.Synthesis.Source.StorageRollback.checkedScenario plan (transactions inputs))
private def imported (value : Solcore.Synthesis.Source.StorageRollback.CheckedScenario) (fuel : Nat := 10000) : IO Json :=
  get (Solcore.Synthesis.Source.StorageRollback.emitCase value (Json.mkObj [("kind", toJson "imported")]) fuel)
private def storage (first second : Word) : Json := toJson ([
  Json.mkObj [("slot", toJson "0"), ("value", toJson (toString first.val))],
  Json.mkObj [("slot", toJson "1"), ("value", toJson (toString second.val))]])

private def checkHistory (value : Solcore.Synthesis.Source.StorageRollback.CheckedScenario) (expected : List (String × Word × Word × Word)) : IO Unit := do
  let observed := Solcore.Synthesis.Source.StorageRollback.observe value bindings 10000
  ensure ((← string observed "status") == "complete") "storage fixture did not finish"
  ensure ((← field observed "initialStorage") == storage Word.zero Word.zero)
    "original Core did not start with empty storage"
  let result ← rows observed
  ensure (result.size == expected.length && result.size == value.transactions.length)
    "original Core changed transaction count"
  for ((status, output, first, second), index) in expected.zipIdx do
    let row := result[index]!
    ensure (some (← string row "id") == (value.transactions[index]?).map (·.id) && (← natural row "index") == index)
      "observer lost stable transaction identity"
    ensure ((← string row "status") == status &&
      (← string row "output") == Solcore.ContractRuntime.encodeBytesText
        (Solcore.ContractRuntime.encodeWordBytesBE output)) "storage return value differs from golden"
    ensure ((← field row "committedStorage") == storage first second)
      "original Core committed the wrong storage prefix"
  ensure ((← field observed "finalStorage") == (← field result[result.size - 1]! "committedStorage"))
    "final storage differs from the last committed prefix"
  ensure ((← rows observed "unexecuted").isEmpty && (← field observed "stoppedAt") == Json.null)
    "successful storage history retained unexecuted work"
  ensure (Solcore.Synthesis.Source.StorageRollback.observe value bindings 10000 == observed) "fresh observation reused a previous world"

private def referenceChecks : IO Json := do
  let identity ← makePlan (.var 0)
  let value ← scenario identity ([2, 3, 4].map Word.ofNatModulo)
  checkHistory value ([("returned", 3, 2, 1), ("reverted", 7, 2, 1), ("returned", 8, 6, 2)].map fun (status, out, a, b) =>
    (status, Word.ofNatModulo out, Word.ofNatModulo a, Word.ofNatModulo b))
  let odd ← scenario identity [Word.ofNatModulo 1, Word.ofNatModulo 3, Word.maximum]
  checkHistory odd [("reverted", Word.ofNatModulo 2, Word.zero, Word.zero),
    ("reverted", Word.ofNatModulo 4, Word.zero, Word.zero), ("reverted", Word.zero, Word.zero, Word.zero)]
  let even ← scenario identity ([0, 2, 2 ^ 256 - 2].map Word.ofNatModulo)
  checkHistory even ([("returned", 1, 0, 1), ("returned", 4, 2, 2), ("returned", 3, 0, 3)].map fun (status, out, a, b) =>
    (status, Word.ofNatModulo out, Word.ofNatModulo a, Word.ofNatModulo b))
  let wrap ← scenario identity [Word.maximum, Word.ofNatModulo 2]
  checkHistory wrap [("reverted", Word.zero, Word.zero, Word.zero),
    ("returned", Word.ofNatModulo 3, Word.ofNatModulo 2, Word.ofNatModulo 1)]
  let privateStep := Wire.Expr.letE (.newCell .word (word 0))
    (.letE (.storeCell (.var 0) (.binary .wordAdd (.loadCell (.var 0)) (word 2)))
      (.binary .wordAdd (.var 2) (.loadCell (.var 1))))
  let mutablePlan ← makePlan privateStep (.binary .wordSub entry (word 1))
  let mutableCase ← scenario mutablePlan ([0, 1, 2].map Word.ofNatModulo)
  -- Both computed-word parity and input+old0 parity differ from the original
  -- input in this sequence. Neither may select the rollback branch.
  checkHistory mutableCase ([("returned", 2, 1, 1), ("reverted", 5, 1, 1), ("returned", 6, 4, 2)].map fun (status, out, a, b) =>
    (status, Word.ofNatModulo out, Word.ofNatModulo a, Word.ofNatModulo b))
  let fresh := Solcore.Synthesis.Source.StorageRollback.observe value ⟨⟨33, by decide⟩, ⟨202, by decide⟩⟩ 10000
  ensure ((← rows fresh).map Solcore.Synthesis.Stateful.AccountStorage.unbound == (← rows (Solcore.Synthesis.Source.StorageRollback.observe value bindings 10000)).map Solcore.Synthesis.Stateful.AccountStorage.unbound &&
      (← rows fresh).all (Solcore.Synthesis.Stateful.AccountStorage.boundTo · [202]))
    "address-independent rollback profile changed with bindings"
  ensure (identity.program.check && identity.program.toCore.checkHost &&
    identity.program.resultType == .sum .word (.sum .word .word))
    "rollback original code lost outcomeV1 host admission"
  let saved ← imported value
  ensure ((← get (Solcore.Synthesis.Source.StorageRollback.replayCase saved 10000)) == saved)
    "imported rollback case did not replay"
  ensure ((← get (Solcore.Synthesis.Source.StorageRollback.replayCase (saved.setObjVal! "directCore" (toJson "forged")) 10000)) == saved)
    "rollback replay consumed a stored expected result"
  let changed ← imported (← scenario identity ([1, 2, 3].map Word.ofNatModulo))
  ensure ((← field saved "program") == (← field changed "program") &&
    (← string saved "source") == (← string changed "source"))
    "rollback runtime inputs were substituted into source or Core code"
  return saved

private def resourceChecks : IO Unit := do
  let slow := (List.range 12).foldl (fun body _ => Wire.Expr.letE (word 1) body) (word 1)
  let plan ← makePlan (.ifE (.binary .wordEq (.var 0) (word 2)) slow (word 0))
  let value ← scenario plan ([0, 1, 2].map Word.ofNatModulo)
  let low := Solcore.Synthesis.Source.StorageRollback.observe value bindings 0
  ensure ((← string low "status") == "incomplete" && (← string low "stoppedAt") == "call-0" &&
    (← rows low).size == 1 && (← rows low "unexecuted").size == 2 &&
    (← field low "finalStorage") == storage Word.zero Word.zero)
    "rollback exhaustion committed or continued work"
  let mut afterRevert := false
  for fuel in List.range 250 do
    let observed := Solcore.Synthesis.Source.StorageRollback.observe value bindings fuel
    let result ← rows observed
    if result.size == 3 then
      if (← string result[2]! "status") == "out-of-fuel" then
        afterRevert := true
        ensure ((← string result[0]! "status") == "returned" &&
          (← string result[1]! "status") == "reverted" &&
          (← field result[0]! "committedStorage") == (← field result[1]! "committedStorage") &&
          (← field observed "finalStorage") == storage Word.zero (Word.ofNatModulo 1))
          "out-of-fuel after revert lost the prior committed world"
  ensure afterRevert "resource regression did not reach a completed rollback prefix"

private def generationChecks : IO Json := do
  for seed in List.range 12 do
    let mut minimum : Option Nat := none
    for budget in List.range 385 do
      if minimum.isNone && (Solcore.Synthesis.Source.StorageRollback.generatedScenario (Seed.ofNat seed) budget).isOk then minimum := some budget
    let some budget := minimum | throw (IO.userError "storage template does not fit default384 budget")
    let (value, _) ← get (Solcore.Synthesis.Source.StorageRollback.generatedScenario (Seed.ofNat seed) budget)
    ensure (Wire.programNodes value.program ≤ budget && value.transactions.length == 3 &&
      value.plan.step.helpers.length == 1 + seed % 3) "storage recipe lost full node/transaction/helper bounds"
    rejected (Solcore.Synthesis.Source.StorageRollback.generatedScenario (Seed.ofNat seed) (budget - 1)) "undersized node budget accepted"
  rejected (Solcore.Synthesis.Source.StorageRollback.generatedScenario (Seed.ofNat 0) 513) "oversized node budget accepted"
  let corpus := Solcore.Synthesis.Source.StorageRollback.generateCases (Seed.ofNat 0) 384 4 256 10000
  ensure (corpus == Solcore.Synthesis.Source.StorageRollback.generateCases (Seed.ofNat 0) 384 4 256 10000) "storage generation nondeterministic"
  let generated ← rows corpus "cases"
  ensure (generated.size == 4 && (← natural corpus "attempted") ≤ 256)
    "storage count does not count complete scenarios"
  for saved in generated do
    let value ← get (Solcore.Synthesis.Source.StorageRollback.caseProgram saved)
    ensure ((value.transactions.map (fun tx => tx.input.val % 2)) == [0, 1, 0]) "generated rollback sequence lost parity recipe"
    ensure (value.transactions.length == 3 && Wire.programNodes value.program ≤ 384)
      "generated case escaped bounded storage profile"
    ensure ((← get (Solcore.Synthesis.Source.StorageRollback.replayCase saved 10000)) == saved) "generated history provenance did not replay"
    let low ← get (Solcore.Synthesis.Source.StorageRollback.replayCase saved 0)
    ensure ((← natural low "executionFuel") == 0 && (← field low "provenance") == (← field saved "provenance"))
      "fresh replay fuel changed the generation validation budget"
  let saved := generated[0]!
  let origin ← field (← field saved "provenance") "origin"
  let some seed := (← string origin "seed").toNat? | throw (IO.userError "invalid generated seed")
  let low := Solcore.Synthesis.Source.StorageRollback.generateCases (Seed.ofNat seed) 384 1 1 0
  let excluded ← rows low "excluded"
  ensure ((← rows low "cases").isEmpty && (← string excluded[0]! "category") == "inconclusive-resource")
    "storage generation resource exhaustion was not distinguished"
  ensure ((← rows (Solcore.Synthesis.Source.StorageRollback.generateCases (Seed.ofNat seed) 384 2 1 10000) "cases").size == 1 &&
    (← natural (Solcore.Synthesis.Source.StorageRollback.generateCases (Seed.ofNat seed) 384 0 10 10000) "attempted") == 0 &&
    (← rows (Solcore.Synthesis.Source.StorageRollback.generateCases (Seed.ofNat seed) 384 1 0 10000) "cases").isEmpty)
    "storage generator ignored count/attempt bounds"
  return saved

private def tamperingChecks (saved generated : Json) : IO Unit := do
  let transactionRows ← rows saved
  let first := transactionRows[0]!
  for (name, bad) in [("id", toJson ""), ("id", toJson "not valid"),
      ("id", toJson (String.ofList (List.replicate 65 'a'))), ("input", toJson "01"),
      ("input", toJson "7"), ("calldata", toJson "0x"), ("value", toJson "1"),
      ("extra", toJson true)] do
    rejected (Solcore.Synthesis.Source.StorageRollback.decodeTransactions (toJson [first.setObjVal! name bad]))
      "noncanonical storage transaction accepted"
  rejected (Solcore.Synthesis.Source.StorageRollback.decodeTransactions (toJson [first, first])) "duplicate transaction IDs accepted"
  rejected (Solcore.Synthesis.Source.StorageRollback.decodeTransactions (toJson ([] : List Json))) "empty transaction list accepted"
  rejected (Solcore.Synthesis.Source.StorageRollback.decodeTransactions
    (toJson (List.replicate (Solcore.Synthesis.Stateful.Sequence.maxTransactions + 1) first)))
    "unbounded transaction count accepted"
  for (name, bad) in [("initialState", Json.mkObj [("storage", toJson [first])]),
      ("observedSlots", toJson (["1", "0"] : List String)), ("executionFuel", toJson (10000001 : Nat)),
      ("program", Wire.encodeProgram {resultType := .word, dataDefinitions := [], body := word 0})] do
    rejected (Solcore.Synthesis.Source.StorageRollback.caseProgram (saved.setObjVal! name bad)) "invalid storage case boundary accepted"
  let provenance ← field generated "provenance"
  let origin ← field provenance "origin"
  let withOrigin := fun changed => generated.setObjVal! "provenance" (provenance.setObjVal! "origin" changed)
  for name in ["generatorVersion", "profileVersion", "functionVersion", "templateVersion", "stepProfileVersion",
      "stepFunctionVersion", "stepTemplateVersion", "emitterVersion", "wrapperVersion", "features"] do
    rejected (Solcore.Synthesis.Source.StorageRollback.replayCase (generated.setObjVal! "provenance" (provenance.setObjVal! name Json.null)) 10000)
      "tampered storage provenance accepted"
  for (name, bad) in [("seed", toJson "00"), ("finalSeed", toJson "bad"),
      ("maxProgramNodes", toJson (513 : Nat)), ("stepOrigin", Json.null), ("sequenceIndices", Json.null), ("sequenceParities", Json.null),
      ("validationFuel", toJson (10000001 : Nat)), ("validationFuel", toJson (0 : Nat))] do
    rejected (Solcore.Synthesis.Source.StorageRollback.replayCase (withOrigin (origin.setObjVal! name bad)) 10000)
      "tampered generated storage recipe accepted"
  let plan ← field saved "storagePlan"
  rejected (Solcore.Synthesis.Source.StorageRollback.checkedPlan (plan.setObjVal! "extra" Json.null)) "noncanonical storage plan accepted"
  rejected (Solcore.Synthesis.Source.StorageRollback.replayCase (saved.setObjVal! "source" (toJson "stale")) 10000) "stale source accepted"
  let contract ← field saved "contract"
  rejected (Solcore.Synthesis.Source.StorageRollback.replayCase (saved.setObjVal! "contract" (contract.setObjVal! "selector" (toJson "0x00000000"))) 10000)
    "wrong storage ABI selector accepted"
  let bindingJson := Solcore.Synthesis.Stateful.StorageExecution.bindingsJson bindings
  ensure ((Solcore.Synthesis.Stateful.StorageExecution.decodeBindings bindingJson).isOk) "valid bindings rejected"
  for (name, value) in [("caller", "017"), ("address", "17"), ("caller", toString (2 ^ 160))] do
    rejected (Solcore.Synthesis.Stateful.StorageExecution.decodeBindings (bindingJson.setObjVal! name (toJson value)))
      "invalid execution bindings accepted"

private def shrinkChecks : IO Unit := do
  let plan ← makePlan (Aggregate.template 3 (word 2))
  let value ← scenario plan [Word.maximum, Word.ofNatModulo 7, Word.maximum]
  let saved ← imported value
  let candidates ← get (Solcore.Synthesis.Source.StorageRollback.shrinkCases saved 1000 10000)
  let result ← rows candidates "cases"
  ensure (!result.isEmpty && candidates == (← get (Solcore.Synthesis.Source.StorageRollback.shrinkCases saved 1000 10000)))
    "storage reductions were empty or nondeterministic"
  let mut removed := false
  let mut loweredInput := false
  let mut changedStep := false
  let mut seen : List String := []
  for row in result do
    let reduced ← get (Solcore.Synthesis.Source.StorageRollback.caseProgram row)
    ensure (decide (Solcore.Synthesis.Source.StorageRollback.StrictlySmaller reduced value) && reduced.program.check &&
      reduced.plan.step.helpers.length == value.plan.step.helpers.length &&
      Aggregate.bindingInventory reduced.plan.step == Aggregate.bindingInventory value.plan.step &&
      decide ((reduced.transactions.map (·.id)).Sublist (value.transactions.map (·.id))))
      "storage reduction lost strict complexity, host typing or stable scope/IDs"
    let key := (Json.mkObj [("program", Wire.encodeProgram reduced.program),
      ("transactions", Solcore.Synthesis.Source.StorageRollback.transactionsJson reduced.transactions)]).compress
    ensure (!seen.contains key) "duplicate storage reduction"
    seen := key :: seen
    removed := removed || reduced.transactions.length < value.transactions.length
    loweredInput := loweredInput || (reduced.transactions.length == value.transactions.length &&
      Solcore.Synthesis.Source.StorageRollback.inputWeight reduced < Solcore.Synthesis.Source.StorageRollback.inputWeight value)
    changedStep := changedStep || Wire.encodeProgram reduced.program != Wire.encodeProgram value.program
    ensure ((← get (Solcore.Synthesis.Source.StorageRollback.replayCase row 10000)) == row) "reduced storage case did not replay"
  ensure (removed && loweredInput && changedStep) "storage shrink omitted sequence/input/step axes"
  ensure ((← rows (← get (Solcore.Synthesis.Source.StorageRollback.shrinkCases saved 2 10000)) "cases") == result.extract 0 2 &&
    (← rows (← get (Solcore.Synthesis.Source.StorageRollback.shrinkCases saved 0 10000)) "cases").isEmpty) "storage shrink limit changed ordering"
  let first := result[0]!
  let reduced ← get (Solcore.Synthesis.Source.StorageRollback.caseProgram first)
  let badParent := Json.mkObj [("kind", toJson "reduced"), ("parentPlan", Solcore.Synthesis.Source.StorageRollback.planJson reduced.plan),
    ("parentProgram", Wire.encodeProgram reduced.program),
    ("parentTransactions", Solcore.Synthesis.Source.StorageRollback.transactionsJson reduced.transactions)]
  let provenance ← field first "provenance"
  rejected (Solcore.Synthesis.Source.StorageRollback.replayCase (first.setObjVal! "provenance" (provenance.setObjVal! "origin" badParent)) 10000)
    "non-strict reduction provenance accepted"

def testSourceStorageRollbackCases : IO Unit := do
  let imported ← referenceChecks
  resourceChecks
  let generated ← generationChecks
  tamperingChecks imported generated
  shrinkChecks

end Tests.SourceStorageRollbackCases
end

section
-- leanmerge: from Solcore.Test.SourceStorageRollbackEmitter
/-! Typed rollback outcomes through actual installed ContractRuntime code.
Golden histories distinguish tentative writes/payloads from committed storage,
and cover original-input parity, Word wrap, private cells and arbitrary entries. -/
set_option autoImplicit false

namespace Tests.SourceStorageRollbackEmitter

open Lean Solcore.Core Solcore.ContractRuntime Solcore.Synthesis.Core
open Solcore.Synthesis.Core.StorageRollback (CheckedPlan)
open Solcore.Synthesis.Source (EmittedProgram)
open Solcore.Synthesis.Stateful

private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)
private def entry : Wire.Expr := .apply (.var 1) (.var 0)
private def increment : Wire.Expr := .binary .wordAdd (.var 0) (word 1)

private def privateStep : Wire.Expr :=
  .letE (.newCell .word (word 0))
    (.letE (.storeCell (.var 0) (.binary .wordAdd (.loadCell (.var 0)) (word 2)))
      (.binary .wordAdd (.var 2) (.loadCell (.var 1))))

private def pairStep : Wire.Expr :=
  .letE (.newCell .word (.var 0))
    (.letE (.pair (.loadCell (.var 0))
      (.letE (.storeCell (.var 0) (word 2)) (.loadCell (.var 1))))
      (.binary .wordAdd (.first (.var 0)) (.second (.var 0))))

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def checked (helpers : List Wire.Expr) (body : Wire.Expr := entry) : IO CheckedPlan := do
  let some step := Aggregates.CheckedDAG.ofParts? helpers body |
    throw (IO.userError "rollback step did not pass the checked aggregate profile")
  let some plan := CheckedPlan.ofStep? step |
    throw (IO.userError "rollback wrapper did not pass the full Wire host checker")
  return plan

private def emitted (plan : CheckedPlan) : IO EmittedProgram :=
  match Solcore.Synthesis.Source.StorageRollback.emit plan with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"rollback source emission failed: {reprStr error}")

private structure Expected where
  input : Word
  reverts : Bool
  payload : Word
  written0 : Word
  committed0 : Word
  committed1 : Word

private def returned (input payload slot0 slot1 : Nat) : Expected :=
  ⟨Word.ofNatModulo input, false, Word.ofNatModulo payload, Word.ofNatModulo slot0,
    Word.ofNatModulo slot0, Word.ofNatModulo slot1⟩

private def reverted (input payload written0 prior0 prior1 : Nat) : Expected :=
  ⟨Word.ofNatModulo input, true, Word.ofNatModulo payload, Word.ofNatModulo written0,
    Word.ofNatModulo prior0, Word.ofNatModulo prior1⟩

private def sequenceCheck (plan : CheckedPlan) (expected : List Expected) (privateCells : Nat := 0) : IO Unit := do
  let bindings := StorageExecution.fixtureBindings
  let registry : CheckedContractRegistry :=
    ⟨fun address => if address == bindings.address then some plan.contract else none⟩
  let mut world := StorageExecution.initialWorldForContract plan.contract bindings
  for row in expected do
    let some prior := world.account? bindings.address | throw (IO.userError "prior account missing")
    let some ⟨contract, installed⟩ := registry.resolve? world bindings.address |
      throw (IO.userError "committed world no longer resolves the original rollback contract")
    let invocation : TopLevelInvocation := {
      target := bindings.address, caller := bindings.caller, callValue := Word.zero,
      inputData := StorageExecution.inputData row.input }
    match TopLevelExecution.run contract invocation installed 0 with
    | .outOfFuel _ _ _ _ _ _ => pure ()
    | .completed _ => throw (IO.userError "zero fuel was treated as a completed return/revert")
    match TopLevelExecution.run contract invocation installed 10000 with
    | .outOfFuel _ _ _ _ _ _ => throw (IO.userError "rollback golden call exhausted its execution budget")
    | .completed result =>
        let expectedValue : Value := if row.reverts then
          .inRight .word (.inLeft .word (.word row.payload))
          else .inLeft (.sum .word .word) (.word row.payload)
        let expectedOutcome : FrameOutcome Word := if row.reverts then
          .reverted (encodeWordBytesBE row.payload) else .returned (encodeWordBytesBE row.payload)
        ensure (result.coreValue == expectedValue && result.outcome == expectedOutcome)
          "typed completion, original-input parity or 32-byte payload changed"
        let some working := result.terminalContext.context.values.working.1.account? bindings.address |
          throw (IO.userError "working account missing")
        ensure (working.storageRead Word.zero == row.written0 &&
          working.storageRead (Word.ofNatModulo 1) == (prior.storageRead (Word.ofNatModulo 1)).add (Word.ofNatModulo 1))
          "return/revert was selected before both tentative writes completed"
        let some committed := result.finalWorld.account? bindings.address |
          throw (IO.userError "committed account missing")
        ensure (committed.storageRead Word.zero == row.committed0 &&
          committed.storageRead (Word.ofNatModulo 1) == row.committed1 &&
          committed.storageRead (Word.ofNatModulo 2) == Word.zero)
          "rollback did not select the expected committed storage"
        if row.committed0 == Word.zero then
          ensure ((committed.storageValue? Word.zero).isNone) "committed zero storage was not sparse"
        if row.written0 == Word.zero then
          ensure ((working.storageValue? Word.zero).isNone) "tentative zero write was not a deletion"
        ensure (committed.balance == Word.zero && committed.nonce == Word.zero &&
          result.committedJournal.logList.isEmpty && result.committedJournal.createdContractList.isEmpty)
          "storage-only execution changed unrelated observations"
        ensure (result.coreStore.length == privateCells && result.coreStore.all (· == .word (Word.ofNatModulo 2)))
          "private step cells were retained or lost across transaction boundaries"
        ensure ((registry.resolve? result.finalWorld bindings.address).isSome)
          "return/revert replaced the installed original Core program"
        world := result.finalWorld

private def executionChecks : IO Unit := do
  let identity ← checked [.var 0]
  sequenceCheck identity [returned 2 3 2 1, reverted 3 7 5 2 1, returned 4 8 6 2]
  sequenceCheck identity [reverted 1 2 1 0 0, reverted 3 4 3 0 0, returned 2 3 2 1]
  sequenceCheck identity [reverted (wordModulus - 1) 0 (wordModulus - 1) 0 0, returned 2 3 2 1]
  sequenceCheck identity [returned (2 ^ 255) (2 ^ 255 + 1) (2 ^ 255) 1,
    reverted 1 (2 ^ 255 + 3) (2 ^ 255 + 1) (2 ^ 255) 1,
    returned (2 ^ 255) 2 0 2]
  let clears ← checked [.ifE (.binary .wordEq (.var 0) (word 1)) (word 0) (.var 0)]
  sequenceCheck clears [returned 2 3 2 1, reverted (wordModulus - 1) 2 0 2 1, returned 0 4 2 2]
  let arbitrary ← checked [privateStep] (.binary .wordSub entry (word 1))
  sequenceCheck arbitrary [returned 0 2 1 1, reverted 1 5 3 1 1, returned 2 6 4 2] 1
  let aggregate ← checked [increment, pairStep] (.apply (.var 1) (.apply (.var 2) (.var 0)))
  sequenceCheck aggregate [returned 2 6 5 1, reverted 3 13 11 5 1, returned 4 14 12 2] 1
  sequenceCheck (← checked [.var 0] (word 0))
    [returned 2 1 0 1, reverted 1 2 0 0 1, returned 4 2 0 2]

private def admissionChecks : IO Unit := do
  for plan in [← checked [increment], ← checked [privateStep] (.binary .wordSub entry (word 1))] do
    ensure (plan.program.check && plan.program.toCore.checkHost &&
      plan.program.resultType == .sum .word (.sum .word .word) && plan.contract.entryProfile == .wordOutcomeV1)
      "rollback plan lost full host checking or the typed outcome convention"
    ensure (plan.contract.code.program == plan.program.toCore) "admission replaced the original contract"
    ensure (StorageRollback.canonicalNodes plan.step == Wire.programNodes plan.program &&
      Wire.programNodes plan.program == Wire.programNodes plan.step.program + StorageRollback.programOverhead)
      "rollback wrapper overhead differs from the complete original Core"
    match plan.program.body with
    | .letE saved _ =>
        ensure (Wire.encodeExpr saved == Wire.encodeExpr plan.step.program.body)
          "rollback wrapper ignored its arbitrary entry closure"
    | _ => throw (IO.userError "rollback wrapper lost its initial closure binding")
    ensure ((← emitted plan) == (← emitted plan)) "rollback emission is nondeterministic"
  -- Raw primitives join the existing opcode import only when a step uses them.
  let divided ← checked [.binary .wordDiv (.var 0) (word 1)]
  match Solcore.Synthesis.Source.StorageRollback.emit divided with
  | .ok emitted => unless (emitted.source.splitOn "import {sload, sstore, mstore, revert_, div as sc_div, ").length == 2 && (emitted.source.splitOn "    let sc_v3: word = sc_div(sc_v0, sc_v2);").length == 2 do
      throw (IO.userError "StorageRollback emission lost the merged raw division alias or its snapshots")
  | .error error => throw (IO.userError s!"StorageRollback raw division was rejected: {reprStr error}")

private def expectedBasic : String := String.intercalate "\n" [
  "import * from std;", "import * from std.dispatch;",
  "import {sload, sstore, mstore, revert_} from std.opcodes;", "",
  "function sc_fn0(sc_arg: word) returns (word) {",
  "    let sc_v0: word = 1;", "    let sc_v1: word = (sc_arg + sc_v0);",
  "    return sc_v1;", "}", "",
  "function sc_step(sc_arg: word) returns (word) {",
  "    let sc_v0: word = sc_fn0(sc_arg);", "    return sc_v0;", "}", "",
  "contract SynthesizedRollback {",
  "    function run(input: uint256) public returns (uint256) {",
  "        let sc_input: word = Typedef.rep(input);",
  "        let sc_old0: word = sload(0);", "        let sc_old1: word = sload(1);",
  "        let sc_computed: word = sc_step(sc_input + sc_old0);",
  "        sstore(0, sc_computed);", "        sstore(1, sc_old1 + 1);",
  "        let sc_final0: word = sload(0);", "        let sc_final1: word = sload(1);",
  "        let sc_result: word = sc_final0 + sc_final1;",
  "        if ((sc_input & 1) == 1) {", "            mstore(0, sc_result);",
  "            revert_(0, 32);", "        }",
  "        return uint256(sc_result);", "    }", "}", ""]

private def formattingChecks : IO Unit := do
  let source ← emitted (← checked [increment])
  ensure (source.source == expectedBasic) "rollback protocol source changed"
  ensure (source.contractName == "SynthesizedRollback" && source.methodSignature == "run(uint256)" &&
    source.deployPath == ["SynthesizedRollbackDeploy"] &&
    source.runtimePath == ["SynthesizedRollbackDeploy", "SynthesizedRollback"])
    "rollback wrapper metadata changed"
  ensure (Solcore.Synthesis.Source.StorageRollback.emitterVersion == "solcore-source-storage-rollback-v2" &&
    Solcore.Synthesis.Source.StorageRollback.wrapperVersion == "solcore-word-storage-rollback-contract-v1" &&
    Solcore.Synthesis.Source.StorageRollback.selector == "0xa444f5e9" &&
    StorageRollback.version == "core-storage-rollback-contract-v1") "rollback provenance changed"

private def observerChecks : IO Unit := do
  let plan ← checked [.var 0]
  let transactions : List StorageExecution.Transaction :=
    [⟨"first", Word.ofNatModulo 2⟩, ⟨"rollback", Word.ofNatModulo 3⟩, ⟨"after", Word.ofNatModulo 4⟩]
  let history := StorageExecution.observeContract plan.contract transactions StorageExecution.fixtureBindings 10000
  let rows := (history.getObjValAs? (List Json) "transactions").toOption.getD []
  ensure ((history.getObjValAs? String "status").toOption == some "complete" && rows.length == 3 &&
    rows.map (fun row => (row.getObjValAs? String "status").toOption) ==
      [some "returned", some "reverted", some "returned"])
    "public observer did not continue after a completed revert"
  ensure ((rows[0]?.bind fun row => (row.getObjVal? "committedStorage").toOption) ==
    (rows[1]?.bind fun row => (row.getObjVal? "committedStorage").toOption))
    "public observer exported tentative reverted storage"
  let exhausted := StorageExecution.observeContract plan.contract transactions StorageExecution.fixtureBindings 0
  ensure ((exhausted.getObjValAs? String "status").toOption == some "incomplete" &&
    (exhausted.getObjValAs? (List String) "unexecuted").toOption == some ["rollback", "after"])
    "public observer conflated fuel exhaustion with a completed rollback"

def testSourceStorageRollbackEmitter : IO Unit := do
  admissionChecks
  executionChecks
  formattingChecks
  observerChecks

end Tests.SourceStorageRollbackEmitter
end
