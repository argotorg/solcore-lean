import Solcore.Synthesis.Source.AdtStorageCases

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
