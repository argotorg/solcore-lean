import Solcore.Synthesis.Source.AggregateCallGraphCases

/-! The fixed aggregate call-graph corpus checks actual original Core execution
against independently computed Words. Feature and composition-shape inventories
describe syntax; source/Rust/EVM agreement is a separate external validation. -/
set_option autoImplicit false

namespace Tests.SourceAggregateCallGraphCorpus
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

def aggregateFeatures : List String := ["pair", "first", "second", "inLeft", "inRight", "case"]

private def versions : List (String × String) := [
  ("profileVersion", AggregateCallGraph.profileVersion), ("functionVersion", AggregateCallGraph.functionVersion),
  ("generatorVersion", AggregateCallGraph.generatorVersion), ("boundaryVersion", AggregateCallGraph.boundaryVersion),
  ("shapeVersion", Solcore.Synthesis.Source.AggregateCallGraph.shapeVersion),
  ("emitterVersion", AggregateCallGraph.emitterVersion), ("wrapperVersion", AggregateCallGraph.wrapperVersion)]

/-- Imported entries are emitted from their saved graph; generated entries are
regenerated from their seed. Both are checked by full canonical replay. -/
private def entryCase (entry : Json) (input : Word) (fuel : Nat) : Except String Json := do
  if let .ok request := entry.getObjVal? "generation" then
    let some seed := (← request.getObjValAs? String "seed").toNat? | throw "invalid generation seed"
    let nodes ← request.getObjValAs? Nat "maxProgramNodes"
    let corpus := AggregateCallGraph.generateCases (Seed.ofNat seed) nodes 8 1 fuel
    require ((← string corpus "status") == "complete") "generated entry was excluded"
    let some saved := (← corpus.getObjValAs? (Array Json) "cases").find? (fun row =>
        (row.getObjValAs? String "input").toOption == some (toString input.val)) |
      throw "generated entry input is outside its boundary group"
    return saved
  let function ← AggregateCallGraph.checkedFunction (← entry.getObjVal? "program")
  AggregateCallGraph.emitCase function input (Json.mkObj [("kind", toJson "imported")]) fuel

def validateManifest (manifest : Json) (fuel : Nat := 1000000) : Except String Json := do
  require ((← string manifest "schema") == "solcore-lean.semantic-corpus-manifest.v1" &&
    (← string manifest "profile") == "runtime-aggregate-call-graphs" &&
    (← string manifest "coverageKind") == "core-ast-features") "unexpected aggregate call-graph manifest scope"
  for (key, expected) in versions do
    require ((← string manifest key) == expected) ("aggregate call-graph manifest changed " ++ key)
  let requiredFeatures ← strings manifest "requiredFeatures"
  require (sameMembers requiredFeatures
      ("functionCall" :: aggregateFeatures ++ Feature.catalog.toList.map featureName))
    "aggregate call-graph corpus must require every scalar and aggregate AST feature and calls"
  let requiredInputs ← strings manifest "requiredInputs"
  require (sameMembers requiredInputs (AggregateCallGraph.boundaryInputs.map fun value => toString value.val))
    "aggregate call-graph corpus must require all eight boundary inputs"
  let requiredHelpers ← manifest.getObjValAs? (List Nat) "requiredHelperCounts"
  require (requiredHelpers == [1, 2, 3]) "fixed aggregate call-graph corpus must require one, two and three helpers"
  let requiredShapes ← strings manifest "requiredAggregateShapes"
  require (requiredShapes == Solcore.Synthesis.Core.AggregateCallGraph.shapeCatalog)
    "fixed aggregate call-graph corpus must require the canonical nine composition shapes"
  let requiredLiterals ← strings manifest "requiredWordLiterals"
  let entries ← manifest.getObjValAs? (Array Json) "cases"
  require (0 < entries.size && entries.size ≤ 128) "aggregate call-graph corpus must contain 1..128 cases"
  let mut identifiers : List String := []
  let mut inputs : List String := []
  let mut counts : List Nat := []
  let mut featureUnion : List String := []
  let mut shapeUnion : List String := []
  let mut literalUnion : List String := []
  let mut sources : List (String × String) := []
  let mut generated := 0
  let mut reductions := 0
  let mut maxAppliedNodes := 0
  for entry in entries do
    let identifier ← string entry "id"
    require (!identifier.isEmpty && identifier.length ≤ 80 && !identifiers.contains identifier)
      "aggregate call-graph case ID is empty, duplicated or too long"
    identifiers := identifiers ++ [identifier]
    require ((entry.getObjVal? "generation").isOk != (entry.getObjVal? "program").isOk)
      (identifier ++ ": entry needs exactly one generation request or program")
    let input ← AggregateCallGraph.inputWord (← string entry "input")
    let expected ← AggregateCallGraph.inputWord (← string entry "expectedCore")
    let saved ← (entryCase entry input fuel).mapError (identifier ++ ": " ++ ·)
    require (saved == (← entryCase entry input fuel)) (identifier ++ ": nondeterministic emission")
    require ((← AggregateCallGraph.replayCase saved fuel) == saved) (identifier ++ ": native replay differs")
    let admitted ← AggregateCallGraph.caseProgram saved
    let function := admitted.function
    if let .ok original := entry.getObjVal? "program" then
      require (Wire.encodeProgram function.program == original) (identifier ++ ": noncanonical graph")
    else generated := generated + 1
    require (admitted.input == input && admitted.program.check && Wire.programNodes admitted.program ≤ 512)
      (identifier ++ ": original Core application failed its input, checker or full node bound")
    maxAppliedNodes := max maxAppliedNodes (Wire.programNodes admitted.program)
    let expectedFeatures ← strings entry "expectedFeatures"
    require (sameMembers expectedFeatures function.features && AggregateCallGraph.hasEntryCall function)
      (identifier ++ ": expected features differ or entry contains no helper call")
    let expectedCount ← entry.getObjValAs? Nat "expectedHelperCount"
    require (expectedCount == function.helpers.length) (identifier ++ ": wrong declared helper count")
    let expectedShapes ← strings entry "expectedAggregateShapes"
    require (expectedShapes == AggregateCallGraph.aggregateShapes function &&
      AggregateCallGraph.hasCallComposition function) (identifier ++ ": wrong composition shapes")
    let actual ← saved.getObjVal? "directCore"
    require ((← string actual "status") == "returned" && (← string actual "word") == toString expected.val)
      (identifier ++ ": actual Core result differs from its independent golden")
    let forged := saved.setObjVal! "directCore" (Json.mkObj [("status", toJson "forged")])
    require ((← AggregateCallGraph.replayCase forged fuel) == saved)
      (identifier ++ ": stored observation became an oracle")
    let source ← string saved "source"
    let key := (Wire.encodeProgram function.program).compress
    if let some (_, previous) := sources.find? (fun item => item.1 == key) then
      require (source == previous) (identifier ++ ": emitted source depends on runtime input")
    else sources := sources ++ [(key, source)]
    let candidates ← AggregateCallGraph.shrinkCases saved 4 fuel
    for reduced in (← candidates.getObjValAs? (Array Json) "cases") do
      let candidate ← AggregateCallGraph.caseProgram reduced
      require (candidate.program.check && candidate.function.helpers.length == function.helpers.length &&
        Aggregate.bindingInventory candidate.function == Aggregate.bindingInventory function &&
        (complexity candidate.program.body).isStrictlySmaller (complexity admitted.program.body))
        (identifier ++ ": shrink changed helpers or binders, is untyped or is not strictly smaller")
      require ((← AggregateCallGraph.replayCase reduced fuel) == reduced) (identifier ++ ": reduced case failed replay")
      reductions := reductions + 1
    inputs := (inputs ++ [toString input.val]).eraseDups
    counts := (counts ++ [function.helpers.length]).eraseDups
    featureUnion := (featureUnion ++ function.features).eraseDups
    shapeUnion := (shapeUnion ++ expectedShapes).eraseDups
    literalUnion := (literalUnion ++ ((function.helpers ++ [function.entry]).flatMap wordLiterals).map
      (fun value => toString value.val)).eraseDups
  require (requiredFeatures.all featureUnion.contains) "native-completed cases missed required AST features"
  require (requiredInputs.all inputs.contains) "native-completed cases missed required runtime inputs"
  require (requiredHelpers.all counts.contains) "native-completed cases missed required helper counts"
  require (requiredShapes.all shapeUnion.contains) "native-completed cases missed required composition shapes"
  require (requiredLiterals.all literalUnion.contains) "native-completed cases missed required Word literals"
  return Json.mkObj [
    ("status", toJson "complete"), ("cases", toJson entries.size), ("functions", toJson sources.length),
    ("generatedCases", toJson generated), ("features", toJson featureUnion.length),
    ("inputs", toJson inputs.length), ("helperCounts", toJson counts),
    ("aggregateShapes", toJson requiredShapes), ("maxAppliedNodes", toJson maxAppliedNodes),
    ("shrinks", toJson reductions), ("nativeCoreExecuted", toJson true),
    ("rustExecuted", toJson false), ("evmExecuted", toJson false)]

private def checked {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def rejects {α : Type} (result : Except String α) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "invalid aggregate call-graph corpus unexpectedly passed")

def testSourceAggregateCallGraphCorpus : IO Unit := do
  let manifest ← checked (Json.parse (← IO.FS.readFile "scripts/semantic-aggregate-call-graph-corpus.json"))
  let summary ← checked (validateManifest manifest)
  let entries ← checked (manifest.getObjValAs? (Array Json) "cases")
  let some first := entries[0]? | throw (IO.userError "missing first aggregate call-graph case")
  let some generatedEntry := entries.find? (fun entry => (entry.getObjVal? "generation").isOk) |
    throw (IO.userError "missing generated aggregate call-graph case")
  let replace := fun (original changed : Json) => manifest.setObjVal! "cases"
    (.arr (entries.map fun entry => if entry == original then changed else entry))
  let expected ← checked (AggregateCallGraph.inputWord (← checked (string first "expectedCore")))
  let wrong := toJson (toString ((expected.val + 1) % (2 ^ 256)))
  rejects (validateManifest (replace first (first.setObjVal! "expectedCore" wrong)))
  rejects (validateManifest (replace generatedEntry (generatedEntry.setObjVal! "expectedCore" wrong)))
  rejects (validateManifest (replace first (first.setObjVal! "expectedHelperCount" (toJson (1 : Nat)))))
  rejects (validateManifest (replace first (first.setObjVal! "expectedAggregateShapes" (toJson ([] : List String)))))
  rejects (validateManifest (replace first (first.setObjVal! "expectedFeatures" (toJson ([] : List String)))))
  rejects (validateManifest (replace first (first.setObjVal! "input" (toJson "00"))))
  rejects (validateManifest (replace first (first.setObjVal! "program" (Wire.encodeProgram
    {resultType := .function .word .word, dataDefinitions := [], body := .lambda .word .word (.var 0)}))))
  rejects (validateManifest (replace first (first.setObjVal! "generation"
    (Json.mkObj [("seed", toJson "13"), ("maxProgramNodes", toJson (192 : Nat))]))))
  rejects (validateManifest (manifest.setObjVal! "cases" (.arr (entries.push first))))
  for (key, value) in [
      ("profile", toJson "runtime-call-graphs"), ("shapeVersion", toJson "forged"),
      ("cases", .arr #[]), ("requiredInputs", toJson ([] : List String)),
      ("requiredFeatures", toJson ([] : List String)), ("requiredHelperCounts", toJson [1, 2]),
      ("requiredAggregateShapes", toJson ([] : List String)),
      ("requiredAggregateShapes", toJson Solcore.Synthesis.Core.AggregateCallGraph.shapeCatalog.reverse)] do
    rejects (validateManifest (manifest.setObjVal! key value))
  rejects (validateManifest manifest 0)
  IO.println summary.compress

end Tests.SourceAggregateCallGraphCorpus
