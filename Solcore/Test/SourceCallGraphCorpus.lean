import Solcore.Synthesis.Source.CallGraphCases

/-! The fixed call-graph corpus checks actual original Core execution against
hand-computed boundary Words. Its feature and shape inventories describe syntax;
source/Rust/EVM agreement is a separate external validation. -/
set_option autoImplicit false

namespace Tests.SourceCallGraphCorpus
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
  ("profileVersion", CallGraph.profileVersion), ("functionVersion", wordFunctionDAGVersion),
  ("generatorVersion", CallGraph.generatorVersion), ("boundaryVersion", CallGraph.boundaryVersion),
  ("callShapeVersion", Solcore.Synthesis.Source.CallGraph.callShapeVersion),
  ("emitterVersion", CallGraph.emitterVersion), ("wrapperVersion", CallGraph.wrapperVersion)]

/-- Sealing, execution, canonical replay and strictly smaller typed reductions
all operate on the original graph, independently of the source emitter output. -/
def validateManifest (manifest : Json) (fuel : Nat := 100000) : Except String Json := do
  require ((← string manifest "schema") == "solcore-lean.semantic-corpus-manifest.v1" &&
    (← string manifest "profile") == "runtime-call-graphs" &&
    (← string manifest "coverageKind") == "core-ast-features") "unexpected call-graph manifest scope"
  for (key, expected) in versions do
    require ((← string manifest key) == expected) ("call-graph manifest changed " ++ key)
  let requiredFeatures ← strings manifest "requiredFeatures"
  require (sameMembers requiredFeatures ("functionCall" :: Feature.catalog.toList.map featureName))
    "call-graph corpus must require every scalar AST feature and calls"
  let requiredInputs ← strings manifest "requiredInputs"
  require (sameMembers requiredInputs (CallGraph.boundaryInputs.map fun value => toString value.val))
    "call-graph corpus must require all eight boundary inputs"
  let requiredHelpers ← manifest.getObjValAs? (List Nat) "requiredHelperCounts"
  require (requiredHelpers == [1, 2, 3]) "fixed call-graph corpus must require one, two and three helpers"
  let requiredShapes ← strings manifest "requiredCallShapes"
  require (requiredShapes == Solcore.Synthesis.Core.CallGraph.callShapeCatalog)
    "fixed call-graph corpus must require the canonical nine AST shapes"
  let requiredLiterals ← strings manifest "requiredWordLiterals"
  let entries ← manifest.getObjValAs? (Array Json) "cases"
  require (0 < entries.size && entries.size ≤ 128) "call-graph corpus must contain 1..128 cases"
  let mut identifiers : List String := []
  let mut inputs : List String := []
  let mut counts : List Nat := []
  let mut featureUnion : List String := []
  let mut shapeUnion : List String := []
  let mut literalUnion : List String := []
  let mut sources : List (String × String) := []
  let mut reductions := 0
  let mut maxAppliedNodes := 0
  for entry in entries do
    let identifier ← string entry "id"
    require (!identifier.isEmpty && identifier.length ≤ 80 && !identifiers.contains identifier)
      "call-graph case ID is empty, duplicated or too long"
    identifiers := identifiers ++ [identifier]
    let original ← entry.getObjVal? "program"
    let function ← CallGraph.checkedFunction original
    require (Wire.encodeProgram function.program == original) (identifier ++ ": noncanonical graph")
    let input ← CallGraph.inputWord (← string entry "input")
    let expected ← CallGraph.inputWord (← string entry "expectedCore")
    let expectedFeatures ← strings entry "expectedFeatures"
    require (sameMembers expectedFeatures function.features &&
      (functionFeatures function.entry).contains "functionCall")
      (identifier ++ ": expected features differ or entry contains no helper call")
    let expectedCount ← entry.getObjValAs? Nat "expectedHelperCount"
    require (expectedCount == function.helpers.length) (identifier ++ ": wrong declared helper count")
    let expectedShapes ← strings entry "expectedCallShapes"
    require (expectedShapes == CallGraph.callShapes function) (identifier ++ ": wrong AST call shapes")
    let origin := Json.mkObj [("kind", toJson "imported")]
    let saved ← CallGraph.emitCase function input origin fuel
    require (saved == (← CallGraph.emitCase function input origin fuel)) (identifier ++ ": nondeterministic emission")
    require ((← CallGraph.replayCase saved fuel) == saved) (identifier ++ ": native replay differs")
    let admitted ← CallGraph.caseProgram saved
    require (admitted.program.check && Wire.programNodes admitted.program ≤ 512)
      (identifier ++ ": original Core application failed its checker or full node bound")
    maxAppliedNodes := max maxAppliedNodes (Wire.programNodes admitted.program)
    let actual ← saved.getObjVal? "directCore"
    require ((← string actual "status") == "returned" && (← string actual "word") == toString expected.val)
      (identifier ++ ": actual Core result differs from its independent boundary golden")
    let provenance ← saved.getObjVal? "provenance"
    require ((← provenance.getObjValAs? Nat "helperCount") == expectedCount &&
      (← provenance.getObjValAs? (List String) "callShapes") == expectedShapes)
      (identifier ++ ": source case lost its authenticated syntax metadata")
    let forged := saved.setObjVal! "directCore" (Json.mkObj [("status", toJson "forged")])
    require ((← CallGraph.replayCase forged fuel) == saved) (identifier ++ ": stored observation became an oracle")
    let source ← string saved "source"
    let key := original.compress
    if let some (_, previous) := sources.find? (fun item => item.1 == key) then
      require (source == previous) (identifier ++ ": emitted source depends on runtime input")
    else sources := sources ++ [(key, source)]
    let candidates ← CallGraph.shrinkCases saved 4 fuel
    for reduced in (← candidates.getObjValAs? (Array Json) "cases") do
      let candidate ← CallGraph.caseProgram reduced
      require (candidate.program.check && candidate.function.helpers.length == function.helpers.length &&
        (complexity candidate.program.body).isStrictlySmaller (complexity admitted.program.body))
        (identifier ++ ": shrink changed helper bindings, is untyped or is not strictly smaller")
      require ((← CallGraph.replayCase reduced fuel) == reduced) (identifier ++ ": reduced case failed replay")
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
  require (requiredShapes.all shapeUnion.contains) "native-completed cases missed required AST call shapes"
  require (requiredLiterals.all literalUnion.contains) "native-completed cases missed required Word literals"
  return Json.mkObj [
    ("status", toJson "complete"), ("cases", toJson entries.size), ("functions", toJson sources.length),
    ("features", toJson featureUnion.length), ("inputs", toJson inputs.length), ("helperCounts", toJson counts),
    ("callShapes", toJson requiredShapes), ("maxAppliedNodes", toJson maxAppliedNodes),
    ("shrinks", toJson reductions), ("nativeCoreExecuted", toJson true),
    ("rustExecuted", toJson false), ("evmExecuted", toJson false)]

private def checked {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def rejects {α : Type} (result : Except String α) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "invalid call-graph corpus unexpectedly passed")

def testSourceCallGraphCorpus : IO Unit := do
  let manifest ← checked (Json.parse (← IO.FS.readFile "scripts/semantic-call-graph-corpus.json"))
  let summary ← checked (validateManifest manifest)
  let entries ← checked (manifest.getObjValAs? (Array Json) "cases")
  let some first := entries[0]? | throw (IO.userError "missing first call-graph case")
  let replaceFirst := fun entry => manifest.setObjVal! "cases" (.arr (entries.set! 0 entry))
  let expected ← checked (CallGraph.inputWord (← checked (string first "expectedCore")))
  rejects (validateManifest (replaceFirst (first.setObjVal! "expectedCore"
    (toJson (toString ((expected.val + 1) % (2 ^ 256)))))))
  rejects (validateManifest (replaceFirst (first.setObjVal! "expectedHelperCount" (toJson (1 : Nat)))))
  rejects (validateManifest (replaceFirst (first.setObjVal! "expectedCallShapes" (toJson ([] : List String)))))
  rejects (validateManifest (replaceFirst (first.setObjVal! "expectedFeatures" (toJson ([] : List String)))))
  rejects (validateManifest (replaceFirst (first.setObjVal! "input" (toJson "00"))))
  rejects (validateManifest (replaceFirst (first.setObjVal! "program" (Wire.encodeProgram
    {resultType := .function .word .word, dataDefinitions := [], body := .lambda .word .word (.var 0)}))))
  rejects (validateManifest (manifest.setObjVal! "cases" (.arr (entries.push first))))
  for (key, value) in [
      ("profile", toJson "runtime-functions"), ("callShapeVersion", toJson "forged"),
      ("cases", .arr #[]), ("requiredInputs", toJson ([] : List String)),
      ("requiredFeatures", toJson ([] : List String)), ("requiredHelperCounts", toJson [1, 2]),
      ("requiredCallShapes", toJson ([] : List String)),
      ("requiredCallShapes", toJson Solcore.Synthesis.Core.CallGraph.callShapeCatalog.reverse)] do
    rejects (validateManifest (manifest.setObjVal! key value))
  rejects (validateManifest manifest 0)
  IO.println summary.compress

end Tests.SourceCallGraphCorpus
