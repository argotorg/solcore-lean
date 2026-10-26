import Solcore.Synthesis.Source.CallGraphLoopCases

/-! The fixed call-graph loop corpus checks actual original Core execution
against independently computed Words. Feature, shape, mask and iteration
inventories describe syntax and the plan definition, not executed traces;
source/Rust/EVM agreement is a separate external validation. -/
set_option autoImplicit false

namespace Tests.SourceCallGraphLoopCorpus
open Lean Solcore.Core Solcore.Synthesis.Core Solcore.Synthesis.Source

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
  ("profileVersion", CallGraphLoop.profileVersion), ("functionVersion", CallGraphLoop.functionVersion),
  ("loopVersion", BoundedLoop.version), ("stepFunctionVersion", wordFunctionDAGVersion),
  ("aggregateVersion", Aggregates.version), ("generatorVersion", CallGraphLoop.generatorVersion),
  ("boundaryVersion", CallGraphLoop.boundaryVersion),
  ("stepBoundaryVersion", CallGraphLoop.stepBoundaryVersion),
  ("callShapeVersion", CallGraphLoop.callShapeVersion),
  ("emitterVersion", CallGraphLoop.emitterVersion), ("wrapperVersion", CallGraphLoop.wrapperVersion)]

/-- Imported entries are emitted from their saved plan; generated entries are
regenerated from their seed. Both are checked by full canonical replay. -/
private def entryCase (entry : Json) (input : Word) (fuel : Nat) : Except String Json := do
  if let .ok request := entry.getObjVal? "generation" then
    let some seed := (← request.getObjValAs? String "seed").toNat? | throw "invalid generation seed"
    let nodes ← request.getObjValAs? Nat "maxProgramNodes"
    let corpus := CallGraphLoop.generateCases (Seed.ofNat seed) nodes 6 1 fuel
    require ((← string corpus "status") == "complete") "generated entry was excluded"
    let some saved := (← corpus.getObjValAs? (Array Json) "cases").find? (fun row =>
        (row.getObjValAs? String "input").toOption == some (toString input.val)) |
      throw "generated entry input is outside its boundary group"
    return saved
  let plan ← CallGraphLoop.checkedPlan (← entry.getObjVal? "loopPlan")
  CallGraphLoop.emitCase plan input (Json.mkObj [("kind", toJson "imported")]) fuel

def validateManifest (manifest : Json) (fuel : Nat := 1000000) : Except String Json := do
  require ((← string manifest "schema") == "solcore-lean.semantic-corpus-manifest.v1" &&
    (← string manifest "profile") == "runtime-call-graph-loops" &&
    (← string manifest "coverageKind") == "core-ast-features") "unexpected call-graph loop manifest scope"
  for (key, expected) in versions do
    require ((← string manifest key) == expected) ("call-graph loop manifest changed " ++ key)
  let requiredFeatures ← strings manifest "requiredFeatures"
  require (sameMembers requiredFeatures ("functionCall" :: Feature.catalog.toList.map featureName))
    "call-graph loop corpus must require every scalar AST feature and calls"
  let requiredInputs ← strings manifest "requiredInputs"
  require (sameMembers requiredInputs (CallGraphLoop.boundaryInputs.map fun value => toString value.val))
    "call-graph loop corpus must require all six loop boundary inputs"
  let requiredHelpers ← manifest.getObjValAs? (List Nat) "requiredHelperCounts"
  require (requiredHelpers == [1, 2, 3]) "fixed call-graph loop corpus must require one, two and three helpers"
  let requiredShapes ← strings manifest "requiredCallShapes"
  require (requiredShapes == Solcore.Synthesis.Core.CallGraph.callShapeCatalog)
    "fixed call-graph loop corpus must require the canonical nine AST shapes"
  let loops ← manifest.getObjVal? "loopRequirements"
  let requiredMasks ← loops.getObjValAs? (List Nat) "masks"
  let requiredIterations ← loops.getObjValAs? (List Nat) "iterations"
  require (requiredMasks == [0, 1, 3, 7] && requiredIterations == [0, 1, 3, 7])
    "fixed call-graph loop corpus must require masks and iterations 0, 1, 3 and 7"
  let requiredLiterals ← strings manifest "requiredWordLiterals"
  let entries ← manifest.getObjValAs? (Array Json) "cases"
  require (0 < entries.size && entries.size ≤ 128) "call-graph loop corpus must contain 1..128 cases"
  let mut identifiers : List String := []
  let mut inputs : List String := []
  let mut counts : List Nat := []
  let mut masks : List Nat := []
  let mut iterations : List Nat := []
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
      "call-graph loop case ID is empty, duplicated or too long"
    identifiers := identifiers ++ [identifier]
    require ((entry.getObjVal? "generation").isOk != (entry.getObjVal? "loopPlan").isOk)
      (identifier ++ ": entry needs exactly one generation request or loop plan")
    let input ← CallGraphLoop.inputWord (← string entry "input")
    let expected ← CallGraphLoop.inputWord (← string entry "expectedCore")
    let saved ← (entryCase entry input fuel).mapError (identifier ++ ": " ++ ·)
    require (saved == (← entryCase entry input fuel)) (identifier ++ ": nondeterministic emission")
    require ((← CallGraphLoop.replayCase saved fuel) == saved) (identifier ++ ": native replay differs")
    let admitted ← CallGraphLoop.caseProgram saved
    let plan := admitted.plan
    if let .ok original := entry.getObjVal? "loopPlan" then
      require (CallGraphLoop.planJson plan == original) (identifier ++ ": noncanonical loop plan")
    else generated := generated + 1
    require (admitted.input == input && admitted.program.check && Wire.programNodes admitted.program ≤ 512)
      (identifier ++ ": original Core loop failed its input, checker or full node bound")
    maxAppliedNodes := max maxAppliedNodes (Wire.programNodes admitted.program)
    let expectedFeatures ← strings entry "expectedFeatures"
    require (sameMembers expectedFeatures plan.features &&
      (functionFeatures plan.graph.entry).contains "functionCall")
      (identifier ++ ": expected features differ or step entry contains no helper call")
    let expectedCount ← entry.getObjValAs? Nat "expectedHelperCount"
    require (expectedCount == plan.graph.helpers.length) (identifier ++ ": wrong declared helper count")
    let expectedShapes ← strings entry "expectedCallShapes"
    require (expectedShapes == CallGraphLoop.callShapes plan) (identifier ++ ": wrong AST call shapes")
    let actual ← saved.getObjVal? "directCore"
    require ((← string actual "status") == "returned" && (← string actual "word") == toString expected.val)
      (identifier ++ ": actual Core result differs from its independent golden")
    let forged := saved.setObjVal! "directCore" (Json.mkObj [("status", toJson "forged")])
    require ((← CallGraphLoop.replayCase forged fuel) == saved) (identifier ++ ": stored observation became an oracle")
    let source ← string saved "source"
    let key := (CallGraphLoop.planJson plan).compress
    if let some (_, previous) := sources.find? (fun item => item.1 == key) then
      require (source == previous) (identifier ++ ": emitted source depends on runtime input")
    else sources := sources ++ [(key, source)]
    let candidates ← CallGraphLoop.shrinkCases saved 4 fuel
    for reduced in (← candidates.getObjValAs? (Array Json) "cases") do
      let candidate ← CallGraphLoop.caseProgram reduced
      require (candidate.program.check && candidate.plan.graph.helpers.length == plan.graph.helpers.length &&
        candidate.plan.mask ≤ plan.mask &&
        (complexity candidate.program.body).isStrictlySmaller (complexity admitted.program.body))
        (identifier ++ ": shrink changed helpers, raised the mask, is untyped or is not strictly smaller")
      require ((← CallGraphLoop.replayCase reduced fuel) == reduced) (identifier ++ ": reduced case failed replay")
      reductions := reductions + 1
    inputs := (inputs ++ [toString input.val]).eraseDups
    counts := (counts ++ [plan.graph.helpers.length]).eraseDups
    masks := (masks ++ [plan.mask]).eraseDups
    iterations := (iterations ++ [(input.bitAnd (Word.ofNatModulo plan.mask)).val]).eraseDups
    featureUnion := (featureUnion ++ plan.features).eraseDups
    shapeUnion := (shapeUnion ++ expectedShapes).eraseDups
    literalUnion := (literalUnion ++ ((plan.graph.helpers ++ [plan.graph.entry]).flatMap wordLiterals).map
      (fun value => toString value.val)).eraseDups
  require (requiredFeatures.all featureUnion.contains) "native-completed cases missed required AST features"
  require (requiredInputs.all inputs.contains) "native-completed cases missed required runtime inputs"
  require (requiredHelpers.all counts.contains) "native-completed cases missed required helper counts"
  require (requiredShapes.all shapeUnion.contains) "native-completed cases missed required AST call shapes"
  require (requiredMasks.all masks.contains) "native-completed cases missed required loop masks"
  require (requiredIterations.all iterations.contains) "native-completed cases missed required iteration counts"
  require (requiredLiterals.all literalUnion.contains) "native-completed cases missed required Word literals"
  return Json.mkObj [
    ("status", toJson "complete"), ("cases", toJson entries.size), ("plans", toJson sources.length),
    ("generatedCases", toJson generated), ("features", toJson featureUnion.length),
    ("inputs", toJson inputs.length), ("helperCounts", toJson counts), ("masks", toJson masks),
    ("iterations", toJson iterations), ("callShapes", toJson requiredShapes),
    ("maxAppliedNodes", toJson maxAppliedNodes), ("shrinks", toJson reductions),
    ("nativeCoreExecuted", toJson true), ("rustExecuted", toJson false), ("evmExecuted", toJson false)]

private def checked {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def rejects {α : Type} (result : Except String α) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "invalid call-graph loop corpus unexpectedly passed")

def testSourceCallGraphLoopCorpus : IO Unit := do
  let manifest ← checked (Json.parse (← IO.FS.readFile "scripts/semantic-call-graph-loop-corpus.json"))
  let summary ← checked (validateManifest manifest)
  let entries ← checked (manifest.getObjValAs? (Array Json) "cases")
  let some first := entries[0]? | throw (IO.userError "missing first call-graph loop case")
  let some generatedEntry := entries.find? (fun entry => (entry.getObjVal? "generation").isOk) |
    throw (IO.userError "missing generated call-graph loop case")
  let replace := fun (original changed : Json) => manifest.setObjVal! "cases"
    (.arr (entries.map fun entry => if entry == original then changed else entry))
  let expected ← checked (CallGraphLoop.inputWord (← checked (string first "expectedCore")))
  let wrong := toJson (toString ((expected.val + 1) % (2 ^ 256)))
  rejects (validateManifest (replace first (first.setObjVal! "expectedCore" wrong)))
  rejects (validateManifest (replace generatedEntry (generatedEntry.setObjVal! "expectedCore" wrong)))
  rejects (validateManifest (replace first (first.setObjVal! "expectedHelperCount" (toJson (2 : Nat)))))
  rejects (validateManifest (replace first (first.setObjVal! "expectedCallShapes" (toJson ([] : List String)))))
  rejects (validateManifest (replace first (first.setObjVal! "expectedFeatures" (toJson ([] : List String)))))
  rejects (validateManifest (replace first (first.setObjVal! "input" (toJson "00"))))
  let plan ← checked (first.getObjVal? "loopPlan")
  rejects (validateManifest (replace first (first.setObjVal! "loopPlan" (plan.setObjVal! "mask" (toJson (2 : Nat))))))
  rejects (validateManifest (replace first (first.setObjVal! "loopPlan"
    (plan.setObjVal! "schema" (toJson "solcore-lean.loop-plan.v1")))))
  rejects (validateManifest (replace first (first.setObjVal! "generation"
    (Json.mkObj [("seed", toJson "3"), ("maxProgramNodes", toJson (256 : Nat))]))))
  rejects (validateManifest (replace generatedEntry (generatedEntry.setObjVal! "generation"
    (Json.mkObj [("seed", toJson "1"), ("maxProgramNodes", toJson (256 : Nat))]))))
  rejects (validateManifest (manifest.setObjVal! "cases" (.arr (entries.push first))))
  for (key, value) in [
      ("profile", toJson "runtime-loops"), ("loopVersion", toJson "forged"),
      ("cases", .arr #[]), ("requiredInputs", toJson ([] : List String)),
      ("requiredFeatures", toJson ([] : List String)), ("requiredHelperCounts", toJson [1, 2]),
      ("requiredCallShapes", toJson ([] : List String)),
      ("loopRequirements", Json.mkObj [("masks", toJson [1, 3, 7]), ("iterations", toJson [0, 1, 3, 7])]),
      ("requiredCallShapes", toJson Solcore.Synthesis.Core.CallGraph.callShapeCatalog.reverse)] do
    rejects (validateManifest (manifest.setObjVal! key value))
  rejects (validateManifest manifest 0)
  IO.println summary.compress

end Tests.SourceCallGraphLoopCorpus
