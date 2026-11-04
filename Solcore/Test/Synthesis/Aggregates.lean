import Solcore.Synthesis.Source.AggregateCallGraphCases
import Solcore.Synthesis.Source.AggregateCallGraphEmitter
import Solcore.Synthesis.Source.CallGraphEmitter
import Solcore.Test.Synthesis.CallGraphs
import Solcore.Core.Machine
import Solcore.Core.Wire.Codec.Program
import Solcore.Synthesis.Source.AggregateCases
import Solcore.Synthesis.Source.AggregateEmitter
import Solcore.Synthesis.Source.AggregateRenderer
import Solcore.Synthesis.Source.PrimitiveEmitter
import Solcore.Synthesis.Source.ClosureCases
import Solcore.Synthesis.Source.ClosureEmitter
import Solcore.Synthesis.Source.LoopClosureCases

/-!
# Aggregate and closure profile tests

Aggregates, aggregate call graphs, closures and loop closures.
-/

section
-- leanmerge: from Solcore.Test.SourceAggregateCallGraphCorpus
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
end

section
-- leanmerge: from Solcore.Test.SourceAggregateCallGraphEmitter
/-! Generation, composition shapes and exact source shape for graphs that
compose Word pairs, Word sums, projections and case payload scopes with helper
calls. Only original Core programs are executed here; these tests neither run
emitted source nor prove compiler meaning preservation. -/
set_option autoImplicit false

namespace Tests.SourceAggregateCallGraphEmitter
open Solcore.Core Solcore.Synthesis.Core Solcore.Synthesis.Source

private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)
private def call (index : Nat) (argument : Wire.Expr) : Wire.Expr := .apply (.var index) argument
private def maximum : Nat := Word.maximum.val
private def high : Nat := 2 ^ 255

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def graph (helpers : List Wire.Expr) (entry : Wire.Expr) : IO Aggregates.CheckedDAG :=
  match Aggregates.CheckedDAG.ofParts? helpers entry with
  | some value => pure value
  | none => throw (IO.userError "aggregate call graph fixture failed checked admission")

private def emitted (value : Aggregates.CheckedDAG) : IO EmittedProgram :=
  match AggregateCallGraph.emit value with
  | .ok source => pure source
  | .error error => throw (IO.userError s!"aggregate call graph emission failed: {reprStr error}")

private def observe (value : Aggregates.CheckedDAG) (input expected : Nat) : IO Unit := do
  let original := value.instantiate (Word.ofNatModulo input)
  ensure original.check "original applied aggregate graph failed Core typing"
  match original.toCore.runStateful 100000 with
  | .done (.word result) state =>
      ensure (result.val == expected) s!"original Core result {result.val} differs from {expected}"
      ensure state.isEmpty "immutable aggregates allocated a cell"
  | _ => throw (IO.userError "original Core aggregate graph did not complete")

/-- h0(x) = x + 1 and h1(x) = 4x + 1 through a let-bound pair of a call and a
product. The entry branches to a sum, cases on it, nests a case whose scrutinee
calls a helper on the payload, and projects a pair built around a call. -/
def allShapesHelpers : List Wire.Expr := [
  .binary .wordAdd (.var 0) (word 1),
  .letE (.pair (call 1 (.var 0)) (.binary .wordMul (.var 0) (word 3)))
    (.binary .wordAdd (.first (.var 0)) (.second (.var 0)))]

def allShapesEntry : Wire.Expr :=
  .letE (.ifE (.binary .wordGt (.var 0) (word 5)) (.inLeft .word (call 1 (.var 0))) (.inRight .word (.var 0)))
    (.caseE (.var 0)
      (.binary .wordAdd (call 4 (.var 0)) (.caseE (.inLeft .word (call 4 (.var 0))) (.var 0) (.var 0)))
      (call 3 (.first (.pair (.var 0) (call 4 (.var 0))))))

private def shapeChecks : IO Unit := do
  let value ← graph allShapesHelpers allShapesEntry
  ensure (AggregateCallGraph.graphWithinGrammar value && value.program.check) "fixture left the grammar"
  ensure (AggregateCallGraph.structuralShapes value == AggregateCallGraph.shapeCatalog)
    "the mixed graph no longer covers the exact ordered nine composition shapes"
  -- x > 5: 8x + 4 through the left payload; otherwise 4x + 1 through the right.
  for (input, expected) in [(0, 1), (1, 5), (2, 9), (255, 2044), (256, 2052),
      (maximum, maximum - 3), (high, 4), (high - 1, maximum - 3)] do
    observe value input expected
  -- Each shape is detected by its own minimal composition, nowhere else.
  let single : List (String × List Wire.Expr × Wire.Expr) := [
    ("pair-component-call", [.var 0], .first (.pair (call 1 (.var 0)) (word 2))),
    ("sum-payload-call", [.var 0], .letE (.inRight .word (call 1 (.var 0))) (word 3)),
    ("projected-call-argument", [.var 0], .letE (.pair (.var 0) (word 1)) (call 2 (.second (.var 0)))),
    ("case-scrutinee-call", [.var 0], .caseE (.ifE (.binary .wordEq (call 1 (.var 0)) (word 0))
      (.inLeft .word (word 1)) (.inRight .word (word 2))) (.var 0) (word 7)),
    ("case-branch-call", [.var 0], .caseE (.inLeft .word (.var 0)) (call 2 (.var 1)) (word 0)),
    ("payload-call-argument", [.var 0], .letE (call 1 (.var 0))
      (.caseE (.inRight .word (.var 0)) (word 0) (call 3 (.var 0)))),
    ("aggregate-let", [.var 0], .letE (.inLeft .word (.var 0)) (call 2 (.var 1))),
    ("aggregate-branch", [.var 0], .letE (call 1 (.var 0))
      (.first (.ifE (.bool true) (.pair (.var 0) (word 1)) (.pair (word 2) (.var 0))))),
    ("nested-case", [.var 0], .letE (call 1 (.var 0))
      (.caseE (.inLeft .word (.var 0)) (.caseE (.inRight .word (.var 0)) (.var 0) (.var 1)) (word 0)))]
  for (shape, helpers, entry) in single do
    let value ← graph helpers entry
    let found := AggregateCallGraph.structuralShapes value
    ensure (found.contains shape) s!"minimal fixture lost composition shape {shape}"
  ensure (AggregateCallGraph.structuralShapes (← graph [.var 0] (call 1 (.var 0)))).isEmpty
    "a scalar call graph claimed an aggregate composition"
  -- A call next to, rather than inside, an aggregate is not a composition.
  let adjacent ← graph [.var 0]
    (.binary .wordAdd (call 1 (.var 0)) (.first (.pair (.var 0) (word 1))))
  ensure (AggregateCallGraph.structuralShapes adjacent).isEmpty "adjacent call was counted as composed"
  -- An argument that names an outer local, not the payload, is not a payload call.
  let outer ← graph [.var 0] (.caseE (.inLeft .word (word 1)) (call 2 (.var 1)) (word 0))
  ensure (AggregateCallGraph.structuralShapes outer == ["case-branch-call"])
    "an outer local was mistaken for the case payload"

private def generationChecks : IO Unit := do
  let mut shapes : List String := []
  let mut features : List String := []
  for budget in [96, 192, 256] do
    for seed in List.range 96 do
      let request : AggregateCallGraph.Request := {seed := Seed.ofNat seed, maxProgramNodes := budget}
      match AggregateCallGraph.generate request with
      | .error error => throw (IO.userError s!"aggregate graph generation failed: {reprStr error}")
      | .ok generated =>
          let value := generated.function
          ensure (generated.nodeCount ≤ budget && value.program.check &&
            AggregateCallGraph.graphWithinGrammar value) "generated graph escaped budget, typing or grammar"
          ensure (generated.bodyBudgets.length == value.helpers.length + 1) "body budgets lost a body"
          match AggregateCallGraph.generate request with
          | .ok again => ensure (Wire.encodeProgram again.function.program == Wire.encodeProgram value.program &&
              again.finalSeed == generated.finalSeed) "aggregate graph generation is not deterministic"
          | .error _ => throw (IO.userError "repeated generation failed")
          shapes := (shapes ++ AggregateCallGraph.structuralShapes value).eraseDups
          features := (features ++ value.features).eraseDups
          let _ ← emitted value
  ensure (AggregateCallGraph.shapeCatalog.all shapes.contains) "generation census missed a composition shape"
  ensure (["pair", "first", "second", "inLeft", "inRight", "case", "functionCall", "let", "if",
      "ternary:Solcore.Core.Wire.TernaryOp.wordMulMod", "unary:Solcore.Core.Wire.UnaryOp.wordClz"].all features.contains)
    "generation census missed an aggregate or primitive feature"
  ensure (!features.contains "newCell" && !features.contains "unitLiteral") "generation produced a cell or Unit"
  ensure (AggregateCallGraph.generate {seed := Seed.ofNat 0, maxProgramNodes := 513} matches .error .budgetTooLarge)
    "oversized aggregate budget accepted"
  ensure (AggregateCallGraph.generate {seed := Seed.ofNat 0, maxProgramNodes := 12} matches .error .budgetTooSmall)
    "aggregate budget below one helper accepted"

/-- Scalar-only bodies must render exactly as in the call-graph profile. -/
private def compatibilityChecks : IO Unit := do
  let bodies : List (List String × Wire.Expr) := [
    (["near", "far"], .binary .wordShl (call 2 (call 1 (.var 0))) (call 1 (word 1))),
    (["sc_fn0"], .ifE (.binary .wordSgt (call 1 (.var 0)) (word 0)) (.letE (word 7) (call 2 (.var 0))) (call 1 (word 9))),
    (["sc_fn1", "sc_fn0"], .letE (call 1 (.var 0)) (.ternary .wordMulMod (.var 0) (call 3 (.var 1)) (word 7))),
    ([], .unary .wordClz (.binary .wordSdiv (.var 0) (.unary .wordNot (word 5))))]
  for (functions, body) in bodies do
    match AggregateCallGraphRenderer.render functions .word [.word "input"] 4 3 body,
        CallGraphRenderer.renderWithFunctions functions .word ["input"] 4 3 body with
    | .ok actual, .ok expected =>
        ensure (actual.lines == expected.lines && actual.value == expected.value && actual.nextId == expected.nextId)
          "scalar formatting drifted from the call-graph renderer"
    | _, _ => throw (IO.userError "scalar compatibility fixture was rejected")
  -- Every scalar helper of the call-graph emitter fixture renders identically.
  for (body, index) in Tests.SourceCallGraphEmitter.mixedHelpers.zipIdx do
    let names := (List.range index).reverse.map CallGraph.helperName
    match AggregateCallGraphRenderer.render names .word [.word "sc_arg"] 4 0 body,
        CallGraphRenderer.renderWithFunctions names .word ["sc_arg"] 4 0 body with
    | .ok actual, .ok expected =>
        ensure (actual.lines == expected.lines && actual.value == expected.value) "helper formatting drifted"
    | _, _ => throw (IO.userError "call-graph helper fixture was rejected")

private def sourceChecks : IO Unit := do
  let projected ← graph [.var 0] (.first (.pair (call 1 (.var 0)) (.var 0)))
  let source ← emitted projected
  ensure (source == (← emitted projected)) "aggregate call graph emission is nondeterministic"
  ensure (source.contractName == "SynthesizedAggregateCallGraphs" && source.methodName == "run" &&
    source.methodSignature == "run(uint256)" && source.deployPath == ["SynthesizedAggregateCallGraphsDeploy"] &&
    source.runtimePath == ["SynthesizedAggregateCallGraphsDeploy", "SynthesizedAggregateCallGraphs"])
    "aggregate call graph wrapper metadata changed"
  ensure (AggregateCallGraph.emitterVersion == "solcore-source-aggregate-call-graphs-v1" &&
    AggregateCallGraph.wrapperVersion == "solcore-word-aggregate-call-graphs-contract-v1" &&
    AggregateCallGraph.selector == "0xa444f5e9") "aggregate call graph versions or ABI selector changed"
  ensure (source.source == String.intercalate "\n" [
    "import * from std;", "import * from std.dispatch;", Primitive.opcodeImport, "",
    "function sc_fn0(sc_arg: word) returns (word) {", "    return sc_arg;", "}", "",
    "contract SynthesizedAggregateCallGraphs {", "    function run(input: uint256) public returns (uint256) {",
    "        let sc_input: word = Typedef.rep(input);", "        let sc_v0: word = sc_input;",
    "        let sc_v1: word = sc_fn0(sc_v0);", "        let sc_v2: (word, word) = (sc_v1, sc_input);",
    "        let sc_v3: word = 0;", "        match (sc_v2) {", "            case (sc_p4, sc_p5) {",
    "                sc_v3 = sc_p4;", "            }", "        }",
    "        return uint256(sc_v3);", "    }", "}", ""])
    "projection of a call pair or the fixed ABI wrapper changed"
  observe projected 9 9
  -- Payloads extend scope before every local; helpers follow the full context.
  let payload ← graph [.binary .wordAdd (.var 0) (word 1)]
    (.letE (.inRight .word (.var 0)) (.caseE (.var 0) (word 0) (call 3 (.var 0))))
  match AggregateCallGraphRenderer.render ["sc_fn0"] .word [.word "input"] 4 0 payload.entry with
  | .ok rendered =>
      ensure (rendered.lines == [
        "    let sc_v0: sum<word, word> = inr(input);", "    let sc_v1: sum<word, word> = sc_v0;",
        "    let sc_v2: word = 0;", "    match (sc_v1) {", "        case inl(sc_p3) {",
        "            let sc_v4: word = 0;", "            sc_v2 = sc_v4;", "        }",
        "        case inr(sc_p5) {", "            let sc_v6: word = sc_p5;",
        "            let sc_v7: word = sc_fn0(sc_v6);", "            sc_v2 = sc_v7;", "        }", "    }"])
        "case payload scope, helper index or branch-local call changed"
  | .error error => throw (IO.userError s!"payload fixture rendering failed: {reprStr error}")
  observe payload 41 42

private def rejectionChecks : IO Unit := do
  let celled ← graph [.var 0] (.letE (.newCell .word (.var 0)) (call 2 (.loadCell (.var 0))))
  ensure (!AggregateCallGraph.graphWithinGrammar celled) "private cells entered the composition grammar"
  ensure (!(AggregateCallGraph.emit celled).toBool) "renderer accepted a private cell"
  let unit ← graph [.var 0] (.letE .unit (call 2 (.var 1)))
  ensure (!AggregateCallGraph.graphWithinGrammar unit) "Unit entered the composition grammar"
  match AggregateCallGraphRenderer.render [] .word [.wordPair "pair"] 4 0 (.var 0) with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "renderer used a pair local as a Word")
  match AggregateCallGraphRenderer.render ["sc_fn0"] .word [.word "input"] 4 0 (.var 1) with
  | .error (.unboundLocal 1) => pure ()
  | _ => throw (IO.userError "helper escaped as a scalar value")
  for body in [(.first (.var 0) : Wire.Expr), .caseE (.var 0) (word 0) (word 1),
      .apply (.var 2) (.var 0), .pair (.var 0) (.pair (word 0) (word 1))] do
    ensure (Aggregates.CheckedDAG.ofParts? [.var 0] body).isNone "ill-typed aggregate composition was admitted"

def testSourceAggregateCallGraphEmitter : IO Unit := do
  shapeChecks
  generationChecks
  compatibilityChecks
  sourceChecks
  rejectionChecks

end Tests.SourceAggregateCallGraphEmitter
end

section
-- leanmerge: from Solcore.Test.SourceAggregateCallGraphCases
/-! Direct aggregate graph generation, strict canonical replay and binder-
preserving typed shrinking. Only original Core executions are performed here. -/
set_option autoImplicit false

namespace Tests.SourceAggregateCallGraphCases
open Lean Solcore.Core Solcore.Synthesis.Core Solcore.Synthesis.Source

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def get {α : Type} : Except String α → IO α
  | .ok result => pure result
  | .error message => throw (IO.userError message)

private def reject {α : Type} (value : Except String α) (message : String) : IO Unit :=
  match value with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError message)

private def graph (helpers : List Wire.Expr) (entry : Wire.Expr) : IO Aggregates.CheckedDAG :=
  match Aggregates.CheckedDAG.ofParts? helpers entry with
  | some value => pure value
  | none => throw (IO.userError "aggregate graph test fixture failed full Core typing")

private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)
private def call (index : Nat) (argument : Wire.Expr) : Wire.Expr := .apply (.var index) argument
private def field (json : Json) (key : String) : IO Json := get (json.getObjVal? key)
private def string (json : Json) (key : String) : IO String := get (json.getObjValAs? String key)
private def natural (json : Json) (key : String) : IO Nat := get (json.getObjValAs? Nat key)
private def rows (json : Json) : IO (Array Json) := get (json.getObjValAs? (Array Json) "cases")

private def imported (function : Aggregates.CheckedDAG) (input : Word) : IO Json :=
  get (AggregateCallGraph.emitCase function input (Json.mkObj [("kind", toJson "imported")]) 20000)

private def mixedGraph : IO Aggregates.CheckedDAG :=
  graph Tests.SourceAggregateCallGraphEmitter.allShapesHelpers Tests.SourceAggregateCallGraphEmitter.allShapesEntry

private def coreAndImports : IO Json := do
  let function ← mixedGraph
  ensure (AggregateCallGraph.aggregateShapes function == AggregateCallGraph.shapeCatalog)
    "mixed graph no longer covers the exact ordered nine composition shapes"
  for (input, expected) in [(0, 1), (2, 9), (256, 2052), (2 ^ 255, 4)] do
    let saved ← imported function (Word.ofNatModulo input)
    let observation ← field saved "directCore"
    ensure ((← string observation "status") == "returned" &&
      (← string observation "word") == toString expected) "aggregate call graph Core golden differs"
    ensure ((← get (AggregateCallGraph.replayCase saved 20000)) == saved) "import replay changed a canonical case"
  let first ← imported function Word.zero
  for input in AggregateCallGraph.boundaryInputs do
    let saved ← imported function input
    ensure ((← string saved "source") == (← string first "source"))
      "emitted source depends on its runtime argument"
    ensure (← get (AggregateCallGraph.caseProgram saved)).program.check "applied graph lost typing"
    let forged := saved.setObjVal! "directCore" (Json.mkObj [("status", toJson "invented")])
    ensure ((← get (AggregateCallGraph.replayCase forged 20000)) == saved) "saved observation supplied the oracle"
    let suspended ← get (AggregateCallGraph.replayCase saved 0)
    ensure ((← string (← field suspended "directCore") "status") == "out-of-fuel")
      "zero fuel was treated as a completed Core result"
  -- Imported graphs may be constant or lack compositions; exploration may not.
  let constant ← graph [word 7] (.first (.pair (call 1 (word 7)) (.var 0)))
  ensure ((← string (← field (← imported constant Word.maximum) "directCore") "word") == "7")
    "constant imported graph was incorrectly excluded"
  reject (AggregateCallGraph.inputSensitive constant 20000) "constant graph admitted as exploration"
  let scalar ← graph [.binary .wordAdd (.var 0) (word 1)] (call 1 (.var 0))
  reject (AggregateCallGraph.inputSensitive scalar 20000) "scalar call graph admitted as an aggregate composition"
  let deadEntry ← graph [.var 0, .first (.pair (.var 0) (call 1 (.var 0)))] (.first (.pair (.var 0) (word 1)))
  reject (AggregateCallGraph.inputSensitive deadEntry 20000) "entry without a call passed exploration filter"
  reject (AggregateCallGraph.inputSensitive function 0) "resource failure passed generation filter"
  let celled ← graph [.var 0] (.letE (.newCell .word (.var 0)) (call 2 (.loadCell (.var 0))))
  reject (AggregateCallGraph.emitCase celled Word.zero (Json.mkObj [("kind", toJson "imported")]) 2000)
    "private cell graph entered the composition profile"
  let oversizedBody := (List.range 256).foldl (fun body _ => .binary .wordAdd body (word 0))
    (.var 0 : Wire.Expr)
  reject (AggregateCallGraph.emitCase (← graph [oversizedBody] (call 1 (.var 0))) Word.zero
    (Json.mkObj [("kind", toJson "imported")]) 2000) "oversized graph escaped applied node budget"
  return first

private def generationChecks : IO Json := do
  let corpus := AggregateCallGraph.generateCases (Seed.ofNat 0) 192 17 128 100000
  ensure (corpus == AggregateCallGraph.generateCases (Seed.ofNat 0) 192 17 128 100000)
    "direct aggregate graph generation is not deterministic"
  ensure ((← string corpus "status") == "complete") "bounded generated corpus did not complete"
  let generated ← rows corpus
  let excluded ← get (corpus.getObjValAs? (Array Json) "excluded")
  ensure (generated.size == 17 && (← natural corpus "attempted") == 3 + excluded.size &&
    (← natural corpus "attempted") ≤ 128) "graph attempts and runtime cases were confused"
  for index in List.range generated.size do
    let saved := generated[index]!
    let admitted ← get (AggregateCallGraph.caseProgram saved)
    let origin ← field (← field saved "provenance") "origin"
    ensure (admitted.program.check && Wire.programNodes admitted.program ≤ 192 &&
      AggregateCallGraph.hasEntryCall admitted.function && AggregateCallGraph.hasCallComposition admitted.function)
      "generated case escaped typing, budget, entry-call or composition filter"
    ensure ((← natural origin "inputIndex") == index % 8 &&
      some admitted.input == AggregateCallGraph.boundaryInputs[index % 8]?) "input bank order changed"
    ensure ((← get (AggregateCallGraph.replayCase saved 100000)) == saved) "generated graph replay differs"
    ensure ((← string (← field (← get (AggregateCallGraph.replayCase saved 0)) "directCore") "status") ==
      "out-of-fuel") "new replay fuel was confused with stored generation validation fuel"
    if index % 8 > 0 then
      ensure ((← string saved "source") == (← string generated[index - index % 8]! "source"))
        "one generated graph emitted different sources across inputs"
  let truncated := AggregateCallGraph.generateCases (Seed.ofNat 0) 192 3 1 100000
  ensure ((← rows truncated).size ≤ 3 && (← natural truncated "attempted") == 1)
    "case count did not bound a boundary group"
  let limited := AggregateCallGraph.generateCases (Seed.ofNat 0) 192 9 1 100000
  ensure ((← rows limited).size ≤ 8 && (← string limited "status") == "generation-exhausted")
    "attempt exhaustion was reported as complete"
  for budget in [12, 513] do
    let invalid := AggregateCallGraph.generateCases (Seed.ofNat 0) budget 1 3 100000
    ensure ((← rows invalid).isEmpty && (← natural invalid "attempted") == 3 &&
      (← get (invalid.getObjValAs? (Array Json) "excluded")).size == 3)
      "invalid requested budget lost bounded exclusions"
  let resources := AggregateCallGraph.generateCases (Seed.ofNat 0) 192 1 8 0
  let reasons ← get (resources.getObjValAs? (Array Json) "excluded")
  ensure ((← rows resources).isEmpty && (← string resources "status") == "generation-exhausted" &&
    reasons.any (fun reason => (reason.getObjValAs? String "category").toOption == some "inconclusive-resource"))
    "fuel exclusion was treated as a pass"
  ensure ((← natural (AggregateCallGraph.generateCases (Seed.ofNat 0) 192 0 100 100000) "attempted") == 0)
    "empty request consumed attempts"
  ensure ((← rows (AggregateCallGraph.generateCases (Seed.ofNat 0) 192 1 0 100000)).isEmpty)
    "zero attempt limit was ignored"
  return corpus

private def tamperingChecks (saved : Json) : IO Unit := do
  let provenance ← field saved "provenance"
  let origin ← field provenance "origin"
  let withOrigin := fun changed => saved.setObjVal! "provenance" (provenance.setObjVal! "origin" changed)
  for name in ["profileVersion", "functionVersion", "generatorVersion", "boundaryVersion",
      "shapeVersion", "emitterVersion", "wrapperVersion"] do
    reject (AggregateCallGraph.replayCase (saved.setObjVal! "provenance"
      (provenance.setObjVal! name (toJson "forged"))) 100000) s!"tampered version {name} accepted"
  for (name, value) in [("seed", toJson "00"), ("seed", toJson "1"),
      ("finalSeed", toJson "0"), ("maxProgramNodes", toJson (513 : Nat)),
      ("bodyBudgets", toJson ([1] : List Nat)), ("helperCount", toJson (99 : Nat)),
      ("inputIndex", toJson (8 : Nat)), ("validationFuel", toJson (10000001 : Nat)),
      ("kind", toJson "call-graph-generated"), ("extra", toJson true)] do
    reject (AggregateCallGraph.replayCase (withOrigin (origin.setObjVal! name value)) 100000)
      s!"tampered generated {name} accepted"
  for (name, value) in [("helperCount", toJson (99 : Nat)),
      ("aggregateShapes", toJson ["invented"]), ("aggregateShapes", toJson ([] : List String)),
      ("features", toJson ([] : List String)), ("callShapes", toJson ([] : List String)),
      ("extra", toJson true)] do
    reject (AggregateCallGraph.replayCase (saved.setObjVal! "provenance" (provenance.setObjVal! name value)) 100000)
      s!"tampered provenance {name} accepted"
  for (name, value) in [("input", toJson "01"), ("input", toJson "1"),
      ("source", toJson "forged"), ("schema", toJson "solcore-lean.semantic-call-graph-case.v1"),
      ("executionFuel", toJson (10000001 : Nat)), ("extra", toJson true)] do
    reject (AggregateCallGraph.replayCase (saved.setObjVal! name value) 100000) s!"tampered envelope {name} accepted"
  let contract ← field saved "contract"
  for (name, value) in [("calldata", toJson "0xa444f5e9"), ("constructorCalldata", toJson "0x00"),
      ("name", toJson "SynthesizedAggregates"), ("runtimePath", toJson ["Other"]), ("extra", toJson true)] do
    reject (AggregateCallGraph.replayCase (saved.setObjVal! "contract" (contract.setObjVal! name value)) 100000)
      "tampered ABI/contract envelope accepted"
  let program ← field saved "program"
  reject (AggregateCallGraph.caseProgram (saved.setObjVal! "program" (program.setObjVal! "extra" (toJson true))))
    "extra Core wire field accepted"
  let bad : Wire.Program := {
    resultType := .word, dataDefinitions := [],
    body := .apply (functionDAGExpression [.var 0] (.first (.var 0))) (word 0)}
  reject (AggregateCallGraph.caseProgram (saved.setObjVal! "program" (Wire.encodeProgram bad)))
    "ill-typed projection escaped case readmission"
  let celled : Wire.Program := {
    resultType := .word, dataDefinitions := [],
    body := .apply (functionDAGExpression [.var 0]
      (.letE (.newCell .word (.var 0)) (call 2 (.loadCell (.var 0))))) (word 0)}
  reject (AggregateCallGraph.caseProgram ((saved.setObjVal! "program" (Wire.encodeProgram celled)).setObjVal!
    "input" (toJson "0"))) "checked private-cell graph escaped the composition grammar"

private def shrinkingChecks (saved : Json) : IO Unit := do
  let source ← get (AggregateCallGraph.caseProgram saved)
  let first ← get (AggregateCallGraph.shrinkCases saved 64 20000)
  ensure (first == (← get (AggregateCallGraph.shrinkCases saved 64 20000))) "shrinking is nondeterministic"
  let candidates ← rows first
  ensure (!candidates.isEmpty && candidates.size ≤ 64) "bounded shrink yielded no candidates"
  for candidate in candidates do
    let admitted ← get (AggregateCallGraph.caseProgram candidate)
    ensure (admitted.program.check && admitted.function.helpers.length == source.function.helpers.length &&
      Aggregate.bindingInventory admitted.function == Aggregate.bindingInventory source.function &&
      AggregateCallGraph.graphWithinGrammar admitted.function &&
      (complexity admitted.program.body).isStrictlySmaller (complexity source.program.body))
      "shrinking lost typing, helpers, binders, grammar or strict measure"
    ensure ((← get (AggregateCallGraph.replayCase candidate 20000)) == candidate) "reduced case failed exact replay"
  let unchangedOrigin := Json.mkObj [("kind", toJson "reduced"),
    ("parentProgram", Wire.encodeProgram source.program), ("parentInput", toJson (toString source.input.val))]
  let unchanged ← get (AggregateCallGraph.emitCase source.function source.input unchangedOrigin 20000)
  reject (AggregateCallGraph.replayCase unchanged 20000) "non-strict self reduction accepted"
  let smallerGraph ← graph [.var 0] (.first (.pair (call 1 (.var 0)) (word 0)))
  let wrongCount ← get (AggregateCallGraph.emitCase smallerGraph Word.zero unchangedOrigin 20000)
  reject (AggregateCallGraph.replayCase wrongCount 20000) "reduction changed helper declarations"
  -- Dropping the entry's sum binder changes the typed binder inventory.
  let unbound ← graph Tests.SourceAggregateCallGraphEmitter.allShapesHelpers (call 1 (.var 0))
  let lostBinder ← get (AggregateCallGraph.emitCase unbound Word.zero unchangedOrigin 20000)
  reject (AggregateCallGraph.replayCase lostBinder 20000) "reduction removed a typed binder or payload scope"
  let reduced := candidates[0]!
  let provenance ← field reduced "provenance"
  let origin ← field provenance "origin"
  for (key, value) in [("parentInput", toJson "01"), ("parentInput", toJson (toString (2 ^ 256))),
      ("parentProgram", Json.null), ("parentPlan", Json.null), ("extra", toJson true)] do
    reject (AggregateCallGraph.replayCase (reduced.setObjVal! "provenance"
      (provenance.setObjVal! "origin" (origin.setObjVal! key value))) 20000)
      "invalid reduced parent provenance accepted"

def testSourceAggregateCallGraphCases : IO Unit := do
  let importedCase ← coreAndImports
  let corpus ← generationChecks
  tamperingChecks (← rows corpus)[0]!
  shrinkingChecks importedCase

end Tests.SourceAggregateCallGraphCases
end

section
-- leanmerge: from Solcore.Test.SourceAggregateCases
/-! Aggregate cases preserve payload scopes, mutable Word cells and the
independent applied Core program across generation, replay and reduction. -/
set_option autoImplicit false

namespace Tests.SourceAggregateCases
open Lean Solcore.Core Solcore.Synthesis.Core Solcore.Synthesis.Source
open Solcore.Synthesis.Core.Aggregates (CheckedDAG)

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
private def cases (value : Json) : IO (Array Json) := get (value.getObjValAs? (Array Json) "cases")
private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)
private def entry : Wire.Expr := .apply (.var 1) (.var 0)
private def checked (helpers : List Wire.Expr) (body : Wire.Expr := entry) : IO CheckedDAG :=
  match CheckedDAG.ofParts? helpers body with
  | some graph => pure graph
  | none => throw (IO.userError "aggregate case fixture failed checked admission")
private def imported (graph : CheckedDAG) (input : Word) : IO Json :=
  get (Aggregate.emitCase graph input (Json.mkObj [("kind", toJson "imported")]) 3000)
private def returned (value : Word) : Json := Json.mkObj [
  ("stage", toJson "execution"), ("status", toJson "returned"),
  ("word", toJson (toString value.val))]

private def templateResult (pattern : Nat) (input scalar : Word) : Word :=
  let high := input.val ≥ 2 ^ 255
  if pattern = 0 then input.add scalar
  else if pattern = 1 then if high then input.bitXor scalar else input.add scalar
  else if pattern = 2 then input.add (if high then scalar.add scalar else scalar)
  else input.add (if high then input.bitXor scalar else input.add scalar)

private def unitCase : Wire.Expr :=
  .letE (.newCell .word (.var 0))
    (.letE (.inLeft .word (.loadCell (.var 0)))
      (.letE (.caseE (.var 0)
        (.storeCell (.var 2) (.var 0)) (.storeCell (.var 2) (.var 0)))
        (.loadCell (.var 2))))

/-- Both the case payload and an unprinted Unit binding shift the helper index. -/
private def payloadCall : Wire.Expr :=
  .letE (.newCell .word (.var 0))
    (.caseE (.inRight .word (.loadCell (.var 0)))
      (.apply (.var 3) (.var 0))
      (.letE .unit (.apply (.var 4) (.binary .wordAdd (.var 1) (.loadCell (.var 2))))))

private def boolCase : Wire.Expr :=
  .ifE (.caseE (.inRight .word (.var 0))
      (.binary .wordEq (.var 0) (word 0)) (.binary .wordGt (.var 0) (word 0)))
    (.var 0) (word 1)

private def fixtures : List (List Wire.Expr) :=
  (List.range 4).map (fun pattern => [Aggregate.template pattern (word 2)]) ++
    [[unitCase], [.binary .wordAdd (.var 0) (word 1), payloadCall], [boolCase]]

private def indexChecks : IO Unit := do
  for pattern in List.range 4 do
    for scalar in [Word.zero, Word.ofNatModulo 2, Word.maximum] do
      let graph ← checked [Aggregate.template pattern (.word scalar)]
      ensure (graph.features.count "newCell" == 1) "template changed its private cell allocation"
      ensure ((Aggregate.bindingInventory graph).count .leftPayload ==
        (Aggregate.bindingInventory graph).count .rightPayload) "template omitted a case branch scope"
      for input in Input.boundaryInputs do
        ensure (Aggregate.observe graph input 3000 == returned (templateResult pattern input scalar))
          s!"aggregate index mismatch: pattern {pattern}, scalar {scalar.val}, input {input.val}"
  let snapshot ← checked [Aggregate.template 0 (word 2)]
  ensure (Aggregate.observe snapshot (Word.ofNatModulo 1) 3000 == returned (Word.ofNatModulo 3))
    "pair construction reread the overwritten left operand"
  let called ← checked [.binary .wordAdd (.var 0) (word 1), payloadCall]
  for input in Input.boundaryInputs do
    ensure (Aggregate.observe called input 3000 == returned (input.add input |>.add (Word.ofNatModulo 1)))
      "case/Unit payload context selected the wrong helper or cell"
  for helpers in fixtures do
    let graph ← checked helpers
    let mut source : Option String := none
    for input in Input.boundaryInputs do
      let saved ← imported graph input
      let current ← string saved "source"
      if let some previous := source then ensure (previous == current) "aggregate source depends on input"
      source := some current
      let admitted ← get (Aggregate.caseProgram saved)
      ensure (admitted.program.check && admitted.input == input) "aggregate case changed its original Core"
      ensure ((← get (Aggregate.replayCase saved 3000)) == saved) "imported aggregate case did not replay"
      ensure ((← get (Aggregate.replayCase (saved.setObjVal! "directCore" (returned Word.zero)) 3000)) == saved)
        "aggregate replay trusted a saved result"
      let low ← get (Aggregate.replayCase saved 0)
      ensure ((← string (← field low "directCore") "status") == "out-of-fuel")
        "zero fuel was confused with aggregate completion"

private def minimumBudget (seed : Nat) : IO Nat := do
  for nodes in List.range 513 do
    if (Aggregate.generatedFunction (Seed.ofNat seed) nodes).isOk then return nodes
  throw (IO.userError "aggregate skeleton did not fit the case node limit")

private def generationChecks : IO Json := do
  let mut saved := Json.null
  for seed in [0, 1, 2, 3, 6, 9] do
    let budget ← minimumBudget seed
    let corpus := Aggregate.generateCases (Seed.ofNat seed) budget 4 1 3000
    ensure (corpus == Aggregate.generateCases (Seed.ofNat seed) budget 4 1 3000)
      "aggregate generation is nondeterministic"
    ensure ((← string corpus "status") == "complete" && (← natural corpus "attempted") == 1)
      "minimal measured skeleton did not generate one four-input case group"
    let rows ← cases corpus
    ensure (rows.size == 4) "generated aggregate group omitted boundary inputs"
    for index in List.range 4 do
      let row := rows[index]!
      let graph ← get (Aggregate.caseProgram row)
      ensure (graph.program.check && graph.function.helpers.length == 1 + seed % 3 &&
        Wire.programNodes graph.program ≤ budget) "aggregate generation escaped helper/type/node budget"
      ensure (some graph.input == Input.boundaryInputs[index]?) "aggregate boundary input order changed"
      ensure ((← get (Aggregate.replayCase row 3000)) == row) "generated aggregate provenance did not replay"
      let low ← get (Aggregate.replayCase row 0)
      ensure ((← string (← field low "directCore") "status") == "out-of-fuel")
        "fresh replay fuel changed original validation fuel"
      saved := row
    ensure ((← cases (Aggregate.generateCases (Seed.ofNat seed) (budget - 1) 1 1 3000)).isEmpty)
      "insufficient skeleton budget silently changed the selected template"
  let corpus := Aggregate.generateCases (Seed.ofNat 0) 256 8 256 3000
  ensure ((← cases corpus).size == 8 && (← natural corpus "attempted") ≤ 256)
    "bounded mixed aggregate corpus did not complete"
  for row in ← cases corpus do
    let graph ← get (Aggregate.caseProgram row)
    ensure (Wire.programNodes graph.program ≤ 256) "closed G0 embedding exceeded the full program budget"
    ensure ((← get (Aggregate.replayCase row 3000)) == row) "mixed aggregate metadata failed replay"
  let budget ← minimumBudget 0
  let low := Aggregate.generateCases (Seed.ofNat 0) budget 1 1 0
  let excluded ← get (low.getObjValAs? (Array Json) "excluded")
  ensure ((← string excluded[0]! "category") == "inconclusive-resource") "generation fuel was a semantic exclusion"
  ensure ((← cases (Aggregate.generateCases (Seed.ofNat 0) budget 3 1 3000)).size == 3)
    "case count did not truncate a boundary group"
  ensure ((← string (Aggregate.generateCases (Seed.ofNat 0) budget 5 1 3000) "status") == "generation-exhausted")
    "aggregate attempt limit counted inputs instead of function candidates"
  ensure ((← natural (Aggregate.generateCases (Seed.ofNat 0) 256 0 100 3000) "attempted") == 0 &&
    (← cases (Aggregate.generateCases (Seed.ofNat 0) 256 1 0 3000)).isEmpty)
    "empty generation budgets consumed work"
  return saved

private def tamperingChecks (saved : Json) : IO Unit := do
  let provenance ← field saved "provenance"
  let origin ← field provenance "origin"
  let withOrigin := fun changed => saved.setObjVal! "provenance" (provenance.setObjVal! "origin" changed)
  for version in ["generatorVersion", "profileVersion", "functionVersion", "templateVersion", "emitterVersion", "wrapperVersion"] do
    rejected (Aggregate.replayCase (saved.setObjVal! "provenance"
      (provenance.setObjVal! version (toJson "forged"))) 3000) "tampered aggregate version accepted"
  for (name, value) in [("seed", toJson "02"), ("finalSeed", toJson "0"),
      ("maxProgramNodes", toJson (513 : Nat)), ("helpers", Json.arr #[]),
      ("helperCount", toJson (0 : Nat)), ("inputIndex", toJson (10 : Nat)),
      ("validationFuel", toJson (10000001 : Nat)), ("validationFuel", toJson (0 : Nat))] do
    rejected (Aggregate.replayCase (withOrigin (origin.setObjVal! name value)) 3000)
      s!"tampered aggregate {name} accepted"
  let metadata ← get (origin.getObjValAs? (Array Json) "helpers")
  for name in ["seed", "finalSeed", "maxProgramNodes", "template"] do
    let changed := metadata[0]!.setObjVal! name (toJson "forged")
    rejected (Aggregate.replayCase (withOrigin (origin.setObjVal! "helpers" (.arr (metadata.set! 0 changed)))) 3000)
      "tampered helper template metadata accepted"
  rejected (Aggregate.replayCase (saved.setObjVal! "source" (toJson "stale")) 3000) "stale aggregate source accepted"
  rejected (Aggregate.replayCase (saved.setObjVal! "input" (toJson "0")) 3000) "input/application mismatch accepted"
  let contract ← field saved "contract"
  rejected (Aggregate.replayCase (saved.setObjVal! "contract" (contract.setObjVal! "calldata" (toJson "0x"))) 3000)
    "wrong aggregate ABI input accepted"
  let bad : Wire.Expr := .letE (.newCell .word (.var 0))
    (.caseE (.inLeft .word (word 1)) (.loadCell (.var 0)) (.loadCell (.var 0)))
  rejected (Aggregate.checkedFunction (Wire.encodeProgram (functionDAGProgram [bad] entry)))
    "case payload was incorrectly treated as the outer cell"
  rejected (Aggregate.caseProgram (saved.setObjVal! "input" (toJson "01")))
    "noncanonical aggregate input accepted"

private def shrinkChecks : IO Unit := do
  for helpers in fixtures do
    let graph ← checked helpers
    let saved ← imported graph Word.maximum
    let original ← get (Aggregate.caseProgram saved)
    let shrunk ← get (Aggregate.shrinkCases saved 1000 3000)
    let rows ← cases shrunk
    ensure (!rows.isEmpty && shrunk == (← get (Aggregate.shrinkCases saved 1000 3000)))
      "aggregate shrinking was empty or nondeterministic"
    let mut seen : List String := []
    let mut inputReduced := false
    let mut storesReduced := false
    for row in rows do
      let candidate ← get (Aggregate.caseProgram row)
      ensure (candidate.program.check && candidate.function.helpers.length == graph.helpers.length &&
        Aggregate.bindingInventory candidate.function == Aggregate.bindingInventory graph &&
        candidate.function.features.count "newCell" == graph.features.count "newCell" &&
        candidate.function.features.count "case" == graph.features.count "case")
        "shrink erased/retyped a cell, aggregate, Unit or case payload binder"
      ensure ((complexity candidate.program.body).isStrictlySmaller (complexity original.program.body))
        "aggregate reduction did not strictly decrease the original Core program"
      let key := (Wire.encodeProgram candidate.program).compress
      ensure (!seen.contains key) "aggregate reduction duplicated a candidate"
      seen := key :: seen
      ensure ((← get (Aggregate.replayCase row 3000)) == row) "aggregate reduction did not replay"
      inputReduced := inputReduced || candidate.input != original.input
      storesReduced := storesReduced || candidate.function.features.count "storeCell" < graph.features.count "storeCell"
    ensure inputReduced "aggregate shrinking omitted input candidates"
    if graph.features.contains "storeCell" then
      ensure storesReduced "aggregate shrinking omitted store-to-Unit candidates"
    ensure ((← cases (← get (Aggregate.shrinkCases saved 2 3000))) == rows.extract 0 2 &&
      (← cases (← get (Aggregate.shrinkCases saved 0 3000))).isEmpty) "aggregate shrink limit changed ordering"

def testSourceAggregateCases : IO Unit := do
  indexChecks
  let saved ← generationChecks
  tamperingChecks saved
  shrinkChecks

end Tests.SourceAggregateCases
end

section
-- leanmerge: from Solcore.Test.SourceAggregateEmitter
/-! Internal aggregates preserve evaluation order and immutable snapshots while
case payloads, Unit sequencing, cells and earlier helpers share Core indices.
These tests check the original Core oracle and the emitted statement structure;
Rust/EVM differential execution exercises the actual source compiler separately. -/
set_option autoImplicit false

namespace Tests.SourceAggregateEmitter

open Solcore.Core
open Solcore.Synthesis.Core
open Solcore.Synthesis.Source
open Solcore.Synthesis.Core.Aggregates (CheckedDAG)

private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)
def entry : Wire.Expr := .apply (.var 1) (.var 0)

/-- The left field snapshots the input, the right field writes two, and a later
write of nine must not alter either field. Input one therefore returns three. -/
def pairSnapshotBody : Wire.Expr :=
  .letE (.newCell .word (.var 0))
    (.letE (.pair (.loadCell (.var 0))
      (.letE (.storeCell (.var 0) (word 2)) (.loadCell (.var 1))))
      (.letE (.storeCell (.var 1) (word 9))
        (.binary .wordAdd (.first (.var 1)) (.second (.var 1)))))

/-- Each field increments the cell. Projection must evaluate this pair once. -/
def projectionOnceBody : Wire.Expr :=
  .letE (.newCell .word (.var 0))
    (.letE (.first (.pair
      (.letE (.storeCell (.var 0) (.binary .wordAdd (.loadCell (.var 0)) (word 1)))
        (.loadCell (.var 1)))
      (.letE (.storeCell (.var 0) (.binary .wordAdd (.loadCell (.var 0)) (word 1)))
        (.loadCell (.var 1)))))
      (.binary .wordAdd (.var 0) (.loadCell (.var 1))))

def sumSnapshotBody : Wire.Expr :=
  .letE (.newCell .word (.var 0))
    (.letE (.ifE (.binary .wordGt (.var 1) (word 0))
      (.inRight .word (.loadCell (.var 0))) (.inLeft .word (.loadCell (.var 0))))
      (.letE (.storeCell (.var 1) (word 9))
        (.caseE (.var 1)
          (.binary .wordAdd (.var 0) (.loadCell (.var 3)))
          (.binary .wordAdd (.binary .wordAdd (.var 0) (word 1))
            (.loadCell (.var 3))))))

/-- The payload shifts both a caller cell and an earlier helper. The helper
allocates its own cell, so its write cannot replace the caller's saved value. -/
def payloadCallBody : Wire.Expr :=
  .letE (.newCell .word (.var 0))
    (.caseE (.ifE (.binary .wordGt (.var 1) (word 0))
      (.inLeft .word (.var 1)) (.inRight .word (.var 1)))
      (.letE (.binary .wordAdd (.var 0) (word 1))
        (.letE (.storeCell (.var 2) (.var 0))
          (.letE (.apply (.var 5) (.var 1))
            (.binary .wordAdd (.var 0) (.loadCell (.var 4))))))
      (.letE (.storeCell (.var 1) (word 5))
        (.apply (.var 4) (.loadCell (.var 2)))))

/-- Both cases return aggregates, and their payload binder shifts the saved pair. -/
def aggregateCaseBody : Wire.Expr :=
  .letE (.caseE (.ifE (.binary .wordGt (.var 0) (word 0))
    (.inRight .word (.var 0)) (.inLeft .word (.var 0)))
    (.pair (.var 0) (word 10))
    (.pair (.binary .wordAdd (.var 0) (word 1)) (word 20)))
    (.letE (.caseE (.inLeft .word (.first (.var 0)))
      (.inRight .word (.binary .wordAdd (.var 0) (.second (.var 1))))
      (.inLeft .word (.var 0)))
      (.caseE (.var 0)
        (.binary .wordAdd (.var 0) (.first (.var 2)))
        (.binary .wordAdd (.var 0) (.first (.var 2)))))

/-- Unit-valued case branches update only the selected branch's caller cell. -/
def unitCaseBody : Wire.Expr :=
  .letE (.newCell .word (.var 0))
    (.letE (.caseE (.ifE (.binary .wordGt (.var 1) (word 0))
      (.inLeft .word (.var 1)) (.inRight .word (.var 1)))
      (.letE (.var 0) (.storeCell (.var 2) (.binary .wordAdd (.var 0) (word 1))))
      (.storeCell (.var 1) (word 7)))
      (.loadCell (.var 1)))

private def joinValue (target : Aggregates.Target) (left : Bool) : Wire.Expr :=
  match target with
  | .word => word (if left then 11 else 13)
  | .bool => .bool left
  | .unit => .letE (word (if left then 11 else 13)) .unit
  | .wordPair => .pair (word (if left then 11 else 13)) (word 1)
  | .wordSum => if left then .inLeft .word (word 11) else .inRight .word (word 13)

private def consume (target : Aggregates.Target) (expression : Wire.Expr) : Wire.Expr :=
  .letE expression (match target with
    | .word => .var 0
    | .bool => .ifE (.var 0) (word 11) (word 13)
    | .unit => word 17
    | .wordPair => .first (.var 0)
    | .wordSum => .caseE (.var 0) (.var 0) (.var 0))

def joinBody (target : Aggregates.Target) (useCase : Bool) : Wire.Expr :=
  let tested := Wire.Expr.binary .wordGt (.var 0) (word 0)
  consume target (if useCase then
    .caseE (.ifE tested (.inLeft .word (.var 0)) (.inRight .word (.var 0)))
      (joinValue target true) (joinValue target false)
    else .ifE tested (joinValue target true) (joinValue target false))

def fixtures : List (String × List Wire.Expr × Wire.Expr) := [
  ("pair-snapshot", [pairSnapshotBody], entry),
  ("projection-once", [projectionOnceBody], entry),
  ("sum-snapshot", [sumSnapshotBody], entry),
  ("payload-helper-isolation", [pairSnapshotBody, payloadCallBody], entry),
  ("aggregate-case-joins", [aggregateCaseBody], entry),
  ("unit-case-effects", [unitCaseBody], entry)]

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def checked (helpers : List Wire.Expr) (body : Wire.Expr := entry) : IO CheckedDAG :=
  match CheckedDAG.ofParts? helpers body with
  | some graph => pure graph
  | none => throw (IO.userError "aggregate fixture failed checked profile admission")

private def emitted (graph : CheckedDAG) : IO EmittedProgram :=
  match Aggregate.emit graph with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"aggregate emission failed: {reprStr error}")

private def observe (graph : CheckedDAG) (input expected : Nat) : IO Unit := do
  let applied := graph.instantiate (Word.ofNatModulo input)
  ensure applied.check "applied aggregate graph failed Core typing"
  match applied.toCore.runStateful 5000 with
  | .done (.word value) _ =>
      ensure (value.val == expected) s!"independent Core aggregate result changed: input {input}, expected {expected}, got {value.val}"
  | _ => throw (IO.userError "independent Core aggregate graph did not return a Word")

private def admissionChecks : IO Unit := do
  for (label, helpers, body) in fixtures do
    let graph ← checked helpers body
    ensure graph.program.check s!"aggregate graph escaped full Core checking: {label}"
    let some restored := CheckedDAG.ofProgram? graph.program |
      throw (IO.userError s!"aggregate graph failed canonical readmission: {label}")
    ensure (Wire.encodeProgram restored.program == Wire.encodeProgram graph.program)
      "aggregate graph readmission changed its original Core"
    let source ← emitted graph
    ensure (source == (← emitted graph)) "aggregate emission is not deterministic"
    ensure (source.contractName == "SynthesizedAggregates" && source.methodSignature == "run(uint256)" &&
      source.deployPath == ["SynthesizedAggregatesDeploy"] &&
      source.runtimePath == ["SynthesizedAggregatesDeploy", "SynthesizedAggregates"])
      "aggregate wrapper metadata changed"
  let nestedPair := Wire.Expr.letE (.pair (.pair (word 1) (word 2)) (word 3)) (word 0)
  let aggregateCell := Wire.Expr.letE (.newCell (.product .word .word)
    (.pair (word 1) (word 2))) (word 0)
  ensure ((functionDAGProgram [nestedPair] entry).check &&
    (functionDAGProgram [aggregateCell] entry).check)
    "aggregate rejection stopped exercising otherwise well-typed Core graphs"
  for body in [nestedPair, aggregateCell,
      .letE (.inLeft .bool (word 1)) (word 0),
      .letE (.inRight .word (.pair (word 1) (word 2))) (word 0),
      .letE (.newCell .word (.var 0)) (.letE (.var 0) (word 0)),
      .letE (.newCell .word (.var 0)) (.pair (.var 0) (word 1)),
      .letE (.newCell .word (.var 0)) (.caseE (.inLeft .word (word 1)) (.var 1) (.var 1)),
      .caseE (.inLeft .word (word 1)) (.var 0) (.bool true),
      .letE (.newCell .word (.var 0))
        (.caseE (.inLeft .word (word 1)) (.loadCell (.var 0)) (.loadCell (.var 1))),
      .apply (.var 1) (.var 0),
      .letE (.lambda .word .word (.var 0)) (.apply (.var 0) (word 1))] do
    ensure (CheckedDAG.ofParts? [body] entry).isNone
      "aggregate profile admitted a nested type, alias, escape, wrong payload scope or indirect call"
  ensure (CheckedDAG.ofParts? [] (.var 0)).isNone "empty aggregate helper graph was admitted"
  ensure (CheckedDAG.ofParts? (List.replicate 4 pairSnapshotBody) entry).isNone
    "aggregate helper count exceeded its bound"
  ensure (Aggregates.infer? [.word, .unit, .wordPair, .wordSum, .cellWord, .word] 1
      (.binary .wordAdd (.first (.var 2)) (.loadCell (.var 4))) == some .word)
    "mixed payload/Unit/aggregate/cell context changed its indices"

private def executionChecks : IO Unit := do
  let pair ← checked [pairSnapshotBody]
  let projection ← checked [projectionOnceBody]
  let sum ← checked [sumSnapshotBody]
  let isolated ← checked [pairSnapshotBody, payloadCallBody]
  let aggregates ← checked [aggregateCaseBody]
  let unit ← checked [unitCaseBody]
  for input in [0, 1, Word.maximum.val, 2 ^ 255] do
    observe pair input (Word.ofNatModulo (input + 2)).val
    observe projection input (Word.ofNatModulo (2 * input + 3)).val
    observe sum input (Word.ofNatModulo (input + if input == 0 then 9 else 10)).val
    observe isolated input (if input == 0 then 7 else (Word.ofNatModulo (2 * input + 4)).val)
    observe aggregates input (if input == 0 then 10 else (Word.ofNatModulo (2 * input + 22)).val)
    observe unit input (if input == 0 then 7 else (Word.ofNatModulo (input + 1)).val)
  observe pair 1 3
  for target in [Aggregates.Target.word, .bool, .unit, .wordPair, .wordSum] do
    for useCase in [false, true] do
      let graph ← checked [joinBody target useCase]
      let _ ← emitted graph
      for input in [0, 1, Word.maximum.val, 2 ^ 255] do
        observe graph input (if target == .unit then 17 else if input == 0 then 13 else 11)
  match (pair.instantiate Word.zero).toCore.runStateful 0 with
  | .outOfFuel _ => pure ()
  | _ => throw (IO.userError "zero fuel was treated as a completed aggregate computation")
  -- Raw primitives render through the call-graph helpers with the alias import.
  let divided := Wire.Expr.caseE (.inLeft .word (.var 0))
    (.binary .wordDiv (.var 0) (word 1)) (.var 0)
  match Aggregate.emit (← checked [divided]) with
  | .ok emitted => unless (emitted.source.splitOn "import { div as sc_div, mod as sc_mod, ").length == 2 && (emitted.source.splitOn " = sc_div(sc_v").length == 2 do
      throw (IO.userError "aggregate emission lost the raw division alias")
  | .error error => throw (IO.userError s!"aggregate raw division was rejected: {reprStr error}")

private def contains (source fragment : String) : Bool := (source.splitOn fragment).length > 1

private def pairSnapshotExpected : String := String.intercalate "\n" [
  "function sc_fn0(sc_arg: word) returns (word) {",
  "    let sc_c0: word = sc_arg;",
  "    let sc_v1: word = sc_c0;",
  "    let sc_v2: word = 2;",
  "    sc_c0 = sc_v2;",
  "    let sc_v3: word = sc_c0;",
  "    let sc_v4: (word, word) = (sc_v1, sc_v3);",
  "    let sc_v5: (word, word) = sc_v4;",
  "    let sc_v6: word = 9;",
  "    sc_c0 = sc_v6;",
  "    let sc_v7: word = 0;",
  "    match (sc_v5) {",
  "        case (sc_p8, sc_p9) {",
  "            sc_v7 = sc_p8;",
  "        }", "    }",
  "    let sc_v10: word = 0;",
  "    match (sc_v5) {",
  "        case (sc_p11, sc_p12) {",
  "            sc_v10 = sc_p12;",
  "        }", "    }",
  "    let sc_v13: word = (sc_v7 + sc_v10);",
  "    return sc_v13;", "}"]

private def formattingChecks : IO Unit := do
  ensure (contains (← emitted (← checked [pairSnapshotBody])).source pairSnapshotExpected)
    "aggregate snapshot or tuple projection rendering changed"
  let projection ← emitted (← checked [projectionOnceBody])
  ensure ((projection.source.splitOn "sc_c0 =").length == 3)
    "projection evaluated an effectful operand more than once"
  for target in [Aggregates.Target.word, .bool, .unit, .wordPair, .wordSum] do
    for useCase in [false, true] do
      let output ← emitted (← checked [joinBody target useCase])
      ensure (!contains output.source ": unit") "Unit join introduced a fake value binding"
      if useCase then
        ensure (contains output.source "case inl(sc_p" && contains output.source "case inr(sc_p")
          "sum match omitted a fresh payload branch"
      match target with
      | .bool => ensure (contains output.source ": bool = false;") "Bool join omitted its typed default"
      | .wordPair =>
        ensure (contains output.source ": (word, word) = (0, 0);")
          "pair join omitted its typed default"
      | .wordSum =>
        ensure (contains output.source ": sum<word, word> = inl(0);")
          "sum join omitted its typed default"
      | _ => pure ()
  let graph ← checked [aggregateCaseBody]
  for feature in ["pair", "first", "second", "inLeft", "inRight", "case", "functionCall"] do
    ensure (graph.features.contains feature) s!"missing aggregate AST feature {feature}"
  ensure (Aggregate.emitterVersion == "solcore-source-aggregates-v2" &&
    Aggregate.wrapperVersion == "solcore-word-aggregates-contract-v1" &&
    Aggregate.selector == "0xa444f5e9" && Aggregates.version == "core-aggregate-dag-v1")
    "aggregate provenance changed"

def testSourceAggregateEmitter : IO Unit := do
  admissionChecks
  executionChecks
  formattingChecks

end Tests.SourceAggregateEmitter
end

section
-- leanmerge: from Solcore.Test.SourceAggregatePrimitives
/-! The aggregate renderer prints the raw primitive aliases with the call-graph
helpers: operand snapshots in Core order, reversed shift arguments, Boolean
conversion of signed comparison, and the original scalar spelling for the
original operations. Expected lines are hand-written goldens. -/
set_option autoImplicit false

namespace Tests.SourceAggregatePrimitives

open Solcore.Core (Word)
open Solcore.Core.Wire Solcore.Synthesis.Source

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def word (value : Nat) : Expr := .word (Word.ofNatModulo value)
private def arg : Expr := .var 0

private def render (body : Expr) (target : Solcore.Synthesis.Core.Aggregates.Target := .word) :
    Except EmitError AggregateRenderer.Rendered :=
  AggregateRenderer.render [] target [.word "sc_arg"] 4 0 body

private def golden (name : String) (body : Expr) (lines : List String) (value : String) : IO Unit :=
  match render body with
  | .ok rendered =>
      ensure (rendered.lines == lines.map ("    " ++ ·) && rendered.value == some value)
        s!"{name} rendering changed: {rendered.lines}"
  | .error error => throw (IO.userError s!"{name} was rejected: {reprStr error}")

private def goldenChecks : IO Unit := do
  golden "addmod" (.ternary .wordAddMod arg (word 3) (word 7))
    ["let sc_v0: word = sc_arg;", "let sc_v1: word = 3;", "let sc_v2: word = sc_v1;",
      "let sc_v3: word = 7;", "let sc_v4: word = sc_v3;",
      "let sc_v5: word = sc_addmod(sc_v0, sc_v2, sc_v4);"] "sc_v5"
  -- Core wordShl(value, shift) prints shl(shift, value) from the snapshots.
  golden "shl" (.binary .wordShl arg (word 8))
    ["let sc_v0: word = sc_arg;", "let sc_v1: word = 8;", "let sc_v2: word = sc_v1;",
      "let sc_v3: word = sc_shl(sc_v2, sc_v0);"] "sc_v3"
  golden "sgt" (.ifE (.binary .wordSgt arg (word 1)) (word 2) (word 3))
    ["let sc_v0: word = sc_arg;", "let sc_v1: word = 1;", "let sc_v2: word = sc_v1;",
      "let sc_v3: bool = tobool(sc_sgt(sc_v0, sc_v2));", "let sc_v4: word = 0;", "if (sc_v3) {",
      "    let sc_v5: word = 2;", "    sc_v4 = sc_v5;", "} else {",
      "    let sc_v6: word = 3;", "    sc_v4 = sc_v6;", "}"] "sc_v4"
  -- A cell load is bound before Clz snapshots it; the cell itself is never passed.
  golden "clz" (.letE (.newCell .word arg) (.unary .wordClz (.loadCell (.var 0))))
    ["let sc_c0: word = sc_arg;", "let sc_v1: word = sc_c0;", "let sc_v2: word = sc_v1;",
      "let sc_v3: word = sc_clz(sc_v2);"] "sc_v3"
  -- Original operations keep their exact unsnapshotted scalar spelling.
  golden "add" (.binary .wordAdd arg (word 1))
    ["let sc_v0: word = 1;", "let sc_v1: word = (sc_arg + sc_v0);"] "sc_v1"
  golden "not" (.unary .wordNot arg) ["let sc_v0: word = (~sc_arg);"] "sc_v0"
  match render (.ternary .wordMulMod arg arg arg) .bool with
  | .error (.unsupportedExpression _) => pure ()
  | _ => throw (IO.userError "a ternary primitive was rendered at a non-Word type")
  match render (.unary .integerToWord (.integer 1)) with
  | .error (.unsupportedUnary .integerToWord) => pure ()
  | _ => throw (IO.userError "integer conversion was rendered by the aggregate renderer")

private def primitiveBodies : List Expr :=
  [.unary .wordClz arg, .ternary .wordAddMod arg (word 3) arg, .ternary .wordMulMod (word 5) arg (word 0)] ++
  ([BinaryOp.wordDiv, .wordMod, .wordShl, .wordShr, .wordSar, .wordSdiv, .wordSmod, .wordByte, .wordPow,
    .wordSignExtend].map fun operation => .binary operation arg (word 255)) ++
  [.ifE (.binary .wordSgt arg (word 1)) (.binary .wordDiv arg arg) (word 0)]

/-- On scalar bodies without Boolean lets, the aggregate renderer and the
call-graph renderer print the same text: the helpers are shared exactly. -/
private def sharedHelperChecks : IO Unit := do
  let scalarBodies := primitiveBodies ++ [.binary .wordXor (.binary .wordAdd arg (word 1)) arg,
    .letE (.ternary .wordAddMod arg arg (word 9)) (.binary .wordShr (.var 0) (.unary .wordClz (.var 1))),
    .ifE (.binary .wordGt arg (word 7)) (.unary .wordNot arg) (.binary .wordMul arg arg)]
  for body in scalarBodies do
    match render body, CallGraphRenderer.renderWithFunctions [] .word ["sc_arg"] 4 0 body with
    | .ok aggregate, .ok callGraph =>
        ensure (aggregate.lines == callGraph.lines && aggregate.value == some callGraph.value &&
          aggregate.nextId == callGraph.nextId) s!"aggregate and call-graph text differ: {aggregate.lines}"
    | _, _ => throw (IO.userError "a shared scalar body was rejected")

private def importChecks : IO Unit := do
  ensure ("import { " ++ ", ".intercalate AggregateRenderer.opcodeAliases ++ " } from std.opcodes;" ==
    Primitive.opcodeImport) "aggregate aliases differ from the primitive profile's import"
  for body in primitiveBodies do
    ensure (AggregateRenderer.usesOpcodeAliases body) "a primitive body was not detected"
    ensure (AggregateRenderer.opcodeImports [word 0, body] == [Primitive.opcodeImport])
      "a primitive body did not import the aliases"
    -- Detection reaches operands under aggregates, cases, cells and lets.
    for nested in [Expr.pair body arg, .caseE (.inLeft .word arg) body arg, .first (.pair body arg),
        .letE (.newCell .word arg) (.storeCell (.var 0) body), .letE body arg] do
      ensure (AggregateRenderer.usesOpcodeAliases nested) "a nested primitive was not detected"
  let original := [Expr.binary .wordAdd arg (word 1), .unary .boolNot (.bool true), .unary .wordNot arg,
    .ifE (.binary .wordGt arg (word 1)) (.binary .wordSub arg arg) (.binary .wordMul arg arg)]
  ensure (original.all (! AggregateRenderer.usesOpcodeAliases ·) && AggregateRenderer.opcodeImports original == [])
    "an original-operation body imported the aliases"
  ensure (AggregateRenderer.opcodeImportWith ["sload", "sstore"] original == "import {sload, sstore} from std.opcodes;")
    "a primitive-free stateful import changed"
  ensure (AggregateRenderer.opcodeImportWith ["sload", "sstore"] (original ++ [.unary .wordClz arg]) ==
      "import {sload, sstore, " ++ ", ".intercalate AggregateRenderer.opcodeAliases ++ "} from std.opcodes;")
    "the aliases were not merged into the stateful opcode import"

def testSourceAggregatePrimitives : IO Unit := do
  goldenChecks
  sharedHelperChecks
  importChecks

end Tests.SourceAggregatePrimitives
end

section
-- leanmerge: from Solcore.Test.SourceClosureCases
/-! Closure-case regressions check snapshot timing, independent captures,
arbitrary step entry, canonical references and sealed scope-preserving reductions. -/
set_option autoImplicit false

namespace Tests.SourceClosureCases
open Lean Solcore.Core Solcore.Synthesis.Core Solcore.Synthesis.Source
open Solcore.Synthesis.Core.Closure (CheckedPlan Variant)

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
private def cases (value : Json) : IO (Array Json) := get (value.getObjValAs? (Array Json) "cases")
private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)
private def entry : Wire.Expr := .apply (.var 1) (.var 0)
private def checked (helpers : List Wire.Expr) (body : Wire.Expr := entry) : IO Aggregates.CheckedDAG :=
  match Aggregates.CheckedDAG.ofParts? helpers body with
  | some graph => pure graph
  | none => throw (IO.userError "closure step fixture failed checked admission")
private def plan (step : Aggregates.CheckedDAG) (variant : Variant) : IO CheckedPlan :=
  match CheckedPlan.ofParts? step variant with
  | some value => pure value
  | none => throw (IO.userError "closure plan fixture failed checked admission")
private def imported (value : CheckedPlan) (input : Word) : IO Json :=
  get (Closure.emitCase value input (Json.mkObj [("kind", toJson "imported")]) 10000)
private def returned (value : Word) : Json := Json.mkObj [
  ("stage", toJson "execution"), ("status", toJson "returned"),
  ("word", toJson (toString value.val))]

/-- One private step cell is followed by the wrapper's mutable capture cell.
The entry differs from the last helper and must not be discarded by the wrapper. -/
private def privateStep : Wire.Expr :=
  .letE (.newCell .word (.var 0))
    (.letE (.storeCell (.var 0) (.binary .wordAdd (.loadCell (.var 0)) (word 2)))
      (.loadCell (.var 1)))

private def expected (variant : Variant) (input : Word) : Word :=
  (input.mul (Word.ofNatModulo 9)).add
    (Word.ofNatModulo (if variant == .snapshot then 9 else 10))

private def referenceChecks : IO Unit := do
  let graph ← checked [privateStep] (.binary .wordSub entry (word 1))
  for variant in [Variant.snapshot, .independent] do
    let value ← plan graph variant
    ensure (Wire.programNodes (value.instantiate Word.zero) ==
      Wire.programNodes graph.program + Solcore.Synthesis.Core.Closure.appliedOverhead variant)
      "measured closure overhead differs from the complete original reference"
    let mut source : Option String := none
    for input in Closure.boundaryInputs do
      ensure (Closure.observe value input 10000 == returned (expected variant input))
        s!"closure snapshot/entry mismatch: {variant.name}, input {input.val}"
      match (value.instantiate input).toCore.runStateful 10000 with
      | .done (.word _) store =>
          ensure (store.length == 2) "closure wrapper changed its private cell inventory"
          ensure (store == [.word (input.add (Word.ofNatModulo 2)),
            .word (input.add (Word.ofNatModulo 4))]) "capture cell was not updated independently of the private step cell"
      | _ => throw (IO.userError "checked closure reference did not return")
      let saved ← imported value input
      let current ← string saved "source"
      if let some previous := source then ensure (current == previous) "closure source depends on runtime input"
      source := some current
      let admitted ← get (Closure.caseProgram saved)
      ensure (admitted.program.check && admitted.input == input && admitted.plan.variant == variant)
        "closure case lost its checked canonical reference"
      ensure ((← get (Closure.replayCase saved 10000)) == saved) "imported closure case did not replay"
      ensure ((← get (Closure.replayCase (saved.setObjVal! "directCore" (returned Word.zero)) 10000)) == saved)
        "closure replay trusted its stored expected result"
      let low ← get (Closure.replayCase saved 0)
      ensure ((← string (← field low "directCore") "status") == "out-of-fuel")
        "closure fuel exhaustion was treated as completion"
  let constant ← checked [word 4]
  for variant in [Variant.snapshot, .independent] do
    let constantPlan ← plan constant variant
    ensure (!(Closure.inputSensitive constantPlan 10000).isOk)
      "generated closure plan lost the step's input-sensitive requirement"
    ensure ((Closure.emitCase constantPlan Word.zero (Json.mkObj [("kind", toJson "imported")]) 10000).isOk)
      "imported constant step should remain supported"

private def minimumBudget (seed : Nat) : IO Nat := do
  for nodes in List.range 513 do
    if (Closure.generatedPlan (Seed.ofNat seed) nodes).isOk then return nodes
  throw (IO.userError "closure skeleton did not fit the case node limit")

private def generationChecks : IO Json := do
  -- All joint helper/template/variant residues have a bounded, fully checked skeleton.
  for seed in List.range 36 do
    let budget ← minimumBudget seed
    ensure (budget ≤ 384) "default closure budget cannot hold a selected template skeleton"
    let (value, _) ← get (Closure.generatedPlan (Seed.ofNat seed) budget)
    ensure (Wire.programNodes (value.instantiate Word.zero) ≤ budget &&
      value.variant == Closure.variantFor (Seed.ofNat seed) && value.step.helpers.length == 1 + seed % 3)
      "closure generation escaped its full node, variant or helper constraints"
    ensure (!(Closure.generatedPlan (Seed.ofNat seed) (budget - 1)).isOk &&
      !(Closure.generatedPlan (Seed.ofNat seed) 513).isOk) "closure node bounds were not enforced"
  let corpus := Closure.generateCases (Seed.ofNat 0) 384 8 512 10000
  ensure (corpus == Closure.generateCases (Seed.ofNat 0) 384 8 512 10000)
    "closure generation is nondeterministic"
  let rows ← cases corpus
  ensure (rows.size == 8 && (← natural corpus "attempted") ≤ 512)
    "bounded closure generation did not complete"
  for (row, index) in rows.toList.zipIdx do
    let admitted ← get (Closure.caseProgram row)
    ensure (Wire.programNodes admitted.program ≤ 384 &&
      some admitted.input == Closure.boundaryInputs[index % 4]?) "closure generation changed boundary order/budget"
    ensure ((← get (Closure.replayCase row 10000)) == row) "generated closure provenance did not replay"
    let low ← get (Closure.replayCase row 0)
    ensure ((← string (← field low "directCore") "status") == "out-of-fuel")
      "fresh closure observation fuel changed saved validation fuel"
  let saved := rows[3]!
  let origin ← field (← field saved "provenance") "origin"
  let seedText ← string origin "seed"
  let some seed := seedText.toNat? | throw (IO.userError "invalid generated seed")
  let low := Closure.generateCases (Seed.ofNat seed) 384 1 1 0
  let excluded ← get (low.getObjValAs? (Array Json) "excluded")
  ensure ((← string excluded[0]! "category") == "inconclusive-resource")
    "closure generation fuel exhaustion was classified as a semantic exclusion"
  ensure ((← cases (Closure.generateCases (Seed.ofNat seed) 384 3 1 10000)).size == 3 &&
    (← string (Closure.generateCases (Seed.ofNat seed) 384 5 1 10000) "status") == "generation-exhausted")
    "closure count/attempt limits did not distinguish cases from function candidates"
  ensure ((← natural (Closure.generateCases (Seed.ofNat seed) 384 0 100 10000) "attempted") == 0 &&
    (← cases (Closure.generateCases (Seed.ofNat seed) 384 1 0 10000)).isEmpty)
    "empty closure generation budgets consumed work"
  return saved

private def tamperingChecks (saved : Json) : IO Unit := do
  let provenance ← field saved "provenance"
  let origin ← field provenance "origin"
  let withOrigin := fun changed => saved.setObjVal! "provenance" (provenance.setObjVal! "origin" changed)
  for name in ["generatorVersion", "profileVersion", "functionVersion", "templateVersion",
      "stepProfileVersion", "stepFunctionVersion", "stepTemplateVersion", "emitterVersion", "wrapperVersion"] do
    rejected (Closure.replayCase (saved.setObjVal! "provenance"
      (provenance.setObjVal! name (toJson "forged"))) 10000) "tampered closure version accepted"
  for (name, value) in [("seed", toJson "00"), ("finalSeed", toJson "forged"),
      ("maxProgramNodes", toJson (513 : Nat)), ("variant", toJson "forged"),
      ("stepOrigin", Json.null), ("inputIndex", toJson (4 : Nat)),
      ("validationFuel", toJson (10000001 : Nat)), ("validationFuel", toJson (0 : Nat))] do
    rejected (Closure.replayCase (withOrigin (origin.setObjVal! name value)) 10000)
      s!"tampered closure {name} accepted"
  let stepOrigin ← field origin "stepOrigin"
  for name in ["seed", "finalSeed", "maxProgramNodes", "helpers", "helperCount"] do
    rejected (Closure.replayCase (withOrigin (origin.setObjVal! "stepOrigin"
      (stepOrigin.setObjVal! name Json.null))) 10000) "tampered nested step recipe accepted"
  let admitted ← get (Closure.caseProgram saved)
  let wrongProgram := Wire.encodeProgram (admitted.plan.step.instantiate admitted.input)
  for kind in ["imported", "reduced", "closure-generated"] do
    let changed := (withOrigin (origin.setObjVal! "kind" (toJson kind))).setObjVal! "program" wrongProgram
    rejected (Closure.caseProgram changed) "noncanonical program accepted under a different origin"
    rejected (Closure.replayCase changed 10000) "replay skipped canonical comparison for an origin"
  let closurePlan ← field saved "closurePlan"
  for (name, value) in [("variant", toJson "unknown"), ("schema", toJson "unknown"),
      ("unexpected", toJson true)] do
    rejected (Closure.checkedPlan (closurePlan.setObjVal! name value)) "malformed closure plan accepted"
  rejected (Closure.caseProgram (saved.setObjVal! "input" (toJson "01"))) "noncanonical closure input accepted"
  rejected (Closure.caseProgram (saved.setObjVal! "input" (toJson "0"))) "input/reference mismatch accepted"
  rejected (Closure.replayCase (saved.setObjVal! "source" (toJson "stale")) 10000) "stale closure source accepted"
  let contract ← field saved "contract"
  rejected (Closure.replayCase (saved.setObjVal! "contract" (contract.setObjVal! "calldata" (toJson "0x"))) 10000)
    "wrong closure ABI input accepted"

private def shrinkChecks : IO Unit := do
  let graph ← checked [Aggregate.template 3 (word 2)]
  let value ← plan graph .independent
  let saved ← imported value Word.maximum
  let original ← get (Closure.caseProgram saved)
  let shrunk ← get (Closure.shrinkCases saved 1000 10000)
  let rows ← cases shrunk
  ensure (!rows.isEmpty && shrunk == (← get (Closure.shrinkCases saved 1000 10000)))
    "closure shrinking was empty or nondeterministic"
  let mut seen : List String := []
  let mut inputReduced := false
  let mut stepReduced := false
  for row in rows do
    let candidate ← get (Closure.caseProgram row)
    ensure (candidate.program.check && candidate.plan.step.helpers.length == graph.helpers.length &&
      Aggregate.bindingInventory candidate.plan.step == Aggregate.bindingInventory graph &&
      candidate.plan.variant == value.variant)
      "closure reduction lost a step binder/helper or changed its closure variant"
    ensure ((complexity candidate.program.body).isStrictlySmaller (complexity original.program.body))
      "closure reduction did not decrease the full original Core program"
    let key := (Wire.encodeProgram candidate.program).compress
    ensure (!seen.contains key) "closure reduction duplicated a canonical program"
    seen := key :: seen
    ensure ((← get (Closure.replayCase row 10000)) == row) "closure reduction did not replay"
    inputReduced := inputReduced || candidate.input != original.input
    stepReduced := stepReduced || Wire.encodeProgram candidate.plan.step.program != Wire.encodeProgram graph.program
  ensure (inputReduced && stepReduced) "closure reduction omitted input or step candidates"
  ensure ((← cases (← get (Closure.shrinkCases saved 2 10000))) == rows.extract 0 2 &&
    (← cases (← get (Closure.shrinkCases saved 0 10000))).isEmpty) "closure shrink limit changed ordering"
  let reduced := rows[0]!
  let candidate ← get (Closure.caseProgram reduced)
  let provenance ← field reduced "provenance"
  let origin ← field provenance "origin"
  for (name, value) in [("parentProgram", Wire.encodeProgram candidate.program),
      ("parentInput", toJson "00"), ("extra", toJson true)] do
    rejected (Closure.replayCase (reduced.setObjVal! "provenance"
      (provenance.setObjVal! "origin" (origin.setObjVal! name value))) 10000)
      "tampered reduction witness accepted"
  let sameParent := Json.mkObj [("kind", toJson "reduced"),
    ("parentProgram", Wire.encodeProgram candidate.program), ("parentPlan", Closure.planJson candidate.plan),
    ("parentInput", toJson (toString candidate.input.val))]
  rejected (Closure.replayCase (reduced.setObjVal! "provenance"
    (provenance.setObjVal! "origin" sameParent)) 10000) "non-strict reduction origin accepted"


def testSourceClosureCases : IO Unit := do
  referenceChecks
  let saved ← generationChecks
  tamperingChecks saved
  shrinkChecks

end Tests.SourceClosureCases
end

section
-- leanmerge: from Solcore.Test.SourceClosureEmitter
/-! Closure snapshots remain independent of a later outer assignment. Weighted
results distinguish the first and second capture, while actual heap observations
check one step execution and a separate mutable capture cell. -/
set_option autoImplicit false

namespace Tests.SourceClosureEmitter

open Solcore.Core Solcore.Synthesis.Core
open Solcore.Synthesis.Core.Closure (CheckedPlan Variant)
open Solcore.Synthesis.Source (EmittedProgram)

private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)
private def entry : Wire.Expr := .apply (.var 1) (.var 0)
private def identityWithCell : Wire.Expr :=
  .letE (.newCell .word (.var 0)) (.loadCell (.var 0))
private def privateStep : Wire.Expr :=
  .letE (.newCell .word (word 0))
    (.letE (.storeCell (.var 0) (word 2))
      (.binary .wordAdd (.var 2) (.loadCell (.var 1))))
private def arbitraryEntry : Wire.Expr := .binary .wordSub entry (word 1)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def step (helpers : List Wire.Expr) (body : Wire.Expr := entry) : IO Aggregates.CheckedDAG :=
  match Aggregates.CheckedDAG.ofParts? helpers body with
  | some graph => pure graph
  | none => throw (IO.userError "closure step did not pass the aggregate checker")

private def checked (graph : Aggregates.CheckedDAG) (variant : Variant) : IO CheckedPlan :=
  match CheckedPlan.ofParts? graph variant with
  | some plan => pure plan
  | none => throw (IO.userError "closure wrapper failed full Core admission")

private def emitted (plan : CheckedPlan) : IO EmittedProgram :=
  match Solcore.Synthesis.Source.Closure.emit plan with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"closure source emission failed: {reprStr error}")

private def inputs : List Nat := [0, 1, Word.maximum.val, 2 ^ 255]

private def identityExpected : Variant → List Nat
  | .snapshot => [4, 13, Word.maximum.val - 4, 2 ^ 255 + 4]
  | .independent => [5, 14, Word.maximum.val - 3, 2 ^ 255 + 5]

private def incrementExpected : Variant → List Nat
  | .snapshot => [9, 18, 0, 2 ^ 255 + 9]
  | .independent => [10, 19, 1, 2 ^ 255 + 10]

private def constantExpected : Variant → List Nat
  | .snapshot => [214, 218, 210, 214]
  | .independent => [215, 219, 211, 215]

private def observe (plan : CheckedPlan) (input expected : Nat) (cells : List Word) : IO Unit := do
  let applied := plan.instantiate (Word.ofNatModulo input)
  ensure applied.check "applied closure plan failed full Core checking"
  match applied.toCore.runStateful 10000 with
  | .done (.word value) store =>
      ensure (value.val == expected)
        s!"closure result changed: {plan.variant.name}, input {input}, expected {expected}, got {value.val}"
      ensure (store == cells.map Value.word)
        "closure wrapper repeated its step or aliased its mutable capture with a private step cell"
  | _ => throw (IO.userError "closure Core application did not return a Word")

private def executionChecks : IO Unit := do
  let identity ← step [identityWithCell]
  let arbitrary ← step [privateStep] arbitraryEntry
  let skippedHelper ← step [privateStep] (.var 0)
  let constant ← step [word 42]
  for variant in Variant.all do
    let identityPlan ← checked identity variant
    let arbitraryPlan ← checked arbitrary variant
    let skippedPlan ← checked skippedHelper variant
    let constantPlan ← checked constant variant
    for (input, expected) in inputs.zip (identityExpected variant) do
      observe identityPlan input expected
        [Word.ofNatModulo input, Word.ofNatModulo (input + 3)]
      observe skippedPlan input expected [Word.ofNatModulo (input + 3)]
    for (input, expected) in inputs.zip (incrementExpected variant) do
      observe arbitraryPlan input expected [Word.ofNatModulo 2, Word.ofNatModulo (input + 4)]
    for (input, expected) in inputs.zip (constantExpected variant) do
      observe constantPlan input expected [Word.ofNatModulo 45]
    match (identityPlan.instantiate Word.zero).toCore.runStateful 0 with
    | .outOfFuel _ => pure ()
    | _ => throw (IO.userError "zero fuel was mistaken for closure completion")

private def admissionChecks : IO Unit := do
  for (variant, overhead) in Variant.all.zip [70, 78] do
    ensure (Variant.ofString? variant.name == some variant) "closure variant is not canonical"
    for graph in [← step [identityWithCell], ← step [privateStep] arbitraryEntry] do
      let plan ← checked graph variant
      ensure (plan.program.check && plan.variant == variant &&
        plan.program.resultType == .function .word .word)
        "closure plan changed variant or escaped whole-program checking"
      match plan.program.body with
      | .letE saved (.letE (.lambda (.function .word .word) _ _) (.lambda .word .word _)) =>
          ensure (Wire.encodeExpr saved == Wire.encodeExpr graph.program.body)
            "closure wrapper ignored its arbitrary checked step entry"
      | _ => throw (IO.userError "closure wrapper lost its higher-order apply closure")
      let measured := Wire.programNodes (plan.instantiate Word.maximum)
      ensure (measured == Closure.appliedNodes graph variant &&
        measured == Closure.canonicalNodes graph variant &&
        measured == Wire.programNodes graph.program + Closure.appliedOverhead variant &&
        Closure.appliedOverhead variant == overhead)
        "closure node overhead differs from the complete original Core application"
      ensure ((← emitted plan) == (← emitted plan)) "closure source emission is nondeterministic"
  for invalid in ["", "Snapshot", "alias", "independent ", "word"] do
    ensure (Variant.ofString? invalid).isNone "closure variant parsing accepted noncanonical metadata"
  -- Raw primitives render through the call-graph helpers with the alias import.
  let divided ← step [.binary .wordDiv (.var 0) (word 1)]
  for variant in Variant.all do
    match Solcore.Synthesis.Source.Closure.emit (← checked divided variant) with
    | .ok emitted =>
        unless (emitted.source.splitOn "import { div as sc_div, mod as sc_mod, ").length == 2 &&
            (emitted.source.splitOn "    let sc_v3: word = sc_div(sc_v0, sc_v2);").length == 2 do
          throw (IO.userError "closure emission lost the raw division alias or its operand snapshots")
    | .error error => throw (IO.userError s!"closure raw division was rejected: {reprStr error}")

private def contains (source fragment : String) : Bool := (source.splitOn fragment).length > 1

private def formattingChecks : IO Unit := do
  let graph ← step [privateStep] arbitraryEntry
  let capturePrefix := String.intercalate "\n" [
    "        let sc_cap: word = sc_step(sc_input);",
    "        let sc_first: function (word) returns (word) = lam (sc_arg: word) -> word {",
    "            return sc_cap + sc_arg;", "        };", "        sc_cap = sc_cap + 1;"]
  let calls := String.intercalate "\n" [
    "        sc_cap = sc_cap + 2;", "        let sc_a: word = sc_first(sc_input);",
    "        let sc_b: word = sc_apply(sc_second, sc_input + 1);",
    "        return uint256(3 * sc_a + sc_b + sc_cap);"]
  for variant in Variant.all do
    let source ← emitted (← checked graph variant)
    ensure (contains source.source capturePrefix && contains source.source calls &&
      contains source.source "function sc_apply<a>(f: function (a) returns (a), x: a) returns (a) {\n    return f(x);\n}" &&
      (source.source.splitOn " = sc_step(sc_input);").length == 2 &&
      (source.source.splitOn " = sc_apply(").length == 2)
      "closure source changed snapshot timing, repeated the step or bypassed generic forwarding"
    ensure (contains source.source (String.intercalate "\n" [
      "function sc_step(sc_arg: word) returns (word) {",
      "    let sc_v0: word = sc_fn0(sc_arg);", "    let sc_v1: word = 1;",
      "    let sc_v2: word = (sc_v0 - sc_v1);", "    return sc_v2;", "}"]))
      "closure source replaced the arbitrary entry with its last helper"
    ensure (source.contractName == "SynthesizedClosures" && source.methodName == "run" &&
      source.methodSignature == "run(uint256)" && source.deployPath == ["SynthesizedClosuresDeploy"] &&
      source.runtimePath == ["SynthesizedClosuresDeploy", "SynthesizedClosures"])
      "closure wrapper metadata changed"
    match variant with
    | .snapshot =>
        ensure (contains source.source
          "sc_cap = sc_cap + 1;\n        let sc_second: function (word) returns (word) = sc_first;\n        sc_cap = sc_cap + 2;" &&
          (source.source.splitOn " = lam (").length == 2)
          "snapshot source recreated its first closure after mutation"
    | .independent =>
        ensure (contains source.source (String.intercalate "\n" [
          "        sc_cap = sc_cap + 1;",
          "        let sc_second: function (word) returns (word) = lam (sc_arg: word) -> word {",
          "            return sc_cap + sc_arg;", "        };", "        sc_cap = sc_cap + 2;"]) &&
          (source.source.splitOn " = lam (").length == 3)
          "independent source lost the second capture's distinct creation time"
  ensure (Solcore.Synthesis.Source.Closure.emitterVersion == "solcore-source-closures-v2" &&
    Solcore.Synthesis.Source.Closure.wrapperVersion == "solcore-word-closures-contract-v1" &&
    Solcore.Synthesis.Source.Closure.selector == "0xa444f5e9" &&
    Closure.version == "core-closure-capture-plan-v1") "closure provenance changed"

def testSourceClosureEmitter : IO Unit := do
  admissionChecks
  executionChecks
  formattingChecks

end Tests.SourceClosureEmitter
end

section
-- leanmerge: from Solcore.Test.SourceLoopClosureCases
/-! The `runtime-loop-closures` profile. Plans admit masks 0, 1, 3 and 7 and
two captures. The unrolled Core reference returns what a model of the emitted
loop returns, iteration by iteration over the step's original Core: the
accumulator capture computes `step(acc + c) + acc + 1` from the snapshot taken
before `acc` changes, and the counter capture `step(acc) + c` from the counter
before its increment. Generation draws all six shapes and replays exactly;
tampering is refused, and reductions lower the mask or move the input, keep
the capture and stay strictly smaller. -/
set_option autoImplicit false

namespace Tests.SourceLoopClosureCases

open Lean
open Solcore.Core (Word)
open Solcore.Synthesis.Core
open Solcore.Synthesis.Core.LoopClosure (CheckedPlan Capture)
open Solcore.Synthesis.Source

private def get {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def fuel : Nat := 1000000

private def cases (corpus : Json) : IO (Array Json) :=
  get (corpus.getObjValAs? (Array Json) "cases")

private def directWord (case : Json) : IO Word := do
  let text ← get ((← get (case.getObjVal? "directCore")).getObjValAs? String "word")
  let some value := text.toNat? | throw (IO.userError "invalid result Word")
  return Word.ofNatModulo value

private def withPlan (case : Json) (change : Json → Json) : IO Json := do
  return case.setObjVal! "loopClosurePlan" (change (← get (case.getObjVal? "loopClosurePlan")))

private def plus (value : Word) (other : Nat) : Word := Word.ofNatModulo (value.val + other)

private def step (plan : CheckedPlan) (value : Word) : Option Word :=
  match (plan.step.instantiate value).toCore.runStateful fuel with
  | .done (.word result) _ => some result
  | _ => none

/-- The emitted loop, iteration by iteration, with closure snapshots. -/
private def model (plan : CheckedPlan) (input : Word) : Option Word := do
  let mut accumulator := input
  for counter in List.range (plan.iterations input) do
    match plan.capture with
    | .accumulator =>
        let snapshot := accumulator
        accumulator := plus snapshot 1
        accumulator := plus (← step plan (plus snapshot counter)) accumulator.val
    | .counter => accumulator := plus (← step plan accumulator) counter
  return accumulator

private def admissionChecks (step : Aggregates.CheckedDAG) : IO Unit := do
  for mask in [0, 1, 3, 7] do
    for capture in Capture.all do
      ensure (CheckedPlan.ofParts? step mask capture).isSome s!"mask {mask} with capture {capture.name} was refused"
  for mask in [2, 5, 15] do
    ensure (CheckedPlan.ofParts? step mask .counter).isNone s!"mask {mask} was admitted"
  ensure (Capture.all.map Capture.name == ["accumulator", "counter"] &&
      Capture.all.all (fun capture => Capture.ofString? capture.name == some capture)) "capture names changed"

/-- Each capture's closure, its change before the call and the wrapper's bound. -/
private def emitterChecks (step : Aggregates.CheckedDAG) : IO Unit := do
  for (capture, lines) in [
      (Capture.accumulator, ["                return sc_step(sc_acc + sc_arg);",
        "            sc_acc = (sc_acc + 1);", "            sc_acc = (sc_f(sc_counter) + sc_acc);"]),
      (.counter, ["                return (sc_step(sc_arg) + sc_counter);",
        "            sc_counter = (sc_counter + 1);", "            sc_acc = sc_apply(sc_f, sc_acc);"])] do
    let some plan := CheckedPlan.ofParts? step 7 capture | throw (IO.userError "plan refused")
    let source := (← get ((LoopClosure.emit plan).mapError reprStr)).source
    for line in lines ++ ["        let sc_limit: word = (sc_input & 7);", "        while (sc_limit > sc_counter) {",
        "            let sc_f: function (word) returns (word) = lam (sc_arg: word) -> word {"] do
      ensure ((source.splitOn line).length == 2) s!"{capture.name}: the source lacks the line {line}"

private def generationChecks : IO Unit := do
  let corpus := LoopClosure.generateCases (Seed.ofNat 1) 384 1020 400 fuel .v4 .seeded
  ensure (corpus == LoopClosure.generateCases (Seed.ofNat 1) 384 1020 400 fuel .v4 .seeded)
    "loop-closure generation is not deterministic"
  let generated ← cases corpus
  ensure (generated.size == 1020) "loop-closure generation did not complete"
  let excluded ← get (corpus.getObjValAs? (Array Json) "excluded")
  for entry in excluded do
    let reason ← get (entry.getObjValAs? String "reason")
    ensure (reason == "all positive-trip boundary inputs returned their original input" ||
        reason == "node budget is too small for the selected aggregate template or exceeds 512")
      s!"unexpected loop-closure exclusion: {reason}"
  let mut shapes : List String := []
  for index in List.range (generated.size / 10) do
    let function := generated.extract (10 * index) (10 * index + 10)
    let some first := function[0]? | throw (IO.userError "empty function")
    let plan := (← get (LoopClosure.caseProgram first)).plan
    shapes := s!"{plan.mask}:{plan.capture.name}" :: shapes
    let mut changed := false
    for (case, position) in function.zipIdx do
      let input := (← get (LoopClosure.caseProgram case)).input
      let result ← directWord case
      ensure (plan.iterations input ≤ 7) "a call ran more than seven iterations"
      ensure (model plan input == some result) "the Core reference differs from the loop-closure model"
      if position < 6 && plan.iterations input > 0 && result != input then changed := true
    ensure changed "a generated loop closure returned every positive-trip boundary input"
  ensure (shapes.eraseDups.length == 6) s!"generation drew {shapes.eraseDups.length} of six shapes"

private def replayChecks (case : Json) : IO Unit := do
  ensure ((← get (LoopClosure.replayCase case fuel)) == case) "a loop-closure case failed exact replay"
  let plan ← get (case.getObjVal? "loopClosurePlan")
  let mask ← get (plan.getObjValAs? Nat "mask")
  let capture ← get (plan.getObjValAs? String "capture")
  for changed in [
      ← withPlan case (·.setObjVal! "mask" (toJson (if mask == 7 then 3 else 7))),
      ← withPlan case (·.setObjVal! "mask" (toJson (5 : Nat))),
      ← withPlan case (·.setObjVal! "capture" (toJson (if capture == "counter" then "accumulator" else "counter"))),
      ← withPlan case (·.setObjVal! "capture" (toJson "reference"))] do
    ensure (LoopClosure.replayCase changed fuel matches .error _) "a tampered loop-closure case replayed"

private def reductionChecks (case : Json) : IO Unit := do
  let source ← get (LoopClosure.caseProgram case)
  let mut lowered := false
  for reduced in LoopClosure.reductions source do
    let plan := reduced.candidate.plan
    ensure (plan.mask ≤ source.plan.mask && plan.capture == source.plan.capture &&
        plan.step.helpers.length == source.plan.step.helpers.length)
      "a reduction raised the mask, changed the capture or changed the helper count"
    ensure ((complexity reduced.candidate.program.body).isStrictlySmaller (complexity source.program.body))
      "a reduction is not strictly smaller"
    if plan.mask < source.plan.mask then lowered := true
  ensure (lowered || source.plan.mask == 0) "no reduction lowered the mask"
  let emitted ← cases (← get (LoopClosure.shrinkCases case 4 fuel))
  ensure (!emitted.isEmpty) "a loop-closure case has no reduction"
  for candidate in emitted do
    ensure ((← get (LoopClosure.replayCase candidate fuel)) == candidate) "a reduction failed exact replay"

/-- An imported plan with mask zero never runs its loop. -/
private def importChecks (step : Aggregates.CheckedDAG) : IO Unit := do
  for capture in Capture.all do
    let some plan := CheckedPlan.ofParts? step 0 capture | throw (IO.userError "plan refused")
    let case ← get (LoopClosure.emitCase plan (Word.ofNatModulo 7) (Json.mkObj [("kind", toJson "imported")]) fuel)
    ensure ((← directWord case) == Word.ofNatModulo 7) "a plan of mask zero changed its input"
    ensure ((← get (LoopClosure.replayCase case fuel)) == case) "an imported loop-closure case failed exact replay"

def testSourceLoopClosureCases : IO Unit := do
  let generated ← cases (LoopClosure.generateCases (Seed.ofNat 2) 384 6 16 fuel .v4)
  let some first := generated[0]? | throw (IO.userError "no loop-closure case")
  let source ← get (LoopClosure.caseProgram first)
  admissionChecks source.plan.step
  emitterChecks source.plan.step
  importChecks source.plan.step
  generationChecks
  for case in generated do
    replayChecks case
  for case in generated.extract 1 5 do
    reductionChecks case

end Tests.SourceLoopClosureCases
end
