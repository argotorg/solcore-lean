import Solcore.Synthesis.Internal.CallGraphs
import Solcore.Core.Machine
import Solcore.Core.Wire.Codec
import Solcore.Synthesis.Internal.Loops
import Solcore.Synthesis.Internal.Calls

/-!
# Call graph profile tests

Call graphs, call graph loops, nested calls, recursion and recursive loops.
-/

section
-- leanmerge: from Solcore.Test.SourceCallGraphCases
/-! Direct graph generation, strict canonical replay and typed shrinking.
Only original Core executions are performed here, not Rust or EVM executions. -/
set_option autoImplicit false

namespace Tests.SourceCallGraphCases
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

private def graph (helpers : List Wire.Expr) (entry : Wire.Expr) : IO CheckedWordFunctionDAG :=
  match CheckedWordFunctionDAG.ofParts? helpers entry with
  | some value => pure value
  | none => throw (IO.userError "call graph test fixture failed full Core typing")

private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)
private def field (json : Json) (key : String) : IO Json := get (json.getObjVal? key)
private def string (json : Json) (key : String) : IO String := get (json.getObjValAs? String key)
private def natural (json : Json) (key : String) : IO Nat := get (json.getObjValAs? Nat key)
private def rows (json : Json) : IO (Array Json) := get (json.getObjValAs? (Array Json) "cases")

private def imported (function : CheckedWordFunctionDAG) (input : Word) : IO Json :=
  get (CallGraph.emitCase function input (Json.mkObj [("kind", toJson "imported")]) 2000)

private def mixedGraph : IO CheckedWordFunctionDAG := graph [
    .binary .wordAdd (.var 0) (word 1),
    .binary .wordMul (.apply (.var 1) (.var 0)) (word 2),
    .binary .wordAdd (.apply (.var 2) (.var 0)) (.apply (.var 1) (.var 0))]
  (.letE (.apply (.var 1) (.var 0))
    (.ifE (.binary .wordGt (.apply (.var 4) (.var 1)) (word 1))
      (.apply (.var 3) (.var 0))
      (.apply (.var 4) (.apply (.var 2) (.var 0)))))

private def coreAndImports : IO Json := do
  let function ← mixedGraph
  ensure (CallGraph.callShapes function == Solcore.Synthesis.Core.CallGraph.callShapeCatalog)
    "mixed graph no longer covers the exact ordered nine AST call shapes"
  for (input, expected) in [(0, 13), (1, 14), (Word.maximum.val, 4), (2 ^ 255, 8)] do
    let saved ← imported function (Word.ofNatModulo input)
    let observation ← field saved "directCore"
    ensure ((← string observation "status") == "returned" &&
      (← string observation "word") == toString expected) "scoped helper/branch Core golden differs"
    ensure ((← get (CallGraph.replayCase saved 2000)) == saved) "import replay changed a canonical case"
  let first ← imported function Word.zero
  for input in CallGraph.boundaryInputs do
    let saved ← imported function input
    ensure ((← string saved "source") == (← string first "source"))
      "emitted source depends on its runtime argument"
    ensure (← get (CallGraph.caseProgram saved)).program.check "applied graph lost typing"
    let forged := saved.setObjVal! "directCore" (Json.mkObj [("status", toJson "invented")])
    ensure ((← get (CallGraph.replayCase forged 2000)) == saved) "saved observation supplied the oracle"
    let suspended ← get (CallGraph.replayCase saved 0)
    ensure ((← string (← field suspended "directCore") "status") == "out-of-fuel")
      "zero fuel was treated as a completed Core result"
  let constant ← graph [word 7] (word 7)
  let savedConstant ← imported constant Word.maximum
  ensure ((← string (← field savedConstant "directCore") "word") == "7")
    "constant imported/reduced graphs were incorrectly excluded"
  reject (CallGraph.inputSensitive constant 2000) "constant graph admitted as exploration"
  let deadCalls ← graph [.var 0, .apply (.var 1) (.var 0)] (.var 0)
  reject (CallGraph.inputSensitive deadCalls 2000) "dead helper-only calls passed exploration filter"
  reject (CallGraph.inputSensitive function 0) "resource failure passed generation filter"
  let oversizedBody := (List.range 256).foldl (fun body _ => .binary .wordAdd body (word 0))
    (.var 0 : Wire.Expr)
  reject (CallGraph.emitCase (← graph [oversizedBody] (.apply (.var 1) (.var 0))) Word.zero
    (Json.mkObj [("kind", toJson "imported")]) 2000) "oversized graph escaped applied node budget"
  return first

private def generationChecks : IO Json := do
  let corpus := CallGraph.generateCases (Seed.ofNat 0) 192 17 128 2000
  ensure (corpus == CallGraph.generateCases (Seed.ofNat 0) 192 17 128 2000)
    "direct graph generation is not deterministic"
  ensure ((← string corpus "status") == "complete") "bounded generated corpus did not complete"
  let generated ← rows corpus
  let excluded ← get (corpus.getObjValAs? (Array Json) "excluded")
  ensure (generated.size == 17 && (← natural corpus "attempted") == 3 + excluded.size &&
    (← natural corpus "attempted") ≤ 128) "function attempts and runtime cases were confused"
  for index in List.range generated.size do
    let saved := generated[index]!
    let admitted ← get (CallGraph.caseProgram saved)
    let provenance ← field saved "provenance"
    let origin ← field provenance "origin"
    ensure (admitted.program.check && Wire.programNodes admitted.program ≤ 192 &&
      CallGraph.hasEntryCall admitted.function) "generated case escaped typing, budget or entry-call filter"
    ensure ((← natural origin "inputIndex") == index % 8 &&
      some admitted.input == CallGraph.boundaryInputs[index % 8]?) "input bank order changed"
    ensure ((← get (CallGraph.replayCase saved 2000)) == saved) "generated graph replay differs"
    ensure ((← string (← field (← get (CallGraph.replayCase saved 0)) "directCore") "status") == "out-of-fuel")
      "new replay fuel was confused with stored generation validation fuel"
    if index % 8 > 0 then
      ensure ((← string saved "source") == (← string generated[index - index % 8]! "source"))
        "one generated graph emitted different sources across inputs"
  let truncated := CallGraph.generateCases (Seed.ofNat 0) 192 3 1 2000
  ensure ((← rows truncated).size == 3 && (← natural truncated "attempted") == 1 &&
    (← string truncated "status") == "complete") "case count did not truncate a boundary group"
  let limited := CallGraph.generateCases (Seed.ofNat 0) 192 9 1 2000
  ensure ((← rows limited).size == 8 && (← string limited "status") == "generation-exhausted")
    "attempt exhaustion was reported as complete"
  for budget in [12, 513] do
    let invalid := CallGraph.generateCases (Seed.ofNat 0) budget 1 3 2000
    ensure ((← rows invalid).isEmpty && (← natural invalid "attempted") == 3 &&
      (← get (invalid.getObjValAs? (Array Json) "excluded")).size == 3)
      "invalid requested budget lost bounded exclusions"
  let resources := CallGraph.generateCases (Seed.ofNat 0) 192 1 1 0
  let reasons ← get (resources.getObjValAs? (Array Json) "excluded")
  ensure ((← rows resources).isEmpty && (← string resources "status") == "generation-exhausted" &&
    (← string reasons[0]! "category") == "inconclusive-resource" &&
    (← string reasons[0]! "code") == "boundary-out-of-fuel") "fuel exclusion was treated as a pass"
  ensure ((← natural (CallGraph.generateCases (Seed.ofNat 0) 192 0 100 2000) "attempted") == 0)
    "empty request consumed attempts"
  ensure ((← rows (CallGraph.generateCases (Seed.ofNat 0) 192 1 0 2000)).isEmpty)
    "zero attempt limit was ignored"
  return corpus

private def tamperingChecks (saved : Json) : IO Unit := do
  let provenance ← field saved "provenance"
  let origin ← field provenance "origin"
  let withOrigin := fun changed => saved.setObjVal! "provenance" (provenance.setObjVal! "origin" changed)
  for name in ["profileVersion", "functionVersion", "generatorVersion", "boundaryVersion",
      "callShapeVersion", "emitterVersion", "wrapperVersion"] do
    reject (CallGraph.replayCase (saved.setObjVal! "provenance"
      (provenance.setObjVal! name (toJson "forged"))) 2000) "tampered version accepted"
  for (name, value) in [("seed", toJson "00"), ("seed", toJson "1"),
      ("finalSeed", toJson "0"), ("maxProgramNodes", toJson (513 : Nat)),
      ("bodyBudgets", toJson ([1] : List Nat)), ("helperCount", toJson (99 : Nat)),
      ("inputIndex", toJson (8 : Nat)), ("validationFuel", toJson (10000001 : Nat)),
      ("kind", toJson "unknown"), ("extra", toJson true)] do
    reject (CallGraph.replayCase (withOrigin (origin.setObjVal! name value)) 2000)
      s!"tampered generated {name} accepted"
  for (name, value) in [("helperCount", toJson (99 : Nat)),
      ("callShapes", toJson ["invented"]), ("features", toJson ([] : List String)),
      ("extra", toJson true)] do
    reject (CallGraph.replayCase (saved.setObjVal! "provenance" (provenance.setObjVal! name value)) 2000)
      s!"tampered provenance {name} accepted"
  for (name, value) in [("input", toJson "01"), ("input", toJson "1"),
      ("source", toJson "forged"), ("schema", toJson "forged"),
      ("executionFuel", toJson (10000001 : Nat)), ("extra", toJson true)] do
    reject (CallGraph.replayCase (saved.setObjVal! name value) 2000) s!"tampered envelope {name} accepted"
  let contract ← field saved "contract"
  for (name, value) in [("calldata", toJson "0xa444f5e9"), ("constructorCalldata", toJson "0x00"),
      ("signature", toJson "run()"), ("runtimePath", toJson ["Other"]), ("extra", toJson true)] do
    reject (CallGraph.replayCase (saved.setObjVal! "contract" (contract.setObjVal! name value)) 2000)
      "tampered ABI/contract envelope accepted"
  let program ← field saved "program"
  reject (CallGraph.caseProgram (saved.setObjVal! "program" (program.setObjVal! "extra" (toJson true))))
    "extra Core wire field accepted"
  let bad : Wire.Program := {
    resultType := .word, dataDefinitions := [],
    body := .apply (functionDAGExpression [.var 0] (.apply (.var 2) (.var 0))) (word 0)}
  reject (CallGraph.caseProgram (saved.setObjVal! "program" (Wire.encodeProgram bad)))
    "out-of-scope helper escaped case readmission"

private def shrinkingChecks (saved : Json) : IO Unit := do
  let source ← get (CallGraph.caseProgram saved)
  let first ← get (CallGraph.shrinkCases saved 40 2000)
  ensure (first == (← get (CallGraph.shrinkCases saved 40 2000))) "shrinking is nondeterministic"
  let candidates ← rows first
  ensure (!candidates.isEmpty && candidates.size ≤ 40) "bounded shrink yielded no candidates"
  for candidate in candidates do
    let admitted ← get (CallGraph.caseProgram candidate)
    ensure (admitted.program.check && admitted.function.helpers.length == source.function.helpers.length &&
      (complexity admitted.program.body).isStrictlySmaller (complexity source.program.body))
      "shrinking lost full typing, helper count or strict measure"
    ensure ((← get (CallGraph.replayCase candidate 2000)) == candidate) "reduced case failed exact replay"
  let unchangedOrigin := Json.mkObj [("kind", toJson "reduced"),
    ("parentProgram", Wire.encodeProgram source.program), ("parentInput", toJson (toString source.input.val))]
  let unchanged ← get (CallGraph.emitCase source.function source.input unchangedOrigin 2000)
  reject (CallGraph.replayCase unchanged 2000) "non-strict self reduction accepted"
  let smallerGraph ← graph [.var 0] (.var 0)
  let wrongCount ← get (CallGraph.emitCase smallerGraph Word.zero unchangedOrigin 2000)
  reject (CallGraph.replayCase wrongCount 2000) "reduction changed helper declarations"
  let reduced := candidates[0]!
  let provenance ← field reduced "provenance"
  let origin ← field provenance "origin"
  for (key, value) in [("parentInput", toJson "01"), ("parentInput", toJson "1"),
      ("parentProgram", Json.null), ("extra", toJson true)] do
    reject (CallGraph.replayCase (reduced.setObjVal! "provenance"
      (provenance.setObjVal! "origin" (origin.setObjVal! key value))) 2000)
      "invalid reduced parent provenance accepted"

def testSourceCallGraphCases : IO Unit := do
  let importedCase ← coreAndImports
  let corpus ← generationChecks
  tamperingChecks (← rows corpus)[0]!
  shrinkingChecks importedCase

end Tests.SourceCallGraphCases
end

section
-- leanmerge: from Solcore.Test.SourceCallGraphCorpus
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
end

section
-- leanmerge: from Solcore.Test.SourceCallGraphEmitter
/-! Checked original Core goldens and source ordering regressions for arbitrary
acyclic scalar helper calls. These tests neither execute emitted source nor
prove compiler meaning preservation. -/
set_option autoImplicit false

namespace Tests.SourceCallGraphEmitter
open Solcore.Core Solcore.Synthesis.Core Solcore.Synthesis.Source

private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)
private def call (index : Nat) (argument : Wire.Expr) : Wire.Expr := .apply (.var index) argument
private def maximum : Nat := Word.maximum.val
private def high : Nat := 2 ^ 255

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def checked (helpers : List Wire.Expr) (entry : Wire.Expr) : IO CheckedWordFunctionDAG :=
  match CheckedWordFunctionDAG.ofParts? helpers entry with
  | some graph => pure graph
  | none => throw (IO.userError "call graph failed checked admission")

private def emitted (graph : CheckedWordFunctionDAG) : IO EmittedProgram :=
  match CallGraph.emit graph with
  | .ok source => pure source
  | .error error => throw (IO.userError s!"call graph emission failed: {reprStr error}")

private def render (functions : List String) (target : Target) (locals : List String)
    (indent nextId : Nat) (body : Wire.Expr) : IO ScalarRenderer.Rendered :=
  match CallGraphRenderer.renderWithFunctions functions target locals indent nextId body with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"call graph rendering failed: {reprStr error}")

private def observe (graph : CheckedWordFunctionDAG) (input expected : Nat) : IO Unit := do
  let original := graph.instantiate (Word.ofNatModulo input)
  ensure original.check "original applied call graph failed Core typing"
  match original.toCore.runStateful 10000 with
  | .done (.word value) state =>
      ensure (value.val == expected) s!"original Core result {value.val} differs from {expected}"
      ensure state.isEmpty "scalar helper calls allocated a cell"
  | _ => throw (IO.userError "original Core call graph did not complete")

/-- Calls occur inside let initializers, branch predicates, primitive operands
and nested call arguments. The entry combines two different dependency paths. -/
def mixedHelpers : List Wire.Expr := [
  .binary .wordAdd (.var 0) (word 1),
  .letE (call 1 (.var 0))
    (.ifE (.binary .wordSgt (.var 1) (word 0))
      (.ternary .wordAddMod (call 2 (.var 0)) (call 2 (.var 1)) (word 7))
      (.binary .wordSdiv (call 2 (.var 1)) (word 2))),
  .binary .wordShl (call 1 (call 2 (.var 0))) (call 2 (word 0))]

def mixedEntry : Wire.Expr :=
  .letE (call 1 (.var 0)) (.binary .wordXor (.var 0) (call 4 (call 3 (.var 1))))

private def originalChecks : IO Unit := do
  let graph ← checked mixedHelpers mixedEntry
  ensure (graph.program.check && functionHelpersAccepted graph.helpers)
    "mixed graph did not retain the whole checker boundary"
  let some restored := CheckedWordFunctionDAG.ofProgram? graph.program |
    throw (IO.userError "original mixed graph could not be readmitted")
  ensure (Wire.encodeProgram restored.program == Wire.encodeProgram graph.program)
    "readmission changed helper declaration order or entry"
  for (input, expected) in [(0, 11), (1, 6), (maximum, 1), (high, high / 2)] do
    observe graph input expected
  let source ← emitted graph
  ensure (source == (← emitted graph)) "call graph emission is nondeterministic"
  ensure (source.contractName == "SynthesizedCallGraphs" && source.methodName == "run" &&
    source.methodSignature == "run(uint256)" && source.deployPath == ["SynthesizedCallGraphsDeploy"] &&
    source.runtimePath == ["SynthesizedCallGraphsDeploy", "SynthesizedCallGraphs"])
    "call graph wrapper metadata changed"
  ensure (CallGraph.emitterVersion == "solcore-source-call-graphs-v2" &&
    CallGraph.wrapperVersion == "solcore-word-call-graphs-contract-v1" &&
    CallGraph.selector == "0xa444f5e9") "call graph versions or ABI selector changed"
  -- A Bool condition may itself contain calls; only the selected branch calls
  -- its helper, and the new Word binder shifts the earlier-helper index.
  let branch : Wire.Expr := .ifE (.binary .wordEq (call 1 (.var 0)) (word 1))
    (.letE (word 7) (call 2 (.binary .wordAdd (.var 0) (.var 1))))
    (call 1 (call 1 (.var 0)))
  let branched ← checked [.binary .wordAdd (.var 0) (word 1)] branch
  observe branched 0 8
  observe branched 1 3
  observe branched maximum 1

private def primitiveChecks : IO Unit := do
  let c := call 1
  let fixtures : List (Wire.Expr × Nat × Nat) := [
    (.unary .wordClz (c (.var 0)), 0, 256),
    (.binary .wordDiv (c (.var 0)) (c (word 2)), 5, 2),
    (.binary .wordMod (c (.var 0)) (c (word 0)), maximum, 0),
    (.binary .wordShl (c (word 1)) (c (.var 0)), 255, high),
    (.binary .wordShr (c (word maximum)) (c (.var 0)), 256, 0),
    (.binary .wordSar (c (word high)) (c (.var 0)), maximum, maximum),
    (.binary .wordSdiv (c (.var 0)) (c (word maximum)), high, high),
    (.binary .wordSmod (c (.var 0)) (c (word 2)), maximum - 6, maximum),
    (.ifE (.binary .wordSgt (c (.var 0)) (c (word 0))) (word 1) (word 0), high - 1, 1),
    (.binary .wordByte (c (.var 0)) (c (word 0x1234)), 31, 0x34),
    (.binary .wordPow (c (word maximum)) (c (.var 0)), maximum, maximum),
    (.binary .wordSignExtend (c (word 0)) (c (.var 0)), 0x80, maximum - 0x7f),
    (.ternary .wordAddMod (c (.var 0)) (c (word 1)) (c (word maximum)), maximum, 1),
    (.ternary .wordMulMod (c (.var 0)) (c (word 2)) (c (word maximum)), high, 1)]
  for (body, input, expected) in fixtures do
    let graph ← checked [.var 0] body
    ensure (CallGraphRenderer.supported body) "call graph excluded a primitive/call composition"
    let _ ← emitted graph
    observe graph input expected
  -- Every scalar primitive without a call must render exactly as its frozen
  -- primitive-profile counterpart, including raw snapshots and shift order.
  let mut expressions : List (Target × Wire.Expr) := []
  for operation in unaryOps do
    let operand := if operation == .boolNot then Wire.Expr.bool true else word 5
    expressions := expressions ++ [(Target.unaryResult operation, .unary operation operand)]
  for operation in binaryOps do
    expressions := expressions ++ [(Target.binaryResult operation, .binary operation (.var 0) (word 2))]
  for operation in ternaryOps do
    expressions := expressions ++ [(.word, .ternary operation (.var 0) (word 2) (word 7))]
  for (target, body) in expressions do
    let actual ← render ["sc_fn0"] target ["sc_input"] 4 7 body
    match PrimitiveRenderer.render target ["sc_input"] 4 7 body with
    | .ok expected =>
        ensure (actual.lines == expected.lines && actual.value == expected.value && actual.nextId == expected.nextId)
          "call-graph primitive formatting drifted from the primitive profile"
    | .error _ => throw (IO.userError "primitive compatibility fixture was unsupported")

private def formattingChecks : IO Unit := do
  let nested : Wire.Expr := .binary .wordShl (call 2 (call 1 (.var 0))) (call 1 (word 1))
  let result ← render ["near", "far"] .word ["input"] 4 0 nested
  ensure (result.lines == [
    "    let sc_v0: word = input;", "    let sc_v1: word = near(sc_v0);",
    "    let sc_v2: word = sc_v1;", "    let sc_v3: word = far(sc_v2);",
    "    let sc_v4: word = sc_v3;", "    let sc_v5: word = 1;",
    "    let sc_v6: word = sc_v5;", "    let sc_v7: word = near(sc_v6);",
    "    let sc_v8: word = sc_v7;", "    let sc_v9: word = sc_shl(sc_v8, sc_v4);"])
    "nested helper calls or raw shift operands changed evaluation order"
  let branch : Wire.Expr := .ifE (.binary .wordSgt (call 1 (.var 0)) (word 0))
    (.letE (word 7) (call 2 (.var 0))) (call 1 (word 9))
  let result ← render ["sc_fn0"] .word ["input"] 4 0 branch
  ensure (result.lines == [
    "    let sc_v0: word = input;", "    let sc_v1: word = sc_fn0(sc_v0);",
    "    let sc_v2: word = sc_v1;", "    let sc_v3: word = 0;", "    let sc_v4: word = sc_v3;",
    "    let sc_v5: bool = tobool(sc_sgt(sc_v2, sc_v4));", "    let sc_v6: word = 0;",
    "    if (sc_v5) {", "        let sc_v7: word = 7;", "        let sc_v8: word = sc_v7;",
    "        let sc_v9: word = sc_v8;", "        let sc_v10: word = sc_fn0(sc_v9);",
    "        sc_v6 = sc_v10;", "    } else {", "        let sc_v11: word = 9;",
    "        let sc_v12: word = sc_v11;", "        let sc_v13: word = sc_fn0(sc_v12);",
    "        sc_v6 = sc_v13;", "    }"])
    "branch-local helper calls escaped their branch or changed binder scope"
  let identity ← emitted (← checked [.var 0] (call 1 (.var 0)))
  ensure (identity.source == String.intercalate "\n" [
    "pragma solcore;", "import * from std;", "import * from std.dispatch;",
    Primitive.opcodeImport, "",
    "function sc_fn0(sc_arg: word) returns (word) {", "    return sc_arg;", "}", "",
    "contract SynthesizedCallGraphs {", "    function run(input: uint256) public returns (uint256) {",
    "        let sc_input: word = Typedef.rep(input);", "        let sc_v0: word = sc_input;",
    "        let sc_v1: word = sc_fn0(sc_v0);", "        return uint256(sc_v1);", "    }", "}", ""])
    "named helper declaration or fixed ABI wrapper changed"

private def rejectionChecks : IO Unit := do
  for body in [(.var 1 : Wire.Expr), .apply (.var 0) (.var 0), .apply (.var 2) (.var 0),
      .apply (.lambda .word .word (.var 0)) (word 0), .newCell .word (word 0),
      .integer 0, .pair (word 0) (word 1)] do
    ensure (CheckedWordFunctionDAG.ofParts? [.var 0] body).isNone
      "closed scalar DAG accepted an escaping/local/host function or unsupported value"
  for helpers in [([] : List Wire.Expr), List.replicate 4 (.var 0),
      [call 1 (.var 0)], [.var 0, call 2 (.var 0)]] do
    ensure (CheckedWordFunctionDAG.ofParts? helpers (call 1 (.var 0))).isNone
      "DAG accepted an empty, oversized, recursive or forward dependency"
  for (target, body) in [(.word, call 0 (.var 0)), (.word, call 2 (.var 0)),
      (.bool, call 1 (.var 0)), (.word, .apply (.lambda .word .word (.var 0)) (word 0)),
      (.word, .newCell .word (word 0)), (.word, .binary .integerAdd (word 0) (word 1))] do
    match CallGraphRenderer.renderWithFunctions ["sc_fn0"] target ["input"] 4 0 body with
    | .error _ => pure ()
    | .ok _ => throw (IO.userError "standalone renderer accepted an unsupported callee or expression")
  match CallGraphRenderer.renderWithFunctions ["sc_fn0"] .word ["input"] 4 0 (.var 1) with
  | .error (.unboundLocal 1) => pure ()
  | _ => throw (IO.userError "helper escaped as a scalar value")

def testSourceCallGraphEmitter : IO Unit := do
  originalChecks
  primitiveChecks
  formattingChecks
  rejectionChecks

end Tests.SourceCallGraphEmitter
end

section
-- leanmerge: from Solcore.Test.SourceCallGraphLoopCases
/-! Bounded call-graph loop generation, strict canonical replay and typed
shrinking. Only original Core executions are performed here, not Rust or EVM. -/
set_option autoImplicit false

namespace Tests.SourceCallGraphLoopCases
open Lean Solcore.Core Solcore.Synthesis.Core Solcore.Synthesis.Source
open Solcore.Synthesis.Core.CallGraphLoop (CheckedPlan)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def get {α : Type} : Except String α → IO α
  | .ok result => pure result
  | .error message => throw (IO.userError message)

private def reject {α : Type} (value : Except String α) (message : String) : IO Unit :=
  match value with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError message)

private def plan (helpers : List Wire.Expr) (entry : Wire.Expr) (mask : Nat) : IO CheckedPlan := do
  let some graph := CheckedWordFunctionDAG.ofParts? helpers entry |
    throw (IO.userError "call-graph loop fixture failed full Core typing")
  let some value := CheckedPlan.ofParts? graph mask |
    throw (IO.userError "call-graph loop fixture failed plan admission")
  return value

private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)
private def call (index : Nat) (argument : Wire.Expr) : Wire.Expr := .apply (.var index) argument
private def field (json : Json) (key : String) : IO Json := get (json.getObjVal? key)
private def string (json : Json) (key : String) : IO String := get (json.getObjValAs? String key)
private def natural (json : Json) (key : String) : IO Nat := get (json.getObjValAs? Nat key)
private def rows (json : Json) : IO (Array Json) := get (json.getObjValAs? (Array Json) "cases")

private def imported (value : CheckedPlan) (input : Word) : IO Json :=
  get (CallGraphLoop.emitCase value input (Json.mkObj [("kind", toJson "imported")]) 20000)

/-- All nine AST call shapes, iterated seven times by the mask. -/
private def mixedPlan (mask : Nat) : IO CheckedPlan := plan [
    .binary .wordAdd (.var 0) (word 1),
    .binary .wordMul (call 1 (.var 0)) (word 2),
    .binary .wordAdd (call 2 (.var 0)) (call 1 (.var 0))]
  (.letE (call 1 (.var 0))
    (.ifE (.binary .wordGt (call 4 (.var 1)) (word 1))
      (call 3 (.var 0))
      (call 4 (call 2 (.var 0))))) mask

private def coreAndImports : IO Json := do
  let value ← mixedPlan 7
  ensure (CallGraphLoop.callShapes value == Solcore.Synthesis.Core.CallGraph.callShapeCatalog)
    "mixed loop step no longer covers the exact ordered nine AST call shapes"
  -- Hand-iterated helpers: the step is x ↦ 6x + 8 for 0 < x < maximum.
  for (input, expected) in [(0, 0), (1, 14), (3, 992), (7, 2407448), (2 ^ 255, 2 ^ 255)] do
    let saved ← imported value (Word.ofNatModulo input)
    let observation ← field saved "directCore"
    ensure ((← string observation "status") == "returned" &&
      (← string observation "word") == toString expected) "bounded call-graph loop Core golden differs"
    ensure ((← get (CallGraphLoop.replayCase saved 20000)) == saved) "import replay changed a canonical case"
  let first ← imported value Word.zero
  for input in CallGraphLoop.boundaryInputs do
    let saved ← imported value input
    ensure ((← string saved "source") == (← string first "source"))
      "emitted source depends on its runtime argument"
    let admitted ← get (CallGraphLoop.caseProgram saved)
    ensure (admitted.program.check && (← field saved "loopPlan") == CallGraphLoop.planJson value)
      "applied loop lost typing or its canonical plan"
    let forged := saved.setObjVal! "directCore" (Json.mkObj [("status", toJson "invented")])
    ensure ((← get (CallGraphLoop.replayCase forged 20000)) == saved) "saved observation supplied the oracle"
    let suspended ← get (CallGraphLoop.replayCase saved 0)
    ensure ((← string (← field suspended "directCore") "status") == "out-of-fuel")
      "zero fuel was treated as a completed Core result"
  -- Imported cases may be constant or never iterate; exploration may not.
  let constant ← plan [word 7] (call 1 (word 7)) 7
  ensure ((← string (← field (← imported constant (Word.ofNatModulo 3)) "directCore") "word") == "7")
    "constant imported loop was incorrectly excluded"
  reject (CallGraphLoop.inputSensitive constant 20000) "constant step admitted as exploration"
  let deadCalls ← plan [.var 0, call 1 (.var 0)] (.binary .wordAdd (.var 0) (word 1)) 7
  reject (CallGraphLoop.inputSensitive deadCalls 20000) "dead helper-only calls passed exploration filter"
  let zeroMask ← mixedPlan 0
  ensure ((← string (← field (← imported zeroMask (Word.ofNatModulo 7)) "directCore") "word") == "7")
    "imported zero-mask loop did not return its input"
  reject (CallGraphLoop.inputSensitive zeroMask 20000) "zero-trip loop admitted as exploration"
  -- The step varies, but each positive trip returns its original input.
  let fixed ← plan [.var 0] (.ifE (.binary .wordGt (.var 0) (word 0)) (call 1 (.var 0)) (word 5)) 7
  reject (CallGraphLoop.inputSensitive fixed 20000) "unchanged positive-trip inputs passed exploration"
  reject (CallGraphLoop.inputSensitive value 0) "resource failure passed generation filter"
  let oversized := (List.range 200).foldl (fun body _ => .binary .wordAdd body (word 0)) (.var 0 : Wire.Expr)
  reject (CallGraphLoop.emitCase (← plan [oversized] (call 1 (.var 0)) 7) Word.zero
    (Json.mkObj [("kind", toJson "imported")]) 2000) "oversized loop escaped applied node budget"
  reject (CallGraphLoop.emitCase value Word.zero (Json.mkObj [("kind", toJson "imported")]) 10000001)
    "execution fuel above the profile limit accepted"
  return first

private def generationChecks : IO Json := do
  let corpus := CallGraphLoop.generateCases (Seed.ofNat 0) 256 13 128 100000
  ensure (corpus == CallGraphLoop.generateCases (Seed.ofNat 0) 256 13 128 100000)
    "bounded loop generation is not deterministic"
  ensure ((← string corpus "status") == "complete") "bounded generated corpus did not complete"
  let generated ← rows corpus
  let excluded ← get (corpus.getObjValAs? (Array Json) "excluded")
  ensure (generated.size == 13 && (← natural corpus "attempted") == 3 + excluded.size &&
    (← natural corpus "attempted") ≤ 128) "plan attempts and runtime cases were confused"
  for index in List.range generated.size do
    let saved := generated[index]!
    let admitted ← get (CallGraphLoop.caseProgram saved)
    let provenance ← field saved "provenance"
    let origin ← field provenance "origin"
    ensure (admitted.program.check && Wire.programNodes admitted.program ≤ 256 &&
      CallGraph.hasEntryCall admitted.plan.graph &&
      Solcore.Synthesis.Core.CallGraphLoop.generatedMasks.contains admitted.plan.mask)
      "generated case escaped typing, budget, entry-call or mask filter"
    ensure ((← natural origin "inputIndex") == index % 6 &&
      some admitted.input == CallGraphLoop.boundaryInputs[index % 6]?) "input bank order changed"
    ensure ((← natural origin "mask") == admitted.plan.mask &&
      (← natural origin "stepBudget") == 256 - BoundedLoop.appliedOverhead admitted.plan.mask)
      "generated origin lost its mask or measured step budget"
    let stepOrigin ← field origin "stepOrigin"
    ensure ((← string stepOrigin "kind") == "call-graph-generated" &&
      (← natural stepOrigin "maxProgramNodes") == (← natural origin "stepBudget"))
      "generated step provenance is not the scalar call-graph generator"
    ensure ((← get (CallGraphLoop.replayCase saved 100000)) == saved) "generated loop replay differs"
    ensure ((← string (← field (← get (CallGraphLoop.replayCase saved 0)) "directCore") "status") == "out-of-fuel")
      "new replay fuel was confused with stored generation validation fuel"
    if index % 6 > 0 then
      ensure ((← string saved "source") == (← string generated[index - index % 6]! "source"))
        "one generated plan emitted different sources across inputs"
  let truncated := CallGraphLoop.generateCases (Seed.ofNat 0) 256 3 1 100000
  ensure ((← rows truncated).size == 3 && (← natural truncated "attempted") == 1 &&
    (← string truncated "status") == "complete") "case count did not truncate a boundary group"
  let limited := CallGraphLoop.generateCases (Seed.ofNat 0) 256 7 1 100000
  ensure ((← rows limited).size == 6 && (← string limited "status") == "generation-exhausted")
    "attempt exhaustion was reported as complete"
  for budget in [38, 513] do
    let invalid := CallGraphLoop.generateCases (Seed.ofNat 0) budget 1 3 100000
    ensure ((← rows invalid).isEmpty && (← natural invalid "attempted") == 3 &&
      (← get (invalid.getObjValAs? (Array Json) "excluded")).size == 3)
      "invalid requested budget lost bounded exclusions"
  let resources := CallGraphLoop.generateCases (Seed.ofNat 0) 256 1 1 0
  let reasons ← get (resources.getObjValAs? (Array Json) "excluded")
  ensure ((← rows resources).isEmpty && (← string resources "status") == "generation-exhausted" &&
    (← string reasons[0]! "category") == "inconclusive-resource" &&
    (← string reasons[0]! "code") == "boundary-out-of-fuel") "fuel exclusion was treated as a pass"
  ensure ((← natural (CallGraphLoop.generateCases (Seed.ofNat 0) 256 0 100 100000) "attempted") == 0)
    "empty request consumed attempts"
  ensure ((← rows (CallGraphLoop.generateCases (Seed.ofNat 0) 256 1 0 100000)).isEmpty)
    "zero attempt limit was ignored"
  return corpus

private def tamperingChecks (saved : Json) : IO Unit := do
  let provenance ← field saved "provenance"
  let origin ← field provenance "origin"
  let withOrigin := fun changed => saved.setObjVal! "provenance" (provenance.setObjVal! "origin" changed)
  for name in ["profileVersion", "functionVersion", "loopVersion", "stepFunctionVersion",
      "aggregateVersion", "generatorVersion", "boundaryVersion", "stepBoundaryVersion",
      "callShapeVersion", "emitterVersion", "wrapperVersion"] do
    reject (CallGraphLoop.replayCase (saved.setObjVal! "provenance"
      (provenance.setObjVal! name (toJson "forged"))) 100000) s!"tampered version {name} accepted"
  let stepOrigin ← field origin "stepOrigin"
  for (name, value) in [("seed", toJson "00"), ("seed", toJson "1"),
      ("finalSeed", toJson "0"), ("maxProgramNodes", toJson (513 : Nat)),
      ("mask", toJson (0 : Nat)), ("stepBudget", toJson (1 : Nat)),
      ("stepOrigin", stepOrigin.setObjVal! "bodyBudgets" (toJson ([1] : List Nat))),
      ("inputIndex", toJson (6 : Nat)), ("validationFuel", toJson (10000001 : Nat)),
      ("kind", toJson "loop-generated"), ("extra", toJson true)] do
    reject (CallGraphLoop.replayCase (withOrigin (origin.setObjVal! name value)) 100000)
      s!"tampered generated {name} accepted"
  for (name, value) in [("helperCount", toJson (99 : Nat)),
      ("callShapes", toJson ["invented"]), ("features", toJson ([] : List String)),
      ("extra", toJson true)] do
    reject (CallGraphLoop.replayCase (saved.setObjVal! "provenance" (provenance.setObjVal! name value)) 100000)
      s!"tampered provenance {name} accepted"
  for (name, value) in [("input", toJson "01"), ("input", toJson "1"),
      ("source", toJson "forged"), ("schema", toJson "forged"),
      ("executionFuel", toJson (10000001 : Nat)), ("extra", toJson true)] do
    reject (CallGraphLoop.replayCase (saved.setObjVal! name value) 100000) s!"tampered envelope {name} accepted"
  let contract ← field saved "contract"
  for (name, value) in [("calldata", toJson "0xa444f5e9"), ("constructorCalldata", toJson "0x00"),
      ("name", toJson "SynthesizedLoops"), ("runtimePath", toJson ["Other"]), ("extra", toJson true)] do
    reject (CallGraphLoop.replayCase (saved.setObjVal! "contract" (contract.setObjVal! name value)) 100000)
      "tampered ABI/contract envelope accepted"
  let loopPlan ← field saved "loopPlan"
  let mask ← natural loopPlan "mask"
  for (name, value) in [("schema", toJson "solcore-lean.loop-plan.v1"),
      ("mask", toJson (if mask == 7 then 3 else 7 : Nat)), ("mask", toJson (2 : Nat)),
      ("extra", toJson true)] do
    reject (CallGraphLoop.replayCase (saved.setObjVal! "loopPlan" (loopPlan.setObjVal! name value)) 100000)
      s!"tampered loop plan {name} accepted"
  let program ← field saved "program"
  reject (CallGraphLoop.caseProgram (saved.setObjVal! "program" (program.setObjVal! "extra" (toJson true))))
    "extra Core wire field accepted"
  let admitted ← get (CallGraphLoop.caseProgram saved)
  reject (CallGraphLoop.caseProgram (saved.setObjVal! "program"
    (Wire.encodeProgram admitted.plan.graph.program))) "scalar graph program replaced the loop reference"
  let aggregate : Wire.Program := {
    resultType := .function .word .word, dataDefinitions := []
    body := functionDAGExpression [.first (.pair (.var 0) (word 1))] (call 1 (.var 0))}
  reject (CallGraphLoop.checkedPlan (loopPlan.setObjVal! "stepProgram" (Wire.encodeProgram aggregate)))
    "aggregate step admitted as a scalar call graph"

private def shrinkingChecks (saved : Json) : IO Unit := do
  let source ← get (CallGraphLoop.caseProgram saved)
  let first ← get (CallGraphLoop.shrinkCases saved 64 20000)
  ensure (first == (← get (CallGraphLoop.shrinkCases saved 64 20000))) "shrinking is nondeterministic"
  let candidates ← rows first
  ensure (!candidates.isEmpty && candidates.size ≤ 64) "bounded shrink yielded no candidates"
  for candidate in candidates do
    let admitted ← get (CallGraphLoop.caseProgram candidate)
    ensure (admitted.program.check &&
      admitted.plan.graph.helpers.length == source.plan.graph.helpers.length &&
      admitted.plan.mask ≤ source.plan.mask &&
      (complexity admitted.program.body).isStrictlySmaller (complexity source.program.body))
      "shrinking lost full typing, helper count, mask bound or strict measure"
    ensure ((← get (CallGraphLoop.replayCase candidate 20000)) == candidate) "reduced case failed exact replay"
  let masks := ((CallGraphLoop.reductions source).map (·.candidate.plan.mask)).eraseDups
  ensure (masks.contains 0 && masks.contains 1 && masks.contains 3 && masks.contains 7)
    "mask reductions or unchanged-mask step reductions were not offered"
  let unchangedOrigin := Json.mkObj [("kind", toJson "reduced"),
    ("parentPlan", CallGraphLoop.planJson source.plan), ("parentInput", toJson (toString source.input.val))]
  let unchanged ← get (CallGraphLoop.emitCase source.plan source.input unchangedOrigin 20000)
  reject (CallGraphLoop.replayCase unchanged 20000) "non-strict self reduction accepted"
  let smaller ← plan [.var 0] (call 1 (.var 0)) 1
  let wrongCount ← get (CallGraphLoop.emitCase smaller Word.zero unchangedOrigin 20000)
  reject (CallGraphLoop.replayCase wrongCount 20000) "reduction changed helper declarations"
  let lowerMask ← mixedPlan 1
  let lowerOrigin := unchangedOrigin.setObjVal! "parentPlan" (CallGraphLoop.planJson lowerMask)
  let raised ← get (CallGraphLoop.emitCase source.plan Word.zero lowerOrigin 20000)
  reject (CallGraphLoop.replayCase raised 20000) "reduction increased its loop mask"
  let reduced := candidates[0]!
  let provenance ← field reduced "provenance"
  let origin ← field provenance "origin"
  for (key, value) in [("parentInput", toJson "01"), ("parentInput", toJson (toString (2 ^ 256))),
      ("parentPlan", Json.null), ("parentProgram", Json.null), ("extra", toJson true)] do
    reject (CallGraphLoop.replayCase (reduced.setObjVal! "provenance"
      (provenance.setObjVal! "origin" (origin.setObjVal! key value))) 20000)
      "invalid reduced parent provenance accepted"

def testSourceCallGraphLoopCases : IO Unit := do
  let importedCase ← coreAndImports
  let corpus ← generationChecks
  tamperingChecks (← rows corpus)[0]!
  ensure ((← string importedCase "input") == "0") "first imported case changed input"
  shrinkingChecks (← imported (← mixedPlan 7) (Word.ofNatModulo 7))

end Tests.SourceCallGraphLoopCases
end

section
-- leanmerge: from Solcore.Test.SourceCallGraphLoopCorpus
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
end

section
-- leanmerge: from Solcore.Test.SourceCallGraphLoopEmitter
/-! Plan sealing, measured generation and exact source shape for bounded loops
over scalar call graphs. Only original Core programs are executed here; these
tests neither run emitted source nor prove compiler meaning preservation. -/
set_option autoImplicit false

namespace Tests.SourceCallGraphLoopEmitter
open Solcore.Core Solcore.Synthesis.Core Solcore.Synthesis.Source
open Solcore.Synthesis.Core.CallGraphLoop (CheckedPlan)

private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)
private def call (index : Nat) (argument : Wire.Expr) : Wire.Expr := .apply (.var index) argument
private def maximum : Nat := Word.maximum.val
private def high : Nat := 2 ^ 255

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def graph (helpers : List Wire.Expr) (entry : Wire.Expr) : IO CheckedWordFunctionDAG :=
  match CheckedWordFunctionDAG.ofParts? helpers entry with
  | some value => pure value
  | none => throw (IO.userError "call graph fixture failed checked admission")

private def plan (function : CheckedWordFunctionDAG) (mask : Nat) : IO CheckedPlan :=
  match CheckedPlan.ofParts? function mask with
  | some value => pure value
  | none => throw (IO.userError "call-graph loop fixture failed plan admission")

private def emitted (value : CheckedPlan) : IO EmittedProgram :=
  match CallGraphLoop.emit value with
  | .ok source => pure source
  | .error error => throw (IO.userError s!"call-graph loop emission failed: {reprStr error}")

private def run (program : Wire.Program) : IO Word := do
  ensure program.check "applied Core program failed its checker"
  match program.toCore.runStateful 100000 with
  | .done (.word value) _ => pure value
  | _ => throw (IO.userError "original Core program did not return a Word")

private def observe (value : CheckedPlan) (input expected : Nat) : IO Unit := do
  let result ← run (value.instantiate (Word.ofNatModulo input))
  ensure (result.val == expected) s!"call-graph loop result {result.val} differs from {expected}"

/-- The finite ordinal reference must agree with repeated scalar applications
of the same graph. Both sides are original Core executions. -/
private def iterated (value : CheckedPlan) (input : Word) : IO Unit := do
  let mut accumulator := input
  for _ in List.range (input.bitAnd (Word.ofNatModulo value.mask)).val do
    accumulator ← run (value.graph.instantiate accumulator)
  ensure ((← run (value.instantiate input)) == accumulator)
    "bounded loop reference differs from repeated scalar graph applications"

private def sealingChecks : IO Unit := do
  let doubled ← graph [.binary .wordAdd (.var 0) (word 1)] (call 1 (.binary .wordMul (.var 0) (word 2)))
  let checked ← plan doubled 7
  ensure (Wire.encodeProgram checked.loop.step.program == Wire.encodeProgram checked.graph.program)
    "executed loop step differs from the scalar graph"
  ensure (Wire.encodeProgram checked.program ==
    Wire.encodeProgram (BoundedLoop.canonicalProgram checked.loop.step 7)) "plan is not the canonical loop"
  ensure (checked.program.check && checked.mask == 7) "sealed plan lost typing or mask"
  -- 2x + 1 for exactly input & 7 iterations; the maximum Word is a fixed point.
  for (input, expected) in [(0, 0), (1, 3), (3, 31), (7, 1023), (maximum, maximum), (high, high)] do
    observe checked input expected
  for mask in [2, 4, 5, 8, 15] do
    ensure (CheckedPlan.ofParts? doubled mask).isNone "loop plan admitted an unsupported mask"
  let three ← plan doubled 3
  match CheckedPlan.ofProgram? doubled.program 3 with
  | some restored =>
      ensure (Wire.encodeProgram restored.program == Wire.encodeProgram three.program)
        "program readmission changed the plan"
  | none => throw (IO.userError "scalar graph program was not readmitted")
  let aggregate : Wire.Program := {
    resultType := .function .word .word, dataDefinitions := []
    body := functionDAGExpression [.first (.pair (.var 0) (word 1))] (call 1 (.var 0))}
  ensure (CheckedPlan.ofProgram? aggregate 1).isNone "aggregate step escaped the scalar call graph"
  -- Raw shifts keep Core operand order through the loop: ((2x) >> 4) three times.
  let shifted ← plan (← graph [.binary .wordShl (.var 0) (word 1)]
    (.binary .wordShr (call 1 (.var 0)) (word 4))) 3
  observe shifted 0xF003 120
  observe shifted 257 32
  for input in [0, 1, 3, 7, 0xF003, maximum, high] do
    iterated shifted (Word.ofNatModulo input)
    iterated checked (Word.ofNatModulo input)

private def generationChecks : IO Unit := do
  let mut masks : List Nat := []
  for seed in List.range 64 do
    let request : CallGraphLoop.Request := {seed := Seed.ofNat seed, maxProgramNodes := 256}
    match CallGraphLoop.generate request with
    | .error error => throw (IO.userError s!"bounded loop generation failed: {reprStr error}")
    | .ok generated =>
        let value := generated.plan
        ensure (CallGraphLoop.generatedMasks.contains value.mask) "generated an imported-only mask"
        masks := (masks ++ [value.mask]).eraseDups
        let overhead := BoundedLoop.appliedOverhead value.mask
        ensure (generated.stepBudget == 256 - overhead && generated.step.maxProgramNodes == generated.stepBudget)
          "step budget did not subtract the measured loop overhead"
        ensure (generated.nodeCount == Wire.programNodes (value.graph.instantiate Word.zero) + overhead &&
          generated.nodeCount ≤ 256) "measured loop overhead or complete budget differs"
        ensure (Wire.encodeProgram value.graph.program == Wire.encodeProgram generated.step.function.program)
          "plan graph differs from its generated step"
        match CallGraphLoop.generate request with
        | .ok again => ensure (Wire.encodeProgram again.plan.program == Wire.encodeProgram value.program &&
            again.finalSeed == generated.finalSeed) "bounded loop generation is not deterministic"
        | .error _ => throw (IO.userError "repeated generation failed")
        for input in [0, 1, 3, 7, maximum, high] do
          iterated value (Word.ofNatModulo input)
  ensure (masks.length == 3) "consecutive seeds did not select all generated masks"
  ensure (CallGraphLoop.generate {seed := Seed.ofNat 0, maxProgramNodes := 513} matches .error .budgetTooLarge)
    "oversized loop budget accepted"
  ensure (CallGraphLoop.generate {seed := Seed.ofNat 0, maxProgramNodes := 38} matches .error .budgetTooSmall)
    "loop budget below every generated mask accepted"
  ensure (CallGraphLoop.minimumAppliedNodes 1 == 39 && CallGraphLoop.minimumAppliedNodes 7 == 111)
    "measured minimum loop programs changed"

private def sourceChecks : IO Unit := do
  let identity ← plan (← graph [.var 0] (call 1 (.var 0))) 1
  let source ← emitted identity
  ensure (source == (← emitted identity)) "call-graph loop emission is nondeterministic"
  ensure (source.contractName == "SynthesizedCallGraphLoops" && source.methodName == "run" &&
    source.methodSignature == "run(uint256)" && source.deployPath == ["SynthesizedCallGraphLoopsDeploy"] &&
    source.runtimePath == ["SynthesizedCallGraphLoopsDeploy", "SynthesizedCallGraphLoops"])
    "call-graph loop wrapper metadata changed"
  ensure (CallGraphLoop.emitterVersion == "solcore-source-call-graph-loops-v2" &&
    CallGraphLoop.wrapperVersion == "solcore-word-call-graph-loops-contract-v1" &&
    CallGraphLoop.selector == "0xa444f5e9") "call-graph loop versions or ABI selector changed"
  ensure (source.source == String.intercalate "\n" [
    "pragma solcore;", "import * from std;", "import * from std.dispatch;",
    Primitive.opcodeImport, "",
    "function sc_fn0(sc_arg: word) returns (word) {", "    return sc_arg;", "}", "",
    "function sc_step(sc_arg: word) returns (word) {", "    let sc_v0: word = sc_arg;",
    "    let sc_v1: word = sc_fn0(sc_v0);", "    return sc_v1;", "}", "",
    "contract SynthesizedCallGraphLoops {",
    "    function run(input: uint256) public returns (uint256) {",
    "        let sc_input: word = Typedef.rep(input);",
    "        let sc_limit: word = (sc_input & 1);",
    "        let sc_acc: word = sc_input;",
    "        let sc_counter: word = 0;",
    "        while (sc_limit > sc_counter) {",
    "            sc_acc = sc_step(sc_acc);",
    "            sc_counter = (sc_counter + 1);",
    "        }",
    "        return uint256(sc_acc);", "    }", "}", ""])
    "named helper, sc_step or bounded while wrapper changed"
  -- Helpers and the entry use the call-graph renderer, including raw aliases.
  let shifted ← plan (← graph [.binary .wordShl (.var 0) (word 1)]
    (.binary .wordShr (call 1 (.var 0)) (word 4))) 3
  let text := (← emitted shifted).source
  let helper ← match CallGraphRenderer.renderWithFunctions [] .word ["sc_arg"] 4 0
      (.binary .wordShl (.var 0) (word 1)) with
    | .ok value => pure value
    | .error _ => throw (IO.userError "helper rendering failed")
  let step ← match CallGraphRenderer.renderWithFunctions ["sc_fn0"] .word ["sc_arg"] 4 0
      (.binary .wordShr (call 1 (.var 0)) (word 4)) with
    | .ok value => pure value
    | .error _ => throw (IO.userError "step rendering failed")
  let expectedPrefix := String.intercalate "\n" ([
    "pragma solcore;", "import * from std;", "import * from std.dispatch;",
    Primitive.opcodeImport, "",
    "function sc_fn0(sc_arg: word) returns (word) {"] ++ helper.lines ++
    ["    return " ++ helper.value ++ ";", "}", "", "function sc_step(sc_arg: word) returns (word) {"] ++
    step.lines ++ ["    return " ++ step.value ++ ";", "}", "", "contract SynthesizedCallGraphLoops {"])
  ensure (text.startsWith expectedPrefix && (text.splitOn "sc_shl(").length == 2 &&
    (text.splitOn "sc_shr(").length == 2 && (text.splitOn "(sc_input & 3);").length == 2)
    "helpers or step were not emitted by the call-graph renderer with raw aliases"
  -- The older aggregate loop emitter remains a separate, unchanged printer.
  let some legacy := Aggregates.CheckedDAG.ofParts? [.var 0] (call 1 (.var 0)) |
    throw (IO.userError "legacy loop step fixture failed")
  let some legacyPlan := BoundedLoop.CheckedPlan.ofParts? legacy 1 |
    throw (IO.userError "legacy loop plan fixture failed")
  match Loop.emit legacyPlan with
  | .ok legacySource =>
      ensure (legacySource.contractName == "SynthesizedLoops" &&
        (legacySource.source.splitOn Primitive.opcodeImport).length == 1)
        "legacy loop emitter changed contract or gained raw primitive imports"
  | .error _ => throw (IO.userError "legacy loop emitter rejected its fixture")

def testSourceCallGraphLoopEmitter : IO Unit := do
  sealingChecks
  generationChecks
  sourceChecks

end Tests.SourceCallGraphLoopEmitter
end

section
-- leanmerge: from Solcore.Test.SourceNestedCallCases
/-! Goldens consume only the real nested scheduler. Expected values below are
regression fixtures, never inputs to generation, replay, shrinking or execution. -/
set_option autoImplicit false

namespace Tests.SourceNestedCallCases
open Lean Solcore.Core Solcore.Synthesis.Core Solcore.Synthesis.Source
open Solcore.Synthesis.Core.NestedCall (CheckedPlan)
open Solcore.Synthesis.Stateful.NestedCallExecution (Transaction Bindings)

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
private def w := Word.ofNatModulo
private def word (value : Nat) : Wire.Expr := .word (w value)
private def entry : Wire.Expr := .apply (.var 1) (.var 0)
private def bindings : Bindings := ⟨⟨17, by decide⟩, ⟨101, by decide⟩, ⟨102, by decide⟩⟩
private def makePlan (body : Wire.Expr) (result : Wire.Expr := entry) : IO CheckedPlan := do
  let some graph := Aggregates.CheckedDAG.ofParts? [body] result |
    throw (IO.userError "call fixture failed step admission")
  let some plan := CheckedPlan.ofStep? graph | throw (IO.userError "call wrappers failed host admission")
  return plan
private def transactions (inputs : List Word) : List Transaction :=
  inputs.zipIdx.map fun (input, index) => ⟨"call-" ++ toString index, input⟩
private def scenario (plan : CheckedPlan) (inputs : List Word) : IO Solcore.Synthesis.Source.NestedCall.CheckedScenario :=
  get (Solcore.Synthesis.Source.NestedCall.checkedScenario plan (transactions inputs))
private def imported (value : Solcore.Synthesis.Source.NestedCall.CheckedScenario) (fuel : Nat := 20000) : IO Json :=
  get (Solcore.Synthesis.Source.NestedCall.emitCase value (Json.mkObj [("kind", toJson "imported")]) fuel)
private def encoded (value : Word) : String := Solcore.ContractRuntime.encodeBytesText
  (Solcore.ContractRuntime.encodeWordBytesBE value)
private def account (role : String) (address : Nat) (balance first second : Word) : Json := Json.mkObj [
  ("role", toJson role), ("address", toJson (toString address)), ("balance", toJson (toString balance.val)),
  ("storage", toJson ([Json.mkObj [("slot", toJson "0"), ("value", toJson (toString first.val))],
    Json.mkObj [("slot", toJson "1"), ("value", toJson (toString second.val))]]))]
private def accounts (p0 p1 c0 c1 : Word) (pb : Nat := 8) (cb : Nat := 0) : Json := toJson [
  account "parent" 101 (w pb) p0 p1, account "child" 102 (w cb) c0 c1]
private def logs (values : List (Nat × Nat × Word)) : Json := toJson (values.map fun (address, topic, value) =>
  Json.mkObj [("address", toJson (toString address)), ("topics", toJson [toString topic]), ("data", toJson (encoded value))])
private def committed (p0 p1 c0 : Nat) : Json := logs [(101, 1, w p0), (102, 2, w c0), (101, 3, w p1)]
private def childReverted (p0 p1 : Nat) : Json := logs [(101, 1, w p0), (101, 3, w p1)]
private def emptyAccounts : Json := accounts Word.zero Word.zero Word.zero Word.zero
private def emptyLogs : Json := logs []

private def checkHistory (value : Solcore.Synthesis.Source.NestedCall.CheckedScenario)
    (expected : List (String × Word × Json × Json)) : IO Json := do
  let observed := Solcore.Synthesis.Source.NestedCall.observe value bindings 20000
  ensure ((← string observed "status") == "complete" && (← field observed "initialAccounts") == emptyAccounts)
    "nested fixture did not start fresh and complete"
  let result ← rows observed
  ensure (result.size == expected.length && result.size == value.transactions.length) "nested transaction count changed"
  for ((status, output, state, events), index) in expected.zipIdx do
    let row := result[index]!
    ensure (some (← string row "id") == (value.transactions[index]?).map (·.id) &&
      (← natural row "index") == index) "stable transaction identity changed"
    ensure ((← string row "status") == status && (← string row "output") == encoded output)
      "nested root outcome/payload differs from golden"
    ensure ((← field row "committedAccounts") == state) "nested committed accounts differ from golden"
    ensure ((← field row "logs") == events) "nested log rollback/order differs from golden"
  ensure ((← field observed "finalAccounts") == (← field result[result.size - 1]! "committedAccounts") &&
    (← rows observed "unexecuted").isEmpty && (← field observed "stoppedAt") == Json.null)
    "nested final history metadata differs from committed prefixes"
  ensure (Solcore.Synthesis.Source.NestedCall.observe value bindings 20000 == observed) "observer reused a previous world"
  return observed

private def referenceChecks : IO Json := do
  let identity ← makePlan (.var 0)
  let singles : List (Nat × String × Nat × Json × Json) := [
    (0, "returned", 0, accounts (w 0) (w 0) (w 0) (w 1), committed 0 0 0),
    (1, "returned", 3, accounts (w 1) (w 2) (w 0) (w 0), childReverted 1 2),
    (2, "reverted", 4, emptyAccounts, emptyLogs),
    (3, "reverted", 7, emptyAccounts, emptyLogs),
    (4, "returned", 8, accounts (w 4) (w 4) (w 4) (w 1) 7 1, committed 4 4 4),
    (5, "returned", 11, accounts (w 5) (w 6) (w 0) (w 0), childReverted 5 6),
    (6, "reverted", 12, emptyAccounts, emptyLogs),
    (7, "reverted", 15, emptyAccounts, emptyLogs)]
  for (input, status, output, state, events) in singles do
    let _ ← checkHistory (← scenario identity [w input]) [(status, w output, state, events)]
  let _ ← checkHistory (← scenario identity [Word.maximum]) [("reverted", Word.maximum, emptyAccounts, emptyLogs)]
  let high := w (2 ^ 255)
  let _ ← checkHistory (← scenario identity [high]) [("returned", Word.zero,
    accounts high high high (w 1), logs [(101, 1, high), (102, 2, high), (101, 3, high)])]
  let mixed ← scenario identity ([4, 5, 4].map w)
  let history ← checkHistory mixed [
    ("returned", w 8, accounts (w 4) (w 4) (w 4) (w 1) 7 1, committed 4 4 4),
    ("returned", w 19, accounts (w 9) (w 10) (w 4) (w 1) 7 1, childReverted 9 10),
    ("returned", w 21, accounts (w 13) (w 8) (w 8) (w 2) 6 2, committed 13 8 8)]
  let _ ← checkHistory (← scenario identity ([4, 6, 0].map w)) [
    ("returned", w 8, accounts (w 4) (w 4) (w 4) (w 1) 7 1, committed 4 4 4),
    ("reverted", w 20, accounts (w 4) (w 4) (w 4) (w 1) 7 1, emptyLogs),
    ("returned", w 8, accounts (w 4) (w 4) (w 4) (w 2) 7 1, committed 4 4 4)]
  -- The same helper's fresh private cell is reset on each successful child call.
  let privateStep := Wire.Expr.letE (.newCell .word (word 0))
    (.letE (.storeCell (.var 0) (.binary .wordAdd (.loadCell (.var 0)) (word 2)))
      (.binary .wordAdd (.var 2) (.loadCell (.var 1))))
  let mutablePlan ← makePlan privateStep (.binary .wordSub entry (word 1))
  let _ ← checkHistory (← scenario mutablePlan ([0, 1, 0].map w)) [
    ("returned", w 1, accounts (w 0) (w 1) (w 1) (w 1), committed 0 1 1),
    ("returned", w 5, accounts (w 1) (w 4) (w 1) (w 1), childReverted 1 4),
    ("returned", w 3, accounts (w 1) (w 2) (w 2) (w 2), committed 1 2 2)]
  let changedBindings : Bindings := ⟨⟨33, by decide⟩, ⟨201, by decide⟩, ⟨202, by decide⟩⟩
  let relocated := Solcore.Synthesis.Source.NestedCall.observe mixed changedBindings 20000
  let originalRows ← rows history
  let relocatedRows ← rows relocated
  for index in List.range originalRows.size do
    ensure ((← string originalRows[index]! "output") == (← string relocatedRows[index]! "output"))
      "call payload depended on fixture addresses"
    let accountRows ← rows relocatedRows[index]! "committedAccounts"
    ensure ((← string accountRows[0]! "address") == "201" && (← string accountRows[1]! "address") == "202" &&
        Solcore.Synthesis.Stateful.AccountStorage.boundTo relocatedRows[index]! [201, 202])
      "observer did not use actual role bindings"
  let input := Solcore.Synthesis.Stateful.NestedCallExecution.inputData bindings (w 4)
  ensure (input.bytes.size == 68 && input.wordBE? (w 4) == some (w 102) &&
    input.wordBE? (w 36) == some (w 4)) "parent ABI did not bind exact child/input words"
  ensure (identity.parentProgram.check && identity.childProgram.check &&
    identity.parentProgram.resultType == .sum .word (.sum .word .word) &&
    identity.childProgram.resultType == .sum .word (.sum .word .word)) "both contracts must retain outcomeV1 admission"
  let saved ← imported mixed
  ensure ((← get (Solcore.Synthesis.Source.NestedCall.replayCase saved 20000)) == saved) "imported call case did not replay"
  ensure ((← get (Solcore.Synthesis.Source.NestedCall.replayCase (saved.setObjVal! "directCore" (toJson "forged")) 20000)) == saved)
    "replay consumed a stored expected result"
  let changed ← imported (← scenario identity ([1, 2, 3].map w))
  ensure ((← field saved "programs") == (← field changed "programs") && (← string saved "source") == (← string changed "source"))
    "runtime inputs leaked into the original code or emitted source"
  return saved

private def resourceChecks : IO Unit := do
  let slow := (List.range 20).foldl (fun body _ => Wire.Expr.letE (word 1) body) (word 8)
  let plan ← makePlan (.ifE (.binary .wordEq (.var 0) (word 8)) slow (.var 0))
  let value ← scenario plan ([4, 5, 4].map w)
  let low := Solcore.Synthesis.Source.NestedCall.observe value bindings 0
  let first := (← rows low)[0]!
  ensure ((← string low "status") == "incomplete" && (← string first "status") == "out-of-fuel" &&
    (← field first "logs") == Json.null && (← rows low "unexecuted").size == 2 &&
    (← field low "finalAccounts") == emptyAccounts) "exhausted nested state/logs were committed"
  let mut afterPrefixes := false
  for fuel in List.range 700 do
    let observed := Solcore.Synthesis.Source.NestedCall.observe value bindings fuel
    let result ← rows observed
    if result.size == 3 then
      if (← string result[2]! "status") == "out-of-fuel" then
        afterPrefixes := true
        ensure ((← field result[2]! "logs") == Json.null &&
          (← field result[2]! "committedAccounts") == (← field result[1]! "committedAccounts") &&
          (← field observed "finalAccounts") == accounts (w 9) (w 10) (w 4) (w 1) 7 1)
          "nested fuel exhaustion after completed prefixes changed committed state"
  ensure afterPrefixes "resource regression did not retain a completed child-rollback prefix"

private def generationChecks : IO Json := do
  for seed in List.range 12 do
    let mut minimum : Option Nat := none
    for budget in List.range 513 do
      if minimum.isNone && (Solcore.Synthesis.Source.NestedCall.generatedScenario (Seed.ofNat seed) budget).isOk then minimum := some budget
    let some budget := minimum | throw (IO.userError "call template does not fit 512-node budget")
    let (value, _) ← get (Solcore.Synthesis.Source.NestedCall.generatedScenario (Seed.ofNat seed) budget)
    ensure (Solcore.Synthesis.Core.NestedCall.combinedNodes value.plan.step ≤ budget && value.transactions.length == 3 &&
      value.plan.step.helpers.length == 1 + seed % 3) "call recipe lost full node/transaction/helper bounds"
    rejected (Solcore.Synthesis.Source.NestedCall.generatedScenario (Seed.ofNat seed) (budget - 1)) "undersized node budget accepted"
  rejected (Solcore.Synthesis.Source.NestedCall.generatedScenario (Seed.ofNat 0) 513) "oversized node budget accepted"
  let corpus := Solcore.Synthesis.Source.NestedCall.generateCases (Seed.ofNat 0) 384 4 256 20000
  ensure (corpus == Solcore.Synthesis.Source.NestedCall.generateCases (Seed.ofNat 0) 384 4 256 20000) "call generation nondeterministic"
  let generated ← rows corpus "cases"
  ensure (generated.size == 4 && (← natural corpus "attempted") ≤ 256)
    "call count does not count complete scenarios"
  for saved in generated do
    let value ← get (Solcore.Synthesis.Source.NestedCall.caseProgram saved)

    ensure (value.transactions.length == 3 && Solcore.Synthesis.Core.NestedCall.combinedNodes value.plan.step ≤ 384)
      "generated case escaped bounded call profile"
    ensure ((← get (Solcore.Synthesis.Source.NestedCall.replayCase saved 20000)) == saved) "generated history provenance did not replay"
    let low ← get (Solcore.Synthesis.Source.NestedCall.replayCase saved 0)
    ensure ((← natural low "executionFuel") == 0 && (← field low "provenance") == (← field saved "provenance"))
      "fresh replay fuel changed the generation validation budget"
  let saved := generated[0]!
  let origin ← field (← field saved "provenance") "origin"
  let some seed := (← string origin "seed").toNat? | throw (IO.userError "invalid generated seed")
  let low := Solcore.Synthesis.Source.NestedCall.generateCases (Seed.ofNat seed) 384 1 1 0
  let excluded ← rows low "excluded"
  ensure ((← rows low "cases").isEmpty && (← string excluded[0]! "category") == "inconclusive-resource")
    "call generation resource exhaustion was not distinguished"
  ensure ((← rows (Solcore.Synthesis.Source.NestedCall.generateCases (Seed.ofNat seed) 384 2 1 20000) "cases").size == 1 &&
    (← natural (Solcore.Synthesis.Source.NestedCall.generateCases (Seed.ofNat seed) 384 0 10 20000) "attempted") == 0 &&
    (← rows (Solcore.Synthesis.Source.NestedCall.generateCases (Seed.ofNat seed) 384 1 0 20000) "cases").isEmpty)
    "call generator ignored count/attempt bounds"
  return saved

private def tamperingChecks (saved generated : Json) : IO Unit := do
  let transactionRows ← rows saved
  let first := transactionRows[0]!
  for (name, bad) in [("id", toJson ""), ("id", toJson "not valid"),
      ("id", toJson (String.ofList (List.replicate 65 'a'))), ("input", toJson "01"),
      ("target", toJson "child"), ("callee", toJson "parent"), ("value", toJson "1"),
      ("extra", toJson true)] do
    rejected (Solcore.Synthesis.Source.NestedCall.decodeTransactions (toJson [first.setObjVal! name bad]))
      "noncanonical call transaction accepted"
  rejected (Solcore.Synthesis.Source.NestedCall.decodeTransactions (toJson [first, first])) "duplicate transaction IDs accepted"
  rejected (Solcore.Synthesis.Source.NestedCall.decodeTransactions (toJson ([] : List Json))) "empty transaction list accepted"
  rejected (Solcore.Synthesis.Source.NestedCall.decodeTransactions
    (toJson (List.replicate (Solcore.Synthesis.Stateful.Sequence.maxTransactions + 1) first)))
    "unbounded transaction count accepted"
  for (name, bad) in [("initialState", Json.mkObj [("call", toJson [first])]),
      ("observedSlots", toJson (["1", "0"] : List String)), ("executionFuel", toJson (10000001 : Nat)),
      ("programs", Json.mkObj [])] do
    rejected (Solcore.Synthesis.Source.NestedCall.caseProgram (saved.setObjVal! name bad)) "invalid call case boundary accepted"
  let programs ← field saved "programs"
  for name in ["parent", "child"] do
    let other ← field programs (if name == "parent" then "child" else "parent")
    rejected (Solcore.Synthesis.Source.NestedCall.caseProgram
      (saved.setObjVal! "programs" (programs.setObjVal! name other)))
      "a different fully checked contract replaced a canonical program"
  let provenance ← field generated "provenance"
  let origin ← field provenance "origin"
  let withOrigin := fun changed => generated.setObjVal! "provenance" (provenance.setObjVal! "origin" changed)
  for name in ["generatorVersion", "profileVersion", "functionVersion", "templateVersion", "stepProfileVersion",
      "stepFunctionVersion", "stepTemplateVersion", "emitterVersion", "wrapperVersion", "features"] do
    rejected (Solcore.Synthesis.Source.NestedCall.replayCase (generated.setObjVal! "provenance" (provenance.setObjVal! name Json.null)) 20000)
      "tampered call provenance accepted"
  for (name, bad) in [("seed", toJson "00"), ("finalSeed", toJson "bad"),
      ("maxProgramNodes", toJson (513 : Nat)), ("stepOrigin", Json.null), ("sequenceIndices", Json.null),
      ("validationFuel", toJson (10000001 : Nat)), ("validationFuel", toJson (0 : Nat))] do
    rejected (Solcore.Synthesis.Source.NestedCall.replayCase (withOrigin (origin.setObjVal! name bad)) 20000)
      "tampered generated call recipe accepted"
  let plan ← field saved "callPlan"
  rejected (Solcore.Synthesis.Source.NestedCall.checkedPlan (plan.setObjVal! "extra" Json.null)) "noncanonical call plan accepted"
  rejected (Solcore.Synthesis.Source.NestedCall.replayCase (saved.setObjVal! "source" (toJson "stale")) 20000) "stale source accepted"
  let contract ← field saved "contracts"
  for role in ["parent", "child"] do
    let metadata ← field contract role
    for (name, wrong) in [("constructorValue", toJson "1"), ("selector", toJson "0x00000000")] do
      rejected (Solcore.Synthesis.Source.NestedCall.replayCase
        (saved.setObjVal! "contracts" (contract.setObjVal! role (metadata.setObjVal! name wrong))) 20000)
        "wrong call constructor or ABI metadata accepted"
  let bindingJson := Solcore.Synthesis.Stateful.NestedCallExecution.bindingsJson bindings
  ensure ((Solcore.Synthesis.Stateful.NestedCallExecution.decodeBindings bindingJson).isOk) "valid bindings rejected"
  for (name, value) in [("caller", "017"), ("parent", "17"), ("child", "101"),
      ("parent", "9"), ("child", "0"), ("parent", "10"), ("child", "10"),
      ("child", "17"), ("parent", "256"), ("child", "256"), ("caller", toString (2 ^ 160))] do
    rejected (Solcore.Synthesis.Stateful.NestedCallExecution.decodeBindings (bindingJson.setObjVal! name (toJson value)))
      "invalid execution bindings accepted"

private def shrinkChecks : IO Unit := do
  let plan ← makePlan (Aggregate.template 3 (word 2))
  let value ← scenario plan [Word.maximum, w 7, Word.maximum]
  let saved ← imported value
  let candidates ← get (Solcore.Synthesis.Source.NestedCall.shrinkCases saved 1000 20000)
  let result ← rows candidates "cases"
  ensure (!result.isEmpty && candidates == (← get (Solcore.Synthesis.Source.NestedCall.shrinkCases saved 1000 20000)))
    "call reductions were empty or nondeterministic"
  let mut removed := false
  let mut loweredInput := false
  let mut changedStep := false
  let mut seen : List String := []
  for row in result do
    let reduced ← get (Solcore.Synthesis.Source.NestedCall.caseProgram row)
    ensure (decide (Solcore.Synthesis.Source.NestedCall.StrictlySmaller reduced value) && reduced.plan.parentProgram.check && reduced.plan.childProgram.check &&
      reduced.plan.step.helpers.length == value.plan.step.helpers.length &&
      Aggregate.bindingInventory reduced.plan.step == Aggregate.bindingInventory value.plan.step &&
      decide ((reduced.transactions.map (·.id)).Sublist (value.transactions.map (·.id))))
      "call reduction lost strict complexity, host typing or stable scope/IDs"
    let key := (Json.mkObj [("programs", Solcore.Synthesis.Source.NestedCall.programsJson reduced.plan),
      ("transactions", Solcore.Synthesis.Source.NestedCall.transactionsJson reduced.transactions)]).compress
    ensure (!seen.contains key) "duplicate call reduction"
    seen := key :: seen
    removed := removed || reduced.transactions.length < value.transactions.length
    loweredInput := loweredInput || (reduced.transactions.length == value.transactions.length &&
      Solcore.Synthesis.Source.NestedCall.inputWeight reduced < Solcore.Synthesis.Source.NestedCall.inputWeight value)
    changedStep := changedStep || Solcore.Synthesis.Source.NestedCall.programsJson reduced.plan != Solcore.Synthesis.Source.NestedCall.programsJson value.plan
    ensure ((← get (Solcore.Synthesis.Source.NestedCall.replayCase row 20000)) == row) "reduced call case did not replay"
  ensure (removed && loweredInput && changedStep) "call shrink omitted sequence/input/step axes"
  ensure ((← rows (← get (Solcore.Synthesis.Source.NestedCall.shrinkCases saved 2 20000)) "cases") == result.extract 0 2 &&
    (← rows (← get (Solcore.Synthesis.Source.NestedCall.shrinkCases saved 0 20000)) "cases").isEmpty) "call shrink limit changed ordering"
  let first := result[0]!
  let reduced ← get (Solcore.Synthesis.Source.NestedCall.caseProgram first)
  let badParent := Json.mkObj [("kind", toJson "reduced"), ("parentPlan", Solcore.Synthesis.Source.NestedCall.planJson reduced.plan),
    ("parentPrograms", Solcore.Synthesis.Source.NestedCall.programsJson reduced.plan),
    ("parentTransactions", Solcore.Synthesis.Source.NestedCall.transactionsJson reduced.transactions)]
  let provenance ← field first "provenance"
  rejected (Solcore.Synthesis.Source.NestedCall.replayCase (first.setObjVal! "provenance" (provenance.setObjVal! "origin" badParent)) 20000)
    "non-strict reduction provenance accepted"

def testSourceNestedCallCases : IO Unit := do
  let imported ← referenceChecks
  resourceChecks
  let generated ← generationChecks
  tamperingChecks imported generated
  shrinkChecks

end Tests.SourceNestedCallCases
end

section
-- leanmerge: from Solcore.Test.SourceNestedCallEmitter
/-! Checked parent/child wrappers through the actual nested scheduler. These
goldens distinguish child rollback from root rollback, retain value transfers
only after committed child success, and exercise an arbitrary stateful step. -/
set_option autoImplicit false

namespace Tests.SourceNestedCallEmitter

open Solcore.Core Solcore.ContractRuntime Solcore.Synthesis.Core
open Solcore.Synthesis.Core.NestedCall (CheckedPlan)
open Solcore.Synthesis.Stateful

private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)
private def entry : Wire.Expr := .apply (.var 1) (.var 0)

private def privateStep : Wire.Expr :=
  .letE (.newCell .word (word 0))
    (.letE (.storeCell (.var 0) (.binary .wordAdd (.loadCell (.var 0)) (word 2)))
      (.binary .wordAdd (.var 2) (.loadCell (.var 1))))

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def checked (helpers : List Wire.Expr) (body : Wire.Expr := entry) : IO CheckedPlan := do
  let some step := Aggregates.CheckedDAG.ofParts? helpers body |
    throw (IO.userError "nested-call step did not pass the aggregate checker")
  let some plan := CheckedPlan.ofStep? step |
    throw (IO.userError "nested-call wrappers did not pass the full Wire host checker")
  return plan

private def emitted (plan : CheckedPlan) : IO Solcore.Synthesis.Source.NestedCall.EmittedContracts :=
  match Solcore.Synthesis.Source.NestedCall.emit plan with
  | .ok result => pure result
  | .error error => throw (IO.userError s!"nested-call source emission failed: {reprStr error}")

private structure Snapshot where
  parent0 : Nat
  parent1 : Nat
  child0 : Nat
  child1 : Nat
  parentBalance : Nat
  childBalance : Nat

private structure Expected where
  input : Nat
  reverts : Bool
  payload : Nat
  committed : Snapshot
  /-- False denotes the parent emitter, true the child emitter. -/
  workingLogs : List (Bool × Nat × Nat)

private def logs (bindings : NestedCallExecution.Bindings)
    (entries : List (Bool × Nat × Nat)) : List CheckedCoreWordLog :=
  entries.map fun (child, topic, payload) =>
    ⟨if child then bindings.child else bindings.parent, Word.ofNatModulo topic, Word.ofNatModulo payload⟩

private def sequenceCheck (plan : CheckedPlan) (expected : List Expected) : IO Unit := do
  let bindings := NestedCallExecution.fixtureBindings
  let registry : CheckedContractRegistry := {
    lookup := fun address => if address = bindings.parent then some plan.parentContract
      else if address = bindings.child then some plan.childContract else none }
  let mut world := NestedCallExecution.initialWorld plan bindings
  for row in expected do
    let some ⟨contract, installed⟩ := registry.resolve? world bindings.parent |
      throw (IO.userError "committed parent no longer resolves to its original Core program")
    let invocation : TopLevelInvocation := {
      target := bindings.parent, caller := bindings.caller, callValue := Word.zero,
      inputData := NestedCallExecution.inputData bindings (Word.ofNatModulo row.input) }
    match (OneLevelNestedExecution.run contract invocation installed registry 0).view with
    | .outOfFuel _ _ _ => pure ()
    | .completed _ => throw (IO.userError "zero fuel was treated as a completed nested transaction")
    match (OneLevelNestedExecution.run contract invocation installed registry 10000).view with
    | .outOfFuel _ _ _ => throw (IO.userError "nested golden exhausted its execution budget")
    | .completed result =>
        let payload := Word.ofNatModulo row.payload
        let typed : Value := if row.reverts then
          .inRight .word (.inLeft .word (.word payload))
          else .inLeft (.sum .word .word) (.word payload)
        let outcome : FrameOutcome Word := if row.reverts then
          .reverted (encodeWordBytesBE payload) else .returned (encodeWordBytesBE payload)
        ensure (result.coreValue == typed && result.outcome == outcome)
          "nested wrapper changed the typed completion or exact 32-byte payload"
        let some parent := result.finalWorld.account? bindings.parent |
          throw (IO.userError "committed parent account missing")
        let some child := result.finalWorld.account? bindings.child |
          throw (IO.userError "committed child account missing")
        let snapshot := row.committed
        ensure (parent.storageRead Word.zero == Word.ofNatModulo snapshot.parent0 &&
          parent.storageRead (Word.ofNatModulo 1) == Word.ofNatModulo snapshot.parent1 &&
          child.storageRead Word.zero == Word.ofNatModulo snapshot.child0 &&
          child.storageRead (Word.ofNatModulo 1) == Word.ofNatModulo snapshot.child1 &&
          parent.balance == Word.ofNatModulo snapshot.parentBalance &&
          child.balance == Word.ofNatModulo snapshot.childBalance)
          "nested rollback or value transfer selected the wrong committed accounts"
        ensure (result.workingJournal.logList == logs bindings row.workingLogs &&
          result.committedJournal.logList == (if row.reverts then [] else logs bindings row.workingLogs))
          "child rollback or root rollback changed committed log order"
        ensure (parent.storageRead (Word.ofNatModulo 2) == Word.zero &&
          child.storageRead (Word.ofNatModulo 2) == Word.zero &&
          parent.nonce == Word.zero && child.nonce == Word.zero && result.coreStore.isEmpty &&
          result.committedJournal.createdContractList.isEmpty)
          "nested execution changed an unrelated account field or exposed the child's private heap"
        ensure ((registry.resolve? result.finalWorld bindings.parent).isSome &&
          (registry.resolve? result.finalWorld bindings.child).isSome)
          "nested completion replaced either installed original Core program"
        world := result.finalWorld

private def executionChecks : IO Unit := do
  let identity ← checked [.var 0]
  sequenceCheck identity [
    ⟨4, false, 8, ⟨4, 4, 4, 1, 7, 1⟩, [(false, 1, 4), (true, 2, 4), (false, 3, 4)]⟩,
    ⟨5, false, 19, ⟨9, 10, 4, 1, 7, 1⟩, [(false, 1, 9), (false, 3, 10)]⟩,
    ⟨6, true, 25, ⟨9, 10, 4, 1, 7, 1⟩, [(false, 1, 15), (true, 2, 10), (false, 3, 10)]⟩]
  -- The helper returns input + 2, but the arbitrary entry subtracts one.
  -- Its fresh private cell must not survive either child success or rollback.
  let arbitrary ← checked [privateStep] (.binary .wordSub entry (word 1))
  sequenceCheck arbitrary [
    ⟨4, false, 9, ⟨4, 5, 5, 1, 7, 1⟩, [(false, 1, 4), (true, 2, 5), (false, 3, 5)]⟩,
    ⟨1, false, 13, ⟨5, 8, 5, 1, 7, 1⟩, [(false, 1, 5), (false, 3, 8)]⟩,
    ⟨0, false, 11, ⟨5, 6, 6, 2, 7, 1⟩, [(false, 1, 5), (true, 2, 6), (false, 3, 6)]⟩]

private def admissionChecks : IO Unit := do
  for plan in [← checked [.var 0], ← checked [privateStep] (.binary .wordSub entry (word 1))] do
    ensure (plan.parentProgram.check && plan.childProgram.check &&
      plan.parentProgram.toCore.checkHost && plan.childProgram.toCore.checkHost &&
      plan.parentProgram.resultType == NestedCall.resultType &&
      plan.childProgram.resultType == NestedCall.resultType &&
      plan.parentContract.entryProfile == .wordOutcomeV1 && plan.childContract.entryProfile == .wordOutcomeV1)
      "nested contracts lost full host checking or their typed outcome convention"
    ensure (plan.parentContract.code.program == plan.parentProgram.toCore &&
      plan.childContract.code.program == plan.childProgram.toCore)
      "nested admission replaced an original Core contract"
    ensure (NestedCall.combinedNodes plan.step ==
      Wire.programNodes plan.parentProgram + Wire.programNodes plan.childProgram &&
      NestedCall.combinedNodes plan.step == Wire.programNodes plan.step.program + NestedCall.programOverhead &&
      NestedCall.programOverhead == 179)
      "nested wrapper budget differs from the two complete original Core programs"
    match plan.childProgram.body with
    | .letE saved _ =>
        ensure (Wire.encodeExpr saved == Wire.encodeExpr plan.step.program.body)
          "child wrapper ignored its arbitrary aggregate entry"
    | _ => throw (IO.userError "child wrapper lost its closed entry binding")
    ensure ((← emitted plan) == (← emitted plan)) "nested source emission is nondeterministic"
  -- Raw primitives join the existing opcode import only when a step uses them.
  let divided ← checked [.binary .wordDiv (.var 0) (word 1)]
  match Solcore.Synthesis.Source.NestedCall.emit divided with
  | .ok emitted => unless (emitted.source.splitOn "log1 as log1_, div as sc_div, mod as sc_mod, ").length == 2 && (emitted.source.splitOn "    let sc_v3: word = sc_div(sc_v0, sc_v2);").length == 2 do
      throw (IO.userError "NestedCall emission lost the merged raw division alias or its snapshots")
  | .error error => throw (IO.userError s!"NestedCall raw division was rejected: {reprStr error}")

private def formattingChecks : IO Unit := do
  let emitted ← emitted (← checked [.var 0])
  ensure (emitted.parentContractName == "SynthesizedCaller" &&
    emitted.childContractName == "SynthesizedCallee" &&
    emitted.parentMethodSignature == "run(uint256,uint256)" && emitted.selector == "0x7357f5d2" &&
    emitted.parentConstructorValue == "8" && emitted.childConstructorValue == "0" &&
    emitted.parentDeployPath == ["SynthesizedCallerDeploy"] &&
    emitted.parentRuntimePath == ["SynthesizedCallerDeploy", "SynthesizedCaller"] &&
    emitted.childDeployPath == ["SynthesizedCalleeDeploy"] &&
    emitted.childRuntimePath == ["SynthesizedCalleeDeploy", "SynthesizedCallee"])
    "nested source metadata changed"
  for fragment in ["log1 as log1_", "fallback() payable", "constructor() payable {}",
    "mstore(64, sc_ptr + 32);", "mstore(64, sc_ptr + 64);",
    "call(gas(), sc_target, sc_value, sc_ptr, 32, sc_ptr + 32, 32)",
    "if (!(returndatasize() == 32))", "invalid();",
    "if ((sc_input & 1) == 1)", "if ((sc_input & 2) == 2)", "if ((sc_input & 4) == 4)"] do
    ensure ((emitted.source.splitOn fragment).length == 2)
      s!"nested source lost or duplicated its protocol fragment: {fragment}"
  ensure (Solcore.Synthesis.Source.NestedCall.emitterVersion == "solcore-source-nested-call-v3" &&
    Solcore.Synthesis.Source.NestedCall.wrapperVersion == "solcore-word-nested-call-v1" &&
    NestedCall.version == "core-nested-word-call-v1") "nested provenance changed"

def testSourceNestedCallEmitter : IO Unit := do
  admissionChecks
  executionChecks
  formattingChecks

end Tests.SourceNestedCallEmitter
end

section
-- leanmerge: from Solcore.Test.SourceRecursionCases
/-! The `runtime-recursion` profile. Plans admit depth masks 0, 1, 3 and 7 and
three forms. The unrolled Core reference returns what a recursive model of the
emitted source returns, frame by frame over the step's original Core, at
depth `input & mask`, at most seven frames deep. Generation draws all nine
shapes, excludes boundary identities and replays exactly; tampering is
refused, and reductions lower the mask, fall back to the tail form or move the
input and stay strictly smaller. -/
set_option autoImplicit false

namespace Tests.SourceRecursionCases

open Lean
open Solcore.Core (Word)
open Solcore.Synthesis.Core
open Solcore.Synthesis.Core.Recursion (CheckedPlan Form)
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
  return case.setObjVal! "recursionPlan" (change (← get (case.getObjVal? "recursionPlan")))

private def step (plan : CheckedPlan) (value : Word) : Option Word :=
  match (plan.step.instantiate value).toCore.runStateful fuel with
  | .done (.word result) _ => some result
  | _ => none

/-- `tail` and `nontail` frames: `f(d, acc)` as the emitted `sc_rec` computes it. -/
private def single (plan : CheckedPlan) (tail : Bool) : Nat → Word → Option Word
  | 0, accumulator => some accumulator
  | depth + 1, accumulator =>
      if tail then do single plan tail depth (← step plan accumulator)
      else do
        let inner ← single plan tail depth accumulator
        return Word.ofNatModulo ((← step plan inner).val + (depth + 1))

/-- `mutual` frames: `even` when `isEven`, as the emitted `sc_even` and `sc_odd` compute them. -/
private def alternating (plan : CheckedPlan) : Bool → Nat → Word → Option Word
  | _, 0, accumulator => some accumulator
  | true, depth + 1, accumulator => do alternating plan false depth (← step plan accumulator)
  | false, depth + 1, accumulator => alternating plan true depth (Word.ofNatModulo (accumulator.val + (depth + 1)))

private def model (plan : CheckedPlan) (input : Word) : Option Word :=
  match plan.form with
  | .tail => single plan true (plan.depth input) input
  | .nontail => single plan false (plan.depth input) input
  | .mutual => alternating plan true (plan.depth input) input

private def admissionChecks (step : Aggregates.CheckedDAG) : IO Unit := do
  for mask in [0, 1, 3, 7] do
    for form in Form.all do
      ensure (CheckedPlan.ofParts? step mask form).isSome s!"mask {mask} with form {form.name} was refused"
  for mask in [2, 5, 15] do
    ensure (CheckedPlan.ofParts? step mask .tail).isNone s!"mask {mask} was admitted"

/-- Each form's recursive calls and the wrapper's depth and entry. -/
private def emitterChecks (step : Aggregates.CheckedDAG) : IO Unit := do
  for (form, entry, lines) in [
      (Form.tail, "sc_rec", ["        sc_result = sc_rec((sc_depth - 1), sc_next);"]),
      (.nontail, "sc_rec", ["        let sc_inner: word = sc_rec((sc_depth - 1), sc_acc);",
        "        sc_result = (sc_stepped + sc_depth);"]),
      (.mutual, "sc_even", ["        sc_result = sc_odd((sc_depth - 1), sc_next);",
        "        let sc_next: word = (sc_acc + sc_depth);", "        sc_result = sc_even((sc_depth - 1), sc_next);"])] do
    let some plan := CheckedPlan.ofParts? step 7 form | throw (IO.userError "plan refused")
    let source := (← get ((Recursion.emit plan).mapError reprStr)).source
    for line in lines ++ ["        let sc_depth: word = (sc_input & 7);",
        "        let sc_out: word = " ++ entry ++ "(sc_depth, sc_input);"] do
      ensure ((source.splitOn line).length == 2) s!"{form.name}: the source lacks the line {line}"
    let functions := if form == .mutual then 2 else 1
    ensure ((source.splitOn "    if (sc_depth > 0) {").length == functions + 1)
      s!"{form.name}: the source does not test the depth once per recursive function"

private def generationChecks : IO Unit := do
  let corpus := Recursion.generateCases (Seed.ofNat 1) 384 1023 400 fuel .v4 .seeded
  ensure (corpus == Recursion.generateCases (Seed.ofNat 1) 384 1023 400 fuel .v4 .seeded)
    "recursion generation is not deterministic"
  let generated ← cases corpus
  ensure (generated.size == 1023) "recursion generation did not complete"
  let excluded ← get (corpus.getObjValAs? (Array Json) "excluded")
  for entry in excluded do
    let reason ← get (entry.getObjValAs? String "reason")
    ensure (reason == Acceptance.identityReason ||
        reason == "node budget is too small for the selected aggregate template or exceeds 512")
      s!"unexpected recursion exclusion: {reason}"
  let mut shapes : List String := []
  for index in List.range (generated.size / 11) do
    let function := generated.extract (11 * index) (11 * index + 11)
    let some first := function[0]? | throw (IO.userError "empty function")
    let plan := (← get (Recursion.caseProgram first)).plan
    shapes := s!"{plan.mask}:{plan.form.name}" :: shapes
    let mut identity := true
    for (case, position) in function.zipIdx do
      let input := (← get (Recursion.caseProgram case)).input
      let result ← directWord case
      ensure (plan.depth input ≤ 7) "a call recursed deeper than seven frames"
      ensure (model plan input == some result) "the Core reference differs from the recursive model"
      if position < 7 && result != input then identity := false
    ensure (!identity) "a generated recursion returned every boundary input"
  ensure (shapes.eraseDups.length == 9) s!"generation drew {shapes.eraseDups.length} of nine shapes"

private def replayChecks (case : Json) : IO Unit := do
  ensure ((← get (Recursion.replayCase case fuel)) == case) "a recursion case failed exact replay"
  let plan ← get (case.getObjVal? "recursionPlan")
  let mask ← get (plan.getObjValAs? Nat "depthMask")
  let form ← get (plan.getObjValAs? String "form")
  for changed in [
      ← withPlan case (·.setObjVal! "depthMask" (toJson (if mask == 7 then 3 else 7))),
      ← withPlan case (·.setObjVal! "depthMask" (toJson (5 : Nat))),
      ← withPlan case (·.setObjVal! "form" (toJson (if form == "tail" then "mutual" else "tail"))),
      ← withPlan case (·.setObjVal! "form" (toJson "loop"))] do
    ensure (Recursion.replayCase changed fuel matches .error _) "a tampered recursion case replayed"

private def reductionChecks (case : Json) : IO Unit := do
  let source ← get (Recursion.caseProgram case)
  let mut lowered := false
  let mut tail := false
  for reduced in Recursion.reductions source do
    let plan := reduced.candidate.plan
    ensure (plan.mask ≤ source.plan.mask && plan.step.helpers.length == source.plan.step.helpers.length)
      "a reduction raised the mask or changed the helper count"
    ensure (plan.form == source.plan.form || plan.form == .tail) "a reduction changed the form to another than tail"
    ensure ((complexity reduced.candidate.program.body).isStrictlySmaller (complexity source.program.body))
      "a reduction is not strictly smaller"
    if plan.mask < source.plan.mask then lowered := true
    if plan.form == .tail && source.plan.form != .tail then tail := true
  ensure lowered "no reduction lowered the mask"
  ensure (tail || source.plan.form == .tail) "no reduction fell back to the tail form"
  let emitted ← cases (← get (Recursion.shrinkCases case 4 fuel))
  ensure (!emitted.isEmpty) "a recursion case has no reduction"
  for candidate in emitted do
    ensure ((← get (Recursion.replayCase candidate fuel)) == candidate) "a reduction failed exact replay"

/-- An imported plan with a depth mask of zero never recurses. -/
private def importChecks (step : Aggregates.CheckedDAG) : IO Unit := do
  let some plan := CheckedPlan.ofParts? step 0 .mutual | throw (IO.userError "plan refused")
  let case ← get (Recursion.emitCase plan (Word.ofNatModulo 7) (Json.mkObj [("kind", toJson "imported")]) fuel)
  ensure ((← directWord case) == Word.ofNatModulo 7) "a plan of depth zero changed its input"
  ensure ((← get (Recursion.replayCase case fuel)) == case) "an imported recursion case failed exact replay"

def testSourceRecursionCases : IO Unit := do
  let generated ← cases (Recursion.generateCases (Seed.ofNat 2) 384 7 16 fuel .v4)
  let some first := generated[0]? | throw (IO.userError "no recursion case")
  let source ← get (Recursion.caseProgram first)
  admissionChecks source.plan.step
  emitterChecks source.plan.step
  importChecks source.plan.step
  generationChecks
  for case in generated do
    replayChecks case
  for case in generated.extract 1 5 do
    reductionChecks case

end Tests.SourceRecursionCases
end

section
-- leanmerge: from Solcore.Test.SourceRecursiveLoopCases
/-! The `runtime-recursive-loops` profile. Plans admit depth and inner masks 0,
1 and 3 and the three recursion forms. The unrolled Core reference returns
what a recursive model of the emitted source returns, frame by frame and loop
iteration by loop iteration over the step's original Core: a frame of depth `e`
runs `e & I` iterations. Generation draws all twelve shapes, excludes boundary
identities and replays exactly; tampering is refused, and reductions lower a
mask, fall back to the tail form or move the input and stay strictly smaller. -/
set_option autoImplicit false

namespace Tests.SourceRecursiveLoopCases

open Lean
open Solcore.Core (Word)
open Solcore.Synthesis.Core
open Solcore.Synthesis.Core.RecursiveLoop (CheckedPlan)
open Solcore.Synthesis.Core.Recursion (Form)
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
  return case.setObjVal! "recursiveLoopPlan" (change (← get (case.getObjVal? "recursiveLoopPlan")))

private def step (plan : CheckedPlan) (value : Word) : Option Word :=
  match (plan.step.instantiate value).toCore.runStateful fuel with
  | .done (.word result) _ => some result
  | _ => none

/-- The trip count of a frame of depth `depth`. -/
private def trips (plan : CheckedPlan) (depth : Nat) : Nat :=
  ((Word.ofNatModulo depth).bitAnd (Word.ofNatModulo plan.innerMask)).val

/-- A frame's while loop over the step. -/
private def iterate (plan : CheckedPlan) : Nat → Word → Option Word
  | 0, value => some value
  | count + 1, value => do iterate plan count (← step plan value)

/-- `tail` and `nontail` frames: `f(d, acc)` as the emitted `sc_rec` computes it. -/
private def single (plan : CheckedPlan) (tail : Bool) : Nat → Word → Option Word
  | 0, accumulator => some accumulator
  | depth + 1, accumulator =>
      if tail then do single plan tail depth (← iterate plan (trips plan (depth + 1)) accumulator)
      else do
        let inner ← single plan tail depth accumulator
        return Word.ofNatModulo ((← iterate plan (trips plan (depth + 1)) inner).val + (depth + 1))

/-- `mutual` frames: `even` when `isEven`, as the emitted `sc_even` and `sc_odd` compute them. -/
private def alternating (plan : CheckedPlan) : Bool → Nat → Word → Option Word
  | _, 0, accumulator => some accumulator
  | true, depth + 1, accumulator => do
      alternating plan false depth (← iterate plan (trips plan (depth + 1)) accumulator)
  | false, depth + 1, accumulator =>
      alternating plan true depth
        (Word.ofNatModulo (accumulator.val + (depth + 1) * trips plan (depth + 1)))

private def model (plan : CheckedPlan) (input : Word) : Option Word :=
  match plan.form with
  | .tail => single plan true (plan.depth input) input
  | .nontail => single plan false (plan.depth input) input
  | .mutual => alternating plan true (plan.depth input) input

private def admissionChecks (step : Aggregates.CheckedDAG) : IO Unit := do
  for depthMask in [0, 1, 3] do
    for innerMask in [0, 1, 3] do
      for form in Form.all do
        ensure (CheckedPlan.ofParts? step depthMask innerMask form).isSome
          s!"masks {depthMask} and {innerMask} with form {form.name} were refused"
  for mask in [2, 5, 7] do
    ensure (CheckedPlan.ofParts? step mask 3 .tail).isNone s!"depth mask {mask} was admitted"
    ensure (CheckedPlan.ofParts? step 3 mask .tail).isNone s!"inner mask {mask} was admitted"

/-- Each form's loop, recursive calls and the wrapper's depth and entry. -/
private def emitterChecks (step : Aggregates.CheckedDAG) : IO Unit := do
  for (form, entry, lines) in [
      (Form.tail, "sc_rec", ["            sc_value = sc_step(sc_value);",
        "        sc_result = sc_rec((sc_depth - 1), sc_value);"]),
      (.nontail, "sc_rec", ["        let sc_inner: word = sc_rec((sc_depth - 1), sc_acc);",
        "            sc_inner = sc_step(sc_inner);", "        sc_result = (sc_inner + sc_depth);"]),
      (.mutual, "sc_even", ["            sc_value = sc_step(sc_value);",
        "        sc_result = sc_odd((sc_depth - 1), sc_value);", "            sc_value = (sc_value + sc_depth);",
        "        sc_result = sc_even((sc_depth - 1), sc_value);"])] do
    let some plan := CheckedPlan.ofParts? step 3 3 form | throw (IO.userError "plan refused")
    let source := (← get ((RecursiveLoop.emit plan).mapError reprStr)).source
    for line in lines ++ ["        let sc_depth: word = (sc_input & 3);",
        "        let sc_out: word = " ++ entry ++ "(sc_depth, sc_input);"] do
      ensure ((source.splitOn line).length == 2) s!"{form.name}: the source lacks the line {line}"
    let functions := if form == .mutual then 2 else 1
    for line in ["    if (sc_depth > 0) {", "        let sc_trips: word = (sc_depth & 3);",
        "        while (sc_trips > sc_j) {"] do
      ensure ((source.splitOn line).length == functions + 1)
        s!"{form.name}: the source does not have {line} once per recursive function"

private def generationChecks : IO Unit := do
  let corpus := RecursiveLoop.generateCases (Seed.ofNat 1) 384 1020 400 fuel .v4 .seeded
  ensure (corpus == RecursiveLoop.generateCases (Seed.ofNat 1) 384 1020 400 fuel .v4 .seeded)
    "recursive-loop generation is not deterministic"
  let generated ← cases corpus
  ensure (generated.size == 1020) "recursive-loop generation did not complete"
  let excluded ← get (corpus.getObjValAs? (Array Json) "excluded")
  for entry in excluded do
    let reason ← get (entry.getObjValAs? String "reason")
    ensure (reason == Acceptance.identityReason ||
        reason == "node budget is too small for the selected aggregate template or exceeds 512")
      s!"unexpected recursive-loop exclusion: {reason}"
  let mut shapes : List String := []
  for index in List.range (generated.size / 10) do
    let function := generated.extract (10 * index) (10 * index + 10)
    let some first := function[0]? | throw (IO.userError "empty function")
    let plan := (← get (RecursiveLoop.caseProgram first)).plan
    shapes := s!"{plan.depthMask}x{plan.innerMask}:{plan.form.name}" :: shapes
    let mut identity := true
    for (case, position) in function.zipIdx do
      let input := (← get (RecursiveLoop.caseProgram case)).input
      let result ← directWord case
      ensure (plan.depth input ≤ 3 && plan.iterations input ≤ 6) "a call recursed deeper or looped longer than its bounds"
      ensure (model plan input == some result) "the Core reference differs from the recursive-loop model"
      if position < 6 && result != input then identity := false
    ensure (!identity) "a generated recursive loop returned every boundary input"
  ensure (shapes.eraseDups.length == 12) s!"generation drew {shapes.eraseDups.length} of twelve shapes"

private def replayChecks (case : Json) : IO Unit := do
  ensure ((← get (RecursiveLoop.replayCase case fuel)) == case) "a recursive-loop case failed exact replay"
  let plan ← get (case.getObjVal? "recursiveLoopPlan")
  let depthMask ← get (plan.getObjValAs? Nat "depthMask")
  let innerMask ← get (plan.getObjValAs? Nat "innerMask")
  let form ← get (plan.getObjValAs? String "form")
  for changed in [
      ← withPlan case (·.setObjVal! "depthMask" (toJson (if depthMask == 3 then 1 else 3))),
      ← withPlan case (·.setObjVal! "innerMask" (toJson (if innerMask == 3 then 1 else 3))),
      ← withPlan case (·.setObjVal! "depthMask" (toJson (7 : Nat))),
      ← withPlan case (·.setObjVal! "form" (toJson (if form == "tail" then "mutual" else "tail"))),
      ← withPlan case (·.setObjVal! "form" (toJson "loop"))] do
    ensure (RecursiveLoop.replayCase changed fuel matches .error _) "a tampered recursive-loop case replayed"

private def reductionChecks (case : Json) : IO Unit := do
  let source ← get (RecursiveLoop.caseProgram case)
  let mut lowered := false
  let mut tail := false
  for reduced in RecursiveLoop.reductions source do
    let plan := reduced.candidate.plan
    ensure (plan.depthMask ≤ source.plan.depthMask && plan.innerMask ≤ source.plan.innerMask &&
        plan.step.helpers.length == source.plan.step.helpers.length)
      "a reduction raised a mask or changed the helper count"
    ensure (plan.form == source.plan.form || plan.form == .tail) "a reduction changed the form to another than tail"
    ensure ((complexity reduced.candidate.program.body).isStrictlySmaller (complexity source.program.body))
      "a reduction is not strictly smaller"
    if plan.depthMask < source.plan.depthMask || plan.innerMask < source.plan.innerMask then lowered := true
    if plan.form == .tail && source.plan.form != .tail then tail := true
  ensure lowered "no reduction lowered a mask"
  -- A mutual plan whose odd frame runs no iteration has the tail form's reference.
  let larger := source.plan.form == .nontail ||
    (source.plan.form == .mutual && source.plan.depthMask > 1 && source.plan.innerMask > 0)
  ensure (tail || !larger) "no reduction fell back to the tail form"
  let emitted ← cases (← get (RecursiveLoop.shrinkCases case 4 fuel))
  ensure (!emitted.isEmpty) "a recursive-loop case has no reduction"
  for candidate in emitted do
    ensure ((← get (RecursiveLoop.replayCase candidate fuel)) == candidate) "a reduction failed exact replay"

/-- An imported plan with a depth mask of zero never recurses, and one with an
inner mask of zero runs no loop iteration. -/
private def importChecks (step : Aggregates.CheckedDAG) : IO Unit := do
  let some plan := CheckedPlan.ofParts? step 0 3 .mutual | throw (IO.userError "plan refused")
  let case ← get (RecursiveLoop.emitCase plan (Word.ofNatModulo 7) (Json.mkObj [("kind", toJson "imported")]) fuel)
  ensure ((← directWord case) == Word.ofNatModulo 7) "a plan of depth zero changed its input"
  ensure ((← get (RecursiveLoop.replayCase case fuel)) == case) "an imported recursive-loop case failed exact replay"
  let some plan := CheckedPlan.ofParts? step 3 0 .nontail | throw (IO.userError "plan refused")
  let case ← get (RecursiveLoop.emitCase plan (Word.ofNatModulo 3) (Json.mkObj [("kind", toJson "imported")]) fuel)
  ensure ((← directWord case) == Word.ofNatModulo 9) "a nontail plan without loop iterations did not add its depths"

def testSourceRecursiveLoopCases : IO Unit := do
  let generated ← cases (RecursiveLoop.generateCases (Seed.ofNat 2) 384 6 16 fuel .v4)
  let some first := generated[0]? | throw (IO.userError "no recursive-loop case")
  let source ← get (RecursiveLoop.caseProgram first)
  admissionChecks source.plan.step
  emitterChecks source.plan.step
  importChecks source.plan.step
  generationChecks
  for case in generated do
    replayChecks case
  for case in generated.extract 1 5 do
    reductionChecks case

end Tests.SourceRecursiveLoopCases
end
