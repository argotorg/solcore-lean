import Solcore.Synthesis.Source.AggregateCallGraphCases
import Solcore.Test.SourceAggregateCallGraphEmitter

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
