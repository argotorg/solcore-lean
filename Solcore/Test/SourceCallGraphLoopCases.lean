import Solcore.Synthesis.Source.CallGraphLoopCases

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
