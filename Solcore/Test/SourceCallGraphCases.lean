import Solcore.Synthesis.Source.CallGraphCases

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
