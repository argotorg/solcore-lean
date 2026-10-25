import Solcore.Synthesis.Source.ModuleCases

/-! Modules cases retain original ASTs and all four source files, execute the Core composition
independently, reject changed provenance, and shrink either typed component. -/
set_option autoImplicit false

namespace Tests.SourceModuleCases
open Lean Solcore.Core Solcore.Synthesis.Core Solcore.Synthesis.Source
open Solcore.Synthesis.Core.Modules (CheckedPlan)

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
  | none => throw (IO.userError "module step fixture failed checked admission")
private def constant (body : Wire.Expr) : IO CheckedWordProgram :=
  match CheckedWordProgram.ofProgram? {resultType := .word, dataDefinitions := [], body} with
  | some value => pure value
  | none => throw (IO.userError "constant fixture is not a checked closed G0 Word")
private def constantBody : Wire.Expr :=
  .letE (.binary .wordAdd (word 2) (word 3))
    (.ifE (.binary .wordGt (.var 0) (word 4))
      (.binary .wordMul (.var 0) (word 2)) (word 0))
private def plan (fixed : CheckedWordProgram) (step : Aggregates.CheckedDAG) : IO CheckedPlan :=
  match CheckedPlan.ofParts? fixed step with
  | some value => pure value
  | none => throw (IO.userError "module plan fixture failed checked admission")
private def imported (value : CheckedPlan) (input : Word) : IO Json :=
  get (Modules.emitCase value input (Json.mkObj [("kind", toJson "imported")]) 10000)
private def returned (value : Word) : Json := Json.mkObj [
  ("stage", toJson "execution"), ("status", toJson "returned"),
  ("word", toJson (toString value.val))]

/-- One private step cell is followed by the wrapper's mutable capture cell.
The entry differs from the last helper and must not be discarded by the wrapper. -/
private def privateStep : Wire.Expr :=
  .letE (.newCell .word (.var 0))
    (.letE (.storeCell (.var 0) (.binary .wordAdd (.loadCell (.var 0)) (word 2)))
      (.loadCell (.var 1)))

private def expected (k input stepOffset : Word) : Word :=
  let left := (((input.add k).add stepOffset).mul (Word.ofNatModulo 2)).add input |>.add (Word.ofNatModulo 1)
  let right := ((input.bitXor k).mul (Word.ofNatModulo 2)).add input |>.add (Word.ofNatModulo 3)
  let selected := if input.bitAnd (Word.ofNatModulo 1) == Word.ofNatModulo 1 then left else right
  ((selected.add left).add (right.mul (Word.ofNatModulo 3))).add k

private def checkBundle (saved : Json) : IO Unit := do
  let bundle ← field saved "sourceBundle"
  ensure ((← string bundle "schema") == "solcore-lean.source-bundle.v1" &&
    (← string bundle "entry") == "case.sol") "module bundle schema/entry changed"
  let files ← get (bundle.getObjValAs? (Array Json) "files")
  let paths ← files.toList.mapM fun file => string file "path"
  ensure (paths == ["case.sol", "common.sol", "left.sol", "right.sol"])
    "module bundle is not the exact sorted four-file source"
  ensure ((← string files[0]! "source") == (← string saved "source"))
    "single source alias differs from case.sol bytes"

private def referenceChecks : IO Unit := do
  let fixed ← constant constantBody
  ensure (Solcore.Synthesis.Source.observe fixed 10000 == returned (Word.ofNatModulo 10))
    "independent closed constant golden failed"
  let graph ← checked [privateStep] (.binary .wordSub entry (word 1))
  let value ← plan fixed graph
  ensure (Wire.programNodes (value.instantiate Word.zero) ==
    Wire.programNodes fixed.program + Wire.programNodes graph.program +
    Solcore.Synthesis.Core.Modules.appliedOverhead)
    "module whole node budget omitted one original expression"
  let mut source : Option Json := none
  for input in Modules.boundaryInputs do
    ensure (Modules.observe value input 10000 == returned (expected (Word.ofNatModulo 10) input (Word.ofNatModulo 1)))
      s!"module provider/capture/selection mismatch: input {input.val}"
    match (value.instantiate input).toCore.runStateful 10000 with
    | .done (.word _) store =>
        ensure (store == [.word (input.add (Word.ofNatModulo 12)),
          .word (input.add (Word.ofNatModulo 12)),
          .word ((input.bitXor (Word.ofNatModulo 10)).add (Word.ofNatModulo 2))])
          "module composition changed provider order or shared a private capture cell"
    | _ => throw (IO.userError "checked module reference did not return")
    let saved ← imported value input
    checkBundle saved
    let current ← field saved "sourceBundle"
    if let some previous := source then ensure (current == previous) "module bundle depends on runtime input"
    source := some current
    let admitted ← get (Modules.caseProgram saved)
    ensure (admitted.program.check && admitted.input == input &&
      Wire.encodeProgram admitted.plan.constant.program == Wire.encodeProgram fixed.program)
      "module case lost one original checked expression"
    ensure ((← get (Modules.replayCase saved 10000)) == saved) "imported module case did not replay"
    ensure ((← get (Modules.replayCase (saved.setObjVal! "directCore" (returned Word.zero)) 10000)) == saved)
      "module replay trusted its stored expected result"
    let low ← get (Modules.replayCase saved 0)
    ensure ((← string (← field low "directCore") "status") == "out-of-fuel")
      "module fuel exhaustion was treated as completion"
  let identity ← checked [.var 0]
  let literal ← constant (word 4)
  let literalPlan ← plan literal identity
  ensure (!(Modules.inputSensitive literalPlan 10000).isOk)
    "generated constant without an operation was admitted"
  ensure ((Modules.emitCase literalPlan Word.zero (Json.mkObj [("kind", toJson "imported")]) 10000).isOk)
    "imported literal constant should remain supported"
  let constantStep ← checked [word 4]
  let constantPlan ← plan fixed constantStep
  ensure (!(Modules.inputSensitive constantPlan 10000).isOk)
    "generated module plan lost the step's input-sensitive requirement"
  let wrapped ← constant (.binary .wordAdd (.word Word.maximum) (word 1))
  let wrappedPlan ← plan wrapped identity
  for input in Modules.boundaryInputs do
    ensure (Modules.observe wrappedPlan input 10000 == returned (expected Word.zero input Word.zero))
      "original constant Word overflow was not preserved"

private def minimumBudget (seed : Nat) : IO Nat := do
  for nodes in List.range 513 do
    if (Modules.generatedPlan (Seed.ofNat seed) nodes).isOk then return nodes
  throw (IO.userError "module skeleton did not fit the case node limit")

private def generationChecks : IO Json := do
  -- All joint helper/template residues have a bounded, fully checked skeleton.
  for seed in List.range 36 do
    let budget ← minimumBudget seed
    ensure (budget ≤ 512) "maximum module budget cannot hold a selected template skeleton"
    let (value, _) ← get (Modules.generatedPlan (Seed.ofNat seed) budget)
    ensure (Wire.programNodes (value.instantiate Word.zero) ≤ budget &&
      value.step.helpers.length == 1 + seed % 3)
      "module generation escaped its full node or helper constraints"
    ensure (!(Modules.generatedPlan (Seed.ofNat seed) (budget - 1)).isOk &&
      !(Modules.generatedPlan (Seed.ofNat seed) 513).isOk) "module node bounds were not enforced"
  let corpus := Modules.generateCases (Seed.ofNat 0) 384 8 512 10000
  ensure (corpus == Modules.generateCases (Seed.ofNat 0) 384 8 512 10000)
    "module generation is nondeterministic"
  let rows ← cases corpus
  ensure (rows.size == 8 && (← natural corpus "attempted") ≤ 512)
    "bounded module generation did not complete"
  for (row, index) in rows.toList.zipIdx do
    let admitted ← get (Modules.caseProgram row)
    ensure (Wire.programNodes admitted.program ≤ 384 &&
      some admitted.input == Modules.boundaryInputs[index % 4]?) "module generation changed boundary order/budget"
    ensure ((← get (Modules.replayCase row 10000)) == row) "generated module provenance did not replay"
    let low ← get (Modules.replayCase row 0)
    ensure ((← string (← field low "directCore") "status") == "out-of-fuel")
      "fresh module observation fuel changed saved validation fuel"
  let saved := rows[3]!
  let origin ← field (← field saved "provenance") "origin"
  let seedText ← string origin "seed"
  let some seed := seedText.toNat? | throw (IO.userError "invalid generated seed")
  let low := Modules.generateCases (Seed.ofNat seed) 384 1 1 0
  let excluded ← get (low.getObjValAs? (Array Json) "excluded")
  ensure ((← string excluded[0]! "category") == "inconclusive-resource")
    "module generation fuel exhaustion was classified as a semantic exclusion"
  ensure ((← cases (Modules.generateCases (Seed.ofNat seed) 384 3 1 10000)).size == 3 &&
    (← string (Modules.generateCases (Seed.ofNat seed) 384 5 1 10000) "status") == "generation-exhausted")
    "module count/attempt limits did not distinguish cases from function candidates"
  ensure ((← natural (Modules.generateCases (Seed.ofNat seed) 384 0 100 10000) "attempted") == 0 &&
    (← cases (Modules.generateCases (Seed.ofNat seed) 384 1 0 10000)).isEmpty)
    "empty module generation budgets consumed work"
  return saved

private def tamperingChecks (saved : Json) : IO Unit := do
  let provenance ← field saved "provenance"
  let origin ← field provenance "origin"
  let withOrigin := fun changed => saved.setObjVal! "provenance" (provenance.setObjVal! "origin" changed)
  for name in ["generatorVersion", "profileVersion", "functionVersion", "templateVersion",
      "stepProfileVersion", "stepFunctionVersion", "stepTemplateVersion", "emitterVersion", "wrapperVersion"] do
    rejected (Modules.replayCase (saved.setObjVal! "provenance"
      (provenance.setObjVal! name (toJson "forged"))) 10000) "tampered module version accepted"
  for (name, value) in [("seed", toJson "00"), ("finalSeed", toJson "forged"),
      ("maxProgramNodes", toJson (513 : Nat)),
      ("stepOrigin", Json.null), ("constantOrigin", Json.null), ("inputIndex", toJson (4 : Nat)),
      ("validationFuel", toJson (10000001 : Nat)), ("validationFuel", toJson (0 : Nat))] do
    rejected (Modules.replayCase (withOrigin (origin.setObjVal! name value)) 10000)
      s!"tampered module {name} accepted"
  let stepOrigin ← field origin "stepOrigin"
  for name in ["seed", "finalSeed", "maxProgramNodes", "helpers", "helperCount"] do
    rejected (Modules.replayCase (withOrigin (origin.setObjVal! "stepOrigin"
      (stepOrigin.setObjVal! name Json.null))) 10000) "tampered nested step recipe accepted"
  let constantOrigin ← field origin "constantOrigin"
  for name in ["kind", "seed", "finalSeed", "maxProgramNodes"] do
    rejected (Modules.replayCase (withOrigin (origin.setObjVal! "constantOrigin"
      (constantOrigin.setObjVal! name Json.null))) 10000) "tampered constant recipe accepted"
  rejected (Modules.replayCase (saved.setObjVal! "provenance"
    (provenance.setObjVal! "constantFeatures" (toJson ([] : List String)))) 10000)
    "tampered constant feature provenance accepted"
  let admitted ← get (Modules.caseProgram saved)
  let wrongProgram := Wire.encodeProgram (admitted.plan.step.instantiate admitted.input)
  for kind in ["imported", "reduced", "module-generated"] do
    let changed := (withOrigin (origin.setObjVal! "kind" (toJson kind))).setObjVal! "program" wrongProgram
    rejected (Modules.caseProgram changed) "noncanonical program accepted under a different origin"
    rejected (Modules.replayCase changed 10000) "replay skipped canonical comparison for an origin"
  let modulePlan ← field saved "modulePlan"
  let changedConstant ← constant (word 17)
  rejected (Modules.caseProgram (saved.setObjVal! "modulePlan"
    (modulePlan.setObjVal! "constantProgram" (Wire.encodeProgram changedConstant.program))))
    "changed constant program was not compared against the full original reference"
  let free : Wire.Program := {resultType := .word, dataDefinitions := [], body := .var 0}
  rejected (Modules.checkedPlan (modulePlan.setObjVal! "constantProgram" (Wire.encodeProgram free)))
    "constant captured an outer runtime input"
  for (name, value) in [("variant", toJson "offset"), ("schema", toJson "unknown"),
      ("unexpected", toJson true)] do
    rejected (Modules.checkedPlan (modulePlan.setObjVal! name value)) "malformed module plan accepted"
  rejected (Modules.caseProgram (saved.setObjVal! "input" (toJson "01"))) "noncanonical module input accepted"
  rejected (Modules.caseProgram (saved.setObjVal! "input" (toJson "0"))) "input/reference mismatch accepted"
  rejected (Modules.replayCase (saved.setObjVal! "source" (toJson "stale")) 10000) "stale module source accepted"
  let bundle ← field saved "sourceBundle"
  let files ← get (bundle.getObjValAs? (Array Json) "files")
  let changedBundle := fun changed => saved.setObjVal! "sourceBundle" changed
  for changed in [bundle.setObjVal! "entry" (toJson "common.sol"),
      bundle.setObjVal! "extra" (toJson true),
      bundle.setObjVal! "files" (.arr (files.extract 0 3)),
      bundle.setObjVal! "files" (.arr (files.push files[0]!)),
      bundle.setObjVal! "files" (toJson files.toList.reverse)] do
    rejected (Modules.replayCase (changedBundle changed) 10000)
      "missing/extra/reordered module bundle accepted"
  for index in List.range files.size do
    let file := files[index]!
    let text ← string file "source"
    let changed := files.set! index (file.setObjVal! "source" (toJson (text ++ "\n")))
    rejected (Modules.replayCase (changedBundle (bundle.setObjVal! "files" (.arr changed))) 10000)
      "changed source dependency was ignored"
  for path in ["../common.sol", "/tmp/common.sol", "case.sol", "common.txt"] do
    let changed := files.set! 1 (files[1]!.setObjVal! "path" (toJson path))
    rejected (Modules.replayCase (changedBundle (bundle.setObjVal! "files" (.arr changed))) 10000)
      "noncanonical dependency path accepted"

  let contract ← field saved "contract"
  rejected (Modules.replayCase (saved.setObjVal! "contract" (contract.setObjVal! "calldata" (toJson "0x"))) 10000)
    "wrong module ABI input accepted"

private def shrinkChecks : IO Unit := do
  let graph ← checked [Aggregate.template 3 (word 2)]
  let fixed ← constant constantBody
  let value ← plan fixed graph
  let saved ← imported value Word.maximum
  let original ← get (Modules.caseProgram saved)
  let shrunk ← get (Modules.shrinkCases saved 1000 10000)
  let rows ← cases shrunk
  ensure (!rows.isEmpty && shrunk == (← get (Modules.shrinkCases saved 1000 10000)))
    "module shrinking was empty or nondeterministic"
  let mut seen : List String := []
  let mut inputReduced := false
  let mut stepReduced := false
  let mut constantReduced := false
  for row in rows do
    let candidate ← get (Modules.caseProgram row)
    ensure (candidate.program.check && candidate.plan.step.helpers.length == graph.helpers.length &&
      Aggregate.bindingInventory candidate.plan.step == Aggregate.bindingInventory graph)
      "module reduction lost a step binder/helper or changed its composition"
    ensure ((complexity candidate.program.body).isStrictlySmaller (complexity original.program.body))
      "module reduction did not decrease the full original Core program"
    let key := (Wire.encodeProgram candidate.program).compress
    ensure (!seen.contains key) "module reduction duplicated a canonical program"
    seen := key :: seen
    ensure ((← get (Modules.replayCase row 10000)) == row) "module reduction did not replay"
    inputReduced := inputReduced || candidate.input != original.input
    constantReduced := constantReduced || Wire.encodeProgram candidate.plan.constant.program != Wire.encodeProgram fixed.program
    stepReduced := stepReduced || Wire.encodeProgram candidate.plan.step.program != Wire.encodeProgram graph.program
  ensure (inputReduced && stepReduced && constantReduced) "module reduction omitted constant, input or step candidates"
  ensure ((← cases (← get (Modules.shrinkCases saved 2 10000))) == rows.extract 0 2 &&
    (← cases (← get (Modules.shrinkCases saved 0 10000))).isEmpty) "module shrink limit changed ordering"
  let reduced := rows[0]!
  let candidate ← get (Modules.caseProgram reduced)
  let provenance ← field reduced "provenance"
  let origin ← field provenance "origin"
  for (name, value) in [("parentProgram", Wire.encodeProgram candidate.program),
      ("parentInput", toJson "00"), ("extra", toJson true)] do
    rejected (Modules.replayCase (reduced.setObjVal! "provenance"
      (provenance.setObjVal! "origin" (origin.setObjVal! name value))) 10000)
      "tampered reduction witness accepted"
  let sameParent := Json.mkObj [("kind", toJson "reduced"),
    ("parentProgram", Wire.encodeProgram candidate.program), ("parentPlan", Modules.planJson candidate.plan),
    ("parentInput", toJson (toString candidate.input.val))]
  rejected (Modules.replayCase (reduced.setObjVal! "provenance"
    (provenance.setObjVal! "origin" sameParent)) 10000) "non-strict reduction origin accepted"


def testSourceModuleCases : IO Unit := do
  referenceChecks
  let saved ← generationChecks
  tamperingChecks saved
  shrinkChecks

end Tests.SourceModuleCases
