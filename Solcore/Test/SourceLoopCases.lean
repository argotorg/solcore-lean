import Solcore.Synthesis.Source.LoopCases

/-! Loop case regressions cover the canonical reference, arbitrary step entry,
zero and positive iterations, provenance, resource exits and sealed reductions. -/
set_option autoImplicit false

namespace Tests.SourceLoopCases
open Lean Solcore.Core Solcore.Synthesis.Core Solcore.Synthesis.Source
open Solcore.Synthesis.Core.BoundedLoop (CheckedPlan)

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
  | none => throw (IO.userError "loop step fixture failed checked admission")
private def plan (step : Aggregates.CheckedDAG) (mask : Nat) : IO CheckedPlan :=
  match CheckedPlan.ofParts? step mask with
  | some value => pure value
  | none => throw (IO.userError "loop plan fixture failed checked admission")
private def imported (value : CheckedPlan) (input : Word) : IO Json :=
  get (Loop.emitCase value input (Json.mkObj [("kind", toJson "imported")]) 10000)
private def returned (value : Word) : Json := Json.mkObj [
  ("stage", toJson "execution"), ("status", toJson "returned"),
  ("word", toJson (toString value.val))]

/-- Every step call must allocate a fresh private cell. The arbitrary entry
subtracts one, so substituting the last helper would give the wrong recurrence. -/
private def privateStep : Wire.Expr :=
  .letE (.newCell .word (word 0))
    (.letE (.storeCell (.var 0) (.binary .wordAdd (.loadCell (.var 0)) (word 2)))
      (.binary .wordAdd (.var 2) (.loadCell (.var 1))))

private def referenceChecks : IO Unit := do
  let graph ← checked [privateStep] (.binary .wordSub entry (word 1))
  for mask in [0, 1, 3, 7] do
    let value ← plan graph mask
    ensure (Wire.programNodes (value.instantiate Word.zero) ==
      Wire.programNodes graph.program + BoundedLoop.appliedOverhead mask)
      "measured loop wrapper overhead did not match the complete reference"
    ensure (BoundedLoop.appliedOverhead mask == 14 + 12 * mask)
      "canonical loop guard skeleton changed unexpectedly"
    let mut source : Option String := none
    for input in Loop.boundaryInputs do
      let iterations := input.bitAnd (Word.ofNatModulo mask)
      ensure (Loop.observe value input 10000 == returned (input.add iterations))
        s!"loop index/entry/private-cell mismatch: mask {mask}, input {input.val}"
      let saved ← imported value input
      let current ← string saved "source"
      if let some previous := source then ensure (current == previous) "loop source depends on runtime input"
      source := some current
      let admitted ← get (Loop.caseProgram saved)
      ensure (admitted.program.check && admitted.input == input && admitted.plan.mask == mask)
        "loop case lost its checked canonical reference"
      ensure ((← get (Loop.replayCase saved 10000)) == saved) "imported loop did not replay"
      ensure ((← get (Loop.replayCase (saved.setObjVal! "directCore" (returned Word.zero)) 10000)) == saved)
        "loop replay trusted its stored expected result"
      let low ← get (Loop.replayCase saved 0)
      ensure ((← string (← field low "directCore") "status") == "out-of-fuel")
        "loop fuel exhaustion was treated as completion"
  let identity ← checked [.var 0]
  let identityPlan ← plan identity 7
  ensure (!(Loop.inputSensitive identityPlan 10000).isOk)
    "zero-iteration input differences allowed an identity loop through the filter"
  let constant ← checked [word 4]
  let constantPlan ← plan constant 7
  ensure (!(Loop.inputSensitive constantPlan 10000).isOk)
    "generated loop lost the step's input-sensitive requirement"
  let zero ← plan graph 0
  ensure (!(Loop.inputSensitive zero 10000).isOk) "generated mask-zero loop passed nontriviality"
  ensure ((Loop.checkedPlan (Loop.planJson zero)).isOk) "imported mask-zero loop was rejected"
  ensure ((CheckedPlan.ofParts? graph 2).isNone) "non-mask loop bound was admitted"

private def minimumBudget (seed : Nat) : IO Nat := do
  for nodes in List.range 513 do
    if (Loop.generatedPlan (Seed.ofNat seed) nodes).isOk then return nodes
  throw (IO.userError "loop skeleton did not fit the case node limit")

private def generationChecks : IO Json := do
  -- All joint helper/template/mask residues have a bounded, fully checked skeleton.
  for seed in List.range 36 do
    let budget ← minimumBudget seed
    ensure (budget ≤ 384) "default loop budget cannot hold a selected template skeleton"
    let (value, _) ← get (Loop.generatedPlan (Seed.ofNat seed) budget)
    ensure (Wire.programNodes (value.instantiate Word.zero) ≤ budget &&
      value.mask == Loop.maskFor (Seed.ofNat seed) && value.step.helpers.length == 1 + seed % 3)
      "loop generation escaped its full node, mask or helper constraints"
    ensure (!(Loop.generatedPlan (Seed.ofNat seed) (budget - 1)).isOk &&
      !(Loop.generatedPlan (Seed.ofNat seed) 513).isOk) "loop node bounds were not enforced"
  let corpus := Loop.generateCases (Seed.ofNat 0) 384 12 512 10000
  ensure (corpus == Loop.generateCases (Seed.ofNat 0) 384 12 512 10000)
    "loop generation is nondeterministic"
  let rows ← cases corpus
  ensure (rows.size == 12 && (← natural corpus "attempted") ≤ 512)
    "bounded loop generation did not complete"
  for (row, index) in rows.toList.zipIdx do
    let admitted ← get (Loop.caseProgram row)
    ensure (Wire.programNodes admitted.program ≤ 384 &&
      some admitted.input == Loop.boundaryInputs[index % 6]?) "loop generation changed boundary order/budget"
    ensure ((← get (Loop.replayCase row 10000)) == row) "generated loop provenance did not replay"
    let low ← get (Loop.replayCase row 0)
    ensure ((← string (← field low "directCore") "status") == "out-of-fuel")
      "fresh loop observation fuel changed saved validation fuel"
  let saved := rows[5]!
  let origin ← field (← field saved "provenance") "origin"
  let seedText ← string origin "seed"
  let some seed := seedText.toNat? | throw (IO.userError "invalid generated seed")
  let low := Loop.generateCases (Seed.ofNat seed) 384 1 1 0
  let excluded ← get (low.getObjValAs? (Array Json) "excluded")
  ensure ((← string excluded[0]! "category") == "inconclusive-resource")
    "loop generation fuel exhaustion was classified as a semantic exclusion"
  ensure ((← cases (Loop.generateCases (Seed.ofNat seed) 384 5 1 10000)).size == 5 &&
    (← string (Loop.generateCases (Seed.ofNat seed) 384 7 1 10000) "status") == "generation-exhausted")
    "loop count/attempt limits did not distinguish cases from function candidates"
  ensure ((← natural (Loop.generateCases (Seed.ofNat seed) 384 0 100 10000) "attempted") == 0 &&
    (← cases (Loop.generateCases (Seed.ofNat seed) 384 1 0 10000)).isEmpty)
    "empty loop generation budgets consumed work"
  return saved

private def tamperingChecks (saved : Json) : IO Unit := do
  let provenance ← field saved "provenance"
  let origin ← field provenance "origin"
  let withOrigin := fun changed => saved.setObjVal! "provenance" (provenance.setObjVal! "origin" changed)
  for name in ["generatorVersion", "profileVersion", "functionVersion", "templateVersion",
      "stepProfileVersion", "stepFunctionVersion", "stepTemplateVersion", "emitterVersion", "wrapperVersion"] do
    rejected (Loop.replayCase (saved.setObjVal! "provenance"
      (provenance.setObjVal! name (toJson "forged"))) 10000) "tampered loop version accepted"
  for (name, value) in [("seed", toJson "00"), ("finalSeed", toJson "forged"),
      ("maxProgramNodes", toJson (513 : Nat)), ("mask", toJson (0 : Nat)),
      ("stepOrigin", Json.null), ("inputIndex", toJson (6 : Nat)),
      ("validationFuel", toJson (10000001 : Nat)), ("validationFuel", toJson (0 : Nat))] do
    rejected (Loop.replayCase (withOrigin (origin.setObjVal! name value)) 10000)
      s!"tampered loop {name} accepted"
  let stepOrigin ← field origin "stepOrigin"
  for name in ["seed", "finalSeed", "maxProgramNodes", "helpers", "helperCount"] do
    rejected (Loop.replayCase (withOrigin (origin.setObjVal! "stepOrigin"
      (stepOrigin.setObjVal! name Json.null))) 10000) "tampered nested step recipe accepted"
  let admitted ← get (Loop.caseProgram saved)
  let wrongProgram := Wire.encodeProgram (admitted.plan.step.instantiate admitted.input)
  for kind in ["imported", "reduced", "loop-generated"] do
    let changed := (withOrigin (origin.setObjVal! "kind" (toJson kind))).setObjVal! "program" wrongProgram
    rejected (Loop.caseProgram changed) "noncanonical program accepted under a different origin"
    rejected (Loop.replayCase changed 10000) "replay skipped canonical comparison for an origin"
  let loopPlan ← field saved "loopPlan"
  for (name, value) in [("mask", toJson (2 : Nat)), ("schema", toJson "unknown"),
      ("unexpected", toJson true)] do
    rejected (Loop.checkedPlan (loopPlan.setObjVal! name value)) "malformed loop plan accepted"
  rejected (Loop.caseProgram (saved.setObjVal! "input" (toJson "01"))) "noncanonical loop input accepted"
  rejected (Loop.caseProgram (saved.setObjVal! "input" (toJson "0"))) "input/reference mismatch accepted"
  rejected (Loop.replayCase (saved.setObjVal! "source" (toJson "stale")) 10000) "stale loop source accepted"
  let contract ← field saved "contract"
  rejected (Loop.replayCase (saved.setObjVal! "contract" (contract.setObjVal! "calldata" (toJson "0x"))) 10000)
    "wrong loop ABI input accepted"

private def shrinkChecks : IO Unit := do
  let graph ← checked [Aggregate.template 3 (word 2)]
  let value ← plan graph 7
  let saved ← imported value Word.maximum
  let original ← get (Loop.caseProgram saved)
  let shrunk ← get (Loop.shrinkCases saved 1000 10000)
  let rows ← cases shrunk
  ensure (!rows.isEmpty && shrunk == (← get (Loop.shrinkCases saved 1000 10000)))
    "loop shrinking was empty or nondeterministic"
  let mut seen : List String := []
  let mut inputReduced := false
  let mut maskReduced := false
  let mut stepReduced := false
  for row in rows do
    let candidate ← get (Loop.caseProgram row)
    ensure (candidate.program.check && candidate.plan.step.helpers.length == graph.helpers.length &&
      Aggregate.bindingInventory candidate.plan.step == Aggregate.bindingInventory graph &&
      candidate.plan.mask ≤ value.mask)
      "loop reduction lost a step binder/helper or enlarged its mask"
    ensure ((complexity candidate.program.body).isStrictlySmaller (complexity original.program.body))
      "loop reduction did not decrease the full original Core program"
    let key := (Wire.encodeProgram candidate.program).compress
    ensure (!seen.contains key) "loop reduction duplicated a canonical program"
    seen := key :: seen
    ensure ((← get (Loop.replayCase row 10000)) == row) "loop reduction did not replay"
    inputReduced := inputReduced || candidate.input != original.input
    maskReduced := maskReduced || candidate.plan.mask == 0
    stepReduced := stepReduced || Wire.encodeProgram candidate.plan.step.program != Wire.encodeProgram graph.program
  ensure (inputReduced && maskReduced && stepReduced) "loop reduction omitted input, zero-mask or step candidates"
  ensure ((← cases (← get (Loop.shrinkCases saved 2 10000))) == rows.extract 0 2 &&
    (← cases (← get (Loop.shrinkCases saved 0 10000))).isEmpty) "loop shrink limit changed ordering"

def testSourceLoopCases : IO Unit := do
  referenceChecks
  let saved ← generationChecks
  tamperingChecks saved
  shrinkChecks

end Tests.SourceLoopCases
