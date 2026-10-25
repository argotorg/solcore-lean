import Solcore.Synthesis.Source.ClosureCases

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
