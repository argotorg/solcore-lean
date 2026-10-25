import Solcore.Synthesis.Source.ComptimeCases

/-! Comptime cases retain original constant and runtime ASTs, execute both
independently, reject changed provenance, and shrink either typed component. -/
set_option autoImplicit false

namespace Tests.SourceComptimeCases
open Lean Solcore.Core Solcore.Synthesis.Core Solcore.Synthesis.Source
open Solcore.Synthesis.Core.Comptime (CheckedPlan Variant)

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
  | none => throw (IO.userError "comptime step fixture failed checked admission")
private def constant (body : Wire.Expr) : IO CheckedWordProgram :=
  match CheckedWordProgram.ofProgram? {resultType := .word, dataDefinitions := [], body} with
  | some value => pure value
  | none => throw (IO.userError "constant fixture is not a checked closed G0 Word")
private def constantBody : Wire.Expr :=
  .letE (.binary .wordAdd (word 2) (word 3))
    (.ifE (.binary .wordGt (.var 0) (word 4))
      (.binary .wordMul (.var 0) (word 2)) (word 0))
private def plan (fixed : CheckedWordProgram) (step : Aggregates.CheckedDAG) (variant : Variant) : IO CheckedPlan :=
  match CheckedPlan.ofParts? fixed step variant with
  | some value => pure value
  | none => throw (IO.userError "comptime plan fixture failed checked admission")
private def imported (value : CheckedPlan) (input : Word) : IO Json :=
  get (Comptime.emitCase value input (Json.mkObj [("kind", toJson "imported")]) 10000)
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
  if variant == .offset then input.add (Word.ofNatModulo 21)
  else (input.mul (Word.ofNatModulo 11)).add (Word.ofNatModulo 21)

private def referenceChecks : IO Unit := do
  let fixed ← constant constantBody
  ensure (Solcore.Synthesis.Source.observe fixed 10000 == returned (Word.ofNatModulo 10))
    "independent closed constant golden failed"
  let graph ← checked [privateStep] (.binary .wordSub entry (word 1))
  for variant in [Variant.offset, .scale] do
    let value ← plan fixed graph variant
    ensure (Wire.programNodes (value.instantiate Word.zero) ==
      Wire.programNodes fixed.program + Wire.programNodes graph.program +
      Solcore.Synthesis.Core.Comptime.appliedOverhead variant)
      "comptime whole node budget omitted one original expression"
    let mut source : Option String := none
    for input in Comptime.boundaryInputs do
      ensure (Comptime.observe value input 10000 == returned (expected variant input))
        s!"comptime original-constant/entry mismatch: {variant.name}, input {input.val}"
      match (value.instantiate input).toCore.runStateful 10000 with
      | .done (.word _) store =>
          ensure (store == [.word (input.add (Word.ofNatModulo (if variant == .offset then 12 else 2)))])
            "comptime wrapper changed runtime step argument or called it more than once"
      | _ => throw (IO.userError "checked comptime reference did not return")
      let saved ← imported value input
      let current ← string saved "source"
      if let some previous := source then ensure (current == previous) "comptime source depends on runtime input"
      source := some current
      let admitted ← get (Comptime.caseProgram saved)
      ensure (admitted.program.check && admitted.input == input && admitted.plan.variant == variant &&
        Wire.encodeProgram admitted.plan.constant.program == Wire.encodeProgram fixed.program)
        "comptime case lost one original checked expression"
      ensure ((← get (Comptime.replayCase saved 10000)) == saved) "imported comptime case did not replay"
      ensure ((← get (Comptime.replayCase (saved.setObjVal! "directCore" (returned Word.zero)) 10000)) == saved)
        "comptime replay trusted its stored expected result"
      let low ← get (Comptime.replayCase saved 0)
      ensure ((← string (← field low "directCore") "status") == "out-of-fuel")
        "comptime fuel exhaustion was treated as completion"
  let identity ← checked [.var 0]
  let literal ← constant (word 4)
  let literalPlan ← plan literal identity .offset
  ensure (!(Comptime.inputSensitive literalPlan 10000).isOk)
    "generated constant without an operation was admitted"
  ensure ((Comptime.emitCase literalPlan Word.zero (Json.mkObj [("kind", toJson "imported")]) 10000).isOk)
    "imported literal constant should remain supported"
  let constantStep ← checked [word 4]
  let constantPlan ← plan fixed constantStep .scale
  ensure (!(Comptime.inputSensitive constantPlan 10000).isOk)
    "generated comptime plan lost the step's input-sensitive requirement"
  let wrapped ← constant (.binary .wordAdd (.word Word.maximum) (word 1))
  for variant in [Variant.offset, .scale] do
    let wrappedPlan ← plan wrapped identity variant
    for input in Comptime.boundaryInputs do
      ensure (Comptime.observe wrappedPlan input 10000 == returned input)
        "original constant Word overflow was not preserved"

private def minimumBudget (seed : Nat) : IO Nat := do
  for nodes in List.range 513 do
    if (Comptime.generatedPlan (Seed.ofNat seed) nodes).isOk then return nodes
  throw (IO.userError "comptime skeleton did not fit the case node limit")

private def generationChecks : IO Json := do
  -- All joint helper/template/variant residues have a bounded, fully checked skeleton.
  for seed in List.range 36 do
    let budget ← minimumBudget seed
    ensure (budget ≤ 384) "default comptime budget cannot hold a selected template skeleton"
    let (value, _) ← get (Comptime.generatedPlan (Seed.ofNat seed) budget)
    ensure (Wire.programNodes (value.instantiate Word.zero) ≤ budget &&
      value.variant == Comptime.variantFor (Seed.ofNat seed) && value.step.helpers.length == 1 + seed % 3)
      "comptime generation escaped its full node, variant or helper constraints"
    ensure (!(Comptime.generatedPlan (Seed.ofNat seed) (budget - 1)).isOk &&
      !(Comptime.generatedPlan (Seed.ofNat seed) 513).isOk) "comptime node bounds were not enforced"
  let corpus := Comptime.generateCases (Seed.ofNat 0) 384 8 512 10000
  ensure (corpus == Comptime.generateCases (Seed.ofNat 0) 384 8 512 10000)
    "comptime generation is nondeterministic"
  let rows ← cases corpus
  ensure (rows.size == 8 && (← natural corpus "attempted") ≤ 512)
    "bounded comptime generation did not complete"
  for (row, index) in rows.toList.zipIdx do
    let admitted ← get (Comptime.caseProgram row)
    ensure (Wire.programNodes admitted.program ≤ 384 &&
      some admitted.input == Comptime.boundaryInputs[index % 4]?) "comptime generation changed boundary order/budget"
    ensure ((← get (Comptime.replayCase row 10000)) == row) "generated comptime provenance did not replay"
    let low ← get (Comptime.replayCase row 0)
    ensure ((← string (← field low "directCore") "status") == "out-of-fuel")
      "fresh comptime observation fuel changed saved validation fuel"
  let saved := rows[3]!
  let origin ← field (← field saved "provenance") "origin"
  let seedText ← string origin "seed"
  let some seed := seedText.toNat? | throw (IO.userError "invalid generated seed")
  let low := Comptime.generateCases (Seed.ofNat seed) 384 1 1 0
  let excluded ← get (low.getObjValAs? (Array Json) "excluded")
  ensure ((← string excluded[0]! "category") == "inconclusive-resource")
    "comptime generation fuel exhaustion was classified as a semantic exclusion"
  ensure ((← cases (Comptime.generateCases (Seed.ofNat seed) 384 3 1 10000)).size == 3 &&
    (← string (Comptime.generateCases (Seed.ofNat seed) 384 5 1 10000) "status") == "generation-exhausted")
    "comptime count/attempt limits did not distinguish cases from function candidates"
  ensure ((← natural (Comptime.generateCases (Seed.ofNat seed) 384 0 100 10000) "attempted") == 0 &&
    (← cases (Comptime.generateCases (Seed.ofNat seed) 384 1 0 10000)).isEmpty)
    "empty comptime generation budgets consumed work"
  return saved

private def tamperingChecks (saved : Json) : IO Unit := do
  let provenance ← field saved "provenance"
  let origin ← field provenance "origin"
  let withOrigin := fun changed => saved.setObjVal! "provenance" (provenance.setObjVal! "origin" changed)
  for name in ["generatorVersion", "profileVersion", "functionVersion", "templateVersion",
      "stepProfileVersion", "stepFunctionVersion", "stepTemplateVersion", "emitterVersion", "wrapperVersion"] do
    rejected (Comptime.replayCase (saved.setObjVal! "provenance"
      (provenance.setObjVal! name (toJson "forged"))) 10000) "tampered comptime version accepted"
  for (name, value) in [("seed", toJson "00"), ("finalSeed", toJson "forged"),
      ("maxProgramNodes", toJson (513 : Nat)), ("variant", toJson "forged"),
      ("stepOrigin", Json.null), ("constantOrigin", Json.null), ("inputIndex", toJson (4 : Nat)),
      ("validationFuel", toJson (10000001 : Nat)), ("validationFuel", toJson (0 : Nat))] do
    rejected (Comptime.replayCase (withOrigin (origin.setObjVal! name value)) 10000)
      s!"tampered comptime {name} accepted"
  let stepOrigin ← field origin "stepOrigin"
  for name in ["seed", "finalSeed", "maxProgramNodes", "helpers", "helperCount"] do
    rejected (Comptime.replayCase (withOrigin (origin.setObjVal! "stepOrigin"
      (stepOrigin.setObjVal! name Json.null))) 10000) "tampered nested step recipe accepted"
  let constantOrigin ← field origin "constantOrigin"
  for name in ["kind", "seed", "finalSeed", "maxProgramNodes"] do
    rejected (Comptime.replayCase (withOrigin (origin.setObjVal! "constantOrigin"
      (constantOrigin.setObjVal! name Json.null))) 10000) "tampered constant recipe accepted"
  rejected (Comptime.replayCase (saved.setObjVal! "provenance"
    (provenance.setObjVal! "constantFeatures" (toJson ([] : List String)))) 10000)
    "tampered constant feature provenance accepted"
  let admitted ← get (Comptime.caseProgram saved)
  let wrongProgram := Wire.encodeProgram (admitted.plan.step.instantiate admitted.input)
  for kind in ["imported", "reduced", "comptime-generated"] do
    let changed := (withOrigin (origin.setObjVal! "kind" (toJson kind))).setObjVal! "program" wrongProgram
    rejected (Comptime.caseProgram changed) "noncanonical program accepted under a different origin"
    rejected (Comptime.replayCase changed 10000) "replay skipped canonical comparison for an origin"
  let comptimePlan ← field saved "comptimePlan"
  let changedConstant ← constant (word 17)
  rejected (Comptime.caseProgram (saved.setObjVal! "comptimePlan"
    (comptimePlan.setObjVal! "constantProgram" (Wire.encodeProgram changedConstant.program))))
    "changed constant program was not compared against the full original reference"
  let free : Wire.Program := {resultType := .word, dataDefinitions := [], body := .var 0}
  rejected (Comptime.checkedPlan (comptimePlan.setObjVal! "constantProgram" (Wire.encodeProgram free)))
    "constant captured an outer runtime input"
  for (name, value) in [("variant", toJson "unknown"), ("schema", toJson "unknown"),
      ("unexpected", toJson true)] do
    rejected (Comptime.checkedPlan (comptimePlan.setObjVal! name value)) "malformed comptime plan accepted"
  rejected (Comptime.caseProgram (saved.setObjVal! "input" (toJson "01"))) "noncanonical comptime input accepted"
  rejected (Comptime.caseProgram (saved.setObjVal! "input" (toJson "0"))) "input/reference mismatch accepted"
  rejected (Comptime.replayCase (saved.setObjVal! "source" (toJson "stale")) 10000) "stale comptime source accepted"
  let contract ← field saved "contract"
  rejected (Comptime.replayCase (saved.setObjVal! "contract" (contract.setObjVal! "calldata" (toJson "0x"))) 10000)
    "wrong comptime ABI input accepted"

private def shrinkChecks : IO Unit := do
  let graph ← checked [Aggregate.template 3 (word 2)]
  let fixed ← constant constantBody
  let value ← plan fixed graph .scale
  let saved ← imported value Word.maximum
  let original ← get (Comptime.caseProgram saved)
  let shrunk ← get (Comptime.shrinkCases saved 1000 10000)
  let rows ← cases shrunk
  ensure (!rows.isEmpty && shrunk == (← get (Comptime.shrinkCases saved 1000 10000)))
    "comptime shrinking was empty or nondeterministic"
  let mut seen : List String := []
  let mut inputReduced := false
  let mut stepReduced := false
  let mut constantReduced := false
  for row in rows do
    let candidate ← get (Comptime.caseProgram row)
    ensure (candidate.program.check && candidate.plan.step.helpers.length == graph.helpers.length &&
      Aggregate.bindingInventory candidate.plan.step == Aggregate.bindingInventory graph &&
      candidate.plan.variant == value.variant)
      "comptime reduction lost a step binder/helper or changed its comptime variant"
    ensure ((complexity candidate.program.body).isStrictlySmaller (complexity original.program.body))
      "comptime reduction did not decrease the full original Core program"
    let key := (Wire.encodeProgram candidate.program).compress
    ensure (!seen.contains key) "comptime reduction duplicated a canonical program"
    seen := key :: seen
    ensure ((← get (Comptime.replayCase row 10000)) == row) "comptime reduction did not replay"
    inputReduced := inputReduced || candidate.input != original.input
    constantReduced := constantReduced || Wire.encodeProgram candidate.plan.constant.program != Wire.encodeProgram fixed.program
    stepReduced := stepReduced || Wire.encodeProgram candidate.plan.step.program != Wire.encodeProgram graph.program
  ensure (inputReduced && stepReduced && constantReduced) "comptime reduction omitted constant, input or step candidates"
  ensure ((← cases (← get (Comptime.shrinkCases saved 2 10000))) == rows.extract 0 2 &&
    (← cases (← get (Comptime.shrinkCases saved 0 10000))).isEmpty) "comptime shrink limit changed ordering"
  let reduced := rows[0]!
  let candidate ← get (Comptime.caseProgram reduced)
  let provenance ← field reduced "provenance"
  let origin ← field provenance "origin"
  for (name, value) in [("parentProgram", Wire.encodeProgram candidate.program),
      ("parentInput", toJson "00"), ("extra", toJson true)] do
    rejected (Comptime.replayCase (reduced.setObjVal! "provenance"
      (provenance.setObjVal! "origin" (origin.setObjVal! name value))) 10000)
      "tampered reduction witness accepted"
  let sameParent := Json.mkObj [("kind", toJson "reduced"),
    ("parentProgram", Wire.encodeProgram candidate.program), ("parentPlan", Comptime.planJson candidate.plan),
    ("parentInput", toJson (toString candidate.input.val))]
  rejected (Comptime.replayCase (reduced.setObjVal! "provenance"
    (provenance.setObjVal! "origin" sameParent)) 10000) "non-strict reduction origin accepted"


def testSourceComptimeCases : IO Unit := do
  referenceChecks
  let saved ← generationChecks
  tamperingChecks saved
  shrinkChecks

end Tests.SourceComptimeCases
