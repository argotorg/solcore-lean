import Solcore.Synthesis.Source.LoopClosureCases

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
