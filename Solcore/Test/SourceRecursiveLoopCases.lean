import Solcore.Synthesis.Source.RecursiveLoopCases

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
