import Solcore.Synthesis.Source.NestedLoopCases

/-! The `runtime-nested-loops` profile. Plans admit masks 0, 1 and 3 and three
inner-bound forms. The unrolled Core reference returns the accumulator of an
independent call-by-call loop specification over the step's original Core,
which also gives every recorded iteration count, at most three outer
iterations, three inner iterations in each and nine step calls. Generation
draws all twelve shapes, excludes boundary identities and replays exactly;
tampering is refused, and reductions lower masks, replace the inner bound or
the input and stay strictly smaller. -/
set_option autoImplicit false

namespace Tests.SourceNestedLoopCases

open Lean
open Solcore.Core (Word)
open Solcore.Synthesis.Core
open Solcore.Synthesis.Core.NestedLoop (CheckedPlan Bound)
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
  return case.setObjVal! "nestedLoopPlan" (change (← get (case.getObjVal? "nestedLoopPlan")))

private def withProvenance (case : Json) (change : Json → Json) : IO Json := do
  return case.setObjVal! "provenance" (change (← get (case.getObjVal? "provenance")))

/-- Masks 0, 1 and 3 are admitted for both loops; 2 and 7 are not. -/
private def admissionChecks (step : Aggregates.CheckedDAG) : IO Unit := do
  for outer in [0, 1, 3] do
    for inner in [0, 1, 3] do
      for bound in Bound.all do
        ensure (CheckedPlan.ofParts? step outer inner bound).isSome
          s!"masks {outer} and {inner} with bound {bound.name} were refused"
  for (outer, inner) in [(2, 1), (1, 2), (7, 3), (3, 7)] do
    ensure (CheckedPlan.ofParts? step outer inner .input).isNone s!"masks {outer} and {inner} were admitted"

/-- The wrapper's inner bound and both loops, for each form. -/
private def emitterChecks (step : Aggregates.CheckedDAG) : IO Unit := do
  for (bound, text) in [(Bound.input, "(sc_input & 3)"), (.counter, "((sc_i + 1) & 3)"),
      (.accumulator, "(sc_acc & 3)")] do
    let some plan := CheckedPlan.ofParts? step 1 3 bound | throw (IO.userError "plan refused")
    let source := (← get ((NestedLoop.emit plan).mapError reprStr)).source
    for line in ["        let sc_outer: word = (sc_input & 1);", "        while (sc_outer > sc_i) {",
        "            sc_inner = " ++ text ++ ";", "            sc_j = 0;", "            while (sc_inner > sc_j) {",
        "                sc_acc = sc_step(sc_acc);", "            sc_i = (sc_i + 1);"] do
      ensure ((source.splitOn line).length == 2) s!"{bound.name}: the wrapper lacks the line {line}"

/-- Every case's Core result equals the loop specification evaluated call by
call, which also gives its recorded iteration counts within the bounds. -/
private def referenceChecks (plan : CheckedPlan) (input : Word) (case : Json) : IO Unit := do
  let some (trips, accumulator) := NestedLoop.simulate plan input fuel |
    throw (IO.userError "a step call did not return a Word")
  ensure (accumulator == (← directWord case)) "the Core reference differs from the loop specification"
  ensure (trips.length == plan.outerTrips input && trips.length ≤ 3 && trips.all (· ≤ plan.inner) &&
      trips.foldl (· + ·) 0 ≤ 9) "iteration counts exceed the plan's bounds"
  match plan.bound with
  | .input => ensure (trips.all (· == (input.bitAnd (Word.ofNatModulo plan.inner)).val)) "input bound differs"
  | .counter =>
      ensure (trips == (List.range trips.length).map fun ordinal => (ordinal + 1) &&& plan.inner)
        "counter bound differs"
  | .accumulator => pure ()
  ensure ((← get ((← get (case.getObjVal? "provenance")).getObjVal? "iterations")) == toJson trips)
    "a case records other iteration counts"

private def generationChecks : IO Unit := do
  let corpus := NestedLoop.generateCases (Seed.ofNat 1) 384 1020 400 fuel .v4 .seeded
  ensure (corpus == NestedLoop.generateCases (Seed.ofNat 1) 384 1020 400 fuel .v4 .seeded)
    "nested loop generation is not deterministic"
  let generated ← cases corpus
  ensure (generated.size == 1020) "nested loop generation did not complete"
  let excluded ← get (corpus.getObjValAs? (Array Json) "excluded")
  for entry in excluded do
    let reason ← get (entry.getObjValAs? String "reason")
    ensure (reason == Acceptance.identityReason ||
        reason == "node budget is too small for the selected aggregate template or exceeds 512")
      s!"unexpected nested loop exclusion: {reason}"
  let mut shapes : List String := []
  let mut functions := 0
  for index in List.range (generated.size / 10) do
    let function := generated.extract (10 * index) (10 * index + 10)
    let some first := function[0]? | throw (IO.userError "empty function")
    let admitted ← get (NestedLoop.caseProgram first)
    let plan := admitted.plan
    shapes := (s!"{plan.outer}x{plan.inner}:{plan.bound.name}") :: shapes
    functions := functions + 1
    let mut identity := true
    for (case, position) in function.zipIdx do
      let input := (← get (NestedLoop.caseProgram case)).input
      referenceChecks plan input case
      if position < 6 && (← directWord case) != input then identity := false
    ensure (!identity) "a generated nested loop returned every boundary input"
  ensure (shapes.eraseDups.length == 12) s!"generation drew {shapes.eraseDups.length} of twelve shapes"
  ensure (functions == 102) "a function lost some of its inputs"

private def replayChecks (case : Json) : IO Unit := do
  ensure ((← get (NestedLoop.replayCase case fuel)) == case) "a nested loop case failed exact replay"
  let plan ← get (case.getObjVal? "nestedLoopPlan")
  let outer ← get (plan.getObjValAs? Nat "outerMask")
  let inner ← get (plan.getObjValAs? Nat "innerMask")
  let bound ← get (plan.getObjValAs? String "innerBound")
  for changed in [
      ← withPlan case (·.setObjVal! "outerMask" (toJson (if outer == 3 then 1 else 3))),
      ← withPlan case (·.setObjVal! "innerMask" (toJson (if inner == 3 then 1 else 3))),
      ← withPlan case (·.setObjVal! "innerBound" (toJson (if bound == "input" then "counter" else "input"))),
      ← withPlan case (·.setObjVal! "innerMask" (toJson (2 : Nat))),
      ← withProvenance case (·.setObjVal! "iterations" (toJson [9])),
      ← withProvenance case (·.setObjVal! "iterations" Json.null)] do
    ensure (NestedLoop.replayCase changed fuel matches .error _) "a tampered nested loop case replayed"

private def reductionChecks (case : Json) : IO Unit := do
  let source ← get (NestedLoop.caseProgram case)
  let mut lowered := false
  let mut rebound := false
  for reduced in NestedLoop.reductions source do
    let plan := reduced.candidate.plan
    ensure (plan.outer ≤ source.plan.outer && plan.inner ≤ source.plan.inner &&
        plan.step.helpers.length == source.plan.step.helpers.length)
      "a reduction raised a mask or changed the helper count"
    ensure ((complexity reduced.candidate.program.body).isStrictlySmaller (complexity source.program.body))
      "a reduction is not strictly smaller"
    if plan.outer < source.plan.outer || plan.inner < source.plan.inner then lowered := true
    if plan.bound == .input && source.plan.bound != .input then rebound := true
  ensure lowered "no reduction lowered a mask"
  ensure (rebound || source.plan.bound == .input) "no reduction replaced the inner bound by the input"
  let emitted ← cases (← get (NestedLoop.shrinkCases case 4 fuel))
  ensure (!emitted.isEmpty) "a nested loop case has no reduction"
  for candidate in emitted do
    ensure ((← get (NestedLoop.replayCase candidate fuel)) == candidate) "a reduction failed exact replay"

/-- An imported plan with an outer mask of zero runs no iteration. -/
private def importChecks (step : Aggregates.CheckedDAG) : IO Unit := do
  let some plan := CheckedPlan.ofParts? step 0 3 .accumulator | throw (IO.userError "plan refused")
  let case ← get (NestedLoop.emitCase plan (Word.ofNatModulo 3) (Json.mkObj [("kind", toJson "imported")]) fuel)
  ensure ((← directWord case) == Word.ofNatModulo 3) "a plan without outer iterations changed its input"
  ensure ((← get (NestedLoop.replayCase case fuel)) == case) "an imported nested loop case failed exact replay"

def testSourceNestedLoopCases : IO Unit := do
  let generated ← cases (NestedLoop.generateCases (Seed.ofNat 7) 384 6 16 fuel .v4)
  let some first := generated[0]? | throw (IO.userError "no nested loop case")
  let source ← get (NestedLoop.caseProgram first)
  admissionChecks source.plan.step
  emitterChecks source.plan.step
  importChecks source.plan.step
  generationChecks
  for case in generated do
    replayChecks case
  for case in generated.extract 0 4 do
    reductionChecks case

end Tests.SourceNestedLoopCases
