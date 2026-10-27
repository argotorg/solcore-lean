import Solcore.Synthesis.Source.RecursionCases

/-! The `runtime-recursion` profile. Plans admit depth masks 0, 1, 3 and 7 and
three forms. The unrolled Core reference returns what a recursive model of the
emitted source returns, frame by frame over the step's original Core, at
depth `input & mask`, at most seven frames deep. Generation draws all nine
shapes, excludes boundary identities and replays exactly; tampering is
refused, and reductions lower the mask, fall back to the tail form or move the
input and stay strictly smaller. -/
set_option autoImplicit false

namespace Tests.SourceRecursionCases

open Lean
open Solcore.Core (Word)
open Solcore.Synthesis.Core
open Solcore.Synthesis.Core.Recursion (CheckedPlan Form)
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
  return case.setObjVal! "recursionPlan" (change (← get (case.getObjVal? "recursionPlan")))

private def step (plan : CheckedPlan) (value : Word) : Option Word :=
  match (plan.step.instantiate value).toCore.runStateful fuel with
  | .done (.word result) _ => some result
  | _ => none

/-- `tail` and `nontail` frames: `f(d, acc)` as the emitted `sc_rec` computes it. -/
private def single (plan : CheckedPlan) (tail : Bool) : Nat → Word → Option Word
  | 0, accumulator => some accumulator
  | depth + 1, accumulator =>
      if tail then do single plan tail depth (← step plan accumulator)
      else do
        let inner ← single plan tail depth accumulator
        return Word.ofNatModulo ((← step plan inner).val + (depth + 1))

/-- `mutual` frames: `even` when `isEven`, as the emitted `sc_even` and `sc_odd` compute them. -/
private def alternating (plan : CheckedPlan) : Bool → Nat → Word → Option Word
  | _, 0, accumulator => some accumulator
  | true, depth + 1, accumulator => do alternating plan false depth (← step plan accumulator)
  | false, depth + 1, accumulator => alternating plan true depth (Word.ofNatModulo (accumulator.val + (depth + 1)))

private def model (plan : CheckedPlan) (input : Word) : Option Word :=
  match plan.form with
  | .tail => single plan true (plan.depth input) input
  | .nontail => single plan false (plan.depth input) input
  | .mutual => alternating plan true (plan.depth input) input

private def admissionChecks (step : Aggregates.CheckedDAG) : IO Unit := do
  for mask in [0, 1, 3, 7] do
    for form in Form.all do
      ensure (CheckedPlan.ofParts? step mask form).isSome s!"mask {mask} with form {form.name} was refused"
  for mask in [2, 5, 15] do
    ensure (CheckedPlan.ofParts? step mask .tail).isNone s!"mask {mask} was admitted"

/-- Each form's recursive calls and the wrapper's depth and entry. -/
private def emitterChecks (step : Aggregates.CheckedDAG) : IO Unit := do
  for (form, entry, lines) in [
      (Form.tail, "sc_rec", ["        sc_result = sc_rec((sc_depth - 1), sc_next);"]),
      (.nontail, "sc_rec", ["        let sc_inner: word = sc_rec((sc_depth - 1), sc_acc);",
        "        sc_result = (sc_stepped + sc_depth);"]),
      (.mutual, "sc_even", ["        sc_result = sc_odd((sc_depth - 1), sc_next);",
        "        let sc_next: word = (sc_acc + sc_depth);", "        sc_result = sc_even((sc_depth - 1), sc_next);"])] do
    let some plan := CheckedPlan.ofParts? step 7 form | throw (IO.userError "plan refused")
    let source := (← get ((Recursion.emit plan).mapError reprStr)).source
    for line in lines ++ ["        let sc_depth: word = (sc_input & 7);",
        "        let sc_out: word = " ++ entry ++ "(sc_depth, sc_input);"] do
      ensure ((source.splitOn line).length == 2) s!"{form.name}: the source lacks the line {line}"
    let functions := if form == .mutual then 2 else 1
    ensure ((source.splitOn "    if (sc_depth > 0) {").length == functions + 1)
      s!"{form.name}: the source does not test the depth once per recursive function"

private def generationChecks : IO Unit := do
  let corpus := Recursion.generateCases (Seed.ofNat 1) 384 1023 400 fuel .v4 .seeded
  ensure (corpus == Recursion.generateCases (Seed.ofNat 1) 384 1023 400 fuel .v4 .seeded)
    "recursion generation is not deterministic"
  let generated ← cases corpus
  ensure (generated.size == 1023) "recursion generation did not complete"
  let excluded ← get (corpus.getObjValAs? (Array Json) "excluded")
  for entry in excluded do
    let reason ← get (entry.getObjValAs? String "reason")
    ensure (reason == Acceptance.identityReason ||
        reason == "node budget is too small for the selected aggregate template or exceeds 512")
      s!"unexpected recursion exclusion: {reason}"
  let mut shapes : List String := []
  for index in List.range (generated.size / 11) do
    let function := generated.extract (11 * index) (11 * index + 11)
    let some first := function[0]? | throw (IO.userError "empty function")
    let plan := (← get (Recursion.caseProgram first)).plan
    shapes := s!"{plan.mask}:{plan.form.name}" :: shapes
    let mut identity := true
    for (case, position) in function.zipIdx do
      let input := (← get (Recursion.caseProgram case)).input
      let result ← directWord case
      ensure (plan.depth input ≤ 7) "a call recursed deeper than seven frames"
      ensure (model plan input == some result) "the Core reference differs from the recursive model"
      if position < 7 && result != input then identity := false
    ensure (!identity) "a generated recursion returned every boundary input"
  ensure (shapes.eraseDups.length == 9) s!"generation drew {shapes.eraseDups.length} of nine shapes"

private def replayChecks (case : Json) : IO Unit := do
  ensure ((← get (Recursion.replayCase case fuel)) == case) "a recursion case failed exact replay"
  let plan ← get (case.getObjVal? "recursionPlan")
  let mask ← get (plan.getObjValAs? Nat "depthMask")
  let form ← get (plan.getObjValAs? String "form")
  for changed in [
      ← withPlan case (·.setObjVal! "depthMask" (toJson (if mask == 7 then 3 else 7))),
      ← withPlan case (·.setObjVal! "depthMask" (toJson (5 : Nat))),
      ← withPlan case (·.setObjVal! "form" (toJson (if form == "tail" then "mutual" else "tail"))),
      ← withPlan case (·.setObjVal! "form" (toJson "loop"))] do
    ensure (Recursion.replayCase changed fuel matches .error _) "a tampered recursion case replayed"

private def reductionChecks (case : Json) : IO Unit := do
  let source ← get (Recursion.caseProgram case)
  let mut lowered := false
  let mut tail := false
  for reduced in Recursion.reductions source do
    let plan := reduced.candidate.plan
    ensure (plan.mask ≤ source.plan.mask && plan.step.helpers.length == source.plan.step.helpers.length)
      "a reduction raised the mask or changed the helper count"
    ensure (plan.form == source.plan.form || plan.form == .tail) "a reduction changed the form to another than tail"
    ensure ((complexity reduced.candidate.program.body).isStrictlySmaller (complexity source.program.body))
      "a reduction is not strictly smaller"
    if plan.mask < source.plan.mask then lowered := true
    if plan.form == .tail && source.plan.form != .tail then tail := true
  ensure lowered "no reduction lowered the mask"
  ensure (tail || source.plan.form == .tail) "no reduction fell back to the tail form"
  let emitted ← cases (← get (Recursion.shrinkCases case 4 fuel))
  ensure (!emitted.isEmpty) "a recursion case has no reduction"
  for candidate in emitted do
    ensure ((← get (Recursion.replayCase candidate fuel)) == candidate) "a reduction failed exact replay"

/-- An imported plan with a depth mask of zero never recurses. -/
private def importChecks (step : Aggregates.CheckedDAG) : IO Unit := do
  let some plan := CheckedPlan.ofParts? step 0 .mutual | throw (IO.userError "plan refused")
  let case ← get (Recursion.emitCase plan (Word.ofNatModulo 7) (Json.mkObj [("kind", toJson "imported")]) fuel)
  ensure ((← directWord case) == Word.ofNatModulo 7) "a plan of depth zero changed its input"
  ensure ((← get (Recursion.replayCase case fuel)) == case) "an imported recursion case failed exact replay"

def testSourceRecursionCases : IO Unit := do
  let generated ← cases (Recursion.generateCases (Seed.ofNat 2) 384 7 16 fuel .v4)
  let some first := generated[0]? | throw (IO.userError "no recursion case")
  let source ← get (Recursion.caseProgram first)
  admissionChecks source.plan.step
  emitterChecks source.plan.step
  importChecks source.plan.step
  generationChecks
  for case in generated do
    replayChecks case
  for case in generated.extract 1 5 do
    reductionChecks case

end Tests.SourceRecursionCases
