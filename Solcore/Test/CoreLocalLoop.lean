import Solcore.Core.LocalLoop
import Solcore.Core.FuelResumptionProperties

/-! Loop helper tests cover actual shared mutation order, transfer propagation,
cyclic administrative cells, finite safety and an all-fuel nonterminating run.
Native Core stores intentionally include the helper's function cell. -/

set_option autoImplicit false

namespace Tests.CoreLocalLoop

open Solcore.Core

private def word (value : Nat) : Word := Word.ofNatModulo value
private def literal (value : Nat) : Expr := .word (word value)
private def scalar (value : Nat) : Value := .word (word value)
private def reason : Word := word 41
private def escaped : Word := word 42

/-- Outer scope is trace reference, then remaining-count reference. -/
private def condition : Expr := LanguageResult.success
  (.letE (.storeCell (.var 0) (.binary .wordAdd (.loadCell (.var 0)) (literal 1)))
    (.binary .wordGt (.loadCell (.var 2)) (literal 0)))

private def whileBody : Expr :=
  .letE (.storeCell (.var 1) (.binary .wordSub (.loadCell (.var 1)) (literal 1)))
    (.letE (.storeCell (.var 1) (.binary .wordAdd (.loadCell (.var 1)) (literal 10)))
      (LocalLoop.fallthrough .word))

private def continuedBody : Expr := LocalLoop.sequence .word
  (.letE (.storeCell (.var 0) (.binary .wordAdd (.loadCell (.var 0)) (literal 10)))
    (LocalLoop.continuing .word))
  (.letE (.storeCell (.var 0) (literal 999)) (LocalLoop.fallthrough .word))

private def post : Expr :=
  .letE (.storeCell (.var 1) (.binary .wordSub (.loadCell (.var 1)) (literal 1)))
    (.letE (.storeCell (.var 1) (.binary .wordAdd (.loadCell (.var 1)) (literal 100)))
      (LocalLoop.fallthrough .word))

private def program (testCondition body testPost : Expr) : Program := {
  resultType := LanguageResult.resultType .word
  body := .letE (.newCell .word (literal 3))
    (.letE (.newCell .word (literal 0))
      (LocalControl.finish .word
        (LocalControl.sequence .word
          (LocalLoop.toControl .word (LocalLoop.iterate .word testCondition body testPost reason) escaped)
          (LocalControl.returned (.loadCell (.var 0))))
        (LanguageResult.failure .word (.word reason))))
}

private def closure (testCondition body testPost : Expr) : Value :=
  LocalLoop.installedClosure .word testCondition body testPost reason 2
    [.cellRef .word 1, .cellRef .word 0]

private def whileProgram : Program := program condition whileBody (LocalLoop.fallthrough .word)
private def forProgram : Program := program condition continuedBody post

private theorem while_checked : whileProgram.check = true := by
  simp [whileProgram, program, condition, whileBody, LocalLoop.iterate, LocalLoop.loopBody,
    LocalLoop.conditional, LocalLoop.advance, LocalLoop.invoke, LocalLoop.fallthrough,
    LocalLoop.toControl, LocalLoop.resultType, LocalLoop.controlType, LocalLoop.transferType,
    LocalLoop.functionType, LocalLoop.returned, LocalControl.choose, LocalControl.finish,
    LocalControl.sequence, LocalControl.returned, LocalControl.controlType,
    OptionalCell.allocate, OptionalCell.read, OptionalCell.cellType, LanguageResult.bind,
    LanguageResult.success, LanguageResult.failure, Expr.weakenAt, literal]
  decide

private theorem for_checked : forProgram.check = true := by
  simp [forProgram, program, condition, continuedBody, post, LocalLoop.iterate, LocalLoop.loopBody,
    LocalLoop.sequence, LocalLoop.continuing, LocalLoop.conditional, LocalLoop.advance,
    LocalLoop.invoke, LocalLoop.fallthrough, LocalLoop.toControl, LocalLoop.resultType,
    LocalLoop.controlType, LocalLoop.transferType, LocalLoop.functionType, LocalLoop.returned,
    LocalControl.choose, LocalControl.finish, LocalControl.sequence, LocalControl.returned,
    LocalControl.controlType, OptionalCell.allocate, OptionalCell.read, OptionalCell.cellType,
    LanguageResult.bind, LanguageResult.success, LanguageResult.failure, Expr.weakenAt, literal]
  decide

set_option maxRecDepth 8192 in
/-- Four conditions and three bodies share the same trace cell: 4 + 3*10. -/
private theorem while_completed : whileProgram.runStateful 1500 =
    .done (.inRight .word (scalar 34))
      [scalar 0, scalar 34, .inRight .unit (closure condition whileBody (LocalLoop.fallthrough .word))] := by
  simp [whileProgram, program, condition, whileBody, closure, LocalLoop.installedClosure,
    LocalLoop.iterate, LocalLoop.loopBody, LocalLoop.conditional, LocalLoop.advance,
    LocalLoop.invoke, LocalLoop.fallthrough, LocalLoop.toControl, LocalLoop.resultType,
    LocalLoop.controlType, LocalLoop.transferType, LocalLoop.functionType, LocalLoop.returned,
    LocalControl.choose, LocalControl.finish, LocalControl.sequence, LocalControl.returned,
    LocalControl.controlType, OptionalCell.allocate, OptionalCell.read, OptionalCell.cellType,
    LanguageResult.bind, LanguageResult.success, LanguageResult.failure, Expr.weakenAt, literal]
  rfl

set_option maxRecDepth 8192 in
/-- Continue skips the body tail, then post runs before the next condition.
The trace records 4 + 3*10 + 3*100, and the counter reaches zero. -/
private theorem for_completed : forProgram.runStateful 2000 =
    .done (.inRight .word (scalar 334))
      [scalar 0, scalar 334, .inRight .unit (closure condition continuedBody post)] := by
  simp [forProgram, program, condition, continuedBody, post, closure, LocalLoop.installedClosure,
    LocalLoop.iterate, LocalLoop.loopBody, LocalLoop.sequence, LocalLoop.continuing,
    LocalLoop.conditional, LocalLoop.advance, LocalLoop.invoke, LocalLoop.fallthrough,
    LocalLoop.toControl, LocalLoop.resultType, LocalLoop.controlType, LocalLoop.transferType,
    LocalLoop.functionType, LocalLoop.returned, LocalControl.choose, LocalControl.finish,
    LocalControl.sequence, LocalControl.returned, LocalControl.controlType,
    OptionalCell.allocate, OptionalCell.read, OptionalCell.cellType, LanguageResult.bind,
    LanguageResult.success, LanguageResult.failure, Expr.weakenAt, literal]
  rfl

example (fuel : Nat) : (whileProgram.runStateful fuel).HasType whileProgram.resultType :=
  Program.checked_runStateful_has_type while_checked fuel

example (fuel : Nat) : (forProgram.runStateful fuel).HasType forProgram.resultType :=
  Program.checked_runStateful_has_type for_checked fuel

example (spent additional : Nat) (checkpoint : State)
    (exhausted : forProgram.runStateful spent = .outOfFuel checkpoint) :
    (runStateful additional checkpoint).HasType forProgram.resultType ∧
      runStateful additional checkpoint = forProgram.runStateful (spent + additional) :=
  well_typed_runStateful_resume_has_type
    (initial_state_has_type (Program.check_full_sound for_checked).bodyHasType) exhausted additional

example : ∃ required, ∀ fuel, required ≤ fuel → forProgram.runStateful fuel =
    .done (.inRight .word (scalar 334))
      [scalar 0, scalar 334, .inRight .unit (closure condition continuedBody post)] :=
  evaluation_runStateful_complete_with_sufficient_fuel (runStateful_evaluation_sound for_completed)

private def spinCondition : Expr := LanguageResult.success (.bool true)
private def spinBody : Expr := LocalLoop.continuing .unit
private def spinPost : Expr := LocalLoop.fallthrough .unit
private def spinProgram : Program := {
  resultType := LocalLoop.resultType .unit
  body := LocalLoop.iterate .unit spinCondition spinBody spinPost reason
}

private def spinState : State := .initial
  (LocalLoop.loopBody .unit spinCondition spinBody spinPost reason)
  [.unit, .cellRef (OptionalCell.cellType (LocalLoop.functionType .unit)) 0]
  [.inRight .unit (LocalLoop.installedClosure .unit spinCondition spinBody spinPost reason 0 [])]

private theorem spin_checked : spinProgram.check = true := by
  simp [spinProgram, spinCondition, spinBody, spinPost, LocalLoop.iterate, LocalLoop.loopBody,
    LocalLoop.conditional, LocalLoop.advance, LocalLoop.invoke, LocalLoop.fallthrough,
    LocalLoop.continuing, LocalLoop.resultType, LocalLoop.controlType, LocalLoop.transferType,
    LocalLoop.functionType, LocalLoop.returned, LocalControl.choose, LocalControl.controlType,
    OptionalCell.allocate, OptionalCell.read, OptionalCell.cellType, LanguageResult.bind,
    LanguageResult.success, LanguageResult.failure, Expr.weakenAt]
  decide

/-- Tail calls return to the exact same state, store and continuation. -/
private theorem spin_cycle : runStateful 53 spinState = .outOfFuel spinState := by
  simp [spinState, spinCondition, spinBody, spinPost, LocalLoop.installedClosure,
    LocalLoop.loopBody, LocalLoop.conditional, LocalLoop.advance, LocalLoop.invoke,
    LocalLoop.fallthrough, LocalLoop.continuing, LocalLoop.returned, LocalControl.choose,
    OptionalCell.read, LanguageResult.bind, LanguageResult.success, LanguageResult.failure, Expr.weakenAt]
  rfl

private theorem spin_reached : spinProgram.runStateful 31 = .outOfFuel spinState := by rfl

/-- A genuine exhaustion at a larger fuel budget excludes both completion and
fault at every smaller budget. This avoids enumerating a cycle's checkpoints. -/
private theorem exhaustion_prefix {spent fuel : Nat} {start suspended : State}
    (exhausted : runStateful spent start = .outOfFuel suspended) (smaller : fuel ≤ spent) :
    ∃ checkpoint, runStateful fuel start = .outOfFuel checkpoint := by
  cases outcome : runStateful fuel start with
  | done value store =>
      obtain ⟨cost, enough, path⟩ := runStateful_sound outcome
      have completed := runStateful_complete_with_fuel path (Nat.le_trans enough smaller)
      rw [completed] at exhausted
      cases exhausted
  | fault error state =>
      obtain ⟨cost, enough, path, terminal⟩ := runStateful_fault_sound outcome
      have fault := runStateful_fault_complete_of_steps path terminal (Nat.le_trans enough smaller)
      rw [fault] at exhausted
      cases exhausted
  | outOfFuel checkpoint => exact ⟨checkpoint, rfl⟩

private theorem spinState_exhausts (fuel : Nat) :
    ∃ checkpoint, runStateful fuel spinState = .outOfFuel checkpoint := by
  induction fuel using Nat.strongRecOn with
  | ind fuel inductionHypothesis =>
      by_cases short : fuel < 53
      · exact exhaustion_prefix spin_cycle (by omega)
      · obtain ⟨checkpoint, exhausted⟩ := inductionHypothesis (fuel - 53) (by omega)
        have resumed := runStateful_resume spin_cycle (fuel - 53)
        have total : 53 + (fuel - 53) = fuel := by omega
        rw [total] at resumed
        exact ⟨checkpoint, resumed.symm.trans exhausted⟩

private theorem spinProgram_exhausts (fuel : Nat) :
    ∃ checkpoint, spinProgram.runStateful fuel = .outOfFuel checkpoint := by
  by_cases short : fuel < 31
  · exact exhaustion_prefix spin_reached (by omega)
  · obtain ⟨checkpoint, exhausted⟩ := spinState_exhausts (fuel - 31)
    have resumed := runStateful_resume spin_reached (fuel - 31)
    have total : 31 + (fuel - 31) = fuel := by omega
    rw [total] at resumed
    exact ⟨checkpoint, resumed.symm.trans exhausted⟩

/-- The all-fuel claim follows from the machine cycle, rather than sampled
timeouts. Each retained state is typed with the cyclic optional-function cell. -/
example (fuel : Nat) : ∃ checkpoint,
    spinProgram.runStateful fuel = .outOfFuel checkpoint ∧
      StateHasType checkpoint spinProgram.resultType := by
  obtain ⟨checkpoint, exhausted⟩ := spinProgram_exhausts fuel
  exact ⟨checkpoint, exhausted, well_typed_runStateful_preserves_checkpoint_type
    (initial_state_has_type (Program.check_full_sound spin_checked).bodyHasType) exhausted⟩

example {value : Value} {store : Store}
    (evaluation : Evaluates [] [] spinProgram.body value store) : False := by
  obtain ⟨required, completes⟩ := evaluation_runStateful_complete_with_sufficient_fuel evaluation
  obtain ⟨checkpoint, exhausted⟩ := spinProgram_exhausts required
  change runStateful required (State.initial spinProgram.body) = .outOfFuel checkpoint at exhausted
  rw [completes required (by omega)] at exhausted
  cases exhausted

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def expect (testCondition body testPost : Expr) (value : Value)
    (remaining trace : Nat) (message : String) : IO Unit := do
  let fixture := program testCondition body testPost
  assertTrue fixture.check s!"{message}: checker"
  assertTrue (fixture.runStateful 2500 == .done value
    [scalar remaining, scalar trace, .inRight .unit (closure testCondition body testPost)]) message

def run : IO Unit := do
  expect condition whileBody (LocalLoop.fallthrough .word) (.inRight .word (scalar 34)) 0 34
    "while condition/body order or shared count"
  expect condition continuedBody post (.inRight .word (scalar 334)) 0 334
    "for continue must run post before condition"
  let breakBody := .letE (.storeCell (.var 0) (literal 11)) (LocalLoop.breaking .word)
  expect condition breakBody post (.inRight .word (scalar 11)) 3 11
    "break must skip post and continue outside the loop"
  let returnBody := .letE (.storeCell (.var 0) (literal 11)) (LocalLoop.returned (literal 7))
  expect condition returnBody post (.inRight .word (scalar 7)) 3 11
    "return must skip post, next condition and outer tail"
  let failureBody := LanguageResult.failure (LocalLoop.controlType .word)
    (.letE (.storeCell (.var 0) (literal 11)) (.word reason))
  expect condition failureBody post (.inLeft .word (.word reason)) 3 11
    "body failure must retain effects and skip post"
  let failureCondition := LanguageResult.failure .bool
    (.letE (.storeCell (.var 0) (literal 11)) (.word reason))
  expect failureCondition continuedBody post (.inLeft .word (.word reason)) 3 11
    "condition failure must skip body and post"
  let failurePost := LanguageResult.failure (LocalLoop.controlType .word)
    (.letE (.storeCell (.var 0) (literal 111)) (.word reason))
  expect condition continuedBody failurePost (.inLeft .word (.word reason)) 3 111
    "post failure must skip the next condition"
  let breakPost := .letE (.storeCell (.var 0) (literal 111)) (LocalLoop.breaking .word)
  expect condition continuedBody breakPost (.inRight .word (scalar 111)) 3 111
    "total helper handling consumes post break"
  let returnPost := .letE (.storeCell (.var 0) (literal 111)) (LocalLoop.returned (literal 7))
  expect condition continuedBody returnPost (.inRight .word (scalar 7)) 3 111
    "total helper handling propagates post return"

end Tests.CoreLocalLoop
