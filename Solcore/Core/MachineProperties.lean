import Solcore.Core.Machine

set_option autoImplicit false

namespace Solcore.Core

theorem advance_next_iff {state next : State} :
    advance state = .next next ↔ Transition state next := by
  constructor
  · intro advanced
    rcases state with ⟨control, continuation⟩
    cases control with
    | eval expr environment =>
        cases expr with
        | unit =>
            simp [advance] at advanced
            cases advanced
            exact .unit
        | bool value =>
            simp [advance] at advanced
            cases advanced
            exact .bool
        | word value =>
            simp [advance] at advanced
            cases advanced
            exact .word
        | var index =>
            cases lookup : environment[index]? with
            | none => simp [advance, lookup] at advanced
            | some value =>
                simp [advance, lookup] at advanced
                cases advanced
                exact .var lookup
        | unary op operand =>
            simp [advance] at advanced
            cases advanced
            exact .enterUnary
        | binary op left right =>
            simp [advance] at advanced
            cases advanced
            exact .enterBinary
        | letE value body =>
            simp [advance] at advanced
            cases advanced
            exact .enterLet
        | ifE condition thenBranch elseBranch =>
            simp [advance] at advanced
            cases advanced
            exact .enterIf
    | ret value =>
        cases continuation with
        | nil => simp [advance] at advanced
        | cons frame continuation =>
            cases frame with
            | unaryApply op =>
                cases applied : op.apply value with
                | none => simp [advance, applied] at advanced
                | some result =>
                    simp [advance, applied] at advanced
                    cases advanced
                    exact .applyUnary applied
            | binaryRight op right environment =>
                simp [advance] at advanced
                cases advanced
                exact .enterBinaryRight
            | binaryApply op leftValue =>
                cases applied : op.apply leftValue value with
                | none => simp [advance, applied] at advanced
                | some result =>
                    simp [advance, applied] at advanced
                    cases advanced
                    exact .applyBinary applied
            | letBody body environment =>
                simp [advance] at advanced
                cases advanced
                exact .bindLet
            | ifBranches thenBranch elseBranch environment =>
                cases value with
                | unit => simp [advance] at advanced
                | word value => simp [advance] at advanced
                | bool decision =>
                    cases decision with
                    | false =>
                        simp [advance] at advanced
                        cases advanced
                        exact .chooseFalse
                    | true =>
                        simp [advance] at advanced
                        cases advanced
                        exact .chooseTrue
  · intro transition
    cases transition <;> simp [advance, *]

theorem advance_done_iff {state : State} {value : Value} :
    advance state = .done value ↔ state = State.final value := by
  constructor
  · intro advanced
    rcases state with ⟨control, continuation⟩
    cases control with
    | eval expr environment =>
        cases expr with
        | unit | bool | word | unary | binary | letE | ifE => simp [advance] at advanced
        | var index =>
            cases lookup : environment[index]? <;> simp [advance, lookup] at advanced
    | ret returned =>
        cases continuation with
        | nil =>
            simp [advance] at advanced
            cases advanced
            rfl
        | cons frame continuation =>
            cases frame with
            | unaryApply op =>
                cases applied : op.apply returned <;>
                  simp [advance, applied] at advanced
            | binaryRight op right environment =>
                simp [advance] at advanced
            | binaryApply op leftValue =>
                cases applied : op.apply leftValue returned <;>
                  simp [advance, applied] at advanced
            | letBody body environment => simp [advance] at advanced
            | ifBranches thenBranch elseBranch environment =>
                cases returned with
                | unit | word => simp [advance] at advanced
                | bool decision =>
                    cases decision <;> simp [advance] at advanced
  · intro final
    subst state
    simp [advance, State.final]

theorem transition_deterministic
    {state left right : State}
    (leftStep : Transition state left)
    (rightStep : Transition state right) :
    left = right := by
  rw [← advance_next_iff] at leftStep rightStep
  rw [leftStep] at rightStep
  cases rightStep
  rfl

theorem run_sound
    {fuel : Nat} {state : State} {value : Value}
    (result : run fuel state = .done value) :
    ∃ steps, steps ≤ fuel ∧ Steps steps state (State.final value) := by
  induction fuel generalizing state value with
  | zero =>
      cases advanced : advance state with
      | next next =>
          rw [run, advanced] at result
          contradiction
      | fault error =>
          rw [run, advanced] at result
          contradiction
      | done returned =>
          have finalState := advance_done_iff.mp advanced
          rw [run, advanced] at result
          cases result
          subst state
          exact ⟨0, Nat.zero_le 0, .refl⟩
  | succ fuel fuelIH =>
      cases advanced : advance state with
      | fault error =>
          rw [run, advanced] at result
          contradiction
      | done returned =>
          have finalState := advance_done_iff.mp advanced
          rw [run, advanced] at result
          cases result
          subst state
          exact ⟨0, Nat.zero_le _, .refl⟩
      | next next =>
          have tailResult : run fuel next = .done value := by
            rw [run, advanced] at result
            exact result
          obtain ⟨steps, bounded, path⟩ := fuelIH tailResult
          exact ⟨steps + 1, Nat.succ_le_succ bounded,
            .cons (advance_next_iff.mp advanced) path⟩

theorem run_complete_of_steps
    {steps fuel : Nat} {state finish : State} {value : Value}
    (path : Steps steps state finish)
    (terminal : advance finish = .done value)
    (enough : steps ≤ fuel) :
    run fuel state = .done value := by
  induction path generalizing fuel value with
  | refl =>
      rw [run, terminal]
  | cons transition tail tailIH =>
      cases fuel with
      | zero => simp at enough
      | succ fuel =>
          have advanced := advance_next_iff.mpr transition
          rw [run, advanced]
          exact tailIH terminal (Nat.le_of_succ_le_succ enough)

theorem run_complete_with_fuel
    {steps fuel : Nat} {state : State} {value : Value}
    (path : Steps steps state (State.final value))
    (enough : steps ≤ fuel) :
    run fuel state = .done value :=
  run_complete_of_steps path (by simp [advance, State.final]) enough

end Solcore.Core
