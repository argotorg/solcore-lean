import Solcore.Core.HostMachine
import Solcore.Core.MachineProperties

/-! Declarative one-step relations for the executable Core/host boundary. -/

set_option autoImplicit false

namespace Solcore.Core

/--
An ordinary step of the host-aware machine. Core transitions are preserved,
while applying a host function first evaluates its Core argument.
-/
inductive HostTransition : State → State → Prop where
  | core
      {state next : State}
      (step : Transition state next) :
      HostTransition state next
  | beginApplication
      {function : HostFunction}
      {argument : Expr}
      {environment : Environment}
      {continuation : List Frame}
      {store : Store} :
      HostTransition
        ⟨.ret (.hostFunction function),
          .applyArgument argument environment :: continuation, store⟩
        ⟨.eval argument environment,
          .hostApply function :: continuation, store⟩

/-- A state emits a particular first-order host request and suspension. -/
inductive HostRequestEmission : State → HostSuspension → Prop where
  | storageRead
      {slot : Word}
      {continuation : List Frame}
      {store : Store} :
      HostRequestEmission
        ⟨.ret (.word slot), .hostApply .storageRead :: continuation, store⟩
        ⟨.storageRead slot, continuation, store⟩

theorem hostTransition_iff
    {state next : State} :
    HostTransition state next ↔
      Transition state next ∨
        ∃ function argument environment continuation store,
          state =
            ⟨.ret (.hostFunction function),
              .applyArgument argument environment :: continuation, store⟩ ∧
          next =
            ⟨.eval argument environment,
              .hostApply function :: continuation, store⟩ := by
  constructor
  · intro step
    cases step with
    | core coreStep => exact .inl coreStep
    | beginApplication => exact .inr ⟨_, _, _, _, _, rfl, rfl⟩
  · rintro (coreStep | ⟨function, argument, environment, continuation,
        store, rfl, rfl⟩)
    · exact .core coreStep
    · exact .beginApplication

theorem hostRequestEmission_iff
    {state : State}
    {suspension : HostSuspension} :
    HostRequestEmission state suspension ↔
      ∃ slot continuation store,
        state =
          ⟨.ret (.word slot), .hostApply .storageRead :: continuation, store⟩ ∧
        suspension = ⟨.storageRead slot, continuation, store⟩ := by
  constructor
  · intro emission
    cases emission
    exact ⟨_, _, _, rfl, rfl⟩
  · rintro ⟨slot, continuation, store, rfl, rfl⟩
    exact .storageRead

@[simp] theorem HostAdvanceResult.ofAdvance_eq_next_iff
    {result : AdvanceResult}
    {next : State} :
    HostAdvanceResult.ofAdvance result = .next next ↔
      result = .next next := by
  cases result <;> simp

@[simp] theorem HostAdvanceResult.ofAdvance_ne_suspended
    (result : AdvanceResult)
    (suspension : HostSuspension) :
    HostAdvanceResult.ofAdvance result ≠ .suspended suspension := by
  cases result <;> simp

theorem hostAdvance_next_iff
    {state next : State} :
    hostAdvance state = .next next ↔ HostTransition state next := by
  constructor
  · intro advanced
    rcases state with ⟨control, continuation, store⟩
    cases control with
    | eval expr environment =>
        exact .core (advance_next_iff.mp (by simpa [hostAdvance] using advanced))
    | ret value =>
        cases continuation with
        | nil =>
            exact .core (advance_next_iff.mp (by simpa [hostAdvance] using advanced))
        | cons frame continuation =>
            cases frame <;>
              try
                exact .core
                  (advance_next_iff.mp (by simpa [hostAdvance] using advanced))
            case applyArgument argument environment =>
              cases value with
              | hostFunction function =>
                  cases advanced
                  exact .beginApplication
              | unit | bool | word | pair | closure | inLeft | inRight | cellRef |
                  constructed =>
                  exact .core
                    (advance_next_iff.mp (by simpa [hostAdvance] using advanced))
            case hostApply function =>
              cases function
              cases value <;> simp [hostAdvance] at advanced
  · intro step
    cases step with
    | beginApplication => rfl
    | core coreStep =>
        cases coreStep <;> simp [hostAdvance, advance, *]

theorem hostAdvance_suspended_iff
    {state : State}
    {suspension : HostSuspension} :
    hostAdvance state = .suspended suspension ↔
      HostRequestEmission state suspension := by
  constructor
  · intro advanced
    rcases state with ⟨control, continuation, store⟩
    cases control with
    | eval expr environment =>
        simp [hostAdvance] at advanced
    | ret value =>
        cases continuation with
        | nil =>
            simp [hostAdvance] at advanced
        | cons frame continuation =>
            cases frame <;> try simp [hostAdvance] at advanced
            case applyArgument argument environment =>
              cases value <;> simp at advanced
            case hostApply function =>
              cases function
              cases value with
              | word slot =>
                  injection advanced with suspensionEquality
                  cases suspensionEquality
                  exact .storageRead
              | unit | bool | hostFunction | pair | closure | inLeft | inRight |
                  cellRef | constructed =>
                  simp at advanced
  · intro emission
    cases emission
    rfl

theorem hostTransition_deterministic
    {state left right : State}
    (leftStep : HostTransition state left)
    (rightStep : HostTransition state right) :
    left = right := by
  rw [← hostAdvance_next_iff] at leftStep rightStep
  rw [leftStep] at rightStep
  cases rightStep
  rfl

theorem hostRequestEmission_deterministic
    {state : State}
    {left right : HostSuspension}
    (leftEmission : HostRequestEmission state left)
    (rightEmission : HostRequestEmission state right) :
    left = right := by
  rw [← hostAdvance_suspended_iff] at leftEmission rightEmission
  rw [leftEmission] at rightEmission
  cases rightEmission
  rfl

theorem hostTransition_requestEmission_disjoint
    {state next suspension}
    (step : HostTransition state next)
    (emission : HostRequestEmission state suspension) :
    False := by
  rw [← hostAdvance_next_iff] at step
  rw [← hostAdvance_suspended_iff] at emission
  rw [step] at emission
  contradiction

end Solcore.Core
