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
  | storageWrite
      {slot value : Word}
      {continuation : List Frame}
      {store : Store} :
      HostRequestEmission
        ⟨.ret (.pair (.word slot) (.word value)),
          .hostApply .storageWrite :: continuation, store⟩
        ⟨.storageWrite slot value, continuation, store⟩
  | storageAddress
      {continuation : List Frame}
      {store : Store} :
      HostRequestEmission
        ⟨.ret .unit, .hostApply .storageAddress :: continuation, store⟩
        ⟨.storageAddress, continuation, store⟩
  | codeAddress
      {continuation : List Frame}
      {store : Store} :
      HostRequestEmission
        ⟨.ret .unit, .hostApply .codeAddress :: continuation, store⟩
        ⟨.codeAddress, continuation, store⟩

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
      (∃ slot continuation store,
          state =
            ⟨.ret (.word slot),
              .hostApply .storageRead :: continuation, store⟩ ∧
          suspension = ⟨.storageRead slot, continuation, store⟩) ∨
        (∃ slot value continuation store,
            state =
              ⟨.ret (.pair (.word slot) (.word value)),
                .hostApply .storageWrite :: continuation, store⟩ ∧
            suspension = ⟨.storageWrite slot value, continuation, store⟩) ∨
          (∃ continuation store,
              state =
                ⟨.ret .unit,
                  .hostApply .storageAddress :: continuation, store⟩ ∧
              suspension = ⟨.storageAddress, continuation, store⟩) ∨
            ∃ continuation store,
              state =
                ⟨.ret .unit,
                  .hostApply .codeAddress :: continuation, store⟩ ∧
              suspension = ⟨.codeAddress, continuation, store⟩ := by
  constructor
  · intro emission
    cases emission with
    | storageRead => exact .inl ⟨_, _, _, rfl, rfl⟩
    | storageWrite => exact .inr (.inl ⟨_, _, _, _, rfl, rfl⟩)
    | storageAddress => exact .inr (.inr (.inl ⟨_, _, rfl, rfl⟩))
    | codeAddress => exact .inr (.inr (.inr ⟨_, _, rfl, rfl⟩))
  · rintro (⟨slot, continuation, store, rfl, rfl⟩ |
        ⟨slot, value, continuation, store, rfl, rfl⟩ |
        ⟨continuation, store, rfl, rfl⟩ |
        ⟨continuation, store, rfl, rfl⟩)
    · exact .storageRead
    · exact .storageWrite
    · exact .storageAddress
    · exact .codeAddress

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
              cases function with
              | storageRead =>
                  cases value <;> simp [hostAdvance] at advanced
              | storageWrite =>
                  cases value with
                  | pair left right =>
                      cases left <;> cases right <;>
                        simp [hostAdvance] at advanced
                  | unit | bool | word | hostFunction | closure | inLeft |
                      inRight | cellRef | constructed =>
                      simp [hostAdvance] at advanced
              | storageAddress =>
                  cases value <;> simp [hostAdvance] at advanced
              | codeAddress =>
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
              cases function with
              | storageRead =>
                  cases value with
                  | word slot =>
                      injection advanced with suspensionEquality
                      cases suspensionEquality
                      exact .storageRead
                  | unit | bool | hostFunction | pair | closure | inLeft |
                      inRight | cellRef | constructed =>
                      simp at advanced
              | storageWrite =>
                  cases value with
                  | pair left right =>
                      cases left <;> cases right <;>
                        simp at advanced
                      case word.word slot value =>
                        cases advanced
                        exact .storageWrite
                  | unit | bool | word | hostFunction | closure | inLeft |
                      inRight | cellRef | constructed =>
                      simp at advanced
              | storageAddress =>
                  cases value with
                  | unit =>
                      cases advanced
                      exact .storageAddress
                  | bool | word | hostFunction | pair | closure | inLeft |
                      inRight | cellRef | constructed =>
                      simp at advanced
              | codeAddress =>
                  cases value with
                  | unit =>
                      cases advanced
                      exact .codeAddress
                  | bool | word | hostFunction | pair | closure | inLeft |
                      inRight | cellRef | constructed =>
                      simp at advanced
  · intro emission
    cases emission <;> rfl

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
