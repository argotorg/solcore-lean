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
  | callValue
      {continuation : List Frame}
      {store : Store} :
      HostRequestEmission
        ⟨.ret .unit, .hostApply .callValue :: continuation, store⟩
        ⟨.callValue, continuation, store⟩
  | callerAddress
      {continuation : List Frame}
      {store : Store} :
      HostRequestEmission
        ⟨.ret .unit, .hostApply .callerAddress :: continuation, store⟩
        ⟨.callerAddress, continuation, store⟩
  | inputDataByte?
      {offset : Word}
      {continuation : List Frame}
      {store : Store} :
      HostRequestEmission
        ⟨.ret (.word offset), .hostApply .inputDataByte? :: continuation, store⟩
        ⟨.inputDataByte? offset, continuation, store⟩
  | inputDataSize
      {continuation : List Frame}
      {store : Store} :
      HostRequestEmission
        ⟨.ret .unit, .hostApply .inputDataSize :: continuation, store⟩
        ⟨.inputDataSize, continuation, store⟩
  | inputDataWordBE?
      {offset : Word}
      {continuation : List Frame}
      {store : Store} :
      HostRequestEmission
        ⟨.ret (.word offset),
          .hostApply .inputDataWordBE? :: continuation, store⟩
        ⟨.inputDataWordBE? offset, continuation, store⟩
  | currentAddress
      {continuation : List Frame}
      {store : Store} :
      HostRequestEmission
        ⟨.ret .unit, .hostApply .currentAddress :: continuation, store⟩
        ⟨.currentAddress, continuation, store⟩
  | callContractWord
      {target input : Word}
      {continuation : List Frame}
      {store : Store} :
      HostRequestEmission
        ⟨.ret (.pair (.word target) (.word input)),
          .hostApply .callContractWord :: continuation, store⟩
        ⟨.callContractWord target input, continuation, store⟩
  | callContractWordWithValue
      {target value input : Word}
      {continuation : List Frame}
      {store : Store} :
      HostRequestEmission
        ⟨.ret
            (.pair (.word target) (.pair (.word value) (.word input))),
          .hostApply .callContractWordWithValue :: continuation, store⟩
        ⟨.callContractWordWithValue target value input,
          continuation, store⟩
  | createContractWord
      {templateId value input : Word}
      {continuation : List Frame}
      {store : Store} :
      HostRequestEmission
        ⟨.ret
            (.pair (.word templateId) (.pair (.word value) (.word input))),
          .hostApply .createContractWord :: continuation, store⟩
        ⟨.createContractWord templateId value input,
          continuation, store⟩

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
            (∃ continuation store,
                state =
                  ⟨.ret .unit,
                    .hostApply .codeAddress :: continuation, store⟩ ∧
                suspension = ⟨.codeAddress, continuation, store⟩) ∨
              (∃ continuation store,
                  state =
                    ⟨.ret .unit,
                      .hostApply .callValue :: continuation, store⟩ ∧
                  suspension = ⟨.callValue, continuation, store⟩) ∨
                (∃ continuation store,
                    state =
                      ⟨.ret .unit,
                        .hostApply .callerAddress :: continuation, store⟩ ∧
                    suspension = ⟨.callerAddress, continuation, store⟩) ∨
                  (∃ offset continuation store,
                      state =
                        ⟨.ret (.word offset),
                          .hostApply .inputDataByte? :: continuation, store⟩ ∧
                      suspension =
                        ⟨.inputDataByte? offset, continuation, store⟩) ∨
                    (∃ continuation store,
                        state =
                          ⟨.ret .unit,
                            .hostApply .inputDataSize :: continuation, store⟩ ∧
                        suspension =
                          ⟨.inputDataSize, continuation, store⟩) ∨
                      (∃ offset continuation store,
                          state =
                            ⟨.ret (.word offset),
                              .hostApply .inputDataWordBE? :: continuation, store⟩ ∧
                          suspension =
                            ⟨.inputDataWordBE? offset, continuation, store⟩) ∨
                        (∃ continuation store,
                            state =
                              ⟨.ret .unit,
                                .hostApply .currentAddress :: continuation, store⟩ ∧
                            suspension =
                              ⟨.currentAddress, continuation, store⟩) ∨
                          (∃ target input continuation store,
                              state =
                                ⟨.ret (.pair (.word target) (.word input)),
                                  .hostApply .callContractWord :: continuation,
                                  store⟩ ∧
                              suspension =
                                ⟨.callContractWord target input, continuation,
                                  store⟩) ∨
                            (∃ target value input continuation store,
                              state =
                                ⟨.ret
                                    (.pair (.word target)
                                      (.pair (.word value) (.word input))),
                                  .hostApply .callContractWordWithValue ::
                                    continuation, store⟩ ∧
                              suspension =
                                ⟨.callContractWordWithValue target value input,
                                  continuation, store⟩) ∨
                              ∃ templateId value input continuation store,
                                state =
                                  ⟨.ret
                                      (.pair (.word templateId)
                                        (.pair (.word value) (.word input))),
                                    .hostApply .createContractWord ::
                                      continuation, store⟩ ∧
                                suspension =
                                  ⟨.createContractWord templateId value input,
                                    continuation, store⟩ := by
  constructor
  · intro emission
    cases emission with
    | storageRead => exact .inl ⟨_, _, _, rfl, rfl⟩
    | storageWrite => exact .inr (.inl ⟨_, _, _, _, rfl, rfl⟩)
    | storageAddress => exact .inr (.inr (.inl ⟨_, _, rfl, rfl⟩))
    | codeAddress => exact .inr (.inr (.inr (.inl ⟨_, _, rfl, rfl⟩)))
    | callValue =>
        exact .inr (.inr (.inr (.inr (.inl ⟨_, _, rfl, rfl⟩))))
    | callerAddress =>
        exact .inr (.inr (.inr (.inr (.inr (.inl ⟨_, _, rfl, rfl⟩)))))
    | inputDataByte? =>
        exact
          .inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨_, _, _, rfl, rfl⟩))))))
    | inputDataSize =>
        exact
          .inr (.inr (.inr (.inr (.inr (.inr (.inr
            (.inl ⟨_, _, rfl, rfl⟩)))))))
    | inputDataWordBE? =>
        exact
          .inr (.inr (.inr (.inr (.inr (.inr (.inr
            (.inr (.inl ⟨_, _, _, rfl, rfl⟩))))))))
    | currentAddress =>
        exact
          .inr (.inr (.inr (.inr (.inr (.inr (.inr
            (.inr (.inr (.inl ⟨_, _, rfl, rfl⟩)))))))))
    | callContractWord =>
        exact
          .inr (.inr (.inr (.inr (.inr (.inr (.inr
            (.inr (.inr (.inr (.inl ⟨_, _, _, _, rfl, rfl⟩))))))))))
    | callContractWordWithValue =>
        exact
          .inr (.inr (.inr (.inr (.inr (.inr (.inr
            (.inr (.inr (.inr (.inr
              (.inl ⟨_, _, _, _, _, rfl, rfl⟩)))))))))))
    | createContractWord =>
        exact
          .inr (.inr (.inr (.inr (.inr (.inr (.inr
            (.inr (.inr (.inr (.inr
              (.inr ⟨_, _, _, _, _, rfl, rfl⟩)))))))))))
  · rintro (⟨slot, continuation, store, rfl, rfl⟩ |
        ⟨slot, value, continuation, store, rfl, rfl⟩ |
        ⟨continuation, store, rfl, rfl⟩ |
        ⟨continuation, store, rfl, rfl⟩ |
        ⟨continuation, store, rfl, rfl⟩ |
        ⟨continuation, store, rfl, rfl⟩ |
        ⟨offset, continuation, store, rfl, rfl⟩ |
        ⟨continuation, store, rfl, rfl⟩ |
        ⟨offset, continuation, store, rfl, rfl⟩ |
        ⟨continuation, store, rfl, rfl⟩ |
        ⟨target, input, continuation, store, rfl, rfl⟩ |
        ⟨target, value, input, continuation, store, rfl, rfl⟩ |
        ⟨templateId, value, input, continuation, store, rfl, rfl⟩)
    · exact .storageRead
    · exact .storageWrite
    · exact .storageAddress
    · exact .codeAddress
    · exact .callValue
    · exact .callerAddress
    · exact .inputDataByte?
    · exact .inputDataSize
    · exact .inputDataWordBE?
    · exact .currentAddress
    · exact .callContractWord
    · exact .callContractWordWithValue
    · exact .createContractWord

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
              | callValue =>
                  cases value <;> simp [hostAdvance] at advanced
              | callerAddress =>
                  cases value <;> simp [hostAdvance] at advanced
              | inputDataByte? =>
                  cases value <;> simp [hostAdvance] at advanced
              | inputDataSize =>
                  cases value <;> simp [hostAdvance] at advanced
              | inputDataWordBE? =>
                  cases value <;> simp [hostAdvance] at advanced
              | currentAddress =>
                  cases value <;> simp [hostAdvance] at advanced
              | callContractWord =>
                  cases value with
                  | pair left right =>
                      cases left <;> cases right <;>
                        simp [hostAdvance] at advanced
                  | unit | bool | word | hostFunction | closure | inLeft |
                      inRight | cellRef | constructed =>
                      simp [hostAdvance] at advanced
              | callContractWordWithValue =>
                  cases value with
                  | pair left right =>
                      cases left with
                      | word target =>
                          cases right with
                          | pair middle last =>
                              cases middle <;> cases last <;>
                                simp [hostAdvance] at advanced
                          | unit | bool | word | hostFunction | closure |
                              inLeft | inRight | cellRef | constructed =>
                              simp [hostAdvance] at advanced
                      | unit | bool | hostFunction | pair | closure | inLeft |
                          inRight | cellRef | constructed =>
                          simp [hostAdvance] at advanced
                  | unit | bool | word | hostFunction | closure | inLeft |
                      inRight | cellRef | constructed =>
                      simp [hostAdvance] at advanced
              | createContractWord =>
                  cases value with
                  | pair left right =>
                      cases left with
                      | word templateId =>
                          cases right with
                          | pair middle last =>
                              cases middle <;> cases last <;>
                                simp [hostAdvance] at advanced
                          | unit | bool | word | hostFunction | closure |
                              inLeft | inRight | cellRef | constructed =>
                              simp [hostAdvance] at advanced
                      | unit | bool | hostFunction | pair | closure | inLeft |
                          inRight | cellRef | constructed =>
                          simp [hostAdvance] at advanced
                  | unit | bool | word | hostFunction | closure | inLeft |
                      inRight | cellRef | constructed =>
                      simp [hostAdvance] at advanced
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
              | callValue =>
                  cases value with
                  | unit =>
                      cases advanced
                      exact .callValue
                  | bool | word | hostFunction | pair | closure | inLeft |
                      inRight | cellRef | constructed =>
                      simp at advanced
              | callerAddress =>
                  cases value with
                  | unit =>
                      cases advanced
                      exact .callerAddress
                  | bool | word | hostFunction | pair | closure | inLeft |
                      inRight | cellRef | constructed =>
                      simp at advanced
              | inputDataByte? =>
                  cases value with
                  | word offset =>
                      injection advanced with suspensionEquality
                      cases suspensionEquality
                      exact .inputDataByte?
                  | unit | bool | hostFunction | pair | closure | inLeft |
                      inRight | cellRef | constructed =>
                      simp at advanced
              | inputDataSize =>
                  cases value with
                  | unit =>
                      cases advanced
                      exact .inputDataSize
                  | bool | word | hostFunction | pair | closure | inLeft |
                      inRight | cellRef | constructed =>
                      simp at advanced
              | inputDataWordBE? =>
                  cases value with
                  | word offset =>
                      injection advanced with suspensionEquality
                      cases suspensionEquality
                      exact .inputDataWordBE?
                  | unit | bool | hostFunction | pair | closure | inLeft |
                      inRight | cellRef | constructed =>
                      simp at advanced
              | currentAddress =>
                  cases value with
                  | unit =>
                      cases advanced
                      exact .currentAddress
                  | bool | word | hostFunction | pair | closure | inLeft |
                      inRight | cellRef | constructed =>
                      simp at advanced
              | callContractWord =>
                  cases value with
                  | pair left right =>
                      cases left <;> cases right <;>
                        simp at advanced
                      case word.word target input =>
                        cases advanced
                        exact .callContractWord
                  | unit | bool | word | hostFunction | closure | inLeft |
                      inRight | cellRef | constructed =>
                      simp at advanced
              | callContractWordWithValue =>
                  cases value with
                  | pair left right =>
                      cases left with
                      | word target =>
                          cases right with
                          | pair middle last =>
                              cases middle <;> cases last <;>
                                simp at advanced
                              case word.word value input =>
                                cases advanced
                                exact .callContractWordWithValue
                          | unit | bool | word | hostFunction | closure |
                              inLeft | inRight | cellRef | constructed =>
                              simp at advanced
                      | unit | bool | hostFunction | pair | closure | inLeft |
                          inRight | cellRef | constructed =>
                          simp at advanced
                  | unit | bool | word | hostFunction | closure | inLeft |
                      inRight | cellRef | constructed =>
                      simp at advanced
              | createContractWord =>
                  cases value with
                  | pair left right =>
                      cases left with
                      | word templateId =>
                          cases right with
                          | pair middle last =>
                              cases middle <;> cases last <;>
                                simp at advanced
                              case word.word value input =>
                                cases advanced
                                exact .createContractWord
                          | unit | bool | word | hostFunction | closure |
                              inLeft | inRight | cellRef | constructed =>
                              simp at advanced
                      | unit | bool | hostFunction | pair | closure | inLeft |
                          inRight | cellRef | constructed =>
                          simp at advanced
                  | unit | bool | word | hostFunction | closure | inLeft |
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
