import Solcore.Frontend.SourceRuntimeDeepValidation
import Solcore.Frontend.SourceTypedRuntime

/-! Legacy execution wrappers retain pure boundary certificates from
`SourceRuntimeDeepValidation` while runtime entry points migrate to Core. -/

set_option autoImplicit false
namespace Solcore.Frontend.SourceTypedRuntime
open SourceInference TypeSystem

private theorem boolOfNotNotTrue {value : Bool}
    (accepted : ¬ (!value) = true) : value = true := by
  cases value <;> simp_all

/-- Preserve the ordinary boundary's precise validation diagnostics before
running the stronger deep checks. -/
private def validateBoundaryInputs (signatures : ProgramSignatures)
    (plan : Plan) (fuel : Nat) : List Ty → List Value → Option RuntimeError
  | [], [] => none
  | expected :: expectedRest, actual :: actualRest =>
      match actual.validateTypeFuel fuel signatures plan expected with
      | .valid => validateBoundaryInputs signatures plan fuel expectedRest
          actualRest
      | .invalid => some (.typeMismatch expected (actual.type? plan))
      | .unsupportedStaged => some (.unsupportedStagedInput expected)
      | .outOfFuel => some (.inputValidationFuelExhausted expected fuel)
  | expected, actual =>
      some (.argumentArityMismatch expected.length actual.length)

/-- Execute only after validating the shallow input contract, prepared-plan
initial heap, and prepared-plan arguments.  Normal completion is exposed only
after validating the final heap and result against that same prepared plan. -/
def runDeepCertifiedWithValidationFuel (program : CheckedProgram) (plan : Plan)
    (entry : Key) (arguments : List Value)
    (validationFuel executionFuel : Nat)
    (initial : RuntimeState := {}) : RunResult :=
  match exactSpecialization plan entry with
  | .error error => .fault error initial
  | .ok specialized =>
      let argumentTypes := specialized.function.typedBody.inputs.map
        (·.scheme.body)
      match validateBoundaryInputs program.signatures plan validationFuel
          argumentTypes arguments with
      | some error => .fault error initial
      | none =>
          match prepareExecutablePlanEvidence program plan with
          | .error error => .fault error initial
          | .ok executablePlan =>
              if !initial.isDeeplySafe validationFuel program.signatures
                  executablePlan then
                .fault .deepSafetyInitialStateRejected initial
              else if !valuesDeeplySafe validationFuel program.signatures
                  executablePlan initial arguments argumentTypes then
                .fault .deepSafetyInputsRejected initial
              else
                match runWithValidationFuel program plan entry arguments
                    validationFuel executionFuel initial with
                | .outOfFuel state => .outOfFuel state
                | .fault error state => .fault error state
                | .done value finalState =>
                    if !finalState.isDeeplySafe validationFuel
                        program.signatures executablePlan then
                      .fault .deepSafetyFinalStateRejected finalState
                    else if !initial.typeLayoutExtends finalState then
                      .fault .deepSafetyFinalStateRejected finalState
                    else if !value.isDeeplySafe validationFuel
                        program.signatures executablePlan finalState
                        specialized.function.inferredBodyType then
                      .fault (.deepSafetyResultRejected
                        specialized.function.inferredBodyType
                        (value.type? executablePlan)) finalState
                    else
                      .done value finalState

/-- Successful certified execution retains executable preconditions and
postconditions against one deterministic prepared plan. -/
theorem runDeepCertifiedWithValidationFuel_done_certificate
    (program : CheckedProgram) (plan : Plan) (entry : Key)
    (arguments : List Value) (validationFuel executionFuel : Nat)
    (initial finalState : RuntimeState) (value : Value)
    (specialized : SourceSpecialization.SpecializedFunction)
    (exact : exactSpecialization plan entry = .ok specialized)
    (done : runDeepCertifiedWithValidationFuel program plan entry arguments
      validationFuel executionFuel initial = .done value finalState) :
    PreparedDeepExecution program plan
      (specialized.function.typedBody.inputs.map (·.scheme.body))
      specialized.function.inferredBodyType arguments initial value finalState := by
  unfold runDeepCertifiedWithValidationFuel at done
  rw [exact] at done
  simp only at done
  cases shallow : validateBoundaryInputs program.signatures plan validationFuel
      (specialized.function.typedBody.inputs.map (·.scheme.body)) arguments with
  | some error => simp [shallow] at done
  | none =>
      simp only [shallow] at done
      cases preparedResult : prepareExecutablePlanEvidence program plan with
      | error error => simp [preparedResult] at done
      | ok executablePlan =>
          simp only [preparedResult] at done
          split at done
          next initialRejected => contradiction
          next initialAccepted =>
            split at done
            next inputsRejected => contradiction
            next inputsAccepted =>
              cases underlying : runWithValidationFuel program plan entry
                  arguments validationFuel executionFuel initial with
              | outOfFuel state => simp [underlying] at done
              | fault error state => simp [underlying] at done
              | done actual actualState =>
                  simp only [underlying] at done
                  split at done
                  next finalRejected => contradiction
                  next finalAccepted =>
                    split at done
                    next layoutRejected => contradiction
                    next layoutAccepted =>
                      split at done
                      next resultRejected => contradiction
                      next resultAccepted =>
                        cases done
                        have planIdentity :
                            preparedDeepExecutablePlan program plan =
                              executablePlan := by
                          simp [preparedDeepExecutablePlan, preparedResult]
                        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
                        · simpa [planIdentity] using preparedResult
                        · rw [planIdentity]
                          apply RuntimeState.isDeeplySafe_sound
                          exact boolOfNotNotTrue initialAccepted
                        · rw [planIdentity]
                          apply valuesDeeplySafe_sound
                          exact boolOfNotNotTrue inputsAccepted
                        · rw [planIdentity]
                          apply RuntimeState.isDeeplySafe_sound
                          exact boolOfNotNotTrue finalAccepted
                        · apply RuntimeState.typeLayoutExtends_sound
                          exact boolOfNotNotTrue layoutAccepted
                        · rw [planIdentity]
                          apply Value.isDeeplySafe_sound
                          exact boolOfNotNotTrue resultAccepted

/-- Compatibility projection used by `SourceCompiler`: successful execution
always carries the complete post-execution certificate. -/
theorem runDeepCertifiedWithValidationFuel_done
    (program : CheckedProgram) (plan : Plan) (entry : Key)
    (arguments : List Value) (validationFuel executionFuel : Nat)
    (initial finalState : RuntimeState) (value : Value)
    (specialized : SourceSpecialization.SpecializedFunction)
    (exact : exactSpecialization plan entry = .ok specialized)
    (done : runDeepCertifiedWithValidationFuel program plan entry arguments
      validationFuel executionFuel initial = .done value finalState) :
    PreparedDeepResult program plan specialized.function.inferredBodyType value
      finalState := by
  have certificate := runDeepCertifiedWithValidationFuel_done_certificate
    program plan entry arguments validationFuel executionFuel initial finalState
    value specialized exact done
  exact ⟨certificate.prepared, certificate.final_state_safe,
    certificate.value_safe⟩

/-- A normal result has the established all-fuel pre/post heap invariants.
Every initialized cell, input, and result additionally carries the finite
checked-plan runtime-image and authenticated-evidence certificate. -/
theorem runDeepCertifiedWithValidationFuel_done_deep
    (program : CheckedProgram) (plan : Plan) (entry : Key)
    (arguments : List Value) (validationFuel executionFuel : Nat)
    (initial finalState : RuntimeState) (value : Value)
    (specialized : SourceSpecialization.SpecializedFunction)
    (exact : exactSpecialization plan entry = .ok specialized)
    (done : runDeepCertifiedWithValidationFuel program plan entry arguments
      validationFuel executionFuel initial = .done value finalState) :
    let executablePlan := preparedDeepExecutablePlan program plan
    initial.HasDeepTypes program.signatures executablePlan ∧
      (∀ cell, cell ∈ initial.heap → ∀ stored,
        cell.value = some stored →
          stored.HasValidCodeAndEvidence program.signatures executablePlan) ∧
      (∀ pair, pair ∈ List.zip
          (specialized.function.typedBody.inputs.map (·.scheme.body)) arguments →
        pair.2.HasDeepType program.signatures executablePlan initial pair.1 ∧
          pair.2.HasValidCodeAndEvidence program.signatures executablePlan) ∧
      finalState.HasDeepTypes program.signatures executablePlan ∧
      (∀ cell, cell ∈ finalState.heap → ∀ stored,
        cell.value = some stored →
          stored.HasValidCodeAndEvidence program.signatures executablePlan) ∧
      initial.TypeLayoutExtends finalState ∧
      value.HasDeepType program.signatures executablePlan finalState
        specialized.function.inferredBodyType ∧
      value.HasValidCodeAndEvidence program.signatures executablePlan := by
  have certificate := runDeepCertifiedWithValidationFuel_done_certificate
    program plan entry arguments validationFuel executionFuel initial finalState
    value specialized exact done
  exact ⟨certificate.initial_state_safe.hasDeepTypes,
    certificate.initial_state_safe.hasValidCodeAndEvidence,
    fun pair member =>
      let inputSafe := certificate.inputs_safe.zip_member member
      ⟨inputSafe.hasDeepType certificate.initial_state_safe,
        inputSafe.code_and_evidence⟩,
    certificate.final_state_safe.hasDeepTypes,
    certificate.final_state_safe.hasValidCodeAndEvidence,
    certificate.state_layout_extends,
    certificate.value_safe.hasDeepType certificate.final_state_safe,
    certificate.value_safe.code_and_evidence⟩

end Solcore.Frontend.SourceTypedRuntime
