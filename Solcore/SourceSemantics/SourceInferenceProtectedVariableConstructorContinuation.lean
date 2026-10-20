import Solcore.SourceSemantics.SourceInferenceProtectedVariableCallContinuation

/-! Contextual and explicit constructor expression dispatch preserves fixed
protected variables before delegating to the actual smaller application. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail

theorem inferExprFuel_dotConstructor_fixes_protected
    {protectedVars : List TypeVarId} {fuel : Nat} {context : SourceInference.Context}
    {expression : Syntax.Expr} {expected : Option Ty} {initial : State}
    {dot : Syntax.SourceSpan} {name : Syntax.Identifier}
    {arguments : Option (Syntax.DelimitedList Syntax.Expr)}
    (expressionEq : expression.value = .dotConstructor dot name arguments)
    (constructorInduction : ∀ dataType constructor typeArguments,
      InferConstructorApplicationFuelFixedness protectedVars fuel context expression
        initial.allocateExpressionId.1 (instantiateDataConstructor dataType constructor typeArguments)
        (arguments.map (·.elements) |>.getD []) expected initial.allocateExpressionId.2) :
    InferExprFuelFixedness protectedVars (fuel+1) context expression expected initial := by
  intro ready wellFormed bound live fixed catalog validated canonical expectedBelow expectedSafe result success
  let id := initial.allocateExpressionId.1
  let allocated := initial.allocateExpressionId.2
  have allocationEq : initial.allocateExpressionId = (id,allocated) := rfl
  have allocatedFixed : FixesProtected protectedVars allocated := fixed.of_substitution_eq rfl
  have allocationProperties : initial.InferenceProgress allocated ∧ allocated.InferenceReady :=
    ⟨.allocateExpressionId _ ready.solved, ready.allocateExpressionId⟩
  have expectedAtAllocated : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow allocated.inference.next := by
    intro expectedType member
    exact (expectedBelow expectedType member).weaken
      allocationProperties.1.next_le
  have allocationTransport : SafeTransport protectedVars initial allocated := .of_substitution_eq rfl
  have allocationPrivacy : SafeTransport protectedVars initial allocated ∧
      LiveBindersSafe protectedVars allocated ∧ allocated.requirements = initial.requirements :=
    ⟨allocationTransport, live.transport rfl allocationTransport, rfl⟩
  have allocatedEq : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocationEq).symm
  have boundAllocated : ∀ metavariable ∈ protectedVars, metavariable.index < allocated.inference.next := by
    intro metavariable member
    rw [allocatedEq]
    change metavariable.index < initial.inference.next
    exact bound metavariable member
  have wfAllocated : allocated.RequirementsWellFormed := by
    rw [allocatedEq]
    change initial.RequirementsWellFormed
    exact wellFormed
  unfold inferExprFuel at success
  simp only [allocationEq, expressionEq, bind, Except.bind] at success
  cases candidateResult : contextualConstructorCandidate context allocated
      expected name.value with
  | error error =>
      simp [candidateResult] at success
  | ok candidate =>
      rcases candidate with ⟨dataType, constructor, typeArguments⟩
      simp only [candidateResult] at success
      have instantiationBelow :=
        contextualConstructorCandidate_success_instantiation_variablesBelow
          allocationProperties.2 expectedAtAllocated validated
          candidateResult
      obtain ⟨dataMember, constructorMember, actual, expectedEq, nominalEq⟩ := contextualConstructorCandidate_success_facts candidateResult
      have instantiationSafe := contextual_constructor allocationProperties.2 validated
        (allocationPrivacy.1 _ (expectedSafe actual (by rw [expectedEq]; simp)))
        (by simpa only [expectedEq] using candidateResult)
      have finished := constructorInduction dataType constructor typeArguments allocationProperties.2 wfAllocated boundAllocated
        allocationPrivacy.2.1 allocatedFixed catalog validated canonical
        instantiationBelow.1 instantiationSafe.1 instantiationBelow.2 instantiationSafe.2
        expectedAtAllocated (fun type member => allocationPrivacy.1 _ (expectedSafe type member)) result success
      exact finished

theorem inferExprFuel_fieldConstructor_fixes_protected
    {protectedVars : List TypeVarId} {fuel : Nat} {context : SourceInference.Context}
    {expression base : Syntax.Expr} {expected : Option Ty} {initial : State}
    {dot : Syntax.SourceSpan} {name : Syntax.Identifier}
    (expressionEq : expression.value = .field base dot name)
    (constructorInduction : ∀ instantiation state,
      InferConstructorApplicationFuelFixedness protectedVars fuel context expression
        initial.allocateExpressionId.1 instantiation [] expected state) :
    InferExprFuelFixedness protectedVars (fuel+1) context expression expected initial := by
  intro ready wellFormed bound live fixed catalog validated canonical expectedBelow expectedSafe result success
  let id := initial.allocateExpressionId.1
  let allocated := initial.allocateExpressionId.2
  have allocationEq : initial.allocateExpressionId = (id,allocated) := rfl
  have allocatedFixed : FixesProtected protectedVars allocated := fixed.of_substitution_eq rfl
  have allocationProperties : initial.InferenceProgress allocated ∧ allocated.InferenceReady :=
    ⟨.allocateExpressionId _ ready.solved, ready.allocateExpressionId⟩
  have expectedAtAllocated : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow allocated.inference.next := by
    intro expectedType member
    exact (expectedBelow expectedType member).weaken
      allocationProperties.1.next_le
  have allocationTransport : SafeTransport protectedVars initial allocated := .of_substitution_eq rfl
  have allocationPrivacy : SafeTransport protectedVars initial allocated ∧
      LiveBindersSafe protectedVars allocated ∧ allocated.requirements = initial.requirements :=
    ⟨allocationTransport, live.transport rfl allocationTransport, rfl⟩
  have allocatedEq : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocationEq).symm
  have boundAllocated : ∀ metavariable ∈ protectedVars, metavariable.index < allocated.inference.next := by
    intro metavariable member
    rw [allocatedEq]
    change metavariable.index < initial.inference.next
    exact bound metavariable member
  have wfAllocated : allocated.RequirementsWellFormed := by
    rw [allocatedEq]
    change initial.RequirementsWellFormed
    exact wellFormed
  unfold inferExprFuel at success
  simp only [allocationEq, expressionEq, bind, Except.bind] at success
  cases candidatesResult :
      constructorCalleeCandidates context allocated expression with
  | error error =>
      simp [candidatesResult] at success
  | ok candidates =>
      simp only [candidatesResult] at success
      cases candidates with
      | nil =>
          simp only [] at success
          repeat' first | split at success
          all_goals contradiction
      | cons candidate rest =>
          cases rest with
          | cons second tail => simp at success
          | nil =>
              rcases candidate with ⟨dataType, constructor⟩
              let freshResult :=
                freshDataConstructorInstantiation dataType constructor
                  allocated
              have candidateFacts :=
                constructorCalleeCandidates_success_members candidatesResult
                  dataType constructor (by simp)
              have payloadTypesBelow :=
                validated.data_constructor_payloadTypes_variablesBelow
                  candidateFacts.1 candidateFacts.2
                  allocated.inference.next
              have freshProperties :=
                freshDataConstructorInstantiation_inferenceProperties
                  dataType constructor allocated allocationProperties.2
                  payloadTypesBelow
              have payloadClosed := validated.data_constructor_payloadTypes_variablesBelow candidateFacts.1 candidateFacts.2 0
              have freshPrivacy := fresh_constructor (dataType := dataType) allocationProperties.2 boundAllocated payloadClosed
              have freshLive := allocationPrivacy.2.1.transport
                (congrArg LexicalScope.binders (freshDataConstructorInstantiation_preserves_lexicalScope dataType constructor allocated)) freshPrivacy.1
              have freshWF := (freshDataConstructorInstantiation_direct_progress dataType constructor allocated).wellFormed wfAllocated
              have finished := constructorInduction freshResult.1 freshResult.2 freshProperties.2.1 freshWF
                (fun metavariable member => Nat.lt_of_lt_of_le (boundAllocated metavariable member) freshProperties.1.next_le)
                freshLive (allocatedFixed.of_substitution_eq (freshDataConstructorInstantiation_substitution _ _ _)) catalog validated canonical freshProperties.2.2.2.1 freshPrivacy.2.1
                freshProperties.2.2.2.2 freshPrivacy.2.2
                (fun type member => (expectedAtAllocated type member).weaken freshProperties.1.next_le)
                (fun type member => freshPrivacy.1 _ (allocationPrivacy.1 _ (expectedSafe type member))) result
                (by simpa only [freshResult] using success)
              exact finished

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
