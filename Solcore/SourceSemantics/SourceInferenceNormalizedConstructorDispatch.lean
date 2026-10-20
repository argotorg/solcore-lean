import Solcore.SourceSemantics.SourceInferenceNormalizedContracts
import Solcore.Frontend.SourceInference.OccurrenceProperties

/-! Source constructor dispatch uses the actual catalog member and freshening
operation before the smaller constructor-application inference call. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
open Frontend SourceInference TypeSystem Detail SourceInferenceSoundness SourceInferenceRequirementFormation

private theorem freshConstructor_requirements (dataType : ProgramDataSignature)
    (constructor : ProgramDataConstructorSignature) (state : State) :
    (freshDataConstructorInstantiation dataType constructor state).2.requirements = state.requirements := by
  have fold (parameters : List TypeParameterId) (accumulator : List Ty × State) :
      (parameters.foldl (fun result _ =>
        (result.1 ++ [result.2.fresh.1],result.2.fresh.2)) accumulator).2.requirements =
        accumulator.2.requirements := by
    induction parameters generalizing accumulator with
    | nil => rfl
    | cons parameter rest ih => exact ih (accumulator.1 ++ [accumulator.2.fresh.1],accumulator.2.fresh.2)
  exact fold dataType.parameters ([],state)

theorem fresh_constructor_normalized_formation
    {semantic : SourceSemantics.Context} {outer : Substitution} {context : SourceInference.Context}
    {state : State} {dataType : ProgramDataSignature} {constructor : ProgramDataConstructorSignature}
    (formation : InferenceFormationContext semantic context outer)
    (formed : NormalizedStateFormation semantic outer state)
    (dataMember : dataType ∈ context.signatures.dataTypes) (constructorMember : constructor ∈ dataType.constructors) :
    let fresh := freshDataConstructorInstantiation dataType constructor state
    NormalizedStateFormation semantic outer fresh.2 ∧
      (∀ type ∈ fresh.1.payloadTypes, TypeAdmissible semantic (outer.apply type)) ∧
      TypeAdmissible semantic (outer.apply fresh.1.resultType) := by
  dsimp only
  have valid := freshDataConstructorInstantiation_admissible (state := state) formation.catalog formation.scope.binders
    formation.residual (formation.signatures.symm ▸ dataMember) constructorMember rfl
  refine ⟨formed.congr
    (congrArg LexicalScope.binders (freshDataConstructorInstantiation_preserves_lexicalScope dataType constructor state))
    (freshConstructor_requirements dataType constructor state),?_,?_⟩
  · intro type member
    exact type_applySubstitution_residual formation.residual formation.range
      (SourceSemantics.DataConstructorInstantiation.Admissible.payload_type_admissible formation.catalog formation.scope.binders valid member)
  · exact type_applySubstitution_residual formation.residual formation.range
      (SourceSemantics.DataConstructorInstantiation.Admissible.result_type_admissible formation.scope.binders valid)

theorem inferExprFuel_dotConstructor_formation
    {semantic : SourceSemantics.Context} {outer : Substitution} {fuel : Nat} {context : SourceInference.Context}
    {expression : Syntax.Expr} {dot : Syntax.SourceSpan} {name : Syntax.Identifier}
    {arguments : Option (Syntax.DelimitedList Syntax.Expr)} {expected : Option Ty} {initial : State}
    (form : expression.value = .dotConstructor dot name arguments)
    (constructorIH : ∀ dataType constructor typeArguments,
      InferConstructorApplicationFuelFormation semantic outer fuel context expression initial.allocateExpressionId.1
        (instantiateDataConstructor dataType constructor typeArguments)
        (arguments.map (·.elements) |>.getD []) expected initial.allocateExpressionId.2) :
    InferExprFuelFormation semantic outer (fuel+1) context expression expected initial := by
  intro ready nodes formed formation expectedBelow expectedFormed result success continuation capture
  let id := initial.allocateExpressionId.1
  let allocated := initial.allocateExpressionId.2
  have allocationEq : initial.allocateExpressionId = (id,allocated) := rfl
  have allocatedReady : allocated.InferenceReady := State.InferenceReady.allocateExpressionId ready
  have allocatedNodes := State.allocateExpressionId_preserves_nodesBelowNextOccurrence initial nodes
  have allocatedFormed : NormalizedStateFormation semantic outer allocated := formed.congr rfl rfl
  unfold inferExprFuel at success
  simp only [allocationEq,form,bind,Except.bind] at success
  cases selected : contextualConstructorCandidate context allocated expected name.value with
  | error error => simp [selected] at success
  | ok candidate =>
    rcases candidate with ⟨dataType,constructor,typeArguments⟩
    simp only [selected] at success
    have below := contextualConstructorCandidate_success_instantiation_variablesBelow allocatedReady expectedBelow formation.validated selected
    have progress := inferConstructorApplicationFuel_inferenceProperties allocatedReady formation.validated
      formation.functionShapes below.1 below.2 expectedBelow success
    have entryContinuation := continuation.trans progress.1.substitution_extends
    obtain ⟨dataMember,constructorMember,actual,expectedEq,nominalEq⟩ := contextualConstructorCandidate_success_facts selected
    have actualFormed := expectedFormed actual (by rw [expectedEq]; simp)
    have resultFormed : TypeAdmissible semantic
        (outer.apply (instantiateDataConstructor dataType constructor typeArguments).resultType) := by
      have resolved : TypeAdmissible semantic (outer.apply (allocated.resolve actual)) :=
        (entryContinuation actual).symm ▸ actualFormed
      simpa only [nominalEq,instantiateDataConstructor] using resolved
    have valid := SourceSemantics.DataConstructorInstantiation.Admissible.instantiateDataConstructor_applySubstitution
      formation.catalog (formation.signatures.symm ▸ dataMember) constructorMember outer resultFormed
    have payloadFormed : ∀ type ∈ (instantiateDataConstructor dataType constructor typeArguments).payloadTypes,
        TypeAdmissible semantic (outer.apply type) := by
      intro type member
      exact SourceSemantics.DataConstructorInstantiation.Admissible.payload_type_admissible
        formation.catalog formation.scope.binders valid (List.mem_map.mpr ⟨type,member,rfl⟩)
    exact constructorIH dataType constructor typeArguments allocatedReady allocatedNodes allocatedFormed formation
      below.1 payloadFormed below.2 resultFormed expectedBelow expectedFormed result success continuation capture

theorem inferExprFuel_fieldConstructor_formation
    {semantic : SourceSemantics.Context} {outer : Substitution} {fuel : Nat} {context : SourceInference.Context}
    {expression base : Syntax.Expr} {dot : Syntax.SourceSpan} {name : Syntax.Identifier}
    {expected : Option Ty} {initial : State}
    (form : expression.value = .field base dot name)
    (constructorIH : ∀ instantiation state,
      InferConstructorApplicationFuelFormation semantic outer fuel context expression initial.allocateExpressionId.1
        instantiation [] expected state) :
    InferExprFuelFormation semantic outer (fuel+1) context expression expected initial := by
  intro ready nodes formed formation expectedBelow expectedFormed result success continuation capture
  let id := initial.allocateExpressionId.1
  let allocated := initial.allocateExpressionId.2
  have allocationEq : initial.allocateExpressionId = (id,allocated) := rfl
  have allocatedReady : allocated.InferenceReady := State.InferenceReady.allocateExpressionId ready
  have allocatedNodes := State.allocateExpressionId_preserves_nodesBelowNextOccurrence initial nodes
  have allocatedFormed : NormalizedStateFormation semantic outer allocated := formed.congr rfl rfl
  unfold inferExprFuel at success
  simp only [allocationEq,form,bind,Except.bind] at success
  cases candidatesResult : constructorCalleeCandidates context allocated expression with
  | error error => simp [candidatesResult] at success
  | ok candidates =>
    simp only [candidatesResult] at success
    cases candidates with
    | nil =>
      simp only at success
      repeat' first | split at success
      all_goals contradiction
    | cons candidate rest =>
      cases rest with
      | cons second tail => simp at success
      | nil =>
        rcases candidate with ⟨dataType,constructor⟩
        let fresh := freshDataConstructorInstantiation dataType constructor allocated
        have members := constructorCalleeCandidates_success_members candidatesResult dataType constructor (by simp)
        have freshProperties := freshDataConstructorInstantiation_inferenceProperties dataType constructor allocated allocatedReady
          (formation.validated.data_constructor_payloadTypes_variablesBelow members.1 members.2 _)
        have freshFormed := fresh_constructor_normalized_formation formation allocatedFormed members.1 members.2
        have freshNodes := (freshDataConstructorInstantiation_occurrenceBoundExtends dataType constructor allocated).nodesBelowNextOccurrence allocatedNodes
        exact constructorIH fresh.1 fresh.2 freshProperties.2.1 freshNodes freshFormed.1 formation
          freshProperties.2.2.2.1 freshFormed.2.1 freshProperties.2.2.2.2 freshFormed.2.2
          (fun type member => (expectedBelow type member).weaken freshProperties.1.next_le)
          expectedFormed result success continuation capture

end Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
