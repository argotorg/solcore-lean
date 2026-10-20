import Solcore.SourceSemantics.SourceInferenceNormalizedCoercionGraph
import Solcore.SourceSemantics.SourceInferenceCoercionIssuedFormation

/-! Final normalized formation for the real requirements committed by
expected-type fitting. The normalization extension is the actual continuation
to the selected finalizer. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
open Frontend SourceInference TypeSystem SourceInferenceRequirementFormation

theorem committed_new_formation
    {semantic : SourceSemantics.Context} {state : State} {outer : Substitution}
    {steps : List Detail.PlannedCoercionStep}
    (stepsFormed : ∀ step ∈ steps, PlannedCoercionStepFormed semantic outer step)
    {row : Requirement}
    (member : row ∈ (Detail.commitCoercionPlan state steps).2.requirements)
    (fresh : row ∉ state.requirements) :
    PredicateAdmissible semantic (TypedTraitResolution.applySubstitution outer row.predicate) := by
  rcases committed_coercion_requirement_origin state steps member with old | new
  · exact (fresh old).elim
  · obtain ⟨step, stepMember, primary | method⟩ := new
    · exact primary ▸ (stepsFormed step stepMember).2.2.1
    · exact (stepsFormed step stepMember).2.2.2 row.predicate method

theorem withExpected_new_requirements_formation
    {semantic : SourceSemantics.Context} {context : SourceInference.Context}
    {state : State} {actual : InferredExpression} {expected : Option Ty}
    {result : Detail.ExpectationResult} {outer : Substitution}
    (formation : FormationContext semantic context outer)
    (extension : outer.SemanticallyExtends state.inference.substitution)
    (actualFormed : TypeAdmissible semantic (outer.apply actual.type))
    (expectedFormed : ∀ type ∈ expected, TypeAdmissible semantic (outer.apply type))
    (accepted : Detail.withExpected context state actual expected = .ok result) :
    ∀ row ∈ result.state.requirements, row ∉ state.requirements →
      PredicateAdmissible semantic (TypedTraitResolution.applySubstitution outer row.predicate) := by
  cases expected with
  | none =>
    simp only [Detail.withExpected, Except.ok.injEq] at accepted
    cases accepted
    exact fun row member fresh => (fresh member).elim
  | some expected =>
    have expectedFormed := expectedFormed expected (by simp)
    cases unified : state.inference.unify actual.type expected with
    | ok inference =>
      simp only [Detail.withExpected, unified, Except.ok.injEq] at accepted
      cases accepted
      exact fun row member fresh => (fresh member).elim
    | error error =>
      cases error with
      | occursCheck _ _ => simp [Detail.withExpected, unified] at accepted
      | exhausted => simp [Detail.withExpected, unified] at accepted
      | mismatch left right =>
        simp only [Detail.withExpected, unified] at accepted
        cases planned : Detail.coercionPlan? context state
            (state.resolve actual.type) (state.resolve expected) with
        | error error => simp [planned, bind, Except.bind] at accepted
        | ok option =>
          cases option with
          | none => simp [planned, bind, Except.bind] at accepted
          | some plan =>
            simp only [planned, bind, Except.bind] at accepted
            change Except.ok _ = Except.ok result at accepted
            cases Except.ok.inj accepted
            have sourceNormalized : TypeAdmissible semantic (outer.apply (state.resolve actual.type)) :=
              (extension actual.type).symm ▸ actualFormed
            have targetNormalized : TypeAdmissible semantic (outer.apply (state.resolve expected)) :=
              (extension expected).symm ▸ expectedFormed
            exact fun _ member fresh => committed_new_formation
              (coercion_plan_formation formation sourceNormalized targetNormalized planned) member fresh

end Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation

namespace Solcore.SourceSemantics.SourceInferenceSoundness.FinalInferenceResources
open Frontend SourceInference TypeSystem

/-- The actual successful finalizer supplies the normalized producer range.
Its static declaration scope is shared with the semantic initializer context. -/
theorem normalizedCoercionContext
    {wholeContext : SourceInference.Context} {wholeReturn : Ty}
    {state : State} {roots : List NodeId} {finalized : SourceInference.Result}
    (resources : FinalInferenceResources wholeContext wholeReturn state roots finalized)
    {semantic : SourceSemantics.Context}
    (formation : SourceInferenceRequirementFormation.CoercionFormationContext semantic wholeContext)
    (binders : TypeParameterBindersWellFormed semantic)
    (parameters : semantic.typeParameters = wholeContext.typeParameters)
    (owner : semantic.currentDeclaration = some wholeContext.scope.genericOwner) :
    SourceInferenceNormalizedCoercionFormation.FormationContext semantic wholeContext finalized.substitution :=
  { toCoercionFormationContext := formation
    range := InferenceSubstitutionRangeFormationValidated.rangeAdmissible resources.range_formation
      binders formation.signatures parameters owner formation.residual }

end Solcore.SourceSemantics.SourceInferenceSoundness.FinalInferenceResources
