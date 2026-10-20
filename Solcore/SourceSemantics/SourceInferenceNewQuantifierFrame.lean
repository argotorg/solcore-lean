import Solcore.SourceSemantics.SourceInferenceProtectedVariableInference
import Solcore.SourceSemantics.SourceInferenceGeneralizedPrivacyBoundary

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem

/-- A fresh generalized variable cannot arise in an old type when the actual
initializer fixes old variables avoided by its live environment. -/
theorem inferExprFuel_fresh_quantifiers_safe
    {protectedVars : List TypeVarId} {fuel : Nat} {context : SourceInference.Context}
    {expression : Syntax.Expr} {expected : Option Ty} {initial final : State}
    {inferredValue : InferredExpression} {type : Ty}
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (expectedClosed : ∀ expectedType ∈ expected, expectedType.VariablesBelow 0)
    (accepted : Detail.inferExprFuel fuel context expression expected initial = .ok (inferredValue, final))
    (lower : ∀ q ∈ protectedVars, initial.inference.next ≤ q.index)
    (live : LiveBindersSafe protectedVars final)
    (typeBelow : type.VariablesBelow initial.inference.next) : Safe protectedVars final type := by
  have inferred := Detail.inferExprFuel_inferenceProperties ready formation canonical
    (fun expectedType present => (expectedClosed expectedType present).weaken (Nat.zero_le _)) accepted
  have binders := congrArg LexicalScope.binders (Detail.inferExprFuel_success_lexicalScope_eq accepted)
  change final.localBinders = initial.localBinders at binders
  intro q occurs quantified
  have composed : final.resolve (initial.resolve type) =
      final.resolve type :=
    inferred.1.substitution_extends type
  rw [← composed] at occurs
  obtain ⟨v, earlierOccurrence, image⟩ :=
    apply_variable_origin final.inference.substitution
      (initial.resolve type) q occurs
  have earlier : v.index < initial.inference.next :=
    ready.solved.variablesBelow_apply typeBelow v earlierOccurrence
  have outside := ready.solved.apply_variables_outside_domain type v earlierOccurrence
  have entryFixed : FixesProtected [v] initial := by
    intro candidate member
    have same : candidate = v := List.mem_singleton.mp member
    subst candidate
    change initial.inference.substitution.apply (.variable v) = .variable v
    simp only [Substitution.apply,
      (Substitution.lookup?_eq_none_iff_not_mem_domain _ _).mpr outside, Option.getD_none]
  have backwards : ∀ beforeType,
      Safe protectedVars final beforeType →
      Safe [v] initial beforeType := by
    intro beforeType safe candidate present member
    obtain rfl := List.mem_singleton.mp member
    have transported := MonomorphicGeneralization.replacement_occurs
      final.inference.substitution (initial.resolve beforeType) present image
    have extension : final.resolve (initial.resolve beforeType) =
        final.resolve beforeType := inferred.1.substitution_extends beforeType
    change q ∈ (final.resolve (initial.resolve beforeType)).freeVariables at transported
    rw [extension] at transported
    exact safe q transported quantified
  have entryLive : LiveBindersSafe [v] initial := by
    intro binder member
    have readyMember : binder ∈ final.localBinders := by
      rw [binders]
      exact member
    have prior := live binder readyMember
    constructor
    · intro w free
      exact backwards _ (prior.1 w free)
    · intro requirement present beforeType typeMember w free unbound
      exact backwards _ (prior.2 requirement present beforeType typeMember w free unbound)
  have finalFixed := inferExprFuel_fixes_protected [v] fuel context expression expected initial ready wellFormed
    (by intro candidate member; obtain rfl := List.mem_singleton.mp member; exact earlier)
    entryLive entryFixed catalog formation canonical
    (fun beforeType present => (expectedClosed beforeType present).weaken (Nat.zero_le _))
    (fun beforeType present => safe_closed _ _ (expectedClosed beforeType present))
    _ accepted
  have same : q = v := by
    have fixed := finalFixed v (List.mem_singleton_self _)
    change q ∈ (final.resolve (.variable v)).freeVariables at image
    simpa only [fixed, Ty.freeVariables, List.mem_singleton] using image
  exact (Nat.not_lt.mpr (lower q quantified)) (same ▸ earlier)

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
