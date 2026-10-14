import Solcore.SourceSemantics.SourceInferenceSelectedLeafSoundness
import Solcore.SourceSemantics.SourceInferenceExpressionLedgerInvariant
import Solcore.SourceSemantics.SourceInferenceExpressionRecursiveSoundness

/-! Actual local calls obtain allocation and capture evidence from the live
checker ledger and the retained lexical binder inventory. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

/-- A retained local expression uses its actual selected binder, its actual
fresh obligation allocation, and finalization's binder-local capture check. -/
theorem
    inferExprFuel_success_localIdentifier_expressionTypingBase_actual
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn : Ty} {evidenceState : State} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    (resources : FinalInferenceResources wholeContext wholeReturn
      evidenceState roots finalized)
    (interfaces : ExecutableCoercionInterfaces.SourceInterfaces
      wholeContext.signatures finalized.solvedRequirements finalized.typedSource)
    {fuel : Nat} {expression : Syntax.Expr} {expected : Option Ty}
    {initial allocated resultState : State}
    {id : ExpressionId} {name : Syntax.Identifier} {binder : TypedBinder}
    {inferred : InferredExpression}
    {semanticSource : TypedSource} {active : SourceSemantics.Context}
    (expressionEq : expression.value = .identifier name)
    (allocationEq : initial.allocateExpressionId = (id, allocated))
    (lookupEq : allocated.lookupBinder? name.value = some binder)
    (success : Detail.inferExprFuel (fuel + 1) inferenceContext expression
      expected initial = .ok (inferred, resultState))
    {pending : List RequirementId}
    (ledger : RecursiveLedgerInvariant initial pending)
    (origins : ActiveBinderCaptureOrigins initial (evidenceState.toTypedSource roots))
    (resultSubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        resultState.inference.substitution)
    (requirementsSubset : resultState.requirements ⊆
      evidenceState.requirements)
    (retained : ExpressionRequirementsRetainedAt
      (resultState.toTypedSource roots) finalized.typedSource inferred.id)
    (coercionsRetained : ExpressionCoercionPrimariesRetainedAt
      (resultState.toTypedSource roots) finalized.typedSource inferred.id)
    (catalog : SignatureCatalogWellFormed inferenceContext.signatures)
    (signaturesEq : inferenceContext.signatures = wholeContext.signatures)
    (canonical : SignatureParametersWellFormed
      wholeContext.scope.genericOwner wholeContext.typeParameters)
    (invariant : RecursiveExpressionInvariant wholeContext finalized initial
      active)
    (covered : TemplateScopeCovered finalized.typedSource active
      (.expression inferred.id)) :
    ExpressionTypingBase (resultState.toTypedSource roots) semanticSource
      active finalized.substitution inferred := by
  have allocatedEq : initial.allocateExpressionId.2 = allocated := congrArg Prod.snd allocationEq
  have allocatedLedger : RecursiveLedgerInvariant allocated pending := by
    rw [← allocatedEq]
    exact ledger.allocateExpressionId
  have allocatedOrigins : ActiveBinderCaptureOrigins allocated
      (evidenceState.toTypedSource roots) := by
    apply origins.congr_localBinders
    rw [← allocatedEq]
    rfl
  let instantiated := binder.scheme.instantiateWithSubstitution allocated.inference.next
  let advanced : State := { allocated with inference := {
    allocated.inference with next := instantiated.next } }
  let predicates := binder.schemeRequirements.map fun requirement =>
    Detail.applyPredicate advanced
      (TypedTraitResolution.applySubstitution instantiated.substitution requirement.predicate)
  have advancedLedger : RecursiveLedgerInvariant advanced pending := allocatedLedger.withInference
  have found : advanced.lookupBinder? name.value = some binder := lookupEq
  have certificate := advancedLedger.templates.lookupBinderRequirementAllocationCertificate
    advancedLedger.requirements name.value binder predicates found
  have noCapture := resources.noCapture_of_lookupBinder? allocatedOrigins lookupEq
  exact inferExprFuel_success_localIdentifier_expressionTypingBase_selected
    resources interfaces expressionEq allocationEq lookupEq success certificate noCapture
    resultSubstitutionExtension requirementsSubset retained coercionsRetained catalog signaturesEq
    canonical invariant covered

end Solcore.SourceSemantics.SourceInferenceSoundness
