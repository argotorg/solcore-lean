import Solcore.SourceSemantics.SourceInferencePatternActiveState
import Solcore.SourceSemantics.SourceInferenceGeneralizedActualStateInvariant
import Solcore.SourceSemantics.SourceInferenceActualPatternLedger

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend SourceInference TypeSystem ProtectedVariables

theorem GeneralizedActualStateInvariant.allocateHiddenLocal
    {state : State} {source : TypedSource}
    (invariant : GeneralizedActualStateInvariant state source) :
    GeneralizedActualStateInvariant state.allocateHiddenLocal.2 source := by
  obtain ⟨pending, ledger⟩ := invariant.ledger
  exact ⟨⟨pending, ledger.allocateHiddenLocal⟩,
    invariant.origins.congr_localBinders rfl,
    activeQuantifiersBelowNext_transport invariant.quantifiersBelow rfl (Nat.le_refl _),
    invariant.privacy.congr rfl rfl,
    invariant.backed.congr rfl rfl rfl⟩

theorem GeneralizedActualStateInvariant.ofPattern
    {fuel : Nat} {context : SourceInference.Context} {pattern : Syntax.Pattern}
    {expected : Ty} {initial final : State} {inferred : TypedMatchPattern} {source : TypedSource}
    (invariant : GeneralizedActualStateInvariant initial source)
    (ready : initial.InferenceReady)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (expectedBelow : expected.VariablesBelow initial.inference.next)
    (expectedSafe : Safe (activeSchemeQuantifiers initial) initial expected)
    (accepted : Detail.inferMatchPatternFuel fuel context pattern expected initial = .ok (inferred, final)) :
    GeneralizedActualStateInvariant final source := by
  obtain ⟨pending, ledger⟩ := invariant.ledger
  have active := inferMatchPatternFuel_active_state ready expectedBelow formation
    invariant.quantifiersBelow invariant.privacy invariant.backed invariant.origins expectedSafe accepted
  exact ⟨⟨pending, inferMatchPatternFuel_ledgerPreservation accepted ledger⟩,
    active.2.2.2, active.2.1, active.1, active.2.2.1⟩

/-- The scrutinee's actual inference supplies privacy for its returned type
with respect to every surviving active scheme. -/
theorem GeneralizedActualStateInvariant.expression_result_private
    {fuel : Nat} {context : SourceInference.Context} {expression : Syntax.Expr}
    {initial final : State} {inferred : InferredExpression} {source : TypedSource}
    (invariant : GeneralizedActualStateInvariant initial source)
    (ready : initial.InferenceReady)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (accepted : Detail.inferExprFuel fuel context expression none initial = .ok (inferred, final)) :
    Safe (activeSchemeQuantifiers final) final inferred.type := by
  have privacy := inferExprFuel_private (activeSchemeQuantifiers initial) fuel context expression none initial
    ready invariant.requirements (activeSchemeQuantifiers_below_next invariant.quantifiersBelow)
    invariant.privacy.all_live catalog formation canonical (by simp) (by simp) _ accepted
  have binders : final.localBinders = initial.localBinders :=
    congrArg LexicalScope.binders (Detail.inferExprFuel_success_lexicalScope_eq accepted)
  simpa only [activeSchemeQuantifiers, binders] using privacy.2.1

/-- Pattern entry after a real scrutinee call derives its expected-type
privacy from that call, then carries the full generalized operational state. -/
theorem GeneralizedActualStateInvariant.pattern_after_expression
    {expressionFuel patternFuel : Nat} {context : SourceInference.Context}
    {expression : Syntax.Expr} {patternSource : Syntax.Pattern}
    {initial scrutineeState final : State} {scrutinee : InferredExpression}
    {pattern : TypedMatchPattern} {source : TypedSource}
    (invariant : GeneralizedActualStateInvariant initial source)
    (ready : initial.InferenceReady)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (expressionAccepted : Detail.inferExprFuel expressionFuel context expression none initial =
      .ok (scrutinee, scrutineeState))
    (patternAccepted : Detail.inferMatchPatternFuel patternFuel context patternSource scrutinee.type
      scrutineeState = .ok (pattern, final)) :
    GeneralizedActualStateInvariant final source := by
  have properties := Detail.inferExprFuel_inferenceProperties ready formation canonical
    (by simp) expressionAccepted
  have after := invariant.ofExpression ready catalog formation canonical (by simp) (by simp) expressionAccepted
  exact after.ofPattern properties.2.1 formation properties.2.2
    (invariant.expression_result_private ready catalog formation canonical expressionAccepted) patternAccepted

end Solcore.SourceSemantics.SourceInferenceSoundness
