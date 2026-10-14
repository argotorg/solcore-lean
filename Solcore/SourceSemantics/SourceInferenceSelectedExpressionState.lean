import Solcore.SourceSemantics.SourceInferenceActualStateInvariant
import Solcore.SourceSemantics.SourceInferenceActualLedgerSoundness
import Solcore.SourceSemantics.SourceInferencePlaceRecursiveSoundness

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

theorem RecursiveExpressionInvariant.ofExpression
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {finalized : Frontend.SourceInference.Result}
    {initial final : State} {inferred : InferredExpression}
    {expression : Syntax.Expr} {expected : Option Ty}
    {semanticContext : SourceSemantics.Context} {fuel : Nat}
    (invariant : RecursiveExpressionInvariant wholeContext finalized initial semanticContext)
    (signatureFormation : ProgramSignatureFormationValidated inferenceContext.signatures)
    (functionsCanonical : ∀ signature ∈ inferenceContext.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow initial.inference.next)
    (extension : finalized.substitution.SemanticallyExtends final.inference.substitution)
    (success : Detail.inferExprFuel fuel inferenceContext expression expected initial = .ok (inferred, final)) :
    RecursiveExpressionInvariant wholeContext finalized final semanticContext := by
  have properties := Detail.inferExprFuel_inferenceProperties invariant.ready
    signatureFormation functionsCanonical expectedBelow success
  refine {
    active := invariant.active.inferExprFuel success
    ready := properties.2.1
    bindersBelow := Detail.inferExprFuel_preserves_localBindersBelowNextLocal invariant.bindersBelow success
    nodesBelow := (Detail.inferExprFuel_occurrenceBoundExtends success).nodesBelowNextOccurrence invariant.nodesBelow
    schemeIsolation := ?_
    substitutionExtension := extension
    signaturesEq := invariant.signaturesEq
    typeParametersEq := invariant.typeParametersEq
    declarationEq := invariant.declarationEq
    residual := invariant.residual
    solvedRequirementsEq := invariant.solvedRequirementsEq
    assumptionsMono := invariant.assumptionsMono
  }
  apply activeSchemeQuantifierIsolation_transport invariant.schemeIsolation
  have scopeEq := Detail.inferExprFuel_success_lexicalScope_eq success
  simpa only [State.lexicalScope] using congrArg LexicalScope.binders scopeEq

theorem ActualStateInvariant.allocateExpressionId
    {initial final : State} {source : TypedSource} {id : ExpressionId}
    (invariant : ActualStateInvariant initial source)
    (allocation : initial.allocateExpressionId = (id, final)) : ActualStateInvariant final source := by
  obtain ⟨pending, ledger⟩ := invariant.ledger
  have stateEq : initial.allocateExpressionId.2 = final := congrArg Prod.snd allocation
  refine ⟨⟨pending, ?_⟩, ?_, ?_, invariant.sourceMonomorphic⟩
  · rw [← stateEq]
    exact ledger.allocateExpressionId
  · apply invariant.origins.congr_localBinders
    rw [← stateEq]
    rfl
  · apply activeQuantifiersBelowNext_transport invariant.quantifiersBelow
    · rw [← stateEq]; rfl
    · rw [← stateEq]; exact Nat.le_refl _

theorem ActualStateInvariant.ofExpression
    {fuel : Nat}
    {context : Frontend.SourceInference.Context} {expression : Syntax.Expr} {expected : Option Ty}
    {initial final : State} {inferred : InferredExpression} {source : TypedSource}
    (invariant : ActualStateInvariant initial source)
    (success : Detail.inferExprFuel fuel context expression expected initial = .ok (inferred, final))
    (nextLe : initial.inference.next ≤ final.inference.next) :
    ActualStateInvariant final source := by
  obtain ⟨pending, ledger⟩ := invariant.ledger
  refine ⟨⟨pending, (actualLedgerFamily fuel).expression success ledger⟩,
    invariant.origins.inferExprFuel success, ?_, invariant.sourceMonomorphic⟩
  exact activeQuantifiersBelowNext_transport invariant.quantifiersBelow
    (congrArg LexicalScope.binders (Detail.inferExprFuel_success_lexicalScope_eq success)) nextLe

theorem ActualStateInvariant.fresh
    {state : State} {source : TypedSource}
    (invariant : ActualStateInvariant state source) : ActualStateInvariant state.fresh.2 source := by
  obtain ⟨pending, ledger⟩ := invariant.ledger
  exact ⟨⟨pending, ledger.fresh⟩, invariant.origins.congr_localBinders rfl,
    activeQuantifiersBelowNext_transport invariant.quantifiersBelow rfl (Nat.le_succ _), invariant.sourceMonomorphic⟩

theorem ActualStateInvariant.unify
    {initial final : State} {source : TypedSource} {left right : Ty}
    (invariant : ActualStateInvariant initial source)
    (success : Detail.unify initial left right = .ok final) : ActualStateInvariant final source := by
  obtain ⟨pending, ledger⟩ := invariant.ledger
  have bindersEq := congrArg LexicalScope.binders (Detail.unify_preserves_lexicalScope success)
  refine ⟨⟨pending, ledger.unify success⟩, invariant.origins.congr_localBinders bindersEq,
    activeQuantifiersBelowNext_transport invariant.quantifiersBelow bindersEq ?_, invariant.sourceMonomorphic⟩
  unfold Detail.unify at success
  cases unification : initial.inference.unify left right with
  | error error => simp [Detail.liftUnification, unification, bind, Except.bind] at success
  | ok inference =>
    simp [Detail.liftUnification, unification, bind, Except.bind] at success
    cases success
    rw [InferState.unify_next unification]
    exact Nat.le_refl _

theorem ActualStateInvariant.allocateMonoBinder
    {state : State} {source : TypedSource}
    (invariant : ActualStateInvariant state source)
    (name : String) (type : Ty) (span : Option Syntax.SourceSpan) (comptime : Bool) :
    ActualStateInvariant (state.allocateBinder name (.mono type) span comptime []).2 source := by
  obtain ⟨pending, ledger⟩ := invariant.ledger
  refine ⟨⟨pending, ledger.allocateBinderWithoutRequirements name (.mono type) span comptime⟩,
    invariant.origins.allocateBinder rfl (.inl rfl), ?_, invariant.sourceMonomorphic⟩
  exact activeQuantifiersBelowNext_allocateBinder state name (.mono type) span comptime []
    invariant.quantifiersBelow (by simp [Scheme.mono])

end Solcore.SourceSemantics.SourceInferenceSoundness
