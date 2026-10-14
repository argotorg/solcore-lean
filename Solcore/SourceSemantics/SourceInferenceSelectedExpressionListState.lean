import Solcore.SourceSemantics.SourceInferenceSelectedExpressionState

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

theorem RecursiveExpressionInvariant.ofExpressions
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {finalized : Frontend.SourceInference.Result}
    {initial final : State} {inferred : List InferredExpression}
    {expressions : List Syntax.Expr}
    {semanticContext : SourceSemantics.Context} {fuel : Nat}
    (invariant : RecursiveExpressionInvariant wholeContext finalized initial semanticContext)
    (signatureFormation : ProgramSignatureFormationValidated inferenceContext.signatures)
    (functionsCanonical : ∀ signature ∈ inferenceContext.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (extension : finalized.substitution.SemanticallyExtends final.inference.substitution)
    (success : Detail.inferExprsFuel fuel inferenceContext expressions initial = .ok (inferred, final)) :
    RecursiveExpressionInvariant wholeContext finalized final semanticContext := by
  have properties := Detail.inferExprsFuel_inferenceProperties invariant.ready
    signatureFormation functionsCanonical success
  refine {
    active := invariant.active.inferExprsFuel success
    ready := properties.2.1
    bindersBelow := Detail.inferExprsFuel_preserves_localBindersBelowNextLocal invariant.bindersBelow success
    nodesBelow := (Detail.inferExprsFuel_occurrenceBoundExtends success).nodesBelowNextOccurrence invariant.nodesBelow
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
  have scopeEq := Detail.inferExprsFuel_success_lexicalScope_eq success
  simpa only [State.lexicalScope] using congrArg LexicalScope.binders scopeEq

theorem ActualStateInvariant.ofExpressions
    {fuel : Nat}
    {context : Frontend.SourceInference.Context} {expressions : List Syntax.Expr}
    {initial final : State} {inferred : List InferredExpression} {source : TypedSource}
    (invariant : ActualStateInvariant initial source)
    (success : Detail.inferExprsFuel fuel context expressions initial = .ok (inferred, final))
    (nextLe : initial.inference.next ≤ final.inference.next) :
    ActualStateInvariant final source := by
  obtain ⟨pending, ledger⟩ := invariant.ledger
  refine ⟨⟨pending, (actualLedgerFamily fuel).expressions success ledger⟩,
    invariant.origins.inferExprsFuel success, ?_, invariant.sourceMonomorphic⟩
  exact activeQuantifiersBelowNext_transport invariant.quantifiersBelow
    (congrArg LexicalScope.binders (Detail.inferExprsFuel_success_lexicalScope_eq success)) nextLe

end Solcore.SourceSemantics.SourceInferenceSoundness
