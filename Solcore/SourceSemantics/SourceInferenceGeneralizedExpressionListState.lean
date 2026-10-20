import Solcore.SourceSemantics.SourceCompiledGeneralizedExpressionList
import Solcore.SourceSemantics.SourceInferenceSelectedExpressionListState

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend SourceInference TypeSystem ProtectedVariables

theorem GeneralizedActualStateInvariant.ofExpressions
    {fuel : Nat} {context : SourceInference.Context} {expressions : List Syntax.Expr}
    {initial final : State} {inferred : List InferredExpression} {source : TypedSource}
    (invariant : GeneralizedActualStateInvariant initial source)
    (ready : initial.InferenceReady)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (accepted : Detail.inferExprsFuel fuel context expressions initial = .ok (inferred, final)) :
    GeneralizedActualStateInvariant final source := by
  obtain ⟨pending, ledger⟩ := invariant.ledger
  have properties := Detail.inferExprsFuel_inferenceProperties ready formation canonical accepted
  have binders : final.localBinders = initial.localBinders :=
    congrArg LexicalScope.binders (Detail.inferExprsFuel_success_lexicalScope_eq accepted)
  refine ⟨⟨pending, (actualLedgerFamily fuel).expressions accepted ledger⟩,
    invariant.origins.inferExprsFuel accepted,
    activeQuantifiersBelowNext_transport invariant.quantifiersBelow binders properties.1.next_le,
    ?_, invariant.backed.transport (fun _ member => binders ▸ member)
      (Detail.inferExprsFuel_requirements_subset accepted) properties.1.substitution_extends⟩
  intro binder member
  have old : binder ∈ initial.localBinders := binders ▸ member
  exact (inferExprsFuel_private binder.scheme.quantified fuel context expressions initial
    ready ledger.requirements (invariant.quantifiersBelow binder old) (invariant.privacy binder old)
    catalog formation canonical _ accepted).2.2.1

end Solcore.SourceSemantics.SourceInferenceSoundness
