import Solcore.SourceSemantics.SourceCompiledGeneralizedForContracts

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend SourceInference TypeSystem ProtectedVariables

theorem GeneralizedActualStateInvariant.ofForItemPreservingBinders
    {fuel : Nat} {context : SourceInference.Context} {item : Syntax.ForItem}
    {initial final : State} {inferred : ForItemForm} {source : TypedSource}
    (invariant : GeneralizedActualStateInvariant initial source)
    (ready : initial.InferenceReady)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (accepted : Detail.inferForItemFuel fuel context item initial = .ok (inferred, final))
    (binders : final.localBinders = initial.localBinders) :
    GeneralizedActualStateInvariant final source := by
  obtain ⟨pending, ledger⟩ := invariant.ledger
  have properties := Detail.inferForItemFuel_inferenceProperties ready formation canonical accepted
  refine ⟨⟨pending ++ inferred.localSchemeTemplateIds, (actualLedgerFamily fuel).statements.forItem accepted ledger⟩,
    invariant.origins.congr_localBinders binders,
    activeQuantifiersBelowNext_transport invariant.quantifiersBelow binders properties.1.next_le,
    ?_, invariant.backed.transport (fun _ member => binders ▸ member)
      (Detail.inferForItemFuel_requirements_subset accepted) properties.1.substitution_extends⟩
  intro binder member
  have old := binders ▸ member
  exact (inferForItemFuel_private binder.scheme.quantified fuel context item initial
    ready ledger.requirements (invariant.quantifiersBelow binder old) (invariant.privacy binder old)
    catalog formation canonical _ accepted).2.1

end Solcore.SourceSemantics.SourceInferenceSoundness
