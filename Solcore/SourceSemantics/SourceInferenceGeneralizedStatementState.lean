import Solcore.SourceSemantics.SourceCompiledGeneralizedStatementContracts

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend SourceInference TypeSystem ProtectedVariables

theorem GeneralizedActualStateInvariant.ofStatementPreservingBinders
    {fuel : Nat} {context : SourceInference.Context} {statement : Syntax.Statement}
    {expectedReturn : Ty} {initial : State} {result : Detail.StatementResult}
    {source : TypedSource}
    (invariant : GeneralizedActualStateInvariant initial source)
    (ready : initial.InferenceReady)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (returnBelow : expectedReturn.VariablesBelow initial.inference.next)
    (returnSafe : ∀ binder ∈ initial.localBinders,
      Safe binder.scheme.quantified initial expectedReturn)
    (accepted : Detail.inferStatementFuel fuel context statement expectedReturn initial = .ok result)
    (binders : result.state.localBinders = initial.localBinders) :
    GeneralizedActualStateInvariant result.state source := by
  obtain ⟨pending, ledger⟩ := invariant.ledger
  have properties := Detail.inferStatementFuel_inferenceProperties ready formation canonical returnBelow accepted
  refine ⟨⟨pending, (actualLedgerFamily fuel).statements.statement accepted ledger⟩,
    invariant.origins.congr_localBinders binders,
    activeQuantifiersBelowNext_transport invariant.quantifiersBelow binders properties.1.next_le,
    ?_, invariant.backed.transport (fun _ member => binders ▸ member)
      (Detail.inferStatementFuel_requirements_subset accepted) properties.1.substitution_extends⟩
  intro binder member
  have old := binders ▸ member
  exact (inferStatementFuel_private binder.scheme.quantified fuel context statement expectedReturn initial
    ready ledger.requirements (invariant.quantifiersBelow binder old) (invariant.privacy binder old)
    catalog formation canonical returnBelow (returnSafe binder old) _ accepted).2.2.1

end Solcore.SourceSemantics.SourceInferenceSoundness
