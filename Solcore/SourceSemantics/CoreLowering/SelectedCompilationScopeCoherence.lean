import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedStageScopes
import Solcore.SourceSemantics.CoreLowering.CallableOrdinaryMethodCatalogSeparation
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationOrdinaryAnnotationCoherence
import Solcore.SourceSemantics.CoreLowering.CallableSelectedCanonicalSourceErasure
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualDiagnosticSources

/-! Every actual named or anonymous selection at an ordinary Source owner has
its canonical guard frame. Original compiler origins and equal annotated Source
justify frame equality even when specialization keys differ. This identifies
neither the selected sidecar nor the complete invocation scope. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationScopeCoherence
open Core Frontend SourceInference
open CallableAncestryMetadata (eraseRequirements)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)

private theorem sidecar_member {plan : SourceCompilationPlan.Plan}
    {owner : SourceCompilationPlan.Key} {sidecar : SourceCoreStageContracts.Sidecar}
    (issued : SourceCoreStageContracts.prepareSidecar plan owner = .ok sidecar) :
    sidecar.caller ∈ plan.specializations := by
  have found := LambdaSourceAlignment.sidecar_lookup issued
  have filtered := CallableIndexedOwnedContextualDiagnosticSources.selected_filter found
  have member : sidecar.caller ∈ plan.specializations.filter
      (fun row => decide (row.key = owner)) := by
    rw [filtered]
    exact List.mem_singleton_self _
  exact (List.mem_filter.mp member).1

/-- The combined registry also has a named selection. Its literal prepared
source supplies the same erasure boundary; an anonymous selection keeps the
existing authenticated ancestry proof. -/
theorem selected_canonical {function : Dynamic.Closure}
    {invocation : Staging.Recursive.Scope}
    (selected : ((RecursiveNamedPreparedStageScopes.registry stagePrepared)).Closure function invocation) :
    ∃ sidecar active,
      SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan sidecar.caller.key = .ok sidecar ∧
      invocation = RecursiveStageRegistry.scope sidecar active function ∧
      eraseRequirements function.source =
        eraseRequirements (sidecar.source.applySubstitution active) := by
  cases selected with
  | anonymous receipt =>
      exact CallableSelectedCanonicalSourceErasure.selected_canonical receipt
  | named prepared sidecar issued same =>
      have sourceEq : prepared.view.source = sidecar.source := by
        change prepared.named.specialized.function.typedBody = sidecar.caller.function.typedBody
        rw [prepared.same, same]
      exact ⟨sidecar, [], by simpa only [same] using issued, rfl,
        by simpa using congrArg eraseRequirements sourceEq⟩
  | method selection statements sidecar issued same =>
      have sourceEq := congrArg (fun row : SourceSpecialization.SpecializedFunction => row.function.typedBody) same
      change sidecar.source = _ at sourceEq
      exact ⟨sidecar, [], by simpa only [same] using issued, rfl,
        by simpa [Staging.Recursive.methodView, Staging.Recursive.globalView, CallableCoercionMethodInstantiation.bodyInstance] using congrArg eraseRequirements sourceEq.symm⟩

theorem selected_frame {function : Dynamic.Closure}
    {invocation : Staging.Recursive.Scope}
    {canonical : SourceCoreStageContracts.Sidecar} {owner : SourceCompilationPlan.Key}
    {active : TypeSystem.Substitution} {signature : ProgramFunctionSignature}
    {before : SourceCompilationPlan.Plan} {fuel budget : Nat}
    (accepted : SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget
      compiled.sourceProgram before fuel budget = .ok compiled.indexed.base.plan)
    (signatures : SignatureCatalogWellFormed compiled.sourceProgram.signatures)
    (owners : ((Program.ofChecked compiled.sourceProgram).functions.map
      fun definition => definition.body.owner).Nodup)
    (atOwner : SelectedCompilationOrdinaryAnnotationCoherence.AtOwner
      compiled.sourceProgram function.source.owner)
    (signatureMember : signature ∈ compiled.sourceProgram.signatures.functions)
    (sourceOwner : function.source.owner = signature.id)
    (canonicalIssued : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan owner = .ok canonical)
    (canonicalSource : LambdaSourceAlignment.SourceReceipt compiled.sourceProgram compiled.indexed.base.plan
      owner active function.source)
    (selected : ((RecursiveNamedPreparedStageScopes.registry stagePrepared)).Closure function invocation) :
    invocation.guards = CallableLedger.frame canonical := by
  obtain ⟨sidecar, selectedActive, issued, scopeEq, erased⟩ :=
    selected_canonical stagePrepared selected
  have canonicalSourceEq := canonicalSource.source canonicalIssued
  have selectedOwner : sidecar.caller.function.typedBody.owner = signature.id := by
    have same := congrArg TypedSource.owner erased
    change function.source.owner = sidecar.caller.function.typedBody.owner at same
    exact same.symm.trans sourceOwner
  have canonicalOwner : canonical.caller.function.typedBody.owner = signature.id := by
    have same := congrArg TypedSource.owner canonicalSourceEq
    exact same.symm.trans sourceOwner
  have selectedOrigin := CallableOrdinaryMethodCatalogSeparation.of_preparation_at_ordinary_owner
    accepted signatures signatureMember _ (sidecar_member issued) selectedOwner
  have canonicalOrigin := CallableOrdinaryMethodCatalogSeparation.of_preparation_at_ordinary_owner
    accepted signatures signatureMember _ (sidecar_member canonicalIssued) canonicalOwner
  have samePlan : sidecar.plan = canonical.plan :=
    (CallContractCertificates.sidecar_of_accepted issued).1.trans
      (CallContractCertificates.sidecar_of_accepted canonicalIssued).1.symm
  rw [scopeEq]
  exact SelectedCompilationOrdinaryAnnotationCoherence.ledger_frame_eq_of_erased
    owners (by
      intro generic member identity
      exact atOwner generic member (identity.trans (selectedOwner.trans sourceOwner.symm)))
    samePlan selectedOrigin canonicalOrigin
    (erased.symm.trans (congrArg eraseRequirements canonicalSourceEq))

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationScopeCoherence
