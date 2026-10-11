import Solcore.SourceSemantics.CoreLowering.CallableOrdinaryMethodCatalogSeparation
import Solcore.SourceSemantics.CoreLowering.CallableOrdinaryAnnotationCoherence
import Solcore.SourceSemantics.CoreLowering.CallableSelectedCanonicalSourceErasure
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCanonicalCallsReady
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualDiagnosticSources

/-!
Actual executable-plan preparation supplies ordinary catalog provenance at an
ordinary function owner. Both recursive scope-selection paths retain the same
canonical source after requirement erasure. Together these facts identify the
complete guard frame and transport the actual canonical call ports.

The original body annotations identify the enclosing result, so no raw
replacement formation premise is needed here. The theorem retains the real
Code, original typing, compiler policy and exact call certificates.
-/
set_option autoImplicit false
set_option Elab.async false

namespace Solcore.SourceSemantics.CoreLowering.CallableOrdinaryPreparedScopeAnnotationCallsReady
open Core Frontend SourceInference
open CallableIndexedLambdaValues CallableAncestryMetadata
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (Certificate)

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

/-- Every selected recursive scope at an ordinary owner has the actual
canonical frame, including selections through applied metadata recipes. -/
theorem selected_frame {program : CheckedProgram}
    {before plan : SourceCompilationPlan.Plan} {fuel budget : Nat}
    {table : SourceCoreStageCodebook.Table} {function : Dynamic.Closure}
    {invocation : Staging.Recursive.Scope}
    {canonical : SourceCoreStageContracts.Sidecar} {owner : SourceCompilationPlan.Key}
    {active : TypeSystem.Substitution} {signature : ProgramFunctionSignature}
    (accepted : SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget
      program before fuel budget = .ok plan)
    (wellFormed : ProgramWellFormed (Program.ofChecked program))
    (signatureMember : signature ∈ program.signatures.functions)
    (sourceOwner : function.source.owner = signature.id)
    (canonicalIssued : SourceCoreStageContracts.prepareSidecar plan owner = .ok canonical)
    (canonicalSource : LambdaSourceAlignment.SourceReceipt program plan owner active function.source)
    (related : RecursiveStageRegistry.Selected program plan table function invocation) :
    invocation.guards = CallableLedger.frame canonical := by
  obtain ⟨selected, selectedActive, selectedIssued, scopeEq, erased⟩ :=
    CallableSelectedCanonicalSourceErasure.selected_canonical related
  have canonicalSourceEq := canonicalSource.source canonicalIssued
  have selectedOwner : selected.caller.function.typedBody.owner = signature.id := by
    have same := congrArg TypedSource.owner erased
    change function.source.owner = selected.caller.function.typedBody.owner at same
    exact same.symm.trans sourceOwner
  have canonicalOwner : canonical.caller.function.typedBody.owner = signature.id := by
    have same := congrArg TypedSource.owner canonicalSourceEq
    exact same.symm.trans sourceOwner
  have selectedMember := sidecar_member selectedIssued
  have canonicalMember := sidecar_member canonicalIssued
  have selectedOrigin := CallableOrdinaryMethodCatalogSeparation.of_preparation_at_ordinary_owner
    accepted wellFormed.signatures signatureMember _ selectedMember selectedOwner
  have canonicalOrigin := CallableOrdinaryMethodCatalogSeparation.of_preparation_at_ordinary_owner
    accepted wellFormed.signatures signatureMember _ canonicalMember canonicalOwner
  have samePlan : selected.plan = canonical.plan :=
    (CallContractCertificates.sidecar_of_accepted selectedIssued).1.trans
      (CallContractCertificates.sidecar_of_accepted canonicalIssued).1.symm
  rw [scopeEq]
  exact CallableOrdinaryAnnotationCoherence.ledger_frame_eq_of_erased
    wellFormed samePlan selectedOrigin canonicalOrigin
    (erased.symm.trans (congrArg eraseRequirements canonicalSourceEq))

/-- Construct every call port at an actual ordinary selected invocation. The
full frame equality and catalog origins are derived from preparation, while
the original compiler certificate and each callee lookup remain unchanged. -/
theorem calls_ready
    {compiled : SourceCoreUnifiedCompilation.Compiled}
    {named : CallableIndexedNamedGeneration.Named}
    {function : Dynamic.Closure} {parameterScope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} {context : SourceSemantics.Context}
    (code : Code compiled.indexed function parameterScope administrative)
    (retained : CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained named code)
    (metadata : CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles.MetadataFor
      compiled.indexed named function.source)
    (sourceReceipt : LambdaSourceAlignment.SourceReceipt compiled.sourceProgram compiled.indexed.base.plan
      code.compilation.owner code.active function.source)
    (unique : NodeOccurrencesUnique function.source)
    {before : SourceCompilationPlan.Plan} {fuel budget : Nat}
    (accepted : SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget
      compiled.sourceProgram before fuel budget = .ok compiled.indexed.base.plan)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    {signature : ProgramFunctionSignature}
    (signatureMember : signature ∈ compiled.sourceProgram.signatures.functions)
    (sourceOwner : function.source.owner = signature.id)
    {invocation : Staging.Recursive.Scope}
    (related : RecursiveStageRegistry.Selected compiled.sourceProgram compiled.indexed.base.plan
      compiled.indexed.ancestry.graph.inputs.callable.table function invocation)
    {rootScope : SourceCoreLocalCell.Scope} {rootId : ExpressionId}
    {rootCode : SourceCoreBasic.LoweredExpr} {rootType : TypeSystem.Ty}
    (typed : ExpressionHasType invocation.source context rootId rootType)
    (root : Certificate code.policy code.lowerBody code.compilation compiled.indexed.fuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source context code.reasonAt rootScope rootId rootCode) :
    CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.CallsReady
      (compiled := compiled) (invocation := invocation) root := by
  rcases invocation with ⟨origin, actualSource, owned, invocationContext, evidence, guards⟩
  have sameSource : actualSource = function.source :=
    (RecursiveStageRegistry.registry compiled.sourceProgram compiled.indexed.base.plan
      compiled.indexed.ancestry.graph.inputs.callable.table).source related
  subst actualSource
  obtain ⟨canonical, issued, _canonicalSelected, ready⟩ :=
    CallableIndexedOwnedPreparedStagedCanonicalCallsReady.canonical_calls_ready
      code retained metadata sourceReceipt unique typed root
  have guardFrame := selected_frame accepted wellFormed signatureMember sourceOwner
    issued sourceReceipt related
  intro callFuel callScope callId callee ids callMetadata lowered compiler path
  obtain ⟨port⟩ := ready compiler path
  exact ⟨{
    prepared := port.prepared
    sidecar := port.sidecar
    caller := port.caller
    view := port.view
    guardFrame := guardFrame.trans port.guardFrame
    originalUnique := port.originalUnique
    sourceParent := port.sourceParent
    calleeNode := port.calleeNode
    calleeFound := port.calleeFound
  }⟩

end Solcore.SourceSemantics.CoreLowering.CallableOrdinaryPreparedScopeAnnotationCallsReady
