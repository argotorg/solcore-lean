import Solcore.SourceSemantics.CoreLowering.CallableOrdinarySpecializationStageCoherence
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCanonicalCallsReady
import Solcore.SourceSemantics.CoreLowering.CallContractCertificates

/-!
Ordinary selected sidecars can reuse the actual canonical call ports. Both
preparation receipts identify their complete post-local source with the same
closure source. Original checked-program typing and ordinary specialization
origins then derive full guard-frame agreement internally.

The original canonical policy, raw typing, finite Calls path and exact compiler
port are preserved. Genuine ordinary origins and complete raw range formation
remain static inputs. Applied-view source provenance and detached method
origins require their own producers before this endpoint covers those scopes.
-/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinaryScopeCallsReady
open Core Frontend SourceInference
open CallableIndexedLambdaValues
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (Certificate)

/-- The two actual source preparation receipts discharge the full post-local
source equality required by ordinary stage coherence. No frame equality or
specialization-key equality is supplied. -/
theorem ledger_frame_of_receipts
    {program : CheckedProgram} {plan : SourceCoreStageContracts.Plan}
    {owner : SourceCoreStageContracts.Key}
    {canonical selected : SourceCoreStageContracts.Sidecar}
    {canonicalActive selectedActive : TypeSystem.Substitution}
    {source : TypedSource}
    (wellFormed : ProgramWellFormed (Program.ofChecked program))
    (canonicalIssued : SourceCoreStageContracts.prepareSidecar plan owner = .ok canonical)
    (selectedIssued : SourceCoreStageContracts.prepareSidecar plan selected.caller.key = .ok selected)
    (canonicalSource : LambdaSourceAlignment.SourceReceipt program plan owner canonicalActive source)
    (selectedSource : LambdaSourceAlignment.SourceReceipt program plan selected.caller.key selectedActive source)
    (canonicalOrigin : RecursiveNamedPublicSpecializationMeaning.Origin program canonical.caller)
    (selectedOrigin : RecursiveNamedPublicSpecializationMeaning.Origin program selected.caller)
    (canonicalRange : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures program.signatures) canonical.caller.parameterSubstitution)
    (selectedRange : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures program.signatures) selected.caller.parameterSubstitution) :
    CallableLedger.frame selected = CallableLedger.frame canonical := by
  have samePlan : selected.plan = canonical.plan :=
    (CallContractCertificates.sidecar_of_accepted selectedIssued).1.trans
      (CallContractCertificates.sidecar_of_accepted canonicalIssued).1.symm
  have sameSource : selected.caller.function.typedBody.applySubstitution selectedActive =
      canonical.caller.function.typedBody.applySubstitution canonicalActive :=
    (LambdaSourceAlignment.SourceReceipt.source selectedSource selectedIssued).symm.trans
      (LambdaSourceAlignment.SourceReceipt.source canonicalSource canonicalIssued)
  exact CallableOrdinarySpecializationStageCoherence.ledger_frame_eq_of_origins
    wellFormed samePlan selectedOrigin canonicalOrigin selectedRange canonicalRange sameSource

/-- Construct every call port for an ordinary selected sidecar scope from the
actual canonical producer. The sidecar equations identify its one authentic
canonical sidecar, and each original port is transported by derived coherence. -/
theorem ordinary_calls_ready
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
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (canonical selected : SourceCoreStageContracts.Sidecar)
    (selectedActive : TypeSystem.Substitution)
    (canonicalIssued : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan
      code.compilation.owner = .ok canonical)
    (selectedIssued : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan
      selected.caller.key = .ok selected)
    (selectedSource : LambdaSourceAlignment.SourceReceipt compiled.sourceProgram compiled.indexed.base.plan
      selected.caller.key selectedActive function.source)
    (canonicalOrigin : RecursiveNamedPublicSpecializationMeaning.Origin compiled.sourceProgram canonical.caller)
    (selectedOrigin : RecursiveNamedPublicSpecializationMeaning.Origin compiled.sourceProgram selected.caller)
    (canonicalRange : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures compiled.sourceProgram.signatures) canonical.caller.parameterSubstitution)
    (selectedRange : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures compiled.sourceProgram.signatures) selected.caller.parameterSubstitution)
    {rootScope : SourceCoreLocalCell.Scope} {rootId : ExpressionId}
    {rootCode : SourceCoreBasic.LoweredExpr} {rootType : TypeSystem.Ty}
    (typed : ExpressionHasType function.source context rootId rootType)
    (root : Certificate code.policy code.lowerBody code.compilation compiled.indexed.fuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      function.source context code.reasonAt rootScope rootId rootCode) :
    CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.CallsReady
      (compiled := compiled)
      (invocation := RecursiveStageRegistry.scope selected selectedActive function) root := by
  obtain ⟨actualCanonical, actualIssued, _actualSelected, ready⟩ :=
    CallableIndexedOwnedPreparedStagedCanonicalCallsReady.canonical_calls_ready
      code retained metadata sourceReceipt unique typed root
  have same : actualCanonical = canonical :=
    Except.ok.inj (actualIssued.symm.trans canonicalIssued)
  cases same
  have guardFrame :
      (RecursiveStageRegistry.scope selected selectedActive function).guards =
        (RecursiveStageRegistry.scope canonical code.active function).guards :=
    ledger_frame_of_receipts wellFormed canonicalIssued selectedIssued sourceReceipt selectedSource
      canonicalOrigin selectedOrigin canonicalRange selectedRange
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

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinaryScopeCallsReady
