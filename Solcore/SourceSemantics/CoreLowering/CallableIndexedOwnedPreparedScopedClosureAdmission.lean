import Solcore.SourceSemantics.CoreLowering.ScopedSourceBodyResultTyping
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinaryMethodScopedSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedSyntaxAdmission

/-! Compiler-derived scoped body certificates use the existing branching closure
collector at the original Source frame and exact current parameter context. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3200000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedScopedClosureAdmission
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedNamedSyntaxAdmission (DirectSite TableAligned)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)

structure SourceBodyCertificate (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function)
    (directRows : List SourceSpecialization.SpecializedFunction) (body : List StatementId) where
  result : TypeSystem.Ty
  scan : ScopedSourceBodyAdmission.Scan named.specialized.function.typedBody
    (fun id => GeneralSyntax named.specialized.function.typedBody id (DirectSite directRows)) result true body
  hasReturn : AcceptedCompilerBodyProfile.HasReturn named.specialized.function.typedBody body
  metadata : CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
    compiled.indexed named named.specialized.function.typedBody (DirectSite directRows)
  signature : ProgramFunctionSignature
  signatureMember : signature ∈ compiled.sourceProgram.signatures.functions
  sourceOwner : named.specialized.function.typedBody.owner = signature.id

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled compiled.indexed.ancestry.graph.inputs.callable)
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {bodyRegistry : SourceCoreRawMetadata.Registry}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (code : CallableIndexedLambdaValues.Code compiled.indexed function scope administrative)
  (support : CallableIndexedOwnedOrdinaryLambdaSupport.Support code bodyRegistry
    (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics))
  (provenance : CallableIndexedOwnedContextualLambdaProvenance.OrdinaryAt code support)
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  {inputs : List (Input compiled)} (rows : Inventory inputs)
  {directRows : List SourceSpecialization.SpecializedFunction} (aligned : TableAligned inputs directRows)
  (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
  (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
  (methods : CallableIndexedOwnedPreparedStagedMethodSelectionIssuer.Catalog compiled)

include stagePrepared code support provenance receiver wellFormed rows aligned checked catalog methods in
theorem of_actual
    (certificate : SourceBodyCertificate compiled support.caller.named directRows function.body) :
    Nonempty (Σ packet : CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport.Branching code
        (RecursiveNamedPreparedStageScopes.registry stagePrepared),
      CallableIndexedOwnedPreparedStagedPhysicalBranchingClosureStaticSupport.SelectedBody (headers rows)
        code support.body.toContext (RecursiveNamedPreparedStageScopes.registry stagePrepared) packet
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) := by
  have supported : ∀ instantiation, DirectSite directRows instantiation →
      CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported code.compilation.plan instantiation := by
    intro instantiation site
    rw [support.compilation]
    exact site.supported aligned
  have covered : ∀ instantiation, DirectSite directRows instantiation → ∀ index signature,
      SourceCompilationPlan.exactInstantiationKey code.compilation.plan instantiation = .ok signature.key →
      code.compilation.globals[index]? = some signature →
      ∃ header ∈ headers rows, header.slot = index ∧ header.named.signature = signature := by
    intro instantiation site index signature target global
    rw [support.compilation] at target global
    exact site.covered rows aligned target global
  obtain ⟨sidecar, _issued, selected⟩ :=
    CallableIndexedOwnedPreparedDirectStageScopeReceipts.code_scope code support.source_receipt support.body.unique
  obtain ⟨finalContext, facts, typed, _⟩ :=
    CallableIndexedOwnedLambdaSourceAdmission.body_typed_at_parameters support.body.frame support.body.extended
  have scan : ScopedSourceBodyAdmission.Scan function.source
      (fun id => GeneralSyntax function.source id (DirectSite directRows)) certificate.result true function.body := by
    simpa only [support.source, CallableIndexedNamedGeneration.source] using certificate.scan
  have returned : AcceptedCompilerBodyProfile.HasReturn function.source function.body := by
    simpa only [support.source, CallableIndexedNamedGeneration.source] using certificate.hasReturn
  have result : function.resultType = certificate.result := scan.result_eq_of_return support.body.unique returned typed rfl
  have syntaxTree := scan.syntax support.body.unique result typed
  rw [← result] at syntaxTree
  exact CallableIndexedOwnedPreparedStagedOrdinaryMethodScopedSupport.of_actual_with_catalog
    stagePrepared code support provenance receiver wellFormed supported
    (by simpa only [support.source, CallableIndexedNamedGeneration.source] using certificate.metadata)
    rows covered checked catalog methods certificate.signatureMember
    (by simpa only [support.source, CallableIndexedNamedGeneration.source] using certificate.sourceOwner)
    scan.shape syntaxTree
    _ (.anonymous selected)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedScopedClosureAdmission
