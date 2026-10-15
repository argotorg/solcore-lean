import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCoercedClosureAdmission
import Solcore.SourceSemantics.CoreLowering.CallableMethodBodyCoherence
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPrimitiveSourceAdmission
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedSyntaxAdmission
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedOrdinaryCoercedTerminalSupport

/-! Finite checks retain each original lambda body and its constrained direct
call. The original coercion rows and captured Source remain unchanged. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 3200000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedCoercedClosureAdmission
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedPreparedCoercedClosureAdmission (BodyCertificate)
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedNamedSyntaxAdmission (DirectSite TableAligned)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled compiled.indexed.ancestry.graph.inputs.callable)
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (code : CallableIndexedLambdaValues.Code compiled.indexed function scope administrative)
  (support : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Support code)
  (provenance : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.PreparedAt code support)
  (callerReceipt : CallableIndexedOwnedOrdinaryCallerReceipts.CallerAt support.caller function.context function.evidence)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (bodies : SelectedCompilationBodyTyping.Bodies compiled)
  {inputs : List (Input compiled)} (rows : Inventory inputs)
  {directRows : List SourceSpecialization.SpecializedFunction} (aligned : TableAligned inputs directRows)
  (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
  (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
  (methods : CallableIndexedOwnedPreparedStagedClosedCoercionSelection.Catalog compiled)

include stagePrepared code support provenance callerReceipt receiver bodies rows aligned checked catalog methods callerReceipt in
theorem of_actual
    (certificate : BodyCertificate compiled support.caller.named directRows function.body)
    (methodBodies : ∀ {method : ExecutableImplMethods.CheckedMethod}
      (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
      (sourceAt : CallablePreparedMethodRuntimeProfileFactory.SourceAt principal.cached.compilation
        (.initial compiled.compatible.checked) principal.sourceBody principal.dictionary)
      (_diagnostic : CallableIndexedOwnedPreparedStagedMethodTerminalSupport.DiagnosticAt principal.cached)
      (_certified : SelectedCompilationMethodBodySupport.Certified principal sourceAt),
      ∃ packet : SelectedCompilationMethodBodySupport.Packet principal,
        packet.sourceAt = sourceAt ∧ SelectedCompilationMethodBodySupport.Support
          principal packet (headers rows) (RecursiveNamedPreparedStageScopes.registry stagePrepared)
          (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) :
    Nonempty (Σ packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.Terminal code
        (RecursiveNamedPreparedStageScopes.registry stagePrepared),
      SelectedCompilationPhysicalClosureStaticSupport.SelectedBody (headers := headers rows)
        code support.body.toContext (RecursiveNamedPreparedStageScopes.registry stagePrepared) packet
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) := by
  have certified := SelectedCompilationOrdinaryClosureFacts.certified bodies callerReceipt
  have supported : CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported
      code.compilation.plan certificate.instantiation := by
    rw [support.compilation]
    exact certificate.direct.supported aligned
  have covered : ∀ index signature,
      SourceCompilationPlan.exactInstantiationKey code.compilation.plan certificate.instantiation = .ok signature.key →
      code.compilation.globals[index]? = some signature →
      ∃ header ∈ headers rows, header.slot = index ∧ header.named.signature = signature := by
    intro index signature target global
    rw [support.compilation] at target global
    exact certificate.direct.covered rows aligned target global
  obtain ⟨sidecar, _issued, selected⟩ :=
    CallableIndexedOwnedPreparedDirectStageScopeReceipts.code_scope code support.source_receipt support.body.unique
  exact SelectedCompilationPreparedOrdinaryCoercedTerminalSupport.of_actual
    stagePrepared code support provenance callerReceipt receiver bodies certified
    (by simpa only [support.source, CallableIndexedNamedGeneration.source] using certificate.metadata)
    rows checked catalog methods certificate.signatureMember
    (by simpa only [support.source, CallableIndexedNamedGeneration.source] using certificate.sourceOwner)
    methodBodies certificate.expression
    (by simpa only [support.source, CallableIndexedNamedGeneration.source] using certificate.terminal)
    (by simpa only [support.source, CallableIndexedNamedGeneration.source] using certificate.found)
    certificate.form certificate.coercions certificate.requirements
    (by simpa only [support.source, CallableIndexedNamedGeneration.source] using certificate.children)
    certificate.initializer supported covered _ (.anonymous selected)

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedCoercedClosureAdmission
