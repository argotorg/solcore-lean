import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPrimitiveMethodTerminalSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPrimitiveMethodAdmission
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPrimitiveMethodAdmission
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedPrimitiveMethodAdmission (Certificate)
open CallableIndexedOwnedPreparedNamedSourceAdmissionTransport (statements)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (certificate : Certificate compiled)
  {method : ExecutableImplMethods.CheckedMethod}
  (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)

include certificate in
/-- SourceAt fixes the original method context, evidence and body typing. The
actual accepted compiler action issues the static packet used by the family. -/
theorem support
    (sourceAt : CallablePreparedMethodRuntimeProfileFactory.SourceAt principal.cached.compilation
      (.initial compiled.compatible.checked) principal.sourceBody principal.dictionary)
    (diagnostic : CallableIndexedOwnedPreparedStagedMethodTerminalSupport.DiagnosticAt principal.cached)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (signatures : SignatureCatalogWellFormed compiled.sourceProgram.signatures)
    (certified : SelectedCompilationMethodBodySupport.Certified principal sourceAt)
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
    (stages : Staging.Recursive.Registry) :
    ∃ packet : SelectedCompilationMethodBodySupport.Packet principal,
      packet.sourceAt = sourceAt ∧ SelectedCompilationMethodBodySupport.Support
        principal packet headers stages (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics) := by
  obtain ⟨source⟩ := certificate.selected principal
  have roots : statements (CallableIndexedNamedGeneration.source principal.named) = principal.cached.compilation.statements := by
    rw [principal.source_eq]
    exact principal.source_frame.roots.filterMap_eq
  have terminal := source.terminal
  rw [roots, principal.source_eq] at terminal
  obtain ⟨receipt⟩ := CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.of_accepted
    (by rfl) terminal sourceAt.accepted
  let packet : SelectedCompilationMethodBodySupport.Packet principal :=
    ⟨sourceAt, source.expression, receipt⟩
  refine ⟨packet, rfl, ?_⟩
  apply SelectedCompilationPrimitiveMethodTerminalSupport.of_actual principal packet diagnostic receiver signatures certified
  · simpa only [principal.source_eq] using source.forms
  · simpa only [principal.source_eq] using source.metadata
  · simpa only [principal.source_eq] using source.tree

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPrimitiveMethodAdmission
