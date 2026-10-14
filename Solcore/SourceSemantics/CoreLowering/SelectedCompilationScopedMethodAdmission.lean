import Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodEvidenceScopedRoots
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodBodies
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedScopedMethodAdmission
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationScopedMethodAdmission
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedScopedMethodAdmission (Certificate)
open CallableIndexedOwnedPreparedNamedSyntaxAdmission (DirectSite TableAligned)
open CallableIndexedOwnedPreparedNamedSourceAdmissionTransport (statements)
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {directRows : List SourceSpecialization.SpecializedFunction}
  (certificate : Certificate compiled directRows)
  {method : ExecutableImplMethods.CheckedMethod}
  (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)

include certificate in
/-- Genuine method selection supplies the resolved caller internally to the
program issuer. The certificate supplies static Source syntax and metadata. -/
theorem support
    (sourceAt : CallablePreparedMethodRuntimeProfileFactory.SourceAt principal.cached.compilation
      (.initial compiled.compatible.checked) principal.sourceBody principal.dictionary)
    (resolved : CallableIndexedOwnedPreparedStagedDirectCallAuthority.ResolvedCaller
      compiled.sourceProgram principal.named.specialized principal.dictionary)
    (diagnostic : CallableIndexedOwnedPreparedStagedMethodTerminalSupport.DiagnosticAt principal.cached)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (bodies : SelectedCompilationBodyTyping.Bodies compiled)
    (certified : SelectedCompilationMethodBodySupport.Certified principal sourceAt)
    {inputs : List (Input compiled)} (rows : Inventory inputs) (aligned : TableAligned inputs directRows)
    {recipe : SourceCoreIndexedSession.Recipe}
    (ready : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : entry ∈ compiled.indexed.entries)
    (stages : Staging.Recursive.Registry) :
    ∃ packet : SelectedCompilationMethodBodies.Packet principal,
      packet.sourceAt = sourceAt ∧ SelectedCompilationMethodBodies.Support
        principal packet (headers rows) stages
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics) := by
  obtain ⟨source⟩ := certificate.selected principal
  have roots : statements (CallableIndexedNamedGeneration.source principal.named) = principal.cached.compilation.statements := by
    rw [principal.source_eq]
    exact principal.source_frame.roots.filterMap_eq
  have resultType : principal.named.specialized.function.inferredBodyType = principal.sourceBody.resultType := by
    rw [principal.cached.same]
    rfl
  have shape := source.source.body.shape
  rw [roots, principal.source_eq] at shape
  have accepted := sourceAt.accepted principal.cached.compilation
  unfold SourceCoreLoops.lowerStatementsWithPolicy at accepted
  obtain ⟨flow, generated, returned⟩ := CompatibleEncoding.bind_ok accepted
  let packet : SelectedCompilationMethodScopedSupport.Packet principal :=
    ⟨sourceAt, flow, generated, (Except.ok.inj returned).symm, shape⟩
  refine ⟨.scoped packet, rfl, ?_⟩
  apply SelectedCompilationMethodEvidenceScopedRoots.of_actual_with_evidence
    (directSites := DirectSite directRows)
    principal packet diagnostic receiver bodies certified
    (by simpa only [principal.source_eq] using source.forms)
    (fun _ site => site.supported aligned)
    (by simpa only [principal.source_eq] using source.source.metadata)
    rows (fun _ site _ _ target global => site.covered rows aligned target global)
    resolved ready member
  obtain ⟨final, facts, typed, _complete⟩ :=
    SelectedCompilationMethodScopedSupport.statements principal packet certified
  have body := source.source.body
  rw [roots, principal.source_eq, resultType] at body
  exact body.syntax sourceAt.unique typed

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationScopedMethodAdmission
