import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedProgramAdmission
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedScopedAdmission
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedFactoryAdmission
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationScopedFactoryAdmission
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalProgramSupport
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationProgramNamedSupport
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedProgramAdmission (Certificate)
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Issued Inventory headers)
open CallableIndexedOwnedPreparedNamedSyntaxAdmission (TableAligned)
open SelectedCompilationPhysicalProgramSupport (stagePrepared stages)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (certificate : Certificate compiled)
  (bodies : SelectedCompilationBodyTyping.Bodies compiled)
  {recipe : SourceCoreIndexedSession.Recipe} (ready : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
  (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
  (identity : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
  {initial : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (issued : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed initial.entry
    initial.result.context.registry initial.result.extension initial.result.diagnostics)
  (registry : initial.result.context.registry = compiled.compatible.checked.staticRegistry)
  {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
  (entryMember : entry ∈ compiled.indexed.entries)
  {inputs : List (Input compiled)} (rows : Inventory inputs)
  (aligned : TableAligned inputs certificate.table.rows)

include certificate bodies ready checked identity issued entryMember rows aligned in
theorem named_support (input : Input compiled) (packet : Issued input) :
    Nonempty (Σ body : CallableIndexedOwnedPreparedStagedNamedBodies.Body packet.header,
      SelectedCompilationPhysicalNamedBodySupport.Support
        (headers := headers rows) (bodyRegistry := initial.result.context.registry)
        (stages := stages compiled)
        (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults initial.result.diagnostics)
        packet.header body) := by
  obtain ⟨source⟩ := certificate.rows input.prepared.named (List.mem_of_getElem? input.prepared.selected)
  let prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued input.prepared packet.selected
  have diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared :=
    ⟨packet.selected.diagnostics, packet.selected.found, rfl⟩
  have certified : SelectedCompilationNamedSourceTyping.Certified packet.header :=
    SelectedCompilationHeaders.certificate_at prepared bodies input.range packet.aligned
  cases source.root with
  | «scoped» admission =>
    have original := CallableIndexedOwnedPreparedNamedSourceAdmissionTransport.source_at_header
      prepared packet.aligned input.prepared.selected input.prepared.same admission
    exact SelectedCompilationNamedScopedAdmission.of_actual prepared packet.aligned rows aligned
      original ready diagnostic issued bodies certified checked identity
      certificate.selection.operatorCatalog
      entryMember (stagePrepared compiled)
  | formation admission =>
    obtain ⟨terminal, ⟨supported⟩⟩ := SelectedCompilationNamedFactoryAdmission.of_actual
      prepared packet.aligned input.prepared.selected input.prepared.same admission ready diagnostic
      certified certificate.profile entryMember
    exact ⟨⟨CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal terminal,
      .formation terminal supported packet.aligned.globals⟩⟩
  | scopedFactory admission =>
    obtain ⟨terminal, ⟨supported⟩⟩ := SelectedCompilationScopedFactoryAdmission.of_actual
      prepared packet.aligned input.prepared.selected input.prepared.same admission ready diagnostic
      certified bodies.signatures certificate.profile entryMember
    exact ⟨⟨CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal terminal,
      .formation terminal supported packet.aligned.globals⟩⟩
  | excluded absent =>
    obtain ⟨request, signature, generic, member, _genericMember, _resolved, specialized⟩ := input.prepared.origin
    have fields := RecursiveNamedSpecializationBodyFacts.identities specialized
    have declaration : input.prepared.named.specialized.declaration = signature.id :=
      (congrArg (·.declaration) input.prepared.same).trans (fields.2.2.trans fields.1.symm)
    exact False.elim (absent signature member declaration)

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationProgramNamedSupport
