import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCatalog
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationHeaderFacts
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationOrdinaryAnnotationCoherence
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOrdinaryCallerReceipts

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationOrdinaryClosureFacts
open Core Frontend SourceInference

/-- The retained caller's real target and cache record identify its selected
original definition, including an invocation outside the current inventory. -/
theorem certified {compiled : SourceCoreUnifiedCompilation.Compiled}
    {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    (bodies : SelectedCompilationBodyTyping.Bodies compiled)
    (caller : CallableIndexedOwnedOrdinaryCallerReceipts.CallerAt header context evidence) :
    SelectedCompilationNamedSourceTyping.Certified header := by
  obtain ⟨request, signature, generic, signatureMember, genericMember, _resolved, accepted⟩ := caller.prepared.origin
  have valid := bodies.ordinary generic
    ⟨caller.prepared.index, caller.prepared.named, signature, request.parameterSubstitution,
      caller.prepared.selected, signatureMember, genericMember,
      by simpa only [caller.prepared.same] using accepted⟩
  have matched := CallableNamedMetadata.matches_of_exact header.target
    (CallableIndexedActualNamedSourceReceipts.header_record compiled header)
  have owner : (FunctionDefinition.ofChecked generic).body.owner = header.instantiation.declaration :=
    (RecursiveNamedSpecializationBodyFacts.identities accepted).2.2.symm.trans matched.declaration
  obtain ⟨types, lexical, facts, certificate⟩ :=
    header.frame.instantiated.certificate_of_valid bodies.signatures bodies.function_ids
      (List.mem_map.mpr ⟨generic, genericMember, rfl⟩) owner valid
  have extended := header.extended
  rw [header.frame.source, header.frame.context, header.frame.parameters] at extended
  have contextEq := Dynamic.MonoBindersExtend.functional certificate.typing.inputs_extend extended
  have typesEq := (Dynamic.MonoBindersExtend.bodyTypes_eq certificate.typing.inputs_extend).symm.trans
    (Dynamic.MonoBindersExtend.bodyTypes_eq extended)
  exact ⟨facts, typesEq ▸ contextEq ▸ certificate⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationOrdinaryClosureFacts
