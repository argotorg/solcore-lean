import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCatalog
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedSourceTyping

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationHeaderCertificates
open Core Frontend SourceInference

/-- Every genuine Header retains its actual cached ordinary origin, even when
it is used as an anchor outside the current finite inventory. -/
theorem certified {compiled : SourceCoreUnifiedCompilation.Compiled}
    (bodies : SelectedCompilationBodyTyping.Bodies compiled)
    (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)) :
    SelectedCompilationNamedSourceTyping.Certified header := by
  have signature : ∃ signature ∈ compiled.sourceProgram.signatures.functions,
      header.instantiation.declaration = signature.id := by
    have instantiated := header.frame.instantiated
    cases instantiated with
    | @intro signature _ _ member _ declaration _ _ _ _ _ =>
      exact ⟨signature, member, declaration⟩
  obtain ⟨signature, member, declaration⟩ := signature
  have record := CallableIndexedActualNamedSourceReceipts.header_record compiled header
  have matched := CallableNamedMetadata.matches_of_exact header.target record
  have origin := SelectedCompilationCatalog.ordinary_origin compiled bodies.signatures
    (CallableNamedMetadata.specialization_of_exact record).1 member
    (matched.declaration.trans declaration)
  obtain ⟨request, actualSignature, generic, signatureMember, genericMember, _resolved, accepted⟩ := origin
  have valid := bodies.ordinary generic
    ⟨header.slot, header.named, actualSignature, request.parameterSubstitution,
      header.selected, signatureMember, genericMember, accepted⟩
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

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationHeaderCertificates
