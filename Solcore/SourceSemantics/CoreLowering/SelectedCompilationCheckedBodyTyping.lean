import Solcore.SourceSemantics.SourceInferenceSelectedCheckedBodyTypingBridge
import Solcore.SourceSemantics.SourceInferenceSelectedActualSoundness
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationSelectedBodyInterfaces

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationCheckedBodyTyping
open Frontend SourceInference TypeSystem
open SourceInferenceSoundness

/-- Only the selected original function uses the recursive source theorem.
Its header and original body-checking receipt come from the public checker. -/
theorem ordinary_valid
    {raw : Workspace.RawWorkspace} {fuel : Nat} {program : CheckedProgram}
    (checked : Frontend.checkProgram raw fuel = .ok program)
    {function : CheckedFunction} (member : function ∈ program.functions)
    (interfaces : ExecutableCoercionInterfaces.BodyInterfaces program.signatures function)
    (monomorphic : ExecutableBinderInterfaces.SourceMonomorphic function.typedBody)
    (recursiveSound : ActualInferStatementsFuelSoundness fuel) :
    FunctionDefinition.Valid program.signatures (FunctionDefinition.ofChecked function) := by
  apply functionDefinitionValid_ofCheckProgram checked member
  intro signature signatureMember bodySuccess
  obtain ⟨headerSignature, headerMember, header⟩ :=
    checkedFunctionHeaderWellFormed_ofCheckProgram checked member
  have signatureEq : headerSignature = signature := by
    have catalog := SignatureCatalogWellFormed.ofCheckProgram checked
    exact eq_of_mem_of_nodup_map catalog.function_ids headerMember signatureMember
      (header.declaration_eq.symm.trans (checkFunctionBody_success_declaration bodySuccess))
  subst headerSignature
  have predicatesFixed : signature.scheme.predicates.map
      (TypedTraitResolution.applySubstitution function.substitution) = signature.scheme.predicates :=
    ((Frontend.checkProgram_success_signature_formation checked).functions
      signature signatureMember).2.2.apply_eq_self function.substitution
  apply checkedBodyHasType_ofStatements bodySuccess
  exact SelectedCheckedBodyTypingBridge.checkedBodyStatementsHaveType_ofCheckProgram_function
    checked signatureMember header predicatesFixed bodySuccess interfaces monomorphic recursiveSound

/-- The selected method retains its actual implementation, trait signature
and original checker carrier throughout body typing. -/
theorem method_valid
    {raw : Workspace.RawWorkspace} {fuel : Nat} {program : CheckedProgram}
    (checked : Frontend.checkProgram raw fuel = .ok program)
    {retained : CheckedImplementationMethod} (member : retained ∈ program.methods)
    (interfaces : ExecutableCoercionInterfaces.BodyInterfaces program.signatures retained.checked)
    (monomorphic : ExecutableBinderInterfaces.SourceMonomorphic retained.checked.typedBody)
    (recursiveSound : ActualInferStatementsFuelSoundness fuel) :
    MethodDefinition.Valid program.signatures (MethodDefinition.ofChecked retained) := by
  apply methodDefinitionValid_ofCheckProgram checked member
  intro implementation method trait implementationMember methodMember traitLookup bodySuccess
  let catalog := SignatureCatalogWellFormed.ofCheckProgram checked
  have implementationWellFormed := catalog.implementations_semantic implementation implementationMember
  have methodWellFormed := implementationWellFormed.methods method methodMember
  obtain ⟨semanticTrait, traitMethod, semanticTraitMember, selectedHeadTrait,
    traitMethodMember, traitMethodId, _, _, _, _, _, _⟩ := methodWellFormed.trait_method
  have rawLookup : program.signatures.traits.find?
      (fun candidate => decide (candidate.id = method.traitMethod.trait)) = some trait := by
    simpa [ProgramSignatures.trait?] using traitLookup
  have selectedMember : trait ∈ program.signatures.traits := List.mem_of_find?_eq_some rawLookup
  have selectedId : trait.id = method.traitMethod.trait := of_decide_eq_true (List.find?_some
    (p := fun candidate : ProgramTraitSignature => decide (candidate.id = method.traitMethod.trait)) rawLookup)
  have semanticTraitWellFormed := catalog.traits_semantic semanticTrait semanticTraitMember
  have traitMethodWellFormed := semanticTraitWellFormed.methods traitMethod traitMethodMember
  have semanticId : semanticTrait.id = method.traitMethod.trait := by
    rw [← traitMethodWellFormed.owner]
    exact congrArg ProgramTraitMethodId.trait traitMethodId
  have traitEq : trait = semanticTrait := Frontend.trait_signature_eq_of_mem_of_id_eq
    catalog.trait_ids selectedMember semanticTraitMember (selectedId.trans semanticId.symm)
  subst semanticTrait
  let signature := implementation.functionSignatureOfMethodWithTrait trait method
  have header : CheckedBodyHeaderWellFormed program.signatures signature retained.checked :=
    CheckedBodyHeaderWellFormed.ofCheckImplementationMethod implementationWellFormed methodWellFormed bodySuccess
  have predicatesFixed : signature.scheme.predicates.map
      (TypedTraitResolution.applySubstitution retained.checked.substitution) = signature.scheme.predicates := by
    simpa [signature, ProgramImplementationSignature.functionSignatureOfMethodWithTrait,
      ProgramImplementationSignature.functionSignatureOfMethod] using
      methodAssumptions_applySubstitution_eq_self catalog implementationMember methodMember
        selectedMember selectedHeadTrait retained.checked.substitution
  apply checkedBodyHasType_ofStatements bodySuccess
  exact SelectedCheckedBodyTypingBridge.checkedBodyStatementsHaveType_ofCheckProgram_method
    checked implementationMember header predicatesFixed bodySuccess interfaces monomorphic recursiveSound

/-- Actual checking, the complete selected compiler profile and recursive
inference soundness construct the body certificate for exactly the retained
compilation scope. The full original program remains unchanged. -/
theorem of_checked_profile
    {raw : Workspace.RawWorkspace} {fuel : Nat} {compiled : SourceCoreUnifiedCompilation.Compiled}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.sourceProgram)
    (profile : CompilerProgramStaticProfile.StaticProfile compiled)
    (recursiveSound : ActualInferStatementsFuelSoundness fuel) :
    SelectedCompilationBodyTyping.Bodies compiled := by
  let catalog := SignatureCatalogWellFormed.ofCheckProgram checked
  obtain ⟨functionIds, methodIds⟩ := Frontend.checkProgram_success_ids checked
  refine ⟨catalog, ?_, ?_, ?_, ?_⟩
  · simp only [Program.ofChecked, List.map_map, Function.comp_def,
      FunctionDefinition.ofChecked, BodyDefinition.ofChecked]
    rw [functionIds]
    exact catalog.function_ids
  · simp only [Program.ofChecked, List.map_map, Function.comp_def, MethodDefinition.ofChecked]
    rw [methodIds]
    exact catalog.implementation_method_ids
  · intro generic selected
    obtain ⟨interfaces, monomorphic⟩ :=
      SelectedCompilationSelectedBodyInterfaces.ordinary checked profile selected
    obtain ⟨index, named, signature, supplied, cached, signatureMember, member, accepted⟩ := selected
    exact ordinary_valid checked member interfaces monomorphic recursiveSound
  · intro retained selected
    obtain ⟨interfaces, monomorphic⟩ :=
      SelectedCompilationSelectedBodyInterfaces.method checked profile selected
    obtain ⟨index, named, method, cached, same, selection, member, identity, original⟩ := selected
    exact method_valid checked member interfaces monomorphic recursiveSound

/-- Successful checking and the accepted compiler profile provide typing for
all selected original bodies. Recursive checker soundness is discharged inside
this producer, using the original checking budget and complete source program. -/
theorem of_checked
    {raw : Workspace.RawWorkspace} {fuel : Nat} {compiled : SourceCoreUnifiedCompilation.Compiled}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.sourceProgram)
    (profile : CompilerProgramStaticProfile.StaticProfile compiled) :
    SelectedCompilationBodyTyping.Bodies compiled :=
  of_checked_profile checked profile (actualInferStatementsFuelSoundness_selected fuel)

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationCheckedBodyTyping
