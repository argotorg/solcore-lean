import Solcore.SourceSemantics.SelectedBodyTypingCertificates
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicSpecializationMeaning
import Solcore.SourceSemantics.CoreLowering.CallableCoercionBodyProvenance

set_option autoImplicit false
set_option Elab.async false

namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationBodyTyping
open Frontend SourceInference TypeSystem

/-- The selected ordinary definition is identified by its actual cached row
and complete successful specialization, including unused replacement rows. -/
def OrdinarySource (compiled : SourceCoreUnifiedCompilation.Compiled)
    (generic : CheckedFunction) : Prop :=
  ∃ (index : Nat) (named : SourceCoreGeneralFunctions.Function)
      (signature : ProgramFunctionSignature) (supplied : ParameterSubstitution),
    compiled.indexed.base.functions[index]? = some named ∧
    signature ∈ compiled.sourceProgram.signatures.functions ∧
    generic ∈ compiled.sourceProgram.functions ∧
    SourceSpecialization.specializeFunction signature generic supplied = .ok named.specialized

/-- A selected method retains the real cache, original method identity and
complete checker carrier recovered by the original method coherence receipt. -/
def MethodSource (compiled : SourceCoreUnifiedCompilation.Compiled)
    (retained : CheckedImplementationMethod) : Prop :=
  ∃ (index : Nat) (named : SourceCoreGeneralFunctions.Function)
      (method : ExecutableImplMethods.CheckedMethod),
    compiled.indexed.base.functions[index]? = some named ∧
    named.specialized = method.specialized ∧
    ∃ selection : CallableCoercionBodyProvenance.Selection compiled.sourceProgram method,
      retained ∈ compiled.sourceProgram.methods ∧ retained.id = method.id ∧
        selection.generic = retained.checked

/-- Global identity facts and typing of only the original definitions selected
by the complete compiled cache. The original program and signature IDs stay fixed. -/
structure Bodies (compiled : SourceCoreUnifiedCompilation.Compiled) : Prop where
  signatures : SignatureCatalogWellFormed compiled.sourceProgram.signatures
  function_ids : ((Program.ofChecked compiled.sourceProgram).functions.map
    fun definition => definition.body.owner).Nodup
  method_ids : ((Program.ofChecked compiled.sourceProgram).methods.map
    fun definition => definition.id).Nodup
  ordinary : ∀ generic, OrdinarySource compiled generic →
    FunctionDefinition.Valid compiled.sourceProgram.signatures (FunctionDefinition.ofChecked generic)
  methods : ∀ retained, MethodSource compiled retained →
    MethodDefinition.Valid compiled.sourceProgram.signatures (MethodDefinition.ofChecked retained)

namespace Bodies
variable {compiled : SourceCoreUnifiedCompilation.Compiled}

/-- Existing whole-program clients can use the narrower interface directly. -/
theorem of_program (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    Bodies compiled := by
  refine ⟨wellFormed.signatures, wellFormed.function_ids, wellFormed.method_ids, ?_, ?_⟩
  · intro generic selected
    obtain ⟨index, named, signature, supplied, cached, signatureMember, member, accepted⟩ := selected
    exact wellFormed.functions_valid _ (List.mem_map.mpr ⟨generic, member, rfl⟩)
  · intro retained selected
    obtain ⟨index, named, method, cached, same, selection, member, identity, checked⟩ := selected
    exact wellFormed.methods_valid _ (List.mem_map.mpr ⟨retained, member, rfl⟩)

/-- An authentic prepared row supplies all membership facts for its original body. -/
theorem prepared_certificate (bodies : Bodies compiled)
    {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures compiled.sourceProgram.signatures) row.parameterSubstitution) :
    ∃ types context facts,
      Dynamic.FunctionInstanceTypingCertificate (Program.ofChecked compiled.sourceProgram)
        (CallableNamedMetadata.instantiation row)
        (RecursiveNamedSpecializationBodyFacts.bodyInstance compiled.sourceProgram row)
        types context facts := by
  obtain ⟨request, signature, generic, signatureMember, genericMember, resolved, accepted⟩ := prepared.origin
  have valid := bodies.ordinary generic
    ⟨prepared.index, prepared.named, signature, request.parameterSubstitution, prepared.selected,
      signatureMember, genericMember, by simpa only [prepared.same] using accepted⟩
  have instantiated := RecursiveNamedSpecializationValidity.instantiated signatureMember genericMember
    accepted (bodies.signatures.function_parameters signature signatureMember).1 range
  have owner : (FunctionDefinition.ofChecked generic).body.owner =
      (CallableNamedMetadata.instantiation row).declaration := by
    exact ((RecursiveNamedSpecializationBodyFacts.identities accepted).2.2).symm
  exact instantiated.certificate_of_valid bodies.signatures bodies.function_ids
    (List.mem_map.mpr ⟨generic, genericMember, rfl⟩) owner valid

/-- A selected method instance uses the retained original definition authenticated
by its exact cache row and method-checking provenance. -/
theorem method_certificate (bodies : Bodies compiled)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (cached : compiled.indexed.base.functions[index]? = some named)
    {method : ExecutableImplMethods.CheckedMethod}
    (same : named.specialized = method.specialized)
    (selection : CallableCoercionBodyProvenance.Selection compiled.sourceProgram method)
    {retained : CheckedImplementationMethod}
    (member : retained ∈ compiled.sourceProgram.methods)
    (identity : retained.id = method.id) (original : selection.generic = retained.checked)
    {substitution : ParameterSubstitution} {bodyInstance : Dynamic.BodyInstance}
    (instantiates : Dynamic.TraitMethodInstantiates (Program.ofChecked compiled.sourceProgram)
      selection.implementation selection.declaration selection.trait
      (MethodDefinition.ofChecked retained) substitution bodyInstance) :
    ∃ types context facts,
      Dynamic.TraitMethodInstanceTypingCertificate (Program.ofChecked compiled.sourceProgram)
        selection.declaration substitution (MethodDefinition.ofChecked retained) bodyInstance
        types context facts := by
  exact instantiates.certificate_of_valid bodies.signatures
    (bodies.methods retained ⟨index, named, method, cached, same, selection, member, identity, original⟩)

end Bodies
end Solcore.SourceSemantics.CoreLowering.SelectedCompilationBodyTyping
