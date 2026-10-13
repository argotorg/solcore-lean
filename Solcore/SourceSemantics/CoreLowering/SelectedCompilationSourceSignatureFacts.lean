import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCatalog
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedSourceSignatureFacts

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationSourceSignatureFacts
open Frontend SourceInference RecursiveNamedCatalog
open CallableIndexedOwnedPreparedFiniteNamedInventories
open CallableIndexedOwnedPreparedOrdinaryCachedInputs

theorem instance_shape_of_valid {program : Program} {instantiation : SourceInference.DeclarationInstantiation}
    {body : Dynamic.BodyInstance} {signature : ProgramFunctionSignature}
    (catalog : SignatureCatalogWellFormed program.signatures)
    (owners : (program.functions.map fun definition => definition.body.owner).Nodup)
    {chosen : FunctionDefinition} (chosenMember : chosen ∈ program.functions)
    (chosenOwner : chosen.body.owner = instantiation.declaration)
    (chosenValid : FunctionDefinition.Valid program.signatures chosen)
    (member : signature ∈ program.signatures.functions)
    (selected : instantiation.declaration = signature.id)
    (instantiated : Dynamic.FunctionInstantiates program instantiation body) :
    body.source.inputs.map (fun binder => binder.scheme.body) =
      signature.parameterTypes.map instantiation.parameterSubstitution.apply ∧
    body.resultType = instantiation.parameterSubstitution.apply (TypeSystem.Ty.productMany signature.returnTypes) := by
  cases instantiated with
  | @intro actual definition _ actualMember definitionMember actualSelected owner valid sourceEq resultEq contextEq =>
    have actualEq : actual = signature := StructuralSubstitution.eq_of_mem_of_mapped_nodup
      catalog.function_ids actualMember member (actualSelected.symm.trans selected)
    subst actual
    have same : chosen = definition := StructuralSubstitution.eq_of_mem_of_mapped_nodup
      owners chosenMember definitionMember
        (chosenOwner.trans (actualSelected.trans owner.symm))
    subst chosen
    cases chosenValid with
    | @intro declared facts declaredMember declaredOwner bodyTyped =>
      have declaredEq : declared = signature := StructuralSubstitution.eq_of_mem_of_mapped_nodup
        catalog.function_ids declaredMember member (declaredOwner.symm.trans owner)
      subst declared
      cases bodyTyped with
      | intro _ _ _ _ _ declaredResult _ _ _ extended _ _ _ _ _ _ =>
        refine ⟨?_, resultEq.trans (congrArg instantiation.parameterSubstitution.apply declaredResult)⟩
        have inputs := congrArg (List.map instantiation.parameterSubstitution.apply) extended.bodyTypes_eq
        simpa only [sourceEq, StructuralSubstitution.applyTypedSource, StructuralSubstitution.applyBinder,
          StructuralSubstitution.applyScheme, List.map_map, Function.comp_def] using inputs


/-- Source argument order and result of this exact selected Header. -/
def Shape {checked : CallableAncestryPairedLookup.Checked}
    {base : CallableAncestryPairedLookup.Base checked}
    {prepared : SourceCoreCallableIndexedAncestry.Prepared base}
    {values : SourceCoreCompatibleValues.Context} {definitions : Core.DataEnvironment} {program : Program}
    (header : RecursiveNamedCatalog.Header prepared values definitions program) : Prop :=
  ∀ signature ∈ program.signatures.functions,
    header.instantiation.declaration = signature.id →
      signature.parameterTypes.map header.instantiation.parameterSubstitution.apply =
        header.bindings.map (fun binding => binding.1.scheme.body) ∧
      header.instantiation.parameterSubstitution.apply (TypeSystem.Ty.productMany signature.returnTypes) =
        header.function.resultType

theorem header_shape
    {compiled : SourceCoreUnifiedCompilation.Compiled}
    {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    (bodies : SelectedCompilationBodyTyping.Bodies compiled)
    {values : SourceCoreCompatibleValues.Context}
    {header : Header compiled.indexed.ancestry values compiled.indexed.layouts.definitions
      (Program.ofChecked compiled.sourceProgram)}
    (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared
      (CallableNamedCanonicalOrder.retainedInstantiation row) header)
    {signature : ProgramFunctionSignature} (member : signature ∈ compiled.sourceProgram.signatures.functions)
    (selected : header.instantiation.declaration = signature.id) :
    signature.parameterTypes.map header.instantiation.parameterSubstitution.apply =
      header.bindings.map (fun binding => binding.1.scheme.body) ∧
    header.instantiation.parameterSubstitution.apply (TypeSystem.Ty.productMany signature.returnTypes) =
      header.function.resultType := by
  obtain ⟨request, original, generic, originalMember, genericMember, resolved, accepted⟩ := prepared.origin
  have valid := bodies.ordinary generic
    ⟨prepared.index, prepared.named, original, request.parameterSubstitution, prepared.selected,
      originalMember, genericMember, by simpa only [prepared.same] using accepted⟩
  have owner : (FunctionDefinition.ofChecked generic).body.owner = header.instantiation.declaration := by
    rw [aligned.metadata]
    exact ((RecursiveNamedSpecializationBodyFacts.identities accepted).2.2).symm
  have shape := instance_shape_of_valid bodies.signatures bodies.function_ids
    (List.mem_map.mpr ⟨generic, genericMember, rfl⟩) owner valid member selected header.frame.instantiated
  have inputs : header.bindings.map (fun binding => binding.1.scheme.body) =
      header.sourceBody.source.inputs.map (fun binder => binder.scheme.body) := by
    have parameters := congrArg (List.map (fun binder => binder.scheme.body))
      (header.parameters.symm.trans header.frame.parameters)
    simpa only [List.map_map, Function.comp_def] using parameters
  exact ⟨shape.1.symm.trans inputs.symm, shape.2.symm.trans header.frame.result.symm⟩

theorem inventory_shape {compiled : SourceCoreUnifiedCompilation.Compiled}
    (bodies : SelectedCompilationBodyTyping.Bodies compiled)
    {inputs : List (Input compiled)}
    (rows : Inventory inputs)
    (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
    (included : header ∈ headers rows)
    {signature : ProgramFunctionSignature} (member : signature ∈ compiled.sourceProgram.signatures.functions)
    (selected : header.instantiation.declaration = signature.id) :
    signature.parameterTypes.map header.instantiation.parameterSubstitution.apply =
      header.bindings.map (fun binding => binding.1.scheme.body) ∧
    header.instantiation.parameterSubstitution.apply (TypeSystem.Ty.productMany signature.returnTypes) =
      header.function.resultType := by
  obtain ⟨input, packet, _, same⟩ := rows.mem_headers header included
  subst header
  exact header_shape (CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued input.prepared packet.selected)
    bodies packet.aligned member selected

theorem Shape.of_prepared
    {compiled : SourceCoreUnifiedCompilation.Compiled}
    {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    (bodies : SelectedCompilationBodyTyping.Bodies compiled)
    {values : SourceCoreCompatibleValues.Context}
    {header : RecursiveNamedCatalog.Header compiled.indexed.ancestry values compiled.indexed.layouts.definitions
      (Program.ofChecked compiled.sourceProgram)}
    (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared
      (CallableNamedCanonicalOrder.retainedInstantiation row) header) : Shape header := by
  intro signature member selected
  exact header_shape prepared bodies aligned member selected

theorem Shape.of_inventory {compiled : SourceCoreUnifiedCompilation.Compiled}
    (bodies : SelectedCompilationBodyTyping.Bodies compiled)
    {inputs : List (Input compiled)} (rows : Inventory inputs)
    (header : CallableIndexedOwnedPreparedFiniteNamedInventories.Header compiled)
    (included : header ∈ headers rows) : Shape header := by
  intro signature member selected
  exact inventory_shape bodies rows header included member selected

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationSourceSignatureFacts
