import Solcore.SourceSemantics.CoreLowering.RecursiveNamedExpressionCompilerCertificates
import Solcore.SourceSemantics.TraitSubstitutionProperties

/-! Independent whole-program typing authenticates the source parameters and
result of each actual named body. Signature identity and complete substitution
are retained. Native projection and invocation evidence are separate receipts;
neither is inferred from packed native types or source body typing. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedSourceSignatureFacts
open Frontend SourceInference RecursiveNamedCatalog

theorem instance_shape {program : Program} {instantiation : SourceInference.DeclarationInstantiation}
    {body : Dynamic.BodyInstance} {signature : ProgramFunctionSignature}
    (programTyped : ProgramWellFormed program)
    (member : signature ∈ program.signatures.functions)
    (selected : instantiation.declaration = signature.id)
    (instantiated : Dynamic.FunctionInstantiates program instantiation body) :
    body.source.inputs.map (fun binder => binder.scheme.body) =
      signature.parameterTypes.map instantiation.parameterSubstitution.apply ∧
    body.resultType = instantiation.parameterSubstitution.apply (TypeSystem.Ty.productMany signature.returnTypes) := by
  cases instantiated with
  | @intro actual definition _ actualMember definitionMember actualSelected owner valid sourceEq resultEq contextEq =>
    have actualEq : actual = signature := StructuralSubstitution.eq_of_mem_of_mapped_nodup
      programTyped.signatures.function_ids actualMember member (actualSelected.symm.trans selected)
    subst actual
    cases programTyped.functions_valid definition definitionMember with
    | @intro declared facts declaredMember declaredOwner bodyTyped =>
      have declaredEq : declared = signature := StructuralSubstitution.eq_of_mem_of_mapped_nodup
        programTyped.signatures.function_ids declaredMember member (declaredOwner.symm.trans owner)
      subst declared
      cases bodyTyped with
      | intro _ _ _ _ _ declaredResult _ _ _ extended _ _ _ _ _ _ =>
        refine ⟨?_, resultEq.trans (congrArg instantiation.parameterSubstitution.apply declaredResult)⟩
        have inputs := congrArg (List.map instantiation.parameterSubstitution.apply) extended.bodyTypes_eq
        simpa only [sourceEq, StructuralSubstitution.applyTypedSource, StructuralSubstitution.applyBinder,
          StructuralSubstitution.applyScheme, List.map_map, Function.comp_def] using inputs

variable {checked : CallableAncestryPairedLookup.Checked} {base : CallableAncestryPairedLookup.Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base}
  {values : SourceCoreCompatibleValues.Context} {definitions : Core.DataEnvironment} {program : Program}

/-- The actual source-frame parameters and result are authenticated separately
from their native carriers. All binder positions remain in source order. -/
theorem header_shape (header : Header prepared values definitions program)
    (programTyped : ProgramWellFormed program)
    {signature : ProgramFunctionSignature} (member : signature ∈ program.signatures.functions)
    (selected : header.instantiation.declaration = signature.id) :
    signature.parameterTypes.map header.instantiation.parameterSubstitution.apply =
      header.bindings.map (fun binding => binding.1.scheme.body) ∧
    header.instantiation.parameterSubstitution.apply (TypeSystem.Ty.productMany signature.returnTypes) =
      header.function.resultType := by
  have shape := instance_shape programTyped member selected header.frame.instantiated
  have inputs : header.bindings.map (fun binding => binding.1.scheme.body) =
      header.sourceBody.source.inputs.map (fun binder => binder.scheme.body) := by
    have parameters := congrArg (List.map (fun binder => binder.scheme.body))
      (header.parameters.symm.trans header.frame.parameters)
    simpa only [List.map_map, Function.comp_def] using parameters
  exact ⟨shape.1.symm.trans inputs.symm, shape.2.symm.trans header.frame.result.symm⟩

/-- Build the existing source-shape receipt from independent program typing.
Actual native projections and the exact invocation dictionary remain explicit. -/
theorem source_types {ambient : Core.AmbientDefinitions values.checked.catalog.definitions}
    {headers : Inventory prepared values ambient.definitions program} {context : Context}
    (programTyped : ProgramWellFormed program)
    (sameSignatures : context.signatures = program.signatures)
    (projections : ∀ header, header ∈ headers →
      (header.bindings.map (fun binding => binding.1.scheme.body)).mapM values.checked.catalog.project =
        .ok (header.bindings.map Prod.snd))
    (evidence : ∀ header, header ∈ headers → header.function.evidence = []) :
    RecursiveNamedExpressionCompilerCertificates.SourceTypes headers context := by
  refine ⟨?_, ?_, projections, evidence⟩
  · intro header _ signature member selected
    exact (header_shape header programTyped (sameSignatures ▸ member) selected).1
  · intro header _ signature member selected
    exact (header_shape header programTyped (sameSignatures ▸ member) selected).2

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedSourceSignatureFacts
