import Solcore.SourceSemantics.CoreLowering.SelectedCompilationRegistryGlobals
import Solcore.SourceSemantics.SelectedOperatorTypingCertificates

/-! Actual checker headers align a shared instantiated body certificate with
the exact method selected by Source execution. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodCertificateTransport
open Frontend SourceInference TypeSystem
open Solcore.SourceSemantics.Dynamic

theorem of_body {program : CheckedProgram} {raw : Workspace.RawWorkspace} {fuel : Nat}
    (checked : Frontend.checkProgram raw fuel = .ok program)
    {implementation : ProgramImplementationSignature} {method : ProgramImplMethodSignature}
    {trait : ProgramTraitSignature} {definition : MethodDefinition}
    {substitution : ParameterSubstitution} {body : BodyInstance}
    {inputTypes : List Ty} {lexical : Context} {facts : BodyFacts}
    (instantiates : TraitMethodInstantiates (Program.ofChecked program)
      implementation method trait definition substitution body)
    (certificate : BodyInstanceTypingCertificate (Program.ofChecked program)
      body inputTypes lexical facts) :
    TraitMethodInstanceTypingCertificate (Program.ofChecked program)
      method substitution definition body inputTypes lexical facts := by
  cases instantiates with
  | intro implementationMember methodMember _ _ definitionMember definitionId _ _ _ sourceEq resultEq _ =>
    obtain ⟨retained, retainedMember, rfl⟩ := List.mem_map.mp definitionMember
    obtain ⟨checkedImplementation, checkedMethod, checkedTrait, checkedImplementationMember,
      checkedMethodMember, _, checkedId, header⟩ :=
      checkedMethodHeaderWellFormed_ofCheckProgram checked retainedMember
    have catalog := SignatureCatalogWellFormed.ofCheckProgram checked
    have methodIds : ((program.signatures.implementations.flatMap (fun item => item.methods)).map
        (fun item => item.id)).Nodup := by
      simpa [List.map_flatMap, Function.comp_def] using catalog.implementation_method_ids
    have sameMethod : checkedMethod = method :=
      StructuralSubstitution.eq_of_mem_of_mapped_nodup methodIds
        (List.mem_flatMap.mpr ⟨checkedImplementation, checkedImplementationMember, checkedMethodMember⟩)
        (List.mem_flatMap.mpr ⟨implementation, implementationMember, methodMember⟩)
        (checkedId.symm.trans definitionId)
    subst checkedMethod
    obtain ⟨genericLexical, genericInputs⟩ := header.inputs_extend
    have genericTypes : retained.checked.typedBody.inputs.map (fun binder => binder.scheme.body) =
        method.parameterTypes := MonoBindersExtend.bodyTypes_eq genericInputs
    have types : inputTypes = method.parameterTypes.map substitution.apply := by
      rw [← MonoBindersExtend.bodyTypes_eq certificate.typing.inputs_extend, sourceEq]
      change ((StructuralSubstitution.applyTypedSource substitution retained.checked.typedBody).inputs.map
        (fun binder => binder.scheme.body)) = _
      simp only [StructuralSubstitution.applyTypedSource, List.map_map, Function.comp_def,
        StructuralSubstitution.applyBinder, StructuralSubstitution.applyScheme]
      simpa only [List.map_map, Function.comp_def] using congrArg (List.map substitution.apply) genericTypes
    have result : body.resultType = substitution.apply (Ty.productMany method.returnTypes) := by
      rw [resultEq]
      exact congrArg substitution.apply header.result_type
    refine { certificate with input_types_eq := types, result_type_eq := result, callable_type := ?_ }
    change substitution.apply retained.checked.type = _
    rw [header.callable_type]
    change Ty.function (substitution.apply (Ty.productMany method.parameterTypes))
      (substitution.apply (Ty.productMany method.returnTypes)) = _
    rw [StructuralSubstitution.apply_productMany, ← types, ← result]

theorem selected {program : CheckedProgram} {raw : Workspace.RawWorkspace} {fuel : Nat}
    (checked : Frontend.checkProgram raw fuel = .ok program)
    {context : Context} {evidence dictionary : EvidenceEnvironment}
    {traitName methodName : String} {requirements : List RequirementId} {body : BodyInstance}
    (selection : OperatorMethodSelected (Program.ofChecked program) context evidence
      traitName methodName requirements body dictionary)
    (certificate : ∃ inputTypes lexical facts,
      BodyInstanceTypingCertificate (Program.ofChecked program) body inputTypes lexical facts) :
    TypedOperatorMethodSelected (Program.ofChecked program) context evidence
      traitName methodName requirements body dictionary := by
  obtain ⟨inputTypes, lexical, facts, certificate⟩ := certificate
  cases selection with
  | intro selects closed implementation trait traitName goal head method methodName owner
      requirements instantiates assembled covers =>
    exact .intro selects closed implementation trait traitName goal head method methodName owner
      requirements instantiates assembled covers ⟨inputTypes, lexical, facts, of_body checked instantiates certificate⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodCertificateTransport
