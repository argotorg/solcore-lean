import Solcore.SourceSemantics.SourceCompiledGeneralizedBodyAssembly

/-! The actual selected ordinary function receives semantic validity from its
original checker receipt and the generalized recursive body proof. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization

/-- Complete validity for the original ordinary definition selected by this
compiler row. The barrier producer is tied to the same selected body. -/
theorem function_valid_of_barriers_of_interfaces
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : Selected compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (interfaces : ExecutableCoercionInterfaces.SourceInterfaces
      (checkingContext selected).signatures selected.body.finalized.solvedRequirements
      selected.body.finalized.typedSource)
    (barriers : SelectedInitializerBarriers selected) :
    FunctionDefinition.Valid compiled.program.signatures
      (FunctionDefinition.ofChecked selected.original) := by
  apply functionDefinitionValid_ofCheckProgram checked selected.originalMember
  intro signature signatureMember bodySuccess
  have same : signature = selected.signature :=
    eq_of_mem_of_nodup_map (SignatureCatalogWellFormed.ofCheckProgram checked).function_ids
      signatureMember selected.signatureMember
      ((checkFunctionBody_success_declaration bodySuccess).symm.trans
        (checkFunctionBody_success_declaration selected.body.accepted))
  subst signature
  exact checked_body_of_barriers_of_interfaces selected checked interfaces barriers

theorem function_valid_of_barriers {raw : Workspace.RawWorkspace}
    {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : Selected compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (member : row ∈ compiled.plan.specializations)
    (barriers : SelectedInitializerBarriers selected) :
    FunctionDefinition.Valid compiled.program.signatures
      (FunctionDefinition.ofChecked selected.original) :=
  function_valid_of_barriers_of_interfaces selected checked
    (selected_original_interfaces selected member) barriers

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
