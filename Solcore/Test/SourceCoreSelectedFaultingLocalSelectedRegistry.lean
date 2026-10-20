import Solcore.Test.SourceCoreSelectedFaultingLocalWellFormed
import Solcore.Test.SourceCoreSelectedFaultingLocalInventory
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCheckedNamedSupport
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedFaultingLocal
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
theorem OriginalTyping.selected_bodies {fixture : CompiledFixture} (original : OriginalTyping fixture) :
    SelectedCompilationBodyTyping.Bodies fixture.recipe.compiled := by
  let catalog := SignatureCatalogWellFormed.ofCheckProgram fixture.checked
  obtain ⟨functionIds,methodIds⟩ := Frontend.checkProgram_success_ids fixture.checked
  refine ⟨catalog, ?_, ?_, ?_, ?_⟩
  · simp only [Program.ofChecked,List.map_map,Function.comp_def,FunctionDefinition.ofChecked,BodyDefinition.ofChecked]
    rw [functionIds]
    exact catalog.function_ids
  · simp only [Program.ofChecked,List.map_map,Function.comp_def,MethodDefinition.ofChecked]
    rw [methodIds]
    exact catalog.implementation_method_ids
  · intro function selected
    obtain ⟨_,_,_,_,_,_,member,_⟩ := selected
    apply functionDefinitionValid_ofCheckProgram fixture.checked member
    intro signature signatureMember accepted
    rw [original.functions] at member
    have same := List.mem_singleton.mp member
    subst function
    let typed := original
    have same : signature = typed.signature := by
      apply eq_of_mem_of_nodup_map catalog.function_ids signatureMember typed.member
      exact (checkFunctionBody_success_declaration accepted).symm.trans typed.owner
    subst signature
    apply checkedBodyHasType_ofStatements accepted
    exact typed.body.statements_typed
  · intro method selected
    obtain ⟨_,_,_,_,_,_,member,_,_⟩ := selected
    rw [original.methods] at member
    cases member

theorem SelectedInventory.ranges {fixture : ProfiledFixture} {row : Row fixture.original}
    (selected : SelectedInventory fixture row) :
    SelectedCompilationRegistryMethodCertificates.Ranges fixture.original.recipe.compiled := by
  intro index named cached
  have member := List.mem_of_getElem? cached
  rw [selected.complete] at member
  have same : named = selected.input.prepared.named := List.mem_singleton.mp member
  rw [same, selected.input.prepared.same, selected.original, row.substitution]
  intro name value found
  cases found

theorem OriginalTyping.checked_registry {fixture : ProfiledFixture} {row : Row fixture.original}
    (original : OriginalTyping fixture.original) (selected : SelectedInventory fixture row) :
    SelectedCompilationCheckedRegistry.Certificate fixture.original.recipe.compiled :=
  SelectedCompilationCheckedRegistry.of_checked fixture.original.checked original.selected_bodies selected.ranges

end Tests.SourceCoreSelectedFaultingLocal
