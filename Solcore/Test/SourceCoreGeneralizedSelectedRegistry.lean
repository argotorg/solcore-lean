import Solcore.Test.SourceCoreGeneralizedExportObserved
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCheckedRegistry

/-! The original declarative rows authenticate only the selected cache origins.
Actual cached replacement observations supply the unchanged registry ranges. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreGeneralizedExport
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
    obtain ⟨typed⟩ := original.functions.at member
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

theorem ObservedCache.ranges {fixture : CompiledFixture}
    (cache : ObservedCache fixture fixture.recipe.compiled.indexed.base.functions) :
    SelectedCompilationRegistryMethodCertificates.Ranges fixture.recipe.compiled := by
  intro index named selected
  obtain ⟨observation⟩ := cache.at_slot selected
  rw [observation.substitution]
  intro name value found
  cases found

theorem OriginalTyping.checked_registry {fixture : CompiledFixture} (original : OriginalTyping fixture)
    (cache : ObservedCache fixture fixture.recipe.compiled.indexed.base.functions) :
    SelectedCompilationCheckedRegistry.Certificate fixture.recipe.compiled :=
  SelectedCompilationCheckedRegistry.of_checked fixture.checked original.selected_bodies cache.ranges

end Tests.SourceCoreGeneralizedExport
