import Solcore.Test.RustHullRootCallCorrespondence
import Solcore.Frontend.RustHull.ContractRootCallExecutionCorrespondence

/-! The actual accepted root compilation establishes its code identity and
captured closure. No catalog entry or assumed Core execution is required. -/
set_option autoImplicit false
namespace Tests.RustHullRootCallCorrespondence
open Solcore Solcore.Frontend.RustHull Correspondence DerivationCorrespondence
private abbrev number := Core.Word.ofNatModulo

def anchors : List CatalogWorldCorrespondence.Anchor := [⟨number 100, rootBytes, 1⟩]

theorem catalog_connection (scenario : Scenario) :
    RootChildCatalogExecutionCorrespondence.CatalogConnection
      (sourceCode scenario) (catalog scenario) [] anchors := by
  intro target source selected
  by_cases root : number 100 == target
  · have addressEq : number 100 = target := by simpa only [beq_iff_eq] using root
    subst target
    have sourceEq : sourceCode scenario = source := by
      simpa [ChildFrameSemantics.select, ChildFrameModeSemantics.select, catalog] using selected
    subst source
    exact .inl ⟨rfl, by simp [anchors, sourceCode]⟩
  · simp [ChildFrameSemantics.select, catalog, root] at selected

theorem initial_context_links (object : Contract.CompiledObject) :
    ContractRootCallCorrespondence.InitialContextLinks (some rootBytes) [] object context anchors := by
  intro anchor member
  simp only [anchors, List.mem_cons, List.not_mem_nil, or_false] at member
  subst anchor
  exact .inl ⟨rfl, rfl, rfl, rfl⟩

theorem public_evaluates (scenario : Scenario) {object : Contract.CompiledObject}
    (accepted : Contract.compileObject (program scenario) ["Root"] 64 (some rootBytes) [] = .ok object) :
    ∃ value final, Core.Evaluates [] [] (object.instantiate context).expression value final ∧
      ContractRootCallCorrespondence.PublicMessageRel context result (finalState object scenario).external value := by
  have image : object.codeImages.head?.getD none = some rootBytes := by
    rw [CatalogWorldCorrespondence.compileObject_images accepted]
    rfl
  exact ContractRootCallCorrespondence.compileObject_preserves (height := 0) (code := code scenario) rfl accepted
    (eligible scenario names_supported) (catalog_connection scenario) (InitCatalogCorrespondence.InitCatalogConnection.empty rfl (by decide)) context rfl
    (initial_context_links object) (source object scenario image)

theorem public_resumes (scenario : Scenario) {object : Contract.CompiledObject}
    (accepted : Contract.compileObject (program scenario) ["Root"] 64 (some rootBytes) [] = .ok object) :
    ∃ value, ContractRootCallCorrespondence.PublicMessageRel context result (finalState object scenario).external value ∧
      ∃ required, ∀ initialFuel additional limit last,
        Contract.ReceiptResumes limit (Contract.runWithReceipt (object.instantiate context) initialFuel limit) additional last →
        (last = Contract.finish limit value ↔ required ≤ initialFuel + additional) ∧
        ((∃ checkpoint, last.outcome = .outOfFuel checkpoint) ↔ initialFuel + additional < required) := by
  have image : object.codeImages.head?.getD none = some rootBytes := by
    rw [CatalogWorldCorrespondence.compileObject_images accepted]
    rfl
  exact ContractRootCallCorrespondence.compileObject_resumes_exact (height := 0) (code := code scenario) rfl accepted
    (eligible scenario names_supported) (catalog_connection scenario) (InitCatalogCorrespondence.InitCatalogConnection.empty rfl (by decide)) context rfl
    (initial_context_links object) (source object scenario image)

end Tests.RustHullRootCallCorrespondence
