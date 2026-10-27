import Solcore.Test.RustHullLifecycleCorrespondence
import Solcore.Frontend.RustHull.ContractCallModeExecutionCorrespondence

/-! A child account destruction reaches public execution and resumption,
including successful finalization and a revert by the parent frame. -/
set_option autoImplicit false
namespace Tests.RustHullLifecycleCorrespondence
open Solcore Solcore.Frontend.RustHull Correspondence DerivationCorrespondence
private abbrev number := Core.Word.ofNatModulo

def anchors : List CatalogWorldCorrespondence.Anchor := [⟨number 100, childBytes, 2⟩]

theorem catalog_connection_of_eligible (scenario : Scenario)
    (childEligible : ExecutableProgram (ContractCallModeCorrespondence.supported true) childFunctions) :
    ModeChildCatalogExecutionCorrespondence.CatalogConnection (catalog scenario) (compiledCatalog scenario) anchors := by
  intro target source selected
  by_cases child : number 100 == target
  · have addressEq : number 100 = target := by simpa only [beq_iff_eq] using child
    subst target
    have sourceEq : sourceCode scenario = source := by
      simpa [ChildFrameSemantics.select, ChildFrameModeSemantics.select, catalog] using selected
    subst source
    refine ⟨0, {program := program scenario, path := ["Child"], bytes := childBytes},
      rfl, rfl, rfl, rfl, ?_, ?_, ?_, childEligible⟩
    · simp [anchors, sourceCode]
    · decide +kernel
    · change (List.range 2).find? (fun candidate => number 2 == number (candidate + 1)) = some 1
      decide +kernel
  · simp [ChildFrameSemantics.select, catalog, child] at selected

theorem catalog_connection (scenario : Scenario) :
    ModeChildCatalogExecutionCorrespondence.CatalogConnection (catalog scenario) (compiledCatalog scenario) anchors :=
  catalog_connection_of_eligible scenario (child_eligible names_supported)

theorem initial_context_links (scenario : Scenario) (object : Contract.CompiledObject) :
    ContractCallModeCorrespondence.InitialContextLinks none (compiledCatalog scenario) object (context scenario) anchors := by
  intro anchor member
  simp only [anchors, List.mem_cons, List.not_mem_nil, or_false] at member
  subst anchor
  refine ⟨childAccount scenario, rfl, rfl, ?_, rfl⟩
  change number 100 ≠ number 0
  decide +kernel

theorem public_evaluates (scenario : Scenario) {object : Contract.CompiledObject}
    (accepted : Contract.compileObject (program scenario) ["Parent"] 64 none (compiledCatalog scenario) = .ok object) :
    ∃ value final, Core.Evaluates [] [] (object.instantiate (context scenario)).expression value final ∧
      ContractCallModeCorrespondence.PublicMessageRel (context scenario) result (finalState object scenario).external value := by
  exact ContractCallModeCorrespondence.compileObject_preserves (height := 0) (code := code scenario) (by rfl) accepted rfl
    (eligible scenario names_supported) (catalog_connection scenario) (InitCatalogCorrespondence.InitCatalogConnection.empty rfl (by cases scenario <;> decide)) (context scenario) rfl
    (initial_context_links scenario object) (source object scenario)

theorem public_resumes (scenario : Scenario) {object : Contract.CompiledObject}
    (accepted : Contract.compileObject (program scenario) ["Parent"] 64 none (compiledCatalog scenario) = .ok object) :
    ∃ value, ContractCallModeCorrespondence.PublicMessageRel (context scenario) result (finalState object scenario).external value ∧
      ∃ required, ∀ initialFuel additional limit last,
        Contract.ReceiptResumes limit (Contract.runWithReceipt (object.instantiate (context scenario)) initialFuel limit) additional last →
        (last = Contract.finish limit value ↔ required ≤ initialFuel + additional) ∧
        ((∃ checkpoint, last.outcome = .outOfFuel checkpoint) ↔ initialFuel + additional < required) := by
  exact ContractCallModeCorrespondence.compileObject_resumes_exact (height := 0) (code := code scenario) (by rfl) accepted rfl
    (eligible scenario names_supported) (catalog_connection scenario) (InitCatalogCorrespondence.InitCatalogConnection.empty rfl (by cases scenario <;> decide)) (context scenario) rfl
    (initial_context_links scenario object) (source object scenario)

end Tests.RustHullLifecycleCorrespondence
