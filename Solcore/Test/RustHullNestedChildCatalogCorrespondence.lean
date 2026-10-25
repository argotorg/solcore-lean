import Solcore.Test.RustHullNestedChildCallCorrespondence
import Solcore.Frontend.RustHull.ContractNestedChildCallExecutionCorrespondence

/-! The two concrete child accounts select their actual catalog entries and
obtain exact executable identities from public context initialization. -/
set_option autoImplicit false
namespace Tests.RustHullNestedChildCallCorrespondence
open Solcore Solcore.Frontend.RustHull Correspondence DerivationCorrespondence
private abbrev number := Core.Word.ofNatModulo

def anchors : List CatalogWorldCorrespondence.Anchor :=
  [⟨number 100, (image .child).getD [], 2⟩, ⟨number 200, (image .grandchild).getD [], 3⟩]

theorem catalog_connection_of_eligible (scenario : Scenario)
    (childEligible : ExecutableProgram (ContractChildCallCorrespondence.supported true) (functions scenario .child))
    (grandchildEligible : ExecutableProgram (ContractChildCallCorrespondence.supported true) (functions scenario .grandchild)) :
    NestedChildCatalogExecutionCorrespondence.CatalogConnection (catalog scenario) (compiledCatalog scenario) anchors := by
  intro target source selected
  by_cases child : number 100 == target
  · have addressEq : number 100 = target := by simpa only [beq_iff_eq] using child
    subst target
    have sourceEq : sourceCode scenario .child = source := by
      simpa [ChildFrameSemantics.select, catalog] using selected
    subst source
    refine ⟨0, {program := program scenario, path := ["Child"], bytes := (image .child).getD []},
      rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
    · simp [anchors, sourceCode]
    · decide +kernel
    · change (List.range 3).find? (fun candidate => number 2 == number (candidate + 1)) = some 1
      decide +kernel
    · exact childEligible
  · by_cases grandchild : number 200 == target
    · have addressEq : number 200 = target := by simpa only [beq_iff_eq] using grandchild
      subst target
      have sourceEq : sourceCode scenario .grandchild = source := by
        simpa [ChildFrameSemantics.select, catalog, child] using selected
      subst source
      refine ⟨1, {program := program scenario, path := ["Grandchild"], bytes := (image .grandchild).getD []},
        rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
      · simp [anchors, sourceCode]
      · decide +kernel
      · change (List.range 3).find? (fun candidate => number 3 == number (candidate + 1)) = some 2
        decide +kernel
      · exact grandchildEligible
    · simp [ChildFrameSemantics.select, catalog, child, grandchild] at selected

theorem catalog_connection (scenario : Scenario) :
    NestedChildCatalogExecutionCorrespondence.CatalogConnection (catalog scenario) (compiledCatalog scenario) anchors :=
  catalog_connection_of_eligible scenario (eligible scenario .child names_supported)
    (eligible scenario .grandchild names_supported)

theorem initial_context_links (scenario : Scenario) (object : Contract.CompiledObject) :
    ContractNestedChildCallCorrespondence.InitialContextLinks none (compiledCatalog scenario) object context anchors := by
  intro anchor member
  simp only [anchors, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · refine ⟨childAccount, rfl, rfl, ?_, rfl⟩
    decide +kernel
  · refine ⟨grandchildAccount, rfl, rfl, ?_, rfl⟩
    decide +kernel

end Tests.RustHullNestedChildCallCorrespondence
