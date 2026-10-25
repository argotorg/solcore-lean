import Solcore.Test.RustHullNestedChildCatalogCorrespondence

/-! Independent two-level call derivations reach actual compilation, public
receipts and exact resumption thresholds. Catalog identities and initial code
links are discharged by the concrete source/context fixtures. -/
set_option autoImplicit false
namespace Tests.RustHullNestedChildCallCorrespondence
open Solcore Solcore.Frontend.RustHull

theorem public_evaluates (scenario : Scenario) {object : Contract.CompiledObject}
    (accepted : Contract.compileObject (program scenario) ["Parent"] 64 none (compiledCatalog scenario) = .ok object) :
    ∃ value final, Core.Evaluates [] [] (object.instantiate context).expression value final ∧
      ContractNestedChildCallCorrespondence.PublicMessageRel context result (finalState object scenario).external value := by
  exact ContractNestedChildCallCorrespondence.compileObject_preserves (height := 1) (code := code scenario .parent) (by rfl) accepted rfl
    (eligible scenario .parent names_supported) (catalog_connection scenario) context rfl
    (initial_context_links scenario object) (source object scenario)

theorem public_resumes (scenario : Scenario) {object : Contract.CompiledObject}
    (accepted : Contract.compileObject (program scenario) ["Parent"] 64 none (compiledCatalog scenario) = .ok object) :
    ∃ value, ContractNestedChildCallCorrespondence.PublicMessageRel context result (finalState object scenario).external value ∧
      ∃ required, ∀ initialFuel additional limit last,
        Contract.ReceiptResumes limit (Contract.runWithReceipt (object.instantiate context) initialFuel limit) additional last →
        (last = Contract.finish limit value ↔ required ≤ initialFuel + additional) ∧
        ((∃ checkpoint, last.outcome = .outOfFuel checkpoint) ↔ initialFuel + additional < required) := by
  exact ContractNestedChildCallCorrespondence.compileObject_resumes_exact (height := 1) (code := code scenario .parent) (by rfl) accepted rfl
    (eligible scenario .parent names_supported) (catalog_connection scenario) context rfl
    (initial_context_links scenario object) (source object scenario)

end Tests.RustHullNestedChildCallCorrespondence
