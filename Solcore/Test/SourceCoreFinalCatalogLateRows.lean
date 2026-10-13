import Solcore.Test.SourceCoreMethodOriginEvidenceFixture
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryCatalog

/-! The final ordinary catalog also recovers the two identity rows discovered
while preparing genuine implementation methods. This reuses the existing
nested-evidence fixture and does not add another execution model. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreFinalCatalogLateRows
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Issued Inventory)
open Tests.SourceCoreMethodOriginEvidence

private theorem eligible {fixture signature} (row : ObservedRow fixture signature) :
    CallableIndexedOwnedPreparedOrdinaryCatalogReceipts.Eligible fixture.recipe.compiled row.named.specialized := by
  rw [row.same]
  refine ⟨row.origin, ?_, row.ordinary, row.inputsOrdinary⟩
  intro parameter replacement member
  have scalar := of_decide_eq_true (List.all_eq_true.mp row.scalarRange (parameter, replacement) member)
  rcases scalar with rfl | rfl
  · exact ⟨by simp [TypeParameterBindersWellFormed, Context.ofSignatures], .builtin .word⟩
  · exact ⟨by simp [TypeParameterBindersWellFormed, Context.ofSignatures], .builtin .bool⟩

theorem identity_packets (fixture : CompiledFixture) (observed : ObservedProgram fixture) :
    ∃ catalog : CallableIndexedOwnedPreparedOrdinaryCatalogReceipts.Catalog fixture.recipe.compiled,
      (∃ input : Input fixture.recipe.compiled, ∃ packet : Issued input,
        Inventory.HasRow packet catalog.rows ∧ input.row = observed.identityWordRow.row ∧
        input.prepared.index = observed.identityWordRow.index ∧
        input.prepared.named = observed.identityWordRow.named) ∧
      (∃ input : Input fixture.recipe.compiled, ∃ packet : Issued input,
        Inventory.HasRow packet catalog.rows ∧ input.row = observed.identityBoolRow.row ∧
        input.prepared.index = observed.identityBoolRow.index ∧
        input.prepared.named = observed.identityBoolRow.named) := by
  obtain ⟨catalog⟩ := CallableIndexedOwnedPreparedOrdinaryCatalog.of_compiled
    fixture.recipe.compiled fixture.source_wellFormed
  refine ⟨catalog, ?_, ?_⟩
  · obtain ⟨input, packet, retained, same, slot, named⟩ :=
      catalog.packet_at observed.identityWordRow.cached (eligible observed.identityWordRow)
    exact ⟨input, packet, retained, same.trans observed.identityWordRow.same, slot, named⟩
  · obtain ⟨input, packet, retained, same, slot, named⟩ :=
      catalog.packet_at observed.identityBoolRow.cached (eligible observed.identityBoolRow)
    exact ⟨input, packet, retained, same.trans observed.identityBoolRow.same, slot, named⟩

def runLateRows : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeProgram fixture
  have _packets := identity_packets fixture observed
  let early := fixture.recipe.compiled.validationPlan.specializations
  unless !(early.any (· == observed.identityWordRow.row)) &&
      !(early.any (· == observed.identityBoolRow.row)) do
    throw (IO.userError "identity rows were already in the validation plan")
  IO.println "FINAL_CATALOG_LATE_ROWS_PASS: both method-discovered identity rows are issued from the final cache"

end Tests.SourceCoreFinalCatalogLateRows
