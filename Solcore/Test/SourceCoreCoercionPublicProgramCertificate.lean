import Solcore.Test.SourceCoreCoercionPublicCommon
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedProgramAdmission

/-! The original coercion program is admitted once from its complete actual
cache. A finite row check selects the existing three-header order; it does not
construct syntax, metadata, closure support or method body support. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCoercionPublic
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

structure ObservedProgramCertificate (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  certificate : CallableIndexedOwnedPreparedProgramAdmission.Certificate fixture.recipe.compiled
  accepted : CallableIndexedOwnedPreparedProgramAdmission.certify fixture.recipe.compiled
    fixture.source_wellFormed 64 = some certificate
  rows : ∀ row ∈ certificate.table.rows,
    row = observed.makeRow.row ∨ row = observed.useRow.row ∨ row = observed.keepRow.row

def observeProgramCertificate (fixture : CompiledFixture) (observed : ObservedProgram fixture) :
    IO (ObservedProgramCertificate fixture observed) := do
  match accepted : CallableIndexedOwnedPreparedProgramAdmission.certify fixture.recipe.compiled
      fixture.source_wellFormed 64 with
  | none => throw (IO.userError "original coercion program certification rejected")
  | some certificate =>
      if rows : certificate.table.rows.all (fun row =>
          (row == observed.makeRow.row) || ((row == observed.useRow.row) || (row == observed.keepRow.row))) = true then
        pure ⟨certificate, accepted, by
          intro row member
          have same := List.all_eq_true.mp rows row member
          simp only [Bool.or_eq_true] at same
          rcases same with same | same | same
          · exact .inl (eq_of_beq same)
          · exact .inr (.inl (eq_of_beq same))
          · exact .inr (.inr (eq_of_beq same))⟩
      else throw (IO.userError "actual direct table contains an unselected ordinary row")

theorem ObservedProgramCertificate.aligned {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (admission : ObservedProgramCertificate fixture observed) (inventory : OrdinaryInventory fixture observed) :
    CallableIndexedOwnedPreparedNamedSyntaxAdmission.TableAligned
      [inventory.makeInput, inventory.useInput, inventory.keepInput] admission.certificate.table.rows := by
  intro row member
  rcases admission.rows row member with rfl | rfl | rfl
  · exact ⟨inventory.makeInput, by simp, inventory.makeSame⟩
  · exact ⟨inventory.useInput, by simp, inventory.useSame⟩
  · exact ⟨inventory.keepInput, by simp, inventory.keepSame⟩

/-- The primary production entry point constructs its own complete eligible
ordinary catalog and closes table alignment without the selected subset. -/
theorem ObservedProgramCertificate.automatic_catalog {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (admission : ObservedProgramCertificate fixture observed) (receiver : ObservedReceiver fixture observed) :
    ∃ catalog : CallableIndexedOwnedPreparedOrdinaryCatalogReceipts.Catalog fixture.recipe.compiled,
      Nonempty (CallableIndexedOwnedPreparedPhysicalProgramSupport.Support fixture.recipe.compiled
        (headers catalog.rows) (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
        receiver.completion) := by
  exact admission.certificate.issue fixture.source_wellFormed fixture.recipePrepared receiver.issued
    receiver.registry observed.makeRow.entryMember (by rw [fixture.sameProgram]; exact fixture.checked)

/-- This proof is exercised by the same runtime-produced certificate used by
the seven-call regression; catalog construction is kept inside the proof. -/
theorem ObservedProgramCertificate.automatic_catalog_initial {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (admission : ObservedProgramCertificate fixture observed) :
    ∃ receiver : ObservedReceiver fixture observed,
      ∃ catalog : CallableIndexedOwnedPreparedOrdinaryCatalogReceipts.Catalog fixture.recipe.compiled,
        Nonempty (CallableIndexedOwnedPreparedPhysicalProgramSupport.Support fixture.recipe.compiled
          (headers catalog.rows) (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
          receiver.completion) := by
  obtain ⟨receiver⟩ := initial_receiver fixture observed
  exact ⟨receiver, admission.automatic_catalog receiver⟩

end Tests.SourceCoreCoercionPublic
