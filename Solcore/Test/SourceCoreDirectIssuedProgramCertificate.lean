import Solcore.Test.SourceCoreDirectIssuedInventory
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedProgramAdmission

/-! The original direct issued program is admitted once from its complete actual
cache. A finite row check selects the existing two-header order; it does not
construct syntax, metadata, closure support or method body support. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreDirectIssued
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreCapturedReuse
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

structure ObservedProgramCertificate (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  certificate : CallableIndexedOwnedPreparedProgramAdmission.Certificate fixture.recipe.compiled
  accepted : CallableIndexedOwnedPreparedProgramAdmission.certify fixture.recipe.compiled
    fixture.source_wellFormed 64 = some certificate
  rows : ∀ row ∈ certificate.table.rows, row ∈ [observed.makeRow.row, observed.readRow.row]

def observeProgramCertificate (fixture : CompiledFixture) (observed : ObservedProgram fixture) :
    IO (ObservedProgramCertificate fixture observed) := do
  match accepted : CallableIndexedOwnedPreparedProgramAdmission.certify fixture.recipe.compiled
      fixture.source_wellFormed 64 with
  | none => throw (IO.userError "original direct issued program certification rejected")
  | some certificate =>
      if rows : certificate.table.rows.all (fun row =>
          [observed.makeRow.row, observed.readRow.row].any (fun expected => row == expected)) = true then
        pure ⟨certificate, accepted, by
          intro row member
          obtain ⟨expected, present, same⟩ := List.any_eq_true.mp (List.all_eq_true.mp rows row member)
          exact (eq_of_beq same).symm ▸ present⟩
      else throw (IO.userError "actual direct table contains an unselected ordinary row")

theorem ObservedProgramCertificate.aligned {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (admission : ObservedProgramCertificate fixture observed) (inventory : OrdinaryInventory fixture observed) :
    CallableIndexedOwnedPreparedNamedSyntaxAdmission.TableAligned
      [inventory.makeInput, inventory.readInput] admission.certificate.table.rows := by
  intro row member
  have present := admission.rows row member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl
  · exact ⟨inventory.makeInput, by simp, inventory.makeRow⟩
  · exact ⟨inventory.readInput, by simp, inventory.readRow⟩

/-- The primary production entry point constructs its own complete eligible
ordinary catalog and closes table alignment without the selected subset. -/
theorem ObservedProgramCertificate.automatic_catalog {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (admission : ObservedProgramCertificate fixture observed) (receiver : ObservedReceiver fixture observed) :
    ∃ catalog : CallableIndexedOwnedPreparedOrdinaryCatalogReceipts.Catalog fixture.recipe.compiled,
      Nonempty (CallableIndexedOwnedPreparedPhysicalProgramSupport.Support fixture.recipe.compiled
        (headers catalog.rows) (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
        receiver.completion) := by
  exact admission.certificate.issue_without_methods fixture.source_wellFormed fixture.recipePrepared receiver.issued
    receiver.registry observed.makeRow.entryMember (by rw [fixture.sameProgram]; exact fixture.checked)
    (by rw [fixture.sameProgram]; exact fixture.methods)

/-- This proof is exercised by the same runtime-produced certificate used by
the five-operation regression; catalog construction is kept inside the proof. -/
theorem ObservedProgramCertificate.automatic_catalog_initial {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (admission : ObservedProgramCertificate fixture observed) :
    ∃ receiver : ObservedReceiver fixture observed,
      ∃ catalog : CallableIndexedOwnedPreparedOrdinaryCatalogReceipts.Catalog fixture.recipe.compiled,
        Nonempty (CallableIndexedOwnedPreparedPhysicalProgramSupport.Support fixture.recipe.compiled
          (headers catalog.rows) (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
          receiver.completion) := by
  obtain ⟨receiver⟩ := initial_receiver fixture observed
  exact ⟨receiver, admission.automatic_catalog receiver⟩

end Tests.SourceCoreDirectIssued
