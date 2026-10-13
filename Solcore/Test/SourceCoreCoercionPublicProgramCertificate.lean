import Solcore.Test.SourceCoreCoercionPublicKeepCompilerSupport
import Solcore.SourceSemantics.CoreLowering.AcceptedProgramBodyCompletion

/-! The actual keep cache row receives its body from the accepted compiler
receipt. The complementary checker validates every other root and all closures
and methods, then the same full certificate feeds both public issuers. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCoercionPublic
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

structure ObservedProgramCertificate (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  pending : AcceptedProgramBodyCompletion.Pending fixture.recipe.compiled observed.keepRow.index
  accepted : AcceptedProgramBodyCompletion.certify fixture.recipe.compiled
    fixture.source_wellFormed observed.keepRow.index 64 = some pending
  metadata : CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
    fixture.recipe.compiled.indexed observed.keepRow.named observed.keepRow.row.function.typedBody
    (CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite pending.table.rows)
  metadataAccepted : CallableIndexedOwnedPreparedNamedSyntaxAdmission.metadata?
    fixture.recipe.compiled.indexed observed.keepRow.named observed.keepRow.row.function.typedBody
    (CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite pending.table.rows) = some ⟨metadata⟩
  rows : ∀ row ∈ pending.table.rows,
    row = observed.makeRow.row ∨ row = observed.useRow.row ∨ row = observed.keepRow.row

/-- The only pending root is filled from the authentic Header compiler action;
all remaining fields are retained from the executed finite checker. -/
def ObservedProgramCertificate.certificate {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (admission : ObservedProgramCertificate fixture observed) :
    CallableIndexedOwnedPreparedProgramAdmission.Certificate fixture.recipe.compiled :=
  admission.pending.complete (.scoped (by
    have same : admission.pending.chosen = observed.keepRow.named :=
      Option.some.inj (admission.pending.selected.symm.trans observed.keepRow.cached)
    rw [same]
    exact observed.keep_source_admission admission.metadata))

def observeProgramCertificate (fixture : CompiledFixture) (observed : ObservedProgram fixture) :
    IO (ObservedProgramCertificate fixture observed) := do
  match accepted : AcceptedProgramBodyCompletion.certify fixture.recipe.compiled
      fixture.source_wellFormed observed.keepRow.index 64 with
  | none => throw (IO.userError "original coercion complementary certification rejected")
  | some pending =>
      match metadataAccepted : CallableIndexedOwnedPreparedNamedSyntaxAdmission.metadata?
          fixture.recipe.compiled.indexed observed.keepRow.named observed.keepRow.row.function.typedBody
          (CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite pending.table.rows) with
      | none => throw (IO.userError "original keep expression metadata rejected")
      | some metadata =>
          if rows : pending.table.rows.all (fun row =>
              (row == observed.makeRow.row) || ((row == observed.useRow.row) || (row == observed.keepRow.row))) = true then
            pure ⟨pending, accepted, metadata.down, metadataAccepted, by
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
