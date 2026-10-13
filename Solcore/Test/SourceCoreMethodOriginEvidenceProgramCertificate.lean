import Solcore.Test.SourceCoreMethodOriginEvidenceCommon
import Solcore.Test.SourceCoreMethodOriginEvidenceRootCompilerSupport
import Solcore.SourceSemantics.CoreLowering.AcceptedProgramRootCompletion

/-! The original cache is checked with both actual entry roots pending.
Their accepted compiler actions complete the same shared program certificate. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMethodOriginEvidence
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

structure ObservedProgramCertificate (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  pending : AcceptedProgramRootCompletion.Pending fixture.recipe.compiled
    [observed.wordRow.index, observed.boolRow.index]
  accepted : AcceptedProgramRootCompletion.certify fixture.recipe.compiled
    fixture.source_wellFormed [observed.wordRow.index, observed.boolRow.index] 64 = some pending
  wordSite : CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite pending.table.rows observed.wordShape.call.instantiation
  wordAccepted : CallableIndexedOwnedPreparedNamedSyntaxAdmission.directSite?
    pending.table.rows observed.wordShape.call.instantiation = some ⟨wordSite⟩
  boolSite : CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite pending.table.rows observed.boolShape.call.instantiation
  boolAccepted : CallableIndexedOwnedPreparedNamedSyntaxAdmission.directSite?
    pending.table.rows observed.boolShape.call.instantiation = some ⟨boolSite⟩
  rows : ∀ row ∈ pending.table.rows, row ∈ [observed.wordRow.row, observed.boolRow.row, observed.makeWordRow.row, observed.makeBoolRow.row, observed.relayWordRow.row, observed.relayBoolRow.row, observed.useWordRow.row, observed.useBoolRow.row, observed.identityWordRow.row, observed.identityBoolRow.row]

def observeProgramCertificate (fixture : CompiledFixture) (observed : ObservedProgram fixture) :
    IO (ObservedProgramCertificate fixture observed) := do
  match accepted : AcceptedProgramRootCompletion.certify fixture.recipe.compiled
      fixture.source_wellFormed [observed.wordRow.index, observed.boolRow.index] 64 with
  | none => throw (IO.userError "original method-origin complementary certification rejected")
  | some pending =>
      match wordAccepted : CallableIndexedOwnedPreparedNamedSyntaxAdmission.directSite?
          pending.table.rows observed.wordShape.call.instantiation with
      | none => throw (IO.userError "original word direct target missing")
      | some ⟨wordSite⟩ =>
        match boolAccepted : CallableIndexedOwnedPreparedNamedSyntaxAdmission.directSite?
            pending.table.rows observed.boolShape.call.instantiation with
        | none => throw (IO.userError "original bool direct target missing")
        | some ⟨boolSite⟩ =>
          if rows : pending.table.rows.all (fun row =>
              [observed.wordRow.row, observed.boolRow.row, observed.makeWordRow.row, observed.makeBoolRow.row, observed.relayWordRow.row, observed.relayBoolRow.row, observed.useWordRow.row, observed.useBoolRow.row, observed.identityWordRow.row, observed.identityBoolRow.row].any (fun expected => row == expected)) = true then
            pure ⟨pending, accepted, wordSite, wordAccepted, boolSite, boolAccepted, by
              intro row member
              obtain ⟨expected, present, same⟩ := List.any_eq_true.mp (List.all_eq_true.mp rows row member)
              exact (eq_of_beq same).symm ▸ present⟩
          else throw (IO.userError "actual direct table contains an unselected ordinary row")

theorem ObservedProgramCertificate.aligned_pending {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (admission : ObservedProgramCertificate fixture observed) (inventory : OrdinaryInventory fixture observed) :
    CallableIndexedOwnedPreparedNamedSyntaxAdmission.TableAligned
      [inventory.wordInput, inventory.boolInput, inventory.makeWordInput, inventory.makeBoolInput, inventory.relayWordInput, inventory.relayBoolInput, inventory.useWordInput, inventory.useBoolInput, inventory.identityWordInput, inventory.identityBoolInput] admission.pending.table.rows := by
  intro row member
  have present := admission.rows row member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨inventory.wordInput, by simp, inventory.wordSame⟩
  · exact ⟨inventory.boolInput, by simp, inventory.boolSame⟩
  · exact ⟨inventory.makeWordInput, by simp, inventory.makeWordSame⟩
  · exact ⟨inventory.makeBoolInput, by simp, inventory.makeBoolSame⟩
  · exact ⟨inventory.relayWordInput, by simp, inventory.relayWordSame⟩
  · exact ⟨inventory.relayBoolInput, by simp, inventory.relayBoolSame⟩
  · exact ⟨inventory.useWordInput, by simp, inventory.useWordSame⟩
  · exact ⟨inventory.useBoolInput, by simp, inventory.useBoolSame⟩
  · exact ⟨inventory.identityWordInput, by simp, inventory.identityWordSame⟩
  · exact ⟨inventory.identityBoolInput, by simp, inventory.identityBoolSame⟩

/-- Each selected root is derived from its actual Header, then transported
back to that same cached function. Other pending certificate fields are unused. -/
theorem ObservedProgramCertificate.word_source_admission {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (admission : ObservedProgramCertificate fixture observed) :
    CallableIndexedOwnedPreparedNamedScopedAdmission.SourceAdmission fixture.recipe.compiled
      observed.wordRow.named observed.wordRow.named.specialized.function.typedBody
      (CallableIndexedOwnedPreparedNamedSourceAdmissionTransport.statements observed.wordRow.named.specialized.function.typedBody)
      observed.wordRow.named.specialized.function.inferredBodyType admission.pending.table.rows := by
  obtain ⟨inventory⟩ := ordinary_inventory fixture observed
  exact AcceptedNamedBodyAdmission.source_of_header inventory.wordHeader.prepared inventory.wordHeader.aligned
    observed.wordRow.cached observed.wordRow.same
    (inventory.wordHeader.root_compiler_admission observed.wordShape observed.wordNodes observed.noLocals
      admission.wordSite (fun _ site => site.supported (admission.aligned_pending inventory)))

theorem ObservedProgramCertificate.bool_source_admission {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (admission : ObservedProgramCertificate fixture observed) :
    CallableIndexedOwnedPreparedNamedScopedAdmission.SourceAdmission fixture.recipe.compiled
      observed.boolRow.named observed.boolRow.named.specialized.function.typedBody
      (CallableIndexedOwnedPreparedNamedSourceAdmissionTransport.statements observed.boolRow.named.specialized.function.typedBody)
      observed.boolRow.named.specialized.function.inferredBodyType admission.pending.table.rows := by
  obtain ⟨inventory⟩ := ordinary_inventory fixture observed
  exact AcceptedNamedBodyAdmission.source_of_header inventory.boolHeader.prepared inventory.boolHeader.aligned
    observed.boolRow.cached observed.boolRow.same
    (inventory.boolHeader.root_compiler_admission observed.boolShape observed.boolNodes observed.noLocals
      admission.boolSite (fun _ site => site.supported (admission.aligned_pending inventory)))

/-- Selection uses actual cache indices. The original complete Certificate is
constructed only after both accepted compiler roots fill their own positions. -/
def ObservedProgramCertificate.certificate {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (admission : ObservedProgramCertificate fixture observed) :
    CallableIndexedOwnedPreparedProgramAdmission.Certificate fixture.recipe.compiled :=
  admission.pending.complete fun position member named selected =>
    if word : position = observed.wordRow.index then .scoped (by
      have same : named = observed.wordRow.named :=
        Option.some.inj ((word ▸ selected).symm.trans observed.wordRow.cached)
      subst named
      exact admission.word_source_admission)
    else .scoped (by
      have bool : position = observed.boolRow.index := by
        simpa only [List.mem_cons, List.not_mem_nil, or_false, word, false_or] using member
      have same : named = observed.boolRow.named :=
        Option.some.inj ((bool ▸ selected).symm.trans observed.boolRow.cached)
      subst named
      exact admission.bool_source_admission)

theorem ObservedProgramCertificate.aligned {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (admission : ObservedProgramCertificate fixture observed) (inventory : OrdinaryInventory fixture observed) :
    CallableIndexedOwnedPreparedNamedSyntaxAdmission.TableAligned
      [inventory.wordInput, inventory.boolInput, inventory.makeWordInput, inventory.makeBoolInput, inventory.relayWordInput, inventory.relayBoolInput, inventory.useWordInput, inventory.useBoolInput, inventory.identityWordInput, inventory.identityBoolInput] admission.certificate.table.rows :=
  admission.aligned_pending inventory

/-- The primary production entry point constructs its own complete eligible
ordinary catalog and closes table alignment without the selected subset. -/
theorem ObservedProgramCertificate.automatic_catalog {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (admission : ObservedProgramCertificate fixture observed) (receiver : ObservedReceiver fixture observed) :
    ∃ catalog : CallableIndexedOwnedPreparedOrdinaryCatalogReceipts.Catalog fixture.recipe.compiled,
      Nonempty (CallableIndexedOwnedPreparedPhysicalProgramSupport.Support fixture.recipe.compiled
        (headers catalog.rows) (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
        receiver.completion) := by
  exact admission.certificate.issue fixture.source_wellFormed fixture.recipePrepared receiver.issued
    receiver.registry observed.wordRow.entryMember (by rw [fixture.sameProgram]; exact fixture.checked)

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

end Tests.SourceCoreMethodOriginEvidence
