import Solcore.Test.SourceCoreMethodOriginEvidenceSelection
import Solcore.SourceSemantics.CoreLowering.CertifiedPublicSessionRows

/-! Original observed rows identify the actual packets in an automatic catalog.
No Header order or separately assembled inventory is used. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMethodOriginEvidence.Certified
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Issued Inventory headers)
open CallableIndexedOwnedPreparedOrdinaryCatalogReceipts (Eligible)

variable {fixture : CompiledFixture} {signature : ProgramFunctionSignature}

theorem row_eligible (row : ObservedRow fixture signature) :
    Eligible fixture.recipe.compiled row.named.specialized := by
  rw [row.same]
  refine ⟨row.origin, ?_, row.ordinary, row.inputsOrdinary⟩
  intro parameter replacement member
  have scalar := of_decide_eq_true (List.all_eq_true.mp row.scalarRange (parameter, replacement) member)
  rcases scalar with rfl | rfl
  · exact ⟨by simp [TypeParameterBindersWellFormed, Context.ofSignatures], .builtin .word⟩
  · exact ⟨by simp [TypeParameterBindersWellFormed, Context.ofSignatures], .builtin .bool⟩

def selected_row (row : ObservedRow fixture signature) :
    CertifiedPublicSession.EligibleRow fixture.recipe.compiled row.row.key :=
  ⟨row.named, row.index, row.global, row.cached, row.slot, row.globalKey, row_eligible row⟩

/-- The chosen Header is literally the issued packet in this catalog. Full
named equality fixes its original specialized Source and dictionary. -/
theorem header_of_member
    (row : ObservedRow fixture signature)
    {inputs : List (Input fixture.recipe.compiled)} (rows : Inventory inputs)
    {header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    (member : header ∈ headers rows)
    (named : header.named = row.named) :
    ∃ actual : ActualHeader fixture row.row, actual.header = header := by
  obtain ⟨input, packet, _retained, sameHeader⟩ := rows.mem_headers header member
  subst header
  have sameRow : input.row = row.row :=
    input.prepared.same.symm.trans
      ((congrArg (·.specialized) (packet.aligned.named.symm.trans named)).trans row.same)
  let actual : ActualHeader fixture input.row := {
    prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued input.prepared packet.selected
    header := packet.header
    aligned := packet.aligned
    diagnostic := ⟨⟨packet.selected.diagnostics, packet.selected.found, rfl⟩⟩ }
  have transported : ∀ (left right : SourceSpecialization.SpecializedFunction)
      (same : left = right) (value : ActualHeader fixture left),
      (same ▸ value : ActualHeader fixture right).header = value.header := by
    intro left right same value
    cases same
    rfl
  exact ⟨sameRow ▸ actual, transported _ _ sameRow actual⟩

end Tests.SourceCoreMethodOriginEvidence.Certified
