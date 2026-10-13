import Solcore.Test.SourceCoreCertifiedLexicalFailureCertificate
import Solcore.Test.SourceCoreInitialLexicalFailureSelection

set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCertifiedLexicalFailure
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreInitialLexicalFailure
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)

variable {fixture : CompiledFixture} {signature : ProgramFunctionSignature}

theorem eligible_row (row : ObservedRow fixture signature) :
    ∃ selected : CertifiedPublicSession.EligibleRow fixture.recipe.compiled row.row.key,
      selected.named.specialized = row.row := by
  obtain ⟨prepared⟩ := fixture.prepared row.member
  obtain ⟨signatureEq, indexEq⟩ := row.prepared_slot prepared
  have eligible : CallableIndexedOwnedPreparedOrdinaryCatalogReceipts.Eligible fixture.recipe.compiled
      prepared.named.specialized := by
    rw [prepared.same]
    refine ⟨prepared.origin, ?_, row.ordinary, row.inputsOrdinary⟩
    simp only [row.parameters, ParameterSubstitution.RangeWellFormed, List.not_mem_nil,
      false_implies, implies_true]
  exact ⟨⟨prepared.named, prepared.index, row.global, prepared.selected,
    by rw [indexEq]; exact row.slot, row.globalKey, eligible⟩, prepared.same⟩

theorem header_of_member (row : ObservedRow fixture signature)
    {inputs : List (Input fixture.recipe.compiled)} (rows : Inventory inputs)
    {header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    (member : header ∈ headers rows) (source : header.named.specialized = row.row) :
    ∃ actual : ActualHeader fixture row.row, actual.header = header := by
  obtain ⟨input, packet, _retained, sameHeader⟩ := rows.mem_headers header member
  subst header
  have sameRow : input.row = row.row := input.prepared.same.symm.trans
    ((congrArg (·.specialized) packet.aligned.named.symm).trans source)
  have parameters : input.row.parameterSubstitution = [] := sameRow ▸ row.parameters
  have metadata : CallableNamedCanonicalOrder.retainedInstantiation input.row =
      CallableNamedMetadata.instantiation input.row := by
    simp [CallableNamedCanonicalOrder.retainedInstantiation, CallableNamedMetadata.instantiation, parameters]
  let actual : ActualHeader fixture input.row := {
    prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued input.prepared packet.selected
    header := packet.header
    aligned := by simpa only [metadata] using packet.aligned
    diagnostic := ⟨⟨packet.selected.diagnostics, packet.selected.found, rfl⟩⟩ }
  have transported : ∀ (left right : SourceSpecialization.SpecializedFunction)
      (same : left = right) (value : ActualHeader fixture left),
      (same ▸ value : ActualHeader fixture right).header = value.header := by
    intro left right same value
    cases same
    rfl
  exact ⟨sameRow ▸ actual, transported _ _ sameRow actual⟩

theorem header_types
    (header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram)) :
    header.types = header.bindings.map (fun binding => binding.1.scheme.body) := by
  have same := Dynamic.MonoBindersExtend.bodyTypes_eq header.extended
  rw [header.parameters] at same
  simpa only [List.map_map, Function.comp_def] using same.symm

end Tests.SourceCoreCertifiedLexicalFailure
