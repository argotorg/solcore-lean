import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedFiniteNamedInventories

/-! A finite ordinary catalog retains every admitted actual cache position.
Admission uses original Source origin, complete replacement ranges and stage
markers. Physical cache positions are preserved when other rows are omitted. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryCatalogReceipts
open Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Issued Inventory headers)

structure Eligible (compiled : SourceCoreUnifiedCompilation.Compiled)
    (row : SourceSpecialization.SpecializedFunction) : Prop where
  origin : RecursiveNamedPublicSpecializationMeaning.Origin compiled.sourceProgram row
  range : SourceSemantics.ParameterSubstitution.RangeWellFormed
    (Context.ofSignatures compiled.sourceProgram.signatures) row.parameterSubstitution
  ordinaryReturn : row.function.returnComptime = false
  ordinaryParameters : ∀ binder, binder ∈ row.function.typedBody.inputs → binder.comptime = false

structure Catalog (compiled : SourceCoreUnifiedCompilation.Compiled) where
  inputs : List (Input compiled)
  rows : Inventory inputs
  distinct : (inputs.map (fun input => input.prepared.index)).Nodup
  admitted : ∀ input ∈ inputs, Eligible compiled input.row
  covered : ∀ index named, compiled.indexed.base.functions[index]? = some named →
    Eligible compiled named.specialized →
    ∃ input ∈ inputs, input.prepared.index = index ∧ input.prepared.named = named

theorem Catalog.packet_at {compiled : SourceCoreUnifiedCompilation.Compiled}
    (catalog : Catalog compiled) {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : compiled.indexed.base.functions[index]? = some named)
    (eligible : Eligible compiled named.specialized) :
    ∃ input : Input compiled, ∃ packet : Issued input,
      Inventory.HasRow packet catalog.rows ∧ input.row = named.specialized ∧
      input.prepared.index = index ∧ input.prepared.named = named := by
  obtain ⟨input, member, slot, same⟩ := catalog.covered index named selected eligible
  obtain ⟨packet, retained⟩ := catalog.rows.row_at input member
  exact ⟨input, packet, retained, input.prepared.same.symm.trans (congrArg (·.specialized) same), slot, same⟩

theorem Catalog.header_at {compiled : SourceCoreUnifiedCompilation.Compiled}
    (catalog : Catalog compiled) {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : compiled.indexed.base.functions[index]? = some named)
    (eligible : Eligible compiled named.specialized) :
    ∃ header ∈ headers catalog.rows, header.slot = index ∧ header.named = named := by
  obtain ⟨input, packet, retained, _row, slot, same⟩ := catalog.packet_at selected eligible
  exact ⟨packet.header, Inventory.header_member retained,
    packet.aligned.slot.trans slot, packet.aligned.named.trans same⟩

/-- This finite assembly lemma consumes static input receipts. The compiler
entry point constructs those receipts from actual cached preparation. -/
theorem collect (compiled : SourceCoreUnifiedCompilation.Compiled)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (receipt : ∀ index named, compiled.indexed.base.functions[index]? = some named →
      Eligible compiled named.specialized →
      ∃ input : Input compiled, input.row = named.specialized ∧
        input.prepared.index = index ∧ input.prepared.named = named) :
    Nonempty (Catalog compiled) := by
  classical
  let functions := compiled.indexed.base.functions
  let positions : List (Fin functions.length) := (List.finRange functions.length).filter
    (fun position => decide (Eligible compiled functions[position.val].specialized))
  have admittedPosition : ∀ position ∈ positions, Eligible compiled functions[position.val].specialized := by
    intro position member
    exact of_decide_eq_true (List.mem_filter.mp member).2
  have available : ∀ position : {position // position ∈ positions},
      ∃ input : Input compiled, input.row = functions[position.val.val].specialized ∧
        input.prepared.index = position.val.val ∧ input.prepared.named = functions[position.val.val] := by
    intro position
    exact receipt position.val.val functions[position.val.val]
      (List.getElem?_eq_getElem position.val.isLt) (admittedPosition position.val position.property)
  let choose := fun position => Classical.choose (available position)
  have chosen := fun position => Classical.choose_spec (available position)
  let inputs := positions.attach.map choose
  have indices : inputs.map (fun input => input.prepared.index) = positions.map Fin.val := by
    calc
      _ = positions.attach.map (fun position => position.val.val) := by
        simp only [inputs, List.map_map]
        exact List.map_congr_left (fun position _ => (chosen position).2.1)
      _ = positions.map Fin.val := List.attach_map_val
  obtain ⟨rows⟩ := CallableIndexedOwnedPreparedFiniteNamedInventories.inventory wellFormed inputs
  refine ⟨{ inputs := inputs, rows := rows, distinct := ?_, admitted := ?_, covered := ?_ }⟩
  · rw [indices]
    apply List.pairwise_map.mpr
    exact List.Pairwise.imp (fun different equal => different (Fin.ext equal))
      (List.Pairwise.filter _ (List.nodup_finRange functions.length))
  · intro input member
    obtain ⟨position, _member, rfl⟩ := List.mem_map.mp member
    rw [(chosen position).1]
    exact admittedPosition position.val position.property
  · intro index named selected eligible
    obtain ⟨bound, namedEq⟩ := List.getElem?_eq_some_iff.mp selected
    have namedAt : functions[index] = named := namedEq
    let position : Fin functions.length := ⟨index, bound⟩
    have present : position ∈ positions := by
      apply List.mem_filter.mpr
      exact ⟨List.mem_finRange position, by simpa only [position, namedAt, decide_eq_true_eq] using eligible⟩
    let attached : {position // position ∈ positions} := ⟨position, present⟩
    refine ⟨choose attached, List.mem_map.mpr ⟨attached, List.mem_attach _ _, rfl⟩,
      (chosen attached).2.1, ?_⟩
    exact (chosen attached).2.2.trans namedEq

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryCatalogReceipts
