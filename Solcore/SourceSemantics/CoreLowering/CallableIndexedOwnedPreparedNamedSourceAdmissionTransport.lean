import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedCatalogAdmission

/-! Data-only source certificates transport to authentic Headers using actual
cache identity and compiled statement roots. Existing complete inventories
cover a scanned table through those same physical slots. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedSourceAdmissionTransport
open Core Frontend SourceInference
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedNamedSyntaxAdmission (TableAligned)
open CallableIndexedOwnedPreparedNamedScopedAdmission (SourceAdmission Admission)

def statements (source : TypedSource) : List StatementId :=
  source.roots.filterMap fun node => match node with
    | .statement id => some id
    | .expression _ => none

/-- Equal original cached rows identify the same prepared function and slot. -/
theorem cached_named {compiled : SourceCoreUnifiedCompilation.Compiled}
    {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : compiled.indexed.base.functions[index]? = some named)
    (same : named.specialized = row) : prepared.named = named := by
  have slot := CallableIndexedOwnedPreparedOrdinaryCachedInputs.cached_slot compiled selected
  have global := CallableIndexedPreparedInventories.cached_global_at compiled prepared.selected
  have key : prepared.named.signature.key = named.signature.key := by
    rw [CallableIndexedOwnedPreparedOrdinaryCachedInputs.cached_key compiled prepared.selected,
      CallableIndexedOwnedPreparedOrdinaryCachedInputs.cached_key compiled selected,
      prepared.same, same]
  have member : (prepared.named.signature, prepared.index) ∈
      compiled.indexed.base.globals.zipIdx.filter
        (fun item => decide (item.1.key = named.signature.key)) :=
    List.mem_filter.mpr ⟨List.mk_mem_zipIdx_iff_getElem?.mpr global, by simp only [key, decide_true]⟩
  rw [slot] at member
  have indexEq := (Prod.mk.inj (List.mem_singleton.mp member)).2
  exact Option.some.inj ((indexEq ▸ prepared.selected).symm.trans selected)

/-- The canonical data roots are exactly the accepted compiler roots. -/
theorem header_data {compiled : SourceCoreUnifiedCompilation.Compiled}
    {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    {instantiation : DeclarationInstantiation}
    {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header) :
    header.function.source = prepared.named.specialized.function.typedBody ∧
      header.function.body = statements prepared.named.specialized.function.typedBody ∧
      header.function.resultType = prepared.named.specialized.function.inferredBodyType := by
  rw [aligned.function]
  refine ⟨rfl, ?_, rfl⟩
  change prepared.compilation.statements = statements prepared.named.specialized.function.typedBody
  unfold statements
  rw [RecursiveNamedPreparedSourceFrames.compiled_roots_eq prepared.compilation]
  simp only [List.filterMap_map]
  induction prepared.compilation.statements with
  | nil => rfl
  | cons first rest ih => simpa only [List.filterMap_cons, Function.comp_apply] using congrArg (List.cons first) ih

/-- All source, body, result and contextual metadata indices are transported
from the real cached record; no independent equalities are requested. -/
theorem source_at_header {compiled : SourceCoreUnifiedCompilation.Compiled}
    {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    {instantiation : DeclarationInstantiation}
    {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : compiled.indexed.base.functions[index]? = some named)
    (same : named.specialized = row)
    {directRows : List SourceSpecialization.SpecializedFunction}
    (certificate : SourceAdmission compiled named named.specialized.function.typedBody
      (statements named.specialized.function.typedBody)
      named.specialized.function.inferredBodyType directRows) :
    Admission prepared header directRows := by
  have namedEq := cached_named prepared selected same
  obtain ⟨source, body, result⟩ := header_data prepared aligned
  change SourceAdmission compiled prepared.named header.function.source header.function.body
    header.function.resultType directRows
  rw [source, body, result, namedEq]
  exact certificate

/-- A legacy complete inventory also covers every executable table row. The
proof uses the exact cache position, never evaluation of semantic Inputs. -/
theorem table_aligned_of_complete {compiled : SourceCoreUnifiedCompilation.Compiled}
    {inputs : List (Input compiled)} (rows : Inventory inputs)
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (headers rows))
    (table : CallableIndexedOwnedPreparedOrdinarySyntaxTable.Table compiled) :
    TableAligned inputs table.rows := by
  intro row member
  obtain ⟨index, named, selected, same, _eligible⟩ := table.admitted row member
  obtain ⟨header, headerMember, slot, _signature⟩ := complete index named.signature
    (CallableIndexedPreparedInventories.cached_global_at compiled selected)
  obtain ⟨input, packet, retained, packetEq⟩ := rows.mem_headers header headerMember
  have indexEq : input.prepared.index = index := packet.aligned.slot.symm.trans
    ((congrArg (·.slot) packetEq).trans slot)
  have namedEq : input.prepared.named = named :=
    Option.some.inj ((indexEq ▸ input.prepared.selected).symm.trans selected)
  exact ⟨input, Inventory.input_member retained,
    input.prepared.same.symm.trans ((congrArg (·.specialized) namedEq).trans same)⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedSourceAdmissionTransport
