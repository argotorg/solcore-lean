import Solcore.SourceSemantics.CoreLowering.RecursiveGlobalInitializationTyping
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogEntries

/-! Initial catalog authority is constructed from the actual reserved slots,
installed full closures and real empty indexed frame. Independent static source
headers and their empty lexical contexts remain explicit. No source body law,
source execution or decoder-derived history is used to initialize authority. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogInitialization
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableAncestryPairedLookup CallableIndexedHistory RecursiveNamedCatalog
open RecursiveGlobalInitializationMeaning RecursiveGlobalInitializationTyping

def location (signatures : List Signature) (slot : Nat) : Nat := 1 + (signatures.length - 1 - slot)

theorem global_reference (signatures : List Signature) (layout : SourceCoreCallableIndexedFrames.Layout)
    {slot : Nat} {signature : Signature} (found : signatures[slot]? = some signature) :
    (initialEnvironment signatures layout)[slot]? =
      some (.cellRef (OptionalCell.cellType signature.functionType) (location signatures slot)) := by
  simpa only [initialEnvironment, location, List.reverse_reverse, List.length_reverse, List.length_singleton] using
    reserved_reference signatures.reverse [SourceCoreCallableIndexedFrames.encode layout .empty]
      [.cellRef layout.type 0] (by simpa using found)

theorem frame_reference (signatures : List Signature) (layout : SourceCoreCallableIndexedFrames.Layout) :
    (initialEnvironment signatures layout)[signatures.length]? = some (.cellRef layout.type 0) := by
  rw [initialEnvironment, reserved_environment]
  simp

theorem frame_read (signatures : List Signature) (rows : List LambdaRow)
    (layout : SourceCoreCallableIndexedFrames.Layout) :
    (initialStore signatures rows layout).read? 0 = some (SourceCoreCallableIndexedFrames.encode layout .empty) := by
  have unchanged :=
    initialized_prefix signatures.reverse rows [.cellRef layout.type 0]
      [SourceCoreCallableIndexedFrames.encode layout .empty]
      (fun index => 1 + (signatures.length - 1 - index))
      (by intro i within; simp only [List.length_singleton]; omega) (location := 0) (by simp)
  exact unchanged.trans rfl

private theorem row_bound {signatures : List Signature} {rows : List LambdaRow}
    (ordered : ∀ (i : Nat) (row : LambdaRow), rows[i]? = some row → ∃ (signature : Signature),
      signatures[i]? = some signature ∧ signature.functionType = .function row.parameter row.result)
    {i : Nat} (within : i < rows.length) : i < signatures.length := by
  obtain ⟨signature, selected, _⟩ := ordered i rows[i] (List.getElem?_eq_getElem within)
  exact (List.getElem?_eq_some_iff.mp selected).1

theorem closure_read (signatures : List Signature) (rows : List LambdaRow)
    (layout : SourceCoreCallableIndexedFrames.Layout)
    (ordered : ∀ (i : Nat) (row : LambdaRow), rows[i]? = some row → ∃ (signature : Signature),
      signatures[i]? = some signature ∧ signature.functionType = .function row.parameter row.result)
    {slot : Nat} {row : LambdaRow} (found : rows[slot]? = some row) :
    (initialStore signatures rows layout).read? (location signatures slot) =
      some (.inRight .unit (installedValue (initialEnvironment signatures layout) slot row)) := by
  have bounds : ∀ i, i < rows.length → location signatures (0 + i) <
      (reserve signatures.reverse [SourceCoreCallableIndexedFrames.encode layout .empty] [.cellRef layout.type 0]).1.length := by
    intro i within
    simpa only [location, List.length_singleton, List.length_reverse, Nat.zero_add] using
      reserved_location_bound signatures.reverse [SourceCoreCallableIndexedFrames.encode layout .empty]
        [.cellRef layout.type 0] (by simpa using row_bound ordered within)
  have distinct : ∀ i j, i < rows.length → j < rows.length → i ≠ j → location signatures (0 + i) ≠ location signatures (0 + j) := by
    intro i j hi hj different
    have left := row_bound ordered hi
    have right := row_bound ordered hj
    simp only [Nat.zero_add, location]
    omega
  have receipt := installed_read rows (location signatures) (initialEnvironment signatures layout)
      (reserve signatures.reverse [SourceCoreCallableIndexedFrames.encode layout .empty] [.cellRef layout.type 0]).1
      0 bounds distinct found
  have locations : location signatures = (fun index => 1 + (signatures.length - 1 - index)) := rfl
  rw [locations] at receipt
  simpa only [initialStore, location, Nat.zero_add] using receipt

theorem row_of_cached {rows : List LambdaRow} {slot : Nat} {parameter result : Ty} {body : Expr}
    (cached : (rows.map LambdaRow.expression)[slot]? = some (.lambda parameter result body)) :
    rows[slot]? = some ⟨parameter, result, body⟩ := by
  rw [List.getElem?_map] at cached
  cases found : rows[slot]? with
  | none => simp [found] at cached
  | some row =>
    rcases row with ⟨p, r, b⟩
    simp only [found, Option.map_some, LambdaRow.expression] at cached
    cases cached
    rfl

variable (compiled : SourceCoreUnifiedCompilation.Compiled)
  {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}
  (headers : Inventory compiled.indexed.ancestry values ambient.definitions program)
  (rows : List LambdaRow)
  (cached : compiled.indexed.secondPass.closures = rows.map LambdaRow.expression)
  (ordered : ∀ (i : Nat) (row : LambdaRow), rows[i]? = some row → ∃ (signature : Signature),
    compiled.indexed.base.globals[i]? = some signature ∧ signature.functionType = .function row.parameter row.result)
  (ledger : Ledger headers compiled.indexed.secondPass.closures)
  (globals : ∀ header, header ∈ headers → compiled.indexed.base.globals[header.slot]? = some header.named.signature)
  (sizes : ∀ header, header ∈ headers → header.globals = compiled.indexed.base.globals.length)
  (locals : ∀ header, header ∈ headers → header.function.context.locals = [])

include cached ordered ledger globals sizes locals in
/-- All native captures and their shared references follow from actual cache
reads and native store preservation. The independent source header and empty
source lexical context are explicit static inputs. -/
def of_stored {world : StoreTyping}
    (typed : RuntimeStoreHasTypes world
      (initialStore compiled.indexed.base.globals rows compiled.indexed.ancestry.layout.frame) ambient.definitions) :
    Authority headers (fun header => location compiled.indexed.base.globals header.slot) 0 [] world ⟨[]⟩
      (initialStore compiled.indexed.base.globals rows compiled.indexed.ancestry.layout.frame) := by
  have frameRead := frame_read compiled.indexed.base.globals rows compiled.indexed.ancestry.layout.frame
  have frameType : world[0]? = some compiled.indexed.ancestry.layout.frame.type := by
    rw [typed.world_eq, List.getElem?_map]
    change Option.map Value.type ((initialStore _ _ _).read? 0) = _
    rw [frameRead]
    rfl
  refine {
    frameLocation := 0, unmapped := by simp, typed := frameType,
    current := .empty, ghost := .empty, frame := ⟨frameRead, .stable .empty⟩,
    records := [], snapshots := by simp [CallableIndexedSnapshots.All], distinct := by simp,
    captures := ?_ }
  intro header member
  have rowFound := row_of_cached (by rw [← cached]; exact ledger.cached header member)
  have read := closure_read compiled.indexed.base.globals rows compiled.indexed.ancestry.layout.frame ordered rowFound
  obtain ⟨capturedContext, capturedTyped, _⟩ := stored_closure typed read
  obtain ⟨canonicalContext, canonicalTyped⟩ := drop_installer_units header.slot capturedTyped
  have embedding : EnvironmentsAgree (shift header.slot)
      (initialEnvironment compiled.indexed.base.globals compiled.indexed.ancestry.layout.frame)
      (List.replicate header.slot .unit ++ initialEnvironment compiled.indexed.base.globals compiled.indexed.ancestry.layout.frame) := by
    intro index value found
    rw [List.getElem?_append_right (by simp [shift])]
    simpa [shift] using found
  have reference := frame_reference compiled.indexed.base.globals compiled.indexed.ancestry.layout.frame
  refine ⟨{
    administrative := canonicalContext,
    canonical := initialEnvironment compiled.indexed.base.globals compiled.indexed.ancestry.layout.frame,
    captured := List.replicate header.slot (Value.unit) ++ initialEnvironment compiled.indexed.base.globals compiled.indexed.ancestry.layout.frame,
    capturedContext := capturedContext, embedding := shift header.slot,
    environments := .nil canonicalTyped, locals := ?_, layout := embedding, typed := capturedTyped,
    reference := by simpa only [sizes header member] using reference,
    capturedReference := embedding reference, coherent := ?_, unmapped := by simp,
    distinct := by simp [location], read := read }⟩
  · rw [locals header member]
    exact .nil
  · intro target targetMember
    simpa only [Nat.zero_add] using global_reference compiled.indexed.base.globals
      compiled.indexed.ancestry.layout.frame (globals target targetMember)

include cached ordered ledger globals sizes locals in
/-- The actual recipe closes native store typing. This factory has no source
or native function-body correspondence premise. -/
theorem of_recipe {recipe : SourceCoreIndexedSession.Recipe}
    (accepted : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (definitions : compiled.indexed.layouts.definitions = ambient.definitions) :
    ∃ world, Nonempty (Authority headers (fun header => location compiled.indexed.base.globals header.slot) 0 [] world ⟨[]⟩
      (initialStore compiled.indexed.base.globals rows compiled.indexed.ancestry.layout.frame)) := by
  obtain ⟨world, typed⟩ := stored accepted rows cached ordered
  rw [definitions] at typed
  exact ⟨world, ⟨of_stored compiled headers rows cached ordered ledger globals sizes locals typed⟩⟩

include cached ordered ledger globals sizes locals in
/-- A fresh source heap is represented alongside the complete initial caller
entry. The source function model is explicit; its body semantics is not used
to create administrative closures or catalog authority. -/
theorem initial_entry {recipe : SourceCoreIndexedSession.Recipe}
    (accepted : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (definitions : compiled.indexed.layouts.definitions = ambient.definitions)
    (functions : FunctionModel values.checked.catalog ambient) (registry : SourceCoreRawMetadata.Registry) :
    ∃ world,
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions [] world ⟨[]⟩
        (initialStore compiled.indexed.base.globals rows compiled.indexed.ancestry.layout.frame) ∧
      Nonempty (Entry headers (fun header => location compiled.indexed.base.globals header.slot) 0 0 [] [] world ⟨[]⟩
        (initialStore compiled.indexed.base.globals rows compiled.indexed.ancestry.layout.frame)
        (initialEnvironment compiled.indexed.base.globals compiled.indexed.ancestry.layout.frame)) := by
  obtain ⟨world, typed⟩ := stored accepted rows cached ordered
  rw [definitions] at typed
  refine ⟨world, ⟨rfl, ?_, typed, ?_⟩, ⟨of_stored compiled headers rows cached ordered ledger globals sizes locals typed, ?_⟩⟩
  · intro left right target impossible
    simp at impossible
  · intro source target impossible
    simp at impossible
  · intro header member
    simpa only [List.length_nil, Nat.zero_add] using global_reference compiled.indexed.base.globals
      compiled.indexed.ancestry.layout.frame (globals header member)

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogInitialization
