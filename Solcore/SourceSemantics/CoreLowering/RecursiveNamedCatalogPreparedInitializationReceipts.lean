import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogPreparedInitialization

/-! Positive receipts for the actual prepared catalog initializer. The returned
entry is built with the existing stored authority. Each retained capture comes
from its prescribed initialized closure read, with the real installer prefix.
Source headers and their static cache alignment remain explicit. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogPreparedInitializationReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload RecursiveNamedCatalog
open RecursiveGlobalInitializationMeaning RecursiveGlobalInitializationTyping

variable (compiled : SourceCoreUnifiedCompilation.Compiled)
  {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}
  (headers : Inventory compiled.indexed.ancestry values ambient.definitions program)
  (rows : List LambdaRow)

/-- The same initialized capture retains its actual canonical environment,
installer prefix and code renaming. Its full store read and typing are fields
of the indexed Capture itself. -/
structure StoredCaptureReceipt {world : StoreTyping}
    {header : Header compiled.indexed.ancestry values ambient.definitions program}
    (capture : Capture headers
      (fun target => RecursiveNamedCatalogInitialization.location compiled.indexed.base.globals target.slot)
      0 0 header [] world ⟨[]⟩
      (initialStore compiled.indexed.base.globals rows compiled.indexed.ancestry.layout.frame)) : Prop where
  canonical : capture.canonical =
    initialEnvironment compiled.indexed.base.globals compiled.indexed.ancestry.layout.frame
  captured : capture.captured = List.replicate header.slot Value.unit ++
    initialEnvironment compiled.indexed.base.globals compiled.indexed.ancestry.layout.frame
  embedding : capture.embedding = shift header.slot

variable
  (cached : compiled.indexed.secondPass.closures = rows.map LambdaRow.expression)
  (ordered : ∀ (i : Nat) (row : LambdaRow), rows[i]? = some row → ∃ (signature : Signature),
    compiled.indexed.base.globals[i]? = some signature ∧ signature.functionType = .function row.parameter row.result)
  (ledger : Ledger headers compiled.indexed.secondPass.closures)
  (globals : ∀ header, header ∈ headers → compiled.indexed.base.globals[header.slot]? = some header.named.signature)
  (sizes : ∀ header, header ∈ headers → header.globals = compiled.indexed.base.globals.length)
  (locals : ∀ header, header ∈ headers → header.function.context.locals = [])

include cached ordered ledger globals sizes locals in
/-- Construct a prescribed capture from the actual initialized store. Native
closure typing is used only for this full known closure read. -/
theorem stored_capture {world : StoreTyping}
    (typed : RuntimeStoreHasTypes world
      (initialStore compiled.indexed.base.globals rows compiled.indexed.ancestry.layout.frame) ambient.definitions)
    (header : Header compiled.indexed.ancestry values ambient.definitions program) (member : header ∈ headers) :
    ∃ capture : Capture headers
        (fun target => RecursiveNamedCatalogInitialization.location compiled.indexed.base.globals target.slot)
        0 0 header [] world ⟨[]⟩
        (initialStore compiled.indexed.base.globals rows compiled.indexed.ancestry.layout.frame),
      StoredCaptureReceipt compiled headers rows capture := by
  have rowFound := RecursiveNamedCatalogInitialization.row_of_cached
    (by rw [← cached]; exact ledger.cached header member)
  have read := RecursiveNamedCatalogInitialization.closure_read compiled.indexed.base.globals rows
    compiled.indexed.ancestry.layout.frame ordered rowFound
  obtain ⟨capturedContext, capturedTyped, _⟩ := stored_closure typed read
  obtain ⟨canonicalContext, canonicalTyped⟩ := drop_installer_units header.slot capturedTyped
  have embedding : EnvironmentsAgree (shift header.slot)
      (initialEnvironment compiled.indexed.base.globals compiled.indexed.ancestry.layout.frame)
      (List.replicate header.slot .unit ++ initialEnvironment compiled.indexed.base.globals compiled.indexed.ancestry.layout.frame) := by
    intro index value found
    rw [List.getElem?_append_right (by simp [shift])]
    simpa [shift] using found
  have reference := RecursiveNamedCatalogInitialization.frame_reference compiled.indexed.base.globals
    compiled.indexed.ancestry.layout.frame
  refine ⟨{
    administrative := canonicalContext,
    canonical := initialEnvironment compiled.indexed.base.globals compiled.indexed.ancestry.layout.frame,
    captured := List.replicate header.slot Value.unit ++
      initialEnvironment compiled.indexed.base.globals compiled.indexed.ancestry.layout.frame,
    capturedContext := capturedContext, embedding := shift header.slot,
    environments := .nil canonicalTyped, locals := ?_, layout := embedding, typed := capturedTyped,
    reference := by simpa only [sizes header member] using reference,
    capturedReference := embedding reference, coherent := ?_, unmapped := by simp,
    distinct := by simp [RecursiveNamedCatalogInitialization.location], read := read },
    ⟨rfl, rfl, rfl⟩⟩
  · rw [locals header member]
    exact .nil
  · intro target targetMember
    simpa only [Nat.zero_add] using RecursiveNamedCatalogInitialization.global_reference
      compiled.indexed.base.globals compiled.indexed.ancestry.layout.frame (globals target targetMember)

/-- These facts concern the concrete initial Entry returned by the producer,
with the same initial store and genuine positive captures. -/
structure ConstructorReceipt (world : StoreTyping)
    (entry : Entry headers
      (fun header => RecursiveNamedCatalogInitialization.location compiled.indexed.base.globals header.slot)
      0 0 [] [] world ⟨[]⟩ (RecursiveNamedCatalogPreparedInitialization.store compiled)
      (RecursiveNamedCatalogPreparedInitialization.environment compiled)) : Prop where
  frameLocation : entry.authority.frameLocation = 0
  current : entry.authority.current = .empty
  ghost : entry.authority.ghost = .empty
  records : entry.authority.records = []
  captures : ∀ header, header ∈ headers →
    ∃ capture : Capture headers
        (fun target => RecursiveNamedCatalogInitialization.location compiled.indexed.base.globals target.slot)
        0 0 header [] world ⟨[]⟩ (RecursiveNamedCatalogPreparedInitialization.store compiled),
      StoredCaptureReceipt compiled headers (RecursiveNamedCachedRows.rows compiled) capture

include ledger sizes locals in
/-- Actual preparation supplies native store typing once. The existing stored
authority and empty heap representation are retained at that same world/store;
no body execution or classification of an arbitrary returned Entry is needed. -/
theorem entry_with_constructor {recipe : SourceCoreIndexedSession.Recipe}
    (accepted : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (definitions : compiled.indexed.layouts.definitions = ambient.definitions)
    (functions : FunctionModel values.checked.catalog ambient) (registry : SourceCoreRawMetadata.Registry) :
    ∃ world, ∃ entry : Entry headers
        (fun header => RecursiveNamedCatalogInitialization.location compiled.indexed.base.globals header.slot)
        0 0 [] [] world ⟨[]⟩ (RecursiveNamedCatalogPreparedInitialization.store compiled)
        (RecursiveNamedCatalogPreparedInitialization.environment compiled),
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions [] world ⟨[]⟩
        (RecursiveNamedCatalogPreparedInitialization.store compiled) ∧
      ConstructorReceipt compiled headers world entry := by
  obtain ⟨world, typed⟩ := RecursiveNamedCatalogPreparedInitialization.typed accepted
  rw [definitions] at typed
  have actualGlobals : ∀ header, header ∈ headers →
      compiled.indexed.base.globals[header.slot]? = some header.named.signature :=
    fun header _ => CallableIndexedPreparedInventories.cached_global_at compiled header.selected
  let authority := RecursiveNamedCatalogInitialization.of_stored compiled headers
    (RecursiveNamedCachedRows.rows compiled) (RecursiveNamedCachedRows.exact_cache compiled)
    (RecursiveNamedCachedRows.ordered compiled) ledger actualGlobals sizes locals typed
  let entry : Entry headers
      (fun header => RecursiveNamedCatalogInitialization.location compiled.indexed.base.globals header.slot)
      0 0 [] [] world ⟨[]⟩ (RecursiveNamedCatalogPreparedInitialization.store compiled)
      (RecursiveNamedCatalogPreparedInitialization.environment compiled) :=
    ⟨authority, by
      intro header member
      simpa only [RecursiveNamedCatalogPreparedInitialization.environment, List.length_nil, Nat.zero_add] using
        RecursiveNamedCatalogInitialization.global_reference
        compiled.indexed.base.globals compiled.indexed.ancestry.layout.frame (actualGlobals header member)⟩
  refine ⟨world, entry, ⟨rfl, ?_, typed, ?_⟩, ⟨rfl, rfl, rfl, rfl, ?_⟩⟩
  · intro left right target impossible
    simp at impossible
  · intro source target impossible
    simp at impossible
  · intro header member
    exact stored_capture compiled headers (RecursiveNamedCachedRows.rows compiled)
      (RecursiveNamedCachedRows.exact_cache compiled) (RecursiveNamedCachedRows.ordered compiled)
      ledger actualGlobals sizes locals typed header member

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogPreparedInitializationReceipts
