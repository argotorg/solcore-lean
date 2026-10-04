import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaEntryPrefix
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogEntries
import Solcore.Test.SourceCoreCallableIndexedLambdaRuntimeBody

/-! The actual parameter allocator supplies the canonical spine. The reached
entry retains its original function model, full heap, typed environment and
caller/lexical histories. The spine shifts existing global and frame slots;
neither a continuation agreement nor native typing supplies source history.
The runner reuses the registered actual indexed lambda suite. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreCallableIndexedLambdaEntrySpines
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CoreProof CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues
open CallableIndexedParameterCertificates CallableIndexedParameterMeaning SourceCoreCallableIndexedFrames
open CallableIndexedLambdaEntryPrefix

abbrev actual_view_prefix := @CallableIndexedLambdaViewPrefix.entry_of_accepted_with_spine

section Entry
variable {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {capturedActual : Environment}
  (captured : CallableIndexedLambdaValues.Captures prepared mapping world scope function.captured capturedActual)
  (code : Code prepared function scope captured.administrative) (history : History code)
  (inputs : CallableIndexedLambdaEntryPrefix.Context code) (functions : FunctionModel values.checked.catalog (CallableIndexedAmbient.ambientDefinitions prepared))
  {registry : SourceCoreRawMetadata.Registry} {arguments : List Dynamic.Value} {nativeArguments : List Value}
  (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    mapping world code.receipt.loweredParameters arguments nativeArguments)
  {before : Dynamic.Heap} {store : Store} {location : Location}
  {current : NativeFrame} {currentGhost : GhostFrame} {currentMetadata : Option MetadataState}
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
  (reference : captured.canonical[code.referenceIndex]? = some (.cellRef prepared.ancestry.layout.frame.type location))
  (read : store.read? location = some (encode prepared.ancestry.layout.frame current))
  (currentCarried : Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table current currentGhost currentMetadata)
  (unmapped : location ∉ mapping)
  (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed prepared.ancestry.graph.inputs history.metadata code.descriptor.id = true)


include captured code history inputs functions represented heaps locals reference read currentCarried unmapped allowed in
/-- The actual accepted prefix returns the allocated spine and the original
complete heap relation in the same entry. No body completion is required. -/
theorem actual_entry :
    ∃ entry : EntryFor captured code history inputs functions registry arguments nativeArguments before store location current currentGhost,
      ∃ added : Environment, added.length = code.receipt.loweredParameters.length ∧
        entry.entry.canonical = added ++ captured.canonical ∧
        CompatibleAmbientHeap.HeapRepresents values.checked registry functions
          entry.entry.mapping entry.entry.world entry.entry.heap entry.entry.store := by
  obtain ⟨entry, added, length, spine⟩ := entry_exists_for_with_spine captured code history inputs functions
    represented heaps locals reference read currentCarried unmapped allowed
  exact ⟨entry, added, length, spine, entry.entry.heaps⟩

include captured code history inputs functions represented heaps locals reference read currentCarried unmapped allowed in
/-- Empty arity adds no canonical values. Administrative values, heaps and
both histories remain in the original entry. -/
theorem empty_parameters (empty : nativeArguments = []) :
    ∃ entry : EntryFor captured code history inputs functions registry arguments nativeArguments before store location current currentGhost,
      entry.entry.canonical = captured.canonical := by
  obtain ⟨entry, added, length, spine⟩ := entry_exists_for_with_spine captured code history inputs functions
    represented heaps locals reference read currentCarried unmapped allowed
  have zero : code.receipt.loweredParameters.length = 0 := by simpa [empty] using represented.length.2
  have nil : added = [] := List.eq_nil_of_length_eq_zero (length.trans zero)
  exact ⟨entry, by simpa only [nil, List.nil_append] using spine⟩

variable (entry : EntryFor captured code history inputs functions registry arguments nativeArguments before store location current currentGhost)
  {added : Environment} (length : added.length = code.receipt.loweredParameters.length)
  (spine : entry.entry.canonical = added ++ captured.canonical)

include length spine in
/-- Every old slot is shifted by the actual number of allocated parameters. -/
theorem shifted_lookup {index : Nat} {value : Value}
    (found : captured.canonical[index]? = some value) :
    entry.entry.canonical[code.receipt.loweredParameters.length + index]? = some value := by
  rw [spine, ← length, List.getElem?_append_right (by omega)]
  simpa using found

include length spine reference in
/-- The surviving frame slot is the same physical reference; no type-tag
argument invents a carried frame or history. -/
theorem shifted_reference :
    entry.entry.canonical[code.receipt.loweredParameters.length + code.referenceIndex]? =
      some (.cellRef prepared.ancestry.layout.frame.type location) :=
  shifted_lookup captured code history inputs functions entry length spine reference

include entry in
theorem same_full_heap :
    CompatibleAmbientHeap.HeapRepresents values.checked registry functions
      entry.entry.mapping entry.entry.world entry.entry.heap entry.entry.store := entry.entry.heaps

include entry in
theorem same_frame_history :
    Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table entry.next
      (.lambda code.descriptor.id history.ghost) (some history.metadata) := entry.nextHistory

variable {program : SourceSemantics.Program}
  {headers : RecursiveNamedCatalog.Inventory prepared.ancestry values prepared.layouts.definitions program}
  {locations : RecursiveNamedCatalog.Locations (prepared := prepared.ancestry) (values := values)
    (ambient := CallableIndexedAmbient.ambientDefinitions prepared) (program := program)}
  {capturePrefix callerPrefix : Nat}
  (initial : RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix scope mapping world before store captured.canonical)

include length spine initial in
/-- A real catalog entry supplies the ordered global slot. The allocator's
spine preserves that slot independently of arbitrary unused administrative data. -/
theorem ordered_global
    (header : RecursiveNamedCatalog.Header prepared.ancestry values prepared.layouts.definitions program)
    (member : header ∈ headers) :
    entry.entry.canonical[code.receipt.loweredParameters.length + (scope.length + callerPrefix + header.slot)]? =
      some (.cellRef (OptionalCell.cellType header.named.signature.functionType) (locations header)) :=
  shifted_lookup captured code history inputs functions entry length spine (initial.globals header member)
end Entry

section Concrete
/-- This finite example has two global slots and an arbitrary untouched
administrative suffix. Only the actual one-value prefix shifts the lookups. -/
theorem nonempty_globals_unused_suffix (unused : Environment) :
    let canonical : Environment := [.cellRef .word 3, .cellRef .bool 4, .unit] ++ unused
    let reached : Environment := [.bool true] ++ canonical
    reached[1]? = some (.cellRef .word 3) ∧
      reached[2]? = some (.cellRef .bool 4) ∧ reached.drop 4 = unused := by
  simp
end Concrete

def run : IO Unit := Tests.SourceCoreCallableIndexedLambdaRuntimeBody.run
end Tests.SourceCoreCallableIndexedLambdaEntrySpines
