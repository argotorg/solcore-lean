import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaRuntimeEntry
import Solcore.Test.SourceCoreCallableIndexedLambdaRuntimeBody

/-! The actual lambda allocator and its retained spine supply a catalog entry
with the full lambda history. Initial capture coherence and catalog authority
are explicit observations, independent of native typing. The source entry
stays distinct from a named entry. Lambda body meaning remains the existing
builtin fragment; this unit supplies the catalog boundary needed by a later
named-body extension. The runner reuses the registered actual lambda suite. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreCallableIndexedLambdaCatalogEntries
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CoreProof CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues
open CallableIndexedParameterCertificates CallableIndexedParameterMeaning SourceCoreCallableIndexedFrames
open CallableIndexedLambdaCatalogEntries

section Entry
variable {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {capturedActual : Environment}
  (captured : Captures prepared mapping world scope function.captured capturedActual)
  (code : Code prepared function scope captured.administrative) (history : History code)
  (inputs : CallableIndexedLambdaEntryPrefix.Context code)
  (functions : FunctionModel values.checked.catalog (CallableIndexedAmbient.ambientDefinitions prepared))
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
  {program : SourceSemantics.Program}
  {headers : RecursiveNamedCatalog.Inventory prepared.ancestry values prepared.layouts.definitions program}
  {locations : RecursiveNamedCatalog.Locations (prepared := prepared.ancestry) (values := values)
    (ambient := CallableIndexedAmbient.ambientDefinitions prepared) (program := program)}
  {capturePrefix callerPrefix : Nat}
  (initial : RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix scope mapping world before store captured.canonical)
  (sameFrame : initial.authority.frameLocation = location)

include captured code history inputs functions represented heaps locals reference read currentCarried unmapped allowed initial sameFrame in
/-- The same actual unsized prefix supplies the source state, full heap and
ordered globals. Its existing agreement is not converted into a grade. -/
theorem actual_source_entry :
    ∃ entry : CallableIndexedLambdaEntryPrefix.EntryFor captured code history inputs functions registry
      arguments nativeArguments before store location current currentGhost,
      ∃ sourceEntry : SourceEntry code history headers locations capturePrefix callerPrefix
        (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
        entry.entry.mapping entry.entry.world entry.entry.heap entry.entry.store entry.entry.canonical,
        sourceEntry.catalog.authority.frameLocation = location ∧
        sourceEntry.catalog.authority.current = entry.next ∧
        CompatibleAmbientHeap.HeapRepresents values.checked registry functions
          entry.entry.mapping entry.entry.world entry.entry.heap entry.entry.store := by
  obtain ⟨entry, added, length, spine⟩ := CallableIndexedLambdaEntryPrefix.entry_exists_for_with_spine
    captured code history inputs functions represented heaps locals reference read currentCarried unmapped allowed
  exact ⟨entry, source_entry entry initial sameFrame length spine, sameFrame, rfl, entry.entry.heaps⟩

include captured code inputs initial reference in
/-- Capture coherence observes the actual canonical slots. The separate
initial catalog supplies authority; the frame lookup comes from the receipt. -/
theorem actual_capture_globals : CaptureGlobals headers locations callerPrefix scope captured.canonical location :=
  ⟨initial.globals, by simpa only [inputs.referenceIndex] using reference⟩

variable (entry : CallableIndexedLambdaEntryPrefix.EntryFor captured code history inputs functions registry
    arguments nativeArguments before store location current currentGhost)
  {added : Environment} (length : added.length = code.receipt.loweredParameters.length)
  (spine : entry.entry.canonical = added ++ captured.canonical)

include initial sameFrame length spine in
theorem reached_ordered_global
    (header : RecursiveNamedCatalog.Header prepared.ancestry values prepared.layouts.definitions program)
    (member : header ∈ headers) :
    entry.entry.canonical[(code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope).length +
      callerPrefix + header.slot]? = some (.cellRef (OptionalCell.cellType header.named.signature.functionType) (locations header)) :=
  (source_entry entry initial sameFrame length spine).catalog.globals header member

include initial sameFrame length spine in
theorem full_carried_history :
    Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table
      (source_entry entry initial sameFrame length spine).catalog.authority.current
      (.lambda code.descriptor.id history.ghost) (some history.metadata) :=
  (source_entry entry initial sameFrame length spine).carried

variable (reached : CallableIndexedLambdaEntryBounds.PrefixFor captured code history inputs functions registry arguments before store location current)

include reached initial sameFrame in
/-- Sized completions supply the same catalog boundary without changing the
original body witness or either grade. -/
theorem sized_catalog_is_legacy :
    (source_entry_sized reached initial sameFrame).catalog =
      CallableIndexedLambdaRuntimeEntry.catalog_entry_for reached initial sameFrame := rfl

include reached initial sameFrame in
theorem sized_frame_reference :
    reached.canonical[(code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope).length +
      1 + prepared.base.globals.length]? =
      some (.cellRef prepared.ancestry.layout.frame.type (source_entry_sized reached initial sameFrame).catalog.authority.frameLocation) :=
  (source_entry_sized reached initial sameFrame).reference

end Entry

section Boundaries
/-- Native typing has no role in this constructor distinction. The actual
lambda ghost cannot be substituted for a named source-entry ghost. -/
theorem lambda_not_named (id origin : Word) (parent : GhostFrame) :
    ((.lambda id parent) : GhostFrame) ≠ .named origin := by intro same; cases same

/-- Two ordered globals and a physical frame survive finite capture retention
and one real added slot. The arbitrary unused suffix is kept independently. -/
theorem nonempty_globals_unused_suffix (unused : Environment) :
    let canonical : Environment := [.cellRef .word 3, .cellRef .bool 4, .cellRef .unit 5] ++ unused
    let finite := canonical.take 3
    let reached : Environment := [.bool true] ++ canonical
    finite[0]? = some (.cellRef .word 3) ∧ finite[1]? = some (.cellRef .bool 4) ∧
      finite[2]? = some (.cellRef .unit 5) ∧
      reached[1]? = some (.cellRef .word 3) ∧ reached[2]? = some (.cellRef .bool 4) ∧
      reached[3]? = some (.cellRef .unit 5) ∧ reached.drop 4 = unused := by simp

end Boundaries

def run : IO Unit := Tests.SourceCoreCallableIndexedLambdaRuntimeBody.run
end Tests.SourceCoreCallableIndexedLambdaCatalogEntries
