import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaEntryPrefix
import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaEntryBounds
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogEntries

/-! Actual lambda prefixes transport a separately observed finite catalog.
The unsized allocator receipt and the original sized completion use the same
installation and ordered-spine proof. Source entries retain the lambda ghost,
full carried metadata and physical frame reference; named source entries are
not substituted for them. Catalog authority and capture coherence remain
independent inputs. No lambda body correspondence is supplied here. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaCatalogEntries
open Core Frontend SourceInference GeneralHeap ReadOnly CoreProof CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues
open CallableIndexedParameterCertificates CallableIndexedParameterMeaning
open SourceCoreCallableIndexedFrames

variable {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {program : Program}
  {headers : RecursiveNamedCatalog.Inventory prepared.ancestry values prepared.layouts.definitions program}
  {locations : RecursiveNamedCatalog.Locations (prepared := prepared.ancestry) (values := values)
    (ambient := CallableIndexedAmbient.ambientDefinitions prepared) (program := program)}
  {capturePrefix callerPrefix : Nat}

/-- These are observations of actual ordered captures and the shared physical
frame. They contain neither authority nor a runtime body law. -/
structure CaptureGlobals (headers : RecursiveNamedCatalog.Inventory prepared.ancestry values prepared.layouts.definitions program)
    (locations : RecursiveNamedCatalog.Locations (prepared := prepared.ancestry) (values := values)
      (ambient := CallableIndexedAmbient.ambientDefinitions prepared) (program := program))
    (callerPrefix : Nat) (scope : SourceCoreLocalCell.Scope) (canonical : Environment) (location : Location) : Prop where
  globals : ∀ header, header ∈ headers → canonical[scope.length + callerPrefix + header.slot]? = some
    (.cellRef (OptionalCell.cellType header.named.signature.functionType) (locations header))
  reference : canonical[scope.length + 1 + prepared.base.globals.length]? =
    some (.cellRef prepared.ancestry.layout.frame.type location)

def CaptureGlobals.catalog {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap}
    {store : Store} {canonical : Environment} {location : Location}
    (observed : CaptureGlobals headers locations callerPrefix scope canonical location)
    (authority : RecursiveNamedCatalog.Authority headers locations capturePrefix mapping world heap store) :
    RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix scope mapping world heap store canonical :=
  ⟨authority, observed.globals⟩

/-- Keeping a finite supported prefix preserves its observed global and frame
slots. Bounds are independent static evidence about those actual slots. -/
theorem CaptureGlobals.take {canonical : Environment} {location : Location}
    (observed : CaptureGlobals headers locations callerPrefix scope canonical location) {count : Nat}
    (globalBounds : ∀ header, header ∈ headers → scope.length + callerPrefix + header.slot < count)
    (frameBound : scope.length + 1 + prepared.base.globals.length < count) :
    CaptureGlobals headers locations callerPrefix scope (canonical.take count) location := by
  constructor
  · intro header member
    rw [List.getElem?_take, if_pos (globalBounds header member)]
    exact observed.globals header member
  · rw [List.getElem?_take, if_pos frameBound]
    exact observed.reference

section Prefix
variable {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {canonical : Environment} {code : Code prepared function scope administrative} {history : History code}
  {location : Location} {next : NativeFrame} {futureMap : LocationMap} {futureWorld : StoreTyping}
  {after : Dynamic.Heap} {futureStore : Store} {futureCanonical : Environment}

/-- The sole catalog installation proof consumes original prefix effects and
the actual allocator's ordered additions. It does not execute a body. -/
def catalog_after_prefix
    (initial : RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix scope mapping world before store canonical)
    (sameFrame : initial.authority.frameLocation = location)
    (history : Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table next
      (.lambda code.descriptor.id history.ghost) (some history.metadata))
    (maps : LocationMap.Extends mapping futureMap) (worlds : WorldExtends world futureWorld)
    (frame : AdministrativePreserved mapping (store.set location (encode prepared.ancestry.layout.frame next)) futureMap futureStore)
    (metadata : Dynamic.HeapMetadataExtend before after)
    (spine : ∃ added : Environment, added.length = code.receipt.loweredParameters.length ∧ futureCanonical = added ++ canonical) :
    RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      futureMap futureWorld after futureStore futureCanonical := by
  let installed := initial.authority.install (Current.stable history)
  have installedFrame : AdministrativePreserved mapping
      (store.set initial.authority.frameLocation (encode prepared.ancestry.layout.frame next)) futureMap futureStore := by
    simpa only [sameFrame] using frame
  refine ⟨installed.extend maps worlds installedFrame metadata, ?_⟩
  intro header member
  obtain ⟨added, length, canonicalEq⟩ := spine
  rw [canonicalEq]
  simp only [List.length_append, List.length_map, List.length_reverse]
  have index : code.receipt.loweredParameters.length + scope.length + callerPrefix + header.slot =
      added.length + (scope.length + callerPrefix + header.slot) := by omega
  rw [index, List.getElem?_append_right (by omega)]
  simpa only [Nat.add_sub_cancel_left] using initial.globals header member

end Prefix

/-- This source entry has the actual lambda ghost and full original metadata.
Its frame reference and catalog authority are separate from native typing. -/
structure SourceEntry (code : Code prepared function scope administrative) (history : History code)
    (headers : RecursiveNamedCatalog.Inventory prepared.ancestry values prepared.layouts.definitions program)
    (locations : RecursiveNamedCatalog.Locations (prepared := prepared.ancestry) (values := values)
      (ambient := CallableIndexedAmbient.ambientDefinitions prepared) (program := program)) (capturePrefix callerPrefix : Nat)
    (bodyScope : SourceCoreLocalCell.Scope) (mapping : LocationMap) (world : StoreTyping)
    (heap : Dynamic.Heap) (store : Store) (canonical : Environment) where
  catalog : RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix bodyScope mapping world heap store canonical
  ghost : catalog.authority.ghost = .lambda code.descriptor.id history.ghost
  carried : Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table catalog.authority.current
    (.lambda code.descriptor.id history.ghost) (some history.metadata)
  reference : canonical[bodyScope.length + 1 + prepared.base.globals.length]? =
    some (.cellRef prepared.ancestry.layout.frame.type catalog.authority.frameLocation)

variable {code : Code prepared function scope administrative} {history : History code}

def SourceEntry.extend {bodyScope : SourceCoreLocalCell.Scope} {mapping futureMap : LocationMap} {world futureWorld : StoreTyping}
    {heap after : Dynamic.Heap} {store futureStore : Store} {canonical : Environment}
    (entry : SourceEntry code history headers locations capturePrefix callerPrefix bodyScope mapping world heap store canonical)
    (maps : LocationMap.Extends mapping futureMap) (worlds : WorldExtends world futureWorld)
    (frame : AdministrativePreserved mapping store futureMap futureStore)
    (metadata : Dynamic.HeapMetadataExtend heap after) :
    SourceEntry code history headers locations capturePrefix callerPrefix bodyScope futureMap futureWorld after futureStore canonical :=
  { entry with catalog := entry.catalog.extend maps worlds frame metadata }

def protectedEntry (code : Code prepared function scope administrative) (history : History code)
    (headers : RecursiveNamedCatalog.Inventory prepared.ancestry values prepared.layouts.definitions program)
    (locations : RecursiveNamedCatalog.Locations (prepared := prepared.ancestry) (values := values)
      (ambient := CallableIndexedAmbient.ambientDefinitions prepared) (program := program)) (capturePrefix callerPrefix : Nat) :
    ProtectedExpressionMeaning.Entry :=
  fun bodyScope mapping world heap store canonical =>
    Nonempty (SourceEntry code history headers locations capturePrefix callerPrefix bodyScope mapping world heap store canonical)

theorem transport : ProtectedExpressionMeaning.Transport
    (protectedEntry code history headers locations capturePrefix callerPrefix) := by
  constructor
  intro bodyScope mapping world heap store canonical futureMap futureWorld after futureStore entry maps worlds frame metadata
  obtain ⟨entry⟩ := entry
  exact ⟨entry.extend maps worlds frame metadata⟩

theorem binds : ProtectedExpressionMeaning.Binds
    (protectedEntry code history headers locations capturePrefix callerPrefix) := by
  constructor
  · intro bodyScope mapping world heap store canonical id type value entry
    obtain ⟨entry⟩ := entry
    refine ⟨{ catalog := ⟨entry.catalog.authority, ?_⟩
              ghost := entry.ghost, carried := entry.carried, reference := ?_ }⟩
    · intro header member
      have index : ((id, type) :: bodyScope).length + callerPrefix + header.slot =
          (bodyScope.length + callerPrefix + header.slot) + 1 := by simp only [List.length_cons]; omega
      simpa only [index, List.getElem?_cons_succ] using entry.catalog.globals header member
    · have index : ((id, type) :: bodyScope).length + 1 + prepared.base.globals.length =
          (bodyScope.length + 1 + prepared.base.globals.length) + 1 := by simp only [List.length_cons]; omega
      simpa only [index, List.getElem?_cons_succ] using entry.reference
  · intro bodyScope mapping world heap store canonical id type value entry
    obtain ⟨entry⟩ := entry
    refine ⟨{ catalog := ⟨entry.catalog.authority, ?_⟩
              ghost := entry.ghost, carried := entry.carried, reference := ?_ }⟩
    · intro header member
      have found := entry.catalog.globals header member
      have index : ((id, type) :: bodyScope).length + callerPrefix + header.slot =
          (bodyScope.length + callerPrefix + header.slot) + 1 := by simp only [List.length_cons]; omega
      simpa only [index, List.getElem?_cons_succ] using found
    · have found := entry.reference
      have index : ((id, type) :: bodyScope).length + 1 + prepared.base.globals.length =
          (bodyScope.length + 1 + prepared.base.globals.length) + 1 := by simp only [List.length_cons]; omega
      simpa only [index, List.getElem?_cons_succ] using found

section ActualEntry
variable {mapping : LocationMap} {world : StoreTyping} {capturedActual : Environment}
  {captured : Captures prepared mapping world scope function.captured capturedActual}
  {code : Code prepared function scope captured.administrative} {history : History code}
  {inputs : CallableIndexedLambdaEntryPrefix.Context code}
  {functions : FunctionModel values.checked.catalog (CallableIndexedAmbient.ambientDefinitions prepared)}
  {registry : SourceCoreRawMetadata.Registry} {arguments : List Dynamic.Value} {nativeArguments : List Value}
  {before : Dynamic.Heap} {store : Store} {location : Location} {current : NativeFrame} {currentGhost : GhostFrame}
  (entry : CallableIndexedLambdaEntryPrefix.EntryFor captured code history inputs functions registry arguments nativeArguments before store location current currentGhost)
  (initial : RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix scope mapping world before store captured.canonical)
  (sameFrame : initial.authority.frameLocation = location)
  {added : Environment} (length : added.length = code.receipt.loweredParameters.length)
  (spine : entry.entry.canonical = added ++ captured.canonical)

/-- Unsized prefix construction retains its exact returned entry and spine.
No completion or grade is extracted from its continuation agreement. -/
def catalog_entry : RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix
    (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
    entry.entry.mapping entry.entry.world entry.entry.heap entry.entry.store entry.entry.canonical :=
  catalog_after_prefix initial sameFrame entry.nextHistory entry.entry.maps entry.entry.worlds entry.entry.frame
    entry.entry.metadata ⟨added, length, spine⟩

def source_entry : SourceEntry code history headers locations capturePrefix callerPrefix
    (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
    entry.entry.mapping entry.entry.world entry.entry.heap entry.entry.store entry.entry.canonical :=
  { catalog := catalog_entry entry initial sameFrame length spine
    ghost := rfl
    carried := entry.nextHistory
    reference := by
      change entry.entry.canonical[_]? = some (Value.cellRef prepared.ancestry.layout.frame.type initial.authority.frameLocation)
      simpa only [sameFrame] using entry.entry.reference }

end ActualEntry

section SizedEntry
variable {mapping : LocationMap} {world : StoreTyping} {capturedActual : Environment}
  {captured : Captures prepared mapping world scope function.captured capturedActual}
  {code : Code prepared function scope captured.administrative} {history : History code}
  {inputs : CallableIndexedLambdaEntryPrefix.Context code}
  {functions : FunctionModel values.checked.catalog (CallableIndexedAmbient.ambientDefinitions prepared)}
  {registry : SourceCoreRawMetadata.Registry} {arguments : List Dynamic.Value}
  {before : Dynamic.Heap} {store : Store} {location : Location} {current : NativeFrame}
  (reached : CallableIndexedLambdaEntryBounds.PrefixFor captured code history inputs functions registry arguments before store location current)
  (initial : RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix scope mapping world before store captured.canonical)
  (sameFrame : initial.authority.frameLocation = location)

def catalog_entry_sized : RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix
    (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
    reached.mapping reached.world reached.heap reached.store reached.canonical :=
  catalog_after_prefix initial sameFrame reached.nextHistory reached.maps reached.worlds reached.frame reached.metadata reached.spine

def source_entry_sized : SourceEntry code history headers locations capturePrefix callerPrefix
    (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
    reached.mapping reached.world reached.heap reached.store reached.canonical :=
  { catalog := catalog_entry_sized reached initial sameFrame
    ghost := rfl
    carried := reached.nextHistory
    reference := by
      change reached.canonical[_]? = some (Value.cellRef prepared.ancestry.layout.frame.type initial.authority.frameLocation)
      simpa only [sameFrame] using reached.reference }

end SizedEntry
end Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaCatalogEntries
