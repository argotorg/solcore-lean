import Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodRuntimeMeaning
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogEntries

/-! Actual method prefixes retain a separately supplied finite catalog. The
marked allocator supplies the exact added cells and packed argument slot; the
real hook supplies its named history. Source method attribution remains a
separate frame receipt, without ordinary function instantiation. No method body
grammar or execution correspondence is required by these catalog transports. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodCatalogEntries
open Core Frontend SourceInference GeneralHeap ReadOnly CoreProof CompatiblePayload
open CallableAncestryPairedLookup CallableIndexedHistory CallableIndexedParameterCertificates CallableIndexedParameterMeaning
open SourceCoreCallableIndexedFrames
open CallablePreparedMethodRuntimeMeaning

variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base}
  {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {program : Program}
  {headers : RecursiveNamedCatalog.Inventory prepared values ambient.definitions program}
  {locations : RecursiveNamedCatalog.Locations (prepared := prepared) (values := values) (ambient := ambient) (program := program)}
  {capturePrefix callerPrefix : Nat}

/-- Source attribution, actual named history, and catalog authority are kept as
independent receipts. The dictionary is the one in the original closure view. -/
structure SourceEntry (named : SourceCoreGeneralFunctions.Function)
    (sourceBody : Dynamic.BodyInstance) (function : Dynamic.Closure)
    (headers : RecursiveNamedCatalog.Inventory prepared values ambient.definitions program)
    (locations : RecursiveNamedCatalog.Locations (prepared := prepared) (values := values) (ambient := ambient) (program := program))
    (capturePrefix callerPrefix : Nat) (scope : SourceCoreLocalCell.Scope)
    (mapping : LocationMap) (world : StoreTyping) (heap : Dynamic.Heap) (store : Store) (canonical : Environment) where
  catalog : RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix scope mapping world heap store canonical
  sourceFrame : CallableCoercionMethodFrame.Frame sourceBody function
  sameSource : sourceBody.source = CallableIndexedNamedGeneration.source named
  origin : Word
  metadata : MetadataState
  owned : prepared.graph.inputs.callable.table.idAt? (.named named.signature.key) = some origin
  ghost : catalog.authority.ghost = .named origin
  carried : Carries prepared.graph.inputs prepared.graph.table catalog.authority.current (.named origin) (some metadata)
  reference : canonical[scope.length + 1 + base.globals.length]? =
    some (.cellRef prepared.layout.frame.type catalog.authority.frameLocation)

variable {named : SourceCoreGeneralFunctions.Function} {sourceBody : Dynamic.BodyInstance} {function : Dynamic.Closure}

def SourceEntry.extend {scope : SourceCoreLocalCell.Scope} {mapping futureMap : LocationMap}
    {world futureWorld : StoreTyping} {heap after : Dynamic.Heap} {store futureStore : Store} {canonical : Environment}
    (entry : SourceEntry named sourceBody function headers locations capturePrefix callerPrefix scope mapping world heap store canonical)
    (maps : LocationMap.Extends mapping futureMap) (worlds : WorldExtends world futureWorld)
    (frame : AdministrativePreserved mapping store futureMap futureStore)
    (metadata : Dynamic.HeapMetadataExtend heap after) :
    SourceEntry named sourceBody function headers locations capturePrefix callerPrefix scope futureMap futureWorld after futureStore canonical :=
  { entry with catalog := entry.catalog.extend maps worlds frame metadata }

def protectedEntry (named : SourceCoreGeneralFunctions.Function) (sourceBody : Dynamic.BodyInstance)
    (function : Dynamic.Closure) (headers : RecursiveNamedCatalog.Inventory prepared values ambient.definitions program)
    (locations : RecursiveNamedCatalog.Locations (prepared := prepared) (values := values) (ambient := ambient) (program := program))
    (capturePrefix callerPrefix : Nat) : ProtectedExpressionMeaning.Entry :=
  fun scope mapping world heap store canonical =>
    Nonempty (SourceEntry named sourceBody function headers locations capturePrefix callerPrefix scope mapping world heap store canonical)

theorem transport : ProtectedExpressionMeaning.Transport
    (protectedEntry named sourceBody function headers locations capturePrefix callerPrefix) := by
  constructor
  intro scope mapping world heap store canonical futureMap futureWorld after futureStore entry maps worlds frame metadata
  obtain ⟨entry⟩ := entry
  exact ⟨entry.extend maps worlds frame metadata⟩

theorem binds : ProtectedExpressionMeaning.Binds
    (protectedEntry named sourceBody function headers locations capturePrefix callerPrefix) := by
  constructor
  all_goals
    intro scope mapping world heap store canonical id type value entry
    obtain ⟨entry⟩ := entry
    refine ⟨{ entry with catalog := ⟨entry.catalog.authority, ?_⟩, reference := ?_ }⟩
    · intro header member
      have index : ((id, type) :: scope).length + callerPrefix + header.slot =
          (scope.length + callerPrefix + header.slot) + 1 := by simp only [List.length_cons]; omega
      simpa only [index, List.getElem?_cons_succ] using entry.catalog.globals header member
    · have index : ((id, type) :: scope).length + 1 + base.globals.length =
          (scope.length + 1 + base.globals.length) + 1 := by simp only [List.length_cons]; omega
      simpa only [index, List.getElem?_cons_succ] using entry.reference

section Effects
variable {bindings : List Binding} {nativeArguments : List Value}
  {mapping prefixMap : LocationMap} {world prefixWorld : StoreTyping}
  {before prefixHeap : Dynamic.Heap} {store prefixStore : Store}
  {canonical prefixCanonical added : Environment} {location : Location} {next : NativeFrame}
  (initial : RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix [] mapping world before store canonical)
  (sameFrame : initial.authority.frameLocation = location)
  (maps : LocationMap.Extends mapping prefixMap) (worlds : WorldExtends world prefixWorld)
  (frame : AdministrativePreserved mapping (store.set location (encode prepared.layout.frame next)) prefixMap prefixStore)
  (metadata : Dynamic.HeapMetadataExtend before prefixHeap)
  (length : added.length = bindings.length)
  (spine : prefixCanonical = added ++ DataPatternValues.packValues nativeArguments :: canonical)

/-- Actual installation and prefix effects suffice before any body completion.
The ordered spine retains the packed slot and every original catalog row. -/
def catalog_entry_of_effects {nextGhost : GhostFrame}
    (history : Current prepared.graph.inputs prepared.graph.table next nextGhost) :
    RecursiveNamedCatalog.Entry headers locations capturePrefix (callerPrefix + 1)
      (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) prefixMap prefixWorld
      prefixHeap prefixStore prefixCanonical := by
  let installed := initial.authority.install history
  have effects : AdministrativePreserved mapping
      (store.set initial.authority.frameLocation (encode prepared.layout.frame next)) prefixMap prefixStore := by
    simpa only [sameFrame] using frame
  refine ⟨installed.extend maps worlds effects metadata, ?_⟩
  intro header member
  rw [spine]
  simp only [List.length_map, List.length_reverse]
  have index : bindings.length + (callerPrefix + 1) + header.slot =
      added.length + (callerPrefix + header.slot + 1) := by omega
  rw [index, List.getElem?_append_right (by omega)]
  simpa only [Nat.add_sub_cancel_left, List.getElem?_cons_succ, List.length_nil, Nat.zero_add]
    using initial.globals header member

/-- Source attribution and actual carried history remain separate inputs.
No native evaluation or type creates the source method frame. -/
def source_entry_of_effects {origin : Word} {state : MetadataState}
    (reference : prefixCanonical[(bindings.reverse.map (fun binding => (binding.1.id, binding.2))).length + 1 + base.globals.length]? =
      some (.cellRef prepared.layout.frame.type location))
    (owned : prepared.graph.inputs.callable.table.idAt? (.named named.signature.key) = some origin)
    (history : Carries prepared.graph.inputs prepared.graph.table next (.named origin) (some state))
    (sourceFrame : CallableCoercionMethodFrame.Frame sourceBody function)
    (sameSource : sourceBody.source = CallableIndexedNamedGeneration.source named) :
    SourceEntry named sourceBody function headers locations capturePrefix (callerPrefix + 1)
      (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) prefixMap prefixWorld
      prefixHeap prefixStore prefixCanonical :=
  { catalog := catalog_entry_of_effects initial sameFrame maps worlds frame metadata length spine (.stable history)
    sourceFrame, sameSource, origin, metadata := state, owned
    ghost := rfl
    carried := history
    reference := by
      change prefixCanonical[_]? = some (Value.cellRef prepared.layout.frame.type initial.authority.frameLocation)
      simpa only [sameFrame] using reference }
end Effects

section Prefix
variable {functions : FunctionModel values.checked.catalog ambient} {registry : SourceCoreRawMetadata.Registry}
  {context : SourceSemantics.Context} {bindings : List Binding} {arguments : List Dynamic.Value}
  {nativeArguments : List Value} {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {administrative actualContext : Core.Context} {canonical actual : Environment} {ξ : Renaming}
  {parameterCode body : Expr} {size : Nat} {result : Value} {bodyStore : Store}
  {location : Location} {next : NativeFrame}
  (reached : Prefix prepared.layout.frame base.globals.length location next values functions registry function context bindings
    arguments before (store.set location (encode prepared.layout.frame next)) mapping world administrative actualContext
    actual ξ parameterCode body size result bodyStore)
  (initial : RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix [] mapping world before store canonical)
  (sameFrame : initial.authority.frameLocation = location)
  {added : Environment} (length : added.length = bindings.length)
  (spine : reached.canonical = added ++ DataPatternValues.packValues nativeArguments :: canonical)

/-- Installation and the original prefix effects preserve every catalog row.
The extra packed-argument slot increases only the caller offset. -/
def catalog_entry {nextGhost : GhostFrame}
    (history : Current prepared.graph.inputs prepared.graph.table next nextGhost) :
    RecursiveNamedCatalog.Entry headers locations capturePrefix (callerPrefix + 1)
      (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) reached.mapping reached.world
      reached.heap reached.store reached.canonical :=
  catalog_entry_of_effects initial sameFrame reached.maps reached.worlds reached.frame reached.metadata length spine history

/-- The actual hook's owned key and complete history are joined to the
independent trait-method frame. The source dictionary is never reconstructed. -/
def source_entry {origin : Word} {metadata : MetadataState}
    (owned : prepared.graph.inputs.callable.table.idAt? (.named named.signature.key) = some origin)
    (history : Carries prepared.graph.inputs prepared.graph.table next (.named origin) (some metadata))
    (sourceFrame : CallableCoercionMethodFrame.Frame sourceBody function)
    (sameSource : sourceBody.source = CallableIndexedNamedGeneration.source named) :
    SourceEntry named sourceBody function headers locations capturePrefix (callerPrefix + 1)
      (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) reached.mapping reached.world
      reached.heap reached.store reached.canonical :=
  source_entry_of_effects initial sameFrame reached.maps reached.worlds reached.frame reached.metadata length spine
    reached.reference owned history sourceFrame sameSource

include initial sameFrame in
/-- Body effects restore the original caller catalog, including its complete
captures and protected snapshots. No body evaluation or source trace is added. -/
theorem restore_catalog {current : NativeFrame} {currentGhost : GhostFrame}
    (caller : CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location current currentGhost store)
    (registered : prepared.layout.frame.Registered ambient.definitions)
    {finalMap : LocationMap} {finalWorld : StoreTyping} {after : Dynamic.Heap} {finalBodyStore : Store}
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalBodyStore)
    (maps : LocationMap.Extends reached.mapping finalMap) (worlds : WorldExtends reached.world finalWorld)
    (frame : AdministrativePreserved reached.mapping reached.store finalMap finalBodyStore)
    (metadata : Dynamic.HeapMetadataExtend reached.heap after) :
    CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after
      (finalBodyStore.set location (encode prepared.layout.frame current)) ∧
    Nonempty (RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix [] finalMap finalWorld after
      (finalBodyStore.set location (encode prepared.layout.frame current)) canonical) ∧
    AdministrativePreserved mapping store finalMap (finalBodyStore.set location (encode prepared.layout.frame current)) ∧
    CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location current currentGhost
      (finalBodyStore.set location (encode prepared.layout.frame current)) := by
  have unmapped : location ∉ mapping := sameFrame ▸ initial.authority.unmapped
  have typed : world[location]? = some prepared.layout.frame.type := sameFrame ▸ initial.authority.typed
  obtain ⟨finalHeaps, restoredFrame, finalCaller⟩ := CallableIndexedBodyFrames.restore registered unmapped typed caller
    heaps (reached.worlds.trans worlds) (reached.frame.trans frame)
  exact ⟨finalHeaps, ⟨initial.extend (reached.maps.trans maps) (reached.worlds.trans worlds) restoredFrame
    (reached.metadata.trans metadata)⟩, restoredFrame, finalCaller⟩

end Prefix
section ActualHook
variable (functions : CompatiblePayload.FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {function : Dynamic.Closure} {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {readFuel : Nat} {bindings : List Binding} {output : Ty} {policy : SourceCoreLoops.Policy}
  {fuel : Nat} {fellThrough escaped : Word} {body parameterCode : Expr}
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution}
  (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
  (parameters : function.parameters = bindings.map Prod.fst)
  (inputs : function.source.inputs = bindings.map Prod.fst)
  (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
  (unique : NodeOccurrencesUnique function.source) {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, CompatiblePayload.MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (acceptedPrefix : SourceCoreSourceCells.bindParameters
    (SourceCoreCallableIndexedAllocationFrames.allocator prepared.layout.frame base.globals.length
      (layouts.allocatorAt owner active onError)) function.source [] bindings output
    SourceCoreFunctions.argumentProjection body = .ok parameterCode)
  (definitions : layouts.definitions = ambient.definitions) (registered : prepared.layout.frame.Registered ambient.definitions)
  {named : SourceCoreGeneralFunctions.Function} {code : Expr} {ξ : Renaming}
  (acceptedHook : SourceCoreCallableIndexedAncestry.namedBody prepared named parameterCode = .ok code)
  {mapping : LocationMap} {world : StoreTyping} {arguments : List Dynamic.Value} {nativeArguments : List Value}
  (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    mapping world bindings arguments nativeArguments)
  {administrative actualContext : Core.Context} {canonical actual : Environment} {before : Dynamic.Heap} {store : Store}
  {location : Location} {current : NativeFrame} {currentGhost : GhostFrame}
  {records : List CallableIndexedSnapshots.Record}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
    administrative [] [] canonical ambient.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
  (initialLocals : Dynamic.EnvironmentAgrees before function.context.locals [])
  (actualLayout : EnvironmentsAgree ξ (DataPatternValues.packValues nativeArguments :: canonical) actual)
  (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
  (canonicalReference : canonical[base.globals.length]? = some (.cellRef prepared.layout.frame.type location))
  (actualReference : actual[ξ (base.globals.length + 1)]? = some (.cellRef prepared.layout.frame.type location))
  (unmapped : location ∉ mapping) (typed : world[location]? = some prepared.layout.frame.type)
  (caller : CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location current currentGhost store)
  (snapshots : CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame mapping store records)


include parameters inputs extended acceptedPrefix definitions registered represented environments heaps initialLocals
  actualLayout canonicalReference actualReference unmapped typed caller acceptedHook actualTyped in
/-- The original completed hook supplies the measured prefix, its exact
packed-argument spine and the catalog at that same body state. Source method
attribution is supplied independently of native history and typing. -/
theorem hook_catalog_entry
    (sourceFrame : CallableCoercionMethodFrame.Frame sourceBody function)
    (sameSource : sourceBody.source = CallableIndexedNamedGeneration.source named)
    (initial : RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix [] mapping world before store canonical)
    (sameFrame : initial.authority.frameLocation = location)
    {size : Nat} {value : Value} {finalStore : Store}
    (evaluation : EvaluationSize size actual store (code.rename ξ) value finalStore) :
    ∃ index bodyStore prefixSize,
      prefixSize < size ∧ finalStore = bodyStore.set location (encode prepared.layout.frame current) ∧
      ∃ entry : Prefix prepared.layout.frame base.globals.length location (.state index) values functions registry
        function context bindings arguments before (store.set location (encode prepared.layout.frame (.state index))) mapping world
        administrative (.unit :: prepared.layout.frame.type :: actualContext)
        (.unit :: encode prepared.layout.frame current :: actual)
        (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ))
        parameterCode body prefixSize value bodyStore,
        entry.childSize < size ∧
        (∃ added : Environment, added.length = bindings.length ∧
          entry.canonical = added ++ DataPatternValues.packValues nativeArguments :: canonical) ∧
        Nonempty (SourceEntry named sourceBody function headers locations capturePrefix (callerPrefix + 1)
          (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) entry.mapping entry.world
          entry.heap entry.store entry.canonical) := by
  obtain ⟨origin, index, metadata, bodyStore, prefixSize, owned, history, smaller, finalEq, entry, added, length, spine⟩ :=
    hook_prefix_with_spine (prepared := prepared) (functions := functions) (onError := onError)
      (parameters := parameters) (inputs := inputs) (extended := extended) (acceptedPrefix := acceptedPrefix)
      (definitions := definitions) (registered := registered) (acceptedHook := acceptedHook)
      (represented := represented) (environments := environments) (heaps := heaps) (initialLocals := initialLocals)
      (actualLayout := actualLayout) (actualTyped := actualTyped) (canonicalReference := canonicalReference)
      (actualReference := actualReference) (unmapped := unmapped) (typed := typed) (caller := caller) evaluation
  exact ⟨index, bodyStore, prefixSize, smaller, finalEq, entry, Nat.lt_of_le_of_lt entry.bounded smaller,
    ⟨added, length, spine⟩, ⟨source_entry entry initial sameFrame length spine owned history sourceFrame sameSource⟩⟩

end ActualHook

end Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodCatalogEntries
