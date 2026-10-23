import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalCallFrame
import Solcore.SourceSemantics.CoreLowering.CellAwareLambdaViewPrefix
import Solcore.SourceSemantics.CoreLowering.CellAwareBodyFrames

/-! The actual materialized closure enters its emitted body through the retained
lexical snapshot, the read recipe, the manifest, and the marked parameter fold.
Every source cell uses the same relation throughout the prefix. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBodyEntry
open Core Frontend SourceInference GeneralHeap ReadOnly CoreProof CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues SourceCoreCallableIndexedFrames
open CallableIndexedLambdaEntryPrefix (parameters prefix_accepted bodyEmbedding)
open CallableIndexedParameterCertificates CallableIndexedParameterMeaning
open GeneralizedLocalDescriptorOrigin

private theorem body_agrees {canonical actual : Environment} {embedding : Renaming}
    (agrees : EnvironmentsAgree embedding canonical actual) (argument lexical saved : Value) :
    EnvironmentsAgree (bodyEmbedding embedding) (argument :: canonical)
      (.unit :: saved :: argument :: lexical :: actual) := by
  intro index value found
  cases index with
  | zero => exact found
  | succ index => exact agrees found

private theorem reference_typed {definitions : DataEnvironment} {world : StoreTyping}
    {environment : Environment} {context : Core.Context} {index location : Nat} {type : Ty}
    (typed : RuntimeEnvironmentHasTypes world environment context definitions)
    (found : environment[index]? = some (.cellRef type location)) : world[location]? = some type := by
  have atType : context[index]? = some (.cell type) := by
    rw [← typed.type_tags]
    simp [List.getElem?_map, found, Value.type]
  obtain ⟨value, selected, related⟩ := typed.lookup atType
  have same := Option.some.inj (selected.symm.trans found)
  subst value
  cases related with | cellRef typed => exact typed

structure Entry {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
    {descriptor : Dynamic.GeneralizedClosure} {binding : SourceCoreLocalPolymorphism.Binding}
    {lexical : TypeSystem.Substitution} (origin : Origin prepared descriptor binding lexical)
    {function : Dynamic.Closure} {scope : Scope} {mapping : LocationMap} {world : StoreTyping}
    {capturedActual : Environment}
    (captured : Captures prepared mapping world scope function.captured capturedActual)
    {viewRelation : TypedSource → TypedSource → Prop}
    (code : Code prepared function scope captured.administrative viewRelation) (inputs : CallableIndexedLambdaEntryPrefix.Context code)
    (functions : FunctionModel values.checked.catalog (CallableIndexedAmbient.ambientDefinitions prepared))
    (registry : SourceCoreRawMetadata.Registry)
    (cells : GenericHeap.CellModel prepared.layouts.definitions)
    (arguments : List Dynamic.Value) (nativeArguments : List Value)
    (before : Dynamic.Heap) (store : Store) (location : Location)
    (callerNative : NativeFrame) (callerGhost : GhostFrame) (caller : MetadataState) (id : Word)
    (recipe : CallableAppliedViewProvenance.Recipe prepared.ancestry.graph.inputs callerGhost
      origin.ghost caller origin.metadata id code.descriptor.id) where private mk ::
  next : NativeFrame
  nextHistory : Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table next
    (.appliedView id code.descriptor.id callerGhost origin.ghost) (some (recipe.read.after origin.metadata))
  actual : Environment
  actualContext : Core.Context
  embedding : Renaming
  entry : CellAwareLambdaViewPrefix.Entry prepared.ancestry.layout.frame prepared.base.globals.length
    location next values functions registry cells function inputs.context scope code.receipt.loweredParameters
    arguments before (store.set location (encode prepared.ancestry.layout.frame next)) mapping world
    captured.administrative actualContext actual embedding code.receipt.allocatedBody code.receipt.body
  wrap : ∀ {result bodyStore}, Evaluates entry.actualBody entry.store
      (code.receipt.body.rename entry.embedding) result bodyStore →
    Evaluates (DataPatternValues.packValues nativeArguments :: encode prepared.ancestry.layout.frame origin.native :: capturedActual)
      store (code.body.rename captured.embedding.lift.lift) result
      (bodyStore.set location (encode prepared.ancestry.layout.frame
        (SourceCoreCallableIndexedDispatch.readFrame id code.descriptor.id callerNative)))
  unwrap : ∀ {result finalStore},
    Evaluates (DataPatternValues.packValues nativeArguments :: encode prepared.ancestry.layout.frame origin.native :: capturedActual)
      store (code.body.rename captured.embedding.lift.lift) result finalStore →
    ∃ bodyStore, Evaluates entry.actualBody entry.store (code.receipt.body.rename entry.embedding) result bodyStore ∧
      finalStore = bodyStore.set location (encode prepared.ancestry.layout.frame
        (SourceCoreCallableIndexedDispatch.readFrame id code.descriptor.id callerNative))
  unmapped : location ∉ mapping
  referenceTyped : world[location]? = some prepared.ancestry.layout.frame.type
  currentRead : store.read? location = some (encode prepared.ancestry.layout.frame
    (SourceCoreCallableIndexedDispatch.readFrame id code.descriptor.id callerNative))

namespace Stateful

theorem entry_exists_with_spine_of_input_ids {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
    {descriptor : Dynamic.GeneralizedClosure} {binding : SourceCoreLocalPolymorphism.Binding}
    {lexical : TypeSystem.Substitution} (origin : Origin prepared descriptor binding lexical)
    {function : Dynamic.Closure} {scope : Scope} {mapping : LocationMap} {world : StoreTyping}
    {capturedActual : Environment}
    (captured : Captures prepared mapping world scope function.captured capturedActual)
    {viewRelation : TypedSource → TypedSource → Prop}
    (code : Code prepared function scope captured.administrative viewRelation) (inputs : CallableIndexedLambdaEntryPrefix.Context code)
    (inputIds : function.source.inputs.map TypedBinder.id = code.view.inputs.map TypedBinder.id)
    (functions : FunctionModel values.checked.catalog (CallableIndexedAmbient.ambientDefinitions prepared))
    {registry : SourceCoreRawMetadata.Registry} {cells : GenericHeap.CellModel prepared.layouts.definitions}
    (ordinaryCells : GenericHeap.OrdinaryCells
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) cells)
    {Records : Type} (protocol : ProtectedStateTransition.Protocol Records)
    (producer : ProtectedStateTransition.CellAllocation.Producer
      (catalog := CompatibleEquality.storageCatalog values.checked.catalog) protocol prepared.layouts
      prepared.ancestry.layout.frame cells)
    {arguments : List Dynamic.Value} {nativeArguments : List Value}
    (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      mapping world code.receipt.loweredParameters arguments nativeArguments)
    {before : Dynamic.Heap} {store : Store} {location : Location}
    {callerNative : NativeFrame} {callerGhost : GhostFrame} {caller : MetadataState} {id : Word}
    (callerCarried : Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table
      callerNative callerGhost (some caller))
    (recipe : CallableAppliedViewProvenance.Recipe prepared.ancestry.graph.inputs callerGhost
      origin.ghost caller origin.metadata id code.descriptor.id)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
    (reference : captured.canonical[code.referenceIndex]? = some (.cellRef prepared.ancestry.layout.frame.type location))
    (read : store.read? location = some (encode prepared.ancestry.layout.frame
      (SourceCoreCallableIndexedDispatch.readFrame id code.descriptor.id callerNative)))
    (unmapped : location ∉ mapping)
    (initial : protocol.State ⟨scope, mapping, world, before,
      store.set location (encode prepared.ancestry.layout.frame
        (SourceCoreCallableIndexedDispatch.selectedFrame prepared.ancestry.graph.table code.descriptor.id origin.native
          (SourceCoreCallableIndexedDispatch.readFrame id code.descriptor.id callerNative))), captured.canonical⟩)
    (readyAt : ProtectedStateTransition.CellAllocation.ReadyAt producer location
      (SourceCoreCallableIndexedDispatch.selectedFrame prepared.ancestry.graph.table code.descriptor.id origin.native
        (SourceCoreCallableIndexedDispatch.readFrame id code.descriptor.id callerNative))) :
    ∃ entry : Entry origin captured code inputs functions registry cells arguments nativeArguments before store
      location callerNative callerGhost caller id recipe,
      ∃ added : Environment, added.length = code.receipt.loweredParameters.length ∧
        entry.entry.canonical = added ++ captured.canonical ∧
        ProtectedStateTransition.Transition protocol initial
          ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
            entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩ := by
  let layout := prepared.ancestry.layout.frame
  let argument := DataPatternValues.packValues nativeArguments
  let current := SourceCoreCallableIndexedDispatch.readFrame id code.descriptor.id callerNative
  let saved := encode layout current
  let lexicalValue := encode layout origin.native
  let next := SourceCoreCallableIndexedDispatch.selectedFrame prepared.ancestry.graph.table code.descriptor.id origin.native current
  have registered := CallableIndexedAmbient.frame_registered prepared
  have nextHistory := GeneralizedLocalCallPrefix.applied_history origin callerCarried recipe
  have refTyped := reference_typed captured.represented.runtime_hasTypes reference
  have written : store.write? location (encode layout next) = some (store.set location (encode layout next)) :=
    Store.write?_eq_some_iff.mpr ⟨(List.getElem?_eq_some_iff.mp read).1, rfl⟩
  have installedHeaps := heaps.write_administrative
    (fun found => unmapped (List.mem_of_getElem? found)) refTyped
    (encode_runtime_typed world registered next) written
  have installedRead := Store.write?_reads_written written
  have hook := code.receipt.bodyHook
  rw [code.manifest] at hook
  obtain ⟨manifestDescriptor, fields, emitted⟩ := CallableIndexedLambdaManifest.of_hook hook
  let actual := .unit :: saved :: argument :: lexicalValue :: capturedActual
  have actualLayout : EnvironmentsAgree (bodyEmbedding captured.embedding) (argument :: captured.canonical) actual :=
    body_agrees captured.agrees argument lexicalValue saved
  have actualTyped : RuntimeEnvironmentHasTypes world actual
      (.unit :: layout.type :: SourceCoreCompatibleCatalog.packTypes (code.receipt.loweredParameters.map Prod.snd) ::
        layout.type :: captured.actualContext) prepared.layouts.definitions :=
    .cons .unit (.cons (encode_runtime_typed world registered current)
      (.cons (CallableIndexedParameters.Arguments.pack_typed represented)
        (.cons (encode_runtime_typed world registered origin.native) captured.typed)))
  obtain ⟨manifest, manifestTyped, manifestAgreement⟩ := CallableIndexedLambdaManifest.agreement
    captured.represented actualLayout manifestDescriptor fields code.receipt.allocatedBody
      (store.set location (encode layout next))
  obtain ⟨entry, added, prefixLength, canonicalEq, transition⟩ :=
    CellAwareLambdaViewPrefix.Stateful.entry_of_accepted_with_spine_of_input_ids functions ordinaryCells code.allocationError
      protocol producer inputIds (prefix_accepted code) (parameters code) inputs.kinds inputs.extended
      rfl registered represented captured.represented installedHeaps locals
      (GenericExpressionMeaning.agree_prefix actualLayout manifest) (.cons manifestTyped actualTyped)
      (inputs.referenceIndex ▸ reference) installedRead unmapped initial readyAt
  have agreement : ContinuationAgreement actual (store.set location (encode layout next))
      (code.receipt.rawBody.rename (bodyEmbedding captured.embedding)) entry.actualBody entry.store
      (code.receipt.body.rename entry.embedding) := by
    rw [emitted]
    exact manifestAgreement.trans entry.agreement
  have frame := GeneralizedLocalCallFrame.agreement origin captured code callerCarried recipe
    (argument := argument) reference read
  exact ⟨⟨next, nextHistory, _, _, _, entry,
    fun evaluated => frame.1 (agreement.wrap evaluated),
    fun evaluated => by
      obtain ⟨bodyStore, bodyEval, finalEq⟩ := frame.2 evaluated
      exact ⟨bodyStore, agreement.unwrap bodyEval, finalEq⟩,
    unmapped, refTyped, read⟩, added, prefixLength, canonicalEq, transition⟩

/-- Compatibility with full-table view evidence. -/
theorem entry_exists_with_spine {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
    {descriptor : Dynamic.GeneralizedClosure} {binding : SourceCoreLocalPolymorphism.Binding}
    {lexical : TypeSystem.Substitution} (origin : Origin prepared descriptor binding lexical)
    {function : Dynamic.Closure} {scope : Scope} {mapping : LocationMap} {world : StoreTyping}
    {capturedActual : Environment}
    (captured : Captures prepared mapping world scope function.captured capturedActual)
    (code : Code prepared function scope captured.administrative) (inputs : CallableIndexedLambdaEntryPrefix.Context code)
    (functions : FunctionModel values.checked.catalog (CallableIndexedAmbient.ambientDefinitions prepared))
    {registry : SourceCoreRawMetadata.Registry} {cells : GenericHeap.CellModel prepared.layouts.definitions}
    (ordinaryCells : GenericHeap.OrdinaryCells
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) cells)
    {Records : Type} (protocol : ProtectedStateTransition.Protocol Records)
    (producer : ProtectedStateTransition.CellAllocation.Producer
      (catalog := CompatibleEquality.storageCatalog values.checked.catalog) protocol prepared.layouts
      prepared.ancestry.layout.frame cells)
    {arguments : List Dynamic.Value} {nativeArguments : List Value}
    (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      mapping world code.receipt.loweredParameters arguments nativeArguments)
    {before : Dynamic.Heap} {store : Store} {location : Location}
    {callerNative : NativeFrame} {callerGhost : GhostFrame} {caller : MetadataState} {id : Word}
    (callerCarried : Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table
      callerNative callerGhost (some caller))
    (recipe : CallableAppliedViewProvenance.Recipe prepared.ancestry.graph.inputs callerGhost
      origin.ghost caller origin.metadata id code.descriptor.id)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
    (reference : captured.canonical[code.referenceIndex]? = some (.cellRef prepared.ancestry.layout.frame.type location))
    (read : store.read? location = some (encode prepared.ancestry.layout.frame
      (SourceCoreCallableIndexedDispatch.readFrame id code.descriptor.id callerNative)))
    (unmapped : location ∉ mapping)
    (initial : protocol.State ⟨scope, mapping, world, before,
      store.set location (encode prepared.ancestry.layout.frame
        (SourceCoreCallableIndexedDispatch.selectedFrame prepared.ancestry.graph.table code.descriptor.id origin.native
          (SourceCoreCallableIndexedDispatch.readFrame id code.descriptor.id callerNative))), captured.canonical⟩)
    (readyAt : ProtectedStateTransition.CellAllocation.ReadyAt producer location
      (SourceCoreCallableIndexedDispatch.selectedFrame prepared.ancestry.graph.table code.descriptor.id origin.native
        (SourceCoreCallableIndexedDispatch.readFrame id code.descriptor.id callerNative))) :
    ∃ entry : Entry origin captured code inputs functions registry cells arguments nativeArguments before store
      location callerNative callerGhost caller id recipe,
      ∃ added : Environment, added.length = code.receipt.loweredParameters.length ∧
        entry.entry.canonical = added ++ captured.canonical ∧
        ProtectedStateTransition.Transition protocol initial
          ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
            entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩ := by
  exact entry_exists_with_spine_of_input_ids origin captured code inputs
    (congrArg (List.map TypedBinder.id) code.viewOfSource.inputs) functions ordinaryCells protocol producer
    represented callerCarried recipe heaps locals reference read unmapped initial readyAt

end Stateful
end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBodyEntry
