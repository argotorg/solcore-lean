import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBodyEntry
import Solcore.SourceSemantics.CoreLowering.CellAwareScopeAuthority

/-! Entering an actual materialized body writes only the unmapped context frame
and appends marked parameters. Both operations retain every generalized row. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBodyEntry
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues SourceCoreCallableIndexedFrames
open GeneralizedLocalDescriptorOrigin

theorem Entry.scope_effect {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
    {descriptor : Dynamic.GeneralizedClosure} {binding : SourceCoreLocalPolymorphism.Binding}
    {lexical : TypeSystem.Substitution} (origin : Origin prepared descriptor binding lexical)
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
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
      origin.ghost caller origin.metadata id code.descriptor.id)
    (entry : Entry origin captured code inputs functions registry cells arguments nativeArguments before store
      location callerNative callerGhost caller id recipe)
    (instances : GeneralizedLocalDescriptorHeap.InstanceModel prepared.layouts.definitions) :
    CellAwareScopeAuthority.Effect instances mapping world before store
      entry.entry.mapping entry.entry.world entry.entry.heap entry.entry.store := by
  obtain ⟨suffix, extended⟩ := entry.entry.storeExtension
  rw [extended]
  exact (CellAwareScopeAuthority.Effect.set_unmapped store
    (encode prepared.ancestry.layout.frame entry.next) entry.unmapped).trans
      (.append _ suffix entry.entry.metadata entry.entry.maps entry.entry.worlds)

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBodyEntry
