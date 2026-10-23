import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBodyEntryEffects
import Solcore.SourceSemantics.CoreLowering.ActualBodyInvocationInputIdentities

/-! A real materialized read enters its stored body using only the input
identities derived from its two actual histories. Captures and the native
frame cell are the same ones retained by the original allocation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalMaterializedBodyEntry
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open GeneralizedLocalAcceptedMaterialization
open CallableIndexedLambdaValues CallableIndexedHistory
open SourceCoreCallableIndexedFrames

theorem entry_exists_with_spine
    {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
    {mapping : LocationMap} {world : StoreTyping} {function : Dynamic.Closure}
    {viewRelation : TypedSource → TypedSource → Prop}
    (material : Materialization compiled mapping world function viewRelation)
    (view : View material)
    (frame : Dynamic.ClosureFrame program function)
    (functions : FunctionModel compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
    {registry : SourceCoreRawMetadata.Registry}
    {cells : GenericHeap.CellModel compiled.indexed.layouts.definitions}
    (ordinaryCells : GenericHeap.OrdinaryCells
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) cells)
    {Records : Type} (protocol : ProtectedStateTransition.Protocol Records)
    (producer : ProtectedStateTransition.CellAllocation.Producer
      (catalog := CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      protocol compiled.indexed.layouts compiled.indexed.ancestry.layout.frame cells)
    {arguments : List Dynamic.Value} {nativeArguments : List Value}
    (represented : CallableIndexedParameterMeaning.Arguments
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      mapping world material.code.receipt.loweredParameters arguments nativeArguments)
    {before : Dynamic.Heap} {store : Store}
    (heaps : GenericHeap.CellHeapRepresents cells mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
    (read : store.read? view.location =
      some (encode compiled.indexed.ancestry.layout.frame view.transient))
    (unmapped : view.location ∉ mapping)
    (initial : protocol.State ⟨material.inputs.scope, mapping, world, before,
      store.set view.location (encode compiled.indexed.ancestry.layout.frame view.selected),
      material.captured.canonical⟩)
    (readyAt : ProtectedStateTransition.CellAllocation.ReadyAt producer view.location view.selected) :
    ∃ inputs : CallableIndexedLambdaEntryPrefix.Context
        (values := .initial compiled.compatible.checked) material.code,
      ∃ entry : GeneralizedLocalBodyEntry.Entry (values := .initial compiled.compatible.checked) material.origin material.captured material.code inputs
        functions registry cells arguments nativeArguments before store view.location
        view.callerNative view.callerGhost view.caller view.id view.recipe,
        ∃ added : Environment, added.length = material.code.receipt.loweredParameters.length ∧
          entry.entry.canonical = added ++ material.captured.canonical ∧
          ProtectedStateTransition.Transition protocol initial
            ⟨material.code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++
                material.inputs.scope,
              entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩ := by
  obtain ⟨inputs⟩ := GeneralizedLocalAcceptedBodyCompiler.entry_context material frame material.ownership
  refine ⟨inputs, ?_⟩
  exact GeneralizedLocalBodyEntry.Stateful.entry_exists_with_spine_of_input_ids
    (values := .initial compiled.compatible.checked)
    material.origin material.captured material.code inputs
    (ActualBodyInvocation.materialized_input_ids material view)
    functions ordinaryCells protocol producer represented view.carried view.recipe heaps locals
    view.lexicalReference read unmapped initial readyAt

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalMaterializedBodyEntry
