import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedBodyCompiler
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalOwnedBodyEntry
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBodyEntryEffects

/-! A materialized general body enters through its actual captured frame and
marked parameter fold. Source typing and the whole compiler receipt refer to
that same closure, including nested declarations and all later statements. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedInvocation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues SourceCoreCallableIndexedFrames
open CallableIndexedOwnedFunctionState CallableIndexedParameterMeaning
open GeneralizedLocalAcceptedMaterialization

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {function : Dynamic.Closure} {mapping : LocationMap} {world : StoreTyping}
  (material : Materialization compiled mapping world function)
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry}
  {arguments : List Dynamic.Value} {nativeArguments : List Value}
  {before : Dynamic.Heap} {store : Store} {callerScope : SourceCoreLocalCell.Scope}
  {callerCanonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (callerState : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (view : View material)

local notation "payload" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions
local notation "instances" => GeneralizedLocalAcceptedInstances.model compiled.indexed
local notation "cells" => GeneralizedLocalDescriptorHeap.cellModel payload instances

/-- The current authority and actual Source frame construct the complete body
entry. No finite body profile, body execution, or future heap is supplied. -/
theorem enters
    (frame : Dynamic.ClosureFrame program function)
    (represented : Arguments payload mapping world material.code.receipt.loweredParameters arguments nativeArguments)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
    (beforeTyped : Dynamic.HeapWellTyped function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes function.context before arguments
      (function.parameters.map (fun binder => binder.scheme.body)))
    (sameLocation : view.location = owner.key.frameLocation)
    (read : store.read? owner.key.frameLocation = some (encode compiled.indexed.ancestry.layout.frame
      (SourceCoreCallableIndexedDispatch.readFrame view.id material.code.descriptor.id view.callerNative))) :
    ∃ inputs : CallableIndexedLambdaEntryPrefix.Context
        (values := .initial compiled.compatible.checked) material.code,
    ∃ entry : GeneralizedLocalBodyEntry.Entry (values := .initial compiled.compatible.checked)
        material.origin material.captured material.code inputs functions registry cells arguments nativeArguments
        before store owner.key.frameLocation view.callerNative view.callerGhost view.caller view.id view.recipe,
      Dynamic.SourceRuntimeValid program inputs.context function.source ∧
      function.evidence.Covers inputs.context ∧
      Dynamic.HeapWellTyped inputs.context entry.entry.heap ∧
      Dynamic.EnvironmentAgrees entry.entry.heap inputs.context.locals entry.entry.environment ∧
      (∃ finalContext facts,
        StatementsHaveType function.source { returnType := function.resultType } inputs.context
          function.body finalContext facts ∧ BodyCompletes function.resultType facts) ∧
      CellAwareScopeAuthority.Effect instances mapping world before store
        entry.entry.mapping entry.entry.world entry.entry.heap entry.entry.store ∧
      (∃ added : Environment, added.length = material.code.receipt.loweredParameters.length ∧
        entry.entry.canonical = added ++ material.captured.canonical ∧
        ProtectedStateTransition.Transition (protocol headers keys) callerState
          ⟨material.code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ material.inputs.scope,
            entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩) := by
  obtain ⟨inputs⟩ := GeneralizedLocalAcceptedBodyCompiler.entry_context material frame material.ownership
  have reference : material.captured.canonical[material.code.referenceIndex]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
    simpa only [sameLocation] using view.lexicalReference
  have ordinaryCells : GenericHeap.OrdinaryCells payload cells :=
    GeneralizedLocalDescriptorHeap.ordinary_cells
  obtain ⟨entry, added, length, spine, transition⟩ :=
    GeneralizedLocalOwnedBodyEntry.parameters_with_state material.origin material.captured material.code inputs
      functions ordinaryCells represented owner callerState view.carried view.recipe heaps locals reference read
  have argumentsTyped : Dynamic.ValuesHaveTypes function.context before arguments inputs.types := by
    simpa only [← Dynamic.MonoBindersExtend.bodyTypes_eq inputs.extended] using argumentsTyped
  obtain ⟨runtime, covers, heapTyped, environmentTyped, bodyTyped⟩ :=
    GeneralizedLocalOwnedBodyEntry.source_admission material.origin material.captured material.code inputs
      functions owner view.recipe entry frame beforeTyped argumentsTyped
  exact ⟨inputs, entry, runtime, covers, heapTyped, environmentTyped, bodyTyped,
    GeneralizedLocalBodyEntry.Entry.scope_effect (values := .initial compiled.compatible.checked) material.origin material.captured material.code inputs functions registry cells
      arguments nativeArguments before store owner.key.frameLocation view.callerNative view.callerGhost
      view.caller view.id view.recipe entry instances, added, length, spine, transition⟩

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedInvocation
