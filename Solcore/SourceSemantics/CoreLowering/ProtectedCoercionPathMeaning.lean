import Solcore.SourceSemantics.CoreLowering.CallableCoercionPathMeaning
import Solcore.SourceSemantics.CoreLowering.ProtectedStateTransition

/-! Ordered coercion methods consume the actual reached protocol state.
The original Source/native path folds compose its relation through every
method and keep the final method's actual post, including faults. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedCoercionPathMeaning
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableCoercionPathMeaning
universe v
variable {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{0, v} Records)
  (scope : SourceCoreLocalCell.Scope) (canonical : Environment)

/-- Each actual path state keeps the caller's original scope and captures. -/
abbrev states (mapping : LocationMap) (world : StoreTyping) (heap : Dynamic.Heap) (store : Store) :=
  protocol.State ⟨scope, mapping, world, heap, store, canonical⟩

/-- The relation is the protocol's original relation at the actual indices. -/
def relation : StateRelation (states protocol scope canonical) :=
  fun {_mapping _nextMap _world _nextWorld _before _after _store _finalStore} first last =>
    protocol.Relates first last

variable {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {α : Type} {row : α → Row}
  (functions : FunctionModel values.checked.catalog ambient) (program : Program)
  {caller : Environment} {reason : Word}

/-- The one-method interface retains the actual post and its full relation. -/
abbrev StepPreserves (methods : List α) :=
  StepPreservesForWithState row (states protocol scope canonical) (relation protocol scope canonical)
    functions registry faults program caller reason methods

/-- Native rows retain original completion receipts for their chosen invocation. -/
abbrev StepReflects (invocation : CallableCoercionSpine.Call → Store → Value → Value → Store → Prop)
    (methods : List α) :=
  StepReflectsForWithState row (states protocol scope canonical) (relation protocol scope canonical)
    functions registry faults program invocation methods

/-- The same ordered Source fold forwards every method's real reached state. -/
theorem preserves
    {source target : TypeSystem.Ty} {inputType outputType : Ty} {methods : List α}
    (step : StepPreserves (row := row) (registry := registry) (faults := faults) (caller := caller) (reason := reason)
      protocol scope canonical functions program methods)
    (chain : ChainFor row source inputType methods target outputType)
    {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap} {store : Store}
    {input : Dynamic.Value} {native : Value} {outcome : Dynamic.ExpressionOutcome}
    (entry : states protocol scope canonical mapping world before store)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (represented : ValueRep values.checked registry functions mapping world source input native inputType)
    (trace : SelectedTraceFor row program methods before input outcome after) :
    ∃ value finalStore finalMap finalWorld,
      CallableCoercionSpine.Runs caller reason store (.inRight .word native) (methods.map (fun method => (row method).call)) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        target outputType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition protocol entry
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  exact preserves_for_with_state (functions := functions)
    (relation := relation protocol scope canonical)
    (fun state => protocol.refl state) (fun first second => protocol.trans first second)
    step chain entry heaps represented trace

/-- Native completion uses the original path inversion and actual post.
The Source result is independent of the native invocation's measurement. -/
theorem reflects
    {invocation : CallableCoercionSpine.Call → Store → Value → Value → Store → Prop}
    (forget : ∀ {call before input result after}, invocation call before input result after →
      CallableCoercionSpine.Invoke caller reason call before input result after)
    {source target : TypeSystem.Ty} {inputType outputType : Ty} {methods : List α}
    (step : StepReflects (row := row) (registry := registry) (faults := faults)
      protocol scope canonical functions program invocation methods)
    (chain : ChainFor row source inputType methods target outputType)
    {mapping : LocationMap} {world : StoreTyping}
    {before : Dynamic.Heap} {store finalStore : Store} {input : Dynamic.Value} {native value : Value}
    (entry : states protocol scope canonical mapping world before store)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (represented : ValueRep values.checked registry functions mapping world source input native inputType)
    (runs : CallableCoercionSpine.RunsFor invocation store (.inRight .word native) (methods.map (fun method => (row method).call)) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      SelectedTraceFor row program methods before input outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        target outputType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition protocol entry
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  exact reflects_for_with_state (functions := functions)
    (relation := relation protocol scope canonical) forget
    (fun state => protocol.refl state) (fun first second => protocol.trans first second)
    step chain entry heaps represented runs

end Solcore.SourceSemantics.CoreLowering.ProtectedCoercionPathMeaning
