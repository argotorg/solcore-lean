import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedNamedExpressionHeads
import Solcore.Test.SourceCoreClosedOwnedExpressionHead

/-! A genuine named parameter receipt constructs the exact pointwise body
callback. Its closed static profile uses no expression leaves; the original
shared mutual proof and real nested allocation producer retain the actual
parameter pool, Source exit, and independently measured native completion. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Tests.SourceCoreClosedAdmittedNamedReceipt
open Solcore Core Frontend SourceInference
open SourceSemantics SourceSemantics.CoreLowering GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState ProtectedStateTransition
open Tests.SourceCoreClosedOwnedLexicalBody (noExpressions noExpressionSyntax reached_pool_observations)
open Tests.SourceCoreClosedOwnedExpressionHead (PreparedReceipts layouts PoolObservations)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)

/-- The full original named static profile, real Source parameter judgments,
hook history and actual parameter pool are retained together. -/
abbrev Receipt {index : Index} (argumentsPool : State headers keys index)
    (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
    (arguments : List Dynamic.Value) :=
  CallableIndexedOwnedAdmittedNamedExpressionHeads.ParameterReceipt
    (owner := owner) (functions := functions) (registry := registry) (faults := faults)
    (certificates := fun _ => noExpressions) (expressionSyntax := fun _ => noExpressionSyntax)
    (diagnosticPolicy := .reachable) (runtime := true) argumentsPool header arguments

variable {index : Index} {argumentsPool : State headers keys index}
  {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  {arguments : List Dynamic.Value}
  (receipt : Receipt (registry := registry) (faults := faults) functions owner argumentsPool header arguments)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (prepared : PreparedReceipts (headers := headers)) (member : header ∈ headers)
  (captureZero : owner.key.capturePrefix = 0)
  (globals : header.globals = compiled.indexed.base.globals.length)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)

private def marked : MarkedAllocation.Producer
    (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner header)
    header.layouts compiled.indexed.ancestry.layout.frame
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) :=
  (layouts prepared member).symm ▸ CallableIndexedOwnedNestedCanonicalState.markedProducer owner header
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)

private theorem ready_layout {first second : SourceCoreAllocationLayouts.Prepared}
    (same : first = second)
    (producer : MarkedAllocation.Producer
      (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner header)
      second compiled.indexed.ancestry.layout.frame
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions))
    {location : Location} {native : NativeFrame}
    (ready : OrdinaryAllocation.ReadyAt producer.toOrdinary location native) :
    OrdinaryAllocation.ReadyAt ((same.symm ▸ producer).toOrdinary) location native := by
  cases same
  exact ready

private theorem acquire (location : Location) (native : NativeFrame)
    (stable : CallableIndexedOwnedAllocationProducer.StableOwner keys location native) :
    OrdinaryAllocation.ReadyAt (marked (registry := registry) functions owner prepared member).toOrdinary location native :=
  ready_layout (registry := registry) functions owner (layouts prepared member)
    (CallableIndexedOwnedNestedCanonicalState.markedProducer owner header
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions))
    (CallableIndexedOwnedNestedCanonicalState.readyAt_of_stableOwner owner header
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) stable)

include wellFormed prepared member extension faithful observations in
/-- The same existing mutual proof closes this real named origin internally.
The nested wrapper uses its actual catalog slots and authenticated hook seed. -/
theorem nested_preserves (size : Nat) :
    CallableRuntimeBodyEntryContracts.PreservesAt (registry := registry) (faults := faults) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) functions (Program.ofChecked compiled.sourceProgram)
      (receipt.nested_entry wellFormed captureZero globals).original size := by
  have meaning := CallableRuntimeBodyMutualMeaning.Stateful.preserves_at
    (fun (_ : Unit) => CallableRuntimeBodyStaticOrigins.named true receipt.profile receipt.escaped)
    functions extension (Program.ofChecked compiled.sourceProgram) faithful observations
    (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner header)
    (fun _ => CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (fun _ => marked (registry := registry) functions owner prepared member)
    (fun _ => acquire (registry := registry) functions owner prepared member)
    (CallableIndexedOwnedNestedCanonicalState.administrativeTransport owner header)
    (CallableIndexedOwnedNestedCanonicalState.bindings owner header)
    (by intro _ context valid budget child within below scope id lowered impossible; cases impossible)
    size ()
  intro outcome after trace
  exact meaning (receipt.nested_entry wellFormed captureZero globals).original trace

include wellFormed prepared member extension faithful observations functionTypes in
/-- Native reflection keeps its original completion size and independently
returns a Source body grade at the exact same wrapped parameter entry. -/
theorem nested_reflects (size : Nat) :
    CallableRuntimeBodyEntryContracts.ReflectsAt (registry := registry) (faults := faults) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) functions (Program.ofChecked compiled.sourceProgram)
      (receipt.nested_entry wellFormed captureZero globals).original size := by
  have meaning := CallableRuntimeBodyMutualMeaning.Stateful.reflects_at
    (fun (_ : Unit) => CallableRuntimeBodyStaticOrigins.named true receipt.profile receipt.escaped)
    functions extension (Program.ofChecked compiled.sourceProgram) faithful observations functionTypes
    (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner header)
    (fun _ => CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (fun _ => marked (registry := registry) functions owner prepared member)
    (fun _ => acquire (registry := registry) functions owner prepared member)
    (CallableIndexedOwnedNestedCanonicalState.administrativeTransport owner header)
    (CallableIndexedOwnedNestedCanonicalState.bindings owner header)
    (by intro _ context valid budget child within below scope id lowered impossible; cases impossible)
    size ()
  intro value finalStore completed
  exact meaning (receipt.nested_entry wellFormed captureZero globals).original completed

include wellFormed prepared member captureZero globals extension faithful observations in
/-- This is exactly the revised Source callback target, including ReachedExit.
Only the nested proof is forgotten beside the same actual returned pool. -/
theorem parameter_preserves (size : Nat) :
    CallableRuntimeBodyEntryContracts.PreservesAt (registry := registry) (faults := faults) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) functions (Program.ofChecked compiled.sourceProgram)
      (receipt.admitted_entry wellFormed).original size :=
  CallableIndexedOwnedBodyNestedEntries.preserves_of_nested functions owner header
    (receipt.admitted_entry wellFormed).original (receipt.packet captureZero globals)
    (nested_preserves functions owner receipt wellFormed prepared member captureZero globals extension faithful observations size)

include wellFormed prepared member captureZero globals extension faithful observations functionTypes in
/-- This is exactly the revised native callback target with its actual post. -/
theorem parameter_reflects (size : Nat) :
    CallableRuntimeBodyEntryContracts.ReflectsAt (registry := registry) (faults := faults) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) functions (Program.ofChecked compiled.sourceProgram)
      (receipt.admitted_entry wellFormed).original size :=
  CallableIndexedOwnedBodyNestedEntries.reflects_of_nested functions owner header
    (receipt.admitted_entry wellFormed).original (receipt.packet captureZero globals)
    (nested_reflects functions owner receipt wellFormed prepared member captureZero globals extension faithful observations functionTypes size)

include wellFormed prepared member captureZero globals extension faithful observations in
/-- A finished Source callback is available at every genuine closed receipt;
its supplied continuation agreement is retained by the production interface. -/
theorem source_callbacks (budget : Nat) :
    CallableIndexedOwnedAdmittedNamedExpressionHeads.SourceBodiesFor
      (headers := headers) (keys := keys) (owner := owner) (functions := functions)
      (registry := registry) (faults := faults) (certificates := fun _ => noExpressions)
      (expressionSyntax := fun _ => noExpressionSyntax) (diagnosticPolicy := .reachable)
      (runtime := true) wellFormed header budget := by
  intro initial argumentsPool arguments actualReceipt _agreement size _smaller
  exact parameter_preserves functions owner actualReceipt wellFormed prepared member captureZero globals extension faithful observations size

include wellFormed prepared member captureZero globals extension faithful observations functionTypes in
/-- The genuine native prefix and saved write select that same exact callback.
No comparison with its reflected Source grade is required. -/
theorem native_callbacks (budget : Nat) :
    CallableIndexedOwnedAdmittedNamedExpressionHeads.NativeBodiesFor
      (headers := headers) (keys := keys) (owner := owner) (functions := functions)
      (registry := registry) (faults := faults) (certificates := fun _ => noExpressions)
      (expressionSyntax := fun _ => noExpressionSyntax) (diagnosticPolicy := .reachable)
      (runtime := true) wellFormed header budget := by
  intro initial argumentsPool arguments actualReceipt prefixSize bodyStore value finalStore
    _prefixRun _prefixWithin _restored size _smaller
  exact parameter_reflects functions owner actualReceipt wellFormed prepared member captureZero globals extension faithful observations functionTypes size

include wellFormed prepared member captureZero globals extension faithful observations in
/-- All observations concern the same actual returned pool. The original
argument pool and the real parameter pool both retain their ordered records. -/
theorem source_post (size : Nat) {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.BodyTrace (Program.ofChecked compiled.sourceProgram) size
      header.function header.context receipt.body.environment receipt.body.heap outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates receipt.body.actualBody receipt.body.store (header.body.rename receipt.body.embedding) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends receipt.body.mapping finalMap ∧ WorldExtends receipt.body.world finalWorld ∧
      AdministrativePreserved receipt.body.mapping receipt.body.store finalMap finalStore ∧
      Dynamic.HeapMetadataExtend receipt.body.heap after ∧
      TypedMixedNamedBody.ReachedExit compiled.compatible.checked
        (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions finalMap finalWorld
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: receipt.administrative)
        (Program.ofChecked compiled.sourceProgram) header.function header.context
        (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
        receipt.body.environment receipt.body.heap after outcome ∧
      ∃ reached : State headers keys ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
          finalMap, finalWorld, after, finalStore, receipt.body.canonical⟩,
        Relates receipt.reached reached ∧
        PoolObservations receipt.reached reached ∧ PoolObservations argumentsPool reached ∧
        CallableIndexedOwnedSourceAdmission.PostAdmission
          (CallableIndexedOwnedIndirectCallerProtocol.of_legacy CallableIndexedOwnedCallerProtocol.base)
          header.context header.function.resultType outcome reached := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds,
      frame, metadata, exit, reached, related⟩ :=
    parameter_preserves functions owner receipt wellFormed prepared member captureZero globals extension faithful observations size trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds,
    frame, metadata, exit, reached, related, reached_pool_observations related,
    reached_pool_observations ((protocol headers keys).trans receipt.related related),
    CallableIndexedOwnedAdmittedBodyEntries.after_body
      (CallableIndexedOwnedIndirectCallerProtocol.of_legacy CallableIndexedOwnedCallerProtocol.base)
      wellFormed (receipt.admitted_entry wellFormed) reached trace frame⟩

include wellFormed prepared member captureZero globals extension faithful observations functionTypes in
/-- Reflection returns its independent Source trace and adds successful deep
typing from that trace at the exact native post, alongside snapshot reads. -/
theorem native_post (size : Nat) {value : Value} {finalStore : Store}
    (completed : EvaluationSize size receipt.body.actualBody receipt.body.store
      (header.body.rename receipt.body.embedding) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyTrace (Program.ofChecked compiled.sourceProgram) sourceSize
        header.function header.context receipt.body.environment receipt.body.heap outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends receipt.body.mapping finalMap ∧ WorldExtends receipt.body.world finalWorld ∧
      AdministrativePreserved receipt.body.mapping receipt.body.store finalMap finalStore ∧
      Dynamic.HeapMetadataExtend receipt.body.heap after ∧
      TypedMixedNamedBody.ReachedExit compiled.compatible.checked
        (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions finalMap finalWorld
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: receipt.administrative)
        (Program.ofChecked compiled.sourceProgram) header.function header.context
        (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
        receipt.body.environment receipt.body.heap after outcome ∧
      ∃ reached : State headers keys ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
          finalMap, finalWorld, after, finalStore, receipt.body.canonical⟩,
        Relates receipt.reached reached ∧
        PoolObservations receipt.reached reached ∧ PoolObservations argumentsPool reached ∧
        CallableIndexedOwnedSourceAdmission.PostAdmission
          (CallableIndexedOwnedIndirectCallerProtocol.of_legacy CallableIndexedOwnedCallerProtocol.base)
          header.context header.function.resultType outcome reached := by
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds,
      frame, metadata, exit, reached, related⟩ :=
    parameter_reflects functions owner receipt wellFormed prepared member captureZero globals extension faithful observations functionTypes size completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds,
    frame, metadata, exit, reached, related, reached_pool_observations related,
    reached_pool_observations ((protocol headers keys).trans receipt.related related),
    CallableIndexedOwnedAdmittedBodyEntries.after_body
      (CallableIndexedOwnedIndirectCallerProtocol.of_legacy CallableIndexedOwnedCallerProtocol.base)
      wellFormed (receipt.admitted_entry wellFormed) reached trace frame⟩

end Tests.SourceCoreClosedAdmittedNamedReceipt
