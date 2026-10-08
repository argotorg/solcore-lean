import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedTypedLambdaBodyContinuations
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaInvocationBounds

/-! Typed lambda invocation uses the real parameter receipts and strict flow
family. The original saved-frame restoration and finite apply edges preserve
that actual caller pool, without an escaped-token assumption. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedTypedLambdaInvocationBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedParameterMeaning
open RecursiveNamedCatalogInvocationBounds (Below)
open CallableIndexedOwnedTypedLambdaBodyContinuations (FlowPreserves FlowReflects)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {capturedActual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured capturedActual)
  (code : Code compiled.indexed function scope captured.administrative) (history : History code)
  {expressionSyntax : TypedSource → ExpressionId → Prop}
  {certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (body : CallableIndexedOwnedTypedLambdaStaticBody.Body code program expressionSyntax certificates)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {arguments : List Dynamic.Value} {nativeArguments : List Value} {before : Dynamic.Heap} {store : Store}
  (represented : Arguments (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    mapping world code.receipt.loweredParameters arguments nativeArguments)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
  (reference : captured.canonical[code.referenceIndex]? =
    some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation))
  {currentMetadata : Option MetadataState}
  (currentCarried : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
    (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost currentMetadata)
  (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed compiled.indexed.ancestry.graph.inputs
    history.metadata code.descriptor.id = true)
  (beforeTyped : Dynamic.HeapWellTyped function.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes function.context before arguments body.types)
  (stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows caller)
  (wellFormed : ProgramWellFormed program)

/-- The original invocation result retains its real restored caller state. -/
def ResultAt (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap)
    (value : Value) (finalStore : Store) : Prop :=
  ∃ finalMap finalWorld,
    FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      finalMap finalWorld function.resultType code.receipt.resultCore faults outcome value ∧
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
    LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
    AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
    ProtectedStateTransition.Transition (protocol headers keys) caller
      ⟨callerScope, finalMap, finalWorld, after, finalStore, callerCanonical⟩

include represented heaps locals reference currentCarried allowed beforeTyped argumentsTyped stable wellFormed in
theorem invocation_preserves_bounded (budget : Nat)
    (below : Below budget (FlowPreserves captured code body functions (registry := registry) (faults := faults) (headers := headers) (keys := keys)))
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.CallOutcome program size callContext callerEvidence function.evidence before
      (.closure function) arguments outcome after) (within : size ≤ budget) :
    ∃ value finalStore,
      Evaluates (DataPatternValues.packValues nativeArguments :: SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame history.native :: capturedActual)
        store (code.body.rename captured.embedding.lift.lift) value finalStore ∧
      ResultAt (registry := registry) (faults := faults) captured code functions caller outcome after value finalStore := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, result, finalHeaps, maps, worlds, frame, metadata, transition⟩ :=
    CallableIndexedOwnedLambdaInvocationBounds.invocation_preserves_bounded_at_with_continuation
      captured code history body.toContext functions represented owner caller heaps locals reference currentCarried allowed
      budget (CallableIndexedOwnedTypedLambdaBodyContinuations.source_continuation
        captured code history body functions owner caller beforeTyped argumentsTyped stable wellFormed budget below)
      trace within
  exact ⟨value, finalStore, evaluated, finalMap, finalWorld, result, finalHeaps, maps, worlds, frame, metadata, transition⟩

include represented heaps locals reference currentCarried allowed beforeTyped argumentsTyped stable wellFormed in
theorem invocation_reflects_bounded (budget : Nat)
    (below : Below budget (FlowReflects captured code body functions (registry := registry) (faults := faults) (headers := headers) (keys := keys)))
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {value : Value} {finalStore : Store}
    (completed : EvaluationSize size
      (DataPatternValues.packValues nativeArguments :: SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame history.native :: capturedActual)
      store (code.body.rename captured.embedding.lift.lift) value finalStore) (within : size ≤ budget) :
    ∃ sourceSize outcome after,
      RecursiveNamedCallBounds.CallOutcome program sourceSize callContext callerEvidence function.evidence before
        (.closure function) arguments outcome after ∧
      ResultAt (registry := registry) (faults := faults) captured code functions caller outcome after value finalStore := by
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, finalHeaps, maps, worlds, frame, metadata, transition⟩ :=
    CallableIndexedOwnedLambdaInvocationBounds.invocation_reflects_bounded_at_with_continuation
      captured code history body.toContext functions represented owner caller heaps locals reference currentCarried allowed
      body.frame budget (CallableIndexedOwnedTypedLambdaBodyContinuations.native_continuation
        captured code history body functions owner caller beforeTyped argumentsTyped stable wellFormed budget below)
      completed within
  exact ⟨sourceSize, outcome, after, trace, finalMap, finalWorld, result, finalHeaps, maps, worlds, frame, metadata, transition⟩

include represented heaps locals reference currentCarried allowed beforeTyped argumentsTyped stable wellFormed in
theorem application_preserves_bounded (budget : Nat)
    (below : Below budget (FlowPreserves captured code body functions (registry := registry) (faults := faults) (headers := headers) (keys := keys)))
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.CallOutcome program size callContext callerEvidence function.evidence before
      (.closure function) arguments outcome after) (within : size ≤ budget) :
    ∃ value finalStore,
      Evaluates [CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual,
        DataPatternValues.packValues nativeArguments] store CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      ResultAt (registry := registry) (faults := faults) captured code functions caller outcome after value finalStore := by
  obtain ⟨value, finalStore, evaluated, result⟩ := invocation_preserves_bounded
    captured code history body functions represented owner caller heaps locals reference currentCarried allowed
    beforeTyped argumentsTyped stable wellFormed budget below trace within
  exact ⟨value, finalStore, .apply (.second (.first (.var rfl))) (.var rfl) evaluated, result⟩

include represented heaps locals reference currentCarried allowed beforeTyped argumentsTyped stable wellFormed in
theorem application_reflects_bounded (budget : Nat)
    (below : Below budget (FlowReflects captured code body functions (registry := registry) (faults := faults) (headers := headers) (keys := keys)))
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {value : Value} {finalStore : Store}
    (completed : EvaluationSize size [CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual,
        DataPatternValues.packValues nativeArguments] store CallableIndexedLambdaCalls.applyPayload value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after,
      RecursiveNamedCallBounds.CallOutcome program sourceSize callContext callerEvidence function.evidence before
        (.closure function) arguments outcome after ∧
      ResultAt (registry := registry) (faults := faults) captured code functions caller outcome after value finalStore := by
  obtain ⟨bodySize, smaller, applied⟩ := completed.apply_body (.second (.first (.var rfl))) (.var rfl)
  exact invocation_reflects_bounded
    captured code history body functions represented owner caller heaps locals reference currentCarried allowed
    beforeTyped argumentsTyped stable wellFormed budget below applied (Nat.le_trans (Nat.le_of_lt smaller) within)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedTypedLambdaInvocationBounds
