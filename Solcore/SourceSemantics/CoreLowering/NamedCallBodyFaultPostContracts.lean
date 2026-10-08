import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedInvocationBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedCallerProtocol
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedArgumentTraceBounds

/-! A named call retains its actual argument route and selected body receipt.
The body post stays at the body store; returning a caller wrapper retains the
same physically restored pool. Source and native grades remain independent. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.NamedCallBodyFaultPostContracts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory SourceCoreCallableIndexedFrames RecursiveNamedCatalog
open RecursiveNamedCatalogInvocationBounds CallableIndexedOwnedFunctionState
open NamedInvocationFaultPostContracts
universe u

/-- Only measured native callers supply a strict native child grade. -/
def CompletionBelow (parent : Option Nat) (actual : Environment) (before : Store)
    (expression : Expr) (value : Value) (after : Store) : Prop :=
  match parent with
  | none => True
  | some size => ∃ child, EvaluationSize child actual before expression value after ∧ child < size

/-- The exact body receipt uses the actual invocation grade on native reflection. -/
def InvocationBelow (parent child : Option Nat) : Prop :=
  match parent, child with
  | none, none => True
  | some parent, some child => child < parent
  | _, _ => False

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
  {registry : SourceCoreRawMetadata.Registry}
  {header : CallableIndexedOwnedFunctionValues.Header compiled program}
  {source : TypedSource} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {environment : Dynamic.Environment} {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId}
  {codes : List SourceCoreBasic.LoweredExpr} {mapping : LocationMap} {world : StoreTyping}
  {before : Dynamic.Heap} {store : Store} {canonical actual : Environment} {ξ : Renaming}
  {slots : ProtectedStateTransition.Index → Prop}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}

/-- Each constructor comes from one actual branch of the original call core.
The successful route retains its live capture, exact child receipt, and the
literal equality between the outer returned wrapper and invocation pool. -/
inductive CallRouteAt (post : BodyFaultPost)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) slots callerProtocol)
    (caller : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (sourceParent : Nat) (nativeParent : Option Nat) :
    Dynamic.ExpressionOutcome → Dynamic.Heap → Value → LocationMap → StoreTyping → Store → Prop where
  | argumentFailure {child reason token after finalMap finalWorld finalStore}
      (failed : SourceExecutionSize.ExpressionsFault program child context evidence source environment before ids reason after)
      (smaller : child < sourceParent)
      (evaluation : Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inLeft (SourceCoreCalls.packArguments codes).type (.word token)) finalStore)
      (measured : CompletionBelow nativeParent actual store
        ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inLeft (SourceCoreCalls.packArguments codes).type (.word token)) finalStore)
      (reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (related : callerProtocol.Relates caller reached) :
      CallRouteAt post owner bridge caller sourceParent nativeParent (.fault reason) after
        (.inLeft header.output (.word token)) finalMap finalWorld finalStore
  | bodyApplied {argumentsSize callSize bodySourceSize arguments payloads middle middleMap middleWorld middleStore
      outcome after value finalMap finalWorld finalStore}
      (evaluated : SourceExecutionSize.ExpressionsEvaluate program argumentsSize context evidence source environment before ids arguments middle)
      (argumentsSmaller : argumentsSize < sourceParent)
      (called : RecursiveNamedCallBounds.CallOutcome program callSize context evidence header.function.evidence middle
        (.global ⟨header.instantiation, header.function.evidence⟩) arguments outcome after)
      (callSmaller : callSize < sourceParent)
      (argumentEvaluation : Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inRight .word (DataPatternValues.packValues payloads)) middleStore)
      (argumentMeasured : CompletionBelow nativeParent actual store
        ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inRight .word (DataPatternValues.packValues payloads)) middleStore)
      (argumentState : callerProtocol.State ⟨scope, middleMap, middleWorld, middle, middleStore, canonical⟩)
      (argumentRelated : callerProtocol.Relates caller argumentState)
      (argumentMaps : LocationMap.Extends mapping middleMap)
      (argumentWorlds : WorldExtends world middleWorld)
      (argumentFrame : AdministrativePreserved mapping store middleMap middleStore)
      (argumentMetadata : Dynamic.HeapMetadataExtend before middle)
      (capture : Capture (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        headers owner.key.locations owner.key.capturePrefix ((bridge.pool argumentState).rows owner.position).authority.frameLocation
        header middleMap middleWorld middle middleStore)
      (represented : CallableIndexedParameterMeaning.Arguments
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        middleMap middleWorld header.bindings arguments payloads)
      (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions middleMap middleWorld middle middleStore)
      (bodyTrace : RecursiveNamedCallBounds.BodyOutcome program bodySourceSize header.sourceBody header.function.evidence middle arguments outcome after)
      (bodySmaller : bodySourceSize < callSize)
      (bodyEvaluation : Evaluates (DataPatternValues.packValues payloads :: capture.captured) middleStore
        (header.code.rename capture.embedding.lift) value finalStore)
      (bodyNative : Option Nat)
      (bodyMeasured : InvocationBelow nativeParent bodyNative)
      (receipt : ReturnedAt (header := header) (functions := functions) (registry := registry)
        post bodySourceSize bodyNative owner (bridge.pool argumentState) arguments outcome after value finalMap finalWorld finalStore)
      (finalState : State headers keys ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (bodyRelated : Relates (bridge.pool argumentState) finalState)
      (bodyMaps : LocationMap.Extends middleMap finalMap)
      (bodyWorlds : WorldExtends middleWorld finalWorld)
      (bodyFrame : AdministrativePreserved middleMap middleStore finalMap finalStore)
      (bodyMetadata : Dynamic.HeapMetadataExtend middle after)
      (returned : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (samePool : bridge.pool returned = finalState)
      (relatedCaller : callerProtocol.Relates caller returned) :
      CallRouteAt post owner bridge caller sourceParent nativeParent outcome after value finalMap finalWorld finalStore

section Legacy
variable {faults : FunctionCalls.FaultRep} {arguments : List Dynamic.Value}
  {owner : CallableIndexedOwnedFunctionValues.OwnedKey keys}
  {caller : State headers keys ⟨scope, mapping, world, before, store, canonical⟩}
  {condition : BodyCondition (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix) functions registry header}
  {budget : Nat}

/-- A legacy child supplies only the trivial sidecar on its same actual result. -/
theorem source_trivial
    (meaning : CallableIndexedOwnedInvocationBounds.SourceContinuation (functions := functions) (registry := registry)
      (faults := faults) (header := header) (arguments := arguments) owner caller condition budget) :
    CallableIndexedOwnedInvocationBounds.SourceContinuationWithPost (post := Trivial)
      (functions := functions) (registry := registry) (faults := faults) (header := header)
      (arguments := arguments) owner caller condition budget := by
  intro origin index metadata administrative actualContext actual ξ frameLocation
    physical owned history emitted entry agreement reached related allowed child strict outcome after trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluation, result, finalHeaps,
    maps, worlds, frame, metadata, returned⟩ :=
    meaning physical owned history emitted entry agreement reached related allowed child strict trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluation, result, finalHeaps,
    maps, worlds, frame, metadata, returned, trivial_of_result result⟩

/-- The actual legacy reflected result receives no new fault attribution. -/
theorem native_trivial
    (meaning : CallableIndexedOwnedInvocationBounds.NativeContinuation (functions := functions) (registry := registry)
      (faults := faults) (header := header) (arguments := arguments) owner caller condition budget) :
    CallableIndexedOwnedInvocationBounds.NativeContinuationWithPost (post := Trivial)
      (functions := functions) (registry := registry) (faults := faults) (header := header)
      (arguments := arguments) owner caller condition budget := by
  intro origin index metadata administrative actualContext actual ξ frameLocation prefixSize bodyStore value finalStore
    physical owned history emitted prefixCompleted prefixWithin restored entry reached related allowed child strict
    bodyValue bodyFinalStore bodyCompleted
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, finalHeaps,
    maps, worlds, frame, metadata, returned⟩ :=
    meaning physical owned history emitted prefixCompleted prefixWithin restored entry reached related allowed child strict bodyCompleted
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, finalHeaps,
    maps, worlds, frame, metadata, returned, trivial_of_result result⟩
end Legacy

end Solcore.SourceSemantics.CoreLowering.NamedCallBodyFaultPostContracts
