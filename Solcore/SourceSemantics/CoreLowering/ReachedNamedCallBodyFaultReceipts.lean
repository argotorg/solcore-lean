import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedExpressionHeads
import Solcore.SourceSemantics.CoreLowering.ReachedNamedInvocationFaultReceipts

/-! Finite projections retain the actual named call route. Argument failure
stays distinct from the body receipt, whose post remains at its body store. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ReachedNamedCallBodyFaultReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory SourceCoreCallableIndexedFrames RecursiveNamedCatalog
open RecursiveNamedCatalogInvocationBounds CallableIndexedOwnedFunctionState
open NamedInvocationFaultPostContracts NamedCallBodyFaultPostContracts
open CallableIndexedOwnedExpressionHeads
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {header : CallableIndexedOwnedFunctionValues.Header compiled program}
  {source : TypedSource} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {environment : Dynamic.Environment} {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId}
  {codes : List SourceCoreBasic.LoweredExpr} {mapping : LocationMap} {world : StoreTyping}
  {before : Dynamic.Heap} {store : Store} {canonical actual : Environment} {ξ : Renaming}
  {slots : ProtectedStateTransition.Index → Prop}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  {owner : CallableIndexedOwnedFunctionValues.OwnedKey keys}
  {bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) slots callerProtocol}
  {caller : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩}
  {post : BodyFaultPost}

section Providers
variable {callerPrefix : Nat}
  {namedBridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun index => Globals (headers := headers) owner callerPrefix index.scope index.canonical) callerProtocol}
  {condition : BodyCondition (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix) functions registry header}
  {budget : Nat}

/-- Forget only the strict child's sidecar, preserving its actual continuation. -/
theorem source_provider_forget
    (meaning : SourceInvocationsForWithPost (source := source) (context := context) (evidence := evidence)
      (faults := faults) functions owner condition namedBridge caller (environment := environment) (ids := ids) post budget) :
    SourceInvocationsFor (source := source) (context := context) (evidence := evidence)
      (faults := faults) functions owner condition namedBridge caller (environment := environment) (ids := ids) budget := by
  intro size arguments middle middleMap middleWorld middleStore payloads evaluated argumentState
    related maps worlds frame metadata capture represented heaps
  exact ReachedNamedInvocationFaultReceipts.source_continuation_forget
    (meaning evaluated argumentState related maps worlds frame metadata capture represented heaps)

/-- The reflected continuation retains its independent Source output grade. -/
theorem native_provider_forget
    (meaning : NativeInvocationsForWithPost (source := source) (context := context) (evidence := evidence)
      (faults := faults) functions owner condition namedBridge caller (environment := environment) (ids := ids) post budget) :
    NativeInvocationsFor (source := source) (context := context) (evidence := evidence)
      (faults := faults) functions owner condition namedBridge caller (environment := environment) (ids := ids) budget := by
  intro size arguments middle middleMap middleWorld middleStore payloads evaluated argumentState
    related maps worlds frame metadata capture represented heaps
  exact ReachedNamedInvocationFaultReceipts.native_continuation_forget
    (meaning evaluated argumentState related maps worlds frame metadata capture represented heaps)
end Providers

section Routes
variable {sourceParent : Nat} {nativeParent : Option Nat} {outcome : Dynamic.ExpressionOutcome}
  {after : Dynamic.Heap} {value : Value} {finalMap : LocationMap} {finalWorld : StoreTyping} {finalStore : Store}

/-- A finite route projection keeps the failed list or the same successful
argument pool and exact restored body receipt. It does not classify a fault
by its reason/token or manufacture a primitive origin for argument failure. -/
theorem argument_failure_or_body
    (route : CallRouteAt (functions := functions) (registry := registry) (header := header)
      (source := source) (context := context) (evidence := evidence) (environment := environment)
      (ids := ids) (codes := codes) (actual := actual) (ξ := ξ)
      post owner bridge caller sourceParent nativeParent outcome after value finalMap finalWorld finalStore) :
    (∃ child reason token,
      outcome = .fault reason ∧
      SourceExecutionSize.ExpressionsFault program child context evidence source environment before ids reason after ∧
      child < sourceParent ∧ value = .inLeft header.output (.word token) ∧
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inLeft (SourceCoreCalls.packArguments codes).type (.word token)) finalStore ∧
      CompletionBelow nativeParent actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inLeft (SourceCoreCalls.packArguments codes).type (.word token)) finalStore) ∨
    (∃ argumentsSize arguments middle middleMap middleWorld middleStore,
      ∃ argumentState : callerProtocol.State ⟨scope, middleMap, middleWorld, middle, middleStore, canonical⟩,
      ∃ bodySourceSize bodyNative,
      SourceExecutionSize.ExpressionsEvaluate program argumentsSize context evidence source environment before ids arguments middle ∧
      argumentsSize < sourceParent ∧ bodySourceSize < sourceParent ∧
      callerProtocol.Relates caller argumentState ∧ InvocationBelow nativeParent bodyNative ∧
      ReturnedAt (header := header) (functions := functions) (registry := registry)
        post bodySourceSize bodyNative owner (bridge.pool argumentState) arguments outcome after value finalMap finalWorld finalStore ∧
      ∃ finalState : State headers keys ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
      ∃ returned : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
      Relates (bridge.pool argumentState) finalState ∧ bridge.pool returned = finalState ∧ callerProtocol.Relates caller returned) := by
  cases route with
  | argumentFailure failed smaller evaluation measured reached related =>
    exact .inl ⟨_, _, _, rfl, failed, smaller, rfl, evaluation, measured⟩
  | bodyApplied evaluated argumentsSmaller called callSmaller argumentEvaluation argumentMeasured
      argumentState argumentRelated argumentMaps argumentWorlds argumentFrame argumentMetadata capture represented heaps
      bodyTrace bodySmaller bodyEvaluation bodyNative bodyMeasured receipt finalState bodyRelated
      bodyMaps bodyWorlds bodyFrame bodyMetadata returned samePool relatedCaller =>
    exact .inr ⟨_, _, _, _, _, _, argumentState, _, bodyNative, evaluated, argumentsSmaller,
      Nat.lt_trans bodySmaller callSmaller, argumentRelated, bodyMeasured, receipt,
      finalState, returned, bodyRelated, samePool, relatedCaller⟩

/-- The actual word is retained by either real route. Body fault attribution
still belongs to its exact ReturnedAt receipt at bodyStore. -/
theorem fault_word {reason : Dynamic.SemanticFault}
    (route : CallRouteAt (functions := functions) (registry := registry) (header := header)
      (source := source) (context := context) (evidence := evidence) (environment := environment)
      (ids := ids) (codes := codes) (actual := actual) (ξ := ξ)
      post owner bridge caller sourceParent nativeParent (.fault reason) after value finalMap finalWorld finalStore) :
    ∃ token, value = .inLeft header.output (.word token) := by
  cases route with
  | argumentFailure failed smaller evaluation measured reached related => exact ⟨_, rfl⟩
  | bodyApplied evaluated argumentsSmaller called callSmaller argumentEvaluation argumentMeasured
      argumentState argumentRelated argumentMaps argumentWorlds argumentFrame argumentMetadata capture represented heaps
      bodyTrace bodySmaller bodyEvaluation bodyNative bodyMeasured receipt finalState bodyRelated
      bodyMaps bodyWorlds bodyFrame bodyMetadata returned samePool relatedCaller =>
    exact ReachedNamedInvocationFaultReceipts.fault_word receipt
end Routes
end Solcore.SourceSemantics.CoreLowering.ReachedNamedCallBodyFaultReceipts
