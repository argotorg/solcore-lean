import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedOrdinaryLambdaFormation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedMethodLambdaFormation

/-! Actual literal lambda receipts select one finite formation branch. An
ordinary Header retains its nested packet; a genuine trait-generated lambda
retains its principal packet and full Source seed. Selection contains original
Code and Source observations, never an arbitrary callee classification law.
Both endpoints use already proved formation leaves without another fold. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSelectedFormationHeads
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedSourceAdmission CallableIndexedLambdaNestedRuntimeBodyMeaning
open CallableIndexedOwnedMethodLambdaSupport

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)

/-- This is an actual ordinary lambda branch, including its full accepted
Code, Source occurrence, ranked body and current captured principal packet. -/
structure Ordinary where
  caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)
  owner : CallableIndexedOwnedFunctionValues.OwnedKey keys
  rank : Nat
  source : TypedSource
  context : SourceSemantics.Context
  evidence : Dynamic.EvidenceEnvironment
  scope : SourceCoreLocalCell.Scope
  id : ExpressionId
  lowered : SourceCoreBasic.LoweredExpr
  head : LambdaAt (values := .initial compiled.compatible.checked) headers caller registry faults rank
    source context evidence scope id lowered
  mapping : LocationMap
  world : StoreTyping
  heap : Dynamic.Heap
  store : Store
  canonical : Environment
  actual : Environment
  administrative : Core.Context
  actualContext : Core.Context
  environment : Dynamic.Environment
  embedding : Renaming
  initial : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩
  packet : CallableIndexedOwnedNestedCanonicalState.Packet owner caller _ initial
  complete : RecursiveNamedCatalogNativeContexts.Complete (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers
  globals : caller.globals = compiled.indexed.base.globals.length
  slots : ∀ header, header ∈ headers → header.slot < compiled.indexed.base.globals.length
  prefixZero : owner.key.capturePrefix = 0
  related : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions
  agrees : EnvironmentsAgree embedding canonical actual
  nativeTyped : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions
  wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)
  runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source
  covers : evidence.Covers context
  locals : Dynamic.EnvironmentAgrees heap context.locals environment
  typed : ExpressionHasType source context id head.code.sourceNode.type
  sameSource : source = CallableIndexedNamedGeneration.source caller.named
  unique : NodeOccurrencesUnique source
  heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile) mapping world heap store
  admitted : Admission (CallableIndexedOwnedIndirectCallerProtocol.forget_slots
    (CallableIndexedOwnedNestedCallerProtocol.carrier (headers := headers) owner caller)) context ⟨initial, packet⟩

/-- This is the actual Header-free lambda Code at its genuine method Source
occurrence. Captures and principal authority are the real input receipts. -/
structure Method where
  function : Dynamic.Closure
  owner : CallableIndexedOwnedFunctionValues.OwnedKey keys
  scope : SourceCoreLocalCell.Scope
  mapping : LocationMap
  world : StoreTyping
  heap : Dynamic.Heap
  store : Store
  actual : Environment
  captured : Captures compiled.indexed mapping world scope function.captured actual
  code : Code compiled.indexed function scope captured.administrative
  support : Support code registry faults
  initial : State headers keys ⟨scope, mapping, world, heap, store, captured.canonical⟩
  packet : CallableIndexedOwnedOriginCanonicalState.Packet owner support.principal.named _ initial
  wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)
  runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) function.context function.source
  covers : function.evidence.Covers function.context
  locals : Dynamic.EnvironmentAgrees heap function.context.locals function.captured
  typed : ExpressionHasType function.source function.context code.id code.sourceNode.type
  sourceType : code.sourceNode.type = FunctionValues.sourceType function
  ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions []
  coercions : code.sourceNode.coercions = []
  heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile) mapping world heap store
  admitted : Admission (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
    function.context ⟨initial, packet⟩

/-- Branch construction requires the genuine actual compiler and Source
receipt itself; this sum supplies no classifier for arbitrary closure values. -/
inductive Selected where
  | ordinary (receipt : Ordinary (headers := headers) (keys := keys) (registry := registry) (faults := faults) profile)
  | method (receipt : Method (headers := headers) (keys := keys) (registry := registry) (faults := faults) profile)

/-- The selected branch retains its own authentic protocol without coercion. -/
def protocol (selected : Selected (headers := headers) (keys := keys) (registry := registry) (faults := faults) profile) :
    ProtectedStateTransition.Protocol (Records keys) :=
  match selected with
  | .ordinary receipt => CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) receipt.owner receipt.caller
  | .method receipt => CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) receipt.owner receipt.support.principal.named

/-- Original Source derivations refer to the selected actual occurrence. -/
def SourceAt (selected : Selected (headers := headers) (keys := keys) (registry := registry) (faults := faults) profile)
    (size : Nat) (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap) : Prop :=
  match selected with
  | .ordinary receipt => RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) size
      receipt.context receipt.evidence receipt.source receipt.environment receipt.heap receipt.id outcome after
  | .method receipt => RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) size
      receipt.function.context receipt.function.evidence receipt.function.source receipt.function.captured
      receipt.heap receipt.code.id outcome after

/-- Native grades measure the original emitted branch at its actual captures. -/
def NativeAt (selected : Selected (headers := headers) (keys := keys) (registry := registry) (faults := faults) profile)
    (size : Nat) (result : Value) (finalStore : Store) : Prop :=
  match selected with
  | .ordinary receipt => EvaluationSize size receipt.actual receipt.store
      (receipt.lowered.expression.rename receipt.embedding) result finalStore
  | .method receipt => EvaluationSize size receipt.actual receipt.store
      (receipt.code.lowered.expression.rename receipt.captured.embedding) result finalStore

/-- The complete existing leaf result retains the branch's exact reached
packet, ordered pool, real relation and Source post admission. -/
def ResultAt (selected : Selected (headers := headers) (keys := keys) (registry := registry) (faults := faults) profile)
    (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap) (result : Value) (finalStore : Store) : Prop :=
  match selected with
  | .ordinary receipt => CallableIndexedOwnedAdmittedOrdinaryLambdaFormation.ResultAt
      (actual := receipt.actual) (ξ := receipt.embedding) receipt.head profile receipt.owner receipt.initial receipt.packet
      outcome after result finalStore
  | .method receipt => CallableIndexedOwnedAdmittedMethodLambdaFormation.ResultAt receipt.captured receipt.code receipt.support
      receipt.owner receipt.initial receipt.packet profile outcome after result finalStore

/-- Source dispatch closes both selected literal branches from authentic
receipts. No completed expression or body meaning is an input. -/
theorem preserves_at (selected : Selected (headers := headers) (keys := keys) (registry := registry) (faults := faults) profile)
    {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : SourceAt profile selected size outcome after) :
    ∃ result finalStore, ResultAt profile selected outcome after result finalStore := by
  cases selected with
  | ordinary receipt =>
    exact CallableIndexedOwnedAdmittedOrdinaryLambdaFormation.preserves_at receipt.head profile receipt.complete
      receipt.globals receipt.slots receipt.owner receipt.prefixZero receipt.initial receipt.packet receipt.related
      receipt.agrees receipt.nativeTyped receipt.wellFormed receipt.runtime receipt.covers receipt.locals receipt.typed
      receipt.sameSource receipt.unique receipt.heaps receipt.admitted trace
  | method receipt =>
    exact CallableIndexedOwnedAdmittedMethodLambdaFormation.preserves_at receipt.captured receipt.code receipt.support
      receipt.owner receipt.initial receipt.packet profile receipt.wellFormed receipt.runtime receipt.covers receipt.locals
      receipt.typed receipt.sourceType receipt.ordinary receipt.coercions receipt.heaps receipt.admitted trace

/-- Reflection reuses each original native producer and independently sized
Source result, preserving that branch's exact pool and principal packet. -/
theorem reflects_at (selected : Selected (headers := headers) (keys := keys) (registry := registry) (faults := faults) profile)
    {size : Nat} {result : Value} {finalStore : Store}
    (completed : NativeAt profile selected size result finalStore) :
    ∃ sourceSize outcome after, SourceAt profile selected sourceSize outcome after ∧
      ResultAt profile selected outcome after result finalStore := by
  cases selected with
  | ordinary receipt =>
    exact CallableIndexedOwnedAdmittedOrdinaryLambdaFormation.reflects_at receipt.head profile receipt.complete
      receipt.globals receipt.slots receipt.owner receipt.prefixZero receipt.initial receipt.packet receipt.related
      receipt.agrees receipt.nativeTyped receipt.wellFormed receipt.runtime receipt.covers receipt.locals receipt.typed
      receipt.sameSource receipt.unique receipt.heaps receipt.admitted completed
  | method receipt =>
    exact CallableIndexedOwnedAdmittedMethodLambdaFormation.reflects_at receipt.captured receipt.code receipt.support
      receipt.owner receipt.initial receipt.packet profile receipt.wellFormed receipt.runtime receipt.covers receipt.locals
      receipt.typed receipt.sourceType receipt.ordinary receipt.coercions receipt.heaps receipt.admitted completed

/-- The original ordinary producer retains its complete stronger closure
receipt, including exact captures, Header support and full Source history. -/
def ordinary_closure (receipt : Ordinary (headers := headers) (keys := keys) (registry := registry) (faults := faults) profile) :=
  CallableIndexedOwnedLambdaFormationReceipts.of_formation receipt.head profile receipt.complete receipt.globals receipt.slots
    receipt.initial receipt.owner receipt.prefixZero receipt.packet.observed receipt.packet.carried receipt.packet.bundle
    receipt.related receipt.agrees receipt.nativeTyped receipt.heaps.runtime_hasTypes

/-- The method producer uses this same actual principal row's complete history. -/
def method_history (receipt : Method (headers := headers) (keys := keys) (registry := registry) (faults := faults) profile) :=
  CallableIndexedOwnedMethodLambdaFormationReceipts.history_at receipt.captured receipt.code receipt.support receipt.owner
    receipt.initial receipt.packet

/-- The exact method Source seed is established by that actual producer. -/
theorem method_source_origin (receipt : Method (headers := headers) (keys := keys) (registry := registry) (faults := faults) profile) :
    SourceOrigin receipt.support (method_history profile receipt) :=
  CallableIndexedOwnedMethodLambdaFormationReceipts.source_origin receipt.captured receipt.code receipt.support receipt.owner
    receipt.initial receipt.packet

/-- Invocation's leading bundle is the actual captured packet observation. -/
theorem method_leading (receipt : Method (headers := headers) (keys := keys) (registry := registry) (faults := faults) profile) :
    receipt.captured.administrative[0]? = some receipt.support.principal.named.signature.parameterType :=
  CallableIndexedOwnedMethodLambdaFormationReceipts.leading receipt.captured receipt.code receipt.support receipt.owner
    receipt.initial receipt.packet

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSelectedFormationHeads
