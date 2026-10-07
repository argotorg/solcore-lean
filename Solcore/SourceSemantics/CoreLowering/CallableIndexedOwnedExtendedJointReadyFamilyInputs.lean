import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedJointReadyFamilyInputs
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodLambdaReadyFamilyReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedNestedReadyFamilyReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBodyReadyCatalog

/-! This additive static union preserves all frozen joint branches. Genuine
method-generated lambdas use their trait-principal packets; named nested
entries retain their real Source seed, bundle and frame. Actual mixed
expression dispatch remains a separate strict measured obligation. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedExtendedJointReadyFamilyInputs
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState
open CallableIndexedOwnedAdmittedLexicalReadiness (readiness)
open CallableIndexedOwnedBodySourceOrigin (source_origin)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {certificates : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}

/-- Original branches are retained verbatim. Each additional index carries
its genuine full Source/compiler/principal receipts and exact packet protocol. -/
inductive Index where
  | existing (receipt : CallableIndexedOwnedJointReadyFamilyInputs.Index
      (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax))
  | methodLambda (receipt : CallableIndexedOwnedMethodLambdaReadyFamilyReceipts.Index
      (compiled := compiled) (keys := keys) (registry := registry) (faults := faults))
  | namedNested (receipt : CallableIndexedOwnedNamedNestedReadyFamilyReceipts.Index
      (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax) (diagnosticPolicy := .reachable) true)

/-- The complete original compiler origin is preserved branch by branch. -/
def base_origin (index : Index (headers := headers) (keys := keys) (registry := registry) (faults := faults)
    (certificates := certificates) (expressionSyntax := expressionSyntax)) :
    CallableRuntimeBodyOrigins.StaticOrigin (.initial compiled.compatible.checked)
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed) registry faults :=
  match index with
  | .existing receipt => CallableIndexedOwnedJointReadyFamilyInputs.base_origin receipt
  | .methodLambda receipt => receipt.support.origin receipt.escaped
  | .namedNested receipt => CallableRuntimeBodyStaticOrigins.named true receipt.receipt.profile receipt.receipt.escaped

/-- Runtime validity is the independent genuine Source receipt of that branch. -/
theorem sourceRuntime (index : Index (headers := headers) (keys := keys) (registry := registry) (faults := faults)
    (certificates := certificates) (expressionSyntax := expressionSyntax)) :
    Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
      (base_origin index).context (base_origin index).function.source := by
  cases index with
  | existing receipt => exact CallableIndexedOwnedJointReadyFamilyInputs.sourceRuntime receipt
  | methodLambda receipt => exact receipt.sourceRuntime
  | namedNested receipt => exact receipt.receipt.sourceRuntime

/-- The exact Source domain is strengthened without changing the compiled body. -/
def origin (index : Index (headers := headers) (keys := keys) (registry := registry) (faults := faults)
    (certificates := certificates) (expressionSyntax := expressionSyntax)) :=
  source_origin (base_origin index) (sourceRuntime index)

/-- Named slots, captured lambda packets and trait-principal packets remain
separate genuine protocols over the same full ordered pool representation. -/
def protocol (index : Index (headers := headers) (keys := keys) (registry := registry) (faults := faults)
    (certificates := certificates) (expressionSyntax := expressionSyntax)) :
    ProtectedStateTransition.Protocol (Records keys) :=
  match index with
  | .existing receipt => CallableIndexedOwnedJointReadyFamilyInputs.protocol receipt
  | .methodLambda receipt => CallableIndexedOwnedMethodLambdaReadyFamilyReceipts.body_protocol (headers := headers) receipt
  | .namedNested receipt => CallableIndexedOwnedNamedNestedReadyFamilyReceipts.body_protocol true receipt

/-- Each branch returns the identical underlying actual pool and records. -/
def bridge (index : Index (headers := headers) (keys := keys) (registry := registry) (faults := faults)
    (certificates := certificates) (expressionSyntax := expressionSyntax)) :
    CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) (protocol index) := by
  cases index with
  | existing receipt => exact CallableIndexedOwnedJointReadyFamilyInputs.bridge receipt
  | methodLambda receipt => exact CallableIndexedOwnedMethodLambdaReadyFamilyReceipts.bridge (headers := headers) receipt
  | namedNested receipt => exact CallableIndexedOwnedNamedNestedReadyFamilyReceipts.bridge true receipt

/-- Binding extension and restoration use each original actual protocol. -/
def bindings (index : Index (headers := headers) (keys := keys) (registry := registry) (faults := faults)
    (certificates := certificates) (expressionSyntax := expressionSyntax)) :
    ProtectedStateTransition.Bindings (protocol index) := by
  cases index with
  | existing receipt => exact CallableIndexedOwnedJointReadyFamilyInputs.bindings receipt
  | methodLambda receipt =>
    exact CallableIndexedOwnedOriginCanonicalState.bindings (headers := headers)
      receipt.owner receipt.support.principal.named
  | namedNested receipt =>
    exact CallableIndexedOwnedNestedCanonicalState.bindings (headers := headers)
      receipt.owner receipt.receipt.header

/-- Actual administrative effects preserve packet facets at that same post. -/
def transport (index : Index (headers := headers) (keys := keys) (registry := registry) (faults := faults)
    (certificates := certificates) (expressionSyntax := expressionSyntax)) :
    ProtectedStateTransition.AdministrativeTransport (protocol index) := by
  cases index with
  | existing receipt => exact CallableIndexedOwnedJointReadyFamilyInputs.transport receipt
  | methodLambda receipt =>
    exact CallableIndexedOwnedOriginCanonicalState.administrativeTransport (headers := headers)
      receipt.owner receipt.support.principal.named
  | namedNested receipt =>
    exact CallableIndexedOwnedNestedCanonicalState.administrativeTransport (headers := headers)
      receipt.owner receipt.receipt.header

variable (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (sameLayouts : ∀ header, header ∈ headers → header.layouts = compiled.indexed.layouts)

/-- Real marked allocation returns the exact reached protocol state; layout
casts use only authentic static equalities. -/
def producer (index : Index (headers := headers) (keys := keys) (registry := registry) (faults := faults)
    (certificates := certificates) (expressionSyntax := expressionSyntax)) :
    ProtectedStateTransition.MarkedAllocation.Producer (protocol index) (origin index).layouts (origin index).frameLayout
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) := by
  cases index with
  | existing receipt => exact CallableIndexedOwnedJointReadyFamilyInputs.producer functions sameLayouts receipt
  | methodLambda receipt =>
    exact CallableIndexedOwnedOriginCanonicalState.markedProducer (headers := headers)
      receipt.owner receipt.support.principal.named
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
  | namedNested receipt =>
    change ProtectedStateTransition.MarkedAllocation.Producer
      (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) receipt.owner receipt.receipt.header)
      receipt.receipt.header.layouts compiled.indexed.ancestry.layout.frame
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    exact (sameLayouts receipt.receipt.header receipt.receipt.member).symm ▸
      CallableIndexedOwnedNestedCanonicalState.markedProducer (headers := headers)
        receipt.owner receipt.receipt.header
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)

private theorem ready_cast {stateProtocol : ProtectedStateTransition.Protocol (Records keys)}
    {first second : SourceCoreAllocationLayouts.Prepared} {firstFrame secondFrame : SourceCoreCallableIndexedFrames.Layout}
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects definitions}
    (layouts : first = second) (frame : firstFrame = secondFrame)
    (marked : ProtectedStateTransition.MarkedAllocation.Producer stateProtocol second secondFrame model)
    {location : Location} {native : NativeFrame}
    (ready : ProtectedStateTransition.OrdinaryAllocation.ReadyAt marked.toOrdinary location native) :
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt
      ((layouts.symm ▸ frame.symm ▸ marked).toOrdinary) location native := by
  cases layouts
  cases frame
  exact ready

include functions sameLayouts in
/-- A genuine selected stable row supplies allocation readiness in the same
branch; no Source typing or canonical slots are inferred by this gate. -/
theorem acquire (index : Index (headers := headers) (keys := keys) (registry := registry) (faults := faults)
    (certificates := certificates) (expressionSyntax := expressionSyntax))
    (location : Location) (native : NativeFrame)
    (stable : CallableIndexedOwnedAllocationProducer.StableOwner keys location native) :
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt (producer functions sameLayouts index).toOrdinary location native := by
  cases index with
  | existing receipt => exact CallableIndexedOwnedJointReadyFamilyInputs.acquire functions sameLayouts receipt location native stable
  | methodLambda receipt =>
    exact CallableIndexedOwnedOriginCanonicalState.readyAt_of_stableOwner (headers := headers)
      receipt.owner receipt.support.principal.named
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) stable
  | namedNested receipt =>
    exact ready_cast (sameLayouts receipt.receipt.header receipt.receipt.member) rfl _
      (CallableIndexedOwnedNestedCanonicalState.readyAt_of_stableOwner (headers := headers)
        receipt.owner receipt.receipt.header
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) stable)

variable (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))

/-- Genuine Source facts, static sites, actual allocation and snapshot
transfers build the existing finite catalog input fields internally. -/
def inputs (index : Index (headers := headers) (keys := keys) (registry := registry) (faults := faults)
    (certificates := certificates) (expressionSyntax := expressionSyntax)) :=
  CallableIndexedOwnedBodyReadyCatalog.inputs (bridge index) (base_origin index) (sourceRuntime index)
    (bindings index) wellFormed

variable (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)

include extension faithful observations sameLayouts in
/-- The sole family supplies these actual smaller expression results. The
finite head/loop recipes are proved internally at the exact indexed protocol. -/
theorem preserving_kits (index : Index (headers := headers) (keys := keys) (registry := registry) (faults := faults)
    (certificates := certificates) (expressionSyntax := expressionSyntax)) (budget : Nat)
    (expressions : ∀ context, (origin index).validity context →
      RecursiveNamedHeaderContracts.AtMost budget (fun size =>
        RecursiveNamedLexicalContracts.Stateful.WithReady.ExpressionPreservesAt (protocol index) (readiness (bridge index))
          (Program.ofChecked compiled.sourceProgram) (origin index).function.evidence
          (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
          (inputs wellFormed index).exprFacts ((origin index).certificates context)
          (source := (origin index).function.source) (context := context) (faults := faults) size)) :
    CallableRuntimeBodyReadyInputs.PreservingKits (protocol index) (readiness (bridge index)) (bindings index)
      (Program.ofChecked compiled.sourceProgram) (origin index) functions
      (CallableIndexedOwnedAllocationProducer.StableOwner keys) (inputs wellFormed index) budget :=
  CallableIndexedOwnedBodyReadyCatalog.preserving_ready_kits (bridge index) (base_origin index) (sourceRuntime index)
    (bindings index) wellFormed functions extension faithful observations (CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (producer functions sameLayouts index) (acquire functions sameLayouts index) (transport index) budget expressions

include extension faithful observations sameLayouts in
/-- Native finite kits use the same original strict expression children and
return the same indexed witness; no joint body closure is asserted here. -/
theorem reflecting_kits (functionTypes : FunctionRuntimeViews functions)
    (index : Index (headers := headers) (keys := keys) (registry := registry) (faults := faults)
    (certificates := certificates) (expressionSyntax := expressionSyntax)) (budget : Nat)
    (expressions : ∀ context, (origin index).validity context →
      RecursiveNamedBoundedContracts.Below budget (fun size =>
        RecursiveNamedLexicalContracts.Stateful.WithReady.ExpressionReflectsAt (protocol index) (readiness (bridge index))
          (Program.ofChecked compiled.sourceProgram) (origin index).function.evidence
          (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
          (inputs wellFormed index).exprFacts ((origin index).certificates context)
          (source := (origin index).function.source) (context := context) (faults := faults) size)) :
    CallableRuntimeBodyReadyInputs.ReflectingKits (protocol index) (readiness (bridge index)) (bindings index)
      (Program.ofChecked compiled.sourceProgram) (origin index) functions
      (CallableIndexedOwnedAllocationProducer.StableOwner keys) (inputs wellFormed index) budget :=
  CallableIndexedOwnedBodyReadyCatalog.reflecting_ready_kits (bridge index) (base_origin index) (sourceRuntime index)
    (bindings index) wellFormed functions extension faithful observations (CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (producer functions sameLayouts index) (acquire functions sameLayouts index) (transport index) budget functionTypes expressions

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedExtendedJointReadyFamilyInputs
