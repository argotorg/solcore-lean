import Solcore.Test.SourceCoreClosedOwnedLexicalBody
import Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyMutualMeaning
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaInvocationBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedCaptureValidity
import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaTemplatePermission

/-! A genuine static anonymous origin with an empty Unit body closes through
the shared actual body family. Its stored payload application retains real
marked parameters, full captures and the actual restored caller pool. -/
set_option autoImplicit false
namespace Tests.SourceCoreClosedOwnedAnonymousInvocation
open Solcore Core Frontend SourceInference
open SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallableIndexedLambdaValues
open CallableIndexedOwnedLambdaInvocationBounds ProtectedStateTransition
open Tests.SourceCoreClosedOwnedLexicalBody (noExpressions noExpressionSyntax reached_pool_observations)

section EmptyOrigin
variable {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (original : CallableRuntimeBodyOrigins.StaticOrigin values ambient registry faults)
  (emptyBody : original.function.body = []) (unitResult : original.function.resultType = .unit)

include emptyBody in
/-- Invert the original static empty statement tree, without another fold. -/
private theorem original_flow : original.body.flow = LocalLoop.fallthrough original.output := by
  have tree := original.body.tree
  rw [emptyBody] at tree
  generalize sameFlow : original.body.flow = flow at tree ⊢
  cases tree with
  | body _ lexical => cases lexical with | nil _ => rfl

/-- Re-extract the same emitted empty body under an empty leaf certificate.
All source contexts, layouts, output types and code receipts stay original. -/
private def emptyKernel : CallableRuntimeBodyKernel.BodyFor original.layouts original.owner original.active
    original.frameLayout original.globals original.onError values original.function noExpressionSyntax noExpressions
    original.validity original.diagnosticPolicy ambient original.administrative original.context original.scope
    original.output original.code original.fellThrough original.escaped registry faults where
  flow := LocalLoop.fallthrough original.output
  tree := .body (emptyBody ▸ .nil (Or.inr unitResult)) (emptyBody ▸ .nil (Or.inr unitResult))
  sites := .body (syntaxTree := emptyBody ▸ .nil (Or.inr unitResult)) (body := emptyBody ▸ .nil (Or.inr unitResult))
  initialValid := original.body.initialValid
  projection := original.body.projection
  unique := original.body.unique
  emitted := by rw [← original_flow original emptyBody]; exact original.body.emitted

def emptyOrigin : CallableRuntimeBodyOrigins.StaticOrigin values ambient registry faults :=
  { original with expressionSyntax := noExpressionSyntax, certificates := noExpressions, body := emptyKernel original emptyBody unitResult }
end EmptyOrigin

section Bodies
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : SourceSemantics.Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (code : Code compiled.indexed function scope administrative)
  (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code)
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (body : BodyOrigin (program := program) code inputs registry faults)
  (emptyBody : function.body = []) (unitResult : function.resultType = .unit)

/-- The original full ClosureFrame and every capture/code alignment are retained. -/
def emptyBodyOrigin : BodyOrigin (program := program) code inputs registry faults where
  origin := emptyOrigin body.origin (by simpa only [body.function_eq] using emptyBody)
    (by simpa only [body.function_eq] using unitResult)
  frame := body.frame
  function_eq := body.function_eq
  context_eq := body.context_eq
  administrative_eq := body.administrative_eq
  scope_eq := body.scope_eq
  frame_eq := body.frame_eq
  globals_eq := body.globals_eq
  output_eq := body.output_eq
  code_eq := body.code_eq

variable (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (layouts : body.origin.layouts = compiled.indexed.layouts)

private def producer : MarkedAllocation.Producer (protocol headers keys) body.origin.layouts body.origin.frameLayout
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) :=
  layouts.symm ▸ (body.frame_eq.symm ▸ CallableIndexedOwnedMarkedAllocation.producer headers keys
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions))

private theorem ready_cast {first second : SourceCoreAllocationLayouts.Prepared}
    {firstFrame secondFrame : SourceCoreCallableIndexedFrames.Layout}
    (same : first = second) (sameFrame : firstFrame = secondFrame)
    (marked : MarkedAllocation.Producer (protocol headers keys) second secondFrame
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions))
    {location : Location} {native : NativeFrame} (ready : OrdinaryAllocation.ReadyAt marked.toOrdinary location native) :
    OrdinaryAllocation.ReadyAt ((same.symm ▸ (sameFrame.symm ▸ marked)).toOrdinary) location native := by
  cases same
  cases sameFrame
  exact ready

private theorem acquire (location : Location) (native : NativeFrame)
    (seed : CallableIndexedOwnedAllocationProducer.StableOwner keys location native) :
    OrdinaryAllocation.ReadyAt (producer (headers := headers) (keys := keys) code inputs body functions layouts).toOrdinary location native := by
  exact ready_cast functions layouts body.frame_eq
    (CallableIndexedOwnedMarkedAllocation.producer headers keys (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions))
    (CallableIndexedOwnedAllocationProducer.readyAt_of_stableOwner
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) seed)

include extension faithful observations layouts in
/-- The single authentic anonymous origin closes its own body family. No
smaller body or expression execution meaning is assumed. -/
theorem empty_preserves (size : Nat) :
    CallableRuntimeBodyOrigins.Stateful.PreservesAt (protocol headers keys)
      (CallableIndexedOwnedAllocationProducer.StableOwner keys) functions program
      (emptyBodyOrigin code inputs body emptyBody unitResult).origin size := by
  exact CallableRuntimeBodyMutualMeaning.Stateful.preserves_at
    (fun (_ : Unit) => (emptyBodyOrigin code inputs body emptyBody unitResult).origin)
    functions extension program faithful observations (protocol headers keys)
    (fun _ => CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (fun _ => producer code inputs body functions layouts)
    (fun _ => acquire code inputs body functions layouts)
    (administrativeTransport headers keys) (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys)
    (by intro _ context _ budget child _ _ scope id lowered impossible; cases impossible) size ()

include extension faithful observations functionTypes layouts in
/-- Native reflection uses the same shared closer and keeps its independent
source grade and exact reached state. -/
theorem empty_reflects (size : Nat) :
    CallableRuntimeBodyOrigins.Stateful.ReflectsAt (protocol headers keys)
      (CallableIndexedOwnedAllocationProducer.StableOwner keys) functions program
      (emptyBodyOrigin code inputs body emptyBody unitResult).origin size := by
  exact CallableRuntimeBodyMutualMeaning.Stateful.reflects_at
    (fun (_ : Unit) => (emptyBodyOrigin code inputs body emptyBody unitResult).origin)
    functions extension program faithful observations functionTypes (protocol headers keys)
    (fun _ => CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (fun _ => producer code inputs body functions layouts)
    (fun _ => acquire code inputs body functions layouts)
    (administrativeTransport headers keys) (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys)
    (by intro _ context _ budget child _ _ scope id lowered impossible; cases impossible) size ()
end Bodies

section Application
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : SourceSemantics.Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {function : Dynamic.Closure} {scope callerScope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {capturedActual callerCanonical : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured capturedActual)
  (code : Code compiled.indexed function scope captured.administrative) (history : History code)
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (support : CallableIndexedOwnedFunctionValues.StaticSupport headers registry faults code)
  (escaped : faults .controlEscapedFunction code.compilation.internalReason)
  (emptyBody : function.body = []) (unitResult : function.resultType = .unit)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  {arguments : List Dynamic.Value} {payloads : List Value}
  (represented : CallableIndexedParameterMeaning.Arguments (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    mapping world code.receipt.loweredParameters arguments payloads)
  {before : Dynamic.Heap} {store : Store}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world before store)
  (reference : captured.canonical[code.referenceIndex]? = some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation))
  {metadata : Option MetadataState}
  (carried : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
    (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost metadata)

set_option quotPrecheck false in
local notation "inputs" => support.2.2.receipt.body.toContext
set_option quotPrecheck false in
local notation "originalBody" => BodyOrigin.nested code inputs support.2.2.receipt escaped
set_option quotPrecheck false in
local notation "closedBody" => emptyBodyOrigin code inputs originalBody emptyBody unitResult

/-- Observations use every ordered row of the genuine returned pool. -/
def poolObservations {firstIndex lastIndex : Index}
    (first : State headers keys firstIndex) (last : State headers keys lastIndex) : Prop :=
  (∀ row, RecordPrefix (records first row) (records last row)) ∧
  (∀ row record, record ∈ records last row → CallableIndexedSnapshots.Holds compiled.indexed.ancestry.graph.inputs
    compiled.indexed.ancestry.graph.table compiled.indexed.ancestry.layout.frame lastIndex.mapping lastIndex.store record) ∧
  (∀ row record, record ∈ records first row → record ∈ records last row)

include captured code history support escaped emptyBody unitResult extension faithful observations represented heaps reference carried in
/-- Actual source lambda formation supplies capture validity at this heap.
The stored carrier then runs the genuine parameter/body/restore application. -/
theorem formed_application_source_post
    {formationContext callContext : SourceSemantics.Context} {formationSource : TypedSource}
    {formationEvidence callerEvidence : Dynamic.EvidenceEnvironment} {formationEnvironment : Dynamic.Environment}
    {requirements : List RequirementId} {coercions : List CoercionStep}
    (formationLocals : Dynamic.EnvironmentAgrees before formationContext.locals formationEnvironment)
    (formation : Dynamic.ExpressionFormEvaluates program formationContext formationEvidence formationSource formationEnvironment before
      (.lambda function.parameters function.resultType function.body) requirements coercions (.closure function) before)
    (size : Nat) {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.CallOutcome program size callContext callerEvidence function.evidence before
      (.closure function) arguments outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates [CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual,
        DataPatternValues.packValues payloads] store CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : State headers keys ⟨callerScope, finalMap, finalWorld, after, finalStore, callerCanonical⟩,
        Relates caller reached ∧ poolObservations caller reached := by
  have captures := (CallableIndexedOwnedCaptureValidity.captures_of_formation formationLocals formation).2
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, result, finalHeaps, maps, worlds, preserved, metadata, reached, related⟩ :=
    CallableIndexedOwnedLambdaInvocationBounds.application_preserves_bounded_with captured code history inputs functions represented
      owner caller heaps captures reference carried (CallableIndexedLambdaTemplatePermission.lambda_allowed code history)
      closedBody size (fun child _ => empty_preserves code inputs originalBody emptyBody unitResult functions
        extension faithful observations (by rfl) child) trace (Nat.le_refl _)
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, result, finalHeaps, maps, worlds, preserved, metadata,
    reached, related, reached_pool_observations related⟩

include captured code history support escaped emptyBody unitResult extension faithful observations functionTypes represented heaps reference carried in
/-- Source closure typing authenticates raw capture declarations separately
from its stored native carrier. Reflection returns the original source call
at its own grade and retains the actual restored pool. -/
theorem typed_application_native_post
    {typingContext callContext : SourceSemantics.Context} {parameter result : TypeSystem.Ty}
    {callerEvidence : Dynamic.EvidenceEnvironment}
    (sourceTyped : Dynamic.ValueHasType typingContext before (.closure function) (.function parameter result))
    (size : Nat) {value : Value} {finalStore : Store}
    (completed : EvaluationSize size [CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual,
      DataPatternValues.packValues payloads] store CallableIndexedLambdaCalls.applyPayload value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.CallOutcome program sourceSize callContext callerEvidence function.evidence before
        (.closure function) arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : State headers keys ⟨callerScope, finalMap, finalWorld, after, finalStore, callerCanonical⟩,
        Relates caller reached ∧ poolObservations caller reached := by
  have captures := CallableIndexedOwnedCaptureValidity.captures_of_source_typed sourceTyped
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, finalHeaps, maps, worlds, preserved, metadata, reached, related⟩ :=
    CallableIndexedOwnedLambdaInvocationBounds.application_reflects_bounded_with captured code history inputs functions represented
      owner caller heaps captures reference carried (CallableIndexedLambdaTemplatePermission.lambda_allowed code history)
      closedBody size (fun child _ => empty_reflects code inputs originalBody emptyBody unitResult functions
        extension faithful observations functionTypes (by rfl) child) completed (Nat.le_refl _)
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, finalHeaps, maps, worlds, preserved, metadata,
    reached, related, reached_pool_observations related⟩
end Application

end Tests.SourceCoreClosedOwnedAnonymousInvocation
