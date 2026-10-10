import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedTypedLambdaProtocolContinuations
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaPreparedFlowBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaJointStaticReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOrdinaryLambdaEntries
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodLambdaEntries

/-! The actual JointBody supplies flow under the canonical authority retained
by its parameter packet. Ordinary and selected-method callers use their real
Nested and Origin protocols, marked allocation, binding and frame transport.
The original prepared head/loop producer consumes only smaller expression
members of this same protocol family. No bare base environment is upgraded to
a canonical packet, and no completed body or flow law is stored in Origin. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCanonicalFlowBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedContextualLambdaSourceDiagnostics
open CallableIndexedOwnedContextualLambdaJointStaticReceipts (JointBody trackedFactory)
open CallableIndexedOwnedTypedLambdaBodyContinuations (Validity)
open CallableIndexedOwnedTypedLambdaProtocolContinuations (FlowPreserves FlowReflects)
open RecursiveNamedCatalogInvocationBounds (Below)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}

/-- The finite caller form selects existing canonical operations. A principal
keeps its real Named identity; it is never converted into an ordinary Header.
Full method selection and dictionary authority remain in the actual Support. -/
inductive Origin (compiled : SourceCoreUnifiedCompilation.Compiled) where
  | ordinary (caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
  | principal (named : CallableIndexedNamedGeneration.Named)

namespace Origin
variable (origin : Origin compiled) (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)

def protocol : ProtectedStateTransition.Protocol (Records keys) :=
  match origin with
  | .ordinary caller => CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller
  | .principal named => CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner named

def bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier
    (headers := headers) (fun _ => True) (protocol (headers := headers) origin owner) :=
  match origin with
  | .ordinary caller => CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller
  | .principal named => CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner named

def transport : ProtectedStateTransition.AdministrativeTransport (protocol (headers := headers) origin owner) :=
  match origin with
  | .ordinary caller => CallableIndexedOwnedNestedCanonicalState.administrativeTransport owner caller
  | .principal named => CallableIndexedOwnedOriginCanonicalState.administrativeTransport owner named

def bindings : ProtectedStateTransition.Bindings (protocol (headers := headers) origin owner) :=
  match origin with
  | .ordinary caller => CallableIndexedOwnedNestedCanonicalState.bindings owner caller
  | .principal named => CallableIndexedOwnedOriginCanonicalState.bindings owner named

variable {registry : SourceCoreRawMetadata.Registry}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))

/-- Each branch is the original packet-preserving allocator, including its
actual returned ordered pool. No allocation execution contract is supplied. -/
def producer : ProtectedStateTransition.MarkedAllocation.Producer
    (protocol (headers := headers) origin owner) compiled.indexed.layouts compiled.indexed.ancestry.layout.frame
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) :=
  match origin with
  | .ordinary caller => CallableIndexedOwnedNestedCanonicalState.markedProducer owner caller
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
  | .principal named => CallableIndexedOwnedOriginCanonicalState.markedProducer owner named
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)

theorem acquire (location : Location) (native : NativeFrame)
    (stable : CallableIndexedOwnedAllocationProducer.StableOwner keys location native) :
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt
      (producer (headers := headers) (registry := registry) origin owner functions).toOrdinary location native := by
  cases origin with
  | ordinary caller =>
      exact CallableIndexedOwnedNestedCanonicalState.readyAt_of_stableOwner owner caller
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) stable
  | principal named =>
      exact CallableIndexedOwnedOriginCanonicalState.readyAt_of_stableOwner owner named
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) stable
end Origin

variable
  {named : CallableIndexedNamedGeneration.Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  (namedCompilation : CallableIndexedNamedGeneration.Compilation compiled.indexed named diagnostics namedCode)
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {capturedActual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured capturedActual)
  (code : Code compiled.indexed function scope captured.administrative)
  (issued : IssuedSource compiled code.compilation.owner function.source)
  {expressionSyntax : TypedSource → ExpressionId → Prop}
  {certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (body : JointBody namedCompilation code (Program.ofChecked compiled.sourceProgram) expressionSyntax certificates
    diagnosticPolicy issued.invalidOperand issued.invalidUnary issued.invalidProjection issued.missingDefault)
  (origin : Origin compiled) (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  {table : SourceCoreFaultSites.Table}
  (rebuilt : issued.diagnostics.tableForRegistry registry extension = .ok table)
  (operandIncluded : ∀ reason token, GenericAssignmentDiagnostics.OperandRep issued.assignments reason token → faults reason token)
  (unaryIncluded : ∀ reason token, EmittedDiagnosticTokenPlan.UnaryRep issued.assignments reason token → faults reason token)
  (interprets : ∀ context, Validity (program := Program.ofChecked compiled.sourceProgram) captured code context →
    CallableIndexedOwnedContextualLambdaAssignmentReadiness.ReachedInterpretations
      (context := context) (certificates := certificates body.readFuel function.source)
      (administrative := captured.administrative)
      (factory := trackedFactory diagnosticPolicy function.source issued.invalidOperand)
      (faults := faults) (registry := registry) issued
      (Origin.bridge (headers := headers) origin owner) functions table)

include extension faithful observations wellFormed rebuilt operandIncluded unaryIncluded interprets in
/-- The same prepared flow is closed from E at sizes at most budget. The
original finite head and loop operations are constructed internally once. -/
theorem preserves_flow (budget : Nat)
    (meaning : ∀ context, Validity (program := Program.ofChecked compiled.sourceProgram) captured code context →
      RecursiveNamedHeaderContracts.AtMost budget (fun size =>
        CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt (Origin.bridge (headers := headers) origin owner)
          (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context function.evidence
          function.source (certificates body.readFuel function.source context) faults size)) :
    RecursiveNamedHeaderContracts.AtMost budget
      (FlowPreserves captured code body.toBody functions (Origin.bridge (headers := headers) origin owner)
        (registry := registry) (faults := faults)) := by
  exact CallableIndexedOwnedContextualLambdaPreparedFlowBounds.preserves_flow
    (active := code.active) (onError := code.allocationError)
    (expressionSyntax := expressionSyntax function.source) (certificates := certificates body.readFuel function.source)
    (administrative := captured.administrative) (registry := registry) (faults := faults)
    (factory := trackedFactory diagnosticPolicy function.source issued.invalidOperand)
    issued (Origin.bridge (headers := headers) origin owner) functions rfl
    (CallableIndexedAmbient.frame_registered compiled.indexed) extension function.evidence faithful observations
    (CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (Origin.producer (headers := headers) (registry := registry) origin owner functions)
    (Origin.acquire (headers := headers) (registry := registry) origin owner functions)
    (Origin.transport (headers := headers) origin owner) (Origin.bindings (headers := headers) origin owner)
    body.unique wellFormed rebuilt operandIncluded unaryIncluded interprets budget
    (CallableIndexedOwnedLambdaSourceAdmission.runtime_at_parameters body.frame body.extended).1 meaning body.prepared

include extension faithful observations wellFormed rebuilt operandIncluded unaryIncluded interprets in
/-- F reflection consumes the native strict E family; its Source grade is
independent. The same actual JointBody and receiving table are retained. -/
theorem reflects_flow (budget : Nat) (functionTypes : FunctionRuntimeViews functions)
    (reflection : ∀ context, Validity (program := Program.ofChecked compiled.sourceProgram) captured code context →
      Below budget (fun size =>
        CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt (Origin.bridge (headers := headers) origin owner)
          (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context function.evidence
          function.source (certificates body.readFuel function.source context) faults size)) :
    Below budget (FlowReflects captured code body.toBody functions (Origin.bridge (headers := headers) origin owner)
      (registry := registry) (faults := faults)) := by
  exact CallableIndexedOwnedContextualLambdaPreparedFlowBounds.reflects_flow
    (active := code.active) (onError := code.allocationError)
    (expressionSyntax := expressionSyntax function.source) (certificates := certificates body.readFuel function.source)
    (administrative := captured.administrative) (registry := registry) (faults := faults)
    (factory := trackedFactory diagnosticPolicy function.source issued.invalidOperand)
    issued (Origin.bridge (headers := headers) origin owner) functions rfl
    (CallableIndexedAmbient.frame_registered compiled.indexed) extension function.evidence faithful observations
    (CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (Origin.producer (headers := headers) (registry := registry) origin owner functions)
    (Origin.acquire (headers := headers) (registry := registry) origin owner functions)
    (Origin.transport (headers := headers) origin owner) (Origin.bindings (headers := headers) origin owner)
    body.unique wellFormed rebuilt operandIncluded unaryIncluded interprets budget
    (CallableIndexedOwnedLambdaSourceAdmission.runtime_at_parameters body.frame body.extended).1 functionTypes reflection body.prepared

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCanonicalFlowBounds
