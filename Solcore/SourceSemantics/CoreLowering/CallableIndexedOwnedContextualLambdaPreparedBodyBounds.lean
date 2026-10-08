import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaPreparedFlowBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaJointStaticReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMarkedAllocation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAllocationReadiness

/-! The actual joint body and owning Source issuance produce strict flow
members internally. Typed finish consumes them at the genuine parameter
entries, preserving the original reached exit and caller restoration. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaPreparedBodyBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedLexicalReadiness (readiness)
open CallableIndexedOwnedParameterReadyContinuations (bridge)
open CallableIndexedOwnedContextualLambdaSourceDiagnostics
open CallableIndexedOwnedContextualLambdaJointStaticReceipts (JointBody trackedFactory)
open CallableIndexedOwnedTypedLambdaBodyContinuations (Validity FlowPreserves FlowReflects)
open RecursiveNamedCatalogInvocationBounds (Below)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {named : CallableIndexedNamedGeneration.Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  (namedCompilation : CallableIndexedNamedGeneration.Compilation compiled.indexed named diagnostics namedCode)
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
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
      (faults := faults) (registry := registry) issued (bridge (headers := headers) (keys := keys)) functions table)

private def producer : ProtectedStateTransition.MarkedAllocation.Producer (protocol headers keys)
    compiled.indexed.layouts compiled.indexed.ancestry.layout.frame
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) :=
  CallableIndexedOwnedMarkedAllocation.producer headers keys
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)

private theorem acquire (location : Location) (native : NativeFrame)
    (stable : CallableIndexedOwnedAllocationProducer.StableOwner keys location native) :
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt
      (producer (headers := headers) (keys := keys) (registry := registry) functions).toOrdinary location native := by
  exact CallableIndexedOwnedAllocationProducer.readyAt_of_stableOwner
    (headers := headers) (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) stable

include extension faithful observations wellFormed rebuilt operandIncluded unaryIncluded interprets in
/-- All head and loop recipes come from this same prepared body. -/
theorem preserves_flow (budget : Nat)
    (meaning : ∀ context, Validity (program := Program.ofChecked compiled.sourceProgram) captured code context →
      RecursiveNamedHeaderContracts.AtMost budget (fun size =>
        CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt (bridge (headers := headers) (keys := keys))
          (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context function.evidence
          function.source (certificates body.readFuel function.source context) faults size)) :
    RecursiveNamedHeaderContracts.AtMost budget
      (FlowPreserves captured code body.toBody functions (registry := registry) (faults := faults)
        (headers := headers) (keys := keys)) := by
  exact CallableIndexedOwnedContextualLambdaPreparedFlowBounds.preserves_flow
    (active := code.active) (onError := code.allocationError)
    (expressionSyntax := expressionSyntax function.source) (certificates := certificates body.readFuel function.source)
    (administrative := captured.administrative) (registry := registry) (faults := faults)
    (factory := trackedFactory diagnosticPolicy function.source issued.invalidOperand)
    issued (bridge (headers := headers) (keys := keys)) functions rfl
    (CallableIndexedAmbient.frame_registered compiled.indexed) extension function.evidence faithful observations
    (CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (producer (headers := headers) (keys := keys) (registry := registry) functions)
    (acquire (headers := headers) (keys := keys) (registry := registry) functions)
    (administrativeTransport headers keys) (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys)
    body.unique wellFormed rebuilt operandIncluded unaryIncluded interprets budget
    (CallableIndexedOwnedLambdaSourceAdmission.runtime_at_parameters body.frame body.extended).1 meaning body.prepared

include extension faithful observations wellFormed rebuilt operandIncluded unaryIncluded interprets in
/-- Native children keep their strict grades; the Source grade remains independent. -/
theorem reflects_flow (budget : Nat) (functionTypes : FunctionRuntimeViews functions)
    (reflection : ∀ context, Validity (program := Program.ofChecked compiled.sourceProgram) captured code context →
      Below budget (fun size =>
        CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt (bridge (headers := headers) (keys := keys))
          (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context function.evidence
          function.source (certificates body.readFuel function.source context) faults size)) :
    Below budget (FlowReflects captured code body.toBody functions (registry := registry) (faults := faults)
      (headers := headers) (keys := keys)) := by
  exact CallableIndexedOwnedContextualLambdaPreparedFlowBounds.reflects_flow
    (active := code.active) (onError := code.allocationError)
    (expressionSyntax := expressionSyntax function.source) (certificates := certificates body.readFuel function.source)
    (administrative := captured.administrative) (registry := registry) (faults := faults)
    (factory := trackedFactory diagnosticPolicy function.source issued.invalidOperand)
    issued (bridge (headers := headers) (keys := keys)) functions rfl
    (CallableIndexedAmbient.frame_registered compiled.indexed) extension function.evidence faithful observations
    (CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (producer (headers := headers) (keys := keys) (registry := registry) functions)
    (acquire (headers := headers) (keys := keys) (registry := registry) functions)
    (administrativeTransport headers keys) (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys)
    body.unique wellFormed rebuilt operandIncluded unaryIncluded interprets budget
    (CallableIndexedOwnedLambdaSourceAdmission.runtime_at_parameters body.frame body.extended).1 functionTypes reflection body.prepared

variable (history : History code) (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {arguments : List Dynamic.Value} {nativeArguments : List Value} {before : Dynamic.Heap} {store : Store}
  {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (beforeTyped : Dynamic.HeapWellTyped function.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes function.context before arguments body.types)
  (stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows caller)

include extension faithful observations wellFormed rebuilt operandIncluded unaryIncluded interprets beforeTyped argumentsTyped stable in
/-- The strict expression family yields the local flow family and typed Source
finish at the actual parameter entry; no completed body premise is supplied. -/
theorem source_continuation (budget : Nat)
    (meaning : ∀ context, Validity (program := Program.ofChecked compiled.sourceProgram) captured code context →
      Below budget (fun size =>
        CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt (bridge (headers := headers) (keys := keys))
          (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context function.evidence
          function.source (certificates body.readFuel function.source context) faults size)) :
    CallableIndexedOwnedLambdaEntryBodyContracts.SourceContinuation
      (registry := registry) (faults := faults) (arguments := arguments) (nativeArguments := nativeArguments)
      captured code history body.toBody.toContext functions owner caller budget := by
  apply CallableIndexedOwnedTypedLambdaBodyContinuations.source_continuation
    captured code history body.toBody functions owner caller beforeTyped argumentsTyped stable wellFormed budget
  intro child strict
  exact preserves_flow namedCompilation captured code issued body functions extension faithful observations wellFormed
    rebuilt operandIncluded unaryIncluded interprets child
    (fun context valid size within => meaning context valid size (Nat.lt_of_le_of_lt within strict)) child (Nat.le_refl child)

include extension faithful observations wellFormed rebuilt operandIncluded unaryIncluded interprets beforeTyped argumentsTyped stable in
/-- The native flow and typed finish are derived from the same strict family. -/
theorem native_continuation (budget : Nat) (functionTypes : FunctionRuntimeViews functions)
    (reflection : ∀ context, Validity (program := Program.ofChecked compiled.sourceProgram) captured code context →
      Below budget (fun size =>
        CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt (bridge (headers := headers) (keys := keys))
          (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context function.evidence
          function.source (certificates body.readFuel function.source context) faults size)) :
    CallableIndexedOwnedLambdaEntryBodyContracts.NativeContinuation
      (registry := registry) (faults := faults) (arguments := arguments)
      captured code history body.toBody.toContext functions owner caller budget := by
  exact CallableIndexedOwnedTypedLambdaBodyContinuations.native_continuation
    captured code history body.toBody functions owner caller beforeTyped argumentsTyped stable wellFormed budget
    (reflects_flow namedCompilation captured code issued body functions extension faithful observations wellFormed
      rebuilt operandIncluded unaryIncluded interprets budget functionTypes reflection)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaPreparedBodyBounds
