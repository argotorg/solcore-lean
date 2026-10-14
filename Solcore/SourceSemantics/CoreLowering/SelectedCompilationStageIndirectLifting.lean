import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageIndirectNamedLifting
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageIndirectClosureLifting
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageLiftBuiltin
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageApplicationArity
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageNamedInvocationLifting
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedArgumentRows
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalProgramSupport

/-! The actual indirect head lifts its callee and first guard, then arguments
and the selected named, closure or builtin application at the genuine heap. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2200000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageIndirectLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPreparedStagedSelectedGeneralCallHeadBounds (Port)
open SelectedCompilationPhysicalProgramSupport (Support stages functions stagePrepared)
open SelectedCompilationStageBodyLiftBounds (NamedLiftsBelow)
open Staging.Recursive.Lifting (ApplicationLift)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {receiver : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (support : Support compiled headers keys receiver)
  {registry : SourceCoreRawMetadata.Registry}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (physical : ∀ {index}, callerProtocol.State index → CallableIndexedOwnedPhysicalGlobals.Authority compiled index.mapping index.store)
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation invocation.source scope
    id callee ids metadata reasonAt lowered)
  (port : Port (compiled := compiled) (invocation := invocation) compiler)
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
  (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
  (unique : NodeOccurrencesUnique invocation.source)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (functions support)

include support port physical runtime actualFunctionType unique in
theorem indirect {children : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}
    (budget : Nat)
    (calleeCertified : children scope callee compiler.calleeCode)
    {sourceTypes : List TypeSystem.Ty}
    (tree : DataExpressionSequence.Tree invocation.source children scope ids sourceTypes compiler.codes)
    (childLift : ∀ size, size < budget → SelectedCompilationStageLiftBounds.LiftsAt
      bridge context model (stages compiled) invocation children size)
    (preservation : ∀ size, CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesAt
      bridge context model (stages compiled) invocation children faults size)
    (namedBodies : ∀ header, header ∈ headers → ∀ child,
      (stages compiled).Closure header.function child →
      NamedLiftsBelow (headers := headers) (keys := keys) header model (stages compiled) child budget)
    (closureBodies : ∀ {mapping world function native bindings parameterCore resultCore}
      (association : CallableIndexedOwnedPhysicalClosureAssociation.Association headers keys
        receiver.result.context.registry
        (CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.result.diagnostics)
        mapping world function native bindings parameterCore resultCore),
      SelectedCompilationStageClosurePacketLifting.BelowFor model (stages compiled)
        association.original (support.closurePackets association) budget) :
    SelectedCompilationStageLiftBounds.LiftsAt bridge context model (stages compiled) invocation
      (CallableIndexedOwnedPreparedStagedSelectedGeneralCallHeadBounds.Point scope id lowered) budget := by
  letI : CallableIndexedOwnedPositiveFunctionModels.ErasesToContextual headers keys receiver.result.context.registry
      (CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.result.diagnostics) support.profile (functions support) :=
    CallableIndexedOwnedPositiveFunctionModels.physical support.profile
  intro current expression code point actualNode found parentTyped
    mapping world administrative environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees typed initial admitted execution
  obtain ⟨rfl, rfl, rfl⟩ := point
  cases Option.some.inj (found.symm.trans compiler.found)
  obtain ⟨_parameter, _result, _rawTypes, calleeTyped, _argumentsTyped, _bundle, _resultType⟩ :=
    CallableIndexedOwnedPreparedStagedRecursiveCallerSourceReceipts.original_child_types
      compiler port.sourceParent unique parentTyped
  have reported := CallableIndexedOwnedContextualInitializedClosureReceipts.reported_type_at
    unique port.calleeFound calleeTyped
  have sourceTyped : ExpressionHasType invocation.source context callee port.calleeNode.type := by
    simpa only [reported] using calleeTyped
  have occurrence : Staging.Recursive.Occurrence invocation expression (.call callee ids (.indirect metadata)) :=
    ⟨compiler.original, lookupExpression?_sound compiler.found, compiler.originalForm,
      port.sourceParent.requirements, port.sourceParent.coercions⟩
  rcases SelectedCompilationStageIndirectPrefixLifting.lift_prefix
    (bodyRegistry := receiver.result.context.registry)
    (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.result.diagnostics)
    (functions := functions support) bridge support.profile compiler port
    calleeCertified sourceTyped tree unique parentTyped environments heaps locals agrees typed initial admitted
    budget childLift preservation execution (Nat.le_refl _) with complete | application
  · exact complete
  · obtain ⟨_calleeSize, _argumentsSize, _callSize, sourceValue, _calleeHeap, _argumentsHeap, _sources, _callEvidence,
      calleeTrace, accepted, argumentsTrace, called, smaller, prefixResult⟩ := application
    have lifted : ApplicationLift (Program.ofChecked compiled.sourceProgram) (stages compiled) invocation context _argumentsHeap
        sourceValue _sources outcome after := by
      cases accepted with
      | builtin function => exact ⟨_, _, SelectedCompilationStageLiftBuiltin.builtin_application called.sound, .completed⟩
      | contract bound _passing =>
        cases invocation.guards.userCallable bound with
        | global function =>
          exact SelectedCompilationStageIndirectNamedLifting.named_application support bridge physical compiler port
            runtime actualFunctionType initial budget namedBodies argumentsTrace prefixResult called (Nat.le_of_lt smaller)
        | closure function =>
          exact SelectedCompilationStageIndirectClosureLifting.closure_application support bridge physical compiler port
            runtime actualFunctionType initial budget closureBodies argumentsTrace prefixResult called (Nat.le_of_lt smaller)
    obtain ⟨staged, reached, applied, adapted⟩ := lifted
    exact ⟨staged, reached, .applied occurrence compiler.argumentCoercions calleeTrace.sound accepted
      argumentsTrace.sound port.sourceParent.arity applied, adapted⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageIndirectLifting
