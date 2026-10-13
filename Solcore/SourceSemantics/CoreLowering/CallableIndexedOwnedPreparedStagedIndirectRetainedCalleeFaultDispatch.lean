import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPositiveFunctionModels
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectFaultDispatch
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectRetainedCalleeArgumentPrefix

/-! The actual whole native parent retains its successful callee receipt through ordered arguments. Fault branches preserve the original result; the successful branch exposes the same reached suffix and callee typing to its application producer. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectRetainedCalleeFaultDispatch
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters (Prepared)
open CallableIndexedOwnedContextualDiagnosticSources (SourceView)
open CallableIndexedOwnedPublicFaultReceiverTables (IssuedAt)
open CallableIndexedOwnedPreparedStagedIndirectFaultDispatch (FaultResult)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
    completion.result.extension completion.result.diagnostics)
  {context : SourceSemantics.Context}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}

section Calls
variable {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  (prepared : Prepared compiler compiled.indexed.ancestry.graph.inputs.callable)
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)
  (sourceEq : invocation.source = source)
  (occurrence : Staging.Recursive.Occurrence invocation id (.call callee ids (.indirect metadata)))
  {calleeNode : ExpressionNode}
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  {sidecar : SourceCoreStageContracts.Sidecar}
  (view : SourceView sidecar.source source)
  (guardFrame : invocation.guards = CallableLedger.frame sidecar)

section PositiveModel
variable {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {functionModel : CallableIndexedOwnedPositiveFunctionModels.Receiving
    headers keys bodyRegistry semanticFaults profile}
  [positive : CallableIndexedOwnedPositiveFunctionModels.ErasesToContextual
    headers keys bodyRegistry semanticFaults profile functionModel]
  {certificate : GenericExpressionMeaning.Certificate}
  (certified : certificate scope callee compiler.calleeCode)
  (found : source.lookupExpression? callee = some calleeNode)
  (sourceTyped : ExpressionHasType source context callee calleeNode.type)
  {administrative actualContext : Core.Context}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked completion.result.context.registry
    (functionModel)
    mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (admitted : Admission bridge context initial)
  (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (originalUnique : NodeOccurrencesUnique sidecar.source)
  (sourceParent : CallableIndexedOwnedIndirectSourceAdapters.SourceParent compiler)
  {sourceTypes : List TypeSystem.Ty}
  (tree : DataExpressionSequence.Tree invocation.source certificate scope ids sourceTypes compiler.codes)
  (unique : NodeOccurrencesUnique invocation.source)
  (parentTyped : ExpressionHasType invocation.source context id compiler.original.type)

local notation "functions" => functionModel
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked
  completion.result.context.registry functions
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
  completion.result.diagnostics

include positive receiver prepared stagePrepared sourceEq occurrence certified found sourceTyped
  environments heaps locals agrees typed admitted caller view originalUnique guardFrame
  sourceParent tree unique parentTyped in
/-- The actual whole parent is inverted once. Every reached callee, first-gate
or ordered-argument failure becomes its exact parent result. Successful
arguments retain the authentic application suffix for its concrete producer. -/
theorem reflects_fault_or_application (budget : Nat)
    (children : CallableIndexedOwnedAdmittedStagedExpressionBounds.ReflectsBelow
      bridge context model stages invocation certificate callFaults budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore)
    (within : size ≤ budget) :
    FaultResult (functionModel := functionModel) (completion := completion) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (stages := stages) (invocation := invocation)
      (environment := environment) (actual := actual) (ξ := ξ)
      bridge compiler initial profile value finalStore ∨
    CallableIndexedOwnedPreparedStagedIndirectRetainedCalleeArgumentPrefix.ApplicationPrefix (functionModel := functionModel)
      (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (registry := completion.result.context.registry) (context := context)
      (stages := stages) (invocation := invocation) (environment := environment)
      (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeNode := calleeNode) (sidecar := sidecar)
      bridge profile compiler prepared initial budget value finalStore := by
  rcases CallableIndexedOwnedPreparedStagedIndirectRetainedCalleeArgumentPrefix.reflects_arguments
      bridge profile compiler prepared sourceEq occurrence certified found sourceTyped
      environments heaps locals agrees typed initial admitted caller view originalUnique
      guardFrame sourceParent tree unique parentTyped budget children completed within with
    calleeFault | stageRejected | argumentFault | application
  · obtain ⟨_nativeSize, sourceSize, failure, token, after, finalMap, finalWorld,
      _native, _strict, _child, parentTrace, valueEq, post⟩ := calleeFault
    exact .inl ⟨Staging.Recursive.Size.stepSize [sourceSize], failure, after, token,
      finalMap, finalWorld, parentTrace, valueEq, post⟩
  · obtain ⟨sourceSize, reason, after, token, finalMap, finalWorld,
      parentTrace, valueEq, post⟩ :=
      CallableIndexedOwnedPreparedStagedIndirectFirstGateBounds.reflects_rejected_prefix
        bridge receiver compiler prepared stagePrepared sourceEq occurrence initial
        view guardFrame profile budget stageRejected
    exact .inl ⟨sourceSize, .stage invocation id reason, after, token,
      finalMap, finalWorld, parentTrace, valueEq, post⟩
  · obtain ⟨calleeSize, argumentsSize, sourceValue, calleeHeap, failure, after,
      token, finalMap, finalWorld, _callee, _accepted, _arguments,
      parentTrace, valueEq, post⟩ := argumentFault
    exact .inl ⟨Staging.Recursive.Size.stepSize [calleeSize, argumentsSize],
      failure, after, token, finalMap, finalWorld, parentTrace, valueEq, post⟩
  · exact .inr application

end PositiveModel
end Calls
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectRetainedCalleeFaultDispatch
