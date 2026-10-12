import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectArgumentPrefix
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedReceivingFirstCallGateRejection
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicDecodedStagedCallFaults
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectStageBoundary

/-! Actual first-gate rejection combines the original native failure producer
with the exact receiving stage diagnostic. The callee's concrete reached state
supplies the parent stage post. A strict child proof and the actual reflected
argument prefix feed this constructor; broader dispatch remains separate. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectFirstGateBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters (Prepared)
open CallableIndexedOwnedPreparedStagedIndirectNativePrefix (CalleePost)
open CallableIndexedOwnedPreparedScopedCallBoundaryReceipts (CallView)
open CallableIndexedOwnedContextualDiagnosticSources (SourceView)
open CallableIndexedOwnedSelectedCallCodebookReceipts (Selected)
open CallableIndexedOwnedPublicFaultReceiverTables (IssuedAt)
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

section Constructor
variable
  (functionModel : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked
  completion.result.context.registry functionModel
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
  completion.result.diagnostics

include receiver prepared stagePrepared sourceEq occurrence view guardFrame in
/-- Both the Source parent and native parent stop at the actual callee endpoint.
The literal selected token and receiver lookup establish the stage relation;
the same reached child witness supplies stable rows for the parent. -/
theorem result_at_rejected
    {childSize : Nat} {sourceValue : Dynamic.Value} {after : Dynamic.Heap}
    {carrier : Value} {calleeStore : Store} {finalMap : LocationMap} {finalWorld : StoreTyping}
    (child : Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages childSize
      invocation context environment before callee (.value sourceValue) after)
    (post : CalleePost (registry := completion.result.context.registry) (context := context)
      (actual := actual) (ξ := ξ) (calleeNode := calleeNode)
      bridge functionModel compiler initial sourceValue after carrier calleeStore finalMap finalWorld)
    {originalNode : ExpressionNode} {originalMetadata : IndirectCallResolution}
    (callView : CallView originalNode compiler.original originalMetadata metadata)
    (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar)
      prepared.site prepared.site.call ids sourceValue carrier)
    (selected : Selected sidecar prepared.site callee ids originalMetadata originalNode dispatch.row)
    {reason : Staging.CallGuard.Fault}
    (rejected : Staging.CallBoundary.GuardRejects invocation.guards id ids sourceValue reason) :
    Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages
      (Staging.Recursive.Size.stepSize [childSize]) invocation context environment before id
      (.fault (.stage invocation id reason)) after ∧
    CallableIndexedOwnedPreparedStagedIndirectCalleeFaultBounds.ResultAt
      (registry := completion.result.context.registry) (faults := callFaults) (context := context)
      (actual := actual) (ξ := ξ) bridge functionModel compiler initial
      (.stage invocation id reason) after (dispatch.reason reason) calleeStore finalMap finalWorld := by
  obtain ⟨calleeEvaluation, _payload, calleeHeaps, maps, worlds, frame, heapMetadata,
    reached, related, calleeAdmission⟩ := post
  have actualRejected : Staging.CallBoundary.GuardRejects (CallableLedger.frame sidecar)
      prepared.site.call ids sourceValue reason := by
    simpa only [guardFrame, prepared.call] using rejected
  have shaped := calleeEvaluation
  rw [dispatch.shape] at shaped
  have whole := prepared.site.lower_stage_failure (result := compiler.resultType)
    (arguments := (SourceCoreCalls.packArguments compiler.codes).expression.rename ξ)
    compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown dispatch.row
    (CallStageGuard.error dispatch.guard.sidecar.caller dispatch.guard.node dispatch.guard.contract.owner reason)
    dispatch.found (dispatch.rejected actualRejected) shaped
  have loweredType : lowered.type = compiler.resultType :=
    (congrArg (fun output => output.type) compiler.output).trans compiler.resultTypeEq.symm
  have evaluated : Evaluates actual store (lowered.expression.rename ξ)
      (.inLeft lowered.type (.word (dispatch.reason reason))) calleeStore := by
    simpa only [SourceCoreCallableContracts.Callsite.lower, CallStageBoundary.Dispatch.reason,
      prepared.lowered_rename compiler ξ, loweredType] using whole
  have receiving :=
    CallableIndexedOwnedPreparedReceivingFirstCallGateRejection.receiving_staged_post
      (sourceResult := compiler.original.type) (resultCore := lowered.type)
      compiler prepared stagePrepared dispatch selected receiver sourceEq view callView guardFrame
      (by simpa only [prepared.call] using rejected) initial functionModel reached related calleeHeaps
  have represented : RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
      compiler.original.type lowered.type callFaults
      (.fault (.stage invocation id reason)) (.inLeft lowered.type (.word (dispatch.reason reason))) := by
    have common := CallableIndexedOwnedPublicDecodedStagedCallFaults.first_gate_result model receiving.1
    simpa only [prepared.call] using common
  have parentAdmission : CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
      bridge context compiler.original.type (.fault (.stage invocation id reason)) reached :=
    calleeAdmission.rows
  exact ⟨.rejected occurrence child rejected, evaluated, represented, calleeHeaps,
    maps, worlds, frame, heapMetadata, reached, related, parentAdmission⟩

end Constructor

section PositiveModel
variable {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}
  (certified : certificate scope callee compiler.calleeCode)
  (found : source.lookupExpression? callee = some calleeNode)
  (sourceTyped : ExpressionHasType source context callee calleeNode.type)
  {administrative actualContext : Core.Context}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked completion.result.context.registry
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile)
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

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys
  bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked
  completion.result.context.registry functions
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
  completion.result.diagnostics

include receiver prepared stagePrepared sourceEq occurrence certified found sourceTyped
  environments heaps locals agrees typed admitted caller view originalUnique guardFrame
  sourceParent tree unique parentTyped in
/-- Strict Source descent supplies the actual successful callee post. Positive
payload and original Source rows construct its scoped boundary. A genuine
rejection excludes the builtin branch and invokes the concrete parent once. -/
theorem preserves_rejected (budget : Nat)
    (children : CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow
      bridge context model stages invocation certificate faults budget)
    {childSize : Nat} {sourceValue : Dynamic.Value} {after : Dynamic.Heap}
    (child : Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages childSize
      invocation context environment before callee (.value sourceValue) after)
    (within : Staging.Recursive.Size.stepSize [childSize] ≤ budget)
    {reason : Staging.CallGuard.Fault}
    (rejected : Staging.CallBoundary.GuardRejects invocation.guards id ids sourceValue reason) :
    Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages
      (Staging.Recursive.Size.stepSize [childSize]) invocation context environment before id
      (.fault (.stage invocation id reason)) after ∧
    ∃ token finalStore finalMap finalWorld,
      CallableIndexedOwnedPreparedStagedIndirectCalleeFaultBounds.ResultAt
        (registry := completion.result.context.registry) (faults := callFaults) (context := context)
        (actual := actual) (ξ := ξ) bridge functions compiler initial
        (.stage invocation id reason) after token finalStore finalMap finalWorld := by
  have smaller : childSize < budget := Nat.lt_of_lt_of_le
    (Staging.Recursive.Size.child_lt_stepSize (child := childSize) (children := [childSize]) (by simp)) within
  have actualFound : invocation.source.lookupExpression? callee = some calleeNode := by
    rw [sourceEq]; exact found
  have actualTyped : ExpressionHasType invocation.source context callee calleeNode.type := by
    rw [sourceEq]; exact sourceTyped
  obtain ⟨value, calleeStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, heapMetadata, reached, related, calleeAdmission⟩ :=
    children childSize smaller certified actualFound actualTyped environments heaps locals agrees typed initial admitted child
  cases represented with
  | value payload =>
      have actualPost : ∃ carrier, CalleePost (registry := completion.result.context.registry) (context := context)
          (actual := actual) (ξ := ξ) (calleeNode := calleeNode)
          bridge functions compiler initial sourceValue after carrier calleeStore finalMap finalWorld :=
        ⟨_, evaluated, payload, finalHeaps, maps, worlds, frame, heapMetadata,
          reached, related, calleeAdmission⟩
      obtain ⟨carrier, post⟩ := actualPost
      obtain ⟨originalNode, originalMetadata, _contains, _form, callView, boundary⟩ :=
        CallableIndexedOwnedPreparedStagedIndirectArgumentPrefix.scoped_boundary
          (sourceEq := sourceEq) (found := found) (sourceParent := sourceParent)
          (tree := tree) (unique := unique) (parentTyped := parentTyped)
          bridge profile compiler prepared initial caller view originalUnique post
      cases boundary with
      | user dispatch selected =>
          obtain ⟨trace, result⟩ := result_at_rejected bridge receiver compiler prepared stagePrepared
            sourceEq occurrence initial view guardFrame functions child post callView dispatch selected rejected
          exact ⟨trace, dispatch.reason reason, calleeStore, finalMap, finalWorld, result⟩
      | @builtin function carrier row receipt =>
          exact False.elim (Staging.CallBoundary.GuardAccepts.not_rejects
            (.builtin function) rejected)

include receiver prepared stagePrepared sourceEq occurrence view guardFrame in
/-- The real reflected first-gate prefix already retains its strict native
callee and independent Source grade. Its literal selected row supplies the
receiving token, completing this branch at the same final store and witness. -/
theorem reflects_rejected_prefix (budget : Nat) {value : Value} {finalStore : Store}
    (rejectedPrefix : CallableIndexedOwnedPreparedStagedIndirectArgumentPrefix.StageRejectedPrefix
      (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (registry := completion.result.context.registry) (context := context) (stages := stages)
      (invocation := invocation) (environment := environment) (actual := actual) (ξ := ξ)
      (calleeNode := calleeNode) (sidecar := sidecar) bridge profile compiler prepared initial
      budget value finalStore) :
    ∃ sourceSize reason after token finalMap finalWorld,
      Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages sourceSize
        invocation context environment before id (.fault (.stage invocation id reason)) after ∧
      value = .inLeft lowered.type (.word token) ∧
      CallableIndexedOwnedPreparedStagedIndirectCalleeFaultBounds.ResultAt
        (registry := completion.result.context.registry) (faults := callFaults) (context := context)
        (actual := actual) (ξ := ξ) bridge functions compiler initial
        (.stage invocation id reason) after token finalStore finalMap finalWorld := by
  obtain ⟨_nativeSize, childSize, sourceValue, after, carrier, calleeStore, finalMap, finalWorld,
    originalNode, originalMetadata, reason, _native, _strict, child, post, callView,
    dispatch, selected, rejected, _trace, valueEq, storeEq⟩ := rejectedPrefix
  subst finalStore
  obtain ⟨trace, result⟩ := result_at_rejected bridge receiver compiler prepared stagePrepared
    sourceEq occurrence initial view guardFrame functions child post callView dispatch selected rejected
  exact ⟨Staging.Recursive.Size.stepSize [childSize], reason, after, dispatch.reason reason,
    finalMap, finalWorld, trace, valueEq, result⟩

end PositiveModel
end Calls
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectFirstGateBounds
