import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalClosureUserDispatch
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedFiniteClosureParentBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectBuiltinApplicationDispatch

/-! The retained user prefix selects its genuine closure or global Source
value. A closure's physical count is decided at the actual argument endpoint.
Mismatch constructs the original semantic arity parent; equal count invokes the
same retained contextual Code through its finite body producer. The genuine
global prefix remains available for the independent named-body producer. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedFiniteClosureUserDispatch
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)
open CallableIndexedOwnedPreparedStagedFiniteClosureParentBounds (FiniteFor)
open CallableIndexedOwnedPreparedStagedTerminalClosureUserDispatch (GlobalApplicationPrefix)
open CallableIndexedOwnedPreparedStagedIndirectBuiltinApplicationDispatch (UserApplicationPrefix ParentResult)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry}
  {invocation : Staging.Recursive.Scope}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  (prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler
    compiled.indexed.ancestry.graph.inputs.callable)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  {sourceTypes : List TypeSystem.Ty} {calleeNode : ExpressionNode}
  {sidecar : SourceCoreStageContracts.Sidecar}

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked
  completion.result.context.registry functions
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

variable (sourceParent : CallableIndexedOwnedIndirectSourceAdapters.SourceParent compiler)
  (occurrence : Staging.Recursive.Occurrence invocation id (.call callee ids (.indirect metadata)))
  (preparedStages : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
  (covers : invocation.evidence.Covers context)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  {certificate : GenericExpressionMeaning.Certificate}
  (sourceEq : invocation.source = source)
  (tree : DataExpressionSequence.Tree invocation.source certificate scope ids sourceTypes compiler.codes)
  (unique : NodeOccurrencesUnique invocation.source)
  (parentTyped : ExpressionHasType invocation.source context id compiler.original.type)
  (calleeFound : source.lookupExpression? callee = some calleeNode)
  (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry
    completion.result.context.registry)
  (semantic : ∀ reason token, semanticFaults reason token →
    CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token)

include sourceParent occurrence preparedStages receiver wellFormed runtime covers locals sourceEq tree unique parentTyped calleeFound actualFunctionType extension semantic in
/-- User classification and physical arity happen inside the actual retained
prefix. The closure branch constructs full parent meaning; only the literal
global application remains for the separate named producer. -/
theorem reflects_closure_or_global
    (packets : ∀ {mapping world function native bindings parameterCore resultCore}
      (association : Association headers keys bodyRegistry semanticFaults mapping world function native
        bindings parameterCore resultCore),
      Nonempty (FiniteFor (registry := completion.result.context.registry) (stages := stages) association))
    {budget size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore)
    (user : UserApplicationPrefix (completion := completion) (bodyRegistry := bodyRegistry)
      (semanticFaults := semanticFaults) (context := context) (stages := stages) (invocation := invocation)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeNode := calleeNode) (sidecar := sidecar) bridge profile compiler prepared initial budget value finalStore) :
    ParentResult (completion := completion) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (stages := stages) (invocation := invocation) (environment := environment)
      (actual := actual) (ξ := ξ) bridge profile compiler initial value finalStore ∨
    GlobalApplicationPrefix (completion := completion) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (stages := stages) (invocation := invocation) (environment := environment)
      (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes) (calleeNode := calleeNode) (sidecar := sidecar)
      bridge profile compiler prepared initial budget value finalStore := by
  have originalTree : DataExpressionSequence.Tree source certificate scope ids sourceTypes compiler.codes := by
    simpa only [sourceEq] using tree
  have originalUnique : NodeOccurrencesUnique source := by simpa only [sourceEq] using unique
  have originalTyping : ExpressionHasType source context id compiler.original.type := by
    simpa only [sourceEq] using parentTyped
  obtain ⟨_parameter, _result, _calleeType, argumentsTyped, _bundle, _resultType⟩ :=
    CallableIndexedOwnedIndirectSourceTypeRows.original_rows compiler sourceParent
      originalTree originalUnique originalTyping calleeFound
  have typing : ExpressionsHaveTypes invocation.source context ids sourceTypes := by
    simpa only [sourceEq] using argumentsTyped
  obtain ⟨sourceValue, userKind, rawParameter, rawResult, functionType, bundle, originalResult,
    calleeSize, argumentsSize, calleeHeap, calleeStore, calleeMap, calleeWorld, sources, values, carrier,
    argumentsHeap, argumentsStore, finalMap, finalWorld, originalNode, originalMetadata, tail⟩ := user
  cases userKind with
  | global function =>
    exact .inr ⟨function, rawParameter, rawResult, functionType, bundle, originalResult,
      calleeSize, argumentsSize, calleeHeap, calleeStore, calleeMap, calleeWorld, sources, values, carrier,
      argumentsHeap, argumentsStore, finalMap, finalWorld, originalNode, originalMetadata, tail⟩
  | closure function =>
    obtain ⟨calleePost, calleeTyped, calleeTrace, accepted, argumentsTrace, represented, calleeRelated,
      _callView, boundary, heaps, maps, worlds, frame, heapMetadata, ⟨reached, related, admitted⟩,
      suffixSize, suffix, strict⟩ := tail
    cases boundary with
    | user dispatch selected =>
      by_cases same : dispatch.row.entry.parameterCount = ids.length
      · obtain ⟨_nativeCallee, _representedCallee, _calleeHeaps, _calleeMaps, _calleeWorlds,
          _calleeFrame, calleeMetadata, calleeReached, _calleeRelated, calleeAdmission⟩ := calleePost
        have calleeHeapTyped := calleeAdmission.at_value.2.heap
        have rawCallee : Dynamic.ValueHasType context calleeHeap (.closure function)
            (.function rawParameter rawResult) := by
          simpa only [functionType] using calleeTyped
        have relatedCallee : CallableIndexedOwnedContextualCellOrigins.PayloadOrigins
            headers keys bodyRegistry completion.result.context.registry semanticFaults profile finalMap finalWorld
            (.function rawParameter rawResult) (.closure function) carrier compiler.calleeCode.type := by
          change GenericHeap.PayloadModel.Represents model finalMap finalWorld
            (.function rawParameter rawResult) (.closure function) carrier compiler.calleeCode.type
          simpa only [functionType] using calleeRelated
        obtain ⟨sourceSize, outcome, after, returnedMap, returnedWorld, trace, resultRep, returnedHeaps,
          returnedMaps, returnedWorlds, returnedFrame, returnedMetadata, returned, returnedRelated, returnedPost⟩ :=
          CallableIndexedOwnedPreparedStagedFiniteClosureParentBounds.reflects_suffix
            bridge profile compiler prepared sourceParent occurrence initial reached related admitted
            heaps maps worlds frame heapMetadata dispatch selected same accepted wellFormed runtime covers
            (locals.mono calleeMetadata) calleeHeapTyped typing rawCallee actualFunctionType relatedCallee
            represented bundle originalResult extension semantic packets budget calleeTrace argumentsTrace suffix
            (Nat.le_of_lt strict)
        exact .inl ⟨sourceSize, outcome, after, returnedMap, returnedWorld, trace, completed.sound,
          resultRep, returnedHeaps, returnedMaps, returnedWorlds, returnedFrame, returnedMetadata,
          returned, returnedRelated, returnedPost⟩
      · have physical := CallableIndexedOwnedStoredClosureArityBoundary.parameter_count dispatch selected
        have failedSource := CallableIndexedOwnedPreparedSecondCallGateRejection.closure_source
          occurrence compiler.argumentCoercions sourceParent.arity argumentsTrace calleeTrace accepted
          (by simpa only [physical] using same)
        have lowerType : lowered.type = compiler.resultType :=
          (congrArg (fun output => output.type) compiler.output).trans compiler.resultTypeEq.symm
        obtain ⟨sameValue, sameStore⟩ :=
          CallableIndexedOwnedPreparedStagedIndirectSecondGateBounds.rejected_suffix
            dispatch.shape selected dispatch.found same suffix
        cases sameStore
        obtain ⟨representedFault, keptHeaps, keptState, sameState, keptRelated⟩ :=
          CallableIndexedOwnedPreparedReceivingCallRejectionPosts.receiving_staged_argument_post
            compiler prepared preparedStages selected receiver initial functions reached related heaps
            (sourceResult := compiler.original.type) (resultCore := lowered.type) same
        cases sameState
        refine .inl ⟨Staging.Recursive.Size.stepSize [calleeSize, argumentsSize, Staging.Recursive.Size.stepSize []],
          .fault (.semantic (.argumentArityMismatch dispatch.row.entry.parameterCount ids.length)),
          argumentsHeap, finalMap, finalWorld, ?_, completed.sound, ?_, keptHeaps, maps, worlds, frame,
          heapMetadata, reached, keptRelated, ?_⟩
        · simpa only [physical] using failedSource
        · have exactValue : value = .inLeft lowered.type
              (.word (prepared.site.reasonAt dispatch.row.caller dispatch.row.call dispatch.row.entry.id
                .beforeApplication (.argumentArityMismatch dispatch.row.entry.parameterCount ids.length))) := by
            simpa only [lowerType] using sameValue
          rw [exactValue]
          exact CallableIndexedOwnedPublicDecodedStagedCallFaults.arity_result model representedFault
        · change CallableIndexedOwnedSourceAdmission.PostAdmission bridge context compiler.original.type (.fault _) reached
          exact ⟨admitted.rows, by intro sourceValue impossible; cases impossible⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedFiniteClosureUserDispatch
