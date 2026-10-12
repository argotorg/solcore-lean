import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalClosureUserPreservationDispatch
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedTerminalClosureParentPreservation


import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalClosureParentPreservation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectBuiltinPreservationDispatch

/-! Internal chosen-terminal dispatch for the eventual numeric body family.
The static factory selects one genuine packet; the body hypothesis belongs to
that packet alone. Existing failure, physical arity, parameter/body execution
and saved caller restoration proofs retain their original indices. Original
Source typing and compiler-policy transport remain separate static obligations.
-/
/-! The real successful callee and ordered argument prefix supplies closure
parent preservation. The selected physical count is decided at that exact
reached state. The closure's genuine Source application feeds its same contextual
terminal Code; the complete global Source suffix stays with the named producer.
Every preservation child scope is the actual scope selected by the Source rule. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedTerminalClosureUserPreservationDispatch
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPreparedStagedIndirectNativePrefix (CalleePost)
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)
open CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds (TerminalFor)
open CallableIndexedOwnedPreparedStagedTerminalClosureParentPreservation (PreservesBelowFor)
open CallableIndexedOwnedPreparedStagedIndirectBuiltinPreservationDispatch (ParentAt)
open CallableIndexedOwnedPreparedScopedCallBoundaryReceipts (CallView)
open CallableIndexedOwnedContextualCalleeStageReceipts (BoundaryAt)
open CallableIndexedOwnedPreparedStagedTerminalClosureUserPreservationDispatch (GlobalAppliedPrefix)
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

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys
  bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked
  completion.result.context.registry functions
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
  completion.result.diagnostics


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
  (guardFrame : invocation.guards = CallableLedger.frame sidecar)
  (actualFunctionType : policy.callables.functionType = CallableContract.functionType)

include sourceParent occurrence preparedStages receiver wellFormed runtime covers locals sourceEq tree unique
  parentTyped calleeFound guardFrame actualFunctionType in
/-- Authentic Source application and prefix witnesses construct the original
closure parent. Physical count rejection keeps the reached argument heap and
literal receiving arity word; success preserves the actual selected body once. -/
theorem preserves_closure_or_global
    (terminals : ∀ {mapping world function native bindings parameterCore resultCore}
      (association : Association headers keys bodyRegistry semanticFaults mapping world function native
        bindings parameterCore resultCore), TerminalFor association stages)
    (budget : Nat)
    (children : ∀ {mapping world function native bindings parameterCore resultCore}
      (association : Association headers keys bodyRegistry semanticFaults mapping world function native
        bindings parameterCore resultCore),
      PreservesBelowFor (registry := completion.result.context.registry) (faults := callFaults)
        association (terminals association) functions budget)
    {calleeSize argumentsSize applicationSize : Nat}
    {sourceValue : Dynamic.Value} {calleeHeap argumentsHeap after : Dynamic.Heap}
    {sources : List Dynamic.Value} {outcome : Staging.Recursive.Outcome}
    (user : Staging.CallBoundary.UserCallable sourceValue)
    (calleeTrace : Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages calleeSize
      invocation context environment before callee (.value sourceValue) calleeHeap)
    (accepted : Staging.CallBoundary.GuardAccepts invocation.guards id ids sourceValue)
    (argumentsTrace : Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages argumentsSize
      invocation context environment calleeHeap ids (.values sources) argumentsHeap)
    (called : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) stages applicationSize
      invocation context argumentsHeap sourceValue sources outcome after)
    (within : applicationSize ≤ budget)
    (prefixResult : CallableIndexedOwnedPreparedStagedIndirectValuesPrefix.ValuesPrefix
      (registry := completion.result.context.registry) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeNode := calleeNode) (sidecar := sidecar)
      bridge profile compiler prepared initial sourceValue calleeHeap argumentsHeap sources) :
    ParentAt (completion := completion) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (stages := stages) (invocation := invocation) (environment := environment)
      (actual := actual) (ξ := ξ) bridge profile compiler initial
      (Staging.Recursive.Size.stepSize [calleeSize, argumentsSize, applicationSize]) outcome after ∨
    GlobalAppliedPrefix (completion := completion) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (stages := stages) (invocation := invocation) (environment := environment)
      (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes) (calleeNode := calleeNode) (sidecar := sidecar)
      bridge profile compiler prepared initial calleeSize argumentsSize applicationSize sourceValue
      calleeHeap argumentsHeap sources outcome after := by
  cases user with
  | global function =>
    exact .inr ⟨function, rfl, calleeTrace, accepted, argumentsTrace, called, prefixResult⟩
  | closure function =>
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
    obtain ⟨rawParameter, rawResult, functionType, bundle, originalResult,
      calleeStore, calleeMap, calleeWorld, carrier, values, argumentsStore, finalMap, finalWorld,
      originalNode, originalMetadata, calleePost, calleeTyped, firstGate, argumentsNative,
      represented, calleeRelated, _callView, boundary, heaps, maps, worlds,
      frame, heapMetadata, reached, related, admitted⟩ := prefixResult
    cases boundary with
    | user dispatch selected =>
      by_cases count : dispatch.row.entry.parameterCount = ids.length
      · have calleeNative := calleePost.1
        obtain ⟨_nativeCallee, _representedCallee, _calleeHeaps, _calleeMaps, _calleeWorlds,
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
        exact .inl (CallableIndexedOwnedPreparedStagedSelectedTerminalClosureParentPreservation.preserves_parent
          bridge profile compiler prepared sourceParent occurrence initial reached related admitted
          heaps maps worlds frame heapMetadata dispatch selected count accepted wellFormed runtime covers
          (locals.mono calleeMetadata) calleeHeapTyped typing rawCallee actualFunctionType relatedCallee
          represented bundle originalResult terminals budget children calleeTrace argumentsTrace called within
          calleeNative firstGate argumentsNative)
      · have physical := CallableIndexedOwnedStoredClosureArityBoundary.parameter_count dispatch selected
        have valuesCount := CallableIndexedOwnedPreparedSecondCallGateRejection.values_count argumentsTrace
        have different : function.parameters.length ≠ ids.length := by
          simpa only [physical] using count
        cases called with
        | closure selectedChild valid parameters allocate bodyTrace bodyResult =>
          exact False.elim (different (allocate.length_eq.trans valuesCount))
        | closureArity mismatch =>
          have actualAccepted : Staging.CallBoundary.GuardAccepts (CallableLedger.frame sidecar)
              prepared.site.call ids (.closure function) := by
            simpa only [guardFrame, prepared.call] using accepted
          have argumentsWeaken : Evaluates (.unit :: carrier :: actual) calleeStore
              (((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ).weakenAt 0 |>.weakenAt 0)
              (.inRight .word (DataPatternValues.packValues values)) argumentsStore := by
            simpa only [← GenericExpressionMeaning.rename_prefix, ← GenericExpressionMeaning.rename_prefix]
              using argumentsNative
          have native := CallableIndexedOwnedPreparedSecondCallGateRejection.user_native_preserves
            (result := compiler.resultType) dispatch selected actualAccepted count
            compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown calleePost.1 argumentsWeaken
          change Evaluates actual store
            (CallableContract.call prepared.site.gates
              compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown compiler.resultType
              (compiler.calleeCode.expression.rename ξ)
              ((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ)) _ argumentsStore at native
          rw [← prepared.lowered_rename compiler ξ] at native
          obtain ⟨representedFault, keptHeaps, keptState, sameState, keptRelated⟩ :=
            CallableIndexedOwnedPreparedReceivingCallRejectionPosts.receiving_staged_argument_post
              compiler prepared preparedStages selected receiver initial functions reached related heaps
              (sourceResult := compiler.original.type) (resultCore := lowered.type) count
          cases sameState
          have loweredType : lowered.type = compiler.resultType :=
            (congrArg (fun output => output.type) compiler.output).trans compiler.resultTypeEq.symm
          have faultRep := CallableIndexedOwnedPublicDecodedStagedCallFaults.arity_result model representedFault
          have post : CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context
              compiler.original.type
              (.fault (.semantic (.argumentArityMismatch function.parameters.length sources.length))) reached :=
            ⟨admitted.rows, by intro value impossible; cases impossible⟩
          refine .inl ⟨.applied occurrence compiler.argumentCoercions calleeTrace accepted
            argumentsTrace sourceParent.arity (.closureArity mismatch),
            .inLeft lowered.type (.word (prepared.site.reasonAt dispatch.row.caller dispatch.row.call dispatch.row.entry.id
              .beforeApplication (.argumentArityMismatch dispatch.row.entry.parameterCount ids.length))),
            argumentsStore, finalMap, finalWorld, ?_, ?_, keptHeaps, maps, worlds, frame,
            heapMetadata, reached, keptRelated, post⟩
          · simpa only [loweredType] using native
          · simpa only [physical, valuesCount] using faultRep

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedTerminalClosureUserPreservationDispatch
