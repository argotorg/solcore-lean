import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectApplicationPrefix
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinarySelectedCallReceipts

/-! Actual pure stored-call prefixes retain the original whole fourth bind.
The real initialized callee post closes the first child by determinism; the
attached accepted row closes both guards. One original admitted sequence
produces the ordered arguments at that same caller state. Source argument
fault exclusion is an independent finite fact at this actual input heap. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectPurePrefixBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope id callee ids metadata reasonAt lowered)
  {native : SourceCoreGeneralFunctions.CallableContext} (prepared : Prepared compiler native)
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {certificate : GenericExpressionMeaning.Certificate} {sourceTypes originalTypes : List TypeSystem.Ty}
  (tree : DataExpressionSequence.Tree source certificate scope ids sourceTypes compiler.codes)
  (unique : NodeOccurrencesUnique source)
  (argumentsTyped : ExpressionsHaveTypes source context ids originalTypes)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions

include tree unique argumentsTyped in
/-- Reflect the actual ordered arguments once. The same finite Source fault
exclusion applies to the returned trace, and its genuine post admits the next
original bind without a whole-program typing theorem. -/
theorem reflects_arguments (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      bridge model context evidence source certificate faults size)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {before : Dynamic.Heap} {store : Store}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (noFault : ∀ size reason after, SourceExecutionSize.ExpressionsFault (Program.ofChecked compiled.sourceProgram)
      size context evidence source environment before ids reason after → False)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store ((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ) value finalStore)
    (strict : size < budget) :
    ∃ sourceSize sources values after finalMap finalWorld,
      value = .inRight .word (DataPatternValues.packValues values) ∧
      SourceExecutionSize.ExpressionsEvaluate (Program.ofChecked compiled.sourceProgram) sourceSize
        context evidence source environment before ids sources after ∧
      DataExpressionSequence.Values model finalMap finalWorld sourceTypes (compiler.codes.map (·.type)) sources values ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ Admission bridge context reached := by
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related, post⟩ :=
    CallableIndexedOwnedAdmittedExpressionSequence.reflects_bounded bridge budget tree unique argumentsTyped children
      environments heaps locals agrees typed initial admitted completed strict
  cases represented with
  | values represented =>
    cases trace with
    | values evaluated =>
      exact ⟨sourceSize, _, _, after, finalMap, finalWorld, rfl, evaluated, represented, finalHeaps,
        maps, worlds, frame, metadata, reached, related, post.at_values⟩
  | fault matched =>
    cases trace with
    | fault failed => exact False.elim (noFault sourceSize _ after failed)

section Parent
variable {firstMap : LocationMap} {firstWorld : StoreTyping} {before : Dynamic.Heap} {firstStore : Store}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
  {canonical actual : Environment} {ξ : Renaming} {calleeNode : ExpressionNode}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    firstMap firstWorld administrative scope environment canonical compiled.indexed.layouts.definitions)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes firstWorld actual actualContext compiled.indexed.layouts.definitions)
  (first : callerProtocol.State ⟨scope, firstMap, firstWorld, before, firstStore, canonical⟩)
  {function : Dynamic.Closure} {calleeHeap : Dynamic.Heap} {calleeStore : Store} {calleeNative : Value}
  {calleeMap : LocationMap} {calleeWorld : StoreTyping} {calleeSize : Nat}
  (post : CallableIndexedOwnedStoredFunctionModelReceipts.ValuePost (registry := registry)
    (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context)
    bridge functions compiler first (.closure function) calleeHeap calleeNative calleeStore calleeMap calleeWorld)
  {sidecar : SourceCoreStageContracts.Sidecar}
  (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids
    (.closure function) calleeNative)
  (selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar prepared.site callee ids metadata compiler.original dispatch.row)
  (accepted : CallableIndexedOwnedChosenOrdinarySelectedCallReceipts.AcceptedAt dispatch native.diagnostics.unknown)
  (noFault : ∀ size reason after, SourceExecutionSize.ExpressionsFault (Program.ofChecked compiled.sourceProgram)
    size context evidence source environment calleeHeap ids reason after → False)

include post environments locals agrees typed tree unique argumentsTyped selected accepted noFault in
/-- The whole actual parent completion yields the original full successful
prefix, intermediate and cumulative effects, and entire fourth bind. The body
is left as its genuine measured application child; no invocation runs here. -/
theorem reflects_parent
    (_calleeTrace : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) calleeSize
      context evidence source environment before callee (.closure function) calleeHeap)
    (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      bridge model context evidence source certificate faults size)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual firstStore (lowered.expression.rename ξ) value finalStore)
    (within : size ≤ budget) :
    CallableIndexedOwnedStoredIndirectArgumentPrefix.ForModel.SuccessPrefix
      (registry := registry) (context := context) (evidence := evidence) (environment := environment)
      (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes) (calleeHeap := calleeHeap)
      (calleeNative := calleeNative) (calleeStore := calleeStore)
      bridge functions compiler prepared first budget value finalStore ∧
    CallableIndexedOwnedStoredFunctionModelReceipts.SuccessStep
      (registry := registry) (context := context) (evidence := evidence) (environment := environment)
      (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes) (calleeHeap := calleeHeap)
      (calleeNative := calleeNative) (calleeStore := calleeStore) (calleeMap := calleeMap) (calleeWorld := calleeWorld)
      bridge functions compiler prepared first budget value finalStore ∧
    CallableIndexedOwnedStoredIndirectApplicationPrefix.PassedAt (actual := actual)
      compiler prepared dispatch budget value finalStore := by
  have full := completed
  rw [prepared.lowered_rename compiler ξ] at full
  cases CallableIndirectCallBounds.bind_completed full within with
  | failed child _strict =>
    have impossible := (evaluation_deterministic child.sound post.1).1
    cases impossible
  | continued child remaining _childStrict remainingStrict =>
    obtain ⟨same, stores⟩ := evaluation_deterministic child.sound post.1
    cases same
    rw [stores] at remaining
    have read : Evaluates (calleeNative :: actual) calleeStore (.second (.var 0)) (.word dispatch.contract) calleeStore :=
      .second (.var (by simpa only [List.getElem?_cons_zero] using congrArg some dispatch.shape))
    have gate := prepared.site.dispatch_known .beforeArguments native.diagnostics.unknown dispatch.contract dispatch.row dispatch.found read
    rw [SourceCoreCallableContracts.reason_accepted dispatch.row prepared.site.reasonAt .beforeArguments accepted.first] at gate
    cases CallableIndirectCallBounds.bind_completed remaining (Nat.le_of_lt remainingStrict) with
    | failed failed _gateStrict =>
      have impossible := (evaluation_deterministic failed.sound gate).1
      cases impossible
    | continued gateTrace suffix _gateStrict suffixStrict =>
      obtain ⟨same, stores⟩ := evaluation_deterministic gateTrace.sound gate
      cases same
      rw [stores] at suffix
      obtain ⟨_calleeEvaluation, calleeRepresentation, calleeHeaps, calleeMaps, calleeWorlds,
        calleeFrame, calleeMetadata, calleeReached, calleeRelated, calleePost⟩ := post
      have layout : EnvironmentsAgree ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ξ))
          canonical (.unit :: calleeNative :: actual) :=
        GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix agrees calleeNative) .unit
      have actualTyped := RuntimeEnvironmentHasTypes.cons RuntimeValueHasType.unit
        (RuntimeEnvironmentHasTypes.cons calleeRepresentation.runtime_hasType (typed.weaken calleeWorlds))
      cases CallableIndirectCallBounds.bind_completed suffix (Nat.le_of_lt suffixStrict) with
      | failed argumentTrace argumentStrict =>
        rw [← GenericExpressionMeaning.rename_prefix, ← GenericExpressionMeaning.rename_prefix] at argumentTrace
        obtain ⟨_, _, _, _, _, _, impossible, _⟩ :=
          reflects_arguments bridge functions compiler tree unique argumentsTyped budget children
            (environments.extend calleeMaps calleeWorlds) calleeHeaps (locals.mono calleeMetadata) layout actualTyped
            calleeReached calleePost.at_value.2 noFault argumentTrace argumentStrict
        cases impossible
      | @continued argumentSize remainderSize argumentInput payload argumentStore _ _ argumentTrace remaining argumentStrict remainingStrict =>
        have originalArguments := argumentTrace
        rw [← GenericExpressionMeaning.rename_prefix, ← GenericExpressionMeaning.rename_prefix] at argumentTrace
        obtain ⟨sourceSize, sources, values, after, finalMap, finalWorld, sameValue, evaluated, represented,
          finalHeaps, maps, worlds, frame, heapMetadata, reached, related, argumentAdmission⟩ :=
          reflects_arguments bridge functions compiler tree unique argumentsTyped budget children
            (environments.extend calleeMaps calleeWorlds) calleeHeaps (locals.mono calleeMetadata) layout actualTyped
            calleeReached calleePost.at_value.2 noFault argumentTrace argumentStrict
        cases sameValue
        have applicationPrefix : CallableIndexedOwnedStoredIndirectArgumentPrefix.ApplicationPrefix budget prepared.site
            native.diagnostics.unknown compiler.resultType actual argumentStore calleeNative (DataPatternValues.packValues values) value finalStore := by
          cases CallableIndirectCallBounds.bind_completed remaining (Nat.le_of_lt remainingStrict) with
          | failed failed strict => exact .failed failed strict
          | continued passed application gateStrict applicationStrict => exact .passed passed application gateStrict applicationStrict
        rcases CallableIndexedOwnedStoredIndirectApplicationPrefix.resolve_application dispatch selected applicationPrefix with rejected | succeeded
        · exact False.elim (rejected.1 accepted.physical)
        · obtain ⟨physical, fourth, applicationSize, application, applicationStrict⟩ := succeeded
          refine ⟨?_, ?_, ?_⟩
          · exact ⟨_, sourceSize, sources, values, after, _, finalMap, finalWorld, originalArguments, argumentStrict,
              evaluated, represented, finalHeaps, calleeMaps.trans maps, calleeWorlds.trans worlds,
              calleeFrame.trans frame, calleeMetadata.trans heapMetadata,
              ⟨reached, callerProtocol.trans calleeRelated related, argumentAdmission⟩,
              ⟨_, remaining, remainingStrict, applicationPrefix⟩⟩
          · exact ⟨_, sourceSize, sources, values, after, _, finalMap, finalWorld, originalArguments, argumentStrict,
              evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata,
              calleeMaps.trans maps, calleeWorlds.trans worlds, calleeFrame.trans frame, calleeMetadata.trans heapMetadata,
              ⟨reached, callerProtocol.trans calleeRelated related, argumentAdmission⟩,
              ⟨_, remaining, remainingStrict⟩⟩
          · exact ⟨physical, fourth, values, _, _, applicationSize, remaining, remainingStrict, application, applicationStrict⟩

end Parent
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectPurePrefixBounds
