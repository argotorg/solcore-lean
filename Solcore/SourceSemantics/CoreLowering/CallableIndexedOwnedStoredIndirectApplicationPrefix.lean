import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectArgumentPrefix
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredClosureArityBoundary

/-! Resolve the actual fourth guard using the same selected row's physical
closure and argument counts. The original full fourth-bind receipt remains
beside its strict application projection. Source arity rejection uses the
actual ordered Source trace and its real reached pool; packed types supply no
count or stage verdict. No callable body is invoked by this finite boundary. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectApplicationPrefix
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters
universe u

section Gate
variable {sidecar : SourceCoreStageContracts.Sidecar} {site : SourceCoreCallableContracts.Callsite}
  {callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution} {node : ExpressionNode}
  {function : Dynamic.Closure} {carrier : Value}
  (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) site site.call ids (.closure function) carrier)
  (selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar site callee ids metadata node dispatch.row)

include selected in
/-- The selected row's accepted verdict uses genuine physical counts. -/
theorem accepted_row (same : function.parameters.length = ids.length) : dispatch.row.afterArguments = .ok () := by
  apply dispatch.row.afterArguments_ok
  rw [CallableIndexedOwnedStoredClosureArityBoundary.parameter_count dispatch selected, selected.argument_count]
  exact same

include selected in
/-- Concrete dispatch at the actual callee fixes only this actual fourth gate.
The passed branch exposes the original application trace and strict bound. -/
theorem resolve_application
    {budget : Nat} {unknown : Word} {result : Ty} {actual : Environment}
    {argumentStore finalStore : Store} {packed value : Value}
    (receipt : CallableIndexedOwnedStoredIndirectArgumentPrefix.ApplicationPrefix
      budget site unknown result actual argumentStore carrier packed value finalStore) :
    (function.parameters.length ≠ ids.length ∧
      dispatch.row.afterArguments = .error (.argumentArityMismatch function.parameters.length ids.length) ∧
      value = .inLeft result (.word (site.reasonAt dispatch.row.caller dispatch.row.call dispatch.row.entry.id
        .beforeApplication (.argumentArityMismatch function.parameters.length ids.length))) ∧
      finalStore = argumentStore) ∨
    (function.parameters.length = ids.length ∧ dispatch.row.afterArguments = .ok () ∧
      ∃ size, EvaluationSize size (.unit :: packed :: .unit :: carrier :: actual) argumentStore
        (.apply (.second (.first (.var 3))) (.var 1)) value finalStore ∧ size < budget) := by
  have read : Evaluates (packed :: .unit :: carrier :: actual) argumentStore (.second (.var 2))
      (.word dispatch.contract) argumentStore :=
    .second (.var (by simpa only [List.getElem?_cons_succ, List.getElem?_cons_zero] using congrArg some dispatch.shape))
  have original := site.dispatch_known .beforeApplication unknown dispatch.contract dispatch.row dispatch.found read
  by_cases sameCount : function.parameters.length = ids.length
  · have answer := accepted_row dispatch selected sameCount
    rw [SourceCoreCallableContracts.reason_accepted dispatch.row site.reasonAt .beforeApplication answer] at original
    cases receipt with
    | failed gate strict =>
      have same := (evaluation_deterministic gate.sound original).1
      cases same
    | passed gate application gateStrict applicationStrict =>
      obtain ⟨same, stores⟩ := evaluation_deterministic gate.sound original
      cases same
      subst stores
      exact Or.inr ⟨sameCount, answer, _, application, applicationStrict⟩
  · have answer := CallableIndexedOwnedStoredClosureArityBoundary.rejected_row dispatch selected sameCount
    rw [SourceCoreCallableContracts.reason_rejected dispatch.row site.reasonAt .beforeApplication _ answer] at original
    cases receipt with
    | failed gate strict =>
      obtain ⟨same, stores⟩ := evaluation_deterministic gate.sound original
      cases same
      exact Or.inl ⟨sameCount, answer, rfl, stores⟩
    | passed gate application gateStrict applicationStrict =>
      have same := (evaluation_deterministic gate.sound original).1
      cases same
end Gate

section

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope id callee ids metadata reasonAt lowered)
  {native : SourceCoreGeneralFunctions.CallableContext}
  (prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler native)
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {certificate : GenericExpressionMeaning.Certificate} {calleeNode : ExpressionNode}
  (certified : certificate scope callee compiler.calleeCode)
  (found : source.lookupExpression? callee = some calleeNode)
  (sourceTyped : ExpressionHasType source context callee calleeNode.type)
  (parentTyped : ExpressionHasType source context id compiler.original.type)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
  (covers : evidence.Covers context)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
  {canonical actual : Environment} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    (CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile) mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)

local notation "functions" => CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions

variable {sidecar : SourceCoreStageContracts.Sidecar}
  (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (sidecarSource : sidecar.source = source)

variable {function : Dynamic.Closure} {calleeHeap : Dynamic.Heap} {calleeStore : Store} {calleeNative : Value}
  {calleeMap : LocationMap} {calleeWorld : StoreTyping} {calleeSize : Nat}
  (calleeTrace : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) calleeSize
    context evidence source environment before callee (.closure function) calleeHeap)
  (post : CallableIndexedOwnedStoredIndirectCalleePost.ValuePost (registry := registry) (faults := faults)
    (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context)
    bridge profile compiler initial (.closure function) calleeHeap calleeNative calleeStore calleeMap calleeWorld)
  (accepted : Staging.CallBoundary.GuardAccepts (CallableLedger.frame sidecar) prepared.site.call ids (.closure function))
  {sourceTypes : List TypeSystem.Ty}
  (unique : NodeOccurrencesUnique source) (parent : SourceParent compiler)
  (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids (.closure function) calleeNative)
  (selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar prepared.site callee ids metadata compiler.original dispatch.row)

local notation "arityToken" => prepared.site.reasonAt dispatch.row.caller dispatch.row.call dispatch.row.entry.id
  CallableContract.Phase.beforeApplication (SourceTypedRuntime.RuntimeError.argumentArityMismatch function.parameters.length ids.length)

/-- The exact rejection keeps the independently graded Source fault, actual
argument post and cumulative caller pool. Its token is the selected raw error. -/
def RejectedAt (value : Value) (finalStore : Store) : Prop :=
  ∃ sourceSize after finalMap finalWorld,
    function.parameters.length ≠ ids.length ∧
    dispatch.row.afterArguments = .error (.argumentArityMismatch function.parameters.length ids.length) ∧
    RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
      context evidence source environment before id (.fault (.argumentArityMismatch function.parameters.length ids.length)) after ∧
    Staging.CallBoundary.Executes (Program.ofChecked compiled.sourceProgram) (CallableLedger.frame sidecar)
      context evidence source environment before id callee ids metadata
      (.semanticFault (.argumentArityMismatch function.parameters.length ids.length)) after ∧
    value = .inLeft lowered.type (.word arityToken) ∧
    CallableIndexedOwnedStoredClosureArityBoundary.ResultAt (registry := registry) (faults := faults) (context := context)
      bridge profile compiler prepared initial dispatch (.argumentArityMismatch function.parameters.length ids.length)
      after arityToken finalStore finalMap finalWorld

/-- Actual accepted argument success retains the full fourth bind separately
from the strict application projection, at that same argument store. -/
def PassedAt (budget : Nat) (value : Value) (finalStore : Store) : Prop :=
  function.parameters.length = ids.length ∧ dispatch.row.afterArguments = .ok () ∧
  ∃ values argumentStore remainingSize applicationSize,
    EvaluationSize remainingSize (DataPatternValues.packValues values :: .unit :: calleeNative :: actual) argumentStore
      (LanguageResult.bind compiler.resultType
        (CallableContract.dispatch prepared.site.gates .beforeApplication native.diagnostics.unknown (.second (.var 2)))
        (.apply (.second (.first (.var 3))) (.var 1))) value finalStore ∧ remainingSize < budget ∧
    EvaluationSize applicationSize (.unit :: DataPatternValues.packValues values :: .unit :: calleeNative :: actual) argumentStore
      (.apply (.second (.first (.var 3))) (.var 1)) value finalStore ∧ applicationSize < budget

end

namespace ForModel

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functionModel : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope id callee ids metadata reasonAt lowered)
  {native : SourceCoreGeneralFunctions.CallableContext}
  (prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler native)
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {certificate : GenericExpressionMeaning.Certificate} {calleeNode : ExpressionNode}
  (certified : certificate scope callee compiler.calleeCode)
  (found : source.lookupExpression? callee = some calleeNode)
  (sourceTyped : ExpressionHasType source context callee calleeNode.type)
  (parentTyped : ExpressionHasType source context id compiler.original.type)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
  (covers : evidence.Covers context)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
  {canonical actual : Environment} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    functionModel mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)

local notation "functions" => functionModel
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions

variable {sidecar : SourceCoreStageContracts.Sidecar}
  (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (sidecarSource : sidecar.source = source)

variable {function : Dynamic.Closure} {calleeHeap : Dynamic.Heap} {calleeStore : Store} {calleeNative : Value}
  {calleeMap : LocationMap} {calleeWorld : StoreTyping} {calleeSize : Nat}
  (calleeTrace : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) calleeSize
    context evidence source environment before callee (.closure function) calleeHeap)
  (post : CallableIndexedOwnedStoredFunctionModelReceipts.ValuePost (registry := registry)
    (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context)
    bridge functionModel compiler initial (.closure function) calleeHeap calleeNative calleeStore calleeMap calleeWorld)
  (accepted : Staging.CallBoundary.GuardAccepts (CallableLedger.frame sidecar) prepared.site.call ids (.closure function))
  {sourceTypes : List TypeSystem.Ty}
  (unique : NodeOccurrencesUnique source) (parent : SourceParent compiler)
  (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids (.closure function) calleeNative)
  (selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar prepared.site callee ids metadata compiler.original dispatch.row)

local notation "arityToken" => prepared.site.reasonAt dispatch.row.caller dispatch.row.call dispatch.row.entry.id
  CallableContract.Phase.beforeApplication (SourceTypedRuntime.RuntimeError.argumentArityMismatch function.parameters.length ids.length)

/-- The exact rejection keeps the independently graded Source fault, actual
argument post and cumulative caller pool. Its token is the selected raw error. -/
def RejectedAt (value : Value) (finalStore : Store) : Prop :=
  ∃ sourceSize after finalMap finalWorld,
    function.parameters.length ≠ ids.length ∧
    dispatch.row.afterArguments = .error (.argumentArityMismatch function.parameters.length ids.length) ∧
    RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
      context evidence source environment before id (.fault (.argumentArityMismatch function.parameters.length ids.length)) after ∧
    Staging.CallBoundary.Executes (Program.ofChecked compiled.sourceProgram) (CallableLedger.frame sidecar)
      context evidence source environment before id callee ids metadata
      (.semanticFault (.argumentArityMismatch function.parameters.length ids.length)) after ∧
    value = .inLeft lowered.type (.word arityToken) ∧
    CallableIndexedOwnedStoredFunctionModelReceipts.FaultPost (registry := registry) (context := context)
      bridge functionModel compiler initial
      (CallableIndexedOwnedStoredClosureArityBoundary.FaultToken (faults := faults) compiler prepared dispatch) (.argumentArityMismatch function.parameters.length ids.length)
      after arityToken finalStore finalMap finalWorld

include parentTyped wellFormed runtime covers locals admitted calleeTrace post accepted unique parent selected in
/-- Resolve only the actual successful ordered argument receipt. The original
receipt is returned verbatim; no semantic producer or body result is assumed. -/
theorem resolve_success (budget : Nat) {value : Value} {finalStore : Store}
    (receipt : CallableIndexedOwnedStoredIndirectArgumentPrefix.ForModel.SuccessPrefix
      (registry := registry) (context := context) (evidence := evidence)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeHeap := calleeHeap) (calleeNative := calleeNative) (calleeStore := calleeStore)
      bridge functionModel compiler prepared initial budget value finalStore) :
    CallableIndexedOwnedStoredIndirectArgumentPrefix.ForModel.SuccessPrefix
      (registry := registry) (context := context) (evidence := evidence)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeHeap := calleeHeap) (calleeNative := calleeNative) (calleeStore := calleeStore)
      bridge functionModel compiler prepared initial budget value finalStore ∧
    (RejectedAt (registry := registry) (faults := faults) (context := context) (evidence := evidence)
      (environment := environment) (sidecar := sidecar) bridge functionModel compiler prepared initial dispatch value finalStore ∨
    PassedAt (actual := actual) compiler prepared dispatch budget value finalStore) := by
  refine ⟨receipt, ?_⟩
  obtain ⟨_nativeSize, argumentSize, sources, values, after, argumentStore, finalMap, finalWorld,
    _nativeArguments, _argumentStrict, argumentsTrace, _represented, finalHeaps, maps, worlds,
    frame, metadataExtended, ⟨reached, related, argumentAdmission⟩,
    ⟨remainingSize, remaining, remainingStrict, prefixReceipt⟩⟩ := receipt
  rcases resolve_application dispatch selected prefixReceipt with
    ⟨different, rejected, valueEq, storeEq⟩ | ⟨same, passed, applicationSize, application, applicationStrict⟩
  · subst finalStore
    obtain ⟨_calleeEvaluation, _representation, _calleeHeaps, _calleeMaps, _calleeWorlds, _calleeFrame,
      calleeMetadata, calleeReached, _calleeRelated, calleePost⟩ := post
    have calleeAdmission := calleePost.at_value.2
    obtain ⟨_parameter, _result, rawTypes, _calleeTyped, argumentsTyped, application⟩ :=
      CallableIndexedOwnedStoredClosureArgumentReceipts.original_facts unique compiler.found compiler.originalForm parentTyped
    have count : rawTypes.length = metadata.argumentCount := by cases application with | intro count _ _ _ => exact count.symm
    have argumentsCount := arguments_count_of_source_admission wellFormed runtime covers (locals.mono calleeMetadata)
      calleeAdmission.heap argumentsTyped count argumentsTrace
    have actualCount : sources.length = ids.length := argumentsCount.trans parent.arity.symm
    have failed : Dynamic.CallableFaults (Program.ofChecked compiled.sourceProgram) context evidence function.evidence
        after (.closure function) sources (.argumentArityMismatch function.parameters.length ids.length) after := by
      rw [← actualCount]
      exact .closureArity (actualCount.symm ▸ different)
    have called : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram)
        (SourceExecutionSize.stepSize []) context evidence function.evidence after (.closure function) sources
        (.fault (.argumentArityMismatch function.parameters.length ids.length)) after := by
      rw [← actualCount]
      exact .fault (.closureArity (actualCount.symm ▸ different))
    obtain ⟨sourceSize, original⟩ := SourceSuffix.to_expression compiler.found compiler.originalForm parent.requirements parent.coercions
      compiler.argumentCoercions parent.arity wellFormed runtime covers (locals.mono calleeMetadata) calleeAdmission.heap
      argumentsTyped count calleeTrace (CallableIndexedOwnedIndirectExpressionHeads.SourceSuffix.called argumentsTrace called)
    obtain ⟨packed, packing⟩ := Dynamic.ValuesPack.exists_pack sources
    have coercions : Dynamic.CoercionPathExecutes (Program.ofChecked compiled.sourceProgram) context evidence
        after metadata.argumentCoercions packed packed after := by
      rw [compiler.argumentCoercions]
      exact .nil
    have staged : Staging.CallBoundary.Executes (Program.ofChecked compiled.sourceProgram) (CallableLedger.frame sidecar)
        context evidence source environment before id callee ids metadata
        (.semanticFault (.argumentArityMismatch function.parameters.length ids.length)) after :=
      .applicationFault calleeTrace.sound (by simpa only [prepared.call] using accepted) argumentsTrace.sound packing coercions
        packing parent.arity argumentsCount failed
    have loweredType : lowered.type = compiler.resultType :=
      (congrArg (fun output => output.type) compiler.output).trans compiler.resultTypeEq.symm
    left
    refine ⟨sourceSize, after, finalMap, finalWorld, different, rejected, original, staged, ?_, ?_⟩
    · exact loweredType.symm ▸ valueEq
    · exact ⟨Or.inr ⟨rfl, rfl⟩, finalHeaps, maps, worlds, frame, metadataExtended, reached, related,
        after_expression_sized initial reached admitted wellFormed runtime covers locals parentTyped original frame⟩
  · right
    exact ⟨same, passed, values, argumentStore, remainingSize, applicationSize, remaining, remainingStrict,
      application, applicationStrict⟩

end ForModel

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope id callee ids metadata reasonAt lowered)
  {native : SourceCoreGeneralFunctions.CallableContext}
  (prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler native)
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {certificate : GenericExpressionMeaning.Certificate} {calleeNode : ExpressionNode}
  (certified : certificate scope callee compiler.calleeCode)
  (found : source.lookupExpression? callee = some calleeNode)
  (sourceTyped : ExpressionHasType source context callee calleeNode.type)
  (parentTyped : ExpressionHasType source context id compiler.original.type)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
  (covers : evidence.Covers context)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
  {canonical actual : Environment} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    (CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile) mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)

local notation "functions" => CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions

variable {sidecar : SourceCoreStageContracts.Sidecar}
  (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (sidecarSource : sidecar.source = source)

variable {function : Dynamic.Closure} {calleeHeap : Dynamic.Heap} {calleeStore : Store} {calleeNative : Value}
  {calleeMap : LocationMap} {calleeWorld : StoreTyping} {calleeSize : Nat}
  (calleeTrace : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) calleeSize
    context evidence source environment before callee (.closure function) calleeHeap)
  (post : CallableIndexedOwnedStoredIndirectCalleePost.ValuePost (registry := registry) (faults := faults)
    (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context)
    bridge profile compiler initial (.closure function) calleeHeap calleeNative calleeStore calleeMap calleeWorld)
  (accepted : Staging.CallBoundary.GuardAccepts (CallableLedger.frame sidecar) prepared.site.call ids (.closure function))
  {sourceTypes : List TypeSystem.Ty}
  (unique : NodeOccurrencesUnique source) (parent : SourceParent compiler)
  (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids (.closure function) calleeNative)
  (selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar prepared.site callee ids metadata compiler.original dispatch.row)

local notation "arityToken" => prepared.site.reasonAt dispatch.row.caller dispatch.row.call dispatch.row.entry.id
  CallableContract.Phase.beforeApplication (SourceTypedRuntime.RuntimeError.argumentArityMismatch function.parameters.length ids.length)

include parentTyped wellFormed runtime covers locals admitted calleeTrace post accepted unique parent selected in
/-- Resolve only the actual successful ordered argument receipt. The original
receipt is returned verbatim; no semantic producer or body result is assumed. -/
theorem resolve_success (budget : Nat) {value : Value} {finalStore : Store}
    (receipt : CallableIndexedOwnedStoredIndirectArgumentPrefix.SuccessPrefix
      (registry := registry) (faults := faults) (context := context) (evidence := evidence)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeHeap := calleeHeap) (calleeNative := calleeNative) (calleeStore := calleeStore)
      bridge profile compiler prepared initial budget value finalStore) :
    CallableIndexedOwnedStoredIndirectArgumentPrefix.SuccessPrefix
      (registry := registry) (faults := faults) (context := context) (evidence := evidence)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeHeap := calleeHeap) (calleeNative := calleeNative) (calleeStore := calleeStore)
      bridge profile compiler prepared initial budget value finalStore ∧
    (RejectedAt (registry := registry) (faults := faults) (context := context) (evidence := evidence)
      (environment := environment) (sidecar := sidecar) bridge profile compiler prepared initial dispatch value finalStore ∨
    PassedAt (actual := actual) compiler prepared dispatch budget value finalStore) := by
  exact ForModel.resolve_success (functionModel := functions) (bridge := bridge) (compiler := compiler) (prepared := prepared) (parentTyped := parentTyped) (wellFormed := wellFormed) (runtime := runtime) (covers := covers) (locals := locals) (initial := initial) (admitted := admitted) (calleeTrace := calleeTrace) (post := post) (accepted := accepted) (unique := unique) (parent := parent) (dispatch := dispatch) (selected := selected) budget receipt

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectApplicationPrefix
