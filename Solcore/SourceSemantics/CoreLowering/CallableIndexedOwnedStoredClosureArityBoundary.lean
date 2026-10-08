import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectCalleePost

/-! Closure arity rejection uses the actual successful callee post and ordered
argument children. The selected Generated row and original Source contract
supply physical counts; packed types supply no count. No body is invoked and
no legacy captured prefix is strengthened. The accepted first stage remains
independent. Reflection also retains an earlier argument fault at its real post.
The second-gate token carries its exact RuntimeError and phase. Interpreting it
through the actual diagnostic table is a separate static receipt. -/
set_option autoImplicit false
set_option maxHeartbeats 3200000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredClosureArityBoundary
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters
open CallableIndexedOwnedIndirectExpressionHeads
universe u

section Selected
variable {sidecar : SourceCoreStageContracts.Sidecar} {site : SourceCoreCallableContracts.Callsite}
  {callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution} {node : ExpressionNode}
  {function : Dynamic.Closure} {native : Value}
  (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) site site.call ids (.closure function) native)
  (selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar site callee ids metadata node dispatch.row)

include selected in
/-- The real closure binding identifies the selected ledger's physical count. -/
theorem parameter_count : dispatch.row.entry.parameterCount = function.parameters.length := by
  have retained := CallableIndexedOwnedStoredIndirectCallBounds.selected_contract dispatch selected
  cases dispatch.bound with
  | closure parameters _ =>
    exact (selected.parameter_count retained).trans (congrArg List.length parameters)

include selected in
/-- This is the original second-gate error, with both actual physical counts. -/
theorem rejected_row (different : function.parameters.length ≠ ids.length) :
    dispatch.row.afterArguments = .error (.argumentArityMismatch function.parameters.length ids.length) := by
  have parameters := parameter_count dispatch selected
  have arguments := selected.argument_count
  have mismatch : dispatch.row.entry.parameterCount ≠ dispatch.row.argumentCount := by
    rw [parameters, arguments]
    exact different
  simpa only [parameters, arguments] using dispatch.row.afterArguments_mismatch mismatch

include selected in
/-- Source count rejection closes only the second decision, at its real phase. -/
theorem rejected_gate (different : function.parameters.length ≠ ids.length) (unknown : Word) :
    CallableContract.decision site.gates .beforeApplication unknown dispatch.contract =
      some (site.reasonAt dispatch.row.caller dispatch.row.call dispatch.row.entry.id .beforeApplication
        (.argumentArityMismatch function.parameters.length ids.length)) := by
  rw [site.decision_known .beforeApplication unknown dispatch.contract dispatch.row dispatch.found]
  exact SourceCoreCallableContracts.reason_rejected dispatch.row site.reasonAt .beforeApplication _
    (rejected_row dispatch selected different)
end Selected

section Completion
variable {actual : Environment} {store calleeStore : Store} {native : Value} {token : Word}

/-- The existing third and fourth binds retain the actual argument completion.
An argument fault precedes the pure arity error and keeps its own post. -/
inductive Completion (budget : Nat) (resultType : Ty) (arguments : Expr) : Value → Store → Prop where
  | failed {size : Nat} {input : Ty} {fault : Value} {after : Store}
      (argumentsTrace : EvaluationSize size (.unit :: native :: actual) calleeStore
        ((arguments.weakenAt 0).weakenAt 0) (.inLeft input fault) after)
      (strict : size < budget) : Completion budget resultType arguments (.inLeft resultType fault) after
  | rejected {size : Nat} {input : Ty} {argument : Value} {after : Store}
      (argumentsTrace : EvaluationSize size (.unit :: native :: actual) calleeStore
        ((arguments.weakenAt 0).weakenAt 0) (.inRight input argument) after)
      (strict : size < budget) : Completion budget resultType arguments (.inLeft resultType (.word token)) after

private theorem second_read {environment : Environment} {before : Store} {payload : Value}
    {word : Word} {index : Nat} (shape : native = .pair payload (.word word))
    (found : environment[index]? = some native) :
    Evaluates environment before (.second (.var index)) (.word word) before :=
  .second (.var (found.trans (congrArg some shape)))

/-- Only finite original bind inversions and actual pure gate evaluations are
used. The callee's effectful store is the argument computation's real input. -/
theorem completed {budget size : Nat} {resultType : Ty} {callee arguments : Expr}
    {gates : List CallableContract.Gate} {unknown word : Word} {payload result : Value} {after : Store}
    (shape : native = .pair payload (.word word))
    (calleeTrace : Evaluates actual store callee (.inRight .word native) calleeStore)
    (stage : CallableContract.decision gates .beforeArguments unknown word = none)
    (arity : CallableContract.decision gates .beforeApplication unknown word = some token)
    (trace : EvaluationSize size actual store (CallableContract.call gates unknown resultType callee arguments) result after)
    (within : size ≤ budget) :
    Completion (actual := actual) (calleeStore := calleeStore) (native := native) (token := token)
      budget resultType arguments result after := by
  have descriptor : Evaluates (native :: actual) calleeStore (.second (.var 0)) (.word word) calleeStore :=
    second_read (index := 0) shape rfl
  cases CallableIndirectCallBounds.bind_completed trace within with
  | failed first _ =>
    obtain ⟨same, _⟩ := evaluation_deterministic first.sound calleeTrace
    cases same
  | continued first remaining _ remainingStrict =>
    obtain ⟨same, rfl⟩ := evaluation_deterministic first.sound calleeTrace
    cases same
    cases CallableIndirectCallBounds.bind_completed remaining (Nat.le_of_lt remainingStrict) with
    | failed gate _ =>
      obtain ⟨same, _⟩ := CallableIndirectCallBounds.dispatch_decision descriptor gate
      simp only [stage, CallableContract.resultValue] at same
      cases same
    | continued gate remaining _ remainingStrict =>
      obtain ⟨same, rfl⟩ := CallableIndirectCallBounds.dispatch_decision descriptor gate
      simp only [stage, CallableContract.resultValue] at same
      cases same
      cases CallableIndirectCallBounds.bind_completed remaining (Nat.le_of_lt remainingStrict) with
      | failed argumentsTrace smaller => exact .failed argumentsTrace smaller
      | continued argumentsTrace remaining smaller remainingStrict =>
        cases CallableIndirectCallBounds.bind_completed remaining (Nat.le_of_lt remainingStrict) with
        | failed gate _ =>
          obtain ⟨same, rfl⟩ := CallableIndirectCallBounds.dispatch_decision
            (second_read (index := 2) shape rfl) gate
          simp only [arity, CallableContract.resultValue] at same
          cases same
          exact .rejected argumentsTrace smaller
        | continued gate _ _ _ =>
          obtain ⟨same, _⟩ := CallableIndirectCallBounds.dispatch_decision
            (second_read (index := 2) shape rfl) gate
          simp only [arity, CallableContract.resultValue] at same
          cases same
end Completion

section Boundary
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
  {native : SourceCoreGeneralFunctions.CallableContext} (prepared : Prepared compiler native)
  (parent : SourceParent compiler)
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {certificate : GenericExpressionMeaning.Certificate} {sourceTypes : List TypeSystem.Ty} {calleeNode : ExpressionNode}
  (tree : DataExpressionSequence.Tree source certificate scope ids sourceTypes compiler.codes)
  (unique : NodeOccurrencesUnique source)
  (parentTyped : ExpressionHasType source context id compiler.original.type)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
  (covers : evidence.Covers context)
  {firstMap mapping : LocationMap} {firstWorld world : StoreTyping}
  {before calleeHeap : Dynamic.Heap} {firstStore store : Store}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
  {canonical actual : Environment} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    firstMap firstWorld administrative scope environment canonical compiled.indexed.layouts.definitions)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes firstWorld actual actualContext compiled.indexed.layouts.definitions)
  (first : callerProtocol.State ⟨scope, firstMap, firstWorld, before, firstStore, canonical⟩)
  (firstAdmission : Admission bridge context first)
  {function : Dynamic.Closure} {calleeNative : Value}
  (post : CallableIndexedOwnedStoredIndirectCalleePost.ValuePost (registry := registry) (faults := faults)
    (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context) bridge profile compiler first
    (.closure function) calleeHeap calleeNative store mapping world)
  {sidecar : SourceCoreStageContracts.Sidecar}
  (stages : RecursiveNamedPreparedStageContracts.Prepared compiled native)
  (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (sidecarSource : sidecar.source = source)
  (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids (.closure function) calleeNative)
  (accepted : Staging.CallBoundary.GuardAccepts (CallableLedger.frame sidecar) prepared.site.call ids (.closure function))
  (different : function.parameters.length ≠ ids.length)
  {calleeSize : Nat}
  (calleeTrace : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) calleeSize
    context evidence source environment before callee (.closure function) calleeHeap)

local notation "functions" => CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions
local notation "arityToken" => prepared.site.reasonAt dispatch.row.caller dispatch.row.call dispatch.row.entry.id
  CallableContract.Phase.beforeApplication (SourceTypedRuntime.RuntimeError.argumentArityMismatch function.parameters.length ids.length)

/-- Ordinary child faults keep their original relation. Arity rejection retains
its exact selected RuntimeError and token without assuming a table decoder law. -/
def FaultToken (reason : Dynamic.SemanticFault) (token : Word) : Prop :=
  faults reason token ∨ reason = .argumentArityMismatch function.parameters.length ids.length ∧ token = arityToken

/-- Both fault alternatives retain the same complete actual argument post.
Deep Source heap admission is not asserted for the enclosing fault. -/
def ResultAt (reason : Dynamic.SemanticFault) (after : Dynamic.Heap) (token : Word) (finalStore : Store)
    (finalMap : LocationMap) (finalWorld : StoreTyping) : Prop :=
  FaultToken (faults := faults) compiler prepared dispatch reason token ∧
  CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
  LocationMap.Extends firstMap finalMap ∧ WorldExtends firstWorld finalWorld ∧
  AdministrativePreserved firstMap firstStore finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
  ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
    callerProtocol.Relates first reached ∧ PostAdmission bridge context compiler.original.type (.fault reason) reached

include stages caller sidecarSource unique in
private theorem actual_selected :
    CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar prepared.site callee ids metadata compiler.original dispatch.row := by
  have contains : ContainsExpression sidecar.source prepared.site.call compiler.original := by
    rw [sidecarSource, prepared.call]
    exact lookupExpression?_sound compiler.found
  exact CallableIndexedOwnedSelectedCallCodebookReceipts.selected_at_prepared stages prepared.table caller
    contains compiler.originalForm (sidecarSource ▸ unique) dispatch.found

include parent tree unique parentTyped wellFormed runtime covers environments locals agrees typed firstAdmission
  post stages caller sidecarSource dispatch accepted different calleeTrace in
/-- Actual successful Source arguments produce the real arity fault and raw
selected token. No callable body, strong origin or captured-prefix law is used. -/
theorem preserves_arity (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      bridge model context evidence source certificate faults size)
    {argumentsSize : Nat} {arguments : List Dynamic.Value} {after : Dynamic.Heap}
    (argumentsTrace : SourceExecutionSize.ExpressionsEvaluate (Program.ofChecked compiled.sourceProgram) argumentsSize
      context evidence source environment calleeHeap ids arguments after)
    (within : argumentsSize ≤ budget) :
    ∃ sourceSize finalStore finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize context evidence source
        environment before id (.fault (.argumentArityMismatch function.parameters.length ids.length)) after ∧
      Evaluates actual firstStore (lowered.expression.rename ξ) (.inLeft lowered.type (.word arityToken)) finalStore ∧
      ResultAt (registry := registry) (faults := faults) (context := context) bridge profile compiler prepared first dispatch
        (.argumentArityMismatch function.parameters.length ids.length) after arityToken finalStore finalMap finalWorld := by
  obtain ⟨calleeEvaluation, represented, heaps, maps, worlds, frame, calleeMetadata, calleeState, related, calleePost⟩ := post
  have calleeAdmission := calleePost.at_value.2
  obtain ⟨parameter, sourceResult, rawTypes, _calleeTyping, argumentsTyping, application⟩ :=
    CallableIndexedOwnedStoredClosureArgumentReceipts.original_facts unique compiler.found compiler.originalForm parentTyped
  have count : rawTypes.length = metadata.argumentCount := by cases application with | intro count _ _ _ => exact count.symm
  have argumentsCount := arguments_count_of_source_admission wellFormed runtime covers (locals.mono calleeMetadata)
    calleeAdmission.heap argumentsTyping count argumentsTrace
  have actualCount : arguments.length = ids.length := argumentsCount.trans parent.arity.symm
  have rejected : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) (SourceExecutionSize.stepSize [])
      context evidence function.evidence after (.closure function) arguments
      (.fault (.argumentArityMismatch function.parameters.length ids.length)) after := by
    rw [← actualCount]
    exact .fault (.closureArity (actualCount.symm ▸ different))
  obtain ⟨sourceSize, original⟩ := SourceSuffix.to_expression compiler.found compiler.originalForm parent.requirements parent.coercions
    compiler.argumentCoercions parent.arity wellFormed runtime covers (locals.mono calleeMetadata) calleeAdmission.heap
    argumentsTyping count calleeTrace (SourceSuffix.called argumentsTrace rejected)
  have selected := actual_selected compiler prepared unique stages caller sidecarSource dispatch
  obtain ⟨payloads, finalStore, finalMap, finalWorld, evaluated, _values, finalHeaps, lastMaps, lastWorlds,
      lastFrame, lastMetadata, reached, lastRelated, _argumentAdmission⟩ :=
    CallableIndexedOwnedAdmittedExpressionSequence.preserves_values_bounded bridge budget tree unique argumentsTyping children
      (environments.extend maps worlds) heaps (locals.mono calleeMetadata)
      (GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix agrees calleeNative) .unit)
      (.cons .unit (.cons represented.runtime_hasType (typed.weaken worlds)))
      calleeState calleeAdmission argumentsTrace within
  rw [GenericExpressionMeaning.rename_prefix, GenericExpressionMeaning.rename_prefix] at evaluated
  rw [dispatch.shape] at calleeEvaluation evaluated
  have whole := prepared.site.lower_arity_failure (result := compiler.resultType) native.diagnostics.unknown dispatch.row _ dispatch.found
    (dispatch.accepted accepted) (rejected_row dispatch selected different) calleeEvaluation evaluated
  dsimp only [SourceCoreCallableContracts.Callsite.lower] at whole
  rw [← prepared.lowered_rename compiler ξ] at whole
  have loweredType : lowered.type = compiler.resultType :=
    (congrArg (fun output => output.type) compiler.output).trans compiler.resultTypeEq.symm
  rw [← loweredType] at whole
  exact ⟨sourceSize, finalStore, finalMap, finalWorld, original, whole, Or.inr ⟨rfl, rfl⟩,
    finalHeaps, maps.trans lastMaps, worlds.trans lastWorlds, frame.trans lastFrame, calleeMetadata.trans lastMetadata,
    reached, callerProtocol.trans related lastRelated,
    after_expression_sized first reached firstAdmission wellFormed runtime covers locals parentTyped original (frame.trans lastFrame)⟩

include parent tree unique parentTyped wellFormed runtime covers environments locals agrees typed firstAdmission
  post stages caller sidecarSource dispatch accepted different calleeTrace in
/-- Native reflection retains either the earlier actual argument fault or the
true closure arity rejection. The original binds supply the strict child grade;
Source reconstruction has its own independent grade and exact argument post. -/
theorem reflects_boundary (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      bridge model context evidence source certificate faults size)
    {size : Nat} {value : Value} {finalStore : Store}
    (evaluation : EvaluationSize size actual firstStore (lowered.expression.rename ξ) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize reason after token finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize context evidence source
        environment before id (.fault reason) after ∧ value = .inLeft lowered.type (.word token) ∧
      ResultAt (registry := registry) (faults := faults) (context := context) bridge profile compiler prepared first dispatch
        reason after token finalStore finalMap finalWorld := by
  obtain ⟨calleeEvaluation, represented, heaps, maps, worlds, frame, calleeMetadata, calleeState, related, calleePost⟩ := post
  have calleeAdmission := calleePost.at_value.2
  obtain ⟨parameter, sourceResult, rawTypes, _calleeTyping, argumentsTyping, application⟩ :=
    CallableIndexedOwnedStoredClosureArgumentReceipts.original_facts unique compiler.found compiler.originalForm parentTyped
  have count : rawTypes.length = metadata.argumentCount := by cases application with | intro count _ _ _ => exact count.symm
  have selected := actual_selected compiler prepared unique stages caller sidecarSource dispatch
  have stage := CallableIndexedOwnedSelectedCallStageAcceptance.before_arguments dispatch accepted native.diagnostics.unknown
  have arity := rejected_gate dispatch selected different native.diagnostics.unknown
  rw [prepared.lowered_rename compiler ξ] at evaluation
  have loweredType : lowered.type = compiler.resultType :=
    (congrArg (fun output => output.type) compiler.output).trans compiler.resultTypeEq.symm
  have layout : EnvironmentsAgree ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ξ)) canonical (.unit :: calleeNative :: actual) :=
    GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix agrees calleeNative) .unit
  have actualTyped := RuntimeEnvironmentHasTypes.cons RuntimeValueHasType.unit
    (RuntimeEnvironmentHasTypes.cons represented.runtime_hasType (typed.weaken worlds))
  cases completed dispatch.shape calleeEvaluation stage arity evaluation within with
  | failed argumentsTrace smaller =>
    rw [← GenericExpressionMeaning.rename_prefix, ← GenericExpressionMeaning.rename_prefix] at argumentsTrace
    obtain ⟨argumentsSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
        lastMaps, lastWorlds, lastFrame, lastMetadata, reached, lastRelated, _argumentPost⟩ :=
      CallableIndexedOwnedAdmittedExpressionSequence.reflects_bounded bridge budget tree unique argumentsTyping children
        (environments.extend maps worlds) heaps (locals.mono calleeMetadata) layout actualTyped
        calleeState calleeAdmission argumentsTrace smaller
    cases represented with
    | fault matched =>
      cases trace with
      | fault failed =>
        obtain ⟨sourceSize, original⟩ := SourceSuffix.to_expression compiler.found compiler.originalForm parent.requirements parent.coercions
          compiler.argumentCoercions parent.arity wellFormed runtime covers (locals.mono calleeMetadata) calleeAdmission.heap
          argumentsTyping count calleeTrace (SourceSuffix.argumentFault failed)
        exact ⟨sourceSize, _, after, _, finalMap, finalWorld, original, by rw [loweredType], Or.inl matched,
          finalHeaps, maps.trans lastMaps, worlds.trans lastWorlds, frame.trans lastFrame, calleeMetadata.trans lastMetadata,
          reached, callerProtocol.trans related lastRelated,
          after_expression_sized first reached firstAdmission wellFormed runtime covers locals parentTyped original (frame.trans lastFrame)⟩
  | rejected argumentsTrace smaller =>
    rw [← GenericExpressionMeaning.rename_prefix, ← GenericExpressionMeaning.rename_prefix] at argumentsTrace
    obtain ⟨argumentsSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
        lastMaps, lastWorlds, lastFrame, lastMetadata, reached, lastRelated, _argumentPost⟩ :=
      CallableIndexedOwnedAdmittedExpressionSequence.reflects_bounded bridge budget tree unique argumentsTyping children
        (environments.extend maps worlds) heaps (locals.mono calleeMetadata) layout actualTyped
        calleeState calleeAdmission argumentsTrace smaller
    cases represented with
    | @values sources values _values =>
      cases trace with
      | values sourceArguments =>
        have argumentsCount := arguments_count_of_source_admission wellFormed runtime covers (locals.mono calleeMetadata)
          calleeAdmission.heap argumentsTyping count sourceArguments
        have actualCount : _ = ids.length := argumentsCount.trans parent.arity.symm
        have rejected : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) (SourceExecutionSize.stepSize [])
            context evidence function.evidence after (.closure function) sources
            (.fault (.argumentArityMismatch function.parameters.length ids.length)) after := by
          rw [← actualCount]
          exact .fault (.closureArity (actualCount.symm ▸ different))
        obtain ⟨sourceSize, original⟩ := SourceSuffix.to_expression compiler.found compiler.originalForm parent.requirements parent.coercions
          compiler.argumentCoercions parent.arity wellFormed runtime covers (locals.mono calleeMetadata) calleeAdmission.heap
          argumentsTyping count calleeTrace (SourceSuffix.called sourceArguments rejected)
        exact ⟨sourceSize, _, after, arityToken, finalMap, finalWorld, original, by rw [loweredType], Or.inr ⟨rfl, rfl⟩,
          finalHeaps, maps.trans lastMaps, worlds.trans lastWorlds, frame.trans lastFrame, calleeMetadata.trans lastMetadata,
          reached, callerProtocol.trans related lastRelated,
          after_expression_sized first reached firstAdmission wellFormed runtime covers locals parentTyped original (frame.trans lastFrame)⟩
end Boundary
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredClosureArityBoundary
