import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectStageBoundary

/-! Strict callee IH constructs one actual successful post internally. Only
that produced witness accepts its genuine attached Dispatch and GuardRejects;
no classifier or law promising those static receipts for arbitrary posts is
supplied. Native reflection consumes the actual strict callee child receipt,
then the original two-bind boundary retains the full parent budget. Callee
semantic faults remain a separate genuine staged outcome at their own post. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectStageChildren
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

include certified found sourceTyped environments heaps locals agrees typed admitted caller sidecarSource in
/-- The Source child IH produces one real post; concrete dispatch evidence is
consumed only at that single produced carrier. It is never manufactured. -/
theorem preserves_child (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      bridge model context evidence source certificate faults size)
    {size : Nat} {sourceValue : Dynamic.Value} {after : Dynamic.Heap}
    (trace : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) size
      context evidence source environment before callee sourceValue after)
    (smaller : size < budget) :
    ∃ value finalStore finalMap finalWorld,
      CallableIndexedOwnedStoredIndirectCalleePost.ValuePost (registry := registry) (faults := faults)
        (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context)
        bridge profile compiler initial sourceValue after value finalStore finalMap finalWorld ∧
      ∀ (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar)
          prepared.site prepared.site.call ids sourceValue value)
        (reason : Staging.CallGuard.Fault),
        Staging.CallBoundary.GuardRejects (CallableLedger.frame sidecar) prepared.site.call ids sourceValue reason →
        CallableIndexedOwnedStoredIndirectStageBoundary.ResultAt
          (registry := registry) (faults := faults) (context := context) (evidence := evidence)
          (calleeNode := calleeNode) (mapping := finalMap) (world := finalWorld) (calleeHeap := after) (store := finalStore)
          (environment := environment) (actual := actual) (ξ := ξ) (calleeSize := size)
          bridge profile compiler prepared initial dispatch reason (dispatch.reason reason) finalStore := by
  obtain ⟨value, finalStore, finalMap, finalWorld, post⟩ :=
    CallableIndexedOwnedStoredIndirectCalleePost.preserves_value bridge profile compiler certified found sourceTyped
      environments heaps locals agrees typed initial admitted budget children trace smaller
  refine ⟨value, finalStore, finalMap, finalWorld, post, ?_⟩
  intro dispatch reason rejected
  exact CallableIndexedOwnedStoredIndirectStageBoundary.preserves_rejected bridge profile compiler prepared initial post
    caller sidecarSource dispatch rejected trace

include certified found sourceTyped environments heaps locals agrees typed admitted caller sidecarSource in
/-- Reflection derives the independent Source callee grade and actual post
from the real strict native child. A genuine rejected receipt at that witness
then uses the full original parent completion, including its real budget. -/
theorem reflects_child (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      bridge model context evidence source certificate faults size)
    {calleeSize size : Nat} {value calleeNative : Value} {calleeStore finalStore : Store}
    (child : EvaluationSize calleeSize actual store (compiler.calleeCode.expression.rename ξ)
      (.inRight .word calleeNative) calleeStore)
    (childStrict : calleeSize < budget)
    (completed : EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize sourceValue after finalMap finalWorld,
      SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) sourceSize
        context evidence source environment before callee sourceValue after ∧
      CallableIndexedOwnedStoredIndirectCalleePost.ValuePost (registry := registry) (faults := faults)
        (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context)
        bridge profile compiler initial sourceValue after calleeNative calleeStore finalMap finalWorld ∧
      ∀ (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar)
          prepared.site prepared.site.call ids sourceValue calleeNative)
        (reason : Staging.CallGuard.Fault),
        Staging.CallBoundary.GuardRejects (CallableLedger.frame sidecar) prepared.site.call ids sourceValue reason →
        ∃ token, value = .inLeft compiler.resultType (.word token) ∧
          CallableIndexedOwnedStoredIndirectStageBoundary.ResultAt
            (registry := registry) (faults := faults) (context := context) (evidence := evidence)
            (calleeNode := calleeNode) (mapping := finalMap) (world := finalWorld) (calleeHeap := after) (store := calleeStore)
            (environment := environment) (actual := actual) (ξ := ξ) (calleeSize := sourceSize)
            bridge profile compiler prepared initial dispatch reason token finalStore ∧
          CallableIndexedOwnedStoredIndirectStageBoundary.RejectedCompletion budget prepared.site native.diagnostics.unknown
            (compiler.calleeCode.expression.rename ξ) actual store calleeStore calleeNative token := by
  obtain ⟨sourceSize, sourceValue, after, finalMap, finalWorld, trace, post⟩ :=
    CallableIndexedOwnedStoredIndirectCalleePost.reflects_value bridge profile compiler certified found sourceTyped
      environments heaps locals agrees typed initial admitted budget children child childStrict
  refine ⟨sourceSize, sourceValue, after, finalMap, finalWorld, trace, post, ?_⟩
  intro dispatch reason rejected
  exact CallableIndexedOwnedStoredIndirectStageBoundary.reflects_rejected bridge profile compiler prepared initial post
    caller sidecarSource dispatch rejected trace budget completed within

include prepared certified found sourceTyped parentTyped wellFormed runtime covers
  environments heaps locals agrees typed admitted caller sidecarSource in
/-- A Source callee fault invokes only its strict child and remains the genuine
semanticFault alternative of Staging.CallBoundary at that same reached heap. -/
theorem preserves_callee_fault (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      bridge model context evidence source certificate faults size)
    {size : Nat} {reason : Dynamic.SemanticFault} {after : Dynamic.Heap}
    (fault : SourceExecutionSize.ExpressionFaults (Program.ofChecked compiled.sourceProgram) size
      context evidence source environment before callee reason after)
    (smaller : size < budget) :
    ∃ sourceSize token finalStore finalMap finalWorld,
      SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar ∧
      sidecar.source = source ∧
      Staging.CallBoundary.Executes (Program.ofChecked compiled.sourceProgram) (CallableLedger.frame sidecar)
        context evidence source environment before id callee ids metadata (.semanticFault reason) after ∧
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        context evidence source environment before id (.fault reason) after ∧
      Evaluates actual store (lowered.expression.rename ξ) (.inLeft lowered.type (.word token)) finalStore ∧
      CallableIndexedOwnedStoredIndirectCallBounds.ResultAt (registry := registry) (faults := faults) (context := context)
        bridge profile compiler initial (.fault reason) after (.inLeft lowered.type (.word token)) finalStore finalMap finalWorld := by
  obtain ⟨sourceSize, token, finalStore, finalMap, finalWorld, original, evaluated, post⟩ :=
    CallableIndexedOwnedStoredIndirectCalleePost.preserves_fault bridge profile compiler prepared certified found sourceTyped
      parentTyped wellFormed runtime covers environments heaps locals agrees typed initial admitted budget children fault smaller
  exact ⟨sourceSize, token, finalStore, finalMap, finalWorld, caller, sidecarSource, .calleeFault fault.sound, original, evaluated, post⟩


include prepared certified found sourceTyped parentTyped wellFormed runtime covers
  environments heaps locals agrees typed admitted caller sidecarSource in
/-- Native callee failure reflects only its real strict child, before either
guard. Its raw Source child grade and enclosing Source grade are independent
of native size; the same child pool supplies the actual parent admission. -/
theorem reflects_callee_fault (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      bridge model context evidence source certificate faults size)
    {size : Nat} {token : Word} {finalStore : Store}
    (completed : EvaluationSize size actual store (compiler.calleeCode.expression.rename ξ)
      (.inLeft compiler.calleeCode.type (.word token)) finalStore)
    (smaller : size < budget) :
    ∃ childSourceSize parentSourceSize reason after finalMap finalWorld,
      SourceExecutionSize.ExpressionFaults (Program.ofChecked compiled.sourceProgram) childSourceSize
        context evidence source environment before callee reason after ∧
      SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar ∧
      sidecar.source = source ∧
      Staging.CallBoundary.Executes (Program.ofChecked compiled.sourceProgram) (CallableLedger.frame sidecar)
        context evidence source environment before id callee ids metadata (.semanticFault reason) after ∧
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) parentSourceSize
        context evidence source environment before id (.fault reason) after ∧
      Evaluates actual store (lowered.expression.rename ξ) (.inLeft lowered.type (.word token)) finalStore ∧
      CallableIndexedOwnedStoredIndirectCallBounds.ResultAt (registry := registry) (faults := faults) (context := context)
        bridge profile compiler initial (.fault reason) after (.inLeft lowered.type (.word token)) finalStore finalMap finalWorld := by
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, _post⟩ :=
    children size smaller certified found sourceTyped environments heaps locals agrees typed initial admitted completed
  cases represented with
  | fault matched =>
    rename_i reason
    cases trace with
    | fault failed =>
      have original : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram)
          (SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [sourceSize]]) context evidence source environment
          before id (.fault reason) after := by
        refine .fault (.form (size_fault := SourceExecutionSize.stepSize [sourceSize]) (lookupExpression?_sound compiler.found) ?_)
        rw [compiler.originalForm]
        exact .indirectCallee failed
      have whole := CallableContract.call_callee_failure (result := compiler.resultType)
        (arguments := (SourceCoreCalls.packArguments compiler.codes).expression.rename ξ)
        prepared.site.gates native.diagnostics.unknown completed.sound
      rw [← prepared.lowered_rename compiler ξ] at whole
      have loweredType : lowered.type = compiler.resultType :=
        (congrArg (fun output => output.type) compiler.output).trans compiler.resultTypeEq.symm
      rw [← loweredType] at whole
      exact ⟨sourceSize, _, _, after, finalMap, finalWorld, failed, caller, sidecarSource,
        .calleeFault failed.sound, original, whole, .fault matched, finalHeaps, maps, worlds, frame, metadata,
        reached, related, after_expression_sized initial reached admitted wellFormed runtime covers locals parentTyped original frame⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectStageChildren
