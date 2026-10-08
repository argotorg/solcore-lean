import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectCalleePost
import Solcore.SourceSemantics.CoreLowering.CallableIndirectCallBounds

/-! A real rejected first-stage guard stops at the actual successful callee
post. Source staging faults retain their own CallBoundary outcome, beside the
unchanged callee admission and cumulative pool effects. Two original bind
inversions preserve the actual native child grades and full parent bound.
There is no argument or body invocation, plain Dynamic fault conversion,
whole-expression law, or recursively staged whole-language claim. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectStageBoundary
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters
universe u

/-- The authentic attached guard chooses this exact beforeArguments error. -/
theorem gate_rejected
    {frame : Staging.CallBoundary.Frame} {site : SourceCoreCallableContracts.Callsite}
    {call : ExpressionId} {ids : List ExpressionId} {sourceValue : Dynamic.Value} {carrier : Value}
    (dispatch : CallStageBoundary.Dispatch frame site call ids sourceValue carrier)
    {reason : Staging.CallGuard.Fault} (rejected : Staging.CallBoundary.GuardRejects frame call ids sourceValue reason)
    (unknown : Word) (actual : Environment) (store : Store) :
    Evaluates (carrier :: actual) store
      (CallableContract.dispatch site.gates .beforeArguments unknown (.second (.var 0)))
      (.inLeft .unit (.word (dispatch.reason reason))) store := by
  have read : Evaluates (carrier :: actual) store (.second (.var 0)) (.word dispatch.contract) store :=
    .second (.var (by simpa only [List.getElem?_cons_zero] using congrArg some dispatch.shape))
  have original := site.dispatch_known .beforeArguments unknown dispatch.contract dispatch.row dispatch.found read
  rw [SourceCoreCallableContracts.reason_rejected dispatch.row site.reasonAt .beforeArguments _ (dispatch.rejected rejected)] at original
  exact original

/-- These are the original two strict children at the exact callee store. -/
def RejectedCompletion (budget : Nat) (site : SourceCoreCallableContracts.Callsite) (unknown : Word)
    (callee : Expr) (actual : Environment) (before calleeStore : Store) (carrier : Value) (token : Word) : Prop :=
  ∃ calleeSize gateSize,
    EvaluationSize calleeSize actual before callee (.inRight .word carrier) calleeStore ∧
    EvaluationSize gateSize (carrier :: actual) calleeStore
      (CallableContract.dispatch site.gates .beforeArguments unknown (.second (.var 0)))
      (.inLeft .unit (.word token)) calleeStore ∧
    calleeSize < budget ∧ gateSize < budget

/-- Finite inversion of the two existing binds fixes the rejected first gate.
The entire supplied native grade remains within its original budget. -/
theorem completed_rejected
    {budget size : Nat} {site : SourceCoreCallableContracts.Callsite} {unknown : Word}
    {callee arguments : Expr} {actual : Environment} {before calleeStore after : Store}
    {carrier value : Value} {token : Word} {result : Ty}
    (calleeEvaluation : Evaluates actual before callee (.inRight .word carrier) calleeStore)
    (gateEvaluation : Evaluates (carrier :: actual) calleeStore
      (CallableContract.dispatch site.gates .beforeArguments unknown (.second (.var 0)))
      (.inLeft .unit (.word token)) calleeStore)
    (completed : EvaluationSize size actual before
      (CallableContract.call site.gates unknown result callee arguments) value after)
    (within : size ≤ budget) :
    value = .inLeft result (.word token) ∧ after = calleeStore ∧
      RejectedCompletion budget site unknown callee actual before calleeStore carrier token := by
  cases CallableIndirectCallBounds.bind_completed completed within with
  | failed child _ =>
    have same := (evaluation_deterministic child.sound calleeEvaluation).1
    cases same
  | continued child remaining childStrict remainingStrict =>
    obtain ⟨same, stores⟩ := evaluation_deterministic child.sound calleeEvaluation
    cases same
    subst stores
    cases CallableIndirectCallBounds.bind_completed remaining (Nat.le_of_lt remainingStrict) with
    | failed gate gateStrict =>
      obtain ⟨same, stores⟩ := evaluation_deterministic gate.sound gateEvaluation
      cases same
      subst stores
      exact ⟨rfl, rfl, _, _, child, gate, childStrict, gateStrict⟩
    | continued gate _ _ _ =>
      have same := (evaluation_deterministic gate.sound gateEvaluation).1
      cases same

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
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {calleeNode : ExpressionNode}
  {firstMap mapping : LocationMap} {firstWorld world : StoreTyping}
  {before calleeHeap : Dynamic.Heap} {firstStore store : Store}
  {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
  (first : callerProtocol.State ⟨scope, firstMap, firstWorld, before, firstStore, canonical⟩)
  {sourceValue : Dynamic.Value} {calleeNative : Value}
  (post : CallableIndexedOwnedStoredIndirectCalleePost.ValuePost (registry := registry) (faults := faults)
    (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context) bridge profile compiler first
    sourceValue calleeHeap calleeNative store mapping world)
  {sidecar : SourceCoreStageContracts.Sidecar}
  (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (sidecarSource : sidecar.source = source)
  (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids sourceValue calleeNative)
  {reason : Staging.CallGuard.Fault}
  (rejected : Staging.CallBoundary.GuardRejects (CallableLedger.frame sidecar) prepared.site.call ids sourceValue reason)
  {calleeSize : Nat}
  (calleeTrace : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) calleeSize
    context evidence source environment before callee sourceValue calleeHeap)

/-- The complete original value post remains beside the genuine staged fault.
It is the callee's admission, not a plain Dynamic parent fault admission. -/
def ResultAt (reason : Staging.CallGuard.Fault) (token : Word) (finalStore : Store) : Prop :=
  SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar ∧
  sidecar.source = source ∧
  CallableIndexedOwnedStoredIndirectCalleePost.ValuePost (registry := registry) (faults := faults)
    (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context) bridge profile compiler first
    sourceValue calleeHeap calleeNative store mapping world ∧
  SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) calleeSize
    context evidence source environment before callee sourceValue calleeHeap ∧
  Staging.CallBoundary.Executes (Program.ofChecked compiled.sourceProgram) (CallableLedger.frame sidecar)
    context evidence source environment before id callee ids metadata (.stageFault reason) calleeHeap ∧
  token = dispatch.reason reason ∧ CallStageBoundary.ReasonRepresents prepared.site reason token ∧
  finalStore = store ∧
  Evaluates actual firstStore (lowered.expression.rename ξ)
    (.inLeft compiler.resultType (.word token)) finalStore

include caller sidecarSource post rejected calleeTrace in
/-- The actual Source stage rejection emits its first-gate word at the same
callee pool, before any argument or body computation. -/
theorem preserves_rejected :
    ResultAt (registry := registry) (faults := faults) (context := context) (evidence := evidence)
      (calleeNode := calleeNode) (mapping := mapping) (world := world) (calleeHeap := calleeHeap) (store := store)
      (environment := environment) (actual := actual) (ξ := ξ) (calleeSize := calleeSize) bridge profile compiler prepared first dispatch reason (dispatch.reason reason) store := by
  have failed := dispatch.rejected rejected
  have calleeEvaluation := post.1
  rw [dispatch.shape] at calleeEvaluation
  have whole := prepared.site.lower_stage_failure (result := compiler.resultType)
    (arguments := (SourceCoreCalls.packArguments compiler.codes).expression.rename ξ) native.diagnostics.unknown dispatch.row
    (CallStageGuard.error dispatch.guard.sidecar.caller dispatch.guard.node dispatch.guard.contract.owner reason)
    dispatch.found failed calleeEvaluation
  have original : Staging.CallBoundary.Executes (Program.ofChecked compiled.sourceProgram) (CallableLedger.frame sidecar)
      context evidence source environment before id callee ids metadata (.stageFault reason) calleeHeap :=
    .stageRejected calleeTrace.sound (by simpa only [prepared.call] using rejected)
  refine ⟨caller, sidecarSource, post, calleeTrace, original, rfl, dispatch.reason_represents reason, rfl, ?_⟩
  simpa only [SourceCoreCallableContracts.Callsite.lower, CallStageBoundary.Dispatch.reason, prepared.lowered_rename compiler ξ] using whole

include caller sidecarSource post rejected calleeTrace in
/-- A real bounded native completion reflects the exact same staged fault and
callee post while retaining both original strict native child bounds. -/
theorem reflects_rejected (budget : Nat) {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual firstStore (lowered.expression.rename ξ) value finalStore)
    (within : size ≤ budget) :
    ∃ token, value = .inLeft compiler.resultType (.word token) ∧
      ResultAt (registry := registry) (faults := faults) (context := context) (evidence := evidence)
      (calleeNode := calleeNode) (mapping := mapping) (world := world) (calleeHeap := calleeHeap) (store := store)
      (environment := environment) (actual := actual) (ξ := ξ) (calleeSize := calleeSize) bridge profile compiler prepared first dispatch reason token finalStore ∧
      RejectedCompletion budget prepared.site native.diagnostics.unknown (compiler.calleeCode.expression.rename ξ)
        actual firstStore store calleeNative token := by
  have exactGate := gate_rejected dispatch rejected native.diagnostics.unknown actual store
  have full := completed
  rw [prepared.lowered_rename compiler ξ] at full
  obtain ⟨same, storeEq, bounds⟩ := completed_rejected post.1 exactGate full within
  subst finalStore
  exact ⟨dispatch.reason reason, same,
    preserves_rejected bridge profile compiler prepared first post caller sidecarSource dispatch rejected calleeTrace, bounds⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectStageBoundary
