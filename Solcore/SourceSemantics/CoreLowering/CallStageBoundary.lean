import Solcore.SourceSemantics.Staging.CallBoundary
import Solcore.SourceSemantics.CoreLowering.CallStageGuard
import Solcore.SourceSemantics.CoreLowering.GenericExpressionMeaning
import Solcore.Frontend.SourceCoreCallableContracts

/-! A stage-rejected indirect-call boundary preserves the exact callee prefix.
The child theorem is universal over related states; no child Core evaluation is
assumed. Static dispatch coverage relates artifact descriptors to the explicit
source contract ledger and original retained guard receipts. It is a separate
obligation of the enclosing compiler profile, not inferred from Core typing.

The result is for the staged CallBoundary extension. Plain Dynamic and recursive
stage-frame propagation are deliberately outside this theorem. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallStageBoundary
open Core Frontend Frontend.SourceInference GeneralHeap ReadOnly

/-- All fields concern static provenance and value representation. In
particular this certificate does not contain a guard verdict or an evaluation. -/
structure Dispatch (frame : Staging.CallBoundary.Frame) (site : SourceCoreCallableContracts.Callsite)
    (call : ExpressionId) (arguments : List ExpressionId) (source : Dynamic.Value) (carrier : Value) where
  function : Value
  contract : Word
  row : SourceCoreStageCodebook.Decision
  guard : SourceCoreStageContracts.Guard
  shape : carrier = .pair function (.word contract)
  found : site.rowAt? contract = some row
  attached : row.guard = some guard
  call_eq : guard.node.id = call
  arguments_eq : guard.arguments = arguments
  stages : frame.stages = CallStageGuard.frame guard.sidecar.caller
  bound : frame.Binds source ⟨guard.contract.parameters, guard.contract.stagedResult⟩

def Dispatch.reason {frame : Staging.CallBoundary.Frame} {site : SourceCoreCallableContracts.Callsite}
    {call : ExpressionId} {arguments : List ExpressionId} {source : Dynamic.Value} {carrier : Value}
    (dispatch : Dispatch frame site call arguments source carrier) (reason : Staging.CallGuard.Fault) : Word :=
  site.reasonAt dispatch.row.caller dispatch.row.call dispatch.row.entry.id .beforeArguments
    (CallStageGuard.error dispatch.guard.sidecar.caller dispatch.guard.node dispatch.guard.contract.owner reason)

theorem Dispatch.rejected {frame : Staging.CallBoundary.Frame} {site : SourceCoreCallableContracts.Callsite}
    {call : ExpressionId} {arguments : List ExpressionId} {source : Dynamic.Value} {carrier : Value}
    (dispatch : Dispatch frame site call arguments source carrier) {reason : Staging.CallGuard.Fault}
    (rejected : Staging.CallBoundary.GuardRejects frame call arguments source reason) :
    dispatch.row.beforeArguments = .error
      (CallStageGuard.error dispatch.guard.sidecar.caller dispatch.guard.node dispatch.guard.contract.owner reason) := by
  cases rejected with
  | contract bound rejected =>
    cases frame.unique bound dispatch.bound
    have guarded : Staging.CallGuard.Rejects (CallStageGuard.frame dispatch.guard.sidecar.caller)
        ⟨dispatch.guard.contract.parameters, dispatch.guard.contract.stagedResult⟩
        dispatch.guard.node.id dispatch.guard.arguments reason := by
      simpa only [dispatch.call_eq, dispatch.arguments_eq, ← dispatch.stages] using rejected
    have failed := (CallStageGuard.guard_rejects_iff dispatch.guard _).mpr ⟨reason, guarded, rfl⟩
    simpa only [SourceCoreStageCodebook.Decision.beforeArguments, SourceCoreStageCodebook.Decision.answer,
      dispatch.attached] using failed

/-- Accepted source guards select the exact success branch of the sealed row. -/
theorem Dispatch.accepted {frame : Staging.CallBoundary.Frame} {site : SourceCoreCallableContracts.Callsite}
    {call : ExpressionId} {arguments : List ExpressionId} {source : Dynamic.Value} {carrier : Value}
    (dispatch : Dispatch frame site call arguments source carrier)
    (accepted : Staging.CallBoundary.GuardAccepts frame call arguments source) :
    dispatch.row.beforeArguments = .ok () := by
  cases accepted with
  | builtin => cases frame.userCallable dispatch.bound
  | contract bound accepted =>
    cases frame.unique bound dispatch.bound
    have guarded : Staging.CallGuard.Accepts (CallStageGuard.frame dispatch.guard.sidecar.caller)
        ⟨dispatch.guard.contract.parameters, dispatch.guard.contract.stagedResult⟩
        dispatch.guard.node.id dispatch.guard.arguments := by
      simpa only [dispatch.call_eq, dispatch.arguments_eq, ← dispatch.stages] using accepted
    have passed := (CallStageGuard.guard_accepts_iff dispatch.guard).mpr guarded
    simpa only [SourceCoreStageCodebook.Decision.beforeArguments, SourceCoreStageCodebook.Decision.answer,
      dispatch.attached] using passed

/-- Gate acceptance reconstructs the source guard from its original metadata;
it is not assumed merely because the erased function carrier has a type. -/
theorem Dispatch.accepted_iff {frame : Staging.CallBoundary.Frame} {site : SourceCoreCallableContracts.Callsite}
    {call : ExpressionId} {arguments : List ExpressionId} {source : Dynamic.Value} {carrier : Value}
    (dispatch : Dispatch frame site call arguments source carrier) :
    dispatch.row.beforeArguments = .ok () ↔ Staging.CallBoundary.GuardAccepts frame call arguments source := by
  constructor
  · intro passed
    have guarded : dispatch.guard.decision = .ok () := by
      simpa only [SourceCoreStageCodebook.Decision.beforeArguments, SourceCoreStageCodebook.Decision.answer,
        dispatch.attached] using passed
    apply Staging.CallBoundary.GuardAccepts.contract dispatch.bound
    have accepted := (CallStageGuard.guard_accepts_iff dispatch.guard).mp guarded
    simpa only [dispatch.call_eq, dispatch.arguments_eq, ← dispatch.stages] using accepted
  · exact dispatch.accepted

/-- A retained gate error reconstructs the exact independent stage failure,
including original occurrence/index coordinates before word assignment. -/
theorem Dispatch.rejected_of_error {frame : Staging.CallBoundary.Frame} {site : SourceCoreCallableContracts.Callsite}
    {call : ExpressionId} {arguments : List ExpressionId} {source : Dynamic.Value} {carrier : Value}
    (dispatch : Dispatch frame site call arguments source carrier) (diagnostic : SourceCompilationPlan.Error)
    (failed : dispatch.row.beforeArguments = .error diagnostic) :
    ∃ reason, Staging.CallBoundary.GuardRejects frame call arguments source reason ∧
      diagnostic = CallStageGuard.error dispatch.guard.sidecar.caller dispatch.guard.node dispatch.guard.contract.owner reason := by
  have guarded : dispatch.guard.decision = .error diagnostic := by
    simpa only [SourceCoreStageCodebook.Decision.beforeArguments, SourceCoreStageCodebook.Decision.answer,
      dispatch.attached] using failed
  obtain ⟨reason, rejected, exactError⟩ := (CallStageGuard.guard_rejects_iff dispatch.guard diagnostic).mp guarded
  refine ⟨reason, Staging.CallBoundary.GuardRejects.contract dispatch.bound ?_, exactError⟩
  simpa only [dispatch.call_eq, dispatch.arguments_eq, ← dispatch.stages] using rejected

/-- Stage words retain the exact source failure under the selected sealed row. -/
def ReasonRepresents (site : SourceCoreCallableContracts.Callsite) (reason : Staging.CallGuard.Fault) (token : Word) : Prop :=
  ∃ row guard, row ∈ site.rows ∧ row.guard = some guard ∧
    token = site.reasonAt row.caller row.call row.entry.id .beforeArguments
      (CallStageGuard.error guard.sidecar.caller guard.node guard.contract.owner reason)

theorem Dispatch.reason_represents {frame : Staging.CallBoundary.Frame} {site : SourceCoreCallableContracts.Callsite}
    {call : ExpressionId} {arguments : List ExpressionId} {source : Dynamic.Value} {carrier : Value}
    (dispatch : Dispatch frame site call arguments source carrier) (reason : Staging.CallGuard.Fault) :
    ReasonRepresents site reason (dispatch.reason reason) :=
  ⟨dispatch.row, dispatch.guard, List.mem_of_find?_eq_some dispatch.found, dispatch.attached, rfl⟩

/-- Coverage is a property of the artifact's function-value relation and source
contract ledger. It does not assume the current call or any child completes. -/
def CoversFor {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
    (frame : Staging.CallBoundary.Frame) (site : SourceCoreCallableContracts.Callsite)
    (call : ExpressionId) (arguments : List ExpressionId) (sourceType : TypeSystem.Ty) (type : Ty) : Prop :=
  ∀ {mapping world source carrier contract}, model.Represents mapping world sourceType source carrier type →
    frame.Binds source contract → Nonempty (Dispatch frame site call arguments source carrier)

def Covers {catalog : SourceCoreDataCatalog.Catalog} (model : GenericHeap.PayloadModel catalog)
    (frame : Staging.CallBoundary.Frame) (site : SourceCoreCallableContracts.Callsite)
    (call : ExpressionId) (arguments : List ExpressionId) (sourceType : TypeSystem.Ty) (type : Ty) : Prop :=
  CoversFor model frame site call arguments sourceType type

/-- A finite staged-source rejection derives its Core callee computation from
the universal child theorem, then emits the exact language failure without
executing arguments. The post-callee heap, map/world and administrative frame
are retained, including any writes or allocations performed by the callee. -/
theorem preserves_rejection_for {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {certificate : GenericExpressionMeaning.Certificate} {faults : FunctionCalls.FaultRep}
    {frame : Staging.CallBoundary.Frame} {site : SourceCoreCallableContracts.Callsite} {call callee : ExpressionId}
    {arguments : List ExpressionId} {metadata : IndirectCallResolution} {scope : SourceCoreLocalCell.Scope}
    {lowered : SourceCoreBasic.LoweredExpr} {calleeNode : ExpressionNode}
    (certified : certificate scope callee lowered) (found : source.lookupExpression? callee = some calleeNode)
    (childMeaning : GenericExpressionMeaning.Preserves model program context evidence source certificate faults)
    (coverage : CoversFor model frame site call arguments calleeNode.type lowered.type)
    (unknown : Word) (result : Ty) (argumentCode : Expr)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {reason : Staging.CallGuard.Fault}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (execution : Staging.CallBoundary.Executes program frame context evidence source environment before call callee arguments metadata
      (.stageFault reason) after) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store (site.lower unknown result (lowered.expression.rename ξ) argumentCode)
        (.inLeft result (.word token)) finalStore ∧
      ReasonRepresents site reason token ∧ GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨callable, calleeEvaluation, rejected⟩ := Staging.CallBoundary.Executes.stageFault_iff.mp execution
  obtain ⟨carrier, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, framePreserved, metadataPreserved⟩ :=
    childMeaning certified found environments heaps locals layout (.value calleeEvaluation)
  cases represented with
  | value represented =>
    have binding : ∃ contract, frame.Binds callable contract := by cases rejected with | contract bound _ => exact ⟨_, bound⟩
    obtain ⟨contract, bound⟩ := binding
    obtain ⟨dispatch⟩ := coverage represented bound
    have failed := dispatch.rejected rejected
    rw [dispatch.shape] at evaluated
    exact ⟨dispatch.reason reason, finalStore, finalMap, finalWorld,
      site.lower_stage_failure unknown dispatch.row _ dispatch.found failed evaluated,
      dispatch.reason_represents reason, finalHeaps, maps, worlds, framePreserved, metadataPreserved⟩

theorem preserves_rejection {catalog : SourceCoreDataCatalog.Catalog} {model : GenericHeap.PayloadModel catalog}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {certificate : GenericExpressionMeaning.Certificate} {faults : FunctionCalls.FaultRep}
    {frame : Staging.CallBoundary.Frame} {site : SourceCoreCallableContracts.Callsite} {call callee : ExpressionId}
    {arguments : List ExpressionId} {metadata : IndirectCallResolution} {scope : SourceCoreLocalCell.Scope}
    {lowered : SourceCoreBasic.LoweredExpr} {calleeNode : ExpressionNode}
    (certified : certificate scope callee lowered) (found : source.lookupExpression? callee = some calleeNode)
    (childMeaning : GenericExpressionMeaning.Preserves model program context evidence source certificate faults)
    (coverage : Covers model frame site call arguments calleeNode.type lowered.type)
    (unknown : Word) (result : Ty) (argumentCode : Expr)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {reason : Staging.CallGuard.Fault}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (execution : Staging.CallBoundary.Executes program frame context evidence source environment before call callee arguments metadata
      (.stageFault reason) after) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store (site.lower unknown result (lowered.expression.rename ξ) argumentCode)
        (.inLeft result (.word token)) finalStore ∧
      ReasonRepresents site reason token ∧ GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after :=
  preserves_rejection_for certified found childMeaning coverage unknown result argumentCode
    environments heaps locals layout execution

end Solcore.SourceSemantics.CoreLowering.CallStageBoundary
