import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CallBounds
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.AssignmentContracts
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.CatalogOrigins
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.StageExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.SelectedGeneralCalls
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.IndirectDispatch
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.NamedAdmission
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.TerminalNamedCalls
import Solcore.SourceSemantics.CoreLowering.PublicSupport
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.StageStatements
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.PhysicalClosures
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.TerminalBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.StageForItems

/-!
# Lifting to staged Source: closures and indirect calls

Lifting of closure entry, application and packets, and of indirect calls, with the Source traces they start from.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosureSourceTrace
/-! The actual ordinary closure call supplies its full frame, the copies of its
captures and its parameter allocation. The retained mono parameter row
identifies the original body context. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosureSourceTrace
open Core Frontend SourceInference

private theorem binders_context_eq {owner : Resolved.DeclarationId}
    {before left right : SourceSemantics.Context} {parameters : List TypedBinder}
    {leftTypes rightTypes : List TypeSystem.Ty}
    (first : MonoBindersExtend owner before parameters leftTypes left)
    (second : MonoBindersExtend owner before parameters rightTypes right) : left = right := by
  have same := first.bodyTypes_eq.symm.trans second.bodyTypes_eq
  subst rightTypes
  exact first.functional second

theorem source_prefix {program : Program} {function : Dynamic.Closure}
    {callContext bodyContext : SourceSemantics.Context} {caller invocation : Dynamic.EvidenceEnvironment}
    {before after : Dynamic.Heap} {arguments : List Dynamic.Value} {types : List TypeSystem.Ty}
    {size : Nat} {outcome : Dynamic.ExpressionOutcome}
    (parameters : MonoBindersExtend function.source.owner function.context function.parameters types bodyContext)
    (arity : function.parameters.length = arguments.length)
    (trace : RecursiveNamedCallBounds.CallOutcome program size callContext caller invocation before
      (.closure function) arguments outcome after) :
    ∃ childSize entry copied environment bound,
      Dynamic.ClosureFrame program function ∧
      Dynamic.EnvironmentCopies function.source function.captured before entry copied ∧
      Dynamic.BindersAllocate entry copied function.parameters arguments environment bound ∧
      RecursiveNamedCallBounds.BodyTrace program childSize function bodyContext environment bound outcome after ∧
      childSize < size := by
  cases trace with
  | value applied =>
    cases applied with
    | closure _ valid extended copy allocated body returned =>
      have same := binders_context_eq extended parameters
      subst same
      subst_vars
      exact ⟨_, _, _, _, _, valid, copy, allocated, .returned body, SourceExecutionSize.child_lt_stepSize (by simp)⟩
    | closureUnit _ valid unit extended copy allocated body fellThrough =>
      have same := binders_context_eq extended parameters
      subst same
      obtain ⟨environment, rfl⟩ := fellThrough
      exact ⟨_, _, _, _, _, valid, copy, allocated, .unit unit body, SourceExecutionSize.child_lt_stepSize (by simp)⟩
  | fault failed =>
    cases failed with
    | notCallable invalid => exact False.elim (invalid trivial)
    | closureArity mismatch => exact False.elim (mismatch arity)
    | closureBody _ valid extended copy allocated body =>
      have same := binders_context_eq extended parameters
      subst same
      exact ⟨_, _, _, _, _, valid, copy, allocated, .fault body, SourceExecutionSize.child_lt_stepSize (by simp)⟩
    | closureControlEscape _ valid extended copy allocated body escaped =>
      have same := binders_context_eq extended parameters
      subst same
      exact ⟨_, _, _, _, _, valid, copy, allocated, .escaped body escaped, SourceExecutionSize.child_lt_stepSize (by simp)⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosureSourceTrace
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageIndirectSourceTrace
/-! Actual ordinary indirect evaluation exposes the callee before the ordered
arguments. Empty accepted argument coercions preserve the complete value list
at its original arity, without using a Source body preservation premise. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageIndirectSourceTrace
open Core Frontend SourceInference

inductive TraceAt (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource)
    (environment : Dynamic.Environment) (before : Dynamic.Heap)
    (callee : ExpressionId) (arguments : List ExpressionId) (size : Nat) :
    Dynamic.ExpressionOutcome → Dynamic.Heap → Prop where
  | calleeFault {child reason after}
      (failed : SourceExecutionSize.ExpressionFaults program child context evidence source environment before callee reason after)
      (smaller : child < size) : TraceAt program context evidence source environment before callee arguments size (.fault reason) after
  | notCallable {child value after}
      (evaluated : SourceExecutionSize.ExpressionEvaluates program child context evidence source environment before callee value after)
      (invalid : ¬ Dynamic.CallableValue value)
      (smaller : child < size) : TraceAt program context evidence source environment before callee arguments size (.fault .notCallable) after
  | argumentsFault {calleeSize argumentsSize value middle reason after}
      (calleeTrace : SourceExecutionSize.ExpressionEvaluates program calleeSize context evidence source environment before callee value middle)
      (callable : Dynamic.CallableValue value)
      (failed : SourceExecutionSize.ExpressionsFault program argumentsSize context evidence source environment middle arguments reason after)
      (calleeSmaller : calleeSize < size) (argumentsSmaller : argumentsSize < size) :
      TraceAt program context evidence source environment before callee arguments size (.fault reason) after
  | apply {calleeSize argumentsSize callSize value middle values argumentHeap invocation outcome after}
      (calleeTrace : SourceExecutionSize.ExpressionEvaluates program calleeSize context evidence source environment before callee value middle)
      (argumentsTrace : SourceExecutionSize.ExpressionsEvaluate program argumentsSize context evidence source environment middle arguments values argumentHeap)
      (called : RecursiveNamedCallBounds.CallOutcome program callSize context evidence invocation argumentHeap value values outcome after)
      (calleeSmaller : calleeSize < size) (argumentsSmaller : argumentsSize < size) (callSmaller : callSize < size) :
      TraceAt program context evidence source environment before callee arguments size outcome after

private theorem values_length {program : Program} {size : Nat} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {ids : List ExpressionId} {values : List Dynamic.Value}
    (trace : SourceExecutionSize.ExpressionsEvaluate program size context evidence source environment before ids values after) :
    ids.length = values.length := by
  induction ids generalizing size before values with
  | nil => cases trace; rfl
  | cons id ids ih =>
    cases trace with
    | cons head tail => exact congrArg Nat.succ (ih tail)

theorem source_inv
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id callee : ExpressionId} {arguments : List ExpressionId} {resolution : IndirectCallResolution}
    {node : ExpressionNode} {size : Nat} {outcome : Dynamic.ExpressionOutcome}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
    (form : node.form = .call callee arguments (.indirect resolution))
    (coercions : node.coercions = []) (argumentCoercions : resolution.argumentCoercions = [])
    (arity : arguments.length = resolution.argumentCount)
    (trace : RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment before id outcome after) :
    TraceAt program context evidence source environment before callee arguments size outcome after := by
  cases trace with
  | value evaluated =>
    obtain ⟨child, raw, smaller⟩ := RecursiveNamedExpressionSourceBounds.evaluation_raw_sized unique
      (lookupExpression?_sound found) (by intros; simp [form]) coercions evaluated
    rw [form] at raw
    cases raw with
    | indirectCall _ calleeTrace argumentsTrace packBefore path packAfter _sourceArity appliedArity applied =>
      rw [argumentCoercions] at path
      cases path
      have same := Dynamic.ValuesPack.injective_of_length_eq packBefore packAfter
        ((values_length argumentsTrace).symm.trans (arity.trans appliedArity.symm))
      cases same
      exact .apply calleeTrace argumentsTrace (.value applied)
        (Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller)
        (Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller)
        (Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller)
  | fault failed =>
    obtain ⟨child, raw, smaller⟩ := RecursiveNamedExpressionSourceBounds.fault_raw_sized unique
      (lookupExpression?_sound found) (by intros; simp [form]) coercions failed
    rw [form] at raw
    cases raw with
    | indirectCallee failed =>
      exact .calleeFault failed
        (Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller)
    | indirectNotCallable evaluated invalid =>
      exact .notCallable evaluated invalid
        (Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller)
    | indirectArguments calleeTrace callable failed =>
      exact .argumentsFault calleeTrace callable failed
        (Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller)
        (Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller)
    | indirectSourceArity _ _ mismatch => exact False.elim (mismatch arity.symm)
    | indirectArgumentCoercion _ _ _ _ failed => rw [argumentCoercions] at failed; cases failed
    | indirectApply calleeTrace argumentsTrace packBefore path packAfter _sourceArity appliedArity failed =>
      rw [argumentCoercions] at path
      cases path
      have same := Dynamic.ValuesPack.injective_of_length_eq packBefore packAfter
        ((values_length argumentsTrace).symm.trans (arity.trans appliedArity.symm))
      cases same
      exact .apply calleeTrace argumentsTrace (.fault failed)
        (Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller)
        (Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller)
        (Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller)

/-- The actual named application fixes its complete invocation dictionary.
Pre-body faults retain their original reason and grade. -/
theorem call_with_global_evidence
    {program : Program} {context : SourceSemantics.Context}
    {caller invocation : Dynamic.EvidenceEnvironment} {before after : Dynamic.Heap}
    {function : Dynamic.GlobalFunction} {arguments : List Dynamic.Value}
    {size : Nat} {outcome : Dynamic.ExpressionOutcome}
    (trace : RecursiveNamedCallBounds.CallOutcome program size context caller invocation before
      (.global function) arguments outcome after) :
    RecursiveNamedCallBounds.CallOutcome program size context caller function.evidence before
      (.global function) arguments outcome after := by
  cases trace with
  | value applied =>
    cases applied with
    | global instantiated same covers body =>
      cases same
      exact .value (.global instantiated rfl covers body)
  | fault failed =>
    cases failed with
    | notCallable invalid => exact False.elim (invalid trivial)
    | globalSignatureMissing missing => exact .fault (.globalSignatureMissing missing)
    | globalBodyMissing missing => exact .fault (.globalBodyMissing missing)
    | globalArity instantiated mismatch => exact .fault (.globalArity instantiated mismatch)
    | globalBody instantiated same body =>
      cases same
      exact .fault (.globalBody instantiated rfl body)

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageIndirectSourceTrace
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageIndirectCalleeLifting
/-! A lifted indirect callee reaches its actual physical payload before the
original authenticated stage guard is classified. Rejection preserves that
prefix heap; acceptance retains the same state for ordered arguments. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageIndirectCalleeLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open SelectedCompilationStageLiftBounds (LiftsAt)
open CallableIndexedOwnedPreparedStagedIndirectNativePrefix (CalleePost)
open CallableIndexedOwnedPreparedStagedSelectedGeneralCallHeadBounds (Port)
open Staging.Recursive.Lifting (ExpressionLift)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {functions : CallableIndexedOwnedPositiveFunctionModels.Receiving headers keys bodyRegistry semanticFaults profile}
  [positive : SelectedCompilationCallableOrigins.Origins headers keys bodyRegistry semanticFaults profile functions]
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation invocation.source scope
    id callee ids metadata reasonAt lowered)
  (port : Port (compiled := compiled) (invocation := invocation) compiler)
  (certified : certificate scope callee compiler.calleeCode)
  (sourceTyped : ExpressionHasType invocation.source context callee port.calleeNode.type)
  {sourceTypes : List TypeSystem.Ty}
  (tree : DataExpressionSequence.Tree invocation.source certificate scope ids sourceTypes compiler.codes)
  (unique : NodeOccurrencesUnique invocation.source)
  (parentTyped : ExpressionHasType invocation.source context id compiler.original.type)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
  {canonical actual : Environment} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions

include positive port tree unique parentTyped in
theorem guard_at {value : Dynamic.Value} {after : Dynamic.Heap}
    {carrier : Value} {calleeStore : Store} {finalMap : LocationMap} {finalWorld : StoreTyping}
    (post : CalleePost (registry := registry) (context := context) (actual := actual) (ξ := ξ)
      (calleeNode := port.calleeNode) bridge functions compiler initial
      value after carrier calleeStore finalMap finalWorld) :
    Staging.CallBoundary.GuardAccepts invocation.guards id ids value ∨
      ∃ reason, Staging.CallBoundary.GuardRejects invocation.guards id ids value reason := by
  obtain ⟨_original, _originalMetadata, _contained, _form, _view, boundary⟩ :=
    CallableIndexedOwnedPreparedStagedIndirectArgumentPrefix.scoped_boundary
      (sourceEq := rfl) (found := port.calleeFound) (sourceParent := port.sourceParent)
      (tree := tree) (unique := unique) (parentTyped := parentTyped)
      bridge profile compiler port.prepared initial port.caller port.view port.originalUnique post
  cases boundary with
  | user dispatch _selected =>
    rcases Staging.CallGuard.complete (CallableLedger.frame port.sidecar).stages _ port.prepared.site.call ids with accepted | ⟨reason, rejected⟩
    · left
      simpa only [port.guardFrame, port.prepared.call] using
        (Staging.CallBoundary.GuardAccepts.contract dispatch.bound accepted)
    · right
      refine ⟨reason, ?_⟩
      simpa only [port.guardFrame, port.prepared.call] using
        (Staging.CallBoundary.GuardRejects.contract dispatch.bound rejected)
  | builtin _receipt => exact .inl (.builtin _)

include positive certified sourceTyped tree unique parentTyped environments heaps locals agrees typed admitted in
theorem callee_value (budget : Nat)
    (children : ∀ childSize, childSize < budget → LiftsAt bridge context model stages invocation certificate childSize)
    (preservation : ∀ stageSize, CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesAt
      bridge context model stages invocation certificate faults stageSize)
    {size : Nat} {value : Dynamic.Value} {calleeHeap : Dynamic.Heap}
    {plain : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) size context
      invocation.evidence invocation.source environment before callee value calleeHeap)
    (smaller : size < budget) :
    ExpressionLift (Program.ofChecked compiled.sourceProgram) stages invocation context environment before id plain after ∨
    ∃ carrier calleeStore finalMap finalWorld,
      Staging.Recursive.Expression (Program.ofChecked compiled.sourceProgram) stages invocation context environment
        before callee (.value value) calleeHeap ∧
      CalleePost (registry := registry) (context := context) (actual := actual) (ξ := ξ)
        (calleeNode := port.calleeNode) bridge functions compiler initial
        value calleeHeap carrier calleeStore finalMap finalWorld ∧
      Staging.CallBoundary.GuardAccepts invocation.guards id ids value := by
  have occurrence : Staging.Recursive.Occurrence invocation id (.call callee ids (.indirect metadata)) :=
    ⟨compiler.original, lookupExpression?_sound compiler.found, compiler.originalForm,
      port.sourceParent.requirements, port.sourceParent.coercions⟩
  obtain ⟨staged, reached, lifted, adapted⟩ := children size smaller certified port.calleeFound
    sourceTyped environments heaps locals agrees typed initial admitted (.value trace)
  cases adapted with
  | rejected origin call reason reached =>
    exact .inl ⟨_, _, .calleeFault occurrence lifted, .rejected origin call reason _⟩
  | completed =>
    obtain ⟨stageSize, measured⟩ := Staging.Recursive.Size.Expression.of_trace lifted
    obtain ⟨carrier, calleeStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
        maps, worlds, frame, metadata, reached, related, post⟩ :=
      preservation stageSize certified port.calleeFound sourceTyped environments heaps locals agrees typed initial admitted measured
    cases represented with
    | value payload =>
      have full : CalleePost (registry := registry) (context := context) (actual := actual) (ξ := ξ)
          (calleeNode := port.calleeNode) bridge functions compiler initial
          value calleeHeap _ calleeStore finalMap finalWorld :=
        ⟨evaluated, payload, finalHeaps, maps, worlds, frame, metadata, reached, related, post⟩
      rcases guard_at bridge profile compiler port tree unique parentTyped initial full with accepted | ⟨reason, rejected⟩
      · exact .inr ⟨_, _, _, _, lifted, full, accepted⟩
      · exact .inl ⟨_, _, .rejected occurrence lifted rejected, .rejected invocation id reason _⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageIndirectCalleeLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageIndirectPrefixLifting
/-! The original ordinary indirect call reaches either its exact staged
outcome or the genuine post-argument application prefix. Every nested rejection
keeps the heap reached before the remaining ordinary effects. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2200000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageIndirectPrefixLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open SelectedCompilationStageLiftBounds (LiftsAt)
open CallableIndexedOwnedPreparedStagedIndirectNativePrefix (CalleePost)
open CallableIndexedOwnedPreparedStagedSelectedGeneralCallHeadBounds (Port)
open Staging.Recursive.Lifting (ExpressionLift)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {functions : CallableIndexedOwnedPositiveFunctionModels.Receiving headers keys bodyRegistry semanticFaults profile}
  [positive : SelectedCompilationCallableOrigins.Origins headers keys bodyRegistry semanticFaults profile functions]
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation invocation.source scope
    id callee ids metadata reasonAt lowered)
  (port : Port (compiled := compiled) (invocation := invocation) compiler)
  (certified : certificate scope callee compiler.calleeCode)
  (sourceTyped : ExpressionHasType invocation.source context callee port.calleeNode.type)
  {sourceTypes : List TypeSystem.Ty}
  (tree : DataExpressionSequence.Tree invocation.source certificate scope ids sourceTypes compiler.codes)
  (unique : NodeOccurrencesUnique invocation.source)
  (parentTyped : ExpressionHasType invocation.source context id compiler.original.type)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
  {canonical actual : Environment} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions


def ApplicationPrefix (budget : Nat) (plain : Dynamic.ExpressionOutcome) (after : Dynamic.Heap) : Prop :=
  ∃ calleeSize argumentsSize callSize sourceValue calleeHeap argumentsHeap sources callEvidence,
    Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages calleeSize
      invocation context environment before callee (.value sourceValue) calleeHeap ∧
    Staging.CallBoundary.GuardAccepts invocation.guards id ids sourceValue ∧
    Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages argumentsSize
      invocation context environment calleeHeap ids (.values sources) argumentsHeap ∧
    RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) callSize
      context invocation.evidence callEvidence argumentsHeap sourceValue sources plain after ∧
    callSize < budget ∧
    SelectedCompilationIndirectValuesPrefix.ValuesPrefix
      (functionModel := functions) (registry := registry) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeNode := port.calleeNode) (sidecar := port.sidecar)
      bridge profile compiler port.prepared initial sourceValue calleeHeap argumentsHeap sources

include positive certified sourceTyped tree unique parentTyped environments heaps locals agrees typed admitted in
theorem lift_prefix (budget : Nat)
    (children : ∀ childSize, childSize < budget → LiftsAt bridge context model stages invocation certificate childSize)
    (preservation : ∀ stageSize, CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesAt
      bridge context model stages invocation certificate faults stageSize)
    {size : Nat} {plain : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (execution : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) size
      context invocation.evidence invocation.source environment before id plain after)
    (within : size ≤ budget) :
    ExpressionLift (Program.ofChecked compiled.sourceProgram) stages invocation context environment before id plain after ∨
    ApplicationPrefix (functions := functions) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) (registry := registry) (context := context) (stages := stages)
      (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes) (environment := environment)
      bridge profile compiler port initial budget plain after := by
  have occurrence : Staging.Recursive.Occurrence invocation id (.call callee ids (.indirect metadata)) :=
    ⟨compiler.original, lookupExpression?_sound compiler.found, compiler.originalForm,
      port.sourceParent.requirements, port.sourceParent.coercions⟩
  obtain ⟨_parameter, _result, _functionType, argumentTypes, _bundle, _originalType⟩ :=
    CallableIndexedOwnedPreparedStagedIndirectArgumentPrefix.source_rows
      (sourceEq := rfl) (found := port.calleeFound) (sourceParent := port.sourceParent)
      (tree := tree) (unique := unique) (parentTyped := parentTyped) compiler
  cases SelectedCompilationStageIndirectSourceTrace.source_inv unique compiler.found compiler.originalForm
    port.sourceParent.coercions compiler.argumentCoercions port.sourceParent.arity execution with
  | calleeFault failed smaller =>
    obtain ⟨outcome, reached, trace, adapted⟩ := children _ (Nat.lt_of_lt_of_le smaller within)
      certified port.calleeFound sourceTyped environments heaps locals agrees typed initial admitted (.fault failed)
    cases adapted with
    | completed => exact .inl ⟨_, _, .calleeFault occurrence trace, .completed⟩
    | rejected origin call reason reached => exact .inl ⟨_, _, .calleeFault occurrence trace, .rejected origin call reason _⟩
  | notCallable evaluated invalid smaller =>
    rcases SelectedCompilationStageIndirectCalleeLifting.callee_value bridge profile compiler port certified sourceTyped
      tree unique parentTyped environments heaps locals agrees typed initial admitted budget children preservation
      evaluated (Nat.lt_of_lt_of_le smaller within) with complete | ⟨carrier, calleeStore, calleeMap, calleeWorld, _calleeTrace, _post, accepted⟩
    · exact .inl complete
    · exact False.elim (invalid accepted.callable)
  | argumentsFault calleeTrace _callable failed calleeSmaller argumentsSmaller =>
    rcases SelectedCompilationStageIndirectCalleeLifting.callee_value bridge profile compiler port certified sourceTyped
      tree unique parentTyped environments heaps locals agrees typed initial admitted budget children preservation
      calleeTrace (Nat.lt_of_lt_of_le calleeSmaller within) with complete | ⟨carrier, calleeStore, calleeMap, calleeWorld, liftedCallee, post, accepted⟩
    · exact .inl complete
    · obtain ⟨_native, _payload, calleeHeaps, maps, worlds, _frame, metadata, reached, _related, post⟩ := post
      obtain ⟨outcome, finalHeap, liftedArguments, adapted⟩ := SelectedCompilationStageLiftSequence.fault bridge
        budget tree unique argumentTypes children preservation (environments.extend maps worlds) calleeHeaps
        (locals.mono metadata) agrees (typed.weaken worlds) reached post.at_value.2 failed
        (Nat.le_of_lt (Nat.lt_of_lt_of_le argumentsSmaller within))
      cases adapted with
      | completed => exact .inl ⟨_, _, .argumentsFault occurrence liftedCallee accepted liftedArguments, .completed⟩
      | rejected origin call reason reached =>
        exact .inl ⟨_, _, .argumentsFault occurrence liftedCallee accepted liftedArguments, .rejected origin call reason _⟩
  | apply calleeTrace argumentsTrace called calleeSmaller argumentsSmaller callSmaller =>
    rcases SelectedCompilationStageIndirectCalleeLifting.callee_value bridge profile compiler port certified sourceTyped
      tree unique parentTyped environments heaps locals agrees typed initial admitted budget children preservation
      calleeTrace (Nat.lt_of_lt_of_le calleeSmaller within) with complete | ⟨carrier, calleeStore, calleeMap, calleeWorld, liftedCallee, post, accepted⟩
    · exact .inl complete
    · obtain ⟨_native, _payload, calleeHeaps, maps, worlds, _frame, metadata, reached, _related, post⟩ := post
      obtain ⟨outcome, finalHeap, liftedArguments, adapted⟩ := SelectedCompilationStageLiftSequence.values bridge
        budget tree unique argumentTypes children preservation (environments.extend maps worlds) calleeHeaps
        (locals.mono metadata) agrees (typed.weaken worlds) reached post.at_value.2 argumentsTrace
        (Nat.le_of_lt (Nat.lt_of_lt_of_le argumentsSmaller within))
      cases adapted with
      | rejected origin call reason reached =>
        exact .inl ⟨_, _, .argumentsFault occurrence liftedCallee accepted liftedArguments, .rejected origin call reason _⟩
      | completed =>
        obtain ⟨calleeSize, sizedCallee⟩ := Staging.Recursive.Size.Expression.of_trace liftedCallee
        obtain ⟨argumentsSize, sizedArguments⟩ := Staging.Recursive.Size.Expressions.of_trace liftedArguments
        have valuePrefix := SelectedCompilationIndirectValuesPrefix.preserves_values
          bridge profile compiler port.prepared rfl certified port.calleeFound sourceTyped environments heaps locals agrees typed
          initial admitted port.caller port.view port.originalUnique port.guardFrame port.sourceParent tree unique parentTyped
          (Staging.Recursive.Size.stepSize [calleeSize, argumentsSize]) (fun size _ => preservation size)
          sizedCallee accepted sizedArguments (Nat.le_refl _)
        exact .inr ⟨_, _, _, _, _, _, _, _, sizedCallee, accepted, sizedArguments,
          called, Nat.lt_of_lt_of_le callSmaller within, valuePrefix⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageIndirectPrefixLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageIndirectNamedLifting
/-! The positive named payload selects the same actual cache entry, complete
source dictionary and captured physical frame at the reached argument heap. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2200000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageIndirectNamedLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPreparedStagedSelectedGeneralCallHeadBounds (Port)
open SelectedCompilationPhysicalProgramSupport (Support stages functions stagePrepared)
open SelectedCompilationStageBodyLiftBounds (NamedLiftsBelow)
open Staging.Recursive.Lifting (ApplicationLift)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {receiver : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (support : Support compiled headers keys receiver)
  {registry : SourceCoreRawMetadata.Registry}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (physical : ∀ {index}, callerProtocol.State index → CallableIndexedOwnedPhysicalGlobals.Authority compiled index.mapping index.store)
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation invocation.source scope
    id callee ids metadata reasonAt lowered)
  (port : Port (compiled := compiled) (invocation := invocation) compiler)
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
  (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
  {sourceTypes : List TypeSystem.Ty}
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (functions support)

include support physical runtime actualFunctionType in
theorem named_application (budget : Nat)
    (bodies : ∀ header, header ∈ headers → ∀ child,
      (stages compiled).Closure header.function child →
      NamedLiftsBelow (headers := headers) (keys := keys) header model (stages compiled) child budget)
    {function : Dynamic.GlobalFunction} {calleeHeap argumentsHeap after : Dynamic.Heap}
    {sources : List Dynamic.Value} {size argumentsSize : Nat} {callEvidence : Dynamic.EvidenceEnvironment}
    {outcome : Dynamic.ExpressionOutcome}
    (argumentsTrace : Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) (stages compiled)
      argumentsSize invocation context environment calleeHeap ids (.values sources) argumentsHeap)
    (prefixResult : SelectedCompilationIndirectValuesPrefix.ValuesPrefix
      (functionModel := functions support) (registry := registry)
      (bodyRegistry := receiver.result.context.registry)
      (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.result.diagnostics)
      (context := context) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeNode := port.calleeNode) (sidecar := port.sidecar)
      bridge support.profile compiler port.prepared initial (.global function) calleeHeap argumentsHeap sources)
    (called : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) size
      context invocation.evidence callEvidence argumentsHeap (.global function) sources outcome after)
    (within : size ≤ budget) :
    ApplicationLift (Program.ofChecked compiled.sourceProgram) (stages compiled) invocation context argumentsHeap
      (.global function) sources outcome after := by
  obtain ⟨parameter, result, functionType, bundle, _originalResult,
    _calleeStore, _calleeMap, _calleeWorld, carrier, values, _argumentsStore, finalMap, finalWorld,
    _originalNode, _originalMetadata, _calleePost, calleeTyped, _firstGate, _argumentsNative,
    represented, calleePayload, _callView, boundary, heaps, _maps, _worlds,
    _frame, _heapMetadata, argumentsTyped, argumentMetadata, reached, _related, admitted⟩ := prefixResult
  obtain ⟨rawType, ⟨association⟩, _nativeType⟩ :=
    CallableIndexedOwnedPreparedPhysicalCellOrigins.PayloadOrigins.named_member support.profile calleePayload function rfl
  let header := association.header
  let packet := support.bodies header association.member
  have certified := support.certificates header association.member
  by_cases arity : header.function.parameters.length = sources.length
  · have rawCallee : Dynamic.ValueHasType context calleeHeap (.global function) (.function parameter result) := by
      simpa only [functionType] using calleeTyped
    have certifiedAt := SelectedCompilationNamedArgumentRows.certified_at association.sourceAt support.bodyTyping
      packet.prepared packet.aligned
    cases boundary with
    | user dispatch selected =>
      have count : dispatch.row.entry.parameterCount = ids.length :=
        (CallableIndexedOwnedNamedPhysicalArityReceipts.named_parameter_count association.sourceAt
          port.caller dispatch selected).trans (arity.trans argumentsTrace.sound.length.symm)
      have secondAccepted : CallableContract.decision port.prepared.site.gates .beforeApplication
          compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown dispatch.contract = none := by
        rw [port.prepared.site.decision_known .beforeApplication
          compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown dispatch.contract dispatch.row dispatch.found]
        exact SourceCoreCallableContracts.reason_accepted dispatch.row port.prepared.site.reasonAt .beforeApplication
          (dispatch.row.afterArguments_ok (count.trans selected.argument_count.symm))
      obtain ⟨parameters, physicalArity, _result⟩ := SelectedCompilationNamedArgumentRows.accepted_rows
        association.sourceAt compiler certifiedAt actualFunctionType port.caller dispatch selected secondAccepted
        rawCallee association.type_eq represented bundle
      obtain ⟨headerHeap, headerArguments, _supports⟩ := SelectedCompilationNamedArgumentRows.arguments_at
        association.sourceAt certifiedAt certified runtime admitted.heap argumentsTyped
        (rawCallee.mono argumentMetadata) bundle physicalArity
      obtain ⟨⟨capture, _sameCapture⟩⟩ := association.at_store packet.prepared packet.aligned
        (support.owners association.owner) (physical reached)
      obtain ⟨sidecar, _prepared, _same, selectedScope, _declaration, _local, _evidence, _marker, _analysis⟩ :=
        CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts.selected association.sourceAt packet.prepared packet.aligned
          (stagePrepared compiled) association.descriptor
      rw [CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts.global_view association.sourceAt] at selectedScope
      exact SelectedCompilationStageNamedInvocationLifting.lifts_invocation (functions support) association.owner
        (bridge.pool reached) header capture association.sourceAt packet.layouts (physical reached) association.member
        support.bodyTyping.function_ids certified admitted.rows headerHeap headerArguments parameters heaps selectedScope
        budget (bodies header association.member _ selectedScope)
        (SelectedCompilationStageIndirectSourceTrace.call_with_global_evidence called) within
  · exact SelectedCompilationStageApplicationArity.global_mismatch support.bodyTyping.function_ids
      association.sourceAt.frame arity called

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageIndirectNamedLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosureBodyLifting
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosureBodyLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open SelectedCompilationStageBodyLiftBounds
open SelectedCompilationStageLiftBounds (LiftsAt LiftsRootsAt)

private theorem terminal_of_head {child : Staging.Recursive.Scope} {expression : ExpressionId}
    {statements : List StatementId} (unique : NodeOccurrencesUnique child.source)
    (head : CallableIndexedOwnedAdmittedStagedTerminalStatements.Head child expression statements) :
    CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Terminal child.source expression statements := by
  cases head with
  | returning rest contains form => exact .returning rest (lookupStatement?_complete unique contains) form
  | tail contains form => exact .tail (lookupStatement?_complete unique contains) form

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (code : Code compiled.indexed function scope administrative)
  (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
  (model : GenericHeap.PayloadModel catalog projects definitions)
  (stages : Staging.Recursive.Registry) (child : Staging.Recursive.Scope)

private abbrev parameterScope := code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope
local notation "physicalBridge" => CallableIndexedOwnedNamedCallerProtocol.Carrier.forgetSlots
  (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys) code.compilation.administrativePrefix)

/-- The actual closure parameter entry supplies this physical state. Its
complete capture environment and real frame stay in the original closure. -/
def ClosureLiftsBelow (budget : Nat) : Prop :=
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ contextLocation native},
    DataHeap.EnvRepresents catalog mapping world administrativeContext (parameterScope code) environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before inputs.context.locals environment →
    EnvironmentsAgree ξ canonical actual → RuntimeEnvironmentHasTypes world actual actualContext definitions →
    canonical[(parameterScope code).length + 1 + compiled.indexed.base.globals.length]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type contextLocation) →
    store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame native) →
    contextLocation ∉ mapping →
    CallableIndexedOwnedAllocationProducer.StableOwner keys contextLocation native →
  ∀ initial : (CallableIndexedOwnedPhysicalCanonicalState.protocol headers keys code.compilation.administrativePrefix).State
      ⟨(parameterScope code), mapping, world, before, store, canonical⟩,
    Admission physicalBridge inputs.context initial →
    Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function →
  ∀ {size finalContext outcome after},
    RecursiveNamedCallBounds.FunctionOutcome (Program.ofChecked compiled.sourceProgram) size inputs.context
      child.evidence child.source environment before function.body finalContext outcome after →
    size ≤ budget →
    BodyLift (Program.ofChecked compiled.sourceProgram) stages true child inputs.context environment before
      function.body finalContext outcome after

variable {semanticFaults : FunctionCalls.FaultRep}
  {packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.Terminal code stages}
  (support : SelectedCompilationPhysicalClosureStaticSupport.SelectedBody (headers := headers) code inputs stages packet semanticFaults)
  (selected : stages.Closure function child) (owner : OwnedKey keys)
  (ownerPhysical : CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)

include support selected ownerPhysical in
/-- The same closure packet exposes its original terminal statement and
strict expression child at the genuine allocated parameter state. -/
theorem terminal {budget : Nat}
    (children : ∀ size, size < budget →
      LiftsRootsAt (headers := headers) (keys := keys) model stages semanticFaults size) :
    ClosureLiftsBelow (headers := headers) (keys := keys) code inputs model stages child budget := by
  intro mapping world administrativeContext environment canonical actual actualContext before store ξ contextLocation native
    environments heaps locals agrees typed _reference _read _unmapped _conditioned initial admitted valid size finalContext outcome after trace within
  have view : LambdaMetadataViews.MetadataView child.source code.view := by
    rw [stages.source selected]
    exact code.viewOfSource
  have head := CallableIndexedOwnedPreparedStagedTerminalMetadataBodyBounds.source_head packet.receipt view
  have unique : NodeOccurrencesUnique child.source := by
    rw [stages.source selected]
    exact valid.code.graph.nodeOccurrencesUnique
  obtain ⟨staticFinal, facts, bodyTyped, completes⟩ :=
    CallableIndexedOwnedLambdaSourceAdmission.body_typed_at_parameters valid inputs.extended
  rw [← stages.source selected] at bodyTyped
  obtain ⟨node, found, _sameType, sourceTyped⟩ :=
    CallableIndexedOwnedPreparedStagedTerminalBodyTyping.child_typed unique head bodyTyped completes
  have original := terminal_of_head unique head
  obtain ⟨childSize, plain, strict, finalEq, outcomeEq, evaluated⟩ :=
    SelectedCompilationStageTerminalInversion.child_of_body unique original trace
  subst finalContext
  subst outcome
  have meaning : LiftsAt physicalBridge inputs.context model stages child
      (CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.Point (parameterScope code)
        packet.expression packet.receipt.child) childSize :=
    children childSize (Nat.lt_of_lt_of_le strict within) (support.rootAt child selected) owner ownerPhysical
  have lifted := meaning ⟨rfl, rfl, rfl⟩ found sourceTyped environments heaps locals agrees typed
    initial admitted evaluated
  exact terminal_expression head lifted

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosureBodyLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosureEntryLifting
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosureEntryLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open SelectedCompilationStageBodyLiftBounds

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (code : Code compiled.indexed function scope administrative)
  (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
  (model : GenericHeap.PayloadModel catalog projects definitions)
  (stages : Staging.Recursive.Registry) (child : Staging.Recursive.Scope)

private abbrev parameterScope := code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope
local notation "physicalBridge" => CallableIndexedOwnedNamedCallerProtocol.Carrier.forgetSlots
  (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys) code.compilation.administrativePrefix)

/-- The actual closure parameter entry supplies this physical state. Its
complete capture environment and real frame stay in the original closure. -/
def EntryLiftsBelow (budget : Nat) : Prop :=
  ∀ {mapping world environment canonical actual actualContext before store ξ contextLocation native},
    DataHeap.EnvRepresents catalog mapping world administrative (parameterScope code) environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before inputs.context.locals environment →
    EnvironmentsAgree ξ canonical actual → RuntimeEnvironmentHasTypes world actual actualContext definitions →
    canonical[(parameterScope code).length + 1 + compiled.indexed.base.globals.length]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type contextLocation) →
    store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame native) →
    contextLocation ∉ mapping →
    CallableIndexedOwnedAllocationProducer.StableOwner keys contextLocation native →
  ∀ initial : (CallableIndexedOwnedPhysicalCanonicalState.protocol headers keys code.compilation.administrativePrefix).State
      ⟨(parameterScope code), mapping, world, before, store, canonical⟩,
    Admission physicalBridge inputs.context initial →
    Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function →
  ∀ {size finalContext outcome after},
    RecursiveNamedCallBounds.FunctionOutcome (Program.ofChecked compiled.sourceProgram) size inputs.context
      child.evidence child.source environment before function.body finalContext outcome after →
    size ≤ budget →
    BodyLift (Program.ofChecked compiled.sourceProgram) stages true child inputs.context environment before
      function.body finalContext outcome after

theorem of_general {budget : Nat}
    (lifted : SelectedCompilationStageClosureBodyLifting.ClosureLiftsBelow
      (headers := headers) (keys := keys) code inputs model stages child budget) :
    EntryLiftsBelow (headers := headers) (keys := keys) code inputs model stages child budget := by
  intro mapping world environment canonical actual actualContext before store ξ contextLocation native
    environments heaps locals agrees typed reference read unmapped conditioned initial admitted valid
    size finalContext outcome after trace within
  exact lifted environments heaps locals agrees typed reference read unmapped conditioned initial admitted valid trace within

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosureEntryLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosureEntryApplicationLifting
/-! Real captured closure parameters allocate the original Source environment
and its physical frame before the selected body lift is used. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosureEntryApplicationLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CoreProof CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedSourceAdmission
open SourceCoreCallableIndexedFrames
open Staging.Recursive
open SelectedCompilationStageClosureEntryLifting (EntryLiftsBelow)
open SelectedCompilationStageBodyLiftBounds (BodyLift)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}   {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {capturedActual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured capturedActual)
  (code : Code compiled.indexed function scope captured.administrative) (history : History code)
  (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code)
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {stages : Registry}
  {arguments : List Dynamic.Value} {nativeArguments : List Value}
  (represented : CallableIndexedParameterMeaning.Arguments
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    mapping world code.receipt.loweredParameters arguments nativeArguments)
  {before : Dynamic.Heap} {store : Store} {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions
    mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
  (reference : captured.canonical[code.referenceIndex]? =
    some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation))
  {currentMetadata : Option MetadataState}
  (currentCarried : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
    (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost currentMetadata)
  (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed compiled.indexed.ancestry.graph.inputs
    history.metadata code.descriptor.id = true)
  (capturedSlots : CallableIndexedOwnedPhysicalGlobals.Slots compiled
    code.compilation.administrativePrefix scope captured.canonical)
  (physical : CallableIndexedOwnedPhysicalGlobals.Authority compiled mapping store)
  (savedRows : CallableIndexedOwnedIndirectExpressionHeads.StableRows caller)
  (beforeTyped : Dynamic.HeapWellTyped function.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes function.context before arguments inputs.types)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions
local notation "canonicalBridge" => CallableIndexedOwnedNamedCallerProtocol.Carrier.forgetSlots
  (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys) code.compilation.administrativePrefix)

private theorem capturedSlots_after_prefix
    {bindings : List CallableIndexedParameterCertificates.Binding}
    {callerPrefix : Nat} {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
    (slots : CallableIndexedOwnedPhysicalGlobals.Slots compiled callerPrefix scope canonical)
    (added : Environment) (length : added.length = bindings.length)
    (copied : Environment) {final : Environment} (spine : final = added ++ copied)
    (kept : ∀ slot, scope.length ≤ slot → copied[slot]? = canonical[slot]?) :
    CallableIndexedOwnedPhysicalGlobals.Slots compiled callerPrefix
      (bindings.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope) final := by
  subst final
  intro slot signature found
  have offset : (bindings.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope).length + callerPrefix + slot =
      added.length + (scope.length + callerPrefix + slot) := by simp only [List.length_append, List.length_map, List.length_reverse]; omega
  rw [offset, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left, kept _ (by omega)]
  exact slots slot signature found


include represented heaps locals reference currentCarried allowed capturedSlots physical savedRows beforeTyped argumentsTyped in
theorem lifts_application {child invocation : Scope} (selected : stages.Closure function child)
    {callContext : SourceSemantics.Context} {callerEvidence invocationEvidence : Dynamic.EvidenceEnvironment}
    (budget : Nat)
    (bodies : EntryLiftsBelow (headers := headers) (keys := keys) code inputs model stages child budget)
    {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) size
      callContext callerEvidence invocationEvidence before (.closure function) arguments outcome after)
    (within : size ≤ budget) :
    Lifting.ApplicationLift (Program.ofChecked compiled.sourceProgram) stages invocation callContext before
      (.closure function) arguments outcome after := by
  have arity : function.parameters.length = arguments.length := by
    rw [CallableIndexedLambdaEntryPrefix.parameters (values := .initial compiled.compatible.checked) code,
      List.length_map]
    exact represented.length.1
  obtain ⟨childSize, copies, copiedHeap, environment, bound, valid, copy, allocated, sourceTrace, smaller⟩ :=
    SelectedCompilationStageClosureSourceTrace.source_prefix inputs.extended arity trace
  obtain ⟨finalContext, bodyOutcome, bodyTrace, converted⟩ :=
    SelectedCompilationStageNamedInvocationLifting.body_control sourceTrace
  obtain ⟨entry, added, copied, length, spine, kept, parameterState, _parameterRelated⟩ :=
    CallableIndexedOwnedLambdaInvocationBounds.parameters_with_state captured code history inputs
      functions represented owner caller heaps locals reference currentCarried allowed
  obtain ⟨sameCopies, sameCopied⟩ := Dynamic.EnvironmentCopies.functional entry.entry.copy copy
  rw [← sameCopies, ← sameCopied] at allocated
  obtain ⟨sameEnvironment, sameHeap⟩ := FunctionCallBody.allocations_same entry.entry.allocation allocated
  rw [← sameEnvironment, ← sameHeap] at bodyTrace
  have admitted := CallableIndexedOwnedPreparedLambdaParameterAdmission.at_parameters
    captured code history inputs functions owner caller entry parameterState valid beforeTyped argumentsTyped savedRows
  have slots := capturedSlots_after_prefix capturedSlots added length copied spine kept
  let initial : (CallableIndexedOwnedPhysicalCanonicalState.protocol headers keys code.compilation.administrativePrefix).State
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩ :=
    ⟨⟨parameterState, slots⟩,
      (physical.install (frameLocation := owner.key.frameLocation)
        (native := (caller.rows owner.position).authority.current) entry.currentRead entry.next).extend entry.entry.frame⟩
  have canonicalAdmitted : Admission canonicalBridge inputs.context initial := ⟨admitted.heap, admitted.rows⟩
  have conditioned := CallableIndexedOwnedAllocationProducer.stableOwner_selected owner.position entry.nextHistory
  have lifted := bodies entry.entry.environments entry.entry.heaps entry.entry.locals entry.entry.lookups
    entry.entry.actualTyped entry.entry.reference entry.entry.read entry.entry.unmapped conditioned
    initial canonicalAdmitted valid
    (by simpa only [stages.source selected, stages.evidence selected] using bodyTrace)
    (Nat.le_of_lt (Nat.lt_of_lt_of_le smaller within))
  exact BodyLift.closure selected valid inputs.extended entry.entry.copy entry.entry.allocation lifted converted

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosureEntryApplicationLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosurePacketLifting
/-! The original positive closure association fixes both the selected body
packet and its complete captured environment for real parameter entry. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2200000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosurePacketLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPreparedPhysicalClosureAssociation (Association)
open SelectedCompilationPhysicalClosureStaticSupport (Packet PacketFor SupportFor LegacyPacketFor LegacySupportFor)
open SelectedCompilationStageClosureEntryLifting (EntryLiftsBelow)

section Schema
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (code : Code compiled.indexed function scope administrative)
  (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
  (model : GenericHeap.PayloadModel catalog projects definitions)
  (stages : Staging.Recursive.Registry)

def PacketBelow (packet : Packet code stages) (budget : Nat) : Prop :=
  match packet with
  | .terminal terminal => EntryLiftsBelow (headers := headers) (keys := keys) code inputs model stages terminal.child budget
  | .branching branching => EntryLiftsBelow (headers := headers) (keys := keys) code inputs model stages branching.child budget

variable {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {mapping : LocationMap} {world : StoreTyping} {native : Value}
  {bindings : List CallableIndexedParameterCertificates.Binding} {parameter result : Ty}

def LegacyBelowFor
    (association : CallableIndexedOwnedContextualTypedClosureReceipts.Association headers keys
      bodyRegistry semanticFaults mapping world function native bindings parameter result)
    (packet : LegacyPacketFor association stages) (budget : Nat) : Prop :=
  match association with
  | .ordinary _ _ code _ support _ _ _ _ _ _ =>
    PacketBelow (headers := headers) (keys := keys) code support.body.toContext model stages packet budget
  | .principal _ _ code _ support _ _ _ _ _ _ =>
    PacketBelow (headers := headers) (keys := keys) code support.body.toContext model stages packet budget
def BelowFor
    (association : CallableIndexedOwnedPreparedPhysicalClosureAssociation.Association headers keys
      bodyRegistry semanticFaults mapping world function native bindings parameter result)
    (packet : PacketFor association stages) (budget : Nat) : Prop :=
  match association with
  | .legacy original => LegacyBelowFor model stages original.original packet budget
  | .preparedOrdinary _ _ code _ support _ _ _ _ _ _ _ _ =>
    PacketBelow (headers := headers) (keys := keys) code support.body.toContext model stages packet budget
  | .preparedBranching _ _ code _ support _ _ _ _ _ _ _ _ =>
    PacketBelow (headers := headers) (keys := keys) code support.body.toContext model stages packet budget
end Schema

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {stages : Staging.Recursive.Registry}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {mapping : LocationMap} {world : StoreTyping} {function : Dynamic.Closure}
  {native : Value} {bindings : List CallableIndexedParameterCertificates.Binding}
  {parameterCore resultCore : Ty}
  (association : Association headers keys bodyRegistry semanticFaults mapping world function native bindings parameterCore resultCore)
  (packet : PacketFor association stages)
  (supported : SupportFor association stages packet)
  {before : Dynamic.Heap} {store : Store} {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
  (caller : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
  {sources : List Dynamic.Value} {values : List Value}
  (raw : CallableIndexedOwnedStoredClosureSourceArguments.SourceArguments function before sources)
  (represented : CallableIndexedParameterMeaning.Arguments
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
      (CallableIndexedOwnedPreparedPhysicalCellOrigins.functions headers keys bodyRegistry semanticFaults profile))
    mapping world bindings sources values)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    (CallableIndexedOwnedPreparedPhysicalCellOrigins.functions headers keys bodyRegistry semanticFaults profile)
    mapping world before store)
  (physical : CallableIndexedOwnedPhysicalGlobals.Authority compiled mapping store)
  (stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows caller)

local notation "functions" => CallableIndexedOwnedPreparedPhysicalCellOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions

include physical supported raw represented heaps stable in
theorem application_lifts (budget : Nat)
    (bodies : BelowFor model stages association packet budget)
    {invocation : Staging.Recursive.Scope} {context : SourceSemantics.Context}
    {callerEvidence callEvidence : Dynamic.EvidenceEnvironment}
    {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (called : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) size context
      callerEvidence callEvidence before (.closure function) sources outcome after)
    (within : size ≤ budget) :
    Staging.Recursive.Lifting.ApplicationLift (Program.ofChecked compiled.sourceProgram) stages invocation context
      before (.closure function) sources outcome after := by
  cases association with
  | legacy original =>
    rcases original with ⟨original, slots⟩
    cases original with
    | ordinary owner captured code history support _origin _prefixContext globals referenceIndex _typed _provenance =>
      rename_i capturedScope capturedActual
      have typed : Dynamic.ValuesHaveTypes function.context before sources support.body.types := by
        simpa only [Dynamic.MonoBindersExtend.bodyTypes_eq support.body.extended] using raw.arguments
      obtain ⟨_metadata, carried⟩ := stable owner.position
      have reference : captured.canonical[code.referenceIndex]? =
          some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
        rw [referenceIndex]
        exact globals.reference
      have observed : CallableIndexedOwnedPhysicalGlobals.Slots compiled
          code.compilation.administrativePrefix capturedScope captured.canonical := by
        cases packet <;> rw [supported.prefix] <;> exact slots
      obtain ⟨child, selected, body⟩ : ∃ child, stages.Closure function child ∧
          EntryLiftsBelow (headers := headers) (keys := keys) code support.body.toContext model stages child budget := by
        cases packet with
        | terminal terminal => exact ⟨terminal.child, terminal.selected, bodies⟩
        | branching branching => exact ⟨branching.child, branching.selected, bodies⟩
      exact SelectedCompilationStageClosureEntryApplicationLifting.lifts_application
        captured code history support.body.toContext functions represented owner caller heaps raw.captures reference
        carried (CallableIndexedLambdaTemplatePermission.lambda_allowed code history) observed physical stable raw.heaps typed
        selected budget body called within
    | principal owner captured code history support _origin globals _leading referenceIndex _typed _provenance =>
      rename_i capturedScope capturedActual
      have typed : Dynamic.ValuesHaveTypes function.context before sources support.body.types := by
        simpa only [Dynamic.MonoBindersExtend.bodyTypes_eq support.body.extended] using raw.arguments
      obtain ⟨_metadata, carried⟩ := stable owner.position
      have reference : captured.canonical[code.referenceIndex]? =
          some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
        rw [referenceIndex]
        exact globals.reference
      have observed : CallableIndexedOwnedPhysicalGlobals.Slots compiled
          code.compilation.administrativePrefix capturedScope captured.canonical := by
        cases packet <;> rw [supported.prefix] <;> exact slots
      obtain ⟨child, selected, body⟩ : ∃ child, stages.Closure function child ∧
          EntryLiftsBelow (headers := headers) (keys := keys) code support.body.toContext model stages child budget := by
        cases packet with
        | terminal terminal => exact ⟨terminal.child, terminal.selected, bodies⟩
        | branching branching => exact ⟨branching.child, branching.selected, bodies⟩
      exact SelectedCompilationStageClosureEntryApplicationLifting.lifts_application
        captured code history support.body.toContext functions represented owner caller heaps raw.captures reference
        carried (CallableIndexedLambdaTemplatePermission.lambda_allowed code history) observed physical stable raw.heaps typed
        selected budget body called within
  | preparedOrdinary owner captured code history support _origin _prefixContext globals referenceIndex _typed _prepared slots _callerReceipt =>
    rename_i capturedScope capturedActual
    have typed : Dynamic.ValuesHaveTypes function.context before sources support.body.types := by
      simpa only [Dynamic.MonoBindersExtend.bodyTypes_eq support.body.extended] using raw.arguments
    obtain ⟨_metadata, carried⟩ := stable owner.position
    have reference : captured.canonical[code.referenceIndex]? =
        some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
      rw [referenceIndex]
      exact globals.reference
    have observed : CallableIndexedOwnedPhysicalGlobals.Slots compiled
        code.compilation.administrativePrefix capturedScope captured.canonical := by
      cases packet <;> rw [supported.prefix] <;> exact slots
    obtain ⟨child, selected, body⟩ : ∃ child, stages.Closure function child ∧
        EntryLiftsBelow (headers := headers) (keys := keys) code support.body.toContext model stages child budget := by
      cases packet with
      | terminal terminal => exact ⟨terminal.child, terminal.selected, bodies⟩
      | branching branching => exact ⟨branching.child, branching.selected, bodies⟩
    exact SelectedCompilationStageClosureEntryApplicationLifting.lifts_application
      captured code history support.body.toContext functions represented owner caller heaps raw.captures reference
      carried (CallableIndexedLambdaTemplatePermission.lambda_allowed code history) observed physical stable raw.heaps typed
      selected budget body called within

  | preparedBranching owner captured code history support _origin _prefixContext globals referenceIndex _typed _prepared slots _callerReceipt =>
    rename_i capturedScope capturedActual
    have typed : Dynamic.ValuesHaveTypes function.context before sources support.body.types := by
      simpa only [Dynamic.MonoBindersExtend.bodyTypes_eq support.body.extended] using raw.arguments
    obtain ⟨_metadata, carried⟩ := stable owner.position
    have reference : captured.canonical[code.referenceIndex]? =
        some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
      rw [referenceIndex]
      exact globals.reference
    have observed : CallableIndexedOwnedPhysicalGlobals.Slots compiled
        code.compilation.administrativePrefix capturedScope captured.canonical := by
      cases packet <;> rw [supported.prefix] <;> exact slots
    obtain ⟨child, selected, body⟩ : ∃ child, stages.Closure function child ∧
        EntryLiftsBelow (headers := headers) (keys := keys) code support.body.toContext model stages child budget := by
      cases packet with
      | terminal terminal => exact ⟨terminal.child, terminal.selected, bodies⟩
      | branching branching => exact ⟨branching.child, branching.selected, bodies⟩
    exact SelectedCompilationStageClosureEntryApplicationLifting.lifts_application
      captured code history support.body.toContext functions represented owner caller heaps raw.captures reference
      carried (CallableIndexedLambdaTemplatePermission.lambda_allowed code history) observed physical stable raw.heaps typed
      selected budget body called within

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosurePacketLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageIndirectClosureLifting
/-! Positive closure payloads retain their actual selected body packet and
captures. Raw argument rows and the physical count are derived independently. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2200000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageIndirectClosureLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPreparedStagedSelectedGeneralCallHeadBounds (Port)
open SelectedCompilationPhysicalProgramSupport (Support stages functions stagePrepared)
open SelectedCompilationStageBodyLiftBounds (NamedLiftsBelow)
open Staging.Recursive.Lifting (ApplicationLift)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {receiver : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (support : Support compiled headers keys receiver)
  {registry : SourceCoreRawMetadata.Registry}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (physical : ∀ {index}, callerProtocol.State index → CallableIndexedOwnedPhysicalGlobals.Authority compiled index.mapping index.store)
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation invocation.source scope
    id callee ids metadata reasonAt lowered)
  (port : Port (compiled := compiled) (invocation := invocation) compiler)
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
  (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
  {sourceTypes : List TypeSystem.Ty}
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (functions support)

include support physical runtime actualFunctionType in
theorem closure_application (budget : Nat)
    (bodies : ∀ {mapping world function native bindings parameterCore resultCore}
      (association : CallableIndexedOwnedPreparedPhysicalClosureAssociation.Association headers keys
        receiver.result.context.registry
        (CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.result.diagnostics)
        mapping world function native bindings parameterCore resultCore),
      SelectedCompilationStageClosurePacketLifting.BelowFor model (stages compiled)
        association (support.closurePackets association) budget)
    {function : Dynamic.Closure} {calleeHeap argumentsHeap after : Dynamic.Heap}
    {sources : List Dynamic.Value} {size argumentsSize : Nat} {callEvidence : Dynamic.EvidenceEnvironment}
    {outcome : Dynamic.ExpressionOutcome}
    (argumentsTrace : Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) (stages compiled)
      argumentsSize invocation context environment calleeHeap ids (.values sources) argumentsHeap)
    (prefixResult : SelectedCompilationIndirectValuesPrefix.ValuesPrefix
      (functionModel := functions support) (registry := registry)
      (bodyRegistry := receiver.result.context.registry)
      (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.result.diagnostics)
      (context := context) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeNode := port.calleeNode) (sidecar := port.sidecar)
      bridge support.profile compiler port.prepared initial (.closure function) calleeHeap argumentsHeap sources)
    (called : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) size
      context invocation.evidence callEvidence argumentsHeap (.closure function) sources outcome after)
    (within : size ≤ budget) :
    ApplicationLift (Program.ofChecked compiled.sourceProgram) (stages compiled) invocation context argumentsHeap
      (.closure function) sources outcome after := by
  by_cases arity : function.parameters.length = sources.length
  · obtain ⟨parameter, result, functionType, bundle, _originalResult,
      _calleeStore, _calleeMap, _calleeWorld, carrier, values, _argumentsStore, finalMap, finalWorld,
      _originalNode, _originalMetadata, _calleePost, calleeTyped, _firstGate, _argumentsNative,
      represented, calleePayload, _callView, boundary, heaps, _maps, _worlds,
      _frame, _heapMetadata, argumentsTyped, argumentMetadata, reached, _related, admitted⟩ := prefixResult
    have rawCallee : Dynamic.ValueHasType context calleeHeap (.closure function) (.function parameter result) := by
      simpa only [functionType] using calleeTyped
    have relatedCallee : CallableIndexedOwnedPreparedPhysicalCellOrigins.PayloadOrigins
        headers keys receiver.result.context.registry registry
        (CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.result.diagnostics)
        support.profile finalMap finalWorld (.function parameter result) (.closure function)
        carrier compiler.calleeCode.type := by
      change GenericHeap.PayloadModel.Represents model finalMap finalWorld
        (.function parameter result) (.closure function) carrier compiler.calleeCode.type
      simpa only [functionType] using calleePayload
    cases boundary with
    | user dispatch selected =>
      have count : dispatch.row.entry.parameterCount = ids.length :=
        (CallableIndexedOwnedStoredClosureArityBoundary.parameter_count dispatch selected).trans
          (arity.trans argumentsTrace.sound.length.symm)
      obtain ⟨raw, _valid, bindings, parameterCore, resultCore, member, _parameterEq, _resultEq, parameters⟩ :=
        SelectedCompilationPhysicalClosureArgumentRows.at_arguments bridge support.profile compiler reached dispatch
          selected count runtime argumentsTyped argumentMetadata rawCallee bundle admitted
          actualFunctionType relatedCallee represented argumentsTrace
      obtain ⟨association⟩ := member
      exact SelectedCompilationStageClosurePacketLifting.application_lifts support.profile association
        (support.closurePackets association) (support.closureSupport association) (bridge.pool reached)
        raw parameters heaps (physical reached) admitted.rows budget (bodies association) called within
  · exact SelectedCompilationStageApplicationArity.closure_mismatch arity called

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageIndirectClosureLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageIndirectLifting
/-! The actual indirect head lifts its callee and first guard, then arguments
and the selected named, closure or builtin application at the genuine heap. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2200000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageIndirectLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPreparedStagedSelectedGeneralCallHeadBounds (Port)
open SelectedCompilationPhysicalProgramSupport (Support stages functions stagePrepared)
open SelectedCompilationStageBodyLiftBounds (NamedLiftsBelow)
open Staging.Recursive.Lifting (ApplicationLift)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {receiver : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (support : Support compiled headers keys receiver)
  {registry : SourceCoreRawMetadata.Registry}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (physical : ∀ {index}, callerProtocol.State index → CallableIndexedOwnedPhysicalGlobals.Authority compiled index.mapping index.store)
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation invocation.source scope
    id callee ids metadata reasonAt lowered)
  (port : Port (compiled := compiled) (invocation := invocation) compiler)
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
  (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
  (unique : NodeOccurrencesUnique invocation.source)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (functions support)

include support port physical runtime actualFunctionType unique in
theorem indirect {children : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}
    (budget : Nat)
    (calleeCertified : children scope callee compiler.calleeCode)
    {sourceTypes : List TypeSystem.Ty}
    (tree : DataExpressionSequence.Tree invocation.source children scope ids sourceTypes compiler.codes)
    (childLift : ∀ size, size < budget → SelectedCompilationStageLiftBounds.LiftsAt
      bridge context model (stages compiled) invocation children size)
    (preservation : ∀ size, CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesAt
      bridge context model (stages compiled) invocation children faults size)
    (namedBodies : ∀ header, header ∈ headers → ∀ child,
      (stages compiled).Closure header.function child →
      NamedLiftsBelow (headers := headers) (keys := keys) header model (stages compiled) child budget)
    (closureBodies : ∀ {mapping world function native bindings parameterCore resultCore}
      (association : CallableIndexedOwnedPreparedPhysicalClosureAssociation.Association headers keys
        receiver.result.context.registry
        (CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.result.diagnostics)
        mapping world function native bindings parameterCore resultCore),
      SelectedCompilationStageClosurePacketLifting.BelowFor model (stages compiled)
        association (support.closurePackets association) budget) :
    SelectedCompilationStageLiftBounds.LiftsAt bridge context model (stages compiled) invocation
      (CallableIndexedOwnedPreparedStagedSelectedGeneralCallHeadBounds.Point scope id lowered) budget := by
  letI : SelectedCompilationCallableOrigins.Origins headers keys receiver.result.context.registry
      (CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.result.diagnostics) support.profile (functions support) :=
    SelectedCompilationCallableOrigins.prepared support.profile
  intro current expression code point actualNode found parentTyped
    mapping world administrative environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees typed initial admitted execution
  obtain ⟨rfl, rfl, rfl⟩ := point
  cases Option.some.inj (found.symm.trans compiler.found)
  obtain ⟨_parameter, _result, _rawTypes, calleeTyped, _argumentsTyped, _bundle, _resultType⟩ :=
    CallableIndexedOwnedPreparedStagedRecursiveCallerSourceReceipts.original_child_types
      compiler port.sourceParent unique parentTyped
  have reported := CallableIndexedOwnedContextualInitializedClosureReceipts.reported_type_at
    unique port.calleeFound calleeTyped
  have sourceTyped : ExpressionHasType invocation.source context callee port.calleeNode.type := by
    simpa only [reported] using calleeTyped
  have occurrence : Staging.Recursive.Occurrence invocation expression (.call callee ids (.indirect metadata)) :=
    ⟨compiler.original, lookupExpression?_sound compiler.found, compiler.originalForm,
      port.sourceParent.requirements, port.sourceParent.coercions⟩
  rcases SelectedCompilationStageIndirectPrefixLifting.lift_prefix
    (bodyRegistry := receiver.result.context.registry)
    (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.result.diagnostics)
    (functions := functions support) bridge support.profile compiler port
    calleeCertified sourceTyped tree unique parentTyped environments heaps locals agrees typed initial admitted
    budget childLift preservation execution (Nat.le_refl _) with complete | application
  · exact complete
  · obtain ⟨_calleeSize, _argumentsSize, _callSize, sourceValue, _calleeHeap, _argumentsHeap, _sources, _callEvidence,
      calleeTrace, accepted, argumentsTrace, called, smaller, prefixResult⟩ := application
    have lifted : ApplicationLift (Program.ofChecked compiled.sourceProgram) (stages compiled) invocation context _argumentsHeap
        sourceValue _sources outcome after := by
      cases accepted with
      | builtin function => exact ⟨_, _, SelectedCompilationStageLiftBuiltin.builtin_application called.sound, .completed⟩
      | contract bound _passing =>
        cases invocation.guards.userCallable bound with
        | global function =>
          exact SelectedCompilationStageIndirectNamedLifting.named_application support bridge physical compiler port
            runtime actualFunctionType initial budget namedBodies argumentsTrace prefixResult called (Nat.le_of_lt smaller)
        | closure function =>
          exact SelectedCompilationStageIndirectClosureLifting.closure_application support bridge physical compiler port
            runtime actualFunctionType initial budget closureBodies argumentsTrace prefixResult called (Nat.le_of_lt smaller)
    obtain ⟨staged, reached, applied, adapted⟩ := lifted
    exact ⟨staged, reached, .applied occurrence compiler.argumentCoercions calleeTrace.sound accepted
      argumentsTrace.sound port.sourceParent.arity applied, adapted⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageIndirectLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosureScopedLifting
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosureScopedLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open SelectedCompilationStageBodyLiftBounds SelectedCompilationStageClosureEntryLifting
open SelectedCompilationStageLiftBounds (LiftsAt LiftsRootsAt)
open CallableIndexedOwnedAdmittedStagedExpressionBounds (PreservesAt)
open CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport (Branching parameterScope)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (code : Code compiled.indexed function scope administrative)
  (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  {receiving : SourceCoreRawMetadata.Registry}
  {stages : Staging.Recursive.Registry} {child : Staging.Recursive.Scope}
  {semanticFaults : FunctionCalls.FaultRep} {faults : RecursiveStageMeaning.FaultRep}
  {packet : Branching code stages}
  (support : SelectedCompilationPhysicalBranchingClosureStaticSupport.SelectedBody headers code inputs stages packet semanticFaults)
  (selected : stages.Closure function child) (owner : OwnedKey keys)
  (ownerPhysical : CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions
local notation "physicalBridge" => CallableIndexedOwnedNamedCallerProtocol.Carrier.forgetSlots
  (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys) code.compilation.administrativePrefix)

variable (semantic : ∀ reason token, semanticFaults reason token → faults (.semantic reason) token)
  (assignmentInterpretation : PreparedAssignmentDiagnosticAuthority.Interprets compiled receiving
    (fun reason token => faults (.semantic reason) token))

include support selected ownerPhysical semantic faithful observations assignmentInterpretation in
theorem lifts [RecursiveStageMeaning.FaultTokens faults]
    (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry receiving)
    {budget : Nat}
    (children : ∀ size, size < budget → LiftsRootsAt (headers := headers) (keys := keys) model stages semanticFaults size)
    (preservation : ∀ size, SelectedCompilationMixedRootBounds.PreservesRootsAt
      (headers := headers) (keys := keys) model stages semanticFaults faults size) :
    EntryLiftsBelow (headers := headers) (keys := keys) code inputs model stages child budget := by
  intro mapping world environment canonical actual actualContext before store ξ contextLocation native
    environments heaps locals agrees actualTyped reference read unmapped conditioned initial admitted valid
    size finalContext outcome after trace within
  obtain ⟨sourceFinal, sourceFacts, sourceTyped, _sourceComplete⟩ :=
    CallableIndexedOwnedLambdaSourceAdmission.body_typed_at_parameters valid inputs.extended
  rw [← stages.source selected] at sourceTyped
  have originalTyping : ProtectedStateImperativeTypedSourceSites.Statements child.source inputs.context function.body :=
    ⟨_, _, _, sourceTyped⟩
  have tree := support.tree child selected
  obtain ⟨assignmentAuthority⟩ := support.assignmentAuthority
  have assignmentDiagnostics : PreparedAssignmentReachedDiagnostics.Ready (values := .initial compiled.compatible.checked)
      functions (CallableIndexedOwnedPhysicalCanonicalState.protocol headers keys code.compilation.administrativePrefix)
      function.source support.invalidProjection support.missingDefault receiving
      (fun reason token => faults (.semantic reason) token) :=
    assignmentInterpretation assignmentAuthority functions
      (CallableIndexedOwnedPhysicalCanonicalState.protocol headers keys code.compilation.administrativePrefix)
  rw [← stages.source selected] at assignmentDiagnostics
  have shape : CallableIndexedOwnedPreparedStagedBranchingTree.Shape child.source true function.body := by
    rw [stages.source selected]
    exact packet.shape
  have unique : NodeOccurrencesUnique child.source := by
    rw [stages.source selected]
    exact support.frame.code.graph.nodeOccurrencesUnique
  exact SelectedCompilationStageImperativeLifting.lifts_at
    physicalBridge
    (CallableIndexedOwnedPhysicalCanonicalState.bindings code.compilation.administrativePrefix)
    (CallableIndexedOwnedPhysicalCanonicalState.administrativeTransport code.compilation.administrativePrefix)
    functions faithful observations extension rfl (CallableIndexedAmbient.frame_registered compiled.indexed)
    (CallableIndexedOwnedPhysicalCanonicalState.markedProducer model code.compilation.administrativePrefix)
    (CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (fun _ _ stable => CallableIndexedOwnedPhysicalCanonicalState.readyAt_of_stableOwner
      (headers := headers) model code.compilation.administrativePrefix stable)
    (fun context size smaller scope id lowered certified => by
      obtain ⟨rawType, root⟩ := certified
      exact children size smaller (SelectedCompilationMixedRootSupport.RootAt.ofRoot root) owner ownerPhysical ⟨rfl, rfl, rfl⟩)
    (fun context size scope id lowered certified => by
      obtain ⟨rawType, root⟩ := certified
      exact preservation size (SelectedCompilationMixedRootSupport.RootAt.ofRoot root) owner ownerPhysical ⟨rfl, rfl, rfl⟩)
    unique tree (support.sites child selected receiving) semantic assignmentDiagnostics rfl shape originalTyping support.projection within
    environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted trace

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosureScopedLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosurePacketRoots
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosurePacketRoots
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open SelectedCompilationPhysicalClosureStaticSupport (Packet PacketFor SupportFor)
open SelectedCompilationStageClosurePacketLifting (PacketBelow BelowFor)
open SelectedCompilationStageLiftBounds (LiftsRootsAt)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (code : Code compiled.indexed function scope administrative)
  (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  {receiving : SourceCoreRawMetadata.Registry} {stages : Staging.Recursive.Registry}
  {semanticFaults : FunctionCalls.FaultRep} {faults : RecursiveStageMeaning.FaultRep}
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions

variable (semantic : ∀ reason token, semanticFaults reason token → faults (.semantic reason) token)
  (assignmentInterpretation : PreparedAssignmentDiagnosticAuthority.Interprets compiled receiving
    (fun reason token => faults (.semantic reason) token))

include semantic faithful observations assignmentInterpretation in
 theorem packet_of_roots [RecursiveStageMeaning.FaultTokens faults] (packet : Packet code stages)
    (support : SelectedCompilationPhysicalClosureStaticSupport.Support (headers := headers) code inputs stages packet semanticFaults)
    (owner : OwnedKey keys)
    (ownerPhysical : CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)
    (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry receiving)
    {budget : Nat}
    (children : ∀ size, size < budget → LiftsRootsAt (headers := headers) (keys := keys) model stages semanticFaults size)
    (preservation : ∀ size, SelectedCompilationMixedRootBounds.PreservesRootsAt
      (headers := headers) (keys := keys) model stages semanticFaults faults size) :
    PacketBelow (headers := headers) (keys := keys) code inputs model stages packet budget := by
  cases packet with
  | terminal terminal =>
    exact SelectedCompilationStageClosureEntryLifting.of_general code inputs model stages terminal.child
      (SelectedCompilationStageClosureBodyLifting.terminal code inputs model stages terminal.child
        support terminal.selected owner ownerPhysical children)
  | branching branching =>
    exact SelectedCompilationStageClosureScopedLifting.lifts (semantic := semantic) (assignmentInterpretation := assignmentInterpretation) code inputs functions faithful observations support
      branching.selected owner ownerPhysical extension children preservation

section Association
variable {bodyRegistry : SourceCoreRawMetadata.Registry}
  {mapping : LocationMap} {world : StoreTyping} {native : Value}
  {bindings : List CallableIndexedParameterCertificates.Binding} {parameter result : Ty}

include semantic faithful observations assignmentInterpretation in
 theorem association_of_roots [RecursiveStageMeaning.FaultTokens faults]
    (association : CallableIndexedOwnedPreparedPhysicalClosureAssociation.Association headers keys
      bodyRegistry semanticFaults mapping world function native bindings parameter result)
    (packet : PacketFor association stages)
    (support : SupportFor association stages packet)
    (owners : ∀ owner : OwnedKey keys, CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)
    (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry receiving)
    {budget : Nat}
    (children : ∀ size, size < budget → LiftsRootsAt (headers := headers) (keys := keys) model stages semanticFaults size)
    (preservation : ∀ size, SelectedCompilationMixedRootBounds.PreservesRootsAt
      (headers := headers) (keys := keys) model stages semanticFaults faults size) :
    BelowFor model stages association packet budget := by
  cases association with
  | legacy original =>
    rcases original with ⟨original, _slots⟩
    cases original with
    | ordinary owner captured code history body origin prefixContext globals referenceIndex typed provenance =>
      exact packet_of_roots (semantic := semantic) (assignmentInterpretation := assignmentInterpretation) code body.body.toContext functions faithful observations packet support owner (owners owner)
        extension children preservation
    | principal owner captured code history body origin globals leading referenceIndex typed provenance =>
      exact packet_of_roots (semantic := semantic) (assignmentInterpretation := assignmentInterpretation) code body.body.toContext functions faithful observations packet support owner (owners owner)
        extension children preservation
  | preparedOrdinary owner captured code history body origin prefixContext globals referenceIndex typed prepared slots _callerReceipt =>
    exact packet_of_roots (semantic := semantic) (assignmentInterpretation := assignmentInterpretation) code body.body.toContext functions faithful observations packet support owner (owners owner)
      extension children preservation
  | preparedBranching owner captured code history body origin prefixContext globals referenceIndex typed prepared slots _callerReceipt =>
    exact packet_of_roots (semantic := semantic) (assignmentInterpretation := assignmentInterpretation) code body.body.toContext functions faithful observations packet support owner (owners owner)
      extension children preservation
end Association
end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosurePacketRoots
end
