import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageConditionalSourceInversion
import Solcore.SourceSemantics.CoreLowering.CellAwareSourceFlowReadiness
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedBranchSourceTyping

/-! Ordinary Source conditions and exactly the selected branch reach the same
mixed physical continuation. Genuine earlier stage rejection retains its
actual heap and bypasses the remaining branch and suffix. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareSourceFlowConditionalLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open SelectedCompilationStageBodyLiftBounds SelectedCompilationStageScopedLiftBounds
open CallableIndexedNamedGeneration (source)
open CellAwareSourceFlowReadiness (Ready body_prefix body_ready test_value)

variable {whole : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
    projects whole.indexed.layouts.definitions}
  {named : SourceCoreGeneralFunctions.Function}
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
    whole.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed)))
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}

/-- All child contracts are closed by the actual common compiler tree. -/
theorem lifts {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {mode : Bool} {id : StatementId} {rest left : List StatementId} {right : Option (List StatementId)}
    {statement : StatementNode} {test : ExpressionId} {node : ExpressionNode}
    {testCode : Expr} {certificate : GenericExpressionMeaning.Certificate}
    {expected : TypeSystem.Ty} {type : Ty} {branchCode : Bool → Expr}
    (sourceEq : invocation.source = source named)
    (booleans : ∀ {mapping world sourceValue nativeValue},
      model.Represents mapping world .bool sourceValue nativeValue .bool →
      ∃ truth, sourceValue = .bool truth ∧ nativeValue = .bool truth)
    (statementFound : invocation.source.lookupStatement? id = some statement)
    (form : statement.form = .ifThen test left right)
    (found : invocation.source.lookupExpression? test = some node) (nodeType : node.type = .bool)
    (typed : ExpressionHasType invocation.source context test node.type)
    (generated : certificate scope test ⟨.bool,testCode⟩)
    (children : Dynamic.SourceRuntimeValid program context (source named) → invocation.evidence.Covers context →
      context.solvedRequirements = (CallableIndexedNamedGeneration.context whole.indexed named).solvedRequirements →
      ∀ size, CellAwareScopeSourceLiftBounds.LiftsAt bridge context model named registry invocation certificate size)
    (preservation : Dynamic.SourceRuntimeValid program context (source named) → invocation.evidence.Covers context →
      context.solvedRequirements = (CallableIndexedNamedGeneration.context whole.indexed named).solvedRequirements →
      ∀ size, CellAwareScopeExpressionBounds.PreservesAt bridge context model named registry invocation certificate faults size)
    (branches : ∀ truth : Bool, CellAwareSourceFlowLiftBounds.Lifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) bridge producer context scope false (if truth then left else right.getD []))
    (branchPreservation : ∀ (truth : Bool) size, CellAwareScopeFlowBounds.PreservesAt
      bridge context model named producer registry invocation faults administrative scope false
      (if truth then left else right.getD []) expected type (branchCode truth) size)
    (remaining : CellAwareSourceFlowLiftBounds.Lifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) bridge producer context scope mode rest) :
    CellAwareSourceFlowLiftBounds.Lifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) bridge producer context scope mode (id :: rest) := by
  intro size mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
    initial admitted authority physical owner sameLocation allocationReady finalContext outcome after trace
  have unique : NodeOccurrencesUnique invocation.source := sourceEq.symm ▸ runtime.graph.nodeOccurrencesUnique
  have ready : Ready (named := named) (administrative := administrative) (invocation := invocation)
      (context := context) (scope := scope) bridge producer environment canonical actual actualContext embedding before :=
    ⟨mapping,world,store,environments,heaps,locals,agrees,actualTyped,runtime,covers,sameLedger,
      initial,admitted,authority,physical,owner,sameLocation,allocationReady⟩
  have branchTyped (truth : Bool) := ProtectedStateImperativeTypedSourceSites.branch_typed truth (sourceEq ▸ unique)
    (ProtectedStateImperativeTypedSourceSites.head sourceTyped) (sourceEq ▸ statementFound) form
  have suffixTyped := CallableIndexedOwnedPreparedStagedScopedBranchSourceTyping.suffix
    (sourceEq ▸ unique) sourceTyped (sourceEq ▸ statementFound) form
  have children := children runtime covers sameLedger
  have preservation := preservation runtime covers sameLedger
  have notTail : ∀ expression, statement.form ≠ .expression expression false := by
    intro expression same
    rw [form] at same
    cases same
  rcases SelectedCompilationStageScopedSourceInversion.head_and_tail unique statementFound notTail trace with
    ⟨headSize, reason, _strict, contextEq, outcomeEq, failed⟩ |
    ⟨headSize, _strict, stopped, executed⟩ |
    ⟨headSize, tailSize, middleContext, nextEnvironment, middle, _strict, _tailStrict, executed, tail⟩
  · subst finalContext
    subst outcome
    rcases SelectedCompilationStageConditionalSourceInversion.fault unique statementFound form failed with
      ⟨testSize, _testStrict, failedTest⟩ |
      ⟨testSize, value, actualType, _testStrict, reasonEq, evaluated, nonboolean, _valueType⟩ |
      ⟨testSize, branchSize, truth, testHeap, innerContext, _testStrict, _branchStrict, evaluated, failedBranch⟩
    · obtain ⟨staged, reached, lifted, adapted⟩ := children testSize generated found typed
        environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation (.fault failedTest)
      cases adapted with
      | completed => exact ⟨context, _, _, .ifConditionFault (lookupStatement?_sound statementFound) form lifted,
          .completed (.fault reason)⟩
      | rejected origin call reason reached =>
        exact ⟨context, _, _, .ifConditionFault (lookupStatement?_sound statementFound) form lifted,
          .rejected origin call reason context reached⟩
    · rcases test_value bridge producer children preservation booleans found nodeType typed generated ready evaluated with
        ⟨origin, call, stageReason, reached, lifted⟩ | ⟨_lifted, _ready, boolean⟩
      · exact ⟨context, _, _, .ifConditionFault (lookupStatement?_sound statementFound) form lifted,
          .rejected origin call stageReason context reached⟩
      · exact False.elim (nonboolean boolean)
    · rcases test_value bridge producer children preservation booleans found nodeType typed generated ready evaluated with
        ⟨origin, call, stageReason, reached, lifted⟩ | ⟨liftedTest, testReady, _boolean⟩
      · exact ⟨context, _, _, .ifConditionFault (lookupStatement?_sound statementFound) form lifted,
          .rejected origin call stageReason context reached⟩
      · obtain ⟨nextContext, staged, reached, lifted, adapted⟩ := body_prefix bridge producer
          (branches truth) (branchTyped truth) testReady
          (.fault failedBranch)
        cases adapted with
        | completed matched =>
          cases matched
          exact ⟨context, _, _, .ifFault (lookupStatement?_sound statementFound) form liftedTest lifted,
            .completed (.fault reason)⟩
        | rejected origin call reason reachedContext reached =>
          exact ⟨context, _, _, .ifFault (lookupStatement?_sound statementFound) form liftedTest lifted,
            .rejected origin call reason context reached⟩
  · obtain ⟨testSize, branchSize, truth, testHeap, innerContext, innerOutcome,
        _testStrict, _branchStrict, contextEq, outcomeEq, evaluated, branchTrace⟩ :=
      SelectedCompilationStageConditionalSourceInversion.control unique statementFound form executed
    subst finalContext
    subst outcome
    rcases test_value bridge producer children preservation booleans found nodeType typed generated ready evaluated with
      ⟨origin, call, stageReason, reached, lifted⟩ | ⟨liftedTest, testReady, _boolean⟩
    · exact ⟨context, _, _, .ifConditionFault (lookupStatement?_sound statementFound) form lifted,
        .rejected origin call stageReason context reached⟩
    · obtain ⟨nextContext, staged, reached, lifted, adapted⟩ := body_prefix bridge producer
        (branches truth) (branchTyped truth) testReady
        (.control branchTrace)
      cases adapted with
      | rejected origin call reason reachedContext reached =>
        exact ⟨context, _, _, .ifFault (lookupStatement?_sound statementFound) form liftedTest lifted,
          .rejected origin call reason context reached⟩
      | completed matched =>
        cases matched with
        | returned value =>
          exact ⟨context, _, _, .ifReturned (lookupStatement?_sound statementFound) form liftedTest lifted,
            .completed (.returned value)⟩
        | breaking innerEnvironment =>
          exact ⟨context, _, _, .ifBreaking (lookupStatement?_sound statementFound) form liftedTest lifted,
            .completed (.breaking environment)⟩
        | continuing innerEnvironment =>
          exact ⟨context, _, _, .ifContinuing (lookupStatement?_sound statementFound) form liftedTest lifted,
            .completed (.continuing environment)⟩
        | fault reason =>
          exact ⟨context, _, _, .ifFault (lookupStatement?_sound statementFound) form liftedTest lifted,
            .completed (.fault reason)⟩
        | fallthrough innerEnvironment =>
          rcases stopped with impossible | rfl
          · cases impossible
          · exact ⟨context, _, _, .ifFallthrough (lookupStatement?_sound statementFound) form liftedTest lifted .nil,
              .completed (.fallthrough environment)⟩
  · obtain ⟨testSize, branchSize, truth, testHeap, innerContext, innerOutcome,
        _testStrict, _branchStrict, contextEq, restored, evaluated, branchTrace⟩ :=
      SelectedCompilationStageConditionalSourceInversion.control unique statementFound form executed
    subst middleContext
    cases innerOutcome with
    | fallthrough innerEnvironment =>
      simp only [Dynamic.restoreControl, Dynamic.ControlOutcome.fallthrough.injEq] at restored
      subst nextEnvironment
      rcases test_value bridge producer children preservation booleans found nodeType typed generated ready evaluated with
        ⟨origin, call, stageReason, reached, lifted⟩ | ⟨liftedTest, testReady, _boolean⟩
      · exact ⟨context, _, _, .ifConditionFault (lookupStatement?_sound statementFound) form lifted,
          .rejected origin call stageReason context reached⟩
      · obtain ⟨nextContext, staged, reached, lifted, adapted⟩ := body_prefix bridge producer
          (branches truth) (branchTyped truth) testReady
          (.control branchTrace)
        cases adapted with
        | rejected origin call reason reachedContext reached =>
          exact ⟨context, _, _, .ifFault (lookupStatement?_sound statementFound) form liftedTest lifted,
            .rejected origin call reason context reached⟩
        | completed matched =>
          cases matched
          have nextReady := body_ready bridge producer (branchPreservation truth) (branchTyped truth) testReady lifted
          obtain ⟨nextMap,nextWorld,nextStore,nextEnvironments,nextHeaps,nextLocals,nextAgrees,nextTyped,
            nextRuntime,nextCovers,nextLedger,nextState,nextAdmitted,nextAuthority,nextPhysical,nextOwner,nextLocation,nextAllocationReady⟩ := nextReady
          obtain ⟨lastContext,result,finalHeap,restTrace,restAdapted⟩ := remaining
            nextEnvironments nextHeaps nextLocals nextAgrees nextTyped nextRuntime nextCovers nextLedger suffixTyped
            nextState nextAdmitted nextAuthority nextPhysical nextOwner nextLocation nextAllocationReady tail
          exact ⟨lastContext,result,finalHeap,
            .ifFallthrough (lookupStatement?_sound statementFound) form liftedTest lifted restTrace,restAdapted⟩
    | returned value => cases restored
    | breaking environment => cases restored
    | continuing environment => cases restored
    | fault reason => cases restored

end Solcore.SourceSemantics.CoreLowering.CellAwareSourceFlowConditionalLifting
