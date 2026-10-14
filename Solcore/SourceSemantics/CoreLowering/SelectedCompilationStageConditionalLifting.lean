import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageConditionalSourceInversion
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStagePhysicalReadiness
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedBranchSourceTyping

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageConditionalLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open SelectedCompilationStageBodyLiftBounds SelectedCompilationStageScopedLiftBounds
open SelectedCompilationStageLiftBounds (LiftsAt)
open SelectedCompilationStageWhileLifting (PhysicalReady test_value)
open SelectedCompilationStagePhysicalReadiness (body_prefix body_ready)
open CallableIndexedOwnedAdmittedStagedConditionalHeads (BranchPreserves)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry}
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat} {administrative : Core.Context}
  (condition : Location → NativeFrame → Prop)
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions

include bridge functions condition in
/-- Conditions and the selected branch thread their actual physical states.
An early stage stop bypasses the rest of the branch and the outer suffix. -/
theorem lifts {budget : Nat} {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {mode : Bool} {id : StatementId} {rest left : List StatementId} {right : Option (List StatementId)}
    {statement : StatementNode} {test : ExpressionId} {node : ExpressionNode}
    {testCode : Expr} {certificate : GenericExpressionMeaning.Certificate}
    {expected : TypeSystem.Ty} {type : Ty} {branchCode : Bool → Expr}
    (unique : NodeOccurrencesUnique invocation.source)
    (statementFound : invocation.source.lookupStatement? id = some statement)
    (form : statement.form = .ifThen test left right)
    (found : invocation.source.lookupExpression? test = some node)
    (typed : ExpressionHasType invocation.source context test node.type)
    (generated : certificate scope test ⟨.bool, testCode⟩)
    (children : ∀ childSize, childSize < budget → LiftsAt bridge context model stages invocation certificate childSize)
    (preservation : ∀ childSize, CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesAt
      bridge context model stages invocation certificate faults childSize)
    (branches : ∀ truth : Bool, FlowLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      bridge functions condition context scope false (if truth then left else right.getD []) budget)
    (branchPreservation : ∀ (truth : Bool) childSize, BranchPreserves (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions condition context scope (if truth then left else right.getD []) expected type (branchCode truth) childSize)
    (remaining : FlowLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      bridge functions condition context scope mode rest budget ∨
      (GenericLexicalStatements.Stopped invocation.source left ∧
       GenericLexicalStatements.Stopped invocation.source (right.getD []))) :
    FlowLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      bridge functions condition context scope mode (id :: rest) budget := by
  intro size within mapping world actualContext environment canonical actual before store ξ
    contextLocation native environments heaps locals agrees actualTyped reference read unmapped
    initial conditioned admitted finalContext outcome after trace
  have ready : PhysicalReady (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (context := context) (scope := scope)
      bridge functions condition environment canonical actual actualContext ξ contextLocation native before :=
    ⟨mapping, world, store, environments, heaps, locals, agrees, actualTyped, reference, read, unmapped,
      initial, conditioned, admitted⟩
  have notTail : ∀ expression, statement.form ≠ .expression expression false := by
    intro expression same
    rw [form] at same
    cases same
  rcases SelectedCompilationStageScopedSourceInversion.head_and_tail unique statementFound notTail trace with
    ⟨headSize, reason, strict, contextEq, outcomeEq, failed⟩ |
    ⟨headSize, strict, stopped, executed⟩ |
    ⟨headSize, tailSize, middleContext, nextEnvironment, middle, strict, tailStrict, executed, tail⟩
  · subst finalContext
    subst outcome
    rcases SelectedCompilationStageConditionalSourceInversion.fault unique statementFound form failed with
      ⟨testSize, testStrict, failedTest⟩ |
      ⟨testSize, value, actualType, testStrict, reasonEq, evaluated, nonboolean, _valueType⟩ |
      ⟨testSize, branchSize, truth, testHeap, innerContext, testStrict, branchStrict, evaluated, failedBranch⟩
    · obtain ⟨staged, reached, lifted, adapted⟩ := children testSize
        (Nat.lt_of_lt_of_le (Nat.lt_trans testStrict strict) within) generated found typed
        environments heaps locals agrees actualTyped initial admitted (.fault failedTest)
      cases adapted with
      | completed => exact ⟨context, _, _, .ifConditionFault (lookupStatement?_sound statementFound) form lifted,
          .completed (.fault reason)⟩
      | rejected origin call reason reached =>
        exact ⟨context, _, _, .ifConditionFault (lookupStatement?_sound statementFound) form lifted,
          .rejected origin call reason context reached⟩
    · rcases test_value bridge functions condition children preservation found typed generated ready
        (Nat.lt_of_lt_of_le (Nat.lt_trans testStrict strict) within) evaluated with
        ⟨origin, call, stageReason, reached, lifted⟩ | ⟨_lifted, _ready, boolean⟩
      · exact ⟨context, _, _, .ifConditionFault (lookupStatement?_sound statementFound) form lifted,
          .rejected origin call stageReason context reached⟩
      · exact False.elim (nonboolean boolean)
    · rcases test_value bridge functions condition children preservation found typed generated ready
        (Nat.lt_of_lt_of_le (Nat.lt_trans testStrict strict) within) evaluated with
        ⟨origin, call, stageReason, reached, lifted⟩ | ⟨liftedTest, testReady, _boolean⟩
      · exact ⟨context, _, _, .ifConditionFault (lookupStatement?_sound statementFound) form lifted,
          .rejected origin call stageReason context reached⟩
      · obtain ⟨nextContext, staged, reached, lifted, adapted⟩ := body_prefix bridge functions condition
          (branches truth) testReady (Nat.le_trans (Nat.le_of_lt (Nat.lt_trans branchStrict strict)) within)
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
        testStrict, branchStrict, contextEq, outcomeEq, evaluated, branchTrace⟩ :=
      SelectedCompilationStageConditionalSourceInversion.control unique statementFound form executed
    subst finalContext
    subst outcome
    rcases test_value bridge functions condition children preservation found typed generated ready
      (Nat.lt_of_lt_of_le (Nat.lt_trans testStrict strict) within) evaluated with
      ⟨origin, call, stageReason, reached, lifted⟩ | ⟨liftedTest, testReady, _boolean⟩
    · exact ⟨context, _, _, .ifConditionFault (lookupStatement?_sound statementFound) form lifted,
        .rejected origin call stageReason context reached⟩
    · obtain ⟨nextContext, staged, reached, lifted, adapted⟩ := body_prefix bridge functions condition
        (branches truth) testReady (Nat.le_trans (Nat.le_of_lt (Nat.lt_trans branchStrict strict)) within)
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
        testStrict, branchStrict, contextEq, restored, evaluated, branchTrace⟩ :=
      SelectedCompilationStageConditionalSourceInversion.control unique statementFound form executed
    subst middleContext
    cases innerOutcome with
    | fallthrough innerEnvironment =>
      simp only [Dynamic.restoreControl, Dynamic.ControlOutcome.fallthrough.injEq] at restored
      subst nextEnvironment
      rcases test_value bridge functions condition children preservation found typed generated ready
        (Nat.lt_of_lt_of_le (Nat.lt_trans testStrict strict) within) evaluated with
        ⟨origin, call, stageReason, reached, lifted⟩ | ⟨liftedTest, testReady, _boolean⟩
      · exact ⟨context, _, _, .ifConditionFault (lookupStatement?_sound statementFound) form lifted,
          .rejected origin call stageReason context reached⟩
      · obtain ⟨nextContext, staged, reached, lifted, adapted⟩ := body_prefix bridge functions condition
          (branches truth) testReady (Nat.le_trans (Nat.le_of_lt (Nat.lt_trans branchStrict strict)) within)
          (.control branchTrace)
        cases adapted with
        | rejected origin call reason reachedContext reached =>
          exact ⟨context, _, _, .ifFault (lookupStatement?_sound statementFound) form liftedTest lifted,
            .rejected origin call reason context reached⟩
        | completed matched =>
          cases matched
          rcases remaining with remaining | stopped
          · have nextReady := body_ready bridge functions condition (branchPreservation truth) testReady lifted
            obtain ⟨nextMap, nextWorld, nextStore, nextEnvironments, nextHeaps, nextLocals, nextAgrees,
              nextTyped, nextReference, nextRead, nextUnmapped, nextState, nextCondition, nextAdmitted⟩ := nextReady
            obtain ⟨lastContext, result, finalHeap, restTrace, restAdapted⟩ := remaining
              (Nat.le_trans (Nat.le_of_lt tailStrict) within) nextEnvironments nextHeaps nextLocals
              nextAgrees nextTyped nextReference nextRead nextUnmapped nextState nextCondition nextAdmitted tail
            exact ⟨lastContext, result, finalHeap,
              .ifFallthrough (lookupStatement?_sound statementFound) form liftedTest lifted restTrace, restAdapted⟩
          · have selectedStopped : GenericLexicalStatements.Stopped invocation.source
                (if truth then left else right.getD []) := by cases truth <;> simp_all
            obtain ⟨stagedSize, measured⟩ := Staging.Recursive.Size.StatementsIn.of_trace lifted
            exact False.elim (CallableIndexedOwnedPreparedStagedScopedBranchSourceTyping.stopped_not_fallthrough unique selectedStopped measured)
    | returned value => cases restored
    | breaking environment => cases restored
    | continuing environment => cases restored
    | fault reason => cases restored

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageConditionalLifting
