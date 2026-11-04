import Solcore.SourceSemantics.CoreLowering.Internal.Selected.StageExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.StageWhileMatch
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedLexicalAllocation
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.ScopedSourceInversion
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCallBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedScopedTerminalStatements
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedScopedLexicalPreservation

/-!
# Lifting to staged Source: statements

Inversion and lifting of lexical statements, scoped terminals, discards, blocks and conditionals.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageLexicalInversion
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageLexicalInversion
open Frontend SourceInference
open SelectedCompilationStageScopedLiftBounds

variable {program : Program} {source : TypedSource}
  {context nextContext finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {environment : Dynamic.Environment} {before after : Dynamic.Heap}
  {id : StatementId} {node : StatementNode} {binder : TypedBinder}
  {size : Nat} {outcome : Dynamic.ControlOutcome} {reason : Dynamic.SemanticFault}

private theorem selected (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) {other}
    (contains : ContainsStatement source id other) : other = node :=
  Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)

theorem absent_value (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .letDecl binder none)
    (extended : BinderExtends source.owner context binder nextContext)
    (trace : SourceExecutionSize.StatementExecutes program size context evidence source environment
      before id finalContext outcome after) :
    size = SourceExecutionSize.stepSize [] ∧ finalContext = nextContext ∧
      ∃ location, outcome = .fallthrough ((binder.id, location) :: environment) ∧
      Dynamic.Heap.Allocates before binder.scheme.body none location after := by
  cases trace <;> have same := selected unique found (by assumption) <;> subst_vars <;> simp_all
  rename_i extension allocated
  have equal := Dynamic.BinderExtends.functional extended extension
  exact equal.symm

theorem absent_fault (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .letDecl binder none)
    (mono : binder.scheme.quantified = [])
    (trace : SourceExecutionSize.StatementFaults program size context evidence source environment
      before id reason after) : False := by
  cases trace
  case missing absent => exact Dynamic.StatementAbsentIn.excludes_contains absent (lookupStatement?_sound found)
  all_goals have same := selected unique found (by assumption)
  all_goals subst_vars
  all_goals simp_all

 theorem initialized_value {expression : ExpressionId}
    (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .letDecl binder (some expression))
    (mono : binder.scheme.quantified = [])
    (extended : BinderExtends source.owner context binder nextContext)
    (trace : SourceExecutionSize.StatementExecutes program size context evidence source environment
      before id finalContext outcome after) :
    ∃ child value middle location, size = SourceExecutionSize.stepSize [child] ∧ finalContext = nextContext ∧
      outcome = .fallthrough ((binder.id, location) :: environment) ∧
      SourceExecutionSize.ExpressionEvaluates program child context evidence source environment
        before expression value middle ∧
      Dynamic.Heap.Allocates middle binder.scheme.body (some value) location after := by
  cases trace <;> have same := selected unique found (by assumption) <;> subst_vars <;> simp_all
  rename_i _contains extension allocated
  have equal := Dynamic.BinderExtends.functional extended extension
  exact ⟨_, rfl, equal.symm, _, _, by assumption, allocated⟩

theorem initialized_fault {expression : ExpressionId}
    (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .letDecl binder (some expression))
    (mono : binder.scheme.quantified = [])
    (trace : SourceExecutionSize.StatementFaults program size context evidence source environment
      before id reason after) :
    ∃ child, child < size ∧
      SourceExecutionSize.ExpressionFaults program child context evidence source environment
        before expression reason after := by
  cases trace
  case missing absent => exact False.elim (Dynamic.StatementAbsentIn.excludes_contains absent (lookupStatement?_sound found))
  all_goals have same := selected unique found (by assumption)
  all_goals subst_vars
  all_goals simp_all
  refine ⟨_, ?_, by assumption⟩
  exact SourceExecutionSize.child_lt_stepSize (by simp)


private theorem empty_trace {mode : Bool} {invocation : Staging.Recursive.Scope}
    {context : SourceSemantics.Context} {environment : Dynamic.Environment} {heap : Dynamic.Heap} :
    PlainStatements program mode (SourceExecutionSize.stepSize []) invocation context environment heap
      [] context (.fallthrough environment) heap := by
  cases mode <;> exact .control .nil

/-- The accepted absent declaration performs its exact ordinary allocation
and continues in the extended lexical context. -/
theorem absent {mode : Bool} {invocation : Staging.Recursive.Scope} {rest : List StatementId}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupStatement? id = some node) (form : node.form = .letDecl binder none)
    (mono : binder.scheme.quantified = [])
    (extended : BinderExtends invocation.source.owner context binder nextContext)
    (trace : PlainStatements program mode size invocation context environment before
      (id :: rest) finalContext outcome after) :
    ∃ tailSize location bound, tailSize < size ∧
      Dynamic.Heap.Allocates before binder.scheme.body none location bound ∧
      PlainStatements program mode tailSize invocation nextContext ((binder.id, location) :: environment)
        bound rest finalContext outcome after := by
  rcases SelectedCompilationStageScopedSourceInversion.head_and_tail unique found
    (by intro expression equal; rw [form] at equal; cases equal) trace with
    ⟨_, _, _, _, _, failed⟩ | ⟨_, strict, stopped, head⟩ |
    ⟨_, tailSize, middleContext, nextEnvironment, middle, _, tailStrict, head, tail⟩
  · exact (absent_fault unique found form mono failed).elim
  · obtain ⟨rfl, equalContext, location, equalOutcome, allocated⟩ := absent_value unique found form extended head
    subst finalContext
    subst outcome
    rcases stopped with impossible | rfl
    · cases impossible
    · exact ⟨SourceExecutionSize.stepSize [], location, after, strict, allocated, empty_trace⟩
  · obtain ⟨_, equalContext, location, equalOutcome, allocated⟩ := absent_value unique found form extended head
    subst middleContext
    cases equalOutcome
    exact ⟨tailSize, location, middle, tailStrict, allocated, tail⟩

/-- An initializer fault precedes allocation. Successful initialization keeps
both its exact expression heap and the following allocation and suffix. -/
theorem initialized {mode : Bool} {invocation : Staging.Recursive.Scope} {rest : List StatementId}
    {expression : ExpressionId}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupStatement? id = some node) (form : node.form = .letDecl binder (some expression))
    (mono : binder.scheme.quantified = [])
    (extended : BinderExtends invocation.source.owner context binder nextContext)
    (trace : PlainStatements program mode size invocation context environment before
      (id :: rest) finalContext outcome after) :
    (∃ child reason, child < size ∧ finalContext = context ∧ outcome = .fault reason ∧
      RecursiveNamedCallBounds.ExpressionOutcome program child context invocation.evidence invocation.source
        environment before expression (.fault reason) after) ∨
    (∃ child tailSize value middle location bound, child < size ∧ tailSize < size ∧
      RecursiveNamedCallBounds.ExpressionOutcome program child context invocation.evidence invocation.source
        environment before expression (.value value) middle ∧
      Dynamic.Heap.Allocates middle binder.scheme.body (some value) location bound ∧
      PlainStatements program mode tailSize invocation nextContext ((binder.id, location) :: environment)
        bound rest finalContext outcome after) := by
  rcases SelectedCompilationStageScopedSourceInversion.head_and_tail unique found
    (by intro expression equal; rw [form] at equal; cases equal) trace with
    ⟨_, reason, strict, equalContext, equalOutcome, failed⟩ | ⟨_, strict, stopped, head⟩ |
    ⟨_, tailSize, middleContext, nextEnvironment, middle, strict, tailStrict, head, tail⟩
  · obtain ⟨child, childStrict, failed⟩ := initialized_fault unique found form mono failed
    exact .inl ⟨child, reason, Nat.lt_trans childStrict strict, equalContext, equalOutcome, .fault failed⟩
  · obtain ⟨child, value, middle, location, rfl, equalContext, equalOutcome, evaluated, allocated⟩ :=
      initialized_value unique found form mono extended head
    subst finalContext
    subst outcome
    rcases stopped with impossible | rfl
    · cases impossible
    · exact .inr ⟨child, SourceExecutionSize.stepSize [], value, middle, location, after,
        Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) strict,
        by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega,
        .value evaluated, allocated, empty_trace⟩
  · obtain ⟨child, value, expressionHeap, location, rfl, equalContext, equalOutcome, evaluated, allocated⟩ :=
      initialized_value unique found form mono extended head
    subst middleContext
    cases equalOutcome
    exact .inr ⟨child, tailSize, value, expressionHeap, location, middle,
      Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) strict, tailStrict,
      .value evaluated, allocated, tail⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageLexicalInversion
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageDiscardInversion
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageDiscardInversion
open Frontend SourceInference
open SelectedCompilationStageScopedLiftBounds

private theorem statement_value {program : Program} {source : TypedSource}
    {context finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : StatementId} {node : StatementNode} {expression : ExpressionId} {semicolon : Bool}
    {size : Nat} {outcome : Dynamic.ControlOutcome}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (form : node.form = .expression expression semicolon)
    (trace : SourceExecutionSize.StatementExecutes program size context evidence source environment
      before id finalContext outcome after) :
    ∃ child value, size = SourceExecutionSize.stepSize [child] ∧ finalContext = context ∧
      outcome = .fallthrough environment ∧
      SourceExecutionSize.ExpressionEvaluates program child context evidence source environment
        before expression value after := by
  have sameNode : ∀ {other}, ContainsStatement source id other → other = node := by
    intro other contains
    exact Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  cases trace <;> have same := sameNode (by assumption) <;> subst_vars <;> simp_all
  exact ⟨_, rfl, _, by assumption⟩

private theorem statement_fault {program : Program} {source : TypedSource}
    {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : StatementId} {node : StatementNode} {expression : ExpressionId} {semicolon : Bool}
    {size : Nat} {reason : Dynamic.SemanticFault}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (form : node.form = .expression expression semicolon)
    (trace : SourceExecutionSize.StatementFaults program size context evidence source environment
      before id reason after) :
    ∃ child, child < size ∧
      SourceExecutionSize.ExpressionFaults program child context evidence source environment
        before expression reason after := by
  have sameNode : ∀ {other}, ContainsStatement source id other → other = node := by
    intro other contains
    exact Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  cases trace
  case missing absent => exact False.elim (Dynamic.StatementAbsentIn.excludes_contains absent (lookupStatement?_sound found))
  all_goals have same := sameNode (by assumption)
  all_goals subst_vars
  all_goals simp_all
  refine ⟨_, ?_, by assumption⟩
  exact SourceExecutionSize.child_lt_stepSize (by simp)

/-- Discard executes its expression before its suffix. A singleton function
uses the actual empty suffix; a fault never executes that suffix. -/
theorem child_and_tail {program : Program} {mode semicolon : Bool} {invocation : Staging.Recursive.Scope}
    {context finalContext : SourceSemantics.Context} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : StatementId} {rest : List StatementId}
    {node : StatementNode} {expression : ExpressionId} {size : Nat} {outcome : Dynamic.ControlOutcome}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .expression expression semicolon)
    (discarded : semicolon = true ∨ mode = false)
    (trace : PlainStatements program mode size invocation context environment before
      (id :: rest) finalContext outcome after) :
    (∃ childSize reason, childSize < size ∧ finalContext = context ∧ outcome = .fault reason ∧
      RecursiveNamedCallBounds.ExpressionOutcome program childSize context invocation.evidence invocation.source
        environment before expression (.fault reason) after) ∨
    (∃ childSize tailSize value middle, childSize < size ∧ tailSize < size ∧
      RecursiveNamedCallBounds.ExpressionOutcome program childSize context invocation.evidence invocation.source
        environment before expression (.value value) middle ∧
      PlainStatements program mode tailSize invocation context environment middle rest finalContext outcome after) := by
  have sameNode : ∀ {other}, ContainsStatement invocation.source id other → other = node := by
    intro other contains
    exact Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  cases mode with
  | false =>
    change RecursiveNamedCallBounds.StatementsOutcome _ _ _ _ _ _ _ _ _ _ _ at trace
    cases trace with
    | control executed =>
      cases executed with
      | cons head tail =>
        obtain ⟨child, value, rfl, rfl, equal, evaluated⟩ := statement_value unique found form head
        cases equal
        exact .inr ⟨child, _, value, _, by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil]; omega,
          SourceExecutionSize.child_lt_stepSize (by simp), .value evaluated, .control tail⟩
      | terminal head terminal =>
        obtain ⟨_, _, _, _, equal, _⟩ := statement_value unique found form head
        rw [equal] at terminal
        cases terminal
    | fault failed =>
      cases failed with
      | head failed =>
        obtain ⟨child, strict, failed⟩ := statement_fault unique found form failed
        exact .inl ⟨child, _, Nat.lt_trans strict (SourceExecutionSize.child_lt_stepSize (by simp)),
          rfl, rfl, .fault failed⟩
      | tail head tail =>
        obtain ⟨child, value, rfl, rfl, equal, evaluated⟩ := statement_value unique found form head
        cases equal
        exact .inr ⟨child, _, value, _, by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil]; omega,
          SourceExecutionSize.child_lt_stepSize (by simp), .value evaluated, .fault tail⟩
  | true =>
    have semicolonTrue : semicolon = true := by simpa using discarded
    subst semicolon
    change RecursiveNamedCallBounds.FunctionOutcome _ _ _ _ _ _ _ _ _ _ _ at trace
    cases trace with
    | control executed =>
      cases executed with
      | tailExpression contains otherForm evaluated =>
        cases sameNode contains
        rw [form] at otherForm
        cases otherForm
      | singleton _ _ head =>
        obtain ⟨child, value, rfl, rfl, equal, evaluated⟩ := statement_value unique found form head
        cases equal
        exact .inr ⟨child, SourceExecutionSize.stepSize [], value, _,
          by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil]; omega, by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil]; omega,
          .value evaluated, .control .nil⟩
      | cons head tail =>
        obtain ⟨child, value, rfl, rfl, equal, evaluated⟩ := statement_value unique found form head
        cases equal
        exact .inr ⟨child, _, value, _, by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil]; omega,
          SourceExecutionSize.child_lt_stepSize (by simp), .value evaluated, .control tail⟩
      | terminal head terminal =>
        obtain ⟨_, _, _, _, equal, _⟩ := statement_value unique found form head
        rw [equal] at terminal
        cases terminal
    | fault failed =>
      cases failed with
      | singleton failed | head failed =>
        obtain ⟨child, strict, failed⟩ := statement_fault unique found form failed
        exact .inl ⟨child, _, Nat.lt_trans strict (SourceExecutionSize.child_lt_stepSize (by simp)),
          rfl, rfl, .fault failed⟩
      | tailExpression contains otherForm _ =>
        cases sameNode contains
        rw [form] at otherForm
        cases otherForm
      | tail head tail =>
        obtain ⟨child, value, rfl, rfl, equal, evaluated⟩ := statement_value unique found form head
        cases equal
        exact .inr ⟨child, _, value, _, by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil]; omega,
          SourceExecutionSize.child_lt_stepSize (by simp), .value evaluated, .fault tail⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageDiscardInversion
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageConditionalSourceInversion
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageConditionalSourceInversion
open Frontend SourceInference

/-- The ordinary conditional retains the chosen arm, restored outer context
and two strictly smaller traces. An absent else arm is the empty scoped body. -/
theorem control {program : Program} {source : TypedSource}
    {context finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : StatementId} {node : StatementNode} {condition : ExpressionId}
    {thenBody : List StatementId} {elseBody : Option (List StatementId)}
    {size : Nat} {outcome : Dynamic.ControlOutcome}
    (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node)
    (form : node.form = .ifThen condition thenBody elseBody)
    (trace : SourceExecutionSize.StatementExecutes program size context evidence source
      environment before id finalContext outcome after) :
    ∃ testSize branchSize truth middle innerContext innerOutcome,
      testSize < size ∧ branchSize < size ∧ finalContext = context ∧
      outcome = Dynamic.restoreControl environment innerOutcome ∧
      SourceExecutionSize.ExpressionEvaluates program testSize context evidence source environment before
        condition (.bool truth) middle ∧
      SourceExecutionSize.StatementsExecute program branchSize context evidence source environment middle
        (if truth then thenBody else elseBody.getD []) innerContext innerOutcome after := by
  have sameNode : ∀ {other}, ContainsStatement source id other → other = node := by
    intro other contains
    exact Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  cases trace
  case ifTrue same test actual branch =>
    cases sameNode actual
    rw [form] at same
    cases same
    refine ⟨_, _, true, _, _, _, ?_, ?_, rfl, rfl, test, branch⟩
    · exact SourceExecutionSize.child_lt_stepSize (by simp)
    · exact SourceExecutionSize.child_lt_stepSize (by simp)
  case ifFalseWithElse same test actual branch =>
    cases sameNode actual
    rw [form] at same
    cases same
    refine ⟨_, _, false, _, _, _, ?_, ?_, rfl, rfl, test, branch⟩
    · exact SourceExecutionSize.child_lt_stepSize (by simp)
    · exact SourceExecutionSize.child_lt_stepSize (by simp)
  case ifFalseWithoutElse same actual test =>
    cases sameNode actual
    rw [form] at same
    cases same
    refine ⟨_, SourceExecutionSize.stepSize [], false, _, context, .fallthrough environment,
      ?_, ?_, rfl, rfl, test, ?_⟩
    · exact SourceExecutionSize.child_lt_stepSize (by simp)
    · have positive := test.positive
      simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero]
      omega
    · exact .nil
  all_goals
    have same := sameNode (by assumption)
    subst_vars
    simp_all

/-- Ordinary faults distinguish failed conditions, non-Boolean values and
faults in the chosen arm. No typing premise hides one of these cases. -/
theorem fault {program : Program} {source : TypedSource}
    {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : StatementId} {node : StatementNode} {condition : ExpressionId}
    {thenBody : List StatementId} {elseBody : Option (List StatementId)}
    {size : Nat} {reason : Dynamic.SemanticFault}
    (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node)
    (form : node.form = .ifThen condition thenBody elseBody)
    (trace : SourceExecutionSize.StatementFaults program size context evidence source
      environment before id reason after) :
    (∃ testSize, testSize < size ∧
      SourceExecutionSize.ExpressionFaults program testSize context evidence source environment before
        condition reason after) ∨
    (∃ testSize value actual, testSize < size ∧ reason = .typeMismatch .bool actual ∧
      SourceExecutionSize.ExpressionEvaluates program testSize context evidence source environment before
        condition value after ∧ ¬ Dynamic.BooleanValue value ∧ Dynamic.ValueRuntimeType value actual) ∨
    (∃ testSize branchSize truth middle innerContext,
      testSize < size ∧ branchSize < size ∧
      SourceExecutionSize.ExpressionEvaluates program testSize context evidence source environment before
        condition (.bool truth) middle ∧
      SourceExecutionSize.StatementsFault program branchSize context evidence source environment middle
        (if truth then thenBody else elseBody.getD []) innerContext reason after) := by
  have sameNode : ∀ {other}, ContainsStatement source id other → other = node := by
    intro other contains
    exact Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  cases trace
  case missing absent => exact False.elim (Dynamic.StatementAbsentIn.excludes_contains absent (lookupStatement?_sound found))
  case ifCondition same actual failed =>
    cases sameNode actual
    rw [form] at same
    cases same
    exact .inl ⟨_, SourceExecutionSize.child_lt_stepSize (by simp), failed⟩
  case ifConditionType same nonboolean typed actual test =>
    cases sameNode actual
    rw [form] at same
    cases same
    exact .inr (.inl ⟨_, _, _, SourceExecutionSize.child_lt_stepSize (by simp), rfl, test, nonboolean, typed⟩)
  case ifTrueBody same test actual failed =>
    cases sameNode actual
    rw [form] at same
    cases same
    refine .inr (.inr ⟨_, _, true, _, _, ?_, ?_, test, failed⟩)
    · exact SourceExecutionSize.child_lt_stepSize (by simp)
    · exact SourceExecutionSize.child_lt_stepSize (by simp)
  case ifFalseBody same test actual failed =>
    cases sameNode actual
    rw [form] at same
    cases same
    refine .inr (.inr ⟨_, _, false, _, _, ?_, ?_, test, failed⟩)
    · exact SourceExecutionSize.child_lt_stepSize (by simp)
    · exact SourceExecutionSize.child_lt_stepSize (by simp)
  all_goals
    have same := sameNode (by assumption)
    subst_vars
    simp_all

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageConditionalSourceInversion
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStagePhysicalReadiness
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStagePhysicalReadiness
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open SelectedCompilationStageScopedLiftBounds SelectedCompilationStageBodyLiftBounds
open CallableIndexedOwnedAdmittedStagedConditionalHeads
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
  {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {certificate : GenericExpressionMeaning.Certificate}
  {test : ExpressionId} {node : ExpressionNode} {statements : List StatementId}
  {expected : TypeSystem.Ty} {type : Ty} {testCode loopCode : Expr}

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions

variable {environment : Dynamic.Environment} {canonical actual : Environment}
  {actualContext : Core.Context} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}

local notation "ReadyAt" => SelectedCompilationStageWhileLifting.PhysicalReady (administrative := administrative) (receiving := receiving)
  (frame := frame) (globals := globals) (context := context) (scope := scope)
  bridge functions condition environment canonical actual actualContext ξ contextLocation native

theorem body_prefix {budget size : Nat} {before after : Dynamic.Heap}
    {finalContext : SourceSemantics.Context} {outcome : Dynamic.ControlOutcome}
    (body : FlowLifts (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) bridge functions condition context scope false statements budget)
    (ready : ReadyAt before) (within : size ≤ budget)
    (trace : RecursiveNamedCallBounds.StatementsOutcome program size context invocation.evidence invocation.source
      environment before statements finalContext outcome after) :
    BodyLift program stages false invocation context environment before statements finalContext outcome after := by
  obtain ⟨mapping, world, store, environments, heaps, locals, agrees, actualTyped, reference, read, unmapped,
    initial, conditioned, admitted⟩ := ready
  exact body within environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted trace

theorem body_ready {before after : Dynamic.Heap} {finalContext : SourceSemantics.Context}
    {finalEnvironment : Dynamic.Environment}
    (preservation : ∀ budget, FlowPreserves (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions condition context scope false statements expected type loopCode budget)
    (ready : ReadyAt before)
    (trace : Staging.Recursive.StatementsIn program stages false invocation context environment before statements
      finalContext (.fallthrough finalEnvironment) after) : ReadyAt after := by
  obtain ⟨mapping, world, store, environments, heaps, locals, agrees, actualTyped, reference, read, unmapped,
    initial, conditioned, admitted⟩ := ready
  obtain ⟨size, measured⟩ := Staging.Recursive.Size.StatementsIn.of_trace trace
  obtain ⟨_, finalStore, finalMap, finalWorld, _, _, finalHeaps, maps, worlds, preserved, metadata,
    last, _, post⟩ := preservation size (Nat.le_refl _) environments heaps locals agrees actualTyped
      reference read unmapped initial conditioned admitted measured
  exact ⟨finalMap, finalWorld, finalStore, environments.extend maps worlds, finalHeaps, locals.mono metadata,
    agrees, actualTyped.weaken worlds, reference,
    ((preserved contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read),
    (preserved contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1, last, conditioned, post⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStagePhysicalReadiness
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageLexicalLifting
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageLexicalLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedAllocationCompletion
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open SelectedCompilationStageLiftBounds (LiftsAt)
open SelectedCompilationStageBodyLiftBounds SelectedCompilationStageScopedLiftBounds
open GenericLexicalStatements
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry}
  (definitions : layouts.definitions = (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
  (registered : frame.Registered (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
  (producer : ProtectedStateTransition.OrdinaryAllocation.Producer callerProtocol layouts frame
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions))
  (condition : Location → NativeFrame → Prop)
  (acquire : ∀ location native, condition location native →
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer location native)
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {faults : RecursiveStageMeaning.FaultRep}

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions


include bridge functions definitions registered producer acquire in
/-- The original absent allocation constructs the actual extended physical
state before the body suffix is lifted. -/
theorem absent {budget : Nat} {context nextContext : SourceSemantics.Context}
    {scope : SourceCoreLocalCell.Scope} {mode : Bool} {id : StatementId} {rest : List StatementId}
    {node : StatementNode} {binder : TypedBinder} {payload : Ty}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupStatement? id = some node) (form : node.form = .letDecl binder none)
    (mono : binder.scheme.quantified = [])
    (extended : BinderExtends invocation.source.owner context binder nextContext)
    (ordinary : invocation.source.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (projection : compiled.compatible.checked.catalog.project binder.scheme.body = .ok payload)
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (absentRequest invocation.source scope binder payload))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
      (layouts.allocatorAt owner active onError) (absentRequest invocation.source scope binder payload))
    (same : annotation.original = allocation.expression)
    {administrative : Core.Context}
    (remaining : FlowLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      bridge functions condition nextContext ((binder.id, payload) :: scope) mode rest budget) :
    FlowLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      bridge functions condition context scope mode (id :: rest) budget := by
  intro size within mapping world actualContext environment canonical actual before store ξ
    contextLocation native environments heaps locals agrees actualTyped reference read unmapped
    initial conditioned admitted finalContext outcome after trace
  obtain ⟨tailSize, location, bound, strict, allocated, tail⟩ :=
    SelectedCompilationStageLexicalInversion.absent unique found form mono extended trace
  obtain ⟨_captured, _captures, _capturedTyped, _allocationEval, nextEnvironments, nextHeaps, nextLocals,
      nextAgrees, nextTyped, nextReference, nextRead, preservation, reached, _allocatedRelated, nextAdmitted⟩ :=
    CallableIndexedOwnedAdmittedLexicalAllocation.allocate_absent bridge functions definitions registered producer
      mono extended ordinary projection allocation annotation same environments heaps locals agrees actualTyped
      reference read allocated initial ((acquire _ _ conditioned) initial read) admitted
  obtain ⟨resultContext, result, resultHeap, restTrace, restAdapted⟩ := remaining
    (Nat.le_trans (Nat.le_of_lt strict) within) nextEnvironments nextHeaps nextLocals nextAgrees nextTyped
    nextReference nextRead (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
    reached conditioned nextAdmitted tail
  exact ⟨resultContext, result, resultHeap,
    .letUninitialized (lookupStatement?_sound found) form mono extended allocated restTrace, restAdapted⟩

include bridge functions definitions registered producer acquire in
/-- The initializer reaches its own heap first. Its real represented value
then initializes the original binder before the suffix executes. -/
theorem initialized {budget : Nat} {context nextContext : SourceSemantics.Context}
    {scope : SourceCoreLocalCell.Scope} {mode : Bool} {id : StatementId} {rest : List StatementId}
    {node : StatementNode} {binder : TypedBinder} {expression : ExpressionId}
    {expressionNode : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupStatement? id = some node) (form : node.form = .letDecl binder (some expression))
    (mono : binder.scheme.quantified = [])
    (extended : BinderExtends invocation.source.owner context binder nextContext)
    (ordinary : invocation.source.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (expressionFound : invocation.source.lookupExpression? expression = some expressionNode)
    (sourceType : expressionNode.type = binder.scheme.body)
    (typed : ExpressionHasType invocation.source context expression expressionNode.type)
    (generated : certificates context scope expression lowered)
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (initializedRequest invocation.source scope binder lowered.type))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
      (layouts.allocatorAt owner active onError) (initializedRequest invocation.source scope binder lowered.type))
    (same : annotation.original = allocation.expression)
    (children : ∀ childSize, childSize < budget →
      LiftsAt bridge context model stages invocation (certificates context) childSize)
    (preservation : ∀ childSize, CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesAt
      bridge context model stages invocation (certificates context) faults childSize)
    {administrative : Core.Context}
    (remaining : FlowLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      bridge functions condition nextContext ((binder.id, lowered.type) :: scope) mode rest budget) :
    FlowLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      bridge functions condition context scope mode (id :: rest) budget := by
  intro size within mapping world actualContext environment canonical actual before store ξ
    contextLocation native environments heaps locals agrees actualTyped reference read unmapped
    initial conditioned admitted finalContext outcome after trace
  rcases SelectedCompilationStageLexicalInversion.initialized unique found form mono extended trace with
    ⟨childSize, reason, strict, rfl, rfl, evaluated⟩ |
    ⟨childSize, tailSize, sourceValue, middle, location, bound, strict, tailStrict, evaluated, allocated, tail⟩
  · obtain ⟨staged, reached, lifted, adapted⟩ :=
      children childSize (Nat.lt_of_lt_of_le strict within) generated expressionFound typed
        environments heaps locals agrees actualTyped initial admitted evaluated
    cases adapted with
    | completed => exact ⟨_, _, _, .letFault (lookupStatement?_sound found) form mono lifted,
        .completed (.fault reason)⟩
    | rejected origin call reason reached =>
      exact ⟨_, _, _, .letFault (lookupStatement?_sound found) form mono lifted,
        .rejected origin call reason _ reached⟩
  · obtain ⟨staged, reached, lifted, adapted⟩ :=
      children childSize (Nat.lt_of_lt_of_le strict within) generated expressionFound typed
        environments heaps locals agrees actualTyped initial admitted evaluated
    cases adapted with
    | rejected origin call reason reached =>
      exact ⟨_, _, _, .letFault (lookupStatement?_sound found) form mono lifted,
        .rejected origin call reason _ reached⟩
    | completed =>
      obtain ⟨stagedSize, measured⟩ := Staging.Recursive.Size.Expression.of_trace lifted
      obtain ⟨value, middleStore, middleMap, middleWorld, _evaluated, represented, middleHeaps,
          maps, worlds, framePreserved, metadata, middleState, _related, post⟩ :=
        preservation stagedSize generated expressionFound typed environments heaps locals agrees actualTyped
          initial admitted measured
      cases represented with
      | value payload =>
        have frameRead := (framePreserved contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read
        have stillUnmapped := (framePreserved contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
        obtain ⟨_captured, _captures, _capturedTyped, _allocationEval, nextEnvironments, nextHeaps, nextLocals,
            nextAgrees, nextTyped, nextReference, nextRead, allocationFrame, nextState, _allocatedRelated, nextAdmitted⟩ :=
          CallableIndexedOwnedAdmittedLexicalAllocation.allocate_initialized bridge functions definitions registered producer
            mono extended ordinary allocation annotation same (sourceType ▸ post.at_value.1) (sourceType ▸ payload)
            (environments.extend maps worlds) middleHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds)
            reference frameRead allocated middleState ((acquire _ _ conditioned) middleState frameRead) post.at_value.2
        obtain ⟨resultContext, result, resultHeap, restTrace, restAdapted⟩ := remaining
          (Nat.le_trans (Nat.le_of_lt tailStrict) within) nextEnvironments nextHeaps nextLocals nextAgrees nextTyped
          nextReference nextRead (allocationFrame contextLocation stillUnmapped (List.getElem?_eq_some_iff.mp frameRead).1).1
          nextState conditioned nextAdmitted tail
        exact ⟨resultContext, result, resultHeap,
          .letInitialized (lookupStatement?_sound found) form lifted mono extended allocated restTrace, restAdapted⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageLexicalLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageDiscardLifting
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageDiscardLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open SelectedCompilationStageBodyLiftBounds SelectedCompilationStageScopedLiftBounds
open SelectedCompilationStageLiftBounds (LiftsAt)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry}
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {administrative : Core.Context}
  (condition : Location → NativeFrame → Prop)
  {faults : RecursiveStageMeaning.FaultRep}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions


include bridge functions condition in
/-- A completed expression supplies the real next physical state before the
suffix is lifted. A rejected expression stops at its own reached heap. -/
theorem lifts {budget : Nat} {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {mode semicolon : Bool} {id : StatementId} {rest : List StatementId}
    {node : StatementNode} {expression : ExpressionId} {expressionNode : ExpressionNode}
    {lowered : SourceCoreBasic.LoweredExpr} {certificate : GenericExpressionMeaning.Certificate}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .expression expression semicolon)
    (discarded : semicolon = true ∨ mode = false)
    (expressionFound : invocation.source.lookupExpression? expression = some expressionNode)
    (typed : ExpressionHasType invocation.source context expression expressionNode.type)
    (generated : certificate scope expression lowered)
    (children : ∀ childSize, childSize < budget → LiftsAt bridge context model stages invocation certificate childSize)
    (preservation : ∀ childSize, CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesAt
      bridge context model stages invocation certificate faults childSize)
    (remaining : FlowLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      bridge functions condition context scope mode rest budget) :
    FlowLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      bridge functions condition context scope mode (id :: rest) budget := by
  intro size within mapping world actualContext environment canonical actual before store ξ
    contextLocation native environments heaps locals agrees actualTyped reference read unmapped
    initial conditioned admitted finalContext outcome after trace
  rcases SelectedCompilationStageDiscardInversion.child_and_tail unique found form discarded trace with
    ⟨childSize, reason, strict, rfl, rfl, evaluated⟩ |
    ⟨childSize, tailSize, sourceValue, middle, strict, tailStrict, evaluated, tail⟩
  · obtain ⟨staged, reached, lifted, adapted⟩ :=
      children childSize (Nat.lt_of_lt_of_le strict within) generated expressionFound typed
        environments heaps locals agrees actualTyped initial admitted evaluated
    cases adapted with
    | completed => exact ⟨_, _, _, .expressionFault (lookupStatement?_sound found) form lifted,
        .completed (.fault reason)⟩
    | rejected origin call reason reached =>
      exact ⟨_, _, _, .expressionFault (lookupStatement?_sound found) form lifted,
        .rejected origin call reason _ reached⟩
  · obtain ⟨staged, reached, lifted, adapted⟩ :=
      children childSize (Nat.lt_of_lt_of_le strict within) generated expressionFound typed
        environments heaps locals agrees actualTyped initial admitted evaluated
    cases adapted with
    | rejected origin call reason reached =>
      exact ⟨_, _, _, .expressionFault (lookupStatement?_sound found) form lifted,
        .rejected origin call reason _ reached⟩
    | completed =>
      obtain ⟨stagedSize, measured⟩ := Staging.Recursive.Size.Expression.of_trace lifted
      obtain ⟨_value, middleStore, middleMap, middleWorld, _evaluated, _represented, middleHeaps,
          maps, worlds, framePreserved, metadata, middleState, _related, post⟩ :=
        preservation stagedSize generated expressionFound typed environments heaps locals agrees actualTyped
          initial admitted measured
      have frameRead := (framePreserved contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read
      have stillUnmapped := (framePreserved contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
      obtain ⟨nextContext, result, finalHeap, restTrace, restAdapted⟩ := remaining
        (Nat.le_trans (Nat.le_of_lt tailStrict) within) (environments.extend maps worlds) middleHeaps
        (locals.mono metadata) agrees (actualTyped.weaken worlds) reference frameRead stillUnmapped
        middleState conditioned post.at_value.2 tail
      refine ⟨nextContext, result, finalHeap, ?_, restAdapted⟩
      rcases discarded with rfl | rfl
      · exact .discard (lookupStatement?_sound found) form lifted restTrace
      · cases semicolon with
        | false => exact .discardValue (lookupStatement?_sound found) form lifted restTrace
        | true => exact .discard (lookupStatement?_sound found) form lifted restTrace

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageDiscardLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageBlockLifting
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageBlockLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open SelectedCompilationStageBodyLiftBounds SelectedCompilationStageScopedLiftBounds
open CallableIndexedOwnedAdmittedStagedConditionalHeads (BranchPreserves)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry}
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {administrative : Core.Context}
  (condition : Location → NativeFrame → Prop)
  {faults : RecursiveStageMeaning.FaultRep}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}

include bridge functions condition in
/-- A scoped block keeps the physical state reached by its inner execution.
Its suffix starts with the restored outer bindings and that same heap. -/
theorem lifts {budget : Nat} {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {mode : Bool} {id : StatementId} {rest statements : List StatementId} {node : StatementNode}
    {expected : TypeSystem.Ty} {type : Ty} {innerCode : Expr}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .block statements)
    (inner : FlowLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      bridge functions condition context scope false statements budget)
    (preservation : ∀ childSize, BranchPreserves (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions condition context scope statements expected type innerCode childSize)
    (remaining : FlowLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      bridge functions condition context scope mode rest budget ∨
      GenericLexicalStatements.Stopped invocation.source statements) :
    FlowLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      bridge functions condition context scope mode (id :: rest) budget := by
  intro size within mapping world actualContext environment canonical actual before store ξ
    contextLocation native environments heaps locals agrees actualTyped reference read unmapped
    initial conditioned admitted finalContext outcome after trace
  have notTail : ∀ expression, node.form ≠ .expression expression false := by
    intro expression same
    rw [form] at same
    cases same
  rcases SelectedCompilationStageScopedSourceInversion.head_and_tail unique found notTail trace with
    ⟨headSize, reason, strict, contextEq, outcomeEq, failed⟩ |
    ⟨headSize, strict, stopped, executed⟩ |
    ⟨headSize, tailSize, middleContext, nextEnvironment, middle, strict, tailStrict, executed, tail⟩
  · subst finalContext
    subst outcome
    obtain ⟨innerSize, innerContext, innerStrict, innerTrace⟩ :=
      SelectedCompilationStageScopedSourceInversion.block_fault unique found form failed
    obtain ⟨nextContext, staged, reached, lifted, adapted⟩ := inner
      (Nat.le_trans (Nat.le_of_lt (Nat.lt_trans innerStrict strict)) within)
      environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted
      (show PlainStatements program false innerSize invocation context environment before statements
        innerContext (.fault reason) after from .fault innerTrace)
    cases adapted with
    | completed matched =>
      cases matched
      exact ⟨context, _, _, .blockFault (lookupStatement?_sound found) form lifted, .completed (.fault reason)⟩
    | rejected origin call reason reached =>
      exact ⟨context, _, _, .blockFault (lookupStatement?_sound found) form lifted, .rejected origin call reason context reached⟩
  · obtain ⟨innerSize, innerContext, innerOutcome, innerStrict, contextEq, outcomeEq, innerTrace⟩ :=
      SelectedCompilationStageScopedSourceInversion.block_control unique found form executed
    subst finalContext
    subst outcome
    obtain ⟨nextContext, staged, reached, lifted, adapted⟩ := inner
      (Nat.le_trans (Nat.le_of_lt (Nat.lt_trans innerStrict strict)) within)
      environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted
      (show PlainStatements program false innerSize invocation context environment before statements
        innerContext innerOutcome after from .control innerTrace)
    cases adapted with
    | rejected origin call reason reached =>
      exact ⟨context, _, _, .blockFault (lookupStatement?_sound found) form lifted, .rejected origin call reason context reached⟩
    | completed matched =>
      cases matched with
      | returned value =>
        exact ⟨context, _, _, .blockReturned (lookupStatement?_sound found) form lifted, .completed (.returned value)⟩
      | breaking innerEnvironment =>
        exact ⟨context, _, _, .blockBreaking (lookupStatement?_sound found) form lifted, .completed (.breaking environment)⟩
      | continuing innerEnvironment =>
        exact ⟨context, _, _, .blockContinuing (lookupStatement?_sound found) form lifted, .completed (.continuing environment)⟩
      | fault reason =>
        exact ⟨context, _, _, .blockFault (lookupStatement?_sound found) form lifted, .completed (.fault reason)⟩
      | fallthrough innerEnvironment =>
        rcases stopped with impossible | rfl
        · cases impossible
        · exact ⟨context, _, _, .blockFallthrough (lookupStatement?_sound found) form lifted .nil,
            .completed (.fallthrough environment)⟩
  · obtain ⟨innerSize, innerContext, innerOutcome, innerStrict, contextEq, restored, innerTrace⟩ :=
      SelectedCompilationStageScopedSourceInversion.block_control unique found form executed
    subst middleContext
    cases innerOutcome with
    | fallthrough innerEnvironment =>
      simp only [Dynamic.restoreControl, Dynamic.ControlOutcome.fallthrough.injEq] at restored
      subst nextEnvironment
      obtain ⟨nextContext, staged, reached, lifted, adapted⟩ := inner
        (Nat.le_trans (Nat.le_of_lt (Nat.lt_trans innerStrict strict)) within)
        environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted
        (show PlainStatements program false innerSize invocation context environment before statements
          innerContext (.fallthrough innerEnvironment) middle from .control innerTrace)
      cases adapted with
      | rejected origin call reason reached =>
        exact ⟨context, _, _, .blockFault (lookupStatement?_sound found) form lifted, .rejected origin call reason context reached⟩
      | completed matched =>
        cases matched
        obtain ⟨stagedSize, measured⟩ := Staging.Recursive.Size.StatementsIn.of_trace lifted
        rcases remaining with remaining | stopped
        · obtain ⟨_value, middleStore, middleMap, middleWorld, _evaluated, _represented, middleHeaps,
            maps, worlds, framePreserved, metadata, middleState, _related, post⟩ :=
            preservation stagedSize (Nat.le_refl _) environments heaps locals agrees actualTyped
              reference read unmapped initial conditioned admitted measured
          obtain ⟨lastContext, result, finalHeap, restTrace, restAdapted⟩ := remaining
            (Nat.le_trans (Nat.le_of_lt tailStrict) within)
            (environments.extend maps worlds) middleHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds)
            reference ((framePreserved contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
            (framePreserved contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
            middleState conditioned post tail
          exact ⟨lastContext, result, finalHeap, .blockFallthrough (lookupStatement?_sound found) form lifted restTrace,
            restAdapted⟩
        · exact False.elim (CallableIndexedOwnedPreparedStagedScopedBranchSourceTyping.stopped_not_fallthrough unique stopped measured)

    | returned value => cases restored
    | breaking environment => cases restored
    | continuing environment => cases restored
    | fault reason => cases restored

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageBlockLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageConditionalLifting
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageTerminalInversion
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageTerminalInversion
open Frontend SourceInference
open CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts (Terminal)

def terminalControl (outcome : Dynamic.ExpressionOutcome) : Dynamic.ControlOutcome :=
  match outcome with
  | .value value => .returned value
  | .fault reason => .fault reason

private theorem statement_returned {program : Program} {source : TypedSource}
    {context finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : StatementId} {node : StatementNode} {expression : ExpressionId}
    {size : Nat} {outcome : Dynamic.ControlOutcome}
    (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node)
    (form : node.form = .returnStmt (some expression))
    (trace : SourceExecutionSize.StatementExecutes program size context evidence source environment
      before id finalContext outcome after) :
    ∃ child value, child < size ∧ finalContext = context ∧ outcome = .returned value ∧
      SourceExecutionSize.ExpressionEvaluates program child context evidence source environment before expression value after := by
  have sameNode : ∀ {other}, ContainsStatement source id other → other = node := by
    intro other contains
    exact Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  cases trace <;> have same := sameNode (by assumption) <;> subst_vars <;> simp_all
  refine ⟨_, ?_, by assumption⟩
  exact SourceExecutionSize.child_lt_stepSize (by simp)

private theorem statement_failed {program : Program} {source : TypedSource}
    {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : StatementId} {node : StatementNode} {expression : ExpressionId}
    {size : Nat} {reason : Dynamic.SemanticFault}
    (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node)
    (form : node.form = .returnStmt (some expression) ∨ node.form = .expression expression false)
    (trace : SourceExecutionSize.StatementFaults program size context evidence source environment
      before id reason after) :
    ∃ child, child < size ∧
      SourceExecutionSize.ExpressionFaults program child context evidence source environment before expression reason after := by
  have sameNode : ∀ {other}, ContainsStatement source id other → other = node := by
    intro other contains
    exact Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  cases trace
  case missing absent => exact False.elim (Dynamic.StatementAbsentIn.excludes_contains absent (lookupStatement?_sound found))
  all_goals
    have same := sameNode (by assumption)
    subst_vars
    obtain form | form := form <;> simp_all
  all_goals
    refine ⟨_, ?_, by assumption⟩
    exact SourceExecutionSize.child_lt_stepSize (by simp)

/-- An actual terminal function trace exposes its exact expression child,
strictly below the original size, with unchanged context and final heap. -/
theorem child_of_body {program : Program} {source : TypedSource}
    {context finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {expression : ExpressionId} {statements : List StatementId}
    {size : Nat} {control : Dynamic.ControlOutcome}
    (unique : NodeOccurrencesUnique source)
    (terminal : Terminal source expression statements)
    (trace : RecursiveNamedCallBounds.FunctionOutcome program size context evidence source environment
      before statements finalContext control after) :
    ∃ child outcome, child < size ∧ finalContext = context ∧ control = terminalControl outcome ∧
      RecursiveNamedCallBounds.ExpressionOutcome program child context evidence source environment
        before expression outcome after := by
  cases terminal with
  | @returning id node rest found form =>
    have sameNode : ∀ {other}, ContainsStatement source id other → other = node := by
      intro other contains
      exact Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
    cases trace with
    | control executed =>
      cases executed with
      | tailExpression contains otherForm evaluated =>
        cases sameNode contains
        rw [form] at otherForm
        cases otherForm
      | singleton _ _ head | terminal head _ =>
        obtain ⟨child, value, strict, rfl, rfl, evaluated⟩ := statement_returned unique found form head
        exact ⟨child, .value value, Nat.lt_trans strict (SourceExecutionSize.child_lt_stepSize (by simp)),
          rfl, rfl, .value evaluated⟩
      | cons head _ =>
        obtain ⟨_, _, _, _, impossible, _⟩ := statement_returned unique found form head
        cases impossible
    | fault failed =>
      cases failed with
      | singleton head | head head =>
        obtain ⟨child, strict, failed⟩ := statement_failed unique found (.inl form) head
        exact ⟨child, .fault _, Nat.lt_trans strict (SourceExecutionSize.child_lt_stepSize (by simp)),
          rfl, rfl, .fault failed⟩
      | tailExpression contains otherForm _ =>
        cases sameNode contains
        rw [form] at otherForm
        cases otherForm
      | tail head _ =>
        obtain ⟨_, _, _, _, impossible, _⟩ := statement_returned unique found form head
        cases impossible
  | @tail id node found form =>
    have sameNode : ∀ {other}, ContainsStatement source id other → other = node := by
      intro other contains
      exact Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
    cases trace with
    | control executed =>
      cases executed with
      | tailExpression contains otherForm evaluated =>
        cases sameNode contains
        rw [form] at otherForm
        cases otherForm
        exact ⟨_, .value _, SourceExecutionSize.child_lt_stepSize (by simp), rfl, rfl, .value evaluated⟩
      | singleton contains notTail _ =>
        cases sameNode contains
        exact False.elim (notTail expression form)
    | fault failed =>
      cases failed with
      | singleton head =>
        obtain ⟨child, strict, failed⟩ := statement_failed unique found (.inr form) head
        exact ⟨child, .fault _, Nat.lt_trans strict (SourceExecutionSize.child_lt_stepSize (by simp)),
          rfl, rfl, .fault failed⟩
      | tailExpression contains otherForm failed =>
        cases sameNode contains
        rw [form] at otherForm
        cases otherForm
        exact ⟨_, .fault _, SourceExecutionSize.child_lt_stepSize (by simp), rfl, rfl, .fault failed⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageTerminalInversion
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageScopedTerminalInversion
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageScopedTerminalInversion
open Frontend SourceInference
open SelectedCompilationStageScopedLiftBounds
open SelectedCompilationStageBodyLiftBounds (terminalControl)

variable {program : Program} {source : TypedSource}
  {context finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {environment : Dynamic.Environment} {before after : Dynamic.Heap}
  {id : StatementId} {node : StatementNode} {expression : ExpressionId}
  {size : Nat} {outcome : Dynamic.ControlOutcome} {reason : Dynamic.SemanticFault}

private theorem statement_returned (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .returnStmt (some expression))
    (trace : SourceExecutionSize.StatementExecutes program size context evidence source environment before id finalContext outcome after) :
    ∃ child value, child < size ∧ finalContext = context ∧ outcome = .returned value ∧
      SourceExecutionSize.ExpressionEvaluates program child context evidence source environment before expression value after := by
  have sameNode : ∀ {other}, ContainsStatement source id other → other = node := by
    intro other contains
    exact Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  cases trace <;> have same := sameNode (by assumption) <;> subst_vars <;> simp_all
  refine ⟨_, ?_, by assumption⟩
  exact SourceExecutionSize.child_lt_stepSize (by simp)

private theorem statement_failed (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .returnStmt (some expression))
    (trace : SourceExecutionSize.StatementFaults program size context evidence source environment before id reason after) :
    ∃ child, child < size ∧
      SourceExecutionSize.ExpressionFaults program child context evidence source environment before expression reason after := by
  have sameNode : ∀ {other}, ContainsStatement source id other → other = node := by
    intro other contains
    exact Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  cases trace
  case missing absent => exact False.elim (Dynamic.StatementAbsentIn.excludes_contains absent (lookupStatement?_sound found))
  all_goals have same := sameNode (by assumption)
  all_goals subst_vars; simp_all
  refine ⟨_, ?_, by assumption⟩
  exact SourceExecutionSize.child_lt_stepSize (by simp)

private theorem statement_unit (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .returnStmt none)
    (trace : SourceExecutionSize.StatementExecutes program size context evidence source environment before id finalContext outcome after) :
    finalContext = context ∧ outcome = .returned .unit ∧ after = before := by
  have sameNode : ∀ {other}, ContainsStatement source id other → other = node := by
    intro other contains
    exact Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  cases trace <;> have same := sameNode (by assumption) <;> subst_vars <;> simp_all

private theorem statement_unit_no_fault (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .returnStmt none)
    (trace : SourceExecutionSize.StatementFaults program size context evidence source environment before id reason after) : False := by
  have sameNode : ∀ {other}, ContainsStatement source id other → other = node := by
    intro other contains
    exact Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  cases trace
  case missing absent => exact Dynamic.StatementAbsentIn.excludes_contains absent (lookupStatement?_sound found)
  all_goals have same := sameNode (by assumption)
  all_goals subst_vars; simp_all

theorem nil {mode : Bool} {invocation : Staging.Recursive.Scope}
    (trace : PlainStatements program mode size invocation context environment before [] finalContext outcome after) :
    finalContext = context ∧ outcome = .fallthrough environment ∧ after = before := by
  cases mode <;> cases trace with
  | control executed => cases executed; exact ⟨rfl, rfl, rfl⟩
  | fault failed => cases failed

theorem return_unit {mode : Bool} {invocation : Staging.Recursive.Scope} {rest : List StatementId}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupStatement? id = some node) (form : node.form = .returnStmt none)
    (trace : PlainStatements program mode size invocation context environment before (id :: rest) finalContext outcome after) :
    finalContext = context ∧ outcome = .returned .unit ∧ after = before := by
  rcases SelectedCompilationStageScopedSourceInversion.head_and_tail unique found
    (by intro expression equal; rw [form] at equal; cases equal) trace with
    ⟨_, _, _, _, _, failed⟩ | ⟨_, _, _, head⟩ | ⟨_, _, _, _, _, _, _, head, _⟩
  · exact (statement_unit_no_fault unique found form failed).elim
  · exact statement_unit unique found form head
  · obtain ⟨_, impossible, _⟩ := statement_unit unique found form head
    cases impossible

/-- Returning statements retain the same strict expression in both lexical
modes. The function-only tail expression remains a distinct original form. -/
theorem child_of_body {mode : Bool} {invocation : Staging.Recursive.Scope} {statements : List StatementId}
    (unique : NodeOccurrencesUnique invocation.source)
    (head : CallableIndexedOwnedAdmittedStagedScopedTerminalStatements.Head invocation expression mode statements)
    (trace : PlainStatements program mode size invocation context environment before statements finalContext outcome after) :
    ∃ child plain, child < size ∧ finalContext = context ∧ outcome = terminalControl plain ∧
      RecursiveNamedCallBounds.ExpressionOutcome program child context invocation.evidence invocation.source
        environment before expression plain after := by
  cases head with
  | returning rest contains form =>
    have found := lookupStatement?_complete unique contains
    rcases SelectedCompilationStageScopedSourceInversion.head_and_tail unique found
      (by intro expression equal; rw [form] at equal; cases equal) trace with
      ⟨_, reason, strict, rfl, rfl, failed⟩ | ⟨_, strict, _, head⟩ | ⟨_, _, _, _, _, _, _, head, _⟩
    · obtain ⟨child, childStrict, failed⟩ := statement_failed unique found form failed
      exact ⟨child, .fault reason, Nat.lt_trans childStrict strict, rfl, rfl, .fault failed⟩
    · obtain ⟨child, value, childStrict, rfl, rfl, evaluated⟩ := statement_returned unique found form head
      exact ⟨child, .value value, Nat.lt_trans childStrict strict, rfl, rfl, .value evaluated⟩
    · obtain ⟨_, _, _, _, impossible, _⟩ := statement_returned unique found form head
      cases impossible
  | tail contains form =>
    exact SelectedCompilationStageTerminalInversion.child_of_body unique
      (.tail (lookupStatement?_complete unique contains) form) trace

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageScopedTerminalInversion
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageScopedTerminalLifting
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageScopedTerminalLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open SelectedCompilationStageBodyLiftBounds SelectedCompilationStageScopedLiftBounds
open SelectedCompilationStageLiftBounds (LiftsAt)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry}
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {administrative : Core.Context}
  (condition : Location → NativeFrame → Prop)
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions


include bridge functions condition in
theorem nil {budget : Nat} {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {mode : Bool} :
    FlowLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      bridge functions condition context scope mode [] budget := by
  intro size within mapping world actualContext environment canonical actual before store ξ
    contextLocation native environments heaps locals agrees actualTyped reference read unmapped
    initial conditioned admitted finalContext outcome after trace
  obtain ⟨rfl, rfl, rfl⟩ := SelectedCompilationStageScopedTerminalInversion.nil trace
  exact ⟨_, .fallthrough environment, _, .nil, .completed (.fallthrough environment)⟩

include bridge functions condition in
theorem return_unit {budget : Nat} {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {mode : Bool} {id : StatementId} {rest : List StatementId} {node : StatementNode}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupStatement? id = some node) (form : node.form = .returnStmt none) :
    FlowLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      bridge functions condition context scope mode (id :: rest) budget := by
  intro size within mapping world actualContext environment canonical actual before store ξ
    contextLocation native environments heaps locals agrees actualTyped reference read unmapped
    initial conditioned admitted finalContext outcome after trace
  obtain ⟨rfl, rfl, rfl⟩ := SelectedCompilationStageScopedTerminalInversion.return_unit unique found form trace
  exact ⟨_, .returned .unit, _, .returnUnit (lookupStatement?_sound found) form,
    .completed (.returned .unit)⟩

include bridge functions condition in
theorem terminal {budget : Nat} {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {mode : Bool} {statements : List StatementId} {expression : ExpressionId} {node : ExpressionNode}
    {lowered : SourceCoreBasic.LoweredExpr} {certificate : GenericExpressionMeaning.Certificate}
    (unique : NodeOccurrencesUnique invocation.source)
    (head : CallableIndexedOwnedAdmittedStagedScopedTerminalStatements.Head invocation expression mode statements)
    (found : invocation.source.lookupExpression? expression = some node)
    (typed : ExpressionHasType invocation.source context expression node.type)
    (generated : certificate scope expression lowered)
    (children : ∀ childSize, childSize < budget → LiftsAt bridge context model stages invocation certificate childSize) :
    FlowLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      bridge functions condition context scope mode statements budget := by
  intro size within mapping world actualContext environment canonical actual before store ξ
    contextLocation native environments heaps locals agrees actualTyped reference read unmapped
    initial conditioned admitted finalContext outcome after trace
  obtain ⟨childSize, plain, strict, rfl, rfl, evaluated⟩ :=
    SelectedCompilationStageScopedTerminalInversion.child_of_body unique head trace
  have lifted := children childSize (Nat.lt_of_lt_of_le strict within) generated found typed
    environments heaps locals agrees actualTyped initial admitted evaluated
  obtain ⟨stagedSize, staged, reached, stagedTrace, adapted⟩ := lifted.sized
  refine ⟨_, _, reached, (head.trace stagedTrace).sound, ?_⟩
  cases adapted with
  | completed => cases plain with
    | value value => exact .completed (.returned value)
    | fault reason => exact .completed (.fault reason)
  | rejected origin call reason reached => exact .rejected origin call reason _ reached

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageScopedTerminalLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageLexicalTreeLifting
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageLexicalTreeLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedAllocationCompletion
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedPreparedStagedLexicalTree (TypedCertificate)
open CallableIndexedOwnedPreparedStagedBranchingTree (Shape)
open GenericLexicalStatements (Tree)
open TypedLexicalControl (sequence_rename)
universe u

open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post restore_post)
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (bindings : ProtectedStateTransition.Bindings callerProtocol)

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry}
  (definitions : layouts.definitions = (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
  (registered : frame.Registered (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
  (producer : ProtectedStateTransition.OrdinaryAllocation.Producer callerProtocol layouts frame
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions))
  (condition : Location → NativeFrame → Prop)
  (acquire : ∀ location native, condition location native →
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer location native)
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {faults : RecursiveStageMeaning.FaultRep}

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions

open SelectedCompilationStageScopedLiftBounds
open SelectedCompilationStageLiftBounds (LiftsAt)
open CallableIndexedOwnedAdmittedStagedConditionalHeads (BranchPreserves)

include bridge bindings definitions registered producer acquire in
theorem branch_preservation
    (preservation : ∀ context size, PreservesAt bridge context model stages invocation (certificates context) faults size)
    (unique : NodeOccurrencesUnique invocation.source)
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError (.initial compiled.compatible.checked)
      invocation.source (TypedCertificate invocation.source certificates) context scope false statements expected type code)
    (shape : Shape invocation.source false statements)
    (projection : compiled.compatible.checked.catalog.project expected = .ok type)
    {administrative : Core.Context} :
    ∀ size, BranchPreserves (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions condition context scope statements expected type code size := by
  intro size childSize within
  exact CallableIndexedOwnedAdmittedStagedScopedLexicalPreservation.preserves bridge bindings functions definitions
    registered producer condition acquire (fun context n _ => preservation context n) unique tree shape projection within

include bridge bindings definitions registered producer acquire in
theorem lifts {budget : Nat}
    (children : ∀ context childSize, childSize < budget → LiftsAt bridge context model stages invocation (certificates context) childSize)
    (preservation : ∀ context size, PreservesAt bridge context model stages invocation (certificates context) faults size)
    (unique : NodeOccurrencesUnique invocation.source)
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {mode : Bool} {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError (.initial compiled.compatible.checked)
      invocation.source (TypedCertificate invocation.source certificates) context scope mode statements expected type code)
    (shape : Shape invocation.source mode statements)
    (projection : compiled.compatible.checked.catalog.project expected = .ok type)
    {administrative : Core.Context} :
    FlowLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      bridge functions condition context scope mode statements budget := by
  induction tree generalizing administrative with
  | nil allowed => exact SelectedCompilationStageScopedTerminalLifting.nil bridge functions condition
  | returnUnit rest found form => exact SelectedCompilationStageScopedTerminalLifting.return_unit bridge functions condition unique found form
  | returnValue rest found form expressionFound valueType child =>
    obtain ⟨typedNode, typedFound, typed, certified⟩ := child
    have same := Option.some.inj (expressionFound.symm.trans typedFound)
    cases same
    intro size within
    exact SelectedCompilationStageScopedTerminalLifting.terminal bridge functions condition unique
      (.returning rest (lookupStatement?_sound found) form) expressionFound typed certified (children _) within
  | tail found form expressionFound valueType child =>
    obtain ⟨typedNode, typedFound, typed, certified⟩ := child
    have same := Option.some.inj (expressionFound.symm.trans typedFound)
    cases same
    intro size within
    exact SelectedCompilationStageScopedTerminalLifting.terminal bridge functions condition unique
      (.tail (lookupStatement?_sound found) form) expressionFound typed certified (children _) within
  | uninitialized found form mono extended ordinary projected allocation annotation same tail ih =>
    exact SelectedCompilationStageLexicalLifting.absent bridge functions definitions registered producer condition acquire
      unique found form mono extended ordinary projected allocation annotation same (ih (shape.tail_of_let found form) projection)
  | initialized found form mono extended ordinary initialFound sourceType child allocation annotation same remaining ih =>
    obtain ⟨typedNode, typedFound, typed, certified⟩ := child
    have nodeEq := Option.some.inj (initialFound.symm.trans typedFound)
    cases nodeEq
    intro size within
    exact SelectedCompilationStageLexicalLifting.initialized bridge functions definitions registered producer condition acquire
      unique found form mono extended ordinary initialFound sourceType typed certified allocation annotation same
      (children _) (preservation _) (ih (shape.tail_of_let found form) projection) within
  | discard found form guard expressionFound child remaining ih =>
    obtain ⟨continuing, tailShape⟩ := shape.discard_tail found form guard
    obtain ⟨typedNode, typedFound, typed, certified⟩ := child
    have same := Option.some.inj (expressionFound.symm.trans typedFound)
    cases same
    intro size within
    exact SelectedCompilationStageDiscardLifting.lifts bridge functions condition unique found form continuing
      expressionFound typed certified (children _) (preservation _) (ih tailShape projection) within
  | block found form inner remaining innerIH remainingIH =>
    obtain ⟨innerShape, restShape⟩ := shape.block_children found form
    exact SelectedCompilationStageBlockLifting.lifts bridge functions condition unique found form
      (innerIH innerShape projection)
      (branch_preservation bridge bindings functions definitions registered producer condition acquire preservation unique inner innerShape projection)
      (.inl (remainingIH restShape projection))
  | @ifThen context scope mode id node test testNode left right rest expected type testCode leftCode rightCode body found form conditionFound conditionType conditionTree thenTree elseTree remaining thenIH elseIH remainingIH =>
    obtain ⟨leftShape, rightShape, restShape⟩ := shape.branches found form
    obtain ⟨typedNode, typedFound, typed, certified⟩ := conditionTree
    have same := Option.some.inj (conditionFound.symm.trans typedFound)
    cases same
    apply SelectedCompilationStageConditionalLifting.lifts (expected := expected) (type := type)
      (branchCode := fun truth => if truth then leftCode else rightCode) bridge functions condition unique found form
      conditionFound typed certified (children _) (preservation _)
    · intro truth; cases truth
      · exact elseIH rightShape projection
      · exact thenIH leftShape projection
    · intro truth; cases truth
      · exact branch_preservation bridge bindings functions definitions registered producer condition acquire preservation unique elseTree rightShape projection
      · exact branch_preservation bridge bindings functions definitions registered producer condition acquire preservation unique thenTree leftShape projection
    · exact .inl (remainingIH restShape projection)
  | terminalBlock exactUnique found form inner stops issued ih =>
    obtain ⟨innerShape, _restShape⟩ := shape.block_children found form
    exact SelectedCompilationStageBlockLifting.lifts bridge functions condition unique found form
      (ih innerShape projection)
      (branch_preservation bridge bindings functions definitions registered producer condition acquire preservation unique inner innerShape projection)
      (.inr stops)
  | @terminalIf context scope mode id node test testNode left right rest expected type testCode leftCode rightCode suffix exactUnique found form conditionFound conditionType conditionTree thenTree elseTree thenStops elseStops issued thenIH elseIH =>
    obtain ⟨leftShape, rightShape, _restShape⟩ := shape.branches found form
    obtain ⟨typedNode, typedFound, typed, certified⟩ := conditionTree
    have same := Option.some.inj (conditionFound.symm.trans typedFound)
    cases same
    apply SelectedCompilationStageConditionalLifting.lifts (expected := expected) (type := type)
      (branchCode := fun truth => if truth then leftCode else rightCode) bridge functions condition unique found form
      conditionFound typed certified (children _) (preservation _)
    · intro truth; cases truth
      · exact elseIH rightShape projection
      · exact thenIH leftShape projection
    · intro truth; cases truth
      · exact branch_preservation bridge bindings functions definitions registered producer condition acquire preservation unique elseTree rightShape projection
      · exact branch_preservation bridge bindings functions definitions registered producer condition acquire preservation unique thenTree leftShape projection
    · exact .inr ⟨thenStops, elseStops⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageLexicalTreeLifting
end
