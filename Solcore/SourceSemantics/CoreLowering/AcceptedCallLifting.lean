import Solcore.SourceSemantics.CoreLowering.AcceptedShapes
import Solcore.SourceSemantics.CoreLowering.AcceptedNestedCalls
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.SourceExecutionSize
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.ElementTargetLifting

/-!
# Accepted bodies: lifting call-containing Source traces

Original Source executions of call-containing bodies are staged executions.
The lifting of `CellAwareInvocationAcceptedStatementLifting` runs over sized
derivations, and a direct call's callee body, whose derivation is smaller than
the call's, is lifted by one strong induction on the size across bodies. Their
fault executions are staged fault executions with the same reason, for every
reason the staged traces express.

Main declarations:
- `CellAwareInvocationAcceptedSizedLifting.statements`, the sized lifting of a
  supported statement list given the lifting of its expressions below the size;
- `CellAwareInvocationAcceptedCallLifting.nested_value` and
  `CellAwareInvocationAcceptedCallLifting.nested_roots`, the value execution of
  every nested site;
- `CellAwareInvocationAcceptedCallLifting.bodies` and
  `CellAwareInvocationAcceptedCallLifting.body`, the induction across bodies and
  the staged trace of a call-containing body, given the static receipts of the
  admitted callees (`Callees`);
- `CellAwareInvocationAcceptedFaultLifting.nested_fault`,
  `CellAwareInvocationAcceptedFaultLifting.statements_fault`,
  `CellAwareInvocationAcceptedFaultLifting.bodies_fault` and
  `CellAwareInvocationAcceptedFaultLifting.body_fault`, the same for fault
  executions with an `Expressible` reason, given that the direct calls have
  plain callees (`CalleesPlain`).
-/

section
/-! Sized original Source executions of supported statement lists are staged
executions, given the lifting of their expressions below the size. This is
`CellAwareInvocationAcceptedStatementLifting` over the sized derivations of
`SourceExecutionSize`: every child derivation has a smaller size than its
statement, so a child lifting below the size of a list is enough to lift the
list. Every control outcome is carried unchanged, with the context, environment
and heap of the original execution. Fault executions are lifted by
`CellAwareInvocationAcceptedFaultLifting`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedSizedLifting
open Core Frontend SourceInference
open CellAwareInvocationAcceptedBodyShape (Shape)
open CellAwareInvocationAcceptedStatementLifting (control)

/-- The sized ordinary statement-list judgment of each compiler mode. -/
def Original (program : Program) (size : Nat) : Bool → SourceSemantics.Context → Dynamic.EvidenceEnvironment →
    TypedSource → Dynamic.Environment → Dynamic.Heap → List StatementId → SourceSemantics.Context →
    Dynamic.ControlOutcome → Dynamic.Heap → Prop
  | true => SourceExecutionSize.FunctionStatementsExecute program size
  | false => SourceExecutionSize.StatementsExecute program size

/-- The staged lifting of the value executions of the expressions that `child`
admits, below a size. -/
def ChildLifts (program : Program) (registry : Staging.Recursive.Registry) (scope : Staging.Recursive.Scope)
    (child : ExpressionId → Prop) (bound : Nat) : Prop :=
  ∀ {id : ExpressionId}, child id → ∀ {size : Nat} {context : SourceSemantics.Context}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {value : Dynamic.Value}, size < bound →
    SourceExecutionSize.ExpressionEvaluates program size context scope.evidence scope.source environment before id
      value after →
    Staging.Recursive.Expression program registry scope context environment before id (.value value) after

theorem ChildLifts.mono {program : Program} {registry : Staging.Recursive.Registry} {scope : Staging.Recursive.Scope}
    {child : ExpressionId → Prop} {smaller larger : Nat} (lifts : ChildLifts program registry scope child larger)
    (le : smaller ≤ larger) : ChildLifts program registry scope child smaller := by
  intro _ admitted _ _ _ _ _ _ less trace
  exact lifts admitted (Nat.lt_of_lt_of_le less le) trace

section Inversion
variable {program : Program} {source : TypedSource} {context finalContext : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
  {id : StatementId} {node : StatementNode} {outcome : Dynamic.ControlOutcome} {size : Nat}

private theorem same_node (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    {other : StatementNode} (contains : ContainsStatement source id other) : other = node :=
  Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)

private theorem below_one {first : Nat} : first < SourceExecutionSize.stepSize [first] :=
  SourceExecutionSize.child_lt_stepSize (by simp)

private theorem below_left {first second : Nat} : first < SourceExecutionSize.stepSize [first, second] :=
  SourceExecutionSize.child_lt_stepSize (by simp)

private theorem below_right {first second : Nat} : second < SourceExecutionSize.stepSize [first, second] :=
  SourceExecutionSize.child_lt_stepSize (by simp)

private theorem nil_below {first : Nat} (positive : 0 < first) :
    SourceExecutionSize.stepSize [] < SourceExecutionSize.stepSize [first] := by
  simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil]
  omega

private theorem returned_inv (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    {expression : ExpressionId} (form : node.form = .returnStmt (some expression))
    (head : SourceExecutionSize.StatementExecutes program size context evidence source environment before id
      finalContext outcome after) :
    ∃ child value, child < size ∧
      SourceExecutionSize.ExpressionEvaluates program child context evidence source environment before expression
        value after ∧
      finalContext = context ∧ outcome = .returned value := by
  cases head with
  | returnValue contains formEq evaluate =>
    obtain rfl := same_node unique found contains
    rw [form] at formEq
    cases formEq
    exact ⟨_, _, below_one, evaluate, rfl, rfl⟩
  | _ =>
    exfalso
    obtain rfl := same_node unique found (by assumption)
    simp_all

private theorem return_unit_inv (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (form : node.form = .returnStmt none)
    (head : SourceExecutionSize.StatementExecutes program size context evidence source environment before id
      finalContext outcome after) :
    finalContext = context ∧ outcome = .returned .unit ∧ after = before := by
  cases head with
  | returnUnit => exact ⟨rfl, rfl, rfl⟩
  | _ =>
    exfalso
    obtain rfl := same_node unique found (by assumption)
    simp_all

private theorem declared_inv (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    {binder : TypedBinder} {expression : ExpressionId} (form : node.form = .letDecl binder (some expression))
    (monomorphic : binder.scheme.quantified = [])
    (head : SourceExecutionSize.StatementExecutes program size context evidence source environment before id
      finalContext outcome after) :
    ∃ child value middle location, child < size ∧
      SourceExecutionSize.ExpressionEvaluates program child context evidence source environment before expression
        value middle ∧
      BinderExtends source.owner context binder finalContext ∧
      Dynamic.Heap.Allocates middle binder.scheme.body (some value) location after ∧
      outcome = .fallthrough ((binder.id, location) :: environment) := by
  cases head with
  | letInitialized contains formEq evaluate _ extension allocate =>
    obtain rfl := same_node unique found contains
    rw [form] at formEq
    cases formEq
    exact ⟨_, _, _, _, below_one, evaluate, extension, allocate, rfl⟩
  | letInitializedGeneralized contains formEq _ _ polymorphic _ _ =>
    obtain rfl := same_node unique found contains
    rw [form] at formEq
    cases formEq
    exact absurd monomorphic polymorphic
  | _ =>
    exfalso
    obtain rfl := same_node unique found (by assumption)
    simp_all

private theorem uninitialized_inv (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) {binder : TypedBinder} (form : node.form = .letDecl binder none)
    (head : SourceExecutionSize.StatementExecutes program size context evidence source environment before id
      finalContext outcome after) :
    ∃ location, BinderExtends source.owner context binder finalContext ∧
      Dynamic.Heap.Allocates before binder.scheme.body none location after ∧
      outcome = .fallthrough ((binder.id, location) :: environment) := by
  cases head with
  | letUninitialized contains formEq _ extension allocate =>
    obtain rfl := same_node unique found contains
    rw [form] at formEq
    cases formEq
    exact ⟨_, extension, allocate, rfl⟩
  | _ =>
    exfalso
    obtain rfl := same_node unique found (by assumption)
    simp_all

private theorem assigned_inv (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {expression : ExpressionId}
    (form : node.form = .assignValue assignment operator expression)
    (head : SourceExecutionSize.StatementExecutes program size context evidence source environment before id
      finalContext outcome after) :
    ∃ child updatedRoot, child < size ∧
      SourceExecutionSize.SourcePlaceAssignment program child context evidence source
        (Dynamic.CompoundAssignmentApplies assignment.target.type operator) environment before assignment.target
        expression updatedRoot after ∧
      finalContext = context ∧ outcome = .fallthrough environment := by
  cases head with
  | assignValue contains formEq executes =>
    obtain rfl := same_node unique found contains
    rw [form] at formEq
    cases formEq
    exact ⟨_, _, below_one, executes, rfl, rfl⟩
  | _ =>
    exfalso
    obtain rfl := same_node unique found (by assumption)
    simp_all

private theorem bitNotted_inv (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    {assignment : AssignmentResolution} (form : node.form = .assignBitNot assignment)
    (head : SourceExecutionSize.StatementExecutes program size context evidence source environment before id
      finalContext outcome after) :
    ∃ child updatedRoot, child < size ∧
      SourceExecutionSize.SourcePlaceSnapshotUpdate program child context evidence source
        (Dynamic.BitNotAssignmentApplies assignment.target.type) environment before assignment.target updatedRoot after ∧
      finalContext = context ∧ outcome = .fallthrough environment := by
  cases head with
  | assignBitNot contains formEq executes =>
    obtain rfl := same_node unique found contains
    rw [form] at formEq
    cases formEq
    exact ⟨_, _, below_one, executes, rfl, rfl⟩
  | _ =>
    exfalso
    obtain rfl := same_node unique found (by assumption)
    simp_all

private theorem discarded_inv (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    {expression : ExpressionId} (form : node.form = .expression expression true)
    (head : SourceExecutionSize.StatementExecutes program size context evidence source environment before id
      finalContext outcome after) :
    ∃ child value, child < size ∧
      SourceExecutionSize.ExpressionEvaluates program child context evidence source environment before expression
        value after ∧
      finalContext = context ∧ outcome = .fallthrough environment := by
  cases head with
  | expression contains formEq evaluate =>
    obtain rfl := same_node unique found contains
    rw [form] at formEq
    cases formEq
    exact ⟨_, _, below_one, evaluate, rfl, rfl⟩
  | _ =>
    exfalso
    obtain rfl := same_node unique found (by assumption)
    simp_all

private theorem block_inv (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    {statements : List StatementId} (form : node.form = .block statements)
    (head : SourceExecutionSize.StatementExecutes program size context evidence source environment before id
      finalContext outcome after) :
    ∃ child innerContext inner, child < size ∧
      SourceExecutionSize.StatementsExecute program child context evidence source environment before statements
        innerContext inner after ∧
      finalContext = context ∧ outcome = Dynamic.restoreControl environment inner := by
  cases head with
  | block contains formEq executes =>
    obtain rfl := same_node unique found contains
    rw [form] at formEq
    cases formEq
    exact ⟨_, _, _, below_one, executes, rfl, rfl⟩
  | _ =>
    exfalso
    obtain rfl := same_node unique found (by assumption)
    simp_all

private theorem conditional_inv (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) {condition : ExpressionId} {thenBody : List StatementId}
    {elseBody : Option (List StatementId)} (form : node.form = .ifThen condition thenBody elseBody)
    (head : SourceExecutionSize.StatementExecutes program size context evidence source environment before id
      finalContext outcome after) :
    finalContext = context ∧ ∃ test inner truth middle innerContext innerOutcome, test < size ∧ inner < size ∧
      SourceExecutionSize.ExpressionEvaluates program test context evidence source environment before condition
        (.bool truth) middle ∧
      SourceExecutionSize.StatementsExecute program inner context evidence source environment middle
        (if truth then thenBody else elseBody.getD []) innerContext innerOutcome after ∧
      outcome = Dynamic.restoreControl environment innerOutcome := by
  cases head with
  | ifTrue contains formEq test executes =>
    obtain rfl := same_node unique found contains
    rw [form] at formEq
    cases formEq
    exact ⟨rfl, _, _, true, _, _, _, below_left, below_right, test, executes, rfl⟩
  | ifFalseWithoutElse contains formEq test =>
    obtain rfl := same_node unique found contains
    rw [form] at formEq
    cases formEq
    refine ⟨rfl, _, SourceExecutionSize.stepSize [], false, _, _, _, below_one, ?_, test, .nil, rfl⟩
    have positive := test.positive
    simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at positive ⊢
    omega
  | ifFalseWithElse contains formEq test executes =>
    obtain rfl := same_node unique found contains
    rw [form] at formEq
    cases formEq
    exact ⟨rfl, _, _, false, _, _, _, below_left, below_right, test, executes, rfl⟩
  | _ =>
    exfalso
    obtain rfl := same_node unique found (by assumption)
    simp_all

private theorem break_inv (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (form : node.form = .breakStmt)
    (head : SourceExecutionSize.StatementExecutes program size context evidence source environment before id
      finalContext outcome after) :
    finalContext = context ∧ outcome = .breaking environment ∧ after = before := by
  cases head with
  | breakStmt => exact ⟨rfl, rfl, rfl⟩
  | _ =>
    exfalso
    obtain rfl := same_node unique found (by assumption)
    simp_all

private theorem continue_inv (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (form : node.form = .continueStmt)
    (head : SourceExecutionSize.StatementExecutes program size context evidence source environment before id
      finalContext outcome after) :
    finalContext = context ∧ outcome = .continuing environment ∧ after = before := by
  cases head with
  | continueStmt => exact ⟨rfl, rfl, rfl⟩
  | _ =>
    exfalso
    obtain rfl := same_node unique found (by assumption)
    simp_all

private theorem while_inv (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    {condition : ExpressionId} {body : List StatementId} (form : node.form = .whileLoop condition body)
    (head : SourceExecutionSize.StatementExecutes program size context evidence source environment before id
      finalContext outcome after) :
    ∃ child loopContext inner, child < size ∧
      SourceExecutionSize.WhileExecutes program child context evidence source environment before condition body
        loopContext inner after ∧
      finalContext = context ∧ outcome = Dynamic.restoreControl environment inner := by
  cases head with
  | whileLoop contains formEq iterate =>
    obtain rfl := same_node unique found contains
    rw [form] at formEq
    cases formEq
    exact ⟨_, _, _, below_one, iterate, rfl, rfl⟩
  | _ =>
    exfalso
    obtain rfl := same_node unique found (by assumption)
    simp_all

private theorem for_inv (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    {initializer : List ForItemForm} {condition : ExpressionId} {post : List ForItemForm} {body : List StatementId}
    (form : node.form = .forLoop initializer condition post body)
    (head : SourceExecutionSize.StatementExecutes program size context evidence source environment before id
      finalContext outcome after) :
    ∃ first second loopContext loopEnvironment initialized loopFinalContext inner, first < size ∧ second < size ∧
      SourceExecutionSize.ForItemsExecute program first context evidence source environment before initializer
        loopContext loopEnvironment initialized ∧
      SourceExecutionSize.ForLoopExecutes program second loopContext evidence source loopEnvironment initialized
        condition post body loopFinalContext inner after ∧
      finalContext = context ∧ outcome = Dynamic.restoreControl environment inner := by
  cases head with
  | forLoop contains formEq initial iterate =>
    obtain rfl := same_node unique found contains
    rw [form] at formEq
    cases formEq
    exact ⟨_, _, _, _, _, _, _, below_left, below_right, initial, iterate, rfl, rfl⟩
  | _ =>
    exfalso
    obtain rfl := same_node unique found (by assumption)
    simp_all
end Inversion

variable {program : Program} {registry : Staging.Recursive.Registry} {scope : Staging.Recursive.Scope}
  {expected : TypeSystem.Ty}

/-- A sized Source match whose scrutinee `child` admits and whose selected body lifts within the bound is the
staged match at its entry context. The outcome is the selected body's, restored to the entry bindings; without
a selected body it falls through. -/
private theorem match_lift {child : ExpressionId → Prop} {bound : Nat} (unique : NodeOccurrencesUnique scope.source)
    (lift : ChildLifts program registry scope child bound) {id : StatementId} {node : StatementNode}
    (found : scope.source.lookupStatement? id = some node) {resolution : MatchResolution}
    (form : node.form = .matchWith resolution) (scrutinee : child resolution.scrutinee)
    (body : ∀ {statements : List StatementId}, ((∃ arm ∈ resolution.cases, arm.body = statements) ∨
        resolution.defaultBody = some statements) →
      ∀ {size : Nat} {context environment before innerContext inner after}, size ≤ bound →
      SourceExecutionSize.StatementsExecute program size context scope.evidence scope.source environment before
        statements innerContext inner after →
      Staging.Recursive.StatementsIn program registry false scope context environment before statements
        innerContext (control inner) after)
    {size : Nat} {context finalContext : SourceSemantics.Context} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {outcome : Dynamic.ControlOutcome} (within : size ≤ bound)
    (head : SourceExecutionSize.StatementExecutes program size context scope.evidence scope.source environment
      before id finalContext outcome after) :
    finalContext = context ∧ ∃ inner, outcome = Dynamic.restoreControl environment inner ∧
      Staging.Recursive.Match program registry scope context environment before resolution
        ((control inner).restore environment) after := by
  cases head with
  | matchArm contains formEq scrutineeContains evaluate allocate select bindersEq valuesEq extended allocated
      executes =>
    obtain rfl := same_node unique found contains
    rw [form] at formEq
    cases formEq
    subst bindersEq valuesEq
    obtain ⟨arm, member, same⟩ := (CellAwareInvocationAcceptedStatementLifting.selected_body select).1 _ _ rfl
    exact ⟨rfl, _, rfl, .arm scrutineeContains (lift scrutinee (Nat.lt_of_lt_of_le below_left within) evaluate)
      allocate select extended allocated
      (body (.inl ⟨arm, member, same⟩) (Nat.le_of_lt (Nat.lt_of_lt_of_le below_right within)) executes)⟩
  | matchDefault contains formEq scrutineeContains evaluate allocate select executes =>
    obtain rfl := same_node unique found contains
    rw [form] at formEq
    cases formEq
    exact ⟨rfl, _, rfl, .default scrutineeContains (lift scrutinee (Nat.lt_of_lt_of_le below_left within) evaluate)
      allocate select (body (.inr ((CellAwareInvocationAcceptedStatementLifting.selected_body select).2 _ rfl))
        (Nat.le_of_lt (Nat.lt_of_lt_of_le below_right within)) executes)⟩
  | matchNoBranch contains formEq scrutineeContains evaluate allocate select =>
    obtain rfl := same_node unique found contains
    rw [form] at formEq
    cases formEq
    exact ⟨rfl, .fallthrough environment, rfl, .noBranch scrutineeContains
      (lift scrutinee (Nat.lt_of_lt_of_le below_one within) evaluate) allocate select⟩
  | _ =>
    exfalso
    clear lift body
    obtain rfl := same_node unique found (by assumption)
    simp_all

/-- One statement followed by the rest of its list, over sized derivations. A
falling-through head runs the rest; a terminal head ends the list. -/
private theorem sequence {mode : Bool} {id : StatementId} {rest : List StatementId} {node : StatementNode}
    {size : Nat} (unique : NodeOccurrencesUnique scope.source)
    (found : scope.source.lookupStatement? id = some node)
    (notTail : ∀ expression, node.form ≠ .expression expression false)
    (step : ∀ {context environment before middleContext nextEnvironment middle finalContext outcome after}
        {headSize tailSize : Nat}, headSize < size → tailSize < size →
      SourceExecutionSize.StatementExecutes program headSize context scope.evidence scope.source environment before id
        middleContext (.fallthrough nextEnvironment) middle →
      Original program tailSize mode middleContext scope.evidence scope.source nextEnvironment middle rest finalContext
        outcome after →
      Staging.Recursive.StatementsIn program registry mode scope context environment before (id :: rest)
        finalContext (control outcome) after)
    (stop : ∀ {context environment before finalContext outcome after} {headSize : Nat}, headSize < size →
      SourceExecutionSize.StatementExecutes program headSize context scope.evidence scope.source environment before id
        finalContext outcome after →
      Dynamic.TerminalControl outcome →
      Staging.Recursive.StatementsIn program registry mode scope context environment before (id :: rest)
        finalContext (control outcome) after) :
    ∀ {context environment before finalContext outcome after},
      Original program size mode context scope.evidence scope.source environment before (id :: rest) finalContext
        outcome after →
      Staging.Recursive.StatementsIn program registry mode scope context environment before (id :: rest)
        finalContext (control outcome) after := by
  intro context environment before finalContext outcome after original
  cases mode with
  | false =>
    unfold Original at original
    cases original with
    | cons head next => exact step below_left below_right head next
    | terminal head terminal => exact stop below_one head terminal
  | true =>
    unfold Original at original
    cases original with
    | tailExpression contains form _ =>
      obtain rfl := same_node unique found contains
      exact absurd form (notTail _)
    | singleton _ _ head =>
      have nilBelow := nil_below head.positive
      cases outcome with
      | fallthrough nextEnvironment => exact step below_one nilBelow head .nil
      | returned value => exact stop below_one head (.returned value)
      | breaking environment => exact stop below_one head (.breaking environment)
      | continuing environment => exact stop below_one head (.continuing environment)
      | fault reason => exact stop below_one head (.fault reason)
    | cons head next => exact step below_left below_right head next
    | terminal head terminal => exact stop below_one head terminal

/-- The sized Source evaluation of a path of mapping indices whose keys `child`
admits is the staged evaluation of its keys, in order, given the lifting of
`child` below the size. -/
private theorem projections_values {child : ExpressionId → Prop} {bound : Nat}
    (lift : ChildLifts program registry scope child bound) {context : SourceSemantics.Context}
    {environment : Dynamic.Environment} :
    ∀ {projections : List PlaceProjection},
    (∀ projection ∈ projections, ∃ key, projection = .index key ∧ child key) →
    ∀ {size : Nat} {before after : Dynamic.Heap} {evaluated : List Dynamic.EvaluatedProjection}, size ≤ bound →
      SourceExecutionSize.SourceProjectionsEvaluate program size context scope.evidence scope.source environment
        before projections evaluated after →
      ∃ values, Staging.Recursive.Expressions program registry scope context environment before
          (Staging.Recursive.ProjectedTarget.keys projections) (.values values) after ∧
        Staging.Recursive.ProjectedTarget.Values projections values evaluated := by
  intro projections
  induction projections with
  | nil =>
    intro _ size before after evaluated _ evaluate
    cases evaluate
    exact ⟨[], .nil, .nil⟩
  | cons projection rest ih =>
    intro keys size before after evaluated within evaluate
    obtain ⟨key, rfl, admitted⟩ := keys projection List.mem_cons_self
    cases evaluate with
    | index head tail =>
      simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at within
      obtain ⟨values, staged, ordered⟩ :=
        ih (fun other member => keys other (List.mem_cons_of_mem _ member)) (by omega) tail
      exact ⟨_ :: values, .cons (lift admitted (by omega) head) staged, .index ordered⟩

/-- The sized Source resolution of a place through mapping indices whose keys
`child` admits is the staged evaluation of its keys followed by its staged
snapshot, given the lifting of `child` below the size. -/
private theorem projected_target {child : ExpressionId → Prop} {bound : Nat}
    (lift : ChildLifts program registry scope child bound) {context : SourceSemantics.Context}
    {environment : Dynamic.Environment} {place : PlaceResolution}
    (keys : ∀ projection ∈ place.projections, ∃ key, projection = .index key ∧ child key)
    {size : Nat} {before after : Dynamic.Heap} {target : Dynamic.ResolvedPlace} (within : size ≤ bound)
    (resolve : SourceExecutionSize.SourcePlaceResolves program size context scope.evidence scope.source environment
      before place target after) :
    ∃ values, Staging.Recursive.Expressions program registry scope context environment before
        (Staging.Recursive.ProjectedTarget.keys place.projections) (.values values) after ∧
      Staging.Recursive.ProjectedTarget.Snapshot environment before after place values target := by
  cases resolve with
  | intro lookup initialRead evaluate currentRead initialValue selection =>
    simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at within
    obtain ⟨values, staged, ordered⟩ := projections_values lift keys (by omega) evaluate
    exact ⟨values, staged, .intro lookup initialRead ordered currentRead initialValue selection⟩
  | element projectionsEq => exact absurd projectionsEq (CellAwareInvocationAcceptedBodyShape.indices_no_element keys)

/-- The sized Source iterations of a `while` loop whose condition `child`
admits and whose body lifts within the bound are the staged iterations, with
the same outcome and heap. The loop falls through at its own bindings or
returns. -/
private theorem while_lift {child : ExpressionId → Prop} {bound : Nat}
    (lift : ChildLifts program registry scope child bound) {condition : ExpressionId} {body : List StatementId}
    (test : child condition)
    (inner : ∀ {size : Nat} {context environment before innerContext outcome after}, size ≤ bound →
      SourceExecutionSize.StatementsExecute program size context scope.evidence scope.source environment before body
        innerContext outcome after →
      Staging.Recursive.StatementsIn program registry false scope context environment before body innerContext
        (control outcome) after) :
    ∀ {size : Nat} {context : SourceSemantics.Context} {environment : Dynamic.Environment}
      {before after : Dynamic.Heap} {loopContext : SourceSemantics.Context} {outcome : Dynamic.ControlOutcome},
      size ≤ bound →
      SourceExecutionSize.WhileExecutes program size context scope.evidence scope.source environment before condition
        body loopContext outcome after →
      Staging.Recursive.While program registry scope context environment before condition body (control outcome)
          after ∧
        (outcome = .fallthrough environment ∨ ∃ value, outcome = .returned value) := by
  intro size
  induction size using Nat.strongRecOn with
  | ind size ih =>
    intro context environment before after loopContext outcome within loop
    cases loop with
    | done evaluate => exact ⟨.done (lift test (Nat.lt_of_lt_of_le below_one within) evaluate), .inl rfl⟩
    | nextFallthrough evaluate executes next =>
      have below := within
      simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
      obtain ⟨staged, ended⟩ := ih _ (SourceExecutionSize.child_lt_stepSize (by simp)) (by omega) next
      exact ⟨.next (lift test (by omega) evaluate) (inner (by omega) executes) staged, ended⟩
    | nextContinue evaluate executes next =>
      have below := within
      simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
      obtain ⟨staged, ended⟩ := ih _ (SourceExecutionSize.child_lt_stepSize (by simp)) (by omega) next
      exact ⟨.continueNext (lift test (by omega) evaluate) (inner (by omega) executes) staged, ended⟩
    | breaks evaluate executes =>
      exact ⟨.breakFromBody (lift test (Nat.lt_of_lt_of_le below_left within) evaluate)
        (inner (Nat.le_of_lt (Nat.lt_of_lt_of_le below_right within)) executes), .inl rfl⟩
    | returns evaluate executes =>
      exact ⟨.returned (lift test (Nat.lt_of_lt_of_le below_left within) evaluate)
        (inner (Nat.le_of_lt (Nat.lt_of_lt_of_le below_right within)) executes), .inr ⟨_, rfl⟩⟩

/-- The sized Source execution of a supported header vector whose expressions
`child` admits is the staged execution of the vector, with the same context,
bindings and heap, given the lifting of `child` within the bound. The vector
keeps the signatures of its context. -/
private theorem items_lift {child : ExpressionId → Prop} {bound : Nat}
    (lift : ChildLifts program registry scope child bound) {items : List ForItemForm}
    (shape : CellAwareInvocationAcceptedBodyShape.ItemsShape scope.source child items) :
    ∀ {size : Nat} {context : SourceSemantics.Context} {environment : Dynamic.Environment}
      {before after : Dynamic.Heap} {finalContext : SourceSemantics.Context} {finalEnvironment : Dynamic.Environment},
      size ≤ bound →
      SourceExecutionSize.ForItemsExecute program size context scope.evidence scope.source environment before items
        finalContext finalEnvironment after →
      Staging.Recursive.ForItems program registry scope context environment before items finalContext
          (.done finalEnvironment) after ∧
        finalContext.signatures = context.signatures := by
  induction shape with
  | nil =>
    intro size context environment before after finalContext finalEnvironment _ executes
    cases executes
    exact ⟨.empty, rfl⟩
  | absent monomorphic _ tailIH =>
    intro size context environment before after finalContext finalEnvironment within executes
    cases executes with
    | cons head tail =>
      cases head with
      | letUninitialized _ extension allocate =>
        obtain ⟨staged, signatures⟩ := tailIH (Nat.le_of_lt (Nat.lt_of_lt_of_le below_right within)) tail
        exact ⟨.absent monomorphic extension allocate staged, signatures.trans extension.context_fields.1⟩
  | initialized monomorphic value _ tailIH =>
    intro size context environment before after finalContext finalEnvironment within executes
    cases executes with
    | cons head tail =>
      cases head with
      | letInitialized evaluate _ extension allocate =>
        have below := within
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
        obtain ⟨staged, signatures⟩ := tailIH (by omega) tail
        exact ⟨.initialized monomorphic extension (lift value (by omega) evaluate) allocate staged,
          signatures.trans extension.context_fields.1⟩
      | letInitializedGeneralized _ _ polymorphic => exact absurd monomorphic polymorphic
  | discarded value _ tailIH =>
    intro size context environment before after finalContext finalEnvironment within executes
    cases executes with
    | cons head tail =>
      cases head with
      | expression evaluate =>
        have below := within
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
        obtain ⟨staged, signatures⟩ := tailIH (by omega) tail
        exact ⟨.expression (lift value (by omega) evaluate) staged, signatures⟩
  | assigned assignable value _ tailIH =>
    intro size context environment before after finalContext finalEnvironment within executes
    cases executes with
    | cons head tail =>
      cases head with
      | assignValue executes =>
        cases executes with
        | intro resolve evaluate write =>
          have below := within
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
          obtain ⟨rfl, snapshot⟩ := Staging.Recursive.BareTarget.of_resolves assignable.2.1 resolve.sound
          obtain ⟨staged, signatures⟩ := tailIH (by omega) tail
          exact ⟨.assignment snapshot (lift value (by omega) evaluate) write staged, signatures⟩
  | projectedAssigned assignable keys value _ tailIH =>
    intro size context environment before after finalContext finalEnvironment within executes
    cases executes with
    | cons head tail =>
      cases head with
      | assignValue executes =>
        cases executes with
        | intro resolve evaluate write =>
          have below := within
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
          obtain ⟨values, staged, snapshot⟩ := projected_target lift keys (by omega) resolve
          obtain ⟨remaining, signatures⟩ := tailIH (by omega) tail
          exact ⟨.projectedAssignment assignable.2.1 staged snapshot (lift value (by omega) evaluate) write remaining,
            signatures⟩
  | bitNotted assignable _ tailIH =>
    intro size context environment before after finalContext finalEnvironment within executes
    cases executes with
    | cons head tail =>
      cases head with
      | assignBitNot executes =>
        cases executes with
        | intro resolve write =>
          have below := within
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
          obtain ⟨rfl, snapshot⟩ := Staging.Recursive.BareTarget.of_resolves assignable.2.1 resolve.sound
          obtain ⟨staged, signatures⟩ := tailIH (by omega) tail
          exact ⟨.bitNot snapshot write staged, signatures⟩
  | projectedBitNotted assignable keys _ tailIH =>
    intro size context environment before after finalContext finalEnvironment within executes
    cases executes with
    | cons head tail =>
      cases head with
      | assignBitNot executes =>
        cases executes with
        | intro resolve write =>
          have below := within
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
          obtain ⟨values, staged, snapshot⟩ := projected_target lift keys (by omega) resolve
          obtain ⟨remaining, signatures⟩ := tailIH (by omega) tail
          exact ⟨.projectedBitNot assignable.2.1 staged snapshot write remaining, signatures⟩

/-- The sized Source iterations of a `for` loop whose condition `child` admits,
whose body lifts within the bound and whose post header is supported are the
staged iterations, with the same outcome and heap. The loop falls through at
its own bindings or returns. -/
private theorem for_lift {child : ExpressionId → Prop} {bound : Nat}
    (lift : ChildLifts program registry scope child bound) {condition : ExpressionId} {post : List ForItemForm}
    {body : List StatementId} (test : child condition)
    (inner : ∀ {size : Nat} {context environment before innerContext outcome after}, size ≤ bound →
      SourceExecutionSize.StatementsExecute program size context scope.evidence scope.source environment before body
        innerContext outcome after →
      Staging.Recursive.StatementsIn program registry false scope context environment before body innerContext
        (control outcome) after)
    (postShape : CellAwareInvocationAcceptedBodyShape.ItemsShape scope.source child post) :
    ∀ {size : Nat} {context : SourceSemantics.Context} {environment : Dynamic.Environment}
      {before after : Dynamic.Heap} {loopContext : SourceSemantics.Context} {outcome : Dynamic.ControlOutcome},
      size ≤ bound →
      SourceExecutionSize.ForLoopExecutes program size context scope.evidence scope.source environment before
        condition post body loopContext outcome after →
      Staging.Recursive.ForLoop program registry scope context environment before condition post body
          (control outcome) after ∧
        (outcome = .fallthrough environment ∨ ∃ value, outcome = .returned value) := by
  intro size
  induction size using Nat.strongRecOn with
  | ind size ih =>
    intro context environment before after loopContext outcome within loop
    cases loop with
    | done evaluate =>
      exact ⟨.finished (lift test (Nat.lt_of_lt_of_le below_one within) evaluate), .inl rfl⟩
    | nextFallthrough evaluate executes postExecutes next =>
      have below := within
      simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
      obtain ⟨staged, ended⟩ := ih _ (SourceExecutionSize.child_lt_stepSize (by simp)) (by omega) next
      exact ⟨.iterate (lift test (by omega) evaluate) (inner (by omega) executes)
        (items_lift lift postShape (by omega) postExecutes).1 staged, ended⟩
    | nextContinue evaluate executes postExecutes next =>
      have below := within
      simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
      obtain ⟨staged, ended⟩ := ih _ (SourceExecutionSize.child_lt_stepSize (by simp)) (by omega) next
      exact ⟨.continueIterate (lift test (by omega) evaluate) (inner (by omega) executes)
        (items_lift lift postShape (by omega) postExecutes).1 staged, ended⟩
    | breaks evaluate executes =>
      exact ⟨.forBreakFromBody (lift test (Nat.lt_of_lt_of_le below_left within) evaluate)
        (inner (Nat.le_of_lt (Nat.lt_of_lt_of_le below_right within)) executes), .inl rfl⟩
    | returns evaluate executes =>
      exact ⟨.returnedFromBody (lift test (Nat.lt_of_lt_of_le below_left within) evaluate)
        (inner (Nat.le_of_lt (Nat.lt_of_lt_of_le below_right within)) executes), .inr ⟨_, rfl⟩⟩

/-- A sized ordinary execution of a supported statement list is a staged
execution with the same context, outcome and heap, given the lifting of its
expressions below the size. -/
theorem statements (unique : NodeOccurrencesUnique scope.source) {child : ExpressionId → Prop} {bound : Nat}
    (lift : ChildLifts program registry scope child bound) {mode : Bool} {statements : List StatementId}
    (shape : Shape scope.source expected child mode statements) :
    ∀ {size : Nat} {context : SourceSemantics.Context} {environment : Dynamic.Environment}
      {before after : Dynamic.Heap} {finalContext : SourceSemantics.Context} {outcome : Dynamic.ControlOutcome},
      size ≤ bound →
      Original program size mode context scope.evidence scope.source environment before statements finalContext
        outcome after →
      Staging.Recursive.StatementsIn program registry mode scope context environment before statements finalContext
        (control outcome) after := by
  induction shape with
  | @nil mode _ =>
    intro size context environment before after finalContext outcome _ original
    cases mode <;> unfold Original at original <;> cases original <;> exact .nil
  | returned found form value =>
    intro size context environment before after finalContext outcome within
    apply sequence unique found (fun _ same => by rw [form] at same; cases same)
    · intro context environment before middleContext nextEnvironment middle finalContext outcome after _ _ _ _ head _
      obtain ⟨_, _, _, _, _, impossible⟩ := returned_inv unique found form head
      cases impossible
    · intro context environment before finalContext outcome after headSize below head _
      obtain ⟨_, _, childBelow, evaluate, rfl, rfl⟩ := returned_inv unique found form head
      exact .returnValue (lookupStatement?_sound found) form
        (lift value (by omega) evaluate)
  | returnUnit found form =>
    intro size context environment before after finalContext outcome _
    apply sequence unique found (fun _ same => by rw [form] at same; cases same)
    · intro context environment before middleContext nextEnvironment middle finalContext outcome after _ _ _ _ head _
      obtain ⟨_, impossible, _⟩ := return_unit_inv unique found form head
      cases impossible
    · intro context environment before finalContext outcome after _ _ head _
      obtain ⟨rfl, rfl, rfl⟩ := return_unit_inv unique found form head
      exact .returnUnit (lookupStatement?_sound found) form
  | declared found form monomorphic value _ tailIH =>
    intro size context environment before after finalContext outcome within
    apply sequence unique found (fun _ same => by rw [form] at same; cases same)
    · intro context environment before middleContext nextEnvironment middle finalContext outcome after headSize
        tailSize headBelow tailBelow head next
      obtain ⟨_, _, _, _, childBelow, evaluate, extension, allocate, same⟩ :=
        declared_inv unique found form monomorphic head
      cases same
      exact .letInitialized (lookupStatement?_sound found) form (lift value (by omega) evaluate)
        monomorphic extension allocate (tailIH (by omega) next)
    · intro context environment before finalContext outcome after _ _ head terminal
      obtain ⟨_, _, _, _, _, _, _, _, same⟩ := declared_inv unique found form monomorphic head
      subst same
      cases terminal
  | uninitialized found form monomorphic _ tailIH =>
    intro size context environment before after finalContext outcome within
    apply sequence unique found (fun _ same => by rw [form] at same; cases same)
    · intro context environment before middleContext nextEnvironment middle finalContext outcome after headSize
        tailSize headBelow tailBelow head next
      obtain ⟨_, extension, allocate, same⟩ := uninitialized_inv unique found form head
      cases same
      exact .letUninitialized (lookupStatement?_sound found) form monomorphic extension allocate
        (tailIH (by omega) next)
    · intro context environment before finalContext outcome after _ _ head terminal
      obtain ⟨_, _, _, same⟩ := uninitialized_inv unique found form head
      subst same
      cases terminal
  | assigned found form assignable value _ tailIH =>
    intro size context environment before after finalContext outcome within
    apply sequence unique found (fun _ same => by rw [form] at same; cases same)
    · intro context environment before middleContext nextEnvironment middle finalContext outcome after headSize
        tailSize headBelow tailBelow head next
      obtain ⟨_, _, childBelow, executes, rfl, same⟩ := assigned_inv unique found form head
      cases same
      cases executes with
      | intro resolve evaluate write =>
        obtain ⟨rfl, snapshot⟩ := Staging.Recursive.BareTarget.of_resolves assignable.2.1 resolve.sound
        exact .assignBare (lookupStatement?_sound found) form snapshot
          (lift value (by
            simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at childBelow
            omega) evaluate)
          write (tailIH (by omega) next)
    · intro context environment before finalContext outcome after _ _ head terminal
      obtain ⟨_, _, _, _, _, same⟩ := assigned_inv unique found form head
      subst same
      cases terminal
  | projectedAssigned found form assignable keys value _ tailIH =>
    intro size context environment before after finalContext outcome within
    apply sequence unique found (fun _ same => by rw [form] at same; cases same)
    · intro context environment before middleContext nextEnvironment middle finalContext outcome after headSize
        tailSize headBelow tailBelow head next
      obtain ⟨_, _, childBelow, executes, rfl, same⟩ := assigned_inv unique found form head
      cases same
      cases executes with
      | intro resolve evaluate write =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at childBelow
        obtain ⟨values, staged, snapshot⟩ := projected_target lift keys (by omega) resolve
        exact .assignProjected (lookupStatement?_sound found) form assignable.2.1 staged snapshot
          (lift value (by omega) evaluate) write (tailIH (by omega) next)
    · intro context environment before finalContext outcome after _ _ head terminal
      obtain ⟨_, _, _, _, _, same⟩ := assigned_inv unique found form head
      subst same
      cases terminal
  | bitNotted found form assignable _ tailIH =>
    intro size context environment before after finalContext outcome within
    apply sequence unique found (fun _ same => by rw [form] at same; cases same)
    · intro context environment before middleContext nextEnvironment middle finalContext outcome after headSize
        tailSize headBelow tailBelow head next
      obtain ⟨_, _, _, executes, rfl, same⟩ := bitNotted_inv unique found form head
      cases same
      cases executes with
      | intro resolve write =>
        obtain ⟨rfl, snapshot⟩ := Staging.Recursive.BareTarget.of_resolves assignable.2.1 resolve.sound
        exact .bitNotBare (lookupStatement?_sound found) form snapshot write (tailIH (by omega) next)
    · intro context environment before finalContext outcome after _ _ head terminal
      obtain ⟨_, _, _, _, _, same⟩ := bitNotted_inv unique found form head
      subst same
      cases terminal
  | projectedBitNotted found form assignable keys _ tailIH =>
    intro size context environment before after finalContext outcome within
    apply sequence unique found (fun _ same => by rw [form] at same; cases same)
    · intro context environment before middleContext nextEnvironment middle finalContext outcome after headSize
        tailSize headBelow tailBelow head next
      obtain ⟨_, _, childBelow, executes, rfl, same⟩ := bitNotted_inv unique found form head
      cases same
      cases executes with
      | intro resolve write =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at childBelow
        obtain ⟨values, staged, snapshot⟩ := projected_target lift keys (by omega) resolve
        exact .bitNotProjected (lookupStatement?_sound found) form assignable.2.1 staged snapshot write
          (tailIH (by omega) next)
    · intro context environment before finalContext outcome after _ _ head terminal
      obtain ⟨_, _, _, _, _, same⟩ := bitNotted_inv unique found form head
      subst same
      cases terminal
  | elementAssigned found form _ single index value _ tailIH =>
    intro size context environment before after finalContext outcome within
    apply sequence unique found (fun _ same => by rw [form] at same; cases same)
    · intro context environment before middleContext nextEnvironment middle finalContext outcome after headSize
        tailSize headBelow tailBelow head next
      obtain ⟨_, _, childBelow, executes, rfl, same⟩ := assigned_inv unique found form head
      cases same
      cases executes with
      | intro resolve evaluate write =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at childBelow
        exact .assignElement (lookupStatement?_sound found) form (CellAwareElementTargetLifting.element_place single)
          (CellAwareElementTargetLifting.resolved_sized single (fun below trace => lift index (by omega) trace)
            resolve)
          (lift value (by omega) evaluate) write (tailIH (by omega) next)
    · intro context environment before finalContext outcome after _ _ head terminal
      obtain ⟨_, _, _, _, _, same⟩ := assigned_inv unique found form head
      subst same
      cases terminal
  | elementBitNotted found form _ single index _ tailIH =>
    intro size context environment before after finalContext outcome within
    apply sequence unique found (fun _ same => by rw [form] at same; cases same)
    · intro context environment before middleContext nextEnvironment middle finalContext outcome after headSize
        tailSize headBelow tailBelow head next
      obtain ⟨_, _, childBelow, executes, rfl, same⟩ := bitNotted_inv unique found form head
      cases same
      cases executes with
      | intro resolve write =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at childBelow
        exact .bitNotElement (lookupStatement?_sound found) form (CellAwareElementTargetLifting.element_place single)
          (CellAwareElementTargetLifting.resolved_sized single (fun below trace => lift index (by omega) trace)
            resolve)
          write (tailIH (by omega) next)
    · intro context environment before finalContext outcome after _ _ head terminal
      obtain ⟨_, _, _, _, _, same⟩ := bitNotted_inv unique found form head
      subst same
      cases terminal
  | discarded found form value _ tailIH =>
    intro size context environment before after finalContext outcome within
    apply sequence unique found (fun _ same => by rw [form] at same; cases same)
    · intro context environment before middleContext nextEnvironment middle finalContext outcome after headSize
        tailSize headBelow tailBelow head next
      obtain ⟨_, _, childBelow, evaluate, rfl, same⟩ := discarded_inv unique found form head
      cases same
      exact .discard (lookupStatement?_sound found) form (lift value (by omega) evaluate) (tailIH (by omega) next)
    · intro context environment before finalContext outcome after _ _ head terminal
      obtain ⟨_, _, _, _, _, same⟩ := discarded_inv unique found form head
      subst same
      cases terminal
  | block found form _ _ innerIH tailIH =>
    intro size context environment before after finalContext outcome within
    apply sequence unique found (fun _ same => by rw [form] at same; cases same)
    · intro context environment before middleContext nextEnvironment middle finalContext outcome after headSize
        tailSize headBelow tailBelow head next
      obtain ⟨_, _, inner, innerBelow, executes, rfl, same⟩ := block_inv unique found form head
      cases inner with
      | fallthrough innerEnvironment =>
        cases same
        exact .blockFallthrough (lookupStatement?_sound found) form (innerIH (by omega) executes)
          (tailIH (by omega) next)
      | _ => cases same
    · intro context environment before finalContext outcome after headSize headBelow head terminal
      obtain ⟨_, _, inner, innerBelow, executes, rfl, rfl⟩ := block_inv unique found form head
      have staged := innerIH (by omega) executes
      cases inner with
      | fallthrough => cases terminal
      | returned => exact .blockReturned (lookupStatement?_sound found) form staged
      | breaking => exact .blockBreaking (lookupStatement?_sound found) form staged
      | continuing => exact .blockContinuing (lookupStatement?_sound found) form staged
      | fault => exact .blockFault (lookupStatement?_sound found) form staged
  | @conditional mode id rest node condition thenBody elseBody found form test _ _ _ leftIH rightIH tailIH =>
    intro size context environment before after finalContext outcome within
    have branch : ∀ {truth : Bool} {innerSize : Nat} {context environment before innerContext inner after},
        innerSize ≤ bound →
        SourceExecutionSize.StatementsExecute program innerSize context scope.evidence scope.source environment before
          (if truth then thenBody else elseBody.getD []) innerContext inner after →
        Staging.Recursive.StatementsIn program registry false scope context environment before
          (if truth then thenBody else elseBody.getD []) innerContext (control inner) after := by
      intro truth innerSize context environment before innerContext inner after within executes
      cases truth
      · exact rightIH within executes
      · exact leftIH within executes
    apply sequence unique found (fun _ same => by rw [form] at same; cases same)
    · intro context environment before middleContext nextEnvironment middle finalContext outcome after headSize
        tailSize headBelow tailBelow head next
      obtain ⟨rfl, _, _, truth, _, _, inner, testBelow, innerBelow, evaluate, executes, same⟩ :=
        conditional_inv unique found form head
      cases inner with
      | fallthrough innerEnvironment =>
        cases same
        exact .ifFallthrough (lookupStatement?_sound found) form (lift test (by omega) evaluate)
          (branch (by omega) executes) (tailIH (by omega) next)
      | _ => cases same
    · intro context environment before finalContext outcome after headSize headBelow head terminal
      obtain ⟨rfl, _, _, truth, _, _, inner, testBelow, innerBelow, evaluate, executes, rfl⟩ :=
        conditional_inv unique found form head
      have staged := branch (by omega) executes
      have tested := lift test (by omega) evaluate
      cases inner with
      | fallthrough => cases terminal
      | returned => exact .ifReturned (lookupStatement?_sound found) form tested staged
      | breaking => exact .ifBreaking (lookupStatement?_sound found) form tested staged
      | continuing => exact .ifContinuing (lookupStatement?_sound found) form tested staged
      | fault => exact .ifFault (lookupStatement?_sound found) form tested staged
  | @matched mode id rest node resolution found form scrutinee _ _ _ armsIH fallbackIH tailIH =>
    intro size context environment before after finalContext outcome within
    have body : ∀ {statements : List StatementId}, ((∃ arm ∈ resolution.cases, arm.body = statements) ∨
        resolution.defaultBody = some statements) →
        ∀ {innerSize : Nat} {context environment before innerContext inner after}, innerSize ≤ bound →
        SourceExecutionSize.StatementsExecute program innerSize context scope.evidence scope.source environment
          before statements innerContext inner after →
        Staging.Recursive.StatementsIn program registry false scope context environment before statements
          innerContext (control inner) after := by
      intro statements selected innerSize context environment before innerContext inner after within executes
      rcases selected with ⟨arm, member, rfl⟩ | same
      · exact armsIH arm member within executes
      · rw [same] at fallbackIH
        exact fallbackIH within executes
    apply sequence unique found (fun _ same => by rw [form] at same; cases same)
    · intro context environment before middleContext nextEnvironment middle finalContext outcome after headSize
        tailSize headBelow tailBelow head next
      obtain ⟨rfl, inner, same, staged⟩ := match_lift unique lift found form scrutinee body (by omega) head
      cases inner with
      | fallthrough innerEnvironment =>
        cases same
        exact .matchFallthrough (lookupStatement?_sound found) form staged (tailIH (by omega) next)
      | _ => cases same
    · intro context environment before finalContext outcome after headSize headBelow head terminal
      obtain ⟨rfl, inner, rfl, staged⟩ := match_lift unique lift found form scrutinee body (by omega) head
      cases inner with
      | fallthrough => cases terminal
      | returned => exact .matchReturned (lookupStatement?_sound found) form staged
      | breaking => exact .matchBreaking (lookupStatement?_sound found) form staged
      | continuing => exact .matchContinuing (lookupStatement?_sound found) form staged
      | fault => exact .matchFault (lookupStatement?_sound found) form staged
  | breaking found form =>
    intro size context environment before after finalContext outcome _
    apply sequence unique found (fun _ same => by rw [form] at same; cases same)
    · intro context environment before middleContext nextEnvironment middle finalContext outcome after _ _ _ _ head _
      obtain ⟨_, impossible, _⟩ := break_inv unique found form head
      cases impossible
    · intro context environment before finalContext outcome after _ _ head _
      obtain ⟨rfl, rfl, rfl⟩ := break_inv unique found form head
      exact .breaking (lookupStatement?_sound found) form
  | continuing found form =>
    intro size context environment before after finalContext outcome _
    apply sequence unique found (fun _ same => by rw [form] at same; cases same)
    · intro context environment before middleContext nextEnvironment middle finalContext outcome after _ _ _ _ head _
      obtain ⟨_, impossible, _⟩ := continue_inv unique found form head
      cases impossible
    · intro context environment before finalContext outcome after _ _ head _
      obtain ⟨rfl, rfl, rfl⟩ := continue_inv unique found form head
      exact .continuing (lookupStatement?_sound found) form
  | whileLooped found form test _ _ innerIH tailIH =>
    intro size context environment before after finalContext outcome within
    apply sequence unique found (fun _ same => by rw [form] at same; cases same)
    · intro context environment before middleContext nextEnvironment middle finalContext outcome after headSize
        tailSize headBelow tailBelow head next
      obtain ⟨_, _, loopOutcome, loopBelow, iterate, rfl, same⟩ := while_inv unique found form head
      obtain ⟨loop, ended⟩ := while_lift lift test (fun within executes => innerIH within executes) (by omega)
        iterate
      rcases ended with rfl | ⟨_, rfl⟩
      · cases same
        exact .whileFallthrough (lookupStatement?_sound found) form loop (tailIH (by omega) next)
      · cases same
    · intro context environment before finalContext outcome after headSize headBelow head terminal
      obtain ⟨_, _, loopOutcome, loopBelow, iterate, rfl, rfl⟩ := while_inv unique found form head
      obtain ⟨loop, ended⟩ := while_lift lift test (fun within executes => innerIH within executes) (by omega)
        iterate
      rcases ended with rfl | ⟨_, rfl⟩
      · cases terminal
      · exact .whileReturned (lookupStatement?_sound found) form loop
  | forLooped found form initialItems test _ postItems _ innerIH tailIH =>
    intro size context environment before after finalContext outcome within
    apply sequence unique found (fun _ same => by rw [form] at same; cases same)
    · intro context environment before middleContext nextEnvironment middle finalContext outcome after headSize
        tailSize headBelow tailBelow head next
      obtain ⟨_, _, _, _, _, _, loopOutcome, firstBelow, secondBelow, initialized, iterate, rfl, same⟩ :=
        for_inv unique found form head
      obtain ⟨loop, ended⟩ := for_lift lift test (fun within executes => innerIH within executes) postItems
        (by omega) iterate
      rcases ended with rfl | ⟨_, rfl⟩
      · cases same
        exact .forFallthrough (lookupStatement?_sound found) form (items_lift lift initialItems (by omega) initialized).1
          loop (tailIH (by omega) next)
      · cases same
    · intro context environment before finalContext outcome after headSize headBelow head terminal
      obtain ⟨_, _, _, _, _, _, loopOutcome, firstBelow, secondBelow, initialized, iterate, rfl, rfl⟩ :=
        for_inv unique found form head
      obtain ⟨loop, ended⟩ := for_lift lift test (fun within executes => innerIH within executes) postItems
        (by omega) iterate
      rcases ended with rfl | ⟨_, rfl⟩
      · cases terminal
      · exact .forReturned (lookupStatement?_sound found) form (items_lift lift initialItems (by omega) initialized).1
          loop
  | tail found form _ value =>
    intro size context environment before after finalContext outcome within original
    unfold Original at original
    cases original with
    | tailExpression contains formEq evaluate =>
      obtain rfl := same_node unique found contains
      rw [form] at formEq
      cases formEq
      exact .tail (lookupStatement?_sound found) form (lift value (Nat.lt_of_lt_of_le below_one within) evaluate)
    | singleton contains notTail _ =>
      obtain rfl := same_node unique found contains
      exact absurd form (notTail _)

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedSizedLifting
end

section
/-! Original executions of bodies whose expressions are nested sites are
staged executions. A direct call's original rule runs the callee body, so the
lifting is one strong induction on the size of the original derivation across
bodies: at a call of a given size, the callee body's derivation is smaller, and
its lifting below that size gives the staged global application. A
conversion's and a builtin closure call's original rule applies the builtin as
the staged rule does, a reference to a builtin closure is the staged atomic
value, a mapping index's original rules give the staged index outcome, a
tuple's original rule packs its elements' values as the staged rule does, and
an array form's original rules evaluate its children in the order of the
staged rule and take its step.
Inside one
body, a nested site is lifted by induction on the site, over the sized
derivations of its operands, branches, elements and arguments. The admitted
callees are static inputs (`Callees`): the registry scope of each callee's
global view at the empty dictionary and the shape of its body, whose
expressions are nested sites of its own cache row. Fault executions are lifted
by `CellAwareInvocationAcceptedFaultLifting`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedCallLifting
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (Prepared)
open CellAwareNamedExpressionSyntax (Site)
open CellAwareInvocationAcceptedNestedTrees (Nested)
open CellAwareInvocationAcceptedBodyShape (Shape)
open CellAwareInvocationAcceptedStatementLifting (control)
open CellAwareInvocationAcceptedSizedLifting (ChildLifts)
open CellAwareInvocationAcceptedSourceLifting (expression_value)

section Sites
variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
  {named : SourceCoreGeneralFunctions.Function} {scope : Staging.Recursive.Scope} {id : ExpressionId}

private theorem requirements_of (site : Site prepared named scope.source id)
    {form : ExpressionForm} (same : site.node.form = form)
    (notInteger : ∀ literal resolution, form ≠ .integerLiteral literal resolution) :
    site.node.requirements = [] := by
  have requirements := site.requirements
  split at requirements
  · rename_i literal resolution integer
    exact absurd (same.symm.trans integer) (notInteger literal resolution)
  · exact requirements

private theorem occurrence (site : Site prepared named scope.source id)
    {form : ExpressionForm} (same : site.node.form = form)
    (notInteger : ∀ literal resolution, form ≠ .integerLiteral literal resolution) :
    Staging.Recursive.Occurrence scope id form :=
  ⟨site.node, lookupExpression?_sound site.found, same, requirements_of site same notInteger, site.coercions⟩

end Sites

variable {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
  (program : Program) (registry : Staging.Recursive.Registry) (called : DeclarationInstantiation → Prop)

/-- The static receipts of every admitted callee: the registry scope of the
global view of its body instance at the empty dictionary, the uniqueness of its
nodes, and a supported shape of its body whose expressions are nested sites of
its own cache row. -/
def Callees : Prop :=
  ∀ {instantiation : DeclarationInstantiation} {bodyInstance : Dynamic.BodyInstance} {roots : List StatementId},
    called instantiation → Dynamic.FunctionInstantiates program instantiation bodyInstance →
    Dynamic.StatementRoots bodyInstance.source.roots roots →
    ∃ (child : Staging.Recursive.Scope) (named : SourceCoreGeneralFunctions.Function) (expected : TypeSystem.Ty),
      registry.Closure (Staging.Recursive.globalView bodyInstance [] roots) child ∧
      NodeOccurrencesUnique bodyInstance.source ∧
      Shape bodyInstance.source expected (Nested prepared named bodyInstance.source called) true roots

/-- Every admitted callee's original body derivation below a size is a staged
execution in the registry scope of its global view. -/
def BodiesLift (bound : Nat) : Prop :=
  ∀ {instantiation : DeclarationInstantiation} {bodyInstance : Dynamic.BodyInstance} {roots : List StatementId},
    called instantiation → Dynamic.FunctionInstantiates program instantiation bodyInstance →
    Dynamic.StatementRoots bodyInstance.source.roots roots →
    ∃ child : Staging.Recursive.Scope,
      registry.Closure (Staging.Recursive.globalView bodyInstance [] roots) child ∧
      ∀ {size : Nat} {context : SourceSemantics.Context} {environment : Dynamic.Environment}
        {before after : Dynamic.Heap} {finalContext : SourceSemantics.Context} {outcome : Dynamic.ControlOutcome},
        size < bound →
        SourceExecutionSize.FunctionStatementsExecute program size context [] bodyInstance.source environment before
          roots finalContext outcome after →
        Staging.Recursive.StatementsIn program registry true child context environment before roots finalContext
          (control outcome) after

/-- A direct call without requirements or coercions to a monomorphic
instantiation passes the empty dictionary. -/
theorem evidence_nil {context : SourceSemantics.Context} {caller produced : Dynamic.EvidenceEnvironment}
    (produces : Dynamic.DirectCallProducesEvidence context caller [] [] [] produced) : produced = [] := by
  cases produces with
  | intro coercions requirements produces =>
    rename_i selected contextual signatureRequirements
    have selectedNil : selected = [] := (List.append_eq_nil_iff.mp coercions.symm).1
    have contextualNil : contextual = [] := (List.append_eq_nil_iff.mp coercions.symm).2
    subst selectedNil contextualNil
    have signatureNil : signatureRequirements = [] := by
      simpa [coercionRequirementIds] using requirements.symm
    subst signatureNil
    cases produces
    rfl

variable {program registry called}

private theorem node_unique {scope : Staging.Recursive.Scope} (unique : NodeOccurrencesUnique scope.source)
    {id : ExpressionId} {left right : ExpressionNode} (first : ContainsExpression scope.source id left)
    (second : ContainsExpression scope.source id right) : left = right :=
  Option.some.inj ((lookupExpression?_complete unique first).symm.trans (lookupExpression?_complete unique second))

/-- A sized value execution at a node without coercions that is not a local
read runs the node's form below the same size. -/
private theorem form_below {scope : Staging.Recursive.Scope} (unique : NodeOccurrencesUnique scope.source)
    {id : ExpressionId} {node : ExpressionNode} (found : scope.source.lookupExpression? id = some node)
    (coercions : node.coercions = []) (notLocal : ∀ name binder, node.form ≠ .reference name (.local binder))
    {size : Nat} {context : SourceSemantics.Context} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {value : Dynamic.Value}
    (trace : SourceExecutionSize.ExpressionEvaluates program size context scope.evidence scope.source environment
      before id value after) :
    ∃ formSize, formSize < size ∧ SourceExecutionSize.ExpressionFormEvaluates program formSize context
      scope.evidence scope.source environment before node.form node.requirements [] value after := by
  have contains := lookupExpression?_sound found
  cases trace with
  | intro traceFound form path =>
    cases node_unique unique traceFound contains
    rw [coercions] at path form
    cases path
    exact ⟨_, SourceExecutionSize.child_lt_stepSize (by simp), form⟩
  | generalizedLocal traceFound formEq =>
    cases node_unique unique traceFound contains
    exact absurd formEq (notLocal _ _)

/-- The value executions of nested arguments are staged executions. -/
private theorem arguments_value {scope : Staging.Recursive.Scope} {bound : Nat} :
    ∀ {ids : List ExpressionId},
    (∀ argument ∈ ids, ∀ {size : Nat} {context : SourceSemantics.Context} {environment : Dynamic.Environment}
      {before after : Dynamic.Heap} {value : Dynamic.Value}, size ≤ bound →
      SourceExecutionSize.ExpressionEvaluates program size context scope.evidence scope.source environment before
        argument value after →
      Staging.Recursive.Expression program registry scope context environment before argument (.value value) after) →
    ∀ {size : Nat} {context : SourceSemantics.Context} {environment : Dynamic.Environment}
      {before after : Dynamic.Heap} {values : List Dynamic.Value}, size ≤ bound →
      SourceExecutionSize.ExpressionsEvaluate program size context scope.evidence scope.source environment before ids
        values after →
      Staging.Recursive.Expressions program registry scope context environment before ids (.values values) after := by
  intro ids
  induction ids with
  | nil =>
    intro _ size context environment before after values _ evaluated
    cases evaluated
    exact .nil
  | cons head rest ih =>
    intro lifts size context environment before after values within evaluated
    cases evaluated with
    | cons first tail =>
      exact .cons
        (lifts head List.mem_cons_self (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at within
          omega) first)
        (ih (fun argument member => lifts argument (List.mem_cons_of_mem _ member)) (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at within
          omega) tail)

/-- The value execution of a memref composite's `lidx` is a staged execution,
given those of its array and its index. -/
private theorem reference_value {named : SourceCoreGeneralFunctions.Function} {scope : Staging.Recursive.Scope}
    (unique : NodeOccurrencesUnique scope.source) {bound : Nat} {id reference : ExpressionId}
    (site : CellAwareInvocationAcceptedMemrefSites.MemrefSite prepared named scope.source id reference)
    (first : ∀ {size : Nat} {context : SourceSemantics.Context} {environment : Dynamic.Environment}
      {before after : Dynamic.Heap} {value : Dynamic.Value}, size ≤ bound →
      SourceExecutionSize.ExpressionEvaluates program size context scope.evidence scope.source environment before
        site.base value after →
      Staging.Recursive.Expression program registry scope context environment before site.base (.value value) after)
    (second : ∀ {size : Nat} {context : SourceSemantics.Context} {environment : Dynamic.Environment}
      {before after : Dynamic.Heap} {value : Dynamic.Value}, size ≤ bound →
      SourceExecutionSize.ExpressionEvaluates program size context scope.evidence scope.source environment before
        site.subscript value after →
      Staging.Recursive.Expression program registry scope context environment before site.subscript (.value value)
        after) :
    ∀ {size : Nat} {context : SourceSemantics.Context} {environment : Dynamic.Environment}
      {before after : Dynamic.Heap} {value : Dynamic.Value}, size ≤ bound →
      SourceExecutionSize.ExpressionEvaluates program size context scope.evidence scope.source environment before
        reference value after →
      Staging.Recursive.Expression program registry scope context environment before reference (.value value) after := by
  intro size context environment before after value within trace
  obtain ⟨formSize, formBelow, raw⟩ := form_below unique site.referenceFound site.referenceCoercions
    (fun name binder same => by rw [site.referenceForm] at same; cases same) trace
  rw [site.referenceForm, site.referenceRequirements] at raw
  cases raw with
  | elementRef _ baseEvaluates subscriptEvaluates counted inside =>
    simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
    exact .arrayResult ⟨site.referenceNode, lookupExpression?_sound site.referenceFound, site.referenceForm,
        site.referenceRequirements, site.referenceCoercions⟩ rfl
      (.cons (first (by omega) baseEvaluates) (.cons (second (by omega) subscriptEvaluates) .nil))
      (.elementRef counted inside)

/-- A sized value execution of a nested site is a staged execution with the
same value and heap, given the lifting of the admitted callee bodies below a
bound of its size. -/
theorem nested_value {named : SourceCoreGeneralFunctions.Function} {scope : Staging.Recursive.Scope}
    (unique : NodeOccurrencesUnique scope.source) {bound : Nat} (bodies : BodiesLift program registry called bound)
    {id : ExpressionId} (nested : Nested prepared named scope.source called id) :
    ∀ {size : Nat} {context : SourceSemantics.Context} {environment : Dynamic.Environment}
      {before after : Dynamic.Heap} {value : Dynamic.Value}, size ≤ bound →
      SourceExecutionSize.ExpressionEvaluates program size context scope.evidence scope.source environment before id
        value after →
      Staging.Recursive.Expression program registry scope context environment before id (.value value) after := by
  induction nested with
  | literal site atomic =>
    intro size context environment before after value _ trace
    exact expression_value unique (.literal site atomic) trace.sound
  | read site form =>
    intro size context environment before after value _ trace
    exact expression_value unique (.read site form) trace.sound
  | unary site form _ child =>
    intro size context environment before after value within trace
    obtain ⟨formSize, formBelow, raw⟩ := form_below unique site.found site.coercions
      (fun name binder same => by rw [form] at same; cases same) trace
    rw [form, requirements_of site form (fun _ _ same => by cases same)] at raw
    cases raw with
    | unary layout operand applies =>
      have empty := CompatibleExpressionPrimitives.no_owned layout
      subst empty
      cases applies with
      | primitive applied =>
        exact .unary (occurrence site form (fun _ _ same => by cases same))
          (child (by
            simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
            omega) operand) applied
      | method _ selected _ => cases selected
  | binary site form _ _ left right =>
    intro size context environment before after value within trace
    obtain ⟨formSize, formBelow, raw⟩ := form_below unique site.found site.coercions
      (fun name binder same => by rw [form] at same; cases same) trace
    rw [form, requirements_of site form (fun _ _ same => by cases same)] at raw
    cases raw with
    | binaryShortCircuit _ first circuit _ =>
      exact .binaryShortCircuit (occurrence site form (fun _ _ same => by cases same))
        (left (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
          omega) first) circuit
    | binaryEvaluateRight layout first continues second applies =>
      have empty := CompatibleExpressionPrimitives.no_owned layout
      subst empty
      cases applies with
      | primitive applied =>
        exact .binary (occurrence site form (fun _ _ same => by cases same))
          (left (by
            simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
            omega) first) continues
          (right (by
            simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
            omega) second) applied
      | method _ selected _ => cases selected
  | conditional site form _ _ _ test yes no =>
    intro size context environment before after value within trace
    obtain ⟨formSize, formBelow, raw⟩ := form_below unique site.found site.coercions
      (fun name binder same => by rw [form] at same; cases same) trace
    rw [form, requirements_of site form (fun _ _ same => by cases same)] at raw
    cases raw with
    | conditionalTrue _ first second =>
      exact .conditional (occurrence site form (fun _ _ same => by cases same))
        (test (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
          omega) first)
        (yes (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
          omega) second)
    | conditionalFalse _ first second =>
      exact .conditional (occurrence site form (fun _ _ same => by cases same))
        (test (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
          omega) first)
        (no (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
          omega) second)
  | group site form _ child =>
    intro size context environment before after value within trace
    obtain ⟨formSize, formBelow, raw⟩ := form_below unique site.found site.coercions
      (fun name binder same => by rw [form] at same; cases same) trace
    rw [form, requirements_of site form (fun _ _ same => by cases same)] at raw
    cases raw with
    | group _ inner =>
      exact .group (occurrence site form (fun _ _ same => by cases same))
        (child (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
          omega) inner)
  | pair site form _ _ left right =>
    intro size context environment before after value within trace
    obtain ⟨formSize, formBelow, raw⟩ := form_below unique site.found site.coercions
      (fun name binder same => by rw [form] at same; cases same) trace
    rw [form, requirements_of site form (fun _ _ same => by cases same)] at raw
    cases raw with
    | tuple _ elements pack =>
      cases elements with
      | cons first rest =>
        cases rest with
        | cons second tail =>
          cases tail
          cases pack with
          | cons tail =>
            cases tail
            exact .pair (occurrence site form (fun _ _ same => by cases same))
              (left (by
                simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
                omega) first)
              (right (by
                simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
                omega) second)
  | @call id callee ids instantiation site selected _ arguments =>
    intro size context environment before after value within trace
    have contains := lookupExpression?_sound site.found
    cases trace with
    | intro found form coercions =>
      cases node_unique unique found contains
      rw [site.coercions] at coercions
      cases coercions
      rw [site.form, site.requirements, site.coercions] at form
      cases form with
      | directCall calleeContains calleeForm calleeRequirements calleeCoercions valid evaluated produced applies =>
        have stagedArguments := arguments_value (registry := registry) arguments (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at within
          omega) evaluated
        have nilEvidence := evidence_nil (site.monomorphic.predicates ▸ produced)
        subst nilEvidence
        cases applies with
        | global instantiates invocationEq covers invokes =>
          cases invokes with
          | returned _ rootsEq parameters allocate execute returned =>
            obtain ⟨child, closure, lifts⟩ := bodies selected instantiates rootsEq
            have staged := lifts (by
              simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at within ⊢
              omega) execute
            subst returned
            exact .directApplied ⟨site.node, contains, site.form, site.requirements, site.coercions⟩
              ⟨_, calleeContains, calleeForm, calleeRequirements, calleeCoercions⟩ valid stagedArguments produced
              (.global instantiates covers rootsEq closure parameters allocate staged .returned)
          | unit _ resultUnit rootsEq parameters allocate execute fellThrough =>
            obtain ⟨child, closure, lifts⟩ := bodies selected instantiates rootsEq
            have staged := lifts (by
              simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at within ⊢
              omega) execute
            obtain ⟨finalEnvironment, rfl⟩ := fellThrough
            exact .directApplied ⟨site.node, contains, site.form, site.requirements, site.coercions⟩
              ⟨_, calleeContains, calleeForm, calleeRequirements, calleeCoercions⟩ valid stagedArguments produced
              (.global instantiates covers rootsEq closure parameters allocate staged (by rw [resultUnit]; exact .unit))
    | generalizedLocal found formEq =>
      cases node_unique unique found contains
      rw [site.form] at formEq
      cases formEq
  | @conversion id callee argument function target site _ child =>
    intro size context environment before after value within trace
    have contains := lookupExpression?_sound site.found
    cases trace with
    | intro found form coercions =>
      cases node_unique unique found contains
      rw [site.coercions] at coercions
      cases coercions
      rw [site.form, site.requirements, site.coercions] at form
      cases form with
      | builtinCall layout evaluated applies =>
        have stagedArguments := arguments_value (registry := registry)
          (fun other member => by
            cases List.mem_singleton.mp member
            exact child) (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at within
          omega) evaluated
        cases applies with
        | builtin applied =>
          exact .builtinApplied ⟨site.node, contains, site.form, site.requirements, site.coercions⟩
            stagedArguments (.builtin applied)
    | generalizedLocal found formEq =>
      cases node_unique unique found contains
      rw [site.form] at formEq
      cases formEq
  | index site form _ _ base key =>
    intro size context environment before after value within trace
    obtain ⟨formSize, formBelow, raw⟩ := form_below unique site.found site.coercions
      (fun name binder same => by rw [form] at same; cases same) trace
    rw [form, requirements_of site form (fun _ _ same => by cases same)] at raw
    cases raw with
    | indexFound _ first second lookup =>
      exact .indexResult (occurrence site form (fun _ _ same => by cases same))
        (base (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
          omega) first)
        (key (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
          omega) second) (.found rfl lookup)
    | indexDefault _ first second absent defaulted =>
      exact .indexResult (occurrence site form (fun _ _ same => by cases same))
        (base (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
          omega) first)
        (key (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
          omega) second) (.default rfl absent defaulted)
  | builtinValue site form =>
    intro size context environment before after value _ trace
    exact Staging.Recursive.Lifting.atomic_nonlocal unique (lookupExpression?_sound site.found)
      (by rw [form]; exact .reference _ _) site.coercions
      (fun name binder same => by rw [form] at same; cases same) (.value trace.sound)
  | @builtin id callee ids function site _ arguments =>
    intro size context environment before after value within trace
    have contains := lookupExpression?_sound site.found
    cases trace with
    | intro found form coercions =>
      cases node_unique unique found contains
      rw [site.coercions] at coercions
      cases coercions
      rw [site.form, site.requirements, site.coercions] at form
      cases form with
      | builtinCall layout evaluated applies =>
        have stagedArguments := arguments_value (registry := registry) arguments (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at within
          omega) evaluated
        cases applies with
        | builtin applied =>
          exact .builtinApplied ⟨site.node, contains, site.form, site.requirements, site.coercions⟩
            stagedArguments (.builtin applied)
    | generalizedLocal found formEq =>
      cases node_unique unique found contains
      rw [site.form] at formEq
      cases formEq
  | @tuple id ids site _ elements =>
    intro size context environment before after value within trace
    obtain ⟨formSize, formBelow, raw⟩ := form_below unique site.found site.coercions
      (fun name binder same => by rw [site.form] at same; cases same) trace
    rw [site.form, site.requirements] at raw
    cases raw with
    | tuple _ evaluated pack =>
      exact .tupleValue ⟨site.node, lookupExpression?_sound site.found, site.form, site.requirements, site.coercions⟩
        (arguments_value (registry := registry) elements (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
          omega) evaluated) pack
  | @constructor id instantiation ids site _ arguments =>
    intro size context environment before after value within trace
    obtain ⟨formSize, formBelow, raw⟩ := form_below unique site.found site.coercions
      (fun name binder same => by rw [site.form] at same; cases same) trace
    rw [site.form, site.requirements] at raw
    cases raw with
    | constructor _ valid evaluated =>
      exact .constructorValue
        ⟨site.node, lookupExpression?_sound site.found, site.form, site.requirements, site.coercions⟩ valid
        (arguments_value (registry := registry) arguments (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
          omega) evaluated)
  | @array id form site _ children =>
    intro size context environment before after value within trace
    obtain ⟨formSize, formBelow, raw⟩ := form_below unique site.found site.coercions
      (CellAwareInvocationAcceptedArraySites.not_local site) trace
    have occurrence : Staging.Recursive.Occurrence scope id form :=
      ⟨site.node, lookupExpression?_sound site.found, site.formEq, site.requirements, site.coercions⟩
    rw [site.formEq, site.requirements] at raw
    cases site.shape with
    | arrayLength base =>
      cases raw with
      | arrayLength _ first counted =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
        exact .arrayResult occurrence rfl
          (.cons (children base (by simp [Staging.Recursive.arrayChildren]) (by omega) first) .nil)
          (.arrayLength counted)
    | arrayIndex base subscript =>
      cases raw with
      | arrayIndex _ first second reads =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
        exact .arrayResult occurrence rfl
          (.cons (children base (by simp [Staging.Recursive.arrayChildren]) (by omega) first)
            (.cons (children subscript (by simp [Staging.Recursive.arrayChildren]) (by omega) second) .nil))
          (.arrayIndex reads)
    | elementRef base subscript =>
      cases raw with
      | elementRef _ first second counted inside =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
        exact .arrayResult occurrence rfl
          (.cons (children base (by simp [Staging.Recursive.arrayChildren]) (by omega) first)
            (.cons (children subscript (by simp [Staging.Recursive.arrayChildren]) (by omega) second) .nil))
          (.elementRef counted inside)
    | arraySlice base start stop =>
      cases raw with
      | arraySlice _ first bounds counted chosen ordered inside =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
        exact .arrayResult occurrence rfl
          (.cons (children base (by simp [Staging.Recursive.arrayChildren]) (by omega) first)
            (arguments_value (registry := registry) (ids := start.toList ++ stop.toList)
              (fun bound member => children bound (List.mem_cons_of_mem _ member)) (by omega) bounds))
          (.arraySlice counted chosen ordered inside)
    | newArray length _ =>
      cases raw with
      | newArray _ first fits default allocates =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
        exact .arrayResult occurrence rfl
          (.cons (children length (by simp [Staging.Recursive.arrayChildren]) (by omega) first) .nil)
          (.newArray fits default allocates)
    | arrayLiteral _ _ =>
      cases raw with
      | arrayLiteral _ evaluated allocates =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
        exact .arrayResult occurrence rfl
          (arguments_value (registry := registry) children (by omega) evaluated) (.arrayLiteral allocates)
    | @toArray _ _ slice _ _ _ _ _ _ _ =>
      cases raw with
      | toArray _ first copies allocates =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
        exact .arrayResult occurrence rfl
          (.cons (children slice (by simp [Staging.Recursive.arrayChildren]) (by omega) first) .nil)
          (.toArray copies allocates)
  | @memrefLoad id reference site form _ _ first second =>
    intro size context environment before after value within trace
    obtain ⟨formSize, formBelow, raw⟩ := form_below unique site.found site.coercions
      (fun name binder same => by rw [form] at same; cases same) trace
    rw [form, site.requirements] at raw
    cases raw with
    | memrefLoad _ referenceEvaluates reads =>
      simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
      exact .arrayResult ⟨site.node, lookupExpression?_sound site.found, form, site.requirements, site.coercions⟩ rfl
        (.cons (reference_value prepared unique site first second (by omega) referenceEvaluates) .nil)
        (.memrefLoad reads)
  | @memrefStore id reference value site form _ _ _ first second third =>
    intro size context environment before after result within trace
    obtain ⟨formSize, formBelow, raw⟩ := form_below unique site.found site.coercions
      (fun name binder same => by rw [form] at same; cases same) trace
    rw [form, site.requirements] at raw
    cases raw with
    | memrefStore _ referenceEvaluates valueEvaluates read current replace write =>
      simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
      exact .arrayResult ⟨site.node, lookupExpression?_sound site.found, form, site.requirements, site.coercions⟩ rfl
        (.cons (reference_value prepared unique site first second (by omega) referenceEvaluates)
          (.cons (third (by omega) valueEvaluates) .nil))
        (.memrefStore read current replace write)

/-- The value lifting of every nested site below a size, given the lifting of
the callee bodies below it. -/
theorem nested_roots {named : SourceCoreGeneralFunctions.Function} {scope : Staging.Recursive.Scope}
    (unique : NodeOccurrencesUnique scope.source) {bound : Nat} (bodies : BodiesLift program registry called bound) :
    ChildLifts program registry scope (Nested prepared named scope.source called) bound := by
  intro id nested size context environment before after value below trace
  exact nested_value prepared unique bodies nested (Nat.le_of_lt below) trace

/-- Every admitted callee's original body derivation is a staged execution at
every size: one strong induction on the size across bodies. -/
theorem bodies (callees : Callees prepared program registry called) (bound : Nat) :
    BodiesLift program registry called bound := by
  induction bound using Nat.strongRecOn with
  | ind bound ih =>
    intro instantiation bodyInstance statements admitted instantiates rootsEq
    obtain ⟨child, named, expected, closure, unique, shape⟩ := callees admitted instantiates rootsEq
    refine ⟨child, closure, ?_⟩
    intro size context environment before after finalContext outcome below trace
    have sourceEq : child.source = bodyInstance.source := registry.source closure
    have evidenceEq : child.evidence = [] := registry.evidence closure
    have childUnique : NodeOccurrencesUnique child.source := sourceEq ▸ unique
    have childShape : Shape child.source expected (Nested prepared named child.source called) true statements := by
      rw [sourceEq]
      exact shape
    have lift : ChildLifts program registry child (Nested prepared named child.source called) size :=
      nested_roots prepared childUnique (ih size below)
    refine CellAwareInvocationAcceptedSizedLifting.statements childUnique lift childShape (Nat.le_refl size) ?_
    show SourceExecutionSize.FunctionStatementsExecute program size context child.evidence child.source environment
      before statements finalContext outcome after
    rw [sourceEq, evidenceEq]
    exact trace

/-- An ordinary function-body execution of a supported list whose expressions
are nested sites is a staged execution with the same context, outcome and
heap, at any scope with the execution's Source and evidence, given the static
receipts of the admitted callees. -/
theorem body {scope : Staging.Recursive.Scope} {source : TypedSource} {evidence : Dynamic.EvidenceEnvironment}
    (sourceEq : scope.source = source) (evidenceEq : scope.evidence = evidence)
    (unique : NodeOccurrencesUnique source) (callees : Callees prepared program registry called)
    {named : SourceCoreGeneralFunctions.Function} {expected : TypeSystem.Ty} {statements : List StatementId}
    (shape : Shape source expected (Nested prepared named source called) true statements)
    {context : SourceSemantics.Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {finalContext : SourceSemantics.Context} {outcome : Dynamic.ControlOutcome}
    (trace : Dynamic.FunctionStatementsExecute program context evidence source environment before statements
      finalContext outcome after) :
    ∃ size, Staging.Recursive.Size.Statements program registry size scope context environment before statements
      finalContext (control outcome) after := by
  subst sourceEq evidenceEq
  obtain ⟨size, sized⟩ := SourceExecutionSize.FunctionStatementsExecute.has_size trace
  have lift : ChildLifts program registry scope (Nested prepared named scope.source called) size :=
    nested_roots prepared unique (bodies prepared callees size)
  exact Staging.Recursive.Size.Statements.of_trace
    (CellAwareInvocationAcceptedSizedLifting.statements unique lift shape (Nat.le_refl size) sized)

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedCallLifting
end

section
/-! Original fault executions of bodies whose expressions are nested sites are
staged fault executions with the same reason and heap. A fault keeps its reason
from the innermost failing rule to the body, and the staged traces express
every reason but two (`Expressible`): a type mismatch, since a condition whose
value is not a boolean has no staged rule, and a missing declaration, since a
call of a function without a catalogued body has none. A direct call's staged
rules read its callee's occurrence, which the original rule of a fault after
its arguments does not record, so the Source's direct calls are required to
have a plain callee node (`CalleesPlain`, a finite check); a missing node is
then excluded, as every site is a node of the Source. They also read the
validity of the call's instantiation at the caller's context, which holds at a
monomorphic instantiation once that context keeps the program's signatures. A
callee body's fault is lifted by the strong induction on the size that lifts
its values. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedFaultLifting
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (Prepared)
open CellAwareInvocationAcceptedNestedTrees (Nested)
open CellAwareInvocationAcceptedCallLifting (BodiesLift evidence_nil nested_value)

/-- The fault reasons that the staged traces express: all but a type mismatch
and a missing declaration. -/
def Expressible : Dynamic.SemanticFault → Prop
  | .typeMismatch _ _ | .missingDeclaration _ => False
  | _ => True

/-- A node that refers to `instantiation` at `target` without requirements or
coercions. -/
def CalleeAt (target : ExpressionId) (instantiation : DeclarationInstantiation) : Node → Bool
  | .expression callee =>
    decide (callee.id = target) && callee.requirements.isEmpty && callee.coercions.isEmpty &&
      match callee.form with
      | .reference _ (.declaration other) => decide (other = instantiation)
      | _ => false
  | .statement _ => false

/-- A direct call at a node has its callee among `nodes`. -/
def CalleePlainAt (nodes : List Node) : Node → Bool
  | .expression caller =>
    match caller.form with
    | .call target _ (.declaration instantiation) => nodes.any (CalleeAt target instantiation)
    | _ => true
  | .statement _ => true

/-- Every direct call of a Source has a callee node that refers to the call's
declaration without requirements or coercions. -/
def CalleesPlain (source : TypedSource) : Prop :=
  source.nodes.all (CalleePlainAt source.nodes) = true

instance (source : TypedSource) : Decidable (CalleesPlain source) :=
  inferInstanceAs (Decidable (source.nodes.all (CalleePlainAt source.nodes) = true))

section Sites
variable {program : Program} {scope : Staging.Recursive.Scope}

private theorem atomic_form {form : ExpressionForm} (atomic : CompatibleExpressionLiterals.Atomic form) :
    Staging.Recursive.AtomicForm form := by
  cases atomic <;> constructor

private theorem atomic_not_local {form : ExpressionForm} (atomic : CompatibleExpressionLiterals.Atomic form)
    (name : String) (binder : Resolved.LocalId) : form ≠ .reference name (.local binder) := by
  cases atomic <;> intro same <;> cases same

private theorem calleeAt_sound {target : ExpressionId} {instantiation : DeclarationInstantiation} {node : Node}
    (found : CalleeAt target instantiation node = true) :
    ∃ (callee : ExpressionNode) (name : String), node = .expression callee ∧ callee.id = target ∧
      callee.form = .reference name (.declaration instantiation) ∧ callee.requirements = [] ∧
      callee.coercions = [] := by
  cases node with
  | statement _ => simp [CalleeAt] at found
  | expression callee =>
    simp only [CalleeAt] at found
    cases form : callee.form with
    | reference name resolution =>
      cases resolution with
      | declaration other =>
        rw [form] at found
        simp only [Bool.and_eq_true, decide_eq_true_eq, List.isEmpty_iff] at found
        obtain ⟨⟨⟨idEq, requirements⟩, coercions⟩, same⟩ := found
        exact ⟨callee, name, rfl, idEq, by rw [form, same], requirements, coercions⟩
      | _ =>
        rw [form] at found
        simp at found
    | _ =>
      rw [form] at found
      simp at found

/-- A direct call's callee is an occurrence without requirements or
coercions. -/
private theorem callee_occurrence (plain : CalleesPlain scope.source)
    {id callee : ExpressionId} {ids : List ExpressionId} {instantiation : DeclarationInstantiation}
    {node : ExpressionNode} (contains : ContainsExpression scope.source id node)
    (form : node.form = .call callee ids (.declaration instantiation)) :
    ∃ name, Staging.Recursive.Occurrence scope callee (.reference name (.declaration instantiation)) := by
  have atCaller := List.all_eq_true.mp plain (.expression node) contains.1
  simp only [CalleePlainAt, form] at atCaller
  obtain ⟨calleeNode, member, found⟩ := List.any_eq_true.mp atCaller
  obtain ⟨calleeExpression, name, rfl, idEq, calleeForm, requirements, coercions⟩ := calleeAt_sound found
  exact ⟨name, calleeExpression, ⟨member, idEq⟩, calleeForm, requirements, coercions⟩

/-- A monomorphic instantiation of a program function is valid at every context
with the program's signatures. -/
private theorem valid_at {context : SourceSemantics.Context}
    {instantiation : DeclarationInstantiation} {bodyInstance : Dynamic.BodyInstance}
    (signatures : context.signatures = program.signatures)
    (substitution : instantiation.parameterSubstitution = [])
    (instantiates : Dynamic.FunctionInstantiates program instantiation bodyInstance) :
    SourceSemantics.DeclarationInstantiation.Valid context instantiation := by
  cases instantiates with
  | intro _ _ _ _ valid =>
    cases valid with
    | intro signature member declaration exactness _ type predicates parameterComptime returnComptime =>
      refine .intro signature (by rw [signatures]; exact member) declaration exactness ?_ type predicates
        parameterComptime returnComptime
      intro parameter replacement inMember
      rw [substitution] at inMember
      cases inMember

/-- The empty dictionary covers the body of a program function whose
instantiation has no predicates. -/
private theorem covers_nil {instantiation : DeclarationInstantiation} {bodyInstance : Dynamic.BodyInstance}
    (instantiates : Dynamic.FunctionInstantiates program instantiation bodyInstance)
    (predicates : instantiation.predicates = []) :
    Dynamic.EvidenceEnvironment.Covers bodyInstance.context [] := by
  cases instantiates with
  | intro _ _ _ _ _ _ _ contextEq =>
    rw [contextEq]
    refine ⟨fun _ _ looks => (by cases looks), ?_⟩
    intro predicate member
    simp [declarationContext, SourceSemantics.Context.withResidualTypeVariables,
      SourceSemantics.Context.withSolvedRequirements, SourceSemantics.Context.withAssumptions,
      predicates] at member

/-- A program function's body context keeps the program's signatures. -/
private theorem body_signatures {instantiation : DeclarationInstantiation} {bodyInstance : Dynamic.BodyInstance}
    (instantiates : Dynamic.FunctionInstantiates program instantiation bodyInstance) :
    bodyInstance.context.signatures = program.signatures := by
  cases instantiates with
  | intro _ _ _ _ _ _ _ contextEq =>
    rw [contextEq]
    rfl

/-- A sized fault at a node without coercions that is not a local read faults
in the node's form below the same size. -/
private theorem form_fault (unique : NodeOccurrencesUnique scope.source)
    {id : ExpressionId} {node : ExpressionNode} (found : scope.source.lookupExpression? id = some node)
    (coercions : node.coercions = []) (notLocal : ∀ name binder, node.form ≠ .reference name (.local binder))
    {size : Nat} {context : SourceSemantics.Context} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault}
    (trace : SourceExecutionSize.ExpressionFaults program size context scope.evidence scope.source environment
      before id reason after) :
    ∃ formSize, formSize < size ∧ SourceExecutionSize.ExpressionFormFaults program formSize context
      scope.evidence scope.source environment before node.form node.requirements [] reason after := by
  have contains := lookupExpression?_sound found
  cases trace with
  | missing absent => exact (Dynamic.ExpressionAbsentIn.excludes_contains absent contains).elim
  | form traceFound fault =>
    cases CellAwareInvocationAcceptedCallLifting.node_unique unique traceFound contains
    rw [coercions] at fault
    exact ⟨_, SourceExecutionSize.child_lt_stepSize (by simp), fault⟩
  | coercion traceFound _ fault =>
    cases CellAwareInvocationAcceptedCallLifting.node_unique unique traceFound contains
    rw [coercions] at fault
    cases fault
  | generalizedLocalRequirement traceFound formEq =>
    cases CellAwareInvocationAcceptedCallLifting.node_unique unique traceFound contains
    exact absurd formEq (notLocal _ _)
  | generalizedLocalCoercion traceFound formEq =>
    cases CellAwareInvocationAcceptedCallLifting.node_unique unique traceFound contains
    exact absurd formEq (notLocal _ _)

end Sites

variable {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
  (program : Program) (registry : Staging.Recursive.Registry) (called : DeclarationInstantiation → Prop)

/-- The staged fault lifting of the expressions that `child` admits, below a
size, at contexts with the program's signatures. -/
def ChildFaultLifts (scope : Staging.Recursive.Scope) (child : ExpressionId → Prop) (bound : Nat) : Prop :=
  ∀ {id : ExpressionId}, child id → ∀ {size : Nat} {context : SourceSemantics.Context}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault},
    size < bound → context.signatures = program.signatures → Expressible reason →
    SourceExecutionSize.ExpressionFaults program size context scope.evidence scope.source environment before id
      reason after →
    Staging.Recursive.Expression program registry scope context environment before id (.fault (.semantic reason)) after

/-- The direct calls of every admitted callee's body have plain callees. -/
def CalleesFault : Prop :=
  ∀ {instantiation : DeclarationInstantiation} {bodyInstance : Dynamic.BodyInstance},
    called instantiation → Dynamic.FunctionInstantiates program instantiation bodyInstance →
    CalleesPlain bodyInstance.source

/-- Every admitted callee's original body fault with an expressible reason
below a size, at a context with the program's signatures, is a staged fault
execution in the registry scope of its global view. -/
def BodiesFaultLift (bound : Nat) : Prop :=
  ∀ {instantiation : DeclarationInstantiation} {bodyInstance : Dynamic.BodyInstance} {roots : List StatementId},
    called instantiation → Dynamic.FunctionInstantiates program instantiation bodyInstance →
    Dynamic.StatementRoots bodyInstance.source.roots roots →
    ∃ child : Staging.Recursive.Scope,
      registry.Closure (Staging.Recursive.globalView bodyInstance [] roots) child ∧
      ∀ {size : Nat} {context : SourceSemantics.Context} {environment : Dynamic.Environment}
        {before after : Dynamic.Heap} {finalContext : SourceSemantics.Context} {reason : Dynamic.SemanticFault},
        size < bound → context.signatures = program.signatures → Expressible reason →
        SourceExecutionSize.FunctionStatementsFault program size context [] bodyInstance.source environment before
          roots finalContext reason after →
        Staging.Recursive.StatementsIn program registry true child context environment before roots finalContext
          (.fault (.semantic reason)) after

variable {program registry called}

/-- The fault executions of argument lists whose elements lift. -/
private theorem arguments_fault {scope : Staging.Recursive.Scope} {bound : Nat} :
    ∀ {ids : List ExpressionId},
    (∀ argument ∈ ids, ∀ {size : Nat} {context : SourceSemantics.Context} {environment : Dynamic.Environment}
      {before after : Dynamic.Heap} {value : Dynamic.Value}, size ≤ bound →
      SourceExecutionSize.ExpressionEvaluates program size context scope.evidence scope.source environment before
        argument value after →
      Staging.Recursive.Expression program registry scope context environment before argument (.value value) after) →
    (∀ argument ∈ ids, ∀ {size : Nat} {context : SourceSemantics.Context} {environment : Dynamic.Environment}
      {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault}, size ≤ bound →
      context.signatures = program.signatures → Expressible reason →
      SourceExecutionSize.ExpressionFaults program size context scope.evidence scope.source environment before
        argument reason after →
      Staging.Recursive.Expression program registry scope context environment before argument
        (.fault (.semantic reason)) after) →
    ∀ {size : Nat} {context : SourceSemantics.Context} {environment : Dynamic.Environment}
      {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault}, size ≤ bound →
      context.signatures = program.signatures → Expressible reason →
      SourceExecutionSize.ExpressionsFault program size context scope.evidence scope.source environment before ids
        reason after →
      Staging.Recursive.Expressions program registry scope context environment before ids
        (.fault (.semantic reason)) after := by
  intro ids
  induction ids with
  | nil =>
    intro _ _ size context environment before after reason _ _ _ failed
    cases failed
  | cons head rest ih =>
    intro values faults size context environment before after reason within signatures expressible failed
    cases failed with
    | head fault =>
      exact .headFault (faults head List.mem_cons_self (by
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at within
        omega) signatures expressible fault)
    | tail first tail =>
      exact .tailFault
        (values head List.mem_cons_self (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at within
          omega) first)
        (ih (fun argument member => values argument (List.mem_cons_of_mem _ member))
          (fun argument member => faults argument (List.mem_cons_of_mem _ member)) (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at within
          omega) signatures expressible tail)

/-- The fault execution of a memref composite's `lidx` is a staged fault
execution, given the value and fault liftings of its array and its index. -/
private theorem reference_fault {named : SourceCoreGeneralFunctions.Function} {scope : Staging.Recursive.Scope}
    (unique : NodeOccurrencesUnique scope.source) {bound : Nat} {id reference : ExpressionId}
    (site : CellAwareInvocationAcceptedMemrefSites.MemrefSite prepared named scope.source id reference)
    (firstValue : ∀ {size : Nat} {context : SourceSemantics.Context} {environment : Dynamic.Environment}
      {before after : Dynamic.Heap} {value : Dynamic.Value}, size ≤ bound →
      SourceExecutionSize.ExpressionEvaluates program size context scope.evidence scope.source environment before
        site.base value after →
      Staging.Recursive.Expression program registry scope context environment before site.base (.value value) after)
    (secondValue : ∀ {size : Nat} {context : SourceSemantics.Context} {environment : Dynamic.Environment}
      {before after : Dynamic.Heap} {value : Dynamic.Value}, size ≤ bound →
      SourceExecutionSize.ExpressionEvaluates program size context scope.evidence scope.source environment before
        site.subscript value after →
      Staging.Recursive.Expression program registry scope context environment before site.subscript (.value value)
        after)
    (firstFault : ∀ {size : Nat} {context : SourceSemantics.Context} {environment : Dynamic.Environment}
      {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault}, size ≤ bound →
      context.signatures = program.signatures → Expressible reason →
      SourceExecutionSize.ExpressionFaults program size context scope.evidence scope.source environment before
        site.base reason after →
      Staging.Recursive.Expression program registry scope context environment before site.base
        (.fault (.semantic reason)) after)
    (secondFault : ∀ {size : Nat} {context : SourceSemantics.Context} {environment : Dynamic.Environment}
      {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault}, size ≤ bound →
      context.signatures = program.signatures → Expressible reason →
      SourceExecutionSize.ExpressionFaults program size context scope.evidence scope.source environment before
        site.subscript reason after →
      Staging.Recursive.Expression program registry scope context environment before site.subscript
        (.fault (.semantic reason)) after) :
    ∀ {size : Nat} {context : SourceSemantics.Context} {environment : Dynamic.Environment}
      {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault}, size ≤ bound →
      context.signatures = program.signatures → Expressible reason →
      SourceExecutionSize.ExpressionFaults program size context scope.evidence scope.source environment before
        reference reason after →
      Staging.Recursive.Expression program registry scope context environment before reference
        (.fault (.semantic reason)) after := by
  intro size context environment before after reason within signatures expressible trace
  have occurrence : Staging.Recursive.Occurrence scope reference (.elementRef site.base site.subscript) :=
    ⟨site.referenceNode, lookupExpression?_sound site.referenceFound, site.referenceForm, site.referenceRequirements,
      site.referenceCoercions⟩
  obtain ⟨formSize, formBelow, raw⟩ := form_fault unique site.referenceFound site.referenceCoercions
    (fun name binder same => by rw [site.referenceForm] at same; cases same) trace
  rw [site.referenceForm, site.referenceRequirements] at raw
  cases raw with
  | elementRefBase _ failed =>
    simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
    exact .arrayFault occurrence rfl (.headFault (firstFault (by omega) signatures expressible failed))
  | elementRefIndex _ evaluated failed =>
    simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
    exact .arrayFault occurrence rfl (.tailFault (firstValue (by omega) evaluated)
      (.headFault (secondFault (by omega) signatures expressible failed)))
  | elementRefIndexType _ first second notWord actual =>
    simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
    exact .arrayResult occurrence rfl (.cons (firstValue (by omega) first) (.cons (secondValue (by omega) second) .nil))
      (.elementRefIndexType notWord actual)
  | elementRefOutOfBounds _ first second outside =>
    simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
    exact .arrayResult occurrence rfl (.cons (firstValue (by omega) first) (.cons (secondValue (by omega) second) .nil))
      (.elementRefOutOfBounds outside)

/-- A sized fault execution of a nested site with an expressible reason, at a
context with the program's signatures, is a staged fault execution with the
same reason and heap, given that the Source's direct calls have plain callees
and the value and fault liftings of the admitted callee bodies below a bound
of its size. -/
theorem nested_fault {named : SourceCoreGeneralFunctions.Function} {scope : Staging.Recursive.Scope}
    (unique : NodeOccurrencesUnique scope.source) (plain : CalleesPlain scope.source) {bound : Nat}
    (bodies : BodiesLift program registry called bound) (faults : BodiesFaultLift program registry called bound)
    {id : ExpressionId} (nested : Nested prepared named scope.source called id) :
    ∀ {size : Nat} {context : SourceSemantics.Context} {environment : Dynamic.Environment}
      {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault}, size ≤ bound →
      context.signatures = program.signatures → Expressible reason →
      SourceExecutionSize.ExpressionFaults program size context scope.evidence scope.source environment before id
        reason after →
      Staging.Recursive.Expression program registry scope context environment before id
        (.fault (.semantic reason)) after := by
  induction nested with
  | literal site atomic =>
    intro size context environment before after reason _ _ _ trace
    exact Staging.Recursive.Lifting.atomic_nonlocal unique (lookupExpression?_sound site.found)
      (atomic_form atomic) site.coercions (atomic_not_local atomic) (.fault trace.sound)
  | read site form =>
    intro size context environment before after reason _ _ _ trace
    have contains := lookupExpression?_sound site.found
    cases trace with
    | missing absent => exact (Dynamic.ExpressionAbsentIn.excludes_contains absent contains).elim
    | form found raw =>
      cases CellAwareInvocationAcceptedCallLifting.node_unique unique found contains
      rw [site.coercions] at raw
      exact .atomicFault contains (by rw [form]; exact .reference _ _) site.coercions raw.sound
    | coercion found _ failed =>
      cases CellAwareInvocationAcceptedCallLifting.node_unique unique found contains
      rw [site.coercions] at failed
      cases failed
    | generalizedLocalRequirement found formEq layout lookup read descriptor contextFields selection failed =>
      cases CellAwareInvocationAcceptedCallLifting.node_unique unique found contains
      exact .generalizedLocalRequirement contains formEq layout lookup read descriptor contextFields selection
        failed
    | generalizedLocalCoercion found _ _ _ _ _ _ _ failed =>
      cases CellAwareInvocationAcceptedCallLifting.node_unique unique found contains
      rw [site.coercions] at failed
      cases failed
  | unary site form operandNested child =>
    intro size context environment before after reason within signatures expressible trace
    obtain ⟨formSize, formBelow, raw⟩ := form_fault unique site.found site.coercions
      (fun name binder same => by rw [form] at same; cases same) trace
    rw [form, CellAwareInvocationAcceptedCallLifting.requirements_of site form (fun _ _ same => by cases same)] at raw
    cases raw with
    | unaryOperand _ operand =>
      exact .unaryOperandFault (CellAwareInvocationAcceptedCallLifting.occurrence site form (fun _ _ same => by cases same))
        (child (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
          omega) signatures expressible operand)
    | unaryApply layout operand applies =>
      have empty := CompatibleExpressionPrimitives.no_owned layout
      subst empty
      cases applies with
      | primitive invalid =>
        exact .unaryInvalid (CellAwareInvocationAcceptedCallLifting.occurrence site form (fun _ _ same => by cases same))
          (nested_value prepared unique bodies operandNested (by
            simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
            omega) operand) invalid
      | requirement failed => cases failed
      | method _ selected _ => cases selected
  | binary site form leftNested rightNested left right =>
    intro size context environment before after reason within signatures expressible trace
    obtain ⟨formSize, formBelow, raw⟩ := form_fault unique site.found site.coercions
      (fun name binder same => by rw [form] at same; cases same) trace
    rw [form, CellAwareInvocationAcceptedCallLifting.requirements_of site form (fun _ _ same => by cases same)] at raw
    cases raw with
    | binaryLeft _ first =>
      exact .binaryLeftFault (CellAwareInvocationAcceptedCallLifting.occurrence site form (fun _ _ same => by cases same))
        (left (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
          omega) signatures expressible first)
    | binaryLeftOperand _ first invalid =>
      exact .binaryLeftInvalid (CellAwareInvocationAcceptedCallLifting.occurrence site form (fun _ _ same => by cases same))
        (nested_value prepared unique bodies leftNested (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
          omega) first) invalid
    | binaryRight _ first continues second =>
      exact .binaryRightFault (CellAwareInvocationAcceptedCallLifting.occurrence site form (fun _ _ same => by cases same))
        (nested_value prepared unique bodies leftNested (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
          omega) first) continues
        (right (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
          omega) signatures expressible second)
    | binaryApply layout first continues second applies =>
      have empty := CompatibleExpressionPrimitives.no_owned layout
      subst empty
      have stagedLeft := nested_value prepared unique bodies leftNested (by
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
        omega) first
      have stagedRight := nested_value prepared unique bodies rightNested (by
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
        omega) second
      cases applies with
      | primitive invalid =>
        exact .binaryInvalid (CellAwareInvocationAcceptedCallLifting.occurrence site form (fun _ _ same => by cases same)) stagedLeft continues
          stagedRight invalid
      | panic panics =>
        exact .binaryPanic (CellAwareInvocationAcceptedCallLifting.occurrence site form (fun _ _ same => by cases same)) stagedLeft continues
          stagedRight panics
      | requirement failed => cases failed
      | method _ selected _ => cases selected
  | conditional site form testNested _ _ test yes no =>
    intro size context environment before after reason within signatures expressible trace
    obtain ⟨formSize, formBelow, raw⟩ := form_fault unique site.found site.coercions
      (fun name binder same => by rw [form] at same; cases same) trace
    rw [form, CellAwareInvocationAcceptedCallLifting.requirements_of site form (fun _ _ same => by cases same)] at raw
    cases raw with
    | conditionalCondition _ first =>
      exact .conditionalFault (CellAwareInvocationAcceptedCallLifting.occurrence site form (fun _ _ same => by cases same))
        (test (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
          omega) signatures expressible first)
    | conditionalType _ _ _ _ => simp [Expressible] at expressible
    | conditionalTrueBranch _ first second =>
      exact .conditional (CellAwareInvocationAcceptedCallLifting.occurrence site form (fun _ _ same => by cases same))
        (nested_value prepared unique bodies testNested (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
          omega) first)
        (yes (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
          omega) signatures expressible second)
    | conditionalFalseBranch _ first second =>
      exact .conditional (CellAwareInvocationAcceptedCallLifting.occurrence site form (fun _ _ same => by cases same))
        (nested_value prepared unique bodies testNested (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
          omega) first)
        (no (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
          omega) signatures expressible second)
  | group site form _ child =>
    intro size context environment before after reason within signatures expressible trace
    obtain ⟨formSize, formBelow, raw⟩ := form_fault unique site.found site.coercions
      (fun name binder same => by rw [form] at same; cases same) trace
    rw [form, CellAwareInvocationAcceptedCallLifting.requirements_of site form (fun _ _ same => by cases same)] at raw
    cases raw with
    | group _ inner =>
      exact .group (CellAwareInvocationAcceptedCallLifting.occurrence site form (fun _ _ same => by cases same))
        (child (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
          omega) signatures expressible inner)
  | pair site form leftNested _ left right =>
    intro size context environment before after reason within signatures expressible trace
    obtain ⟨formSize, formBelow, raw⟩ := form_fault unique site.found site.coercions
      (fun name binder same => by rw [form] at same; cases same) trace
    rw [form, CellAwareInvocationAcceptedCallLifting.requirements_of site form (fun _ _ same => by cases same)] at raw
    cases raw with
    | tuple _ elements =>
      cases elements with
      | head first =>
        exact .pairLeftFault (CellAwareInvocationAcceptedCallLifting.occurrence site form (fun _ _ same => by cases same))
          (left (by
            simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
            omega) signatures expressible first)
      | tail first rest =>
        cases rest with
        | head second =>
          exact .pairRightFault (CellAwareInvocationAcceptedCallLifting.occurrence site form (fun _ _ same => by cases same))
            (nested_value prepared unique bodies leftNested (by
              simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
              omega) first)
            (right (by
              simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
              omega) signatures expressible second)
        | tail _ rest => cases rest
  | @call id callee ids instantiation site selected argumentsNested arguments =>
    intro size context environment before after reason within signatures expressible trace
    have contains := lookupExpression?_sound site.found
    obtain ⟨name, calleeOccurrence⟩ := callee_occurrence plain contains site.form
    have callOccurrence : Staging.Recursive.Occurrence scope id (.call callee ids (.declaration instantiation)) :=
      ⟨site.node, contains, site.form, site.requirements, site.coercions⟩
    obtain ⟨formSize, formBelow, raw⟩ := form_fault unique site.found site.coercions
      (fun name binder same => by rw [site.form] at same; cases same) trace
    rw [site.form, site.requirements] at raw
    cases raw with
    | directCalleeMissing absent =>
      obtain ⟨_, calleeContains, _⟩ := calleeOccurrence
      exact (Dynamic.ExpressionAbsentIn.excludes_contains absent calleeContains).elim
    | directArguments _ _ failed =>
      exact .directArgumentsFault callOccurrence calleeOccurrence
        (arguments_fault (fun argument member => nested_value prepared unique bodies (argumentsNested argument member))
          arguments (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
          omega) signatures expressible failed)
    | directRequirements _ failed =>
      rw [site.monomorphic.predicates] at failed
      cases failed
    | directApply evaluated produced failed =>
      have stagedArguments := CellAwareInvocationAcceptedCallLifting.arguments_value (registry := registry)
        (fun argument member => nested_value prepared unique bodies (argumentsNested argument member)) (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
          omega) evaluated
      have nilEvidence := evidence_nil (site.monomorphic.predicates ▸ produced)
      subst nilEvidence
      cases failed with
      | notCallable invalid => exact (invalid trivial).elim
      | globalSignatureMissing _ => simp [Expressible] at expressible
      | globalBodyMissing _ => simp [Expressible] at expressible
      | globalArity instantiates mismatch =>
        exact .directApplied callOccurrence calleeOccurrence
          (valid_at signatures site.monomorphic.substitution instantiates) stagedArguments produced
          (.globalArity instantiates mismatch)
      | globalBody instantiates _ failed =>
        have valid := valid_at signatures site.monomorphic.substitution instantiates
        have covers := covers_nil instantiates site.monomorphic.predicates
        cases failed with
        | arity mismatch =>
          exact .directApplied callOccurrence calleeOccurrence valid stagedArguments produced
            (.globalArity instantiates mismatch)
        | statements rootsEq parameters allocate failed =>
          obtain ⟨child, closure, lifts⟩ := faults selected instantiates rootsEq
          have staged := lifts (by
            simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
            omega)
            ((SourceSemantics.StructuralSubstitution.MonoBindersExtend.signatures_eq parameters).trans
              (body_signatures instantiates))
            expressible failed
          exact .directApplied callOccurrence calleeOccurrence valid stagedArguments produced
            (.global instantiates covers rootsEq closure parameters allocate staged .fault)
        | controlEscape rootsEq parameters allocate execute escaped =>
          obtain ⟨child, closure, lifts⟩ := bodies selected instantiates rootsEq
          have staged := lifts (by
            simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
            omega) execute
          rcases escaped with ⟨escapedEnvironment, rfl⟩ | ⟨escapedEnvironment, rfl⟩
          · exact .directApplied callOccurrence calleeOccurrence valid stagedArguments produced
              (.global instantiates covers rootsEq closure parameters allocate staged .breaking)
          · exact .directApplied callOccurrence calleeOccurrence valid stagedArguments produced
              (.global instantiates covers rootsEq closure parameters allocate staged .continuing)
  | @conversion id callee argument function target site argumentNested child =>
    intro size context environment before after reason within signatures expressible trace
    have contains := lookupExpression?_sound site.found
    have callOccurrence :
        Staging.Recursive.Occurrence scope id (.call callee [argument] (.builtinFunction function)) :=
      ⟨site.node, contains, site.form, site.requirements, site.coercions⟩
    obtain ⟨formSize, formBelow, raw⟩ := form_fault unique site.found site.coercions
      (fun name binder same => by rw [site.form] at same; cases same) trace
    rw [site.form, site.requirements] at raw
    have values : ∀ other ∈ [argument], ∀ {size : Nat} {context : SourceSemantics.Context}
        {environment : Dynamic.Environment} {before after : Dynamic.Heap} {value : Dynamic.Value}, size ≤ bound →
        SourceExecutionSize.ExpressionEvaluates program size context scope.evidence scope.source environment
          before other value after →
        Staging.Recursive.Expression program registry scope context environment before other (.value value)
          after := by
      intro other member
      cases List.mem_singleton.mp member
      exact nested_value prepared unique bodies argumentNested
    cases raw with
    | builtinArguments _ failed =>
      exact .builtinArgumentsFault callOccurrence
        (arguments_fault values (fun other member => by
          cases List.mem_singleton.mp member
          exact child) (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
          omega) signatures expressible failed)
    | builtinApply _ evaluated failed =>
      have stagedArguments := CellAwareInvocationAcceptedCallLifting.arguments_value (registry := registry)
        values (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
          omega) evaluated
      cases failed with
      | notCallable invalid => exact (invalid trivial).elim
      | builtinArity mismatch => exact .builtinApplied callOccurrence stagedArguments (.builtinArity mismatch)
      | builtinArgumentType arity mismatch =>
        exact .builtinApplied callOccurrence stagedArguments (.builtinType arity mismatch)
      | builtinFaults failed => exact .builtinApplied callOccurrence stagedArguments (.builtinFault failed)
  | index site form baseNested keyNested base key =>
    intro size context environment before after reason within signatures expressible trace
    obtain ⟨formSize, formBelow, raw⟩ := form_fault unique site.found site.coercions
      (fun name binder same => by rw [form] at same; cases same) trace
    rw [form, CellAwareInvocationAcceptedCallLifting.requirements_of site form (fun _ _ same => by cases same)] at raw
    cases raw with
    | indexBase _ failed =>
      exact .indexBaseFault (CellAwareInvocationAcceptedCallLifting.occurrence site form (fun _ _ same => by cases same))
        (base (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
          omega) signatures expressible failed)
    | indexKey _ first failed =>
      exact .indexKeyFault (CellAwareInvocationAcceptedCallLifting.occurrence site form (fun _ _ same => by cases same))
        (nested_value prepared unique bodies baseNested (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
          omega) first)
        (key (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
          omega) signatures expressible failed)
    | indexShape _ first second notMapping =>
      exact .indexResult (CellAwareInvocationAcceptedCallLifting.occurrence site form (fun _ _ same => by cases same))
        (nested_value prepared unique bodies baseNested (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
          omega) first)
        (nested_value prepared unique bodies keyNested (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
          omega) second) (.shape notMapping)
    | indexKeyType _ first second actual mismatch =>
      exact .indexResult (CellAwareInvocationAcceptedCallLifting.occurrence site form (fun _ _ same => by cases same))
        (nested_value prepared unique bodies baseNested (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
          omega) first)
        (nested_value prepared unique bodies keyNested (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
          omega) second) (.keyType rfl actual mismatch)
    | indexDefaultUnavailable _ first second keyTyped absent unavailable =>
      exact .indexResult (CellAwareInvocationAcceptedCallLifting.occurrence site form (fun _ _ same => by cases same))
        (nested_value prepared unique bodies baseNested (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
          omega) first)
        (nested_value prepared unique bodies keyNested (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
          omega) second)
        (.unavailable rfl keyTyped absent unavailable)
  | builtinValue site form =>
    intro size context environment before after reason _ _ _ trace
    exact Staging.Recursive.Lifting.atomic_nonlocal unique (lookupExpression?_sound site.found)
      (by rw [form]; exact .reference _ _) site.coercions
      (fun name binder same => by rw [form] at same; cases same) (.fault trace.sound)
  | @builtin id callee ids function site argumentsNested arguments =>
    intro size context environment before after reason within signatures expressible trace
    have contains := lookupExpression?_sound site.found
    have callOccurrence :
        Staging.Recursive.Occurrence scope id (.call callee ids (.builtinFunction function)) :=
      ⟨site.node, contains, site.form, site.requirements, site.coercions⟩
    obtain ⟨formSize, formBelow, raw⟩ := form_fault unique site.found site.coercions
      (fun name binder same => by rw [site.form] at same; cases same) trace
    rw [site.form, site.requirements] at raw
    have values : ∀ other ∈ ids, ∀ {size : Nat} {context : SourceSemantics.Context}
        {environment : Dynamic.Environment} {before after : Dynamic.Heap} {value : Dynamic.Value}, size ≤ bound →
        SourceExecutionSize.ExpressionEvaluates program size context scope.evidence scope.source environment
          before other value after →
        Staging.Recursive.Expression program registry scope context environment before other (.value value)
          after :=
      fun other member => nested_value prepared unique bodies (argumentsNested other member)
    cases raw with
    | builtinArguments _ failed =>
      exact .builtinArgumentsFault callOccurrence
        (arguments_fault values arguments (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
          omega) signatures expressible failed)
    | builtinApply _ evaluated failed =>
      have stagedArguments := CellAwareInvocationAcceptedCallLifting.arguments_value (registry := registry)
        values (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
          omega) evaluated
      cases failed with
      | notCallable invalid => exact (invalid trivial).elim
      | builtinArity mismatch => exact .builtinApplied callOccurrence stagedArguments (.builtinArity mismatch)
      | builtinArgumentType arity mismatch =>
        exact .builtinApplied callOccurrence stagedArguments (.builtinType arity mismatch)
      | builtinFaults failed => exact .builtinApplied callOccurrence stagedArguments (.builtinFault failed)
  | @tuple id ids site elementsNested elements =>
    intro size context environment before after reason within signatures expressible trace
    obtain ⟨formSize, formBelow, raw⟩ := form_fault unique site.found site.coercions
      (fun name binder same => by rw [site.form] at same; cases same) trace
    rw [site.form, site.requirements] at raw
    have values : ∀ other ∈ ids, ∀ {size : Nat} {context : SourceSemantics.Context}
        {environment : Dynamic.Environment} {before after : Dynamic.Heap} {value : Dynamic.Value}, size ≤ bound →
        SourceExecutionSize.ExpressionEvaluates program size context scope.evidence scope.source environment
          before other value after →
        Staging.Recursive.Expression program registry scope context environment before other (.value value)
          after :=
      fun other member => nested_value prepared unique bodies (elementsNested other member)
    cases raw with
    | tuple _ failed =>
      exact .tupleFault ⟨site.node, lookupExpression?_sound site.found, site.form, site.requirements, site.coercions⟩
        (arguments_fault values elements (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
          omega) signatures expressible failed)
  | @constructor id instantiation ids site argumentsNested arguments =>
    intro size context environment before after reason within signatures expressible trace
    have occurrence : Staging.Recursive.Occurrence scope id (.constructor instantiation ids) :=
      ⟨site.node, lookupExpression?_sound site.found, site.form, site.requirements, site.coercions⟩
    obtain ⟨formSize, formBelow, raw⟩ := form_fault unique site.found site.coercions
      (fun name binder same => by rw [site.form] at same; cases same) trace
    rw [site.form, site.requirements] at raw
    have values : ∀ other ∈ ids, ∀ {size : Nat} {context : SourceSemantics.Context}
        {environment : Dynamic.Environment} {before after : Dynamic.Heap} {value : Dynamic.Value}, size ≤ bound →
        SourceExecutionSize.ExpressionEvaluates program size context scope.evidence scope.source environment
          before other value after →
        Staging.Recursive.Expression program registry scope context environment before other (.value value)
          after :=
      fun other member => nested_value prepared unique bodies (argumentsNested other member)
    cases raw with
    | constructorArgument _ failed =>
      exact .constructorFault occurrence
        (arguments_fault values arguments (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
          omega) signatures expressible failed)
    | constructorMetadata _ metadata => exact .constructorMetadataFault occurrence metadata
  | @array id form site childrenNested children =>
    intro size context environment before after reason within signatures expressible trace
    obtain ⟨formSize, formBelow, raw⟩ := form_fault unique site.found site.coercions
      (CellAwareInvocationAcceptedArraySites.not_local site) trace
    have occurrence : Staging.Recursive.Occurrence scope id form :=
      ⟨site.node, lookupExpression?_sound site.found, site.formEq, site.requirements, site.coercions⟩
    rw [site.formEq, site.requirements] at raw
    have values : ∀ other ∈ (Staging.Recursive.arrayChildren form).getD [], ∀ {size : Nat}
        {context : SourceSemantics.Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
        {value : Dynamic.Value}, size ≤ bound →
        SourceExecutionSize.ExpressionEvaluates program size context scope.evidence scope.source environment
          before other value after →
        Staging.Recursive.Expression program registry scope context environment before other (.value value)
          after :=
      fun other member => nested_value prepared unique bodies (childrenNested other member)
    cases site.shape with
    | arrayLength base =>
      cases raw with
      | arrayLengthBase _ failed =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
        exact .arrayFault occurrence rfl
          (.headFault (children base (by simp [Staging.Recursive.arrayChildren]) (by omega) signatures expressible
            failed))
    | arrayIndex base subscript =>
      cases raw with
      | arrayIndexBase _ failed =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
        exact .arrayFault occurrence rfl
          (.headFault (children base (by simp [Staging.Recursive.arrayChildren]) (by omega) signatures expressible
            failed))
      | arrayIndexIndex _ first failed =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
        exact .arrayFault occurrence rfl
          (.tailFault (values base (by simp [Staging.Recursive.arrayChildren]) (by omega) first)
            (.headFault (children subscript (by simp [Staging.Recursive.arrayChildren]) (by omega) signatures
              expressible failed)))
      | arrayIndexType _ first second notWord actual =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
        exact .arrayResult occurrence rfl
          (.cons (values base (by simp [Staging.Recursive.arrayChildren]) (by omega) first)
            (.cons (values subscript (by simp [Staging.Recursive.arrayChildren]) (by omega) second) .nil))
          (.arrayIndexType notWord actual)
      | arrayIndexOutOfBounds _ first second outside =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
        exact .arrayResult occurrence rfl
          (.cons (values base (by simp [Staging.Recursive.arrayChildren]) (by omega) first)
            (.cons (values subscript (by simp [Staging.Recursive.arrayChildren]) (by omega) second) .nil))
          (.arrayIndexOutOfBounds outside)
    | elementRef base subscript =>
      cases raw with
      | elementRefBase _ failed =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
        exact .arrayFault occurrence rfl
          (.headFault (children base (by simp [Staging.Recursive.arrayChildren]) (by omega) signatures expressible
            failed))
      | elementRefIndex _ first failed =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
        exact .arrayFault occurrence rfl
          (.tailFault (values base (by simp [Staging.Recursive.arrayChildren]) (by omega) first)
            (.headFault (children subscript (by simp [Staging.Recursive.arrayChildren]) (by omega) signatures
              expressible failed)))
      | elementRefIndexType _ first second notWord actual =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
        exact .arrayResult occurrence rfl
          (.cons (values base (by simp [Staging.Recursive.arrayChildren]) (by omega) first)
            (.cons (values subscript (by simp [Staging.Recursive.arrayChildren]) (by omega) second) .nil))
          (.elementRefIndexType notWord actual)
      | elementRefOutOfBounds _ first second outside =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
        exact .arrayResult occurrence rfl
          (.cons (values base (by simp [Staging.Recursive.arrayChildren]) (by omega) first)
            (.cons (values subscript (by simp [Staging.Recursive.arrayChildren]) (by omega) second) .nil))
          (.elementRefOutOfBounds outside)
    | arraySlice base start stop =>
      cases raw with
      | arraySliceBase _ failed =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
        exact .arrayFault occurrence rfl
          (.headFault (children base (by simp [Staging.Recursive.arrayChildren]) (by omega) signatures expressible
            failed))
      | arraySliceBounds _ first failed =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
        exact .arrayFault occurrence rfl
          (.tailFault (values base (by simp [Staging.Recursive.arrayChildren]) (by omega) first)
            (arguments_fault (ids := start.toList ++ stop.toList)
              (fun bound member => values bound (List.mem_cons_of_mem _ member))
              (fun bound member => children bound (List.mem_cons_of_mem _ member)) (by omega) signatures
              expressible failed))
      | arraySliceBoundType _ first bounds member notWord actual =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
        exact .arrayResult occurrence rfl
          (.cons (values base (by simp [Staging.Recursive.arrayChildren]) (by omega) first)
            (CellAwareInvocationAcceptedCallLifting.arguments_value (registry := registry)
              (ids := start.toList ++ stop.toList)
              (fun bound member => values bound (List.mem_cons_of_mem _ member)) (by omega) bounds))
          (.arraySliceBoundType member notWord actual)
      | arraySliceOutOfBounds _ first bounds counted chosen outside =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
        exact .arrayResult occurrence rfl
          (.cons (values base (by simp [Staging.Recursive.arrayChildren]) (by omega) first)
            (CellAwareInvocationAcceptedCallLifting.arguments_value (registry := registry)
              (ids := start.toList ++ stop.toList)
              (fun bound member => values bound (List.mem_cons_of_mem _ member)) (by omega) bounds))
          (.arraySliceOutOfBounds counted chosen outside)
    | newArray length _ =>
      cases raw with
      | newArrayLength _ failed =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
        exact .arrayFault occurrence rfl
          (.headFault (children length (by simp [Staging.Recursive.arrayChildren]) (by omega) signatures
            expressible failed))
      | newArrayLengthType _ first notWord actual =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
        exact .arrayResult occurrence rfl
          (.cons (values length (by simp [Staging.Recursive.arrayChildren]) (by omega) first) .nil)
          (.newArrayLengthType notWord actual)
      | newArrayTooLong _ first tooLong =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
        exact .arrayResult occurrence rfl
          (.cons (values length (by simp [Staging.Recursive.arrayChildren]) (by omega) first) .nil)
          (.newArrayTooLong tooLong)
    | arrayLiteral _ _ =>
      cases raw with
      | arrayLiteralElements _ failed =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
        exact .arrayFault occurrence rfl
          (arguments_fault values children (by omega) signatures expressible failed)
    | @toArray _ _ slice _ _ _ _ _ _ _ =>
      cases raw with
      | toArraySlice _ failed =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
        exact .arrayFault occurrence rfl
          (.headFault (children slice (by simp [Staging.Recursive.arrayChildren]) (by omega) signatures
            expressible failed))
  | @memrefLoad id reference site form firstNested secondNested first second =>
    intro size context environment before after reason within signatures expressible trace
    have occurrence : Staging.Recursive.Occurrence scope id (.memrefLoad reference) :=
      ⟨site.node, lookupExpression?_sound site.found, form, site.requirements, site.coercions⟩
    obtain ⟨formSize, formBelow, raw⟩ := form_fault unique site.found site.coercions
      (fun name binder same => by rw [form] at same; cases same) trace
    rw [form, site.requirements] at raw
    cases raw with
    | memrefLoadReference _ failed =>
      simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
      exact .arrayFault occurrence rfl (.headFault (reference_fault prepared unique site
        (nested_value prepared unique bodies firstNested) (nested_value prepared unique bodies secondNested) first
        second (by omega) signatures expressible failed))
  | @memrefStore id reference value site form firstNested secondNested thirdNested first second third =>
    intro size context environment before after reason within signatures expressible trace
    have occurrence : Staging.Recursive.Occurrence scope id (.memrefStore reference value) :=
      ⟨site.node, lookupExpression?_sound site.found, form, site.requirements, site.coercions⟩
    obtain ⟨formSize, formBelow, raw⟩ := form_fault unique site.found site.coercions
      (fun name binder same => by rw [form] at same; cases same) trace
    rw [form, site.requirements] at raw
    cases raw with
    | memrefStoreReference _ failed =>
      simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
      exact .arrayFault occurrence rfl (.headFault (reference_fault prepared unique site
        (nested_value prepared unique bodies firstNested) (nested_value prepared unique bodies secondNested) first
        second (by omega) signatures expressible failed))
    | memrefStoreValue _ referenceEvaluates failed =>
      simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at formBelow
      exact .arrayFault occurrence rfl (.tailFault
        (CellAwareInvocationAcceptedCallLifting.reference_value prepared unique site
          (nested_value prepared unique bodies firstNested) (nested_value prepared unique bodies secondNested)
          (by omega) referenceEvaluates)
        (.headFault (third (by omega) signatures expressible failed)))

/-- The fault lifting of every nested site below a size, given that the
Source's direct calls have plain callees and the value and fault liftings of
the callee bodies below it. -/
theorem nested_fault_roots {named : SourceCoreGeneralFunctions.Function} {scope : Staging.Recursive.Scope}
    (unique : NodeOccurrencesUnique scope.source) (plain : CalleesPlain scope.source) {bound : Nat}
    (bodies : BodiesLift program registry called bound) (faults : BodiesFaultLift program registry called bound) :
    ChildFaultLifts program registry scope (Nested prepared named scope.source called) bound := by
  intro id nested size context environment before after reason below signatures expressible trace
  exact nested_fault prepared unique plain bodies faults nested (Nat.le_of_lt below) signatures expressible trace

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedFaultLifting
end

section
/-! Original fault executions of supported statement lists are staged fault
executions with the same reason and heap, given the value and fault liftings
of their expressions below the size. A statement faults in its expression, its
target, bare or through mapping indices, the operand of its in-place `~`, its
inner list, the pattern or selected body of its match, a header item or an
iteration of its loop, or a
falling-through statement is followed by a fault in the rest of its list; the
staged rule of the same form carries the fault, at the context, environment
and heap of the original execution. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedFaultLifting
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (Prepared)
open CellAwareInvocationAcceptedNestedTrees (Nested)
open CellAwareInvocationAcceptedBodyShape (Shape)
open CellAwareInvocationAcceptedSizedLifting (ChildLifts)
open CellAwareInvocationAcceptedCallLifting (BodiesLift Callees)

/-- The sized fault judgment of each compiler mode's statement lists. -/
def FaultOriginal (program : Program) (size : Nat) : Bool → SourceSemantics.Context → Dynamic.EvidenceEnvironment →
    TypedSource → Dynamic.Environment → Dynamic.Heap → List StatementId → SourceSemantics.Context →
    Dynamic.SemanticFault → Dynamic.Heap → Prop
  | true => SourceExecutionSize.FunctionStatementsFault program size
  | false => SourceExecutionSize.StatementsFault program size

section Inversion
variable {program : Program} {source : TypedSource} {context : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
  {id : StatementId} {node : StatementNode} {reason : Dynamic.SemanticFault} {size : Nat}

private theorem return_fault_inv (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) {expression : ExpressionId}
    (form : node.form = .returnStmt (some expression))
    (fault : SourceExecutionSize.StatementFaults program size context evidence source environment before id
      reason after) :
    ∃ child, child < size ∧ SourceExecutionSize.ExpressionFaults program child context evidence source environment
      before expression reason after := by
  cases fault with
  | missing absent => exact (Dynamic.StatementAbsentIn.excludes_contains absent (lookupStatement?_sound found)).elim
  | returnValue contains formEq fault =>
    obtain rfl := CellAwareInvocationAcceptedSizedLifting.same_node unique found contains
    rw [form] at formEq
    cases formEq
    exact ⟨_, CellAwareInvocationAcceptedSizedLifting.below_one, fault⟩
  | _ =>
    exfalso
    obtain rfl := CellAwareInvocationAcceptedSizedLifting.same_node unique found (by assumption)
    simp_all

private theorem return_unit_fault_inv (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .returnStmt none)
    (fault : SourceExecutionSize.StatementFaults program size context evidence source environment before id
      reason after) : False := by
  cases fault with
  | missing absent => exact Dynamic.StatementAbsentIn.excludes_contains absent (lookupStatement?_sound found)
  | _ =>
    obtain rfl := CellAwareInvocationAcceptedSizedLifting.same_node unique found (by assumption)
    simp_all

private theorem declared_fault_inv (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) {binder : TypedBinder} {expression : ExpressionId}
    (form : node.form = .letDecl binder (some expression)) (monomorphic : binder.scheme.quantified = [])
    (fault : SourceExecutionSize.StatementFaults program size context evidence source environment before id
      reason after) :
    ∃ child, child < size ∧ SourceExecutionSize.ExpressionFaults program child context evidence source environment
      before expression reason after := by
  cases fault with
  | missing absent => exact (Dynamic.StatementAbsentIn.excludes_contains absent (lookupStatement?_sound found)).elim
  | polymorphicLet contains formEq polymorphic _ =>
    obtain rfl := CellAwareInvocationAcceptedSizedLifting.same_node unique found contains
    rw [form] at formEq
    cases formEq
    exact absurd monomorphic polymorphic
  | letInitializer contains formEq _ fault =>
    obtain rfl := CellAwareInvocationAcceptedSizedLifting.same_node unique found contains
    rw [form] at formEq
    cases formEq
    exact ⟨_, CellAwareInvocationAcceptedSizedLifting.below_one, fault⟩
  | _ =>
    exfalso
    obtain rfl := CellAwareInvocationAcceptedSizedLifting.same_node unique found (by assumption)
    simp_all

private theorem uninitialized_fault_inv (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) {binder : TypedBinder}
    (form : node.form = .letDecl binder none) (monomorphic : binder.scheme.quantified = [])
    (fault : SourceExecutionSize.StatementFaults program size context evidence source environment before id
      reason after) : False := by
  cases fault with
  | missing absent => exact Dynamic.StatementAbsentIn.excludes_contains absent (lookupStatement?_sound found)
  | polymorphicLet contains formEq polymorphic _ =>
    obtain rfl := CellAwareInvocationAcceptedSizedLifting.same_node unique found contains
    rw [form] at formEq
    cases formEq
    exact polymorphic monomorphic
  | _ =>
    obtain rfl := CellAwareInvocationAcceptedSizedLifting.same_node unique found (by assumption)
    simp_all

private theorem assigned_fault_inv (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) {assignment : AssignmentResolution}
    {operator : Syntax.ValueAssignOp} {expression : ExpressionId}
    (form : node.form = .assignValue assignment operator expression)
    (fault : SourceExecutionSize.StatementFaults program size context evidence source environment before id
      reason after) :
    ∃ child, child < size ∧ SourceExecutionSize.SourcePlaceAssignmentFaults program child context evidence source
      environment before assignment.target operator expression reason after := by
  cases fault with
  | missing absent => exact (Dynamic.StatementAbsentIn.excludes_contains absent (lookupStatement?_sound found)).elim
  | assignValue contains formEq fault =>
    obtain rfl := CellAwareInvocationAcceptedSizedLifting.same_node unique found contains
    rw [form] at formEq
    cases formEq
    exact ⟨_, CellAwareInvocationAcceptedSizedLifting.below_one, fault⟩
  | _ =>
    exfalso
    obtain rfl := CellAwareInvocationAcceptedSizedLifting.same_node unique found (by assumption)
    simp_all

private theorem bitNotted_fault_inv (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) {assignment : AssignmentResolution}
    (form : node.form = .assignBitNot assignment)
    (fault : SourceExecutionSize.StatementFaults program size context evidence source environment before id
      reason after) :
    ∃ child, child < size ∧ SourceExecutionSize.SourcePlaceBitNotFaults program child context evidence source
      environment before assignment.target reason after := by
  cases fault with
  | missing absent => exact (Dynamic.StatementAbsentIn.excludes_contains absent (lookupStatement?_sound found)).elim
  | assignBitNot contains formEq fault =>
    obtain rfl := CellAwareInvocationAcceptedSizedLifting.same_node unique found contains
    rw [form] at formEq
    cases formEq
    exact ⟨_, CellAwareInvocationAcceptedSizedLifting.below_one, fault⟩
  | _ =>
    exfalso
    obtain rfl := CellAwareInvocationAcceptedSizedLifting.same_node unique found (by assumption)
    simp_all

private theorem expression_fault_inv (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) {expression : ExpressionId} {semicolon : Bool}
    (form : node.form = .expression expression semicolon)
    (fault : SourceExecutionSize.StatementFaults program size context evidence source environment before id
      reason after) :
    ∃ child, child < size ∧ SourceExecutionSize.ExpressionFaults program child context evidence source environment
      before expression reason after := by
  cases fault with
  | missing absent => exact (Dynamic.StatementAbsentIn.excludes_contains absent (lookupStatement?_sound found)).elim
  | expression contains formEq fault =>
    obtain rfl := CellAwareInvocationAcceptedSizedLifting.same_node unique found contains
    rw [form] at formEq
    cases formEq
    exact ⟨_, CellAwareInvocationAcceptedSizedLifting.below_one, fault⟩
  | _ =>
    exfalso
    obtain rfl := CellAwareInvocationAcceptedSizedLifting.same_node unique found (by assumption)
    simp_all

private theorem block_fault_inv (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) {statements : List StatementId}
    (form : node.form = .block statements)
    (fault : SourceExecutionSize.StatementFaults program size context evidence source environment before id
      reason after) :
    ∃ child innerContext, child < size ∧ SourceExecutionSize.StatementsFault program child context evidence source
      environment before statements innerContext reason after := by
  cases fault with
  | missing absent => exact (Dynamic.StatementAbsentIn.excludes_contains absent (lookupStatement?_sound found)).elim
  | block contains formEq fault =>
    obtain rfl := CellAwareInvocationAcceptedSizedLifting.same_node unique found contains
    rw [form] at formEq
    cases formEq
    exact ⟨_, _, CellAwareInvocationAcceptedSizedLifting.below_one, fault⟩
  | _ =>
    exfalso
    obtain rfl := CellAwareInvocationAcceptedSizedLifting.same_node unique found (by assumption)
    simp_all

private theorem conditional_fault_inv (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) {condition : ExpressionId} {thenBody : List StatementId}
    {elseBody : Option (List StatementId)} (form : node.form = .ifThen condition thenBody elseBody)
    (fault : SourceExecutionSize.StatementFaults program size context evidence source environment before id
      reason after) :
    (∃ test, test < size ∧ SourceExecutionSize.ExpressionFaults program test context evidence source environment
      before condition reason after) ∨
    (∃ expected actual, reason = .typeMismatch expected actual) ∨
    (∃ test inner truth middle innerContext, test < size ∧ inner < size ∧
      SourceExecutionSize.ExpressionEvaluates program test context evidence source environment before condition
        (.bool truth) middle ∧
      SourceExecutionSize.StatementsFault program inner context evidence source environment middle
        (if truth then thenBody else elseBody.getD []) innerContext reason after) := by
  cases fault with
  | missing absent => exact (Dynamic.StatementAbsentIn.excludes_contains absent (lookupStatement?_sound found)).elim
  | ifCondition contains formEq fault =>
    obtain rfl := CellAwareInvocationAcceptedSizedLifting.same_node unique found contains
    rw [form] at formEq
    cases formEq
    exact .inl ⟨_, CellAwareInvocationAcceptedSizedLifting.below_one, fault⟩
  | ifConditionType => exact .inr (.inl ⟨_, _, rfl⟩)
  | ifTrueBody contains formEq test fault =>
    obtain rfl := CellAwareInvocationAcceptedSizedLifting.same_node unique found contains
    rw [form] at formEq
    cases formEq
    exact .inr (.inr ⟨_, _, true, _, _, CellAwareInvocationAcceptedSizedLifting.below_left,
      CellAwareInvocationAcceptedSizedLifting.below_right, test, fault⟩)
  | ifFalseBody contains formEq test fault =>
    obtain rfl := CellAwareInvocationAcceptedSizedLifting.same_node unique found contains
    rw [form] at formEq
    cases formEq
    exact .inr (.inr ⟨_, _, false, _, _, CellAwareInvocationAcceptedSizedLifting.below_left,
      CellAwareInvocationAcceptedSizedLifting.below_right, test, fault⟩)
  | _ =>
    exfalso
    obtain rfl := CellAwareInvocationAcceptedSizedLifting.same_node unique found (by assumption)
    simp_all

private theorem jump_fault_inv (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .breakStmt ∨ node.form = .continueStmt)
    (fault : SourceExecutionSize.StatementFaults program size context evidence source environment before id
      reason after) : False := by
  cases fault with
  | missing absent => exact Dynamic.StatementAbsentIn.excludes_contains absent (lookupStatement?_sound found)
  | _ =>
    obtain rfl := CellAwareInvocationAcceptedSizedLifting.same_node unique found (by assumption)
    rcases form with form | form <;> simp_all

private theorem while_fault_inv (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) {condition : ExpressionId} {body : List StatementId}
    (form : node.form = .whileLoop condition body)
    (fault : SourceExecutionSize.StatementFaults program size context evidence source environment before id
      reason after) :
    ∃ child, child < size ∧ SourceExecutionSize.WhileFaults program child context evidence source environment before
      condition body reason after := by
  cases fault with
  | missing absent => exact (Dynamic.StatementAbsentIn.excludes_contains absent (lookupStatement?_sound found)).elim
  | whileIteration contains formEq fault =>
    obtain rfl := CellAwareInvocationAcceptedSizedLifting.same_node unique found contains
    rw [form] at formEq
    cases formEq
    exact ⟨_, CellAwareInvocationAcceptedSizedLifting.below_one, fault⟩
  | _ =>
    exfalso
    obtain rfl := CellAwareInvocationAcceptedSizedLifting.same_node unique found (by assumption)
    simp_all

private theorem for_fault_inv (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) {initializer : List ForItemForm} {condition : ExpressionId}
    {post : List ForItemForm} {body : List StatementId} (form : node.form = .forLoop initializer condition post body)
    (fault : SourceExecutionSize.StatementFaults program size context evidence source environment before id
      reason after) :
    (∃ child failedContext, child < size ∧ SourceExecutionSize.ForItemsFault program child context evidence source
      environment before initializer failedContext reason after) ∨
    (∃ first second loopContext loopEnvironment initialized, first < size ∧ second < size ∧
      SourceExecutionSize.ForItemsExecute program first context evidence source environment before initializer
        loopContext loopEnvironment initialized ∧
      SourceExecutionSize.ForLoopFaults program second loopContext evidence source loopEnvironment initialized
        condition post body reason after) := by
  cases fault with
  | missing absent => exact (Dynamic.StatementAbsentIn.excludes_contains absent (lookupStatement?_sound found)).elim
  | forInitializer contains formEq fault =>
    obtain rfl := CellAwareInvocationAcceptedSizedLifting.same_node unique found contains
    rw [form] at formEq
    cases formEq
    exact .inl ⟨_, _, CellAwareInvocationAcceptedSizedLifting.below_one, fault⟩
  | forIteration contains formEq initial fault =>
    obtain rfl := CellAwareInvocationAcceptedSizedLifting.same_node unique found contains
    rw [form] at formEq
    cases formEq
    exact .inr ⟨_, _, _, _, _, CellAwareInvocationAcceptedSizedLifting.below_left,
      CellAwareInvocationAcceptedSizedLifting.below_right, initial, fault⟩
  | _ =>
    exfalso
    obtain rfl := CellAwareInvocationAcceptedSizedLifting.same_node unique found (by assumption)
    simp_all
end Inversion

variable {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked) {program : Program}
  {registry : Staging.Recursive.Registry} {called : DeclarationInstantiation → Prop}
  {scope : Staging.Recursive.Scope} {expected : TypeSystem.Ty}

/-- An assignment whose bare target faults: its root is unbound or dangling. -/
private theorem bare_target_fault {mode : Bool} {id : StatementId} {rest : List StatementId} {node : StatementNode}
    {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    {size : Nat} {context : SourceSemantics.Context} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault}
    (contains : ContainsStatement scope.source id node) (form : node.form = .assignValue assignment operator rhs)
    (bare : assignment.target.projections = [])
    (failed : SourceExecutionSize.SourcePlaceFaults program size context scope.evidence scope.source environment
      before assignment.target reason after) :
    Staging.Recursive.StatementsIn program registry mode scope context environment before (id :: rest) context
      (.fault (.semantic reason)) after := by
  cases failed with
  | unbound missing => exact .assignBareUnbound contains form bare missing
  | dangling lookup missing => exact .assignBareDangling contains form bare lookup missing
  | projectionExpression _ _ failed =>
    rw [bare] at failed
    cases failed
  | danglingAfterProjections lookup _ evaluated missing =>
    rw [bare] at evaluated
    cases evaluated
    exact .assignBareDangling contains form bare lookup missing
  | projectionRead _ _ evaluated _ _ failed =>
    rw [bare] at evaluated
    cases evaluated
    cases failed
  | uninitialized _ _ evaluated _ _ _ projected =>
    rw [bare] at evaluated
    cases evaluated
    exact absurd rfl projected
  | elementPrefix projectionsEq _
  | elementIndex projectionsEq _ _ _
  | elementIndexType projectionsEq _ _ _ _ _
  | elementOutOfBounds projectionsEq _ _ _ _ _ _
  | elementUninitialized projectionsEq _ _ =>
    rw [bare] at projectionsEq
    simp at projectionsEq

/-- A sized Source fault in a path of mapping indices whose keys `child` admits
is a staged fault of its keys, given the value and fault liftings of `child`
below the size. -/
private theorem projections_fault {child : ExpressionId → Prop} {bound : Nat}
    (lift : ChildLifts program registry scope child bound)
    (faultLift : ChildFaultLifts program registry scope child bound) {context : SourceSemantics.Context}
    {environment : Dynamic.Environment} :
    ∀ {projections : List PlaceProjection},
    (∀ projection ∈ projections, ∃ key, projection = .index key ∧ child key) →
    ∀ {size : Nat} {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault}, size ≤ bound →
      context.signatures = program.signatures → Expressible reason →
      SourceExecutionSize.SourceProjectionsFault program size context scope.evidence scope.source environment
        before projections reason after →
      Staging.Recursive.Expressions program registry scope context environment before
        (Staging.Recursive.ProjectedTarget.keys projections) (.fault (.semantic reason)) after := by
  intro projections
  induction projections with
  | nil =>
    intro _ size before after reason _ _ _ failed
    cases failed
  | cons projection rest ih =>
    intro keys size before after reason within signatures expressible failed
    obtain ⟨key, rfl, admitted⟩ := keys projection List.mem_cons_self
    cases failed with
    | indexHead failed =>
      simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at within
      exact .headFault (faultLift admitted (by omega) signatures expressible failed)
    | indexTail head failed =>
      simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at within
      exact .tailFault (lift admitted (by omega) head)
        (ih (fun other member => keys other (List.mem_cons_of_mem _ member)) (by omega) signatures expressible failed)

/-- A read through a non-empty path, or from a present value, selects a value. -/
private theorem read_selects : ∀ {start : Option Dynamic.Value} {evaluated : List Dynamic.EvaluatedProjection}
    {result : Option Dynamic.Value}, Dynamic.ProjectionsRead start evaluated result →
    (∃ value, start = some value) ∨ evaluated ≠ [] → ∃ value, result = some value := by
  intro start evaluated result read
  induction read with
  | nil =>
    intro present
    rcases present with ⟨value, rfl⟩ | nonempty
    · exact ⟨value, rfl⟩
    · exact absurd rfl nonempty
  | indexFound _ _ ih => intro _; exact ih (.inl ⟨_, rfl⟩)
  | indexDefault _ _ _ ih => intro _; exact ih (.inl ⟨_, rfl⟩)
  | member _ _ ih => intro _; exact ih (.inl ⟨_, rfl⟩)
  | element _ _ ih => intro _; exact ih (.inl ⟨_, rfl⟩)

/-- A non-empty path of projections evaluates to a non-empty path. -/
private theorem evaluated_nonempty {size : Nat} {context : SourceSemantics.Context}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {projections : List PlaceProjection}
    {evaluated : List Dynamic.EvaluatedProjection} (projected : projections ≠ [])
    (evaluate : SourceExecutionSize.SourceProjectionsEvaluate program size context scope.evidence scope.source
      environment before projections evaluated after) : evaluated ≠ [] := by
  cases evaluate with
  | nil => exact absurd rfl projected
  | member _ => exact List.cons_ne_nil _ _
  | index _ _ => exact List.cons_ne_nil _ _

/-- One statement followed by the rest of its list, over sized fault
derivations. A faulting head ends the list at its context; a falling-through
head is followed by a fault in the rest. -/
private theorem sequence_fault {mode : Bool} {id : StatementId} {rest : List StatementId} {node : StatementNode}
    {size : Nat} {reason : Dynamic.SemanticFault} (unique : NodeOccurrencesUnique scope.source)
    (found : scope.source.lookupStatement? id = some node)
    (notTail : ∀ expression, node.form ≠ .expression expression false)
    (step : ∀ {context environment before middleContext nextEnvironment middle finalContext after}
        {headSize tailSize : Nat}, headSize < size → tailSize < size → context.signatures = program.signatures →
      SourceExecutionSize.StatementExecutes program headSize context scope.evidence scope.source environment before id
        middleContext (.fallthrough nextEnvironment) middle →
      FaultOriginal program tailSize mode middleContext scope.evidence scope.source nextEnvironment middle rest
        finalContext reason after →
      Staging.Recursive.StatementsIn program registry mode scope context environment before (id :: rest)
        finalContext (.fault (.semantic reason)) after)
    (stop : ∀ {context environment before after} {headSize : Nat}, headSize < size →
      context.signatures = program.signatures →
      SourceExecutionSize.StatementFaults program headSize context scope.evidence scope.source environment before id
        reason after →
      Staging.Recursive.StatementsIn program registry mode scope context environment before (id :: rest)
        context (.fault (.semantic reason)) after) :
    ∀ {context environment before finalContext after}, context.signatures = program.signatures →
      FaultOriginal program size mode context scope.evidence scope.source environment before (id :: rest)
        finalContext reason after →
      Staging.Recursive.StatementsIn program registry mode scope context environment before (id :: rest)
        finalContext (.fault (.semantic reason)) after := by
  intro context environment before finalContext after signatures original
  cases mode with
  | false =>
    unfold FaultOriginal at original
    cases original with
    | head fault => exact stop CellAwareInvocationAcceptedSizedLifting.below_one signatures fault
    | tail head next =>
      exact step CellAwareInvocationAcceptedSizedLifting.below_left CellAwareInvocationAcceptedSizedLifting.below_right
        signatures head next
  | true =>
    unfold FaultOriginal at original
    cases original with
    | singleton fault => exact stop CellAwareInvocationAcceptedSizedLifting.below_one signatures fault
    | tailExpression contains form _ =>
      obtain rfl := CellAwareInvocationAcceptedSizedLifting.same_node unique found contains
      exact absurd form (notTail _)
    | head fault => exact stop CellAwareInvocationAcceptedSizedLifting.below_one signatures fault
    | tail head next =>
      exact step CellAwareInvocationAcceptedSizedLifting.below_left CellAwareInvocationAcceptedSizedLifting.below_right
        signatures head next

/-- The sized Source fault of a `while` loop whose condition `child` admits and
whose body lifts within the bound, with an expressible reason at a context with
the program's signatures, is a staged fault of the loop with the same heap. -/
private theorem while_fault_lift {child : ExpressionId → Prop} {bound : Nat}
    (lift : ChildLifts program registry scope child bound)
    (faultLift : ChildFaultLifts program registry scope child bound) {condition : ExpressionId}
    {body : List StatementId} (test : child condition)
    (inner : ∀ {size : Nat} {context environment before innerContext outcome after}, size ≤ bound →
      SourceExecutionSize.StatementsExecute program size context scope.evidence scope.source environment before body
        innerContext outcome after →
      Staging.Recursive.StatementsIn program registry false scope context environment before body innerContext
        (CellAwareInvocationAcceptedStatementLifting.control outcome) after)
    (innerFault : ∀ {size : Nat} {context environment before innerContext after} {reason : Dynamic.SemanticFault},
      size ≤ bound → context.signatures = program.signatures → Expressible reason →
      SourceExecutionSize.StatementsFault program size context scope.evidence scope.source environment before body
        innerContext reason after →
      Staging.Recursive.StatementsIn program registry false scope context environment before body innerContext
        (.fault (.semantic reason)) after) :
    ∀ {size : Nat} {context : SourceSemantics.Context} {environment : Dynamic.Environment}
      {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault},
      size ≤ bound → context.signatures = program.signatures → Expressible reason →
      SourceExecutionSize.WhileFaults program size context scope.evidence scope.source environment before condition
        body reason after →
      Staging.Recursive.While program registry scope context environment before condition body
        (.fault (.semantic reason)) after := by
  intro size
  induction size using Nat.strongRecOn with
  | ind size ih =>
    intro context environment before after reason within signatures expressible failed
    cases failed with
    | condition fault =>
      exact .conditionFault (faultLift test
        (Nat.lt_of_lt_of_le CellAwareInvocationAcceptedSizedLifting.below_one within) signatures expressible fault)
    | conditionType => simp [Expressible] at expressible
    | body evaluate fault =>
      exact .bodyFault (lift test (Nat.lt_of_lt_of_le CellAwareInvocationAcceptedSizedLifting.below_left within)
        evaluate)
        (innerFault (Nat.le_of_lt (Nat.lt_of_lt_of_le CellAwareInvocationAcceptedSizedLifting.below_right within))
          signatures expressible fault)
    | nextFallthrough evaluate executes fault =>
      have below := within
      simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
      exact .next (lift test (by omega) evaluate) (inner (by omega) executes)
        (ih _ (SourceExecutionSize.child_lt_stepSize (by simp)) (by omega) signatures expressible fault)
    | nextContinue evaluate executes fault =>
      have below := within
      simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
      exact .continueNext (lift test (by omega) evaluate) (inner (by omega) executes)
        (ih _ (SourceExecutionSize.child_lt_stepSize (by simp)) (by omega) signatures expressible fault)

/-- A header assignment whose bare target faults: its root is unbound or
dangling. -/
private theorem items_bare_target_fault {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp}
    {rhs : ExpressionId} {rest : List ForItemForm} {size : Nat} {context : SourceSemantics.Context}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault}
    (bare : assignment.target.projections = [])
    (failed : SourceExecutionSize.SourcePlaceFaults program size context scope.evidence scope.source environment
      before assignment.target reason after) :
    Staging.Recursive.ForItems program registry scope context environment before
      (.assignValue assignment operator rhs :: rest) context (.fault (.semantic reason)) after := by
  cases failed with
  | unbound missing => exact .unbound bare missing
  | dangling lookup missing => exact .dangling bare lookup missing
  | projectionExpression _ _ failed =>
    rw [bare] at failed
    cases failed
  | danglingAfterProjections lookup _ evaluated missing =>
    rw [bare] at evaluated
    cases evaluated
    exact .dangling bare lookup missing
  | projectionRead _ _ evaluated _ _ failed =>
    rw [bare] at evaluated
    cases evaluated
    cases failed
  | uninitialized _ _ evaluated _ _ _ projected =>
    rw [bare] at evaluated
    cases evaluated
    exact absurd rfl projected
  | elementPrefix projectionsEq _
  | elementIndex projectionsEq _ _ _
  | elementIndexType projectionsEq _ _ _ _ _
  | elementOutOfBounds projectionsEq _ _ _ _ _ _
  | elementUninitialized projectionsEq _ _ =>
    rw [bare] at projectionsEq
    simp at projectionsEq

/-- The sized Source fault of a supported header vector whose expressions
`child` admits, with an expressible reason at a context with the program's
signatures, is a staged fault of the vector with the same heap, given the value
and fault liftings of `child` within the bound. -/
private theorem items_fault_lift {child : ExpressionId → Prop} {bound : Nat}
    (lift : ChildLifts program registry scope child bound)
    (faultLift : ChildFaultLifts program registry scope child bound) {items : List ForItemForm}
    (shape : CellAwareInvocationAcceptedBodyShape.ItemsShape scope.source child items) :
    ∀ {size : Nat} {context : SourceSemantics.Context} {environment : Dynamic.Environment}
      {before after : Dynamic.Heap} {failedContext : SourceSemantics.Context} {reason : Dynamic.SemanticFault},
      size ≤ bound → context.signatures = program.signatures → Expressible reason →
      SourceExecutionSize.ForItemsFault program size context scope.evidence scope.source environment before items
        failedContext reason after →
      Staging.Recursive.ForItems program registry scope context environment before items failedContext
        (.fault (.semantic reason)) after := by
  induction shape with
  | nil =>
    intro size context environment before after failedContext reason _ _ _ failed
    cases failed
  | absent monomorphic _ tailIH =>
    intro size context environment before after failedContext reason within signatures expressible failed
    cases failed with
    | head fault =>
      cases fault with
      | polymorphicLet polymorphic _ => exact absurd monomorphic polymorphic
    | tail head fault =>
      cases head with
      | letUninitialized _ extension allocate =>
        exact .absent monomorphic extension allocate
          (tailIH (Nat.le_of_lt (Nat.lt_of_lt_of_le CellAwareInvocationAcceptedSizedLifting.below_right within))
            (extension.context_fields.1.trans signatures) expressible fault)
  | initialized monomorphic value _ tailIH =>
    intro size context environment before after failedContext reason within signatures expressible failed
    cases failed with
    | head fault =>
      cases fault with
      | polymorphicLet polymorphic _ => exact absurd monomorphic polymorphic
      | letInitializer _ fault =>
        have below := within
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
        exact .initializerFault monomorphic (faultLift value (by omega) signatures expressible fault)
    | tail head fault =>
      cases head with
      | letInitialized evaluate _ extension allocate =>
        have below := within
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
        exact .initialized monomorphic extension (lift value (by omega) evaluate) allocate
          (tailIH (by omega) (extension.context_fields.1.trans signatures) expressible fault)
      | letInitializedGeneralized _ _ polymorphic => exact absurd monomorphic polymorphic
  | discarded value _ tailIH =>
    intro size context environment before after failedContext reason within signatures expressible failed
    cases failed with
    | head fault =>
      cases fault with
      | expression fault =>
        have below := within
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
        exact .expressionFailure (faultLift value (by omega) signatures expressible fault)
    | tail head fault =>
      cases head with
      | expression evaluate =>
        have below := within
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
        exact .expression (lift value (by omega) evaluate) (tailIH (by omega) signatures expressible fault)
  | assigned assignable value _ tailIH =>
    intro size context environment before after failedContext reason within signatures expressible failed
    cases failed with
    | head fault =>
      cases fault with
      | assignValue fault =>
        cases fault with
        | target failed => exact items_bare_target_fault assignable.2.1 failed
        | rhs resolve failed =>
          have below := within
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
          obtain ⟨rfl, snapshot⟩ := Staging.Recursive.BareTarget.of_resolves assignable.2.1 resolve.sound
          exact .assignmentFailure snapshot (faultLift value (by omega) signatures expressible failed)
        | operands resolve evaluate currentRead rootType initialValue pathRead invalid =>
          have below := within
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
          obtain ⟨rfl, snapshot⟩ := Staging.Recursive.BareTarget.of_resolves assignable.2.1 resolve.sound
          exact .assignmentOperands snapshot (lift value (by omega) evaluate) currentRead rootType initialValue
            pathRead invalid
        | panic resolve evaluate currentRead rootType initialValue pathRead panics =>
          have below := within
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
          obtain ⟨rfl, snapshot⟩ := Staging.Recursive.BareTarget.of_resolves assignable.2.1 resolve.sound
          exact .assignmentPanic snapshot (lift value (by omega) evaluate) currentRead rootType initialValue
            pathRead panics
        | structuralUpdate resolve _ _ _ _ failed =>
          obtain ⟨rfl, snapshot⟩ := Staging.Recursive.BareTarget.of_resolves assignable.2.1 resolve.sound
          cases snapshot
          cases failed
    | tail head fault =>
      cases head with
      | assignValue executes =>
        cases executes with
        | intro resolve evaluate write =>
          have below := within
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
          obtain ⟨rfl, snapshot⟩ := Staging.Recursive.BareTarget.of_resolves assignable.2.1 resolve.sound
          exact .assignment snapshot (lift value (by omega) evaluate) write
            (tailIH (by omega) signatures expressible fault)
  | projectedAssigned assignable keys value _ tailIH =>
    intro size context environment before after failedContext reason within signatures expressible failed
    cases failed with
    | head fault =>
      cases fault with
      | assignValue fault =>
        cases fault with
        | target failed =>
          cases failed with
          | unbound missing => exact .projectedAssignmentRootFault assignable.2.1 (.unbound missing)
          | dangling lookup missing => exact .projectedAssignmentRootFault assignable.2.1 (.dangling lookup missing)
          | projectionExpression lookup read failed =>
            have below := within
            simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
            exact .projectedAssignmentKeysFault assignable.2.1 (.intro lookup read)
              (projections_fault lift faultLift keys (by omega) signatures expressible failed)
          | danglingAfterProjections lookup read evaluate missing =>
            have below := within
            simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
            obtain ⟨values, staged, ordered⟩ :=
              CellAwareInvocationAcceptedSizedLifting.projections_values lift keys (by omega) evaluate
            exact .projectedAssignmentGetterFault assignable.2.1 staged (.dangling lookup read ordered missing)
          | projectionRead lookup initialRead evaluate currentRead initialValue failed =>
            have below := within
            simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
            obtain ⟨values, staged, ordered⟩ :=
              CellAwareInvocationAcceptedSizedLifting.projections_values lift keys (by omega) evaluate
            exact .projectedAssignmentGetterFault assignable.2.1 staged
              (.projection lookup initialRead ordered currentRead initialValue failed)
          | uninitialized lookup initialRead evaluate currentRead empty notMapping nonempty =>
            have below := within
            simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
            obtain ⟨values, staged, ordered⟩ :=
              CellAwareInvocationAcceptedSizedLifting.projections_values lift keys (by omega) evaluate
            exact .projectedAssignmentGetterFault assignable.2.1 staged
              (.uninitialized lookup initialRead ordered currentRead empty notMapping nonempty)
          | elementPrefix projectionsEq _
          | elementIndex projectionsEq _ _ _
          | elementIndexType projectionsEq _ _ _ _ _
          | elementOutOfBounds projectionsEq _ _ _ _ _ _
          | elementUninitialized projectionsEq _ _ =>
            exact absurd projectionsEq (CellAwareInvocationAcceptedBodyShape.indices_no_element keys)
        | rhs resolve failed =>
          have below := within
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
          obtain ⟨values, staged, snapshot⟩ :=
            CellAwareInvocationAcceptedSizedLifting.projected_target lift keys (by omega) resolve
          exact .projectedAssignmentRhsFault assignable.2.1 staged snapshot
            (faultLift value (by omega) signatures expressible failed)
        | operands resolve evaluate currentRead rootType initialValue pathRead invalid =>
          have below := within
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
          obtain ⟨values, staged, snapshot⟩ :=
            CellAwareInvocationAcceptedSizedLifting.projected_target lift keys (by omega) resolve
          exact .projectedAssignmentWriteFault assignable.2.1 staged snapshot (lift value (by omega) evaluate)
            (.operands currentRead rootType initialValue pathRead invalid)
        | panic resolve evaluate currentRead rootType initialValue pathRead panics =>
          have below := within
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
          obtain ⟨values, staged, snapshot⟩ :=
            CellAwareInvocationAcceptedSizedLifting.projected_target lift keys (by omega) resolve
          exact .projectedAssignmentWriteFault assignable.2.1 staged snapshot (lift value (by omega) evaluate)
            (.panic currentRead rootType initialValue pathRead panics)
        | structuralUpdate resolve evaluate currentRead rootType initialValue failed =>
          have below := within
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
          obtain ⟨values, staged, snapshot⟩ :=
            CellAwareInvocationAcceptedSizedLifting.projected_target lift keys (by omega) resolve
          exact .projectedAssignmentWriteFault assignable.2.1 staged snapshot (lift value (by omega) evaluate)
            (.structural currentRead rootType initialValue failed)
    | tail head fault =>
      cases head with
      | assignValue executes =>
        cases executes with
        | intro resolve evaluate write =>
          have below := within
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
          obtain ⟨values, staged, snapshot⟩ :=
            CellAwareInvocationAcceptedSizedLifting.projected_target lift keys (by omega) resolve
          exact .projectedAssignment assignable.2.1 staged snapshot (lift value (by omega) evaluate) write
            (tailIH (by omega) signatures expressible fault)
  | bitNotted assignable _ tailIH =>
    intro size context environment before after failedContext reason within signatures expressible failed
    cases failed with
    | head fault =>
      cases fault with
      | assignBitNot fault =>
        have unchanged := Staging.Recursive.bitNot_fault_heap assignable.2.1 fault.sound
        subst unchanged
        exact .bitNotFault assignable.2.1 fault.sound
    | tail head fault =>
      cases head with
      | assignBitNot executes =>
        cases executes with
        | intro resolve write =>
          have below := within
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
          obtain ⟨rfl, snapshot⟩ := Staging.Recursive.BareTarget.of_resolves assignable.2.1 resolve.sound
          exact .bitNot snapshot write (tailIH (by omega) signatures expressible fault)
  | projectedBitNotted assignable keys _ tailIH =>
    intro size context environment before after failedContext reason within signatures expressible failed
    cases failed with
    | head fault =>
      cases fault with
      | assignBitNot fault =>
        cases fault with
        | target failed =>
          cases failed with
          | unbound missing => exact .projectedBitNotRootFault assignable.2.1 (.unbound missing)
          | dangling lookup missing => exact .projectedBitNotRootFault assignable.2.1 (.dangling lookup missing)
          | projectionExpression lookup read failed =>
            have below := within
            simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
            exact .projectedBitNotKeysFault assignable.2.1 (.intro lookup read)
              (projections_fault lift faultLift keys (by omega) signatures expressible failed)
          | danglingAfterProjections lookup read evaluate missing =>
            have below := within
            simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
            obtain ⟨values, staged, ordered⟩ :=
              CellAwareInvocationAcceptedSizedLifting.projections_values lift keys (by omega) evaluate
            exact .projectedBitNotGetterFault assignable.2.1 staged (.dangling lookup read ordered missing)
          | projectionRead lookup initialRead evaluate currentRead initialValue failed =>
            have below := within
            simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
            obtain ⟨values, staged, ordered⟩ :=
              CellAwareInvocationAcceptedSizedLifting.projections_values lift keys (by omega) evaluate
            exact .projectedBitNotGetterFault assignable.2.1 staged
              (.projection lookup initialRead ordered currentRead initialValue failed)
          | uninitialized lookup initialRead evaluate currentRead empty notMapping nonempty =>
            have below := within
            simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
            obtain ⟨values, staged, ordered⟩ :=
              CellAwareInvocationAcceptedSizedLifting.projections_values lift keys (by omega) evaluate
            exact .projectedBitNotGetterFault assignable.2.1 staged
              (.uninitialized lookup initialRead ordered currentRead empty notMapping nonempty)
          | elementPrefix projectionsEq _
          | elementIndex projectionsEq _ _ _
          | elementIndexType projectionsEq _ _ _ _ _
          | elementOutOfBounds projectionsEq _ _ _ _ _ _
          | elementUninitialized projectionsEq _ _ =>
            exact absurd projectionsEq (CellAwareInvocationAcceptedBodyShape.indices_no_element keys)
        | uninitialized resolve empty =>
          exfalso
          cases resolve with
          | intro _ _ evaluate _ _ selection =>
            obtain ⟨_, present⟩ := read_selects selection (.inr (evaluated_nonempty assignable.2.1 evaluate))
            cases present.symm.trans empty
          | element projectionsEq =>
            exact absurd projectionsEq (CellAwareInvocationAcceptedBodyShape.indices_no_element keys)
        | operand resolve selected invalid =>
          have below := within
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
          obtain ⟨values, staged, snapshot⟩ :=
            CellAwareInvocationAcceptedSizedLifting.projected_target lift keys (by omega) resolve
          exact .projectedBitNotOperandFault assignable.2.1 staged snapshot selected invalid
    | tail head fault =>
      cases head with
      | assignBitNot executes =>
        cases executes with
        | intro resolve write =>
          have below := within
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
          obtain ⟨values, staged, snapshot⟩ :=
            CellAwareInvocationAcceptedSizedLifting.projected_target lift keys (by omega) resolve
          exact .projectedBitNot assignable.2.1 staged snapshot write (tailIH (by omega) signatures expressible fault)

/-- The sized Source fault of a `for` loop whose condition `child` admits,
whose body lifts within the bound and whose post header is supported, with an
expressible reason at a context with the program's signatures, is a staged
fault of the loop with the same heap. -/
private theorem for_fault_lift {child : ExpressionId → Prop} {bound : Nat}
    (lift : ChildLifts program registry scope child bound)
    (faultLift : ChildFaultLifts program registry scope child bound) {condition : ExpressionId}
    {post : List ForItemForm} {body : List StatementId} (test : child condition)
    (inner : ∀ {size : Nat} {context environment before innerContext outcome after}, size ≤ bound →
      SourceExecutionSize.StatementsExecute program size context scope.evidence scope.source environment before body
        innerContext outcome after →
      Staging.Recursive.StatementsIn program registry false scope context environment before body innerContext
        (CellAwareInvocationAcceptedStatementLifting.control outcome) after)
    (innerFault : ∀ {size : Nat} {context environment before innerContext after} {reason : Dynamic.SemanticFault},
      size ≤ bound → context.signatures = program.signatures → Expressible reason →
      SourceExecutionSize.StatementsFault program size context scope.evidence scope.source environment before body
        innerContext reason after →
      Staging.Recursive.StatementsIn program registry false scope context environment before body innerContext
        (.fault (.semantic reason)) after)
    (postShape : CellAwareInvocationAcceptedBodyShape.ItemsShape scope.source child post) :
    ∀ {size : Nat} {context : SourceSemantics.Context} {environment : Dynamic.Environment}
      {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault},
      size ≤ bound → context.signatures = program.signatures → Expressible reason →
      SourceExecutionSize.ForLoopFaults program size context scope.evidence scope.source environment before
        condition post body reason after →
      Staging.Recursive.ForLoop program registry scope context environment before condition post body
        (.fault (.semantic reason)) after := by
  intro size
  induction size using Nat.strongRecOn with
  | ind size ih =>
    intro context environment before after reason within signatures expressible failed
    cases failed with
    | condition fault =>
      exact .testFault (faultLift test
        (Nat.lt_of_lt_of_le CellAwareInvocationAcceptedSizedLifting.below_one within) signatures expressible fault)
    | conditionType => simp [Expressible] at expressible
    | body evaluate fault =>
      exact .bodyFailure (lift test (Nat.lt_of_lt_of_le CellAwareInvocationAcceptedSizedLifting.below_left within)
        evaluate)
        (innerFault (Nat.le_of_lt (Nat.lt_of_lt_of_le CellAwareInvocationAcceptedSizedLifting.below_right within))
          signatures expressible fault)
    | postFallthrough evaluate executes fault =>
      have below := within
      simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
      exact .postFailure (lift test (by omega) evaluate) (inner (by omega) executes)
        (items_fault_lift lift faultLift postShape (by omega) signatures expressible fault)
    | postContinue evaluate executes fault =>
      have below := within
      simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
      exact .continuePostFailure (lift test (by omega) evaluate) (inner (by omega) executes)
        (items_fault_lift lift faultLift postShape (by omega) signatures expressible fault)
    | nextFallthrough evaluate executes postExecutes fault =>
      have below := within
      simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
      exact .iterate (lift test (by omega) evaluate) (inner (by omega) executes)
        (CellAwareInvocationAcceptedSizedLifting.items_lift lift postShape (by omega) postExecutes).1
        (ih _ (SourceExecutionSize.child_lt_stepSize (by simp)) (by omega) signatures expressible fault)
    | nextContinue evaluate executes postExecutes fault =>
      have below := within
      simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at below
      exact .continueIterate (lift test (by omega) evaluate) (inner (by omega) executes)
        (CellAwareInvocationAcceptedSizedLifting.items_lift lift postShape (by omega) postExecutes).1
        (ih _ (SourceExecutionSize.child_lt_stepSize (by simp)) (by omega) signatures expressible fault)

/-- The sized Source fault of a match whose scrutinee `child` admits and whose selected body's faults lift
within the bound, with an expressible reason at a context with the program's signatures, is a staged fault of
the match with the same heap: a fault of its scrutinee, an invalid pattern, or a fault of its selected body. -/
private theorem match_fault {child : ExpressionId → Prop} {bound : Nat} (unique : NodeOccurrencesUnique scope.source)
    (lift : ChildLifts program registry scope child bound)
    (faultLift : ChildFaultLifts program registry scope child bound) {id : StatementId} {node : StatementNode}
    (found : scope.source.lookupStatement? id = some node) {resolution : MatchResolution}
    (form : node.form = .matchWith resolution) (scrutinee : child resolution.scrutinee)
    {reason : Dynamic.SemanticFault}
    (body : ∀ {statements : List StatementId}, ((∃ arm ∈ resolution.cases, arm.body = statements) ∨
        resolution.defaultBody = some statements) →
      ∀ {size : Nat} {context environment before innerContext after}, size ≤ bound →
      context.signatures = program.signatures →
      SourceExecutionSize.StatementsFault program size context scope.evidence scope.source environment before
        statements innerContext reason after →
      Staging.Recursive.StatementsIn program registry false scope context environment before statements
        innerContext (.fault (.semantic reason)) after)
    {size : Nat} {context : SourceSemantics.Context} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} (within : size ≤ bound) (signatures : context.signatures = program.signatures)
    (expressible : Expressible reason)
    (fault : SourceExecutionSize.StatementFaults program size context scope.evidence scope.source environment
      before id reason after) :
    Staging.Recursive.Match program registry scope context environment before resolution
      (.fault (.semantic reason)) after := by
  cases fault with
  | missing absent => exact (Dynamic.StatementAbsentIn.excludes_contains absent (lookupStatement?_sound found)).elim
  | matchScrutinee contains formEq failed =>
    obtain rfl := CellAwareInvocationAcceptedSizedLifting.same_node unique found contains
    rw [form] at formEq
    cases formEq
    exact .scrutineeFault (faultLift scrutinee
      (Nat.lt_of_lt_of_le CellAwareInvocationAcceptedSizedLifting.below_one within) signatures expressible failed)
  | matchPattern contains formEq scrutineeContains evaluate allocate invalid =>
    obtain rfl := CellAwareInvocationAcceptedSizedLifting.same_node unique found contains
    rw [form] at formEq
    cases formEq
    exact .patternFault scrutineeContains
      (lift scrutinee (Nat.lt_of_lt_of_le CellAwareInvocationAcceptedSizedLifting.below_one within) evaluate)
      allocate invalid
  | matchArmBody contains formEq scrutineeContains evaluate allocate select bindersEq valuesEq extended allocated
      failed =>
    obtain rfl := CellAwareInvocationAcceptedSizedLifting.same_node unique found contains
    rw [form] at formEq
    cases formEq
    subst bindersEq valuesEq
    obtain ⟨arm, member, same⟩ := (CellAwareInvocationAcceptedStatementLifting.selected_body select).1 _ _ rfl
    exact .arm scrutineeContains
      (lift scrutinee (Nat.lt_of_lt_of_le CellAwareInvocationAcceptedSizedLifting.below_left within) evaluate)
      allocate select extended allocated
      (body (.inl ⟨arm, member, same⟩)
        (Nat.le_of_lt (Nat.lt_of_lt_of_le CellAwareInvocationAcceptedSizedLifting.below_right within))
        (extended.signatures_eq.trans signatures) failed)
  | matchDefaultBody contains formEq scrutineeContains evaluate allocate select failed =>
    obtain rfl := CellAwareInvocationAcceptedSizedLifting.same_node unique found contains
    rw [form] at formEq
    cases formEq
    exact .default scrutineeContains
      (lift scrutinee (Nat.lt_of_lt_of_le CellAwareInvocationAcceptedSizedLifting.below_left within) evaluate)
      allocate select
      (body (.inr ((CellAwareInvocationAcceptedStatementLifting.selected_body select).2 _ rfl))
        (Nat.le_of_lt (Nat.lt_of_lt_of_le CellAwareInvocationAcceptedSizedLifting.below_right within))
        signatures failed)
  | _ =>
    exfalso
    clear lift faultLift body
    obtain rfl := CellAwareInvocationAcceptedSizedLifting.same_node unique found (by assumption)
    simp_all

/-- A sized fault execution of a supported statement list with an expressible
reason, at a context with the program's signatures, is a staged fault
execution with the same context, reason and heap, given the value and fault
liftings of its expressions below the size. -/
theorem statements_fault (unique : NodeOccurrencesUnique scope.source) {child : ExpressionId → Prop} {bound : Nat}
    (lift : ChildLifts program registry scope child bound)
    (faultLift : ChildFaultLifts program registry scope child bound) {mode : Bool} {statements : List StatementId}
    (shape : Shape scope.source expected child mode statements) :
    ∀ {size : Nat} {context : SourceSemantics.Context} {environment : Dynamic.Environment}
      {before after : Dynamic.Heap} {finalContext : SourceSemantics.Context} {reason : Dynamic.SemanticFault},
      size ≤ bound → context.signatures = program.signatures → Expressible reason →
      FaultOriginal program size mode context scope.evidence scope.source environment before statements finalContext
        reason after →
      Staging.Recursive.StatementsIn program registry mode scope context environment before statements finalContext
        (.fault (.semantic reason)) after := by
  induction shape with
  | @nil mode _ =>
    intro size context environment before after finalContext reason _ _ _ original
    cases mode <;> unfold FaultOriginal at original <;> cases original
  | returned found form value =>
    intro size context environment before after finalContext reason within signatures expressible original
    refine sequence_fault unique found (fun _ same => by rw [form] at same; cases same) ?_ ?_ signatures original
    · intro context environment before middleContext nextEnvironment middle finalContext after _ _ _ _ _ head _
      obtain ⟨_, _, _, _, _, impossible⟩ := CellAwareInvocationAcceptedSizedLifting.returned_inv unique found form head
      cases impossible
    · intro context environment before after headSize headBelow signatures fault
      obtain ⟨_, childBelow, fault⟩ := return_fault_inv unique found form fault
      exact .returnFault (lookupStatement?_sound found) form
        (faultLift value (by omega) signatures expressible fault)
  | returnUnit found form =>
    intro size context environment before after finalContext reason _ signatures _ original
    refine sequence_fault unique found (fun _ same => by rw [form] at same; cases same) ?_ ?_ signatures original
    · intro context environment before middleContext nextEnvironment middle finalContext after _ _ _ _ _ head _
      obtain ⟨_, impossible, _⟩ := CellAwareInvocationAcceptedSizedLifting.return_unit_inv unique found form head
      cases impossible
    · intro context environment before after _ _ _ fault
      exact (return_unit_fault_inv unique found form fault).elim
  | declared found form monomorphic value _ tailIH =>
    intro size context environment before after finalContext reason within signatures expressible original
    refine sequence_fault unique found (fun _ same => by rw [form] at same; cases same) ?_ ?_ signatures original
    · intro context environment before middleContext nextEnvironment middle finalContext after headSize
        tailSize headBelow tailBelow signatures head next
      obtain ⟨_, _, _, _, childBelow, evaluate, extension, allocate, same⟩ :=
        CellAwareInvocationAcceptedSizedLifting.declared_inv unique found form monomorphic head
      cases same
      exact .letInitialized (lookupStatement?_sound found) form (lift value (by omega) evaluate)
        monomorphic extension allocate
        (tailIH (by omega) (extension.context_fields.1.trans signatures) expressible next)
    · intro context environment before after headSize headBelow signatures fault
      obtain ⟨_, childBelow, fault⟩ := declared_fault_inv unique found form monomorphic fault
      exact .letFault (lookupStatement?_sound found) form monomorphic
        (faultLift value (by omega) signatures expressible fault)
  | uninitialized found form monomorphic _ tailIH =>
    intro size context environment before after finalContext reason within signatures expressible original
    refine sequence_fault unique found (fun _ same => by rw [form] at same; cases same) ?_ ?_ signatures original
    · intro context environment before middleContext nextEnvironment middle finalContext after headSize
        tailSize headBelow tailBelow signatures head next
      obtain ⟨_, extension, allocate, same⟩ :=
        CellAwareInvocationAcceptedSizedLifting.uninitialized_inv unique found form head
      cases same
      exact .letUninitialized (lookupStatement?_sound found) form monomorphic extension allocate
        (tailIH (by omega) (extension.context_fields.1.trans signatures) expressible next)
    · intro context environment before after _ _ _ fault
      exact (uninitialized_fault_inv unique found form monomorphic fault).elim
  | assigned found form assignable value _ tailIH =>
    intro size context environment before after finalContext reason within signatures expressible original
    refine sequence_fault unique found (fun _ same => by rw [form] at same; cases same) ?_ ?_ signatures original
    · intro context environment before middleContext nextEnvironment middle finalContext after headSize
        tailSize headBelow tailBelow signatures head next
      obtain ⟨_, _, childBelow, executes, rfl, same⟩ :=
        CellAwareInvocationAcceptedSizedLifting.assigned_inv unique found form head
      cases same
      cases executes with
      | intro resolve evaluate write =>
        obtain ⟨rfl, snapshot⟩ := Staging.Recursive.BareTarget.of_resolves assignable.2.1 resolve.sound
        exact .assignBare (lookupStatement?_sound found) form snapshot
          (lift value (by
            simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at childBelow
            omega) evaluate)
          write (tailIH (by omega) signatures expressible next)
    · intro context environment before after headSize headBelow signatures fault
      have contains := lookupStatement?_sound found
      obtain ⟨_, childBelow, fault⟩ := assigned_fault_inv unique found form fault
      cases fault with
      | target failed => exact bare_target_fault contains form assignable.2.1 failed
      | rhs resolve failed =>
        obtain ⟨rfl, snapshot⟩ := Staging.Recursive.BareTarget.of_resolves assignable.2.1 resolve.sound
        exact .assignBareFault contains form snapshot
          (faultLift value (by
            simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at childBelow
            omega) signatures expressible failed)
      | operands resolve evaluate currentRead rootType initialValue pathRead invalid =>
        obtain ⟨rfl, snapshot⟩ := Staging.Recursive.BareTarget.of_resolves assignable.2.1 resolve.sound
        exact .assignBareOperands contains form snapshot
          (lift value (by
            simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at childBelow
            omega) evaluate) currentRead rootType initialValue pathRead invalid
      | panic resolve evaluate currentRead rootType initialValue pathRead panics =>
        obtain ⟨rfl, snapshot⟩ := Staging.Recursive.BareTarget.of_resolves assignable.2.1 resolve.sound
        exact .assignBarePanic contains form snapshot
          (lift value (by
            simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at childBelow
            omega) evaluate) currentRead rootType initialValue pathRead panics
      | structuralUpdate resolve _ _ _ _ failed =>
        obtain ⟨rfl, snapshot⟩ := Staging.Recursive.BareTarget.of_resolves assignable.2.1 resolve.sound
        cases snapshot
        cases failed
  | projectedAssigned found form assignable keys value _ tailIH =>
    intro size context environment before after finalContext reason within signatures expressible original
    refine sequence_fault unique found (fun _ same => by rw [form] at same; cases same) ?_ ?_ signatures original
    · intro context environment before middleContext nextEnvironment middle finalContext after headSize
        tailSize headBelow tailBelow signatures head next
      obtain ⟨_, _, childBelow, executes, rfl, same⟩ :=
        CellAwareInvocationAcceptedSizedLifting.assigned_inv unique found form head
      cases same
      cases executes with
      | intro resolve evaluate write =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at childBelow
        obtain ⟨values, staged, snapshot⟩ :=
          CellAwareInvocationAcceptedSizedLifting.projected_target lift keys (by omega) resolve
        exact .assignProjected (lookupStatement?_sound found) form assignable.2.1 staged snapshot
          (lift value (by omega) evaluate) write (tailIH (by omega) signatures expressible next)
    · intro context environment before after headSize headBelow signatures fault
      have contains := lookupStatement?_sound found
      obtain ⟨_, childBelow, fault⟩ := assigned_fault_inv unique found form fault
      cases fault with
      | target failed =>
        cases failed with
        | unbound missing => exact .assignProjectedRootFault contains form assignable.2.1 (.unbound missing)
        | dangling lookup missing =>
          exact .assignProjectedRootFault contains form assignable.2.1 (.dangling lookup missing)
        | projectionExpression lookup read failed =>
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at childBelow
          exact .assignProjectedKeysFault contains form assignable.2.1 (.intro lookup read)
            (projections_fault lift faultLift keys (by omega) signatures expressible failed)
        | danglingAfterProjections lookup read evaluate missing =>
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at childBelow
          obtain ⟨values, staged, ordered⟩ :=
            CellAwareInvocationAcceptedSizedLifting.projections_values lift keys (by omega) evaluate
          exact .assignProjectedGetterFault contains form assignable.2.1 staged (.dangling lookup read ordered missing)
        | projectionRead lookup initialRead evaluate currentRead initialValue failed =>
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at childBelow
          obtain ⟨values, staged, ordered⟩ :=
            CellAwareInvocationAcceptedSizedLifting.projections_values lift keys (by omega) evaluate
          exact .assignProjectedGetterFault contains form assignable.2.1 staged
            (.projection lookup initialRead ordered currentRead initialValue failed)
        | uninitialized lookup initialRead evaluate currentRead empty notMapping nonempty =>
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at childBelow
          obtain ⟨values, staged, ordered⟩ :=
            CellAwareInvocationAcceptedSizedLifting.projections_values lift keys (by omega) evaluate
          exact .assignProjectedGetterFault contains form assignable.2.1 staged
            (.uninitialized lookup initialRead ordered currentRead empty notMapping nonempty)
        | elementPrefix projectionsEq _
        | elementIndex projectionsEq _ _ _
        | elementIndexType projectionsEq _ _ _ _ _
        | elementOutOfBounds projectionsEq _ _ _ _ _ _
        | elementUninitialized projectionsEq _ _ =>
          exact absurd projectionsEq (CellAwareInvocationAcceptedBodyShape.indices_no_element keys)
      | rhs resolve failed =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at childBelow
        obtain ⟨values, staged, snapshot⟩ :=
          CellAwareInvocationAcceptedSizedLifting.projected_target lift keys (by omega) resolve
        exact .assignProjectedRhsFault contains form assignable.2.1 staged snapshot
          (faultLift value (by omega) signatures expressible failed)
      | operands resolve evaluate currentRead rootType initialValue pathRead invalid =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at childBelow
        obtain ⟨values, staged, snapshot⟩ :=
          CellAwareInvocationAcceptedSizedLifting.projected_target lift keys (by omega) resolve
        exact .assignProjectedWriteFault contains form assignable.2.1 staged snapshot (lift value (by omega) evaluate)
          (.operands currentRead rootType initialValue pathRead invalid)
      | panic resolve evaluate currentRead rootType initialValue pathRead panics =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at childBelow
        obtain ⟨values, staged, snapshot⟩ :=
          CellAwareInvocationAcceptedSizedLifting.projected_target lift keys (by omega) resolve
        exact .assignProjectedWriteFault contains form assignable.2.1 staged snapshot (lift value (by omega) evaluate)
          (.panic currentRead rootType initialValue pathRead panics)
      | structuralUpdate resolve evaluate currentRead rootType initialValue failed =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at childBelow
        obtain ⟨values, staged, snapshot⟩ :=
          CellAwareInvocationAcceptedSizedLifting.projected_target lift keys (by omega) resolve
        exact .assignProjectedWriteFault contains form assignable.2.1 staged snapshot (lift value (by omega) evaluate)
          (.structural currentRead rootType initialValue failed)
  | bitNotted found form assignable _ tailIH =>
    intro size context environment before after finalContext reason within signatures expressible original
    refine sequence_fault unique found (fun _ same => by rw [form] at same; cases same) ?_ ?_ signatures original
    · intro context environment before middleContext nextEnvironment middle finalContext after headSize
        tailSize headBelow tailBelow signatures head next
      obtain ⟨_, _, _, executes, rfl, same⟩ :=
        CellAwareInvocationAcceptedSizedLifting.bitNotted_inv unique found form head
      cases same
      cases executes with
      | intro resolve write =>
        obtain ⟨rfl, snapshot⟩ := Staging.Recursive.BareTarget.of_resolves assignable.2.1 resolve.sound
        exact .bitNotBare (lookupStatement?_sound found) form snapshot write
          (tailIH (by omega) signatures expressible next)
    · intro context environment before after _ _ _ fault
      obtain ⟨_, _, fault⟩ := bitNotted_fault_inv unique found form fault
      have unchanged := Staging.Recursive.bitNot_fault_heap assignable.2.1 fault.sound
      subst unchanged
      exact .bitNotBareFault (lookupStatement?_sound found) form assignable.2.1 fault.sound
  | projectedBitNotted found form assignable keys _ tailIH =>
    intro size context environment before after finalContext reason within signatures expressible original
    refine sequence_fault unique found (fun _ same => by rw [form] at same; cases same) ?_ ?_ signatures original
    · intro context environment before middleContext nextEnvironment middle finalContext after headSize
        tailSize headBelow tailBelow signatures head next
      obtain ⟨_, _, childBelow, executes, rfl, same⟩ :=
        CellAwareInvocationAcceptedSizedLifting.bitNotted_inv unique found form head
      cases same
      cases executes with
      | intro resolve write =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at childBelow
        obtain ⟨values, staged, snapshot⟩ :=
          CellAwareInvocationAcceptedSizedLifting.projected_target lift keys (by omega) resolve
        exact .bitNotProjected (lookupStatement?_sound found) form assignable.2.1 staged snapshot write
          (tailIH (by omega) signatures expressible next)
    · intro context environment before after headSize headBelow signatures fault
      have contains := lookupStatement?_sound found
      obtain ⟨_, childBelow, fault⟩ := bitNotted_fault_inv unique found form fault
      cases fault with
      | target failed =>
        cases failed with
        | unbound missing => exact .bitNotProjectedRootFault contains form assignable.2.1 (.unbound missing)
        | dangling lookup missing =>
          exact .bitNotProjectedRootFault contains form assignable.2.1 (.dangling lookup missing)
        | projectionExpression lookup read failed =>
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at childBelow
          exact .bitNotProjectedKeysFault contains form assignable.2.1 (.intro lookup read)
            (projections_fault lift faultLift keys (by omega) signatures expressible failed)
        | danglingAfterProjections lookup read evaluate missing =>
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at childBelow
          obtain ⟨values, staged, ordered⟩ :=
            CellAwareInvocationAcceptedSizedLifting.projections_values lift keys (by omega) evaluate
          exact .bitNotProjectedGetterFault contains form assignable.2.1 staged (.dangling lookup read ordered missing)
        | projectionRead lookup initialRead evaluate currentRead initialValue failed =>
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at childBelow
          obtain ⟨values, staged, ordered⟩ :=
            CellAwareInvocationAcceptedSizedLifting.projections_values lift keys (by omega) evaluate
          exact .bitNotProjectedGetterFault contains form assignable.2.1 staged
            (.projection lookup initialRead ordered currentRead initialValue failed)
        | uninitialized lookup initialRead evaluate currentRead empty notMapping nonempty =>
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at childBelow
          obtain ⟨values, staged, ordered⟩ :=
            CellAwareInvocationAcceptedSizedLifting.projections_values lift keys (by omega) evaluate
          exact .bitNotProjectedGetterFault contains form assignable.2.1 staged
            (.uninitialized lookup initialRead ordered currentRead empty notMapping nonempty)
        | elementPrefix projectionsEq _
        | elementIndex projectionsEq _ _ _
        | elementIndexType projectionsEq _ _ _ _ _
        | elementOutOfBounds projectionsEq _ _ _ _ _ _
        | elementUninitialized projectionsEq _ _ =>
          exact absurd projectionsEq (CellAwareInvocationAcceptedBodyShape.indices_no_element keys)
      | uninitialized resolve empty =>
        exfalso
        cases resolve with
        | intro _ _ evaluate _ _ selection =>
          obtain ⟨_, present⟩ := read_selects selection (.inr (evaluated_nonempty assignable.2.1 evaluate))
          cases present.symm.trans empty
        | element projectionsEq =>
          exact absurd projectionsEq (CellAwareInvocationAcceptedBodyShape.indices_no_element keys)
      | operand resolve selected invalid =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at childBelow
        obtain ⟨values, staged, snapshot⟩ :=
          CellAwareInvocationAcceptedSizedLifting.projected_target lift keys (by omega) resolve
        exact .bitNotProjectedOperandFault contains form assignable.2.1 staged snapshot selected invalid
  | elementAssigned found form _ single index value _ tailIH =>
    intro size context environment before after finalContext reason within signatures expressible original
    refine sequence_fault unique found (fun _ same => by rw [form] at same; cases same) ?_ ?_ signatures original
    · intro context environment before middleContext nextEnvironment middle finalContext after headSize
        tailSize headBelow tailBelow signatures head next
      obtain ⟨_, _, childBelow, executes, rfl, same⟩ :=
        CellAwareInvocationAcceptedSizedLifting.assigned_inv unique found form head
      cases same
      cases executes with
      | intro resolve evaluate write =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at childBelow
        exact .assignElement (lookupStatement?_sound found) form (CellAwareElementTargetLifting.element_place single)
          (CellAwareElementTargetLifting.resolved_sized single (fun below trace => lift index (by omega) trace)
            resolve)
          (lift value (by omega) evaluate) write (tailIH (by omega) signatures expressible next)
    · intro context environment before after headSize headBelow signatures fault
      have contains := lookupStatement?_sound found
      have element := CellAwareElementTargetLifting.element_place single
      obtain ⟨_, childBelow, fault⟩ := assigned_fault_inv unique found form fault
      cases fault with
      | target failed =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at childBelow
        exact .assignElementTargetFault contains form element
          (CellAwareElementTargetLifting.fault_sized single (fun below trace => lift index (by omega) trace)
            (fun below trace => faultLift index (by omega) signatures expressible trace) failed)
      | rhs resolve failed =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at childBelow
        exact .assignElementRhsFault contains form element
          (CellAwareElementTargetLifting.resolved_sized single (fun below trace => lift index (by omega) trace)
            resolve)
          (faultLift value (by omega) signatures expressible failed)
      | operands resolve evaluate currentRead rootType initialValue pathRead invalid =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at childBelow
        exact .assignElementWriteFault contains form element
          (CellAwareElementTargetLifting.resolved_sized single (fun below trace => lift index (by omega) trace)
            resolve)
          (lift value (by omega) evaluate) (.operands currentRead rootType initialValue pathRead invalid)
      | panic resolve evaluate currentRead rootType initialValue pathRead panics =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at childBelow
        exact .assignElementWriteFault contains form element
          (CellAwareElementTargetLifting.resolved_sized single (fun below trace => lift index (by omega) trace)
            resolve)
          (lift value (by omega) evaluate) (.panic currentRead rootType initialValue pathRead panics)
      | structuralUpdate resolve evaluate currentRead rootType initialValue failed =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at childBelow
        exact .assignElementWriteFault contains form element
          (CellAwareElementTargetLifting.resolved_sized single (fun below trace => lift index (by omega) trace)
            resolve)
          (lift value (by omega) evaluate) (.structural currentRead rootType initialValue failed)
  | elementBitNotted found form _ single index _ tailIH =>
    intro size context environment before after finalContext reason within signatures expressible original
    refine sequence_fault unique found (fun _ same => by rw [form] at same; cases same) ?_ ?_ signatures original
    · intro context environment before middleContext nextEnvironment middle finalContext after headSize
        tailSize headBelow tailBelow signatures head next
      obtain ⟨_, _, childBelow, executes, rfl, same⟩ :=
        CellAwareInvocationAcceptedSizedLifting.bitNotted_inv unique found form head
      cases same
      cases executes with
      | intro resolve write =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at childBelow
        exact .bitNotElement (lookupStatement?_sound found) form (CellAwareElementTargetLifting.element_place single)
          (CellAwareElementTargetLifting.resolved_sized single (fun below trace => lift index (by omega) trace)
            resolve)
          write (tailIH (by omega) signatures expressible next)
    · intro context environment before after headSize headBelow signatures fault
      have contains := lookupStatement?_sound found
      have element := CellAwareElementTargetLifting.element_place single
      obtain ⟨_, childBelow, fault⟩ := bitNotted_fault_inv unique found form fault
      cases fault with
      | target failed =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at childBelow
        exact .bitNotElementTargetFault contains form element
          (CellAwareElementTargetLifting.fault_sized single (fun below trace => lift index (by omega) trace)
            (fun below trace => faultLift index (by omega) signatures expressible trace) failed)
      | uninitialized resolve empty =>
        exact absurd empty (CellAwareElementTargetLifting.selected_ne_none single resolve.sound)
      | operand resolve selected invalid =>
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at childBelow
        exact .bitNotElementOperandFault contains form element
          (CellAwareElementTargetLifting.resolved_sized single (fun below trace => lift index (by omega) trace)
            resolve)
          selected invalid
  | discarded found form value _ tailIH =>
    intro size context environment before after finalContext reason within signatures expressible original
    refine sequence_fault unique found (fun _ same => by rw [form] at same; cases same) ?_ ?_ signatures original
    · intro context environment before middleContext nextEnvironment middle finalContext after headSize
        tailSize headBelow tailBelow signatures head next
      obtain ⟨_, _, childBelow, evaluate, rfl, same⟩ :=
        CellAwareInvocationAcceptedSizedLifting.discarded_inv unique found form head
      cases same
      exact .discard (lookupStatement?_sound found) form (lift value (by omega) evaluate)
        (tailIH (by omega) signatures expressible next)
    · intro context environment before after headSize headBelow signatures fault
      obtain ⟨_, childBelow, fault⟩ := expression_fault_inv unique found form fault
      exact .expressionFault (lookupStatement?_sound found) form
        (faultLift value (by omega) signatures expressible fault)
  | block found form inner _ innerIH tailIH =>
    intro size context environment before after finalContext reason within signatures expressible original
    refine sequence_fault unique found (fun _ same => by rw [form] at same; cases same) ?_ ?_ signatures original
    · intro context environment before middleContext nextEnvironment middle finalContext after headSize
        tailSize headBelow tailBelow signatures head next
      obtain ⟨_, _, innerOutcome, innerBelow, executes, rfl, same⟩ :=
        CellAwareInvocationAcceptedSizedLifting.block_inv unique found form head
      cases innerOutcome with
      | fallthrough innerEnvironment =>
        cases same
        exact .blockFallthrough (lookupStatement?_sound found) form
          (CellAwareInvocationAcceptedSizedLifting.statements unique lift inner (by omega) executes)
          (tailIH (by omega) signatures expressible next)
      | _ => cases same
    · intro context environment before after headSize headBelow signatures fault
      obtain ⟨_, _, innerBelow, fault⟩ := block_fault_inv unique found form fault
      exact .blockFault (lookupStatement?_sound found) form (innerIH (by omega) signatures expressible fault)
  | @conditional mode id rest node condition thenBody elseBody found form test left right _ leftIH rightIH tailIH =>
    intro size context environment before after finalContext reason within signatures expressible original
    have branch : ∀ {truth : Bool} {innerSize : Nat} {context environment before innerContext inner after},
        innerSize ≤ bound →
        SourceExecutionSize.StatementsExecute program innerSize context scope.evidence scope.source environment before
          (if truth then thenBody else elseBody.getD []) innerContext inner after →
        Staging.Recursive.StatementsIn program registry false scope context environment before
          (if truth then thenBody else elseBody.getD []) innerContext
          (CellAwareInvocationAcceptedStatementLifting.control inner) after := by
      intro truth innerSize context environment before innerContext inner after within executes
      cases truth
      · exact CellAwareInvocationAcceptedSizedLifting.statements unique lift right within executes
      · exact CellAwareInvocationAcceptedSizedLifting.statements unique lift left within executes
    have branchFault : ∀ {truth : Bool} {innerSize : Nat} {context environment before innerContext after},
        innerSize ≤ bound → context.signatures = program.signatures →
        SourceExecutionSize.StatementsFault program innerSize context scope.evidence scope.source environment before
          (if truth then thenBody else elseBody.getD []) innerContext reason after →
        Staging.Recursive.StatementsIn program registry false scope context environment before
          (if truth then thenBody else elseBody.getD []) innerContext (.fault (.semantic reason)) after := by
      intro truth innerSize context environment before innerContext after within signatures failed
      cases truth
      · exact rightIH within signatures expressible failed
      · exact leftIH within signatures expressible failed
    refine sequence_fault unique found (fun _ same => by rw [form] at same; cases same) ?_ ?_ signatures original
    · intro context environment before middleContext nextEnvironment middle finalContext after headSize
        tailSize headBelow tailBelow signatures head next
      obtain ⟨rfl, _, _, truth, _, _, innerOutcome, testBelow, innerBelow, evaluate, executes, same⟩ :=
        CellAwareInvocationAcceptedSizedLifting.conditional_inv unique found form head
      cases innerOutcome with
      | fallthrough innerEnvironment =>
        cases same
        exact .ifFallthrough (lookupStatement?_sound found) form (lift test (by omega) evaluate)
          (branch (by omega) executes) (tailIH (by omega) signatures expressible next)
      | _ => cases same
    · intro context environment before after headSize headBelow signatures fault
      rcases conditional_fault_inv unique found form fault with
        ⟨_, testBelow, failed⟩ | ⟨_, _, rfl⟩ | ⟨_, _, truth, _, _, testBelow, innerBelow, evaluate, failed⟩
      · exact .ifConditionFault (lookupStatement?_sound found) form
          (faultLift test (by omega) signatures expressible failed)
      · simp [Expressible] at expressible
      · exact .ifFault (lookupStatement?_sound found) form (lift test (by omega) evaluate)
          (branchFault (by omega) signatures failed)
  | @matched mode id rest node resolution found form scrutinee arms fallback _ armsIH fallbackIH tailIH =>
    intro size context environment before after finalContext reason within signatures expressible original
    have body : ∀ {statements : List StatementId}, ((∃ arm ∈ resolution.cases, arm.body = statements) ∨
        resolution.defaultBody = some statements) →
        ∀ {innerSize : Nat} {context environment before innerContext inner after}, innerSize ≤ bound →
        SourceExecutionSize.StatementsExecute program innerSize context scope.evidence scope.source environment
          before statements innerContext inner after →
        Staging.Recursive.StatementsIn program registry false scope context environment before statements
          innerContext (CellAwareInvocationAcceptedStatementLifting.control inner) after := by
      intro statements selected innerSize context environment before innerContext inner after within executes
      rcases selected with ⟨arm, member, rfl⟩ | same
      · exact CellAwareInvocationAcceptedSizedLifting.statements unique lift (arms arm member) within executes
      · rw [same] at fallback
        exact CellAwareInvocationAcceptedSizedLifting.statements unique lift fallback within executes
    have bodyFault : ∀ {statements : List StatementId}, ((∃ arm ∈ resolution.cases, arm.body = statements) ∨
        resolution.defaultBody = some statements) →
        ∀ {innerSize : Nat} {context environment before innerContext after}, innerSize ≤ bound →
        context.signatures = program.signatures →
        SourceExecutionSize.StatementsFault program innerSize context scope.evidence scope.source environment
          before statements innerContext reason after →
        Staging.Recursive.StatementsIn program registry false scope context environment before statements
          innerContext (.fault (.semantic reason)) after := by
      intro statements selected innerSize context environment before innerContext after within signatures failed
      rcases selected with ⟨arm, member, rfl⟩ | same
      · exact armsIH arm member within signatures expressible failed
      · rw [same] at fallbackIH
        exact fallbackIH within signatures expressible failed
    refine sequence_fault unique found (fun _ same => by rw [form] at same; cases same) ?_ ?_ signatures original
    · intro context environment before middleContext nextEnvironment middle finalContext after headSize
        tailSize headBelow tailBelow signatures head next
      obtain ⟨rfl, inner, same, staged⟩ :=
        CellAwareInvocationAcceptedSizedLifting.match_lift unique lift found form scrutinee body (by omega) head
      cases inner with
      | fallthrough innerEnvironment =>
        cases same
        exact .matchFallthrough (lookupStatement?_sound found) form staged
          (tailIH (by omega) signatures expressible next)
      | _ => cases same
    · intro context environment before after headSize headBelow signatures fault
      exact .matchFault (lookupStatement?_sound found) form
        (match_fault unique lift faultLift found form scrutinee bodyFault (by omega) signatures expressible fault)
  | breaking found form =>
    intro size context environment before after finalContext reason _ signatures _ original
    refine sequence_fault unique found (fun _ same => by rw [form] at same; cases same) ?_ ?_ signatures original
    · intro context environment before middleContext nextEnvironment middle finalContext after _ _ _ _ _ head _
      obtain ⟨_, impossible, _⟩ := CellAwareInvocationAcceptedSizedLifting.break_inv unique found form head
      cases impossible
    · intro context environment before after _ _ _ fault
      exact (jump_fault_inv unique found (.inl form) fault).elim
  | continuing found form =>
    intro size context environment before after finalContext reason _ signatures _ original
    refine sequence_fault unique found (fun _ same => by rw [form] at same; cases same) ?_ ?_ signatures original
    · intro context environment before middleContext nextEnvironment middle finalContext after _ _ _ _ _ head _
      obtain ⟨_, impossible, _⟩ := CellAwareInvocationAcceptedSizedLifting.continue_inv unique found form head
      cases impossible
    · intro context environment before after _ _ _ fault
      exact (jump_fault_inv unique found (.inr form) fault).elim
  | whileLooped found form test inner _ innerIH tailIH =>
    intro size context environment before after finalContext reason within signatures expressible original
    refine sequence_fault unique found (fun _ same => by rw [form] at same; cases same) ?_ ?_ signatures original
    · intro context environment before middleContext nextEnvironment middle finalContext after headSize
        tailSize headBelow tailBelow signatures head next
      obtain ⟨_, _, loopOutcome, loopBelow, iterate, rfl, same⟩ :=
        CellAwareInvocationAcceptedSizedLifting.while_inv unique found form head
      obtain ⟨loop, ended⟩ := CellAwareInvocationAcceptedSizedLifting.while_lift lift test
        (fun within executes => CellAwareInvocationAcceptedSizedLifting.statements unique lift inner within executes)
        (by omega) iterate
      rcases ended with rfl | ⟨_, rfl⟩
      · cases same
        exact .whileFallthrough (lookupStatement?_sound found) form loop
          (tailIH (by omega) signatures expressible next)
      · cases same
    · intro context environment before after headSize headBelow signatures fault
      obtain ⟨_, loopBelow, failed⟩ := while_fault_inv unique found form fault
      exact .whileFault (lookupStatement?_sound found) form
        (while_fault_lift lift faultLift test
          (fun within executes => CellAwareInvocationAcceptedSizedLifting.statements unique lift inner within executes)
          (fun within signatures expressible failed => innerIH within signatures expressible failed)
          (by omega) signatures expressible failed)
  | forLooped found form initialItems test inner postItems _ innerIH tailIH =>
    intro size context environment before after finalContext reason within signatures expressible original
    refine sequence_fault unique found (fun _ same => by rw [form] at same; cases same) ?_ ?_ signatures original
    · intro context environment before middleContext nextEnvironment middle finalContext after headSize
        tailSize headBelow tailBelow signatures head next
      obtain ⟨_, _, _, _, _, _, loopOutcome, firstBelow, secondBelow, initialized, iterate, rfl, same⟩ :=
        CellAwareInvocationAcceptedSizedLifting.for_inv unique found form head
      obtain ⟨loop, ended⟩ := CellAwareInvocationAcceptedSizedLifting.for_lift lift test
        (fun within executes => CellAwareInvocationAcceptedSizedLifting.statements unique lift inner within executes)
        postItems (by omega) iterate
      rcases ended with rfl | ⟨_, rfl⟩
      · cases same
        exact .forFallthrough (lookupStatement?_sound found) form
          (CellAwareInvocationAcceptedSizedLifting.items_lift lift initialItems (by omega) initialized).1 loop
          (tailIH (by omega) signatures expressible next)
      · cases same
    · intro context environment before after headSize headBelow signatures fault
      rcases for_fault_inv unique found form fault with
        ⟨_, _, initialBelow, failed⟩ | ⟨_, _, _, _, _, firstBelow, secondBelow, initialized, failed⟩
      · exact .forInitializerFault (lookupStatement?_sound found) form
          (items_fault_lift lift faultLift initialItems (by omega) signatures expressible failed)
      · obtain ⟨initial, sameSignatures⟩ :=
          CellAwareInvocationAcceptedSizedLifting.items_lift lift initialItems (by omega) initialized
        exact .forFault (lookupStatement?_sound found) form initial
          (for_fault_lift lift faultLift test
            (fun within executes => CellAwareInvocationAcceptedSizedLifting.statements unique lift inner within executes)
            (fun within signatures expressible failed => innerIH within signatures expressible failed)
            postItems (by omega) (sameSignatures.trans signatures) expressible failed)
  | tail found form _ value =>
    intro size context environment before after finalContext reason within signatures expressible original
    unfold FaultOriginal at original
    cases original with
    | singleton fault =>
      obtain ⟨_, childBelow, fault⟩ := expression_fault_inv unique found form fault
      exact .expressionFault (lookupStatement?_sound found) form
        (faultLift value (by
          simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at within
          omega) signatures expressible fault)
    | tailExpression contains formEq fault =>
      obtain rfl := CellAwareInvocationAcceptedSizedLifting.same_node unique found contains
      rw [form] at formEq
      cases formEq
      exact .expressionFault (lookupStatement?_sound found) form
        (faultLift value (Nat.lt_of_lt_of_le CellAwareInvocationAcceptedSizedLifting.below_one within)
          signatures expressible fault)

/-- Every admitted callee's original body fault is a staged fault execution
at every size: the strong induction on the size across bodies that lifts
their values, given that their direct calls have plain callees. -/
theorem bodies_fault (callees : Callees prepared program registry called)
    (plain : CalleesFault program called) (bound : Nat) :
    BodiesFaultLift program registry called bound := by
  induction bound using Nat.strongRecOn with
  | ind bound ih =>
    intro instantiation bodyInstance statements admitted instantiates rootsEq
    obtain ⟨child, named, expected, closure, unique, shape⟩ := callees admitted instantiates rootsEq
    refine ⟨child, closure, ?_⟩
    intro size context environment before after finalContext reason below signatures expressible trace
    have sourceEq : child.source = bodyInstance.source := registry.source closure
    have evidenceEq : child.evidence = [] := registry.evidence closure
    have childUnique : NodeOccurrencesUnique child.source := sourceEq ▸ unique
    have childPlain : CalleesPlain child.source := sourceEq ▸ plain admitted instantiates
    have childShape : Shape child.source expected (Nested prepared named child.source called) true statements := by
      rw [sourceEq]
      exact shape
    have values : BodiesLift program registry called size :=
      CellAwareInvocationAcceptedCallLifting.bodies prepared callees size
    refine statements_fault childUnique
      (CellAwareInvocationAcceptedCallLifting.nested_roots prepared childUnique values)
      (nested_fault_roots prepared childUnique childPlain values (ih size below)) childShape (Nat.le_refl size)
      signatures expressible ?_
    show SourceExecutionSize.FunctionStatementsFault program size context child.evidence child.source environment
      before statements finalContext reason after
    rw [sourceEq, evidenceEq]
    exact trace

/-- An ordinary function-body fault of a supported list whose expressions are
nested sites, with an expressible reason at a context with the program's
signatures, is a staged fault execution with the same context, reason and
heap, at any scope with the execution's Source and evidence, given that the
direct calls of the body and of the admitted callees have plain callees and
the static receipts of the admitted callees. -/
theorem body_fault {scope : Staging.Recursive.Scope} {source : TypedSource} {evidence : Dynamic.EvidenceEnvironment}
    (sourceEq : scope.source = source) (evidenceEq : scope.evidence = evidence)
    (unique : NodeOccurrencesUnique source) (plain : CalleesPlain source)
    (callees : Callees prepared program registry called) (calleesPlain : CalleesFault program called)
    {named : SourceCoreGeneralFunctions.Function} {expected : TypeSystem.Ty} {statements : List StatementId}
    (shape : Shape source expected (Nested prepared named source called) true statements)
    {context : SourceSemantics.Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {finalContext : SourceSemantics.Context} {reason : Dynamic.SemanticFault}
    (signatures : context.signatures = program.signatures) (expressible : Expressible reason)
    (trace : Dynamic.FunctionStatementsFault program context evidence source environment before statements
      finalContext reason after) :
    ∃ size, Staging.Recursive.Size.Statements program registry size scope context environment before statements
      finalContext (.fault (.semantic reason)) after := by
  subst sourceEq evidenceEq
  obtain ⟨size, sized⟩ := SourceExecutionSize.FunctionStatementsFault.has_size trace
  have values : BodiesLift program registry called size :=
    CellAwareInvocationAcceptedCallLifting.bodies prepared callees size
  exact Staging.Recursive.Size.Statements.of_trace
    (statements_fault unique (CellAwareInvocationAcceptedCallLifting.nested_roots prepared unique values)
      (nested_fault_roots prepared unique plain values (bodies_fault prepared callees calleesPlain size)) shape
      (Nat.le_refl size) signatures expressible sized)

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedFaultLifting
end
