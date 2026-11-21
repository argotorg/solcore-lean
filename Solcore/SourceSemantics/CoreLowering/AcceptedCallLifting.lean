import Solcore.SourceSemantics.CoreLowering.AcceptedShapes
import Solcore.SourceSemantics.CoreLowering.AcceptedNestedCalls
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.SourceExecutionSize

/-!
# Accepted bodies: lifting call-containing Source traces

Original Source executions of call-containing bodies are staged executions.
The lifting of `CellAwareInvocationAcceptedStatementLifting` runs over sized
derivations, and a direct call's callee body, whose derivation is smaller than
the call's, is lifted by one strong induction on the size across bodies.

Main declarations:
- `CellAwareInvocationAcceptedSizedLifting.statements`, the sized lifting of a
  supported statement list given the lifting of its expressions below the size;
- `CellAwareInvocationAcceptedCallLifting.nested_value` and
  `CellAwareInvocationAcceptedCallLifting.nested_roots`, the value execution of
  every nested site;
- `CellAwareInvocationAcceptedCallLifting.bodies` and
  `CellAwareInvocationAcceptedCallLifting.body`, the induction across bodies and
  the staged trace of a call-containing body, given the static receipts of the
  admitted callees (`Callees`).
-/

section
/-! Sized original Source executions of supported statement lists are staged
executions, given the lifting of their expressions below the size. This is
`CellAwareInvocationAcceptedStatementLifting` over the sized derivations of
`SourceExecutionSize`: every child derivation has a smaller size than its
statement, so a child lifting below the size of a list is enough to lift the
list. Every control outcome is carried unchanged, with the context, environment
and heap of the original execution. Fault executions are not lifted here. -/
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
end Inversion

variable {program : Program} {registry : Staging.Recursive.Registry} {scope : Staging.Recursive.Scope}
  {expected : TypeSystem.Ty}

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

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedSizedLifting
end

section
/-! Original executions of bodies whose expressions are nested sites are
staged executions. A direct call's original rule runs the callee body, so the
lifting is one strong induction on the size of the original derivation across
bodies: at a call of a given size, the callee body's derivation is smaller, and
its lifting below that size gives the staged global application. A
conversion's original rule applies its builtin as the staged rule does. Inside one
body, a nested site is lifted by induction on the site, over the sized
derivations of its operands, branches, elements and arguments. The admitted
callees are static inputs (`Callees`): the registry scope of each callee's
global view at the empty dictionary and the shape of its body, whose
expressions are nested sites of its own cache row. Fault executions are not
lifted here. -/
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
