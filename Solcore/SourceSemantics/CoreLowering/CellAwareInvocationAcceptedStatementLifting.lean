import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedBodyShape
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedSourceLifting

/-! Original Source executions of supported statement lists are staged
executions. Every statement of `CellAwareInvocationAcceptedBodyShape.Shape`
runs the same rule in both semantics once its subset expressions are staged:
declarations allocate the same cell, a bare assignment resolves its target
without changing the heap and writes it by the same rule, and blocks and
conditional arms restore their entry bindings while keeping their heap. Each
control outcome is carried unchanged, with the context, environment and heap
of the original execution. Fault executions are not lifted here. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedStatementLifting
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (Prepared)
open CellAwareInvocationAcceptedExpressionTrees (Subset)
open CellAwareInvocationAcceptedBodyShape (Shape)
open CellAwareInvocationAcceptedSourceLifting (expression_value)

/-- An ordinary control outcome as a staged body outcome. -/
def control : Dynamic.ControlOutcome → Staging.Recursive.BodyOutcome
  | .fallthrough environment => .fallthrough environment
  | .returned value => .returned value
  | .breaking environment => .breaking environment
  | .continuing environment => .continuing environment
  | .fault reason => .fault (.semantic reason)

/-- The ordinary statement-list judgment of each compiler mode: a function body
has the implicit final return, a branch or block body does not. -/
def Original (program : Program) : Bool → SourceSemantics.Context → Dynamic.EvidenceEnvironment → TypedSource →
    Dynamic.Environment → Dynamic.Heap → List StatementId → SourceSemantics.Context → Dynamic.ControlOutcome →
    Dynamic.Heap → Prop
  | true => Dynamic.FunctionStatementsExecute program
  | false => Dynamic.StatementsExecute program

section Inversion
variable {program : Program} {source : TypedSource} {context finalContext : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
  {id : StatementId} {node : StatementNode} {outcome : Dynamic.ControlOutcome}

private theorem same_node (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    {other : StatementNode} (contains : ContainsStatement source id other) : other = node :=
  Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)

private theorem returned_inv (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    {expression : ExpressionId} (form : node.form = .returnStmt (some expression))
    (head : Dynamic.StatementExecutes program context evidence source environment before id finalContext outcome after) :
    ∃ value, Dynamic.ExpressionEvaluates program context evidence source environment before expression value after ∧
      finalContext = context ∧ outcome = .returned value := by
  cases head with
  | returnValue contains formEq evaluate =>
    obtain rfl := same_node unique found contains
    rw [form] at formEq
    cases formEq
    exact ⟨_, evaluate, rfl, rfl⟩
  | _ =>
    exfalso
    obtain rfl := same_node unique found (by assumption)
    simp_all

private theorem return_unit_inv (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (form : node.form = .returnStmt none)
    (head : Dynamic.StatementExecutes program context evidence source environment before id finalContext outcome after) :
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
    (head : Dynamic.StatementExecutes program context evidence source environment before id finalContext outcome after) :
    ∃ value middle location,
      Dynamic.ExpressionEvaluates program context evidence source environment before expression value middle ∧
      BinderExtends source.owner context binder finalContext ∧
      Dynamic.Heap.Allocates middle binder.scheme.body (some value) location after ∧
      outcome = .fallthrough ((binder.id, location) :: environment) := by
  cases head with
  | letInitialized contains formEq evaluate _ extension allocate =>
    obtain rfl := same_node unique found contains
    rw [form] at formEq
    cases formEq
    exact ⟨_, _, _, evaluate, extension, allocate, rfl⟩
  | letInitializedGeneralized contains formEq _ polymorphic _ _ =>
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
    (head : Dynamic.StatementExecutes program context evidence source environment before id finalContext outcome after) :
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
    (head : Dynamic.StatementExecutes program context evidence source environment before id finalContext outcome after) :
    ∃ updatedRoot, Dynamic.SourcePlaceAssignment program context evidence source
        (Dynamic.AssignmentValueApplies operator) environment before assignment.target expression updatedRoot after ∧
      finalContext = context ∧ outcome = .fallthrough environment := by
  cases head with
  | assignValue contains formEq executes =>
    obtain rfl := same_node unique found contains
    rw [form] at formEq
    cases formEq
    exact ⟨_, executes, rfl, rfl⟩
  | _ =>
    exfalso
    obtain rfl := same_node unique found (by assumption)
    simp_all

private theorem discarded_inv (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    {expression : ExpressionId} (form : node.form = .expression expression true)
    (head : Dynamic.StatementExecutes program context evidence source environment before id finalContext outcome after) :
    ∃ value, Dynamic.ExpressionEvaluates program context evidence source environment before expression value after ∧
      finalContext = context ∧ outcome = .fallthrough environment := by
  cases head with
  | expression contains formEq evaluate =>
    obtain rfl := same_node unique found contains
    rw [form] at formEq
    cases formEq
    exact ⟨_, evaluate, rfl, rfl⟩
  | _ =>
    exfalso
    obtain rfl := same_node unique found (by assumption)
    simp_all

private theorem block_inv (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    {statements : List StatementId} (form : node.form = .block statements)
    (head : Dynamic.StatementExecutes program context evidence source environment before id finalContext outcome after) :
    ∃ innerContext inner,
      Dynamic.StatementsExecute program context evidence source environment before statements innerContext inner after ∧
      finalContext = context ∧ outcome = Dynamic.restoreControl environment inner := by
  cases head with
  | block contains formEq executes =>
    obtain rfl := same_node unique found contains
    rw [form] at formEq
    cases formEq
    exact ⟨_, _, executes, rfl, rfl⟩
  | _ =>
    exfalso
    obtain rfl := same_node unique found (by assumption)
    simp_all

private theorem conditional_inv (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) {condition : ExpressionId} {thenBody : List StatementId}
    {elseBody : Option (List StatementId)} (form : node.form = .ifThen condition thenBody elseBody)
    (head : Dynamic.StatementExecutes program context evidence source environment before id finalContext outcome after) :
    finalContext = context ∧ ∃ truth middle innerContext inner,
      Dynamic.ExpressionEvaluates program context evidence source environment before condition (.bool truth) middle ∧
      Dynamic.StatementsExecute program context evidence source environment middle
        (if truth then thenBody else elseBody.getD []) innerContext inner after ∧
      outcome = Dynamic.restoreControl environment inner := by
  cases head with
  | ifTrue contains formEq test executes =>
    obtain rfl := same_node unique found contains
    rw [form] at formEq
    cases formEq
    exact ⟨rfl, true, _, _, _, test, executes, rfl⟩
  | ifFalseWithoutElse contains formEq test =>
    obtain rfl := same_node unique found contains
    rw [form] at formEq
    cases formEq
    exact ⟨rfl, false, _, _, _, test, .nil, rfl⟩
  | ifFalseWithElse contains formEq test executes =>
    obtain rfl := same_node unique found contains
    rw [form] at formEq
    cases formEq
    exact ⟨rfl, false, _, _, _, test, executes, rfl⟩
  | _ =>
    exfalso
    obtain rfl := same_node unique found (by assumption)
    simp_all
end Inversion

variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
  {named : SourceCoreGeneralFunctions.Function} {program : Program} {registry : Staging.Recursive.Registry}
  {scope : Staging.Recursive.Scope} {expected : TypeSystem.Ty}

/-- One statement followed by the rest of its list. A falling-through head runs
the rest; a terminal head ends the list. Both compiler modes share this
sequencing, except for the function body's implicit final value, which the
head form excludes. -/
private theorem sequence {mode : Bool} {id : StatementId} {rest : List StatementId} {node : StatementNode}
    (unique : NodeOccurrencesUnique scope.source) (found : scope.source.lookupStatement? id = some node)
    (notTail : ∀ expression, node.form ≠ .expression expression false)
    (step : ∀ {context environment before middleContext nextEnvironment middle finalContext outcome after},
      Dynamic.StatementExecutes program context scope.evidence scope.source environment before id middleContext
        (.fallthrough nextEnvironment) middle →
      Original program mode middleContext scope.evidence scope.source nextEnvironment middle rest finalContext
        outcome after →
      Staging.Recursive.StatementsIn program registry mode scope context environment before (id :: rest)
        finalContext (control outcome) after)
    (stop : ∀ {context environment before finalContext outcome after},
      Dynamic.StatementExecutes program context scope.evidence scope.source environment before id finalContext
        outcome after →
      Dynamic.TerminalControl outcome →
      Staging.Recursive.StatementsIn program registry mode scope context environment before (id :: rest)
        finalContext (control outcome) after) :
    ∀ {context environment before finalContext outcome after},
      Original program mode context scope.evidence scope.source environment before (id :: rest) finalContext
        outcome after →
      Staging.Recursive.StatementsIn program registry mode scope context environment before (id :: rest)
        finalContext (control outcome) after := by
  intro context environment before finalContext outcome after original
  cases mode with
  | false =>
    unfold Original at original
    cases original with
    | cons head next => exact step head next
    | terminal head terminal => exact stop head terminal
  | true =>
    unfold Original at original
    cases original with
    | tailExpression contains form _ =>
      obtain rfl := same_node unique found contains
      exact absurd form (notTail _)
    | singleton _ _ head =>
      cases outcome with
      | fallthrough nextEnvironment => exact step head .nil
      | returned value => exact stop head (.returned value)
      | breaking environment => exact stop head (.breaking environment)
      | continuing environment => exact stop head (.continuing environment)
      | fault reason => exact stop head (.fault reason)
    | cons head next => exact step head next
    | terminal head terminal => exact stop head terminal

/-- An ordinary execution of a supported statement list whose expressions are
subset sites is a staged execution with the same context, outcome and heap. -/
theorem statements (unique : NodeOccurrencesUnique scope.source) {mode : Bool} {statements : List StatementId}
    (shape : Shape scope.source expected (Subset prepared named scope.source) mode statements) :
    ∀ {context : SourceSemantics.Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
      {finalContext : SourceSemantics.Context} {outcome : Dynamic.ControlOutcome},
      Original program mode context scope.evidence scope.source environment before statements finalContext
        outcome after →
      Staging.Recursive.StatementsIn program registry mode scope context environment before statements finalContext
        (control outcome) after := by
  induction shape with
  | @nil mode _ =>
    intro context environment before after finalContext outcome original
    cases mode <;> unfold Original at original <;> cases original <;> exact .nil
  | returned found form value =>
    intro context environment before after finalContext outcome
    apply sequence unique found (fun _ same => by rw [form] at same; cases same)
    · intro context environment before middleContext nextEnvironment middle finalContext outcome after head _
      obtain ⟨_, _, _, impossible⟩ := returned_inv unique found form head
      cases impossible
    · intro context environment before finalContext outcome after head _
      obtain ⟨_, evaluate, rfl, rfl⟩ := returned_inv unique found form head
      exact .returnValue (lookupStatement?_sound found) form (expression_value unique value evaluate)
  | returnUnit found form =>
    intro context environment before after finalContext outcome
    apply sequence unique found (fun _ same => by rw [form] at same; cases same)
    · intro context environment before middleContext nextEnvironment middle finalContext outcome after head _
      obtain ⟨_, impossible, _⟩ := return_unit_inv unique found form head
      cases impossible
    · intro context environment before finalContext outcome after head _
      obtain ⟨rfl, rfl, rfl⟩ := return_unit_inv unique found form head
      exact .returnUnit (lookupStatement?_sound found) form
  | declared found form monomorphic value _ tailIH =>
    intro context environment before after finalContext outcome
    apply sequence unique found (fun _ same => by rw [form] at same; cases same)
    · intro context environment before middleContext nextEnvironment middle finalContext outcome after head next
      obtain ⟨_, _, _, evaluate, extension, allocate, same⟩ := declared_inv unique found form monomorphic head
      cases same
      exact .letInitialized (lookupStatement?_sound found) form (expression_value unique value evaluate)
        monomorphic extension allocate (tailIH next)
    · intro context environment before finalContext outcome after head terminal
      obtain ⟨_, _, _, _, _, _, same⟩ := declared_inv unique found form monomorphic head
      subst same
      cases terminal
  | uninitialized found form monomorphic _ tailIH =>
    intro context environment before after finalContext outcome
    apply sequence unique found (fun _ same => by rw [form] at same; cases same)
    · intro context environment before middleContext nextEnvironment middle finalContext outcome after head next
      obtain ⟨_, extension, allocate, same⟩ := uninitialized_inv unique found form head
      cases same
      exact .letUninitialized (lookupStatement?_sound found) form monomorphic extension allocate (tailIH next)
    · intro context environment before finalContext outcome after head terminal
      obtain ⟨_, _, _, same⟩ := uninitialized_inv unique found form head
      subst same
      cases terminal
  | assigned found form assignable value _ tailIH =>
    intro context environment before after finalContext outcome
    apply sequence unique found (fun _ same => by rw [form] at same; cases same)
    · intro context environment before middleContext nextEnvironment middle finalContext outcome after head next
      obtain ⟨_, executes, rfl, same⟩ := assigned_inv unique found form head
      cases same
      cases executes with
      | intro resolve evaluate write =>
        obtain ⟨rfl, snapshot⟩ := Staging.Recursive.BareTarget.of_resolves assignable.2.1 resolve
        exact .assignBare (lookupStatement?_sound found) form snapshot (expression_value unique value evaluate)
          write (tailIH next)
    · intro context environment before finalContext outcome after head terminal
      obtain ⟨_, _, _, same⟩ := assigned_inv unique found form head
      subst same
      cases terminal
  | discarded found form value _ tailIH =>
    intro context environment before after finalContext outcome
    apply sequence unique found (fun _ same => by rw [form] at same; cases same)
    · intro context environment before middleContext nextEnvironment middle finalContext outcome after head next
      obtain ⟨_, evaluate, rfl, same⟩ := discarded_inv unique found form head
      cases same
      exact .discard (lookupStatement?_sound found) form (expression_value unique value evaluate) (tailIH next)
    · intro context environment before finalContext outcome after head terminal
      obtain ⟨_, _, _, same⟩ := discarded_inv unique found form head
      subst same
      cases terminal
  | block found form _ _ innerIH tailIH =>
    intro context environment before after finalContext outcome
    apply sequence unique found (fun _ same => by rw [form] at same; cases same)
    · intro context environment before middleContext nextEnvironment middle finalContext outcome after head next
      obtain ⟨_, inner, executes, rfl, same⟩ := block_inv unique found form head
      cases inner with
      | fallthrough innerEnvironment =>
        cases same
        exact .blockFallthrough (lookupStatement?_sound found) form (innerIH executes) (tailIH next)
      | _ => cases same
    · intro context environment before finalContext outcome after head terminal
      obtain ⟨_, inner, executes, rfl, rfl⟩ := block_inv unique found form head
      have staged := innerIH executes
      cases inner with
      | fallthrough => cases terminal
      | returned => exact .blockReturned (lookupStatement?_sound found) form staged
      | breaking => exact .blockBreaking (lookupStatement?_sound found) form staged
      | continuing => exact .blockContinuing (lookupStatement?_sound found) form staged
      | fault => exact .blockFault (lookupStatement?_sound found) form staged
  | @conditional mode id rest node condition thenBody elseBody found form test _ _ _ leftIH rightIH tailIH =>
    intro context environment before after finalContext outcome
    have branch : ∀ {truth : Bool} {context environment before innerContext inner after},
        Dynamic.StatementsExecute program context scope.evidence scope.source environment before
          (if truth then thenBody else elseBody.getD []) innerContext inner after →
        Staging.Recursive.StatementsIn program registry false scope context environment before
          (if truth then thenBody else elseBody.getD []) innerContext (control inner) after := by
      intro truth context environment before innerContext inner after executes
      cases truth
      · exact rightIH executes
      · exact leftIH executes
    apply sequence unique found (fun _ same => by rw [form] at same; cases same)
    · intro context environment before middleContext nextEnvironment middle finalContext outcome after head next
      obtain ⟨rfl, truth, _, _, inner, evaluate, executes, same⟩ := conditional_inv unique found form head
      cases inner with
      | fallthrough innerEnvironment =>
        cases same
        exact .ifFallthrough (lookupStatement?_sound found) form (expression_value unique test evaluate)
          (branch executes) (tailIH next)
      | _ => cases same
    · intro context environment before finalContext outcome after head terminal
      obtain ⟨rfl, truth, _, _, inner, evaluate, executes, rfl⟩ := conditional_inv unique found form head
      have staged := branch executes
      have tested := expression_value (registry := registry) unique test evaluate
      cases inner with
      | fallthrough => cases terminal
      | returned => exact .ifReturned (lookupStatement?_sound found) form tested staged
      | breaking => exact .ifBreaking (lookupStatement?_sound found) form tested staged
      | continuing => exact .ifContinuing (lookupStatement?_sound found) form tested staged
      | fault => exact .ifFault (lookupStatement?_sound found) form tested staged

/-- An ordinary function-body execution of a supported list whose expressions
are subset sites is a staged execution with the same context, outcome and heap,
at any scope with the execution's Source and evidence. -/
theorem body {source : TypedSource} {evidence : Dynamic.EvidenceEnvironment}
    (sourceEq : scope.source = source) (evidenceEq : scope.evidence = evidence)
    (unique : NodeOccurrencesUnique source) {statements : List StatementId}
    (shape : Shape source expected (Subset prepared named source) true statements)
    {context : SourceSemantics.Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {finalContext : SourceSemantics.Context} {outcome : Dynamic.ControlOutcome}
    (trace : Dynamic.FunctionStatementsExecute program context evidence source environment before statements
      finalContext outcome after) :
    ∃ size, Staging.Recursive.Size.Statements program registry size scope context environment before statements
      finalContext (control outcome) after := by
  subst sourceEq evidenceEq
  exact Staging.Recursive.Size.Statements.of_trace (CellAwareInvocationAcceptedStatementLifting.statements
    (registry := registry) unique shape trace)

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedStatementLifting
