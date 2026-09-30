import Solcore.SourceSemantics.Dynamic

/-! Occurrence-unique inversion views for the source statement judgments.
These views inspect declarative derivations and do not evaluate source code. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.ScalarStatementViews

open Frontend Frontend.SourceInference

private theorem statement_shape {source : TypedSource} {id : StatementId} {node : StatementNode}
    {form : StatementForm} (unique : NodeOccurrencesUnique source)
    (contains : ContainsStatement source id node) (sameForm : node.form = form) :
    ∀ other, ContainsStatement source id other → other.form = form := by
  intro other otherContains
  have same : other = node := Option.some.inj
    ((lookupStatement?_complete unique otherContains).symm.trans (lookupStatement?_complete unique contains))
  exact same ▸ sameForm

section Views

variable {program : Program} {context finalContext : Context} {evidence : Dynamic.EvidenceEnvironment}
  {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
  {id : StatementId} {node : StatementNode} {outcome : Dynamic.ControlOutcome}
  (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)

include unique contains

theorem breaking (form : node.form = .breakStmt)
    (evaluated : Dynamic.StatementExecutes program context evidence source environment before id finalContext outcome after) :
    finalContext = context ∧ outcome = .breaking environment ∧ after = before := by
  have shape := statement_shape unique contains form
  clear contains form
  cases evaluated <;> have actualForm := shape _ (by assumption) <;> simp_all

theorem continuing (form : node.form = .continueStmt)
    (evaluated : Dynamic.StatementExecutes program context evidence source environment before id finalContext outcome after) :
    finalContext = context ∧ outcome = .continuing environment ∧ after = before := by
  have shape := statement_shape unique contains form
  clear contains form
  cases evaluated <;> have actualForm := shape _ (by assumption) <;> simp_all

theorem returnUnit (form : node.form = .returnStmt none)
    (evaluated : Dynamic.StatementExecutes program context evidence source environment before id finalContext outcome after) :
    finalContext = context ∧ outcome = .returned .unit ∧ after = before := by
  have shape := statement_shape unique contains form
  clear contains form
  cases evaluated <;> have actualForm := shape _ (by assumption) <;> simp_all

theorem returnValue {expression : ExpressionId} (form : node.form = .returnStmt (some expression))
    (evaluated : Dynamic.StatementExecutes program context evidence source environment before id finalContext outcome after) :
    finalContext = context ∧ ∃ value, outcome = .returned value ∧
      Dynamic.ExpressionEvaluates program context evidence source environment before expression value after := by
  have shape := statement_shape unique contains form
  clear contains form
  cases evaluated <;> have actualForm := shape _ (by assumption) <;> simp_all

theorem expression {expression : ExpressionId} {semicolon : Bool} (form : node.form = .expression expression semicolon)
    (evaluated : Dynamic.StatementExecutes program context evidence source environment before id finalContext outcome after) :
    finalContext = context ∧ outcome = .fallthrough environment ∧ ∃ value,
      Dynamic.ExpressionEvaluates program context evidence source environment before expression value after := by
  have shape := statement_shape unique contains form
  clear contains form
  cases evaluated <;> have actualForm := shape _ (by assumption) <;> simp_all
  exact ⟨_, by assumption⟩

theorem assignValue {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    (form : node.form = .assignValue assignment operator rhs)
    (evaluated : Dynamic.StatementExecutes program context evidence source environment before id finalContext outcome after) :
    finalContext = context ∧ outcome = .fallthrough environment ∧ ∃ updated,
      Dynamic.SourcePlaceAssignment program context evidence source (Dynamic.AssignmentValueApplies operator)
        environment before assignment.target rhs updated after := by
  have shape := statement_shape unique contains form
  clear contains form
  cases evaluated <;> have actualForm := shape _ (by assumption) <;> simp_all
  exact ⟨_, by assumption⟩

theorem letUninitialized {binder : TypedBinder} (form : node.form = .letDecl binder none)
    (evaluated : Dynamic.StatementExecutes program context evidence source environment before id finalContext outcome after) :
    BinderExtends source.owner context binder finalContext ∧ ∃ location,
      outcome = .fallthrough ((binder.id, location) :: environment) ∧
      Dynamic.Heap.Allocates before binder.scheme.body none location after := by
  have shape := statement_shape unique contains form
  clear contains form
  cases evaluated <;> have actualForm := shape _ (by assumption) <;> simp_all

theorem letInitialized {binder : TypedBinder} {initializer : ExpressionId}
    (form : node.form = .letDecl binder (some initializer)) (mono : binder.scheme.quantified = [])
    (evaluated : Dynamic.StatementExecutes program context evidence source environment before id finalContext outcome after) :
    BinderExtends source.owner context binder finalContext ∧ ∃ location value middle,
      outcome = .fallthrough ((binder.id, location) :: environment) ∧
      Dynamic.ExpressionEvaluates program context evidence source environment before initializer value middle ∧
      Dynamic.Heap.Allocates middle binder.scheme.body (some value) location after := by
  have shape := statement_shape unique contains form
  clear contains form
  cases evaluated <;> have actualForm := shape _ (by assumption) <;> simp_all
  exact ⟨_, _, by assumption, by assumption⟩

theorem block {statements : List StatementId} (form : node.form = .block statements)
    (evaluated : Dynamic.StatementExecutes program context evidence source environment before id finalContext outcome after) :
    finalContext = context ∧ ∃ innerContext innerOutcome,
      outcome = Dynamic.restoreControl environment innerOutcome ∧
      Dynamic.StatementsExecute program context evidence source environment before statements innerContext innerOutcome after := by
  have shape := statement_shape unique contains form
  clear contains form
  cases evaluated <;> have actualForm := shape _ (by assumption) <;> simp_all
  exact ⟨_, _, rfl, by assumption⟩

theorem whileLoop {condition : ExpressionId} {statements : List StatementId} (form : node.form = .whileLoop condition statements)
    (evaluated : Dynamic.StatementExecutes program context evidence source environment before id finalContext outcome after) :
    finalContext = context ∧ ∃ innerContext innerOutcome,
      outcome = Dynamic.restoreControl environment innerOutcome ∧
      Dynamic.WhileExecutes program context evidence source environment before condition statements innerContext innerOutcome after := by
  have shape := statement_shape unique contains form
  clear contains form
  cases evaluated <;> have actualForm := shape _ (by assumption) <;> simp_all
  exact ⟨_, _, rfl, by assumption⟩

theorem ifThen {condition : ExpressionId} {thenBody : List StatementId} {elseBody : Option (List StatementId)}
    (form : node.form = .ifThen condition thenBody elseBody)
    (evaluated : Dynamic.StatementExecutes program context evidence source environment before id finalContext outcome after) :
    finalContext = context ∧ ∃ boolean middle innerContext innerOutcome,
      Dynamic.ExpressionEvaluates program context evidence source environment before condition (.bool boolean) middle ∧
      outcome = Dynamic.restoreControl environment innerOutcome ∧
      Dynamic.StatementsExecute program context evidence source environment middle
        (if boolean then thenBody else elseBody.getD []) innerContext innerOutcome after := by
  have shape := statement_shape unique contains form
  clear contains form
  cases evaluated <;> have actualForm := shape _ (by assumption) <;> simp_all
  · exact .inr ⟨_, by assumption, _, _, rfl, by assumption⟩
  · exact .inl ⟨_, by assumption, context, .fallthrough environment, rfl, .nil⟩
  · exact .inl ⟨_, by assumption, _, _, rfl, by assumption⟩

variable {reason : Dynamic.SemanticFault}

omit unique in
private theorem not_missing : ¬ Dynamic.StatementMissing source id :=
  fun absent => Dynamic.StatementAbsentIn.excludes_contains absent contains

theorem breaking_cannot_fault (form : node.form = .breakStmt)
    (fault : Dynamic.StatementFaults program context evidence source environment before id reason after) : False := by
  have shape := statement_shape unique contains form
  have present := not_missing contains
  clear contains form
  cases fault
  all_goals first
    | exact present (by assumption)
    | have actualForm := shape _ (by assumption); simp_all

theorem continuing_cannot_fault (form : node.form = .continueStmt)
    (fault : Dynamic.StatementFaults program context evidence source environment before id reason after) : False := by
  have shape := statement_shape unique contains form
  have present := not_missing contains
  clear contains form
  cases fault
  all_goals first
    | exact present (by assumption)
    | have actualForm := shape _ (by assumption); simp_all

theorem returnUnit_cannot_fault (form : node.form = .returnStmt none)
    (fault : Dynamic.StatementFaults program context evidence source environment before id reason after) : False := by
  have shape := statement_shape unique contains form
  have present := not_missing contains
  clear contains form
  cases fault
  all_goals first
    | exact present (by assumption)
    | have actualForm := shape _ (by assumption); simp_all

theorem returnValue_fault {expression : ExpressionId} (form : node.form = .returnStmt (some expression))
    (fault : Dynamic.StatementFaults program context evidence source environment before id reason after) :
    Dynamic.ExpressionFaults program context evidence source environment before expression reason after := by
  have shape := statement_shape unique contains form
  have present := not_missing contains
  clear contains form
  cases fault
  all_goals first
    | exact False.elim (present (by assumption))
    | have actualForm := shape _ (by assumption); simp_all

theorem expression_fault {expression : ExpressionId} {semicolon : Bool} (form : node.form = .expression expression semicolon)
    (fault : Dynamic.StatementFaults program context evidence source environment before id reason after) :
    Dynamic.ExpressionFaults program context evidence source environment before expression reason after := by
  have shape := statement_shape unique contains form
  have present := not_missing contains
  clear contains form
  cases fault
  all_goals first
    | exact False.elim (present (by assumption))
    | have actualForm := shape _ (by assumption); simp_all

theorem assignValue_fault {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    (form : node.form = .assignValue assignment operator rhs)
    (fault : Dynamic.StatementFaults program context evidence source environment before id reason after) :
    Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before assignment.target operator rhs reason after := by
  have shape := statement_shape unique contains form
  have present := not_missing contains
  clear contains form
  cases fault
  all_goals first
    | exact False.elim (present (by assumption))
    | have actualForm := shape _ (by assumption); simp_all

theorem letUninitialized_cannot_fault {binder : TypedBinder} (form : node.form = .letDecl binder none)
    (mono : binder.scheme.quantified = [])
    (fault : Dynamic.StatementFaults program context evidence source environment before id reason after) : False := by
  have shape := statement_shape unique contains form
  have present := not_missing contains
  clear contains form
  cases fault
  all_goals first
    | exact present (by assumption)
    | have actualForm := shape _ (by assumption); simp_all

theorem letInitialized_fault {binder : TypedBinder} {initializer : ExpressionId}
    (form : node.form = .letDecl binder (some initializer)) (mono : binder.scheme.quantified = [])
    (fault : Dynamic.StatementFaults program context evidence source environment before id reason after) :
    Dynamic.ExpressionFaults program context evidence source environment before initializer reason after := by
  have shape := statement_shape unique contains form
  have present := not_missing contains
  clear contains form
  cases fault
  all_goals first
    | exact False.elim (present (by assumption))
    | have actualForm := shape _ (by assumption); simp_all

theorem block_fault {statements : List StatementId} (form : node.form = .block statements)
    (fault : Dynamic.StatementFaults program context evidence source environment before id reason after) :
    ∃ innerContext, Dynamic.StatementsFault program context evidence source environment before statements innerContext reason after := by
  have shape := statement_shape unique contains form
  have present := not_missing contains
  clear contains form
  cases fault
  all_goals first
    | exact False.elim (present (by assumption))
    | have actualForm := shape _ (by assumption); simp_all
  exact ⟨_, by assumption⟩

theorem whileLoop_fault {condition : ExpressionId} {statements : List StatementId} (form : node.form = .whileLoop condition statements)
    (fault : Dynamic.StatementFaults program context evidence source environment before id reason after) :
    Dynamic.WhileFaults program context evidence source environment before condition statements reason after := by
  have shape := statement_shape unique contains form
  have present := not_missing contains
  clear contains form
  cases fault
  all_goals first
    | exact False.elim (present (by assumption))
    | have actualForm := shape _ (by assumption); simp_all

theorem ifThen_fault {condition : ExpressionId} {thenBody : List StatementId} {elseBody : Option (List StatementId)}
    (form : node.form = .ifThen condition thenBody elseBody)
    (fault : Dynamic.StatementFaults program context evidence source environment before id reason after) :
    Dynamic.ExpressionFaults program context evidence source environment before condition reason after ∨
    (∃ value actualType,
      Dynamic.ExpressionEvaluates program context evidence source environment before condition value after ∧
      (¬ Dynamic.BooleanValue value) ∧ Dynamic.ValueRuntimeType value actualType ∧ reason = .typeMismatch .bool actualType) ∨
    (∃ boolean middle innerContext,
      Dynamic.ExpressionEvaluates program context evidence source environment before condition (.bool boolean) middle ∧
      Dynamic.StatementsFault program context evidence source environment middle
        (if boolean then thenBody else elseBody.getD []) innerContext reason after) := by
  have shape := statement_shape unique contains form
  have present := not_missing contains
  clear contains form
  cases fault
  all_goals first
    | exact False.elim (present (by assumption))
    | have actualForm := shape _ (by assumption); simp_all
  · exact .inr (.inl ⟨_, by assumption, by assumption, by assumption⟩)
  · exact .inr (.inr (.inr ⟨_, by assumption, _, by assumption⟩))
  · exact .inr (.inr (.inl ⟨_, by assumption, _, by assumption⟩))

end Views

/-- Function mode adds only the implicit final-expression convention. -/
def ListExecutes (functionMode : Bool) (program : Program) (context : Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (statements : List StatementId) (finalContext : Context)
    (outcome : Dynamic.ControlOutcome) (after : Dynamic.Heap) : Prop :=
  if functionMode then Dynamic.FunctionStatementsExecute program context evidence source environment before statements finalContext outcome after
  else Dynamic.StatementsExecute program context evidence source environment before statements finalContext outcome after

def ListFaults (functionMode : Bool) (program : Program) (context : Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (statements : List StatementId) (finalContext : Context)
    (reason : Dynamic.SemanticFault) (after : Dynamic.Heap) : Prop :=
  if functionMode then Dynamic.FunctionStatementsFault program context evidence source environment before statements finalContext reason after
  else Dynamic.StatementsFault program context evidence source environment before statements finalContext reason after

theorem nil_view
    {program : Program} {context finalContext : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {outcome : Dynamic.ControlOutcome} (functionMode : Bool)
    (executed : ListExecutes functionMode program context evidence source environment before [] finalContext outcome after) :
    finalContext = context ∧ outcome = .fallthrough environment ∧ after = before := by
  cases functionMode <;> cases executed <;> exact ⟨rfl, rfl, rfl⟩

theorem nil_cannot_fault
    {program : Program} {context finalContext : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {reason : Dynamic.SemanticFault} (functionMode : Bool)
    (fault : ListFaults functionMode program context evidence source environment before [] finalContext reason after) : False := by
  cases functionMode <;> cases fault

/-- Every non-tail-expression head either continues with the remainder or
terminates at the head. Context/environment changes are retained exactly. -/
theorem cons_view
    {program : Program} {context finalContext : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {outcome : Dynamic.ControlOutcome} {id : StatementId} {node : StatementNode} {rest : List StatementId}
    (functionMode : Bool) (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (notTail : functionMode = true → rest = [] → ∀ expression, node.form ≠ .expression expression false)
    (executed : ListExecutes functionMode program context evidence source environment before (id :: rest) finalContext outcome after) :
    (∃ middleContext nextEnvironment middle,
      Dynamic.StatementExecutes program context evidence source environment before id middleContext (.fallthrough nextEnvironment) middle ∧
      ListExecutes functionMode program middleContext evidence source nextEnvironment middle rest finalContext outcome after) ∨
    (Dynamic.StatementExecutes program context evidence source environment before id finalContext outcome after ∧ Dynamic.TerminalControl outcome) := by
  cases functionMode with
  | false =>
      cases executed with
      | cons head tail => exact .inl ⟨_, _, _, head, tail⟩
      | terminal head terminal => exact .inr ⟨head, terminal⟩
  | true =>
      cases executed with
      | tailExpression otherContains form _ =>
          have same := statement_shape unique otherContains form _ contains
          exact False.elim (notTail rfl rfl _ same)
      | singleton _ _ head =>
          cases outcome with
          | fallthrough nextEnvironment => exact .inl ⟨_, nextEnvironment, _, head, .nil⟩
          | returned value => exact .inr ⟨head, .returned value⟩
          | breaking nextEnvironment => exact .inr ⟨head, .breaking nextEnvironment⟩
          | continuing nextEnvironment => exact .inr ⟨head, .continuing nextEnvironment⟩
          | fault reason => exact .inr ⟨head, .fault reason⟩
      | cons head tail => exact .inl ⟨_, _, _, head, tail⟩
      | terminal head terminal => exact .inr ⟨head, terminal⟩

theorem cons_fault_view
    {program : Program} {context finalContext : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {reason : Dynamic.SemanticFault} {id : StatementId} {node : StatementNode} {rest : List StatementId}
    (functionMode : Bool) (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (notTail : functionMode = true → rest = [] → ∀ expression, node.form ≠ .expression expression false)
    (fault : ListFaults functionMode program context evidence source environment before (id :: rest) finalContext reason after) :
    (finalContext = context ∧ Dynamic.StatementFaults program context evidence source environment before id reason after) ∨
    (∃ middleContext nextEnvironment middle,
      Dynamic.StatementExecutes program context evidence source environment before id middleContext (.fallthrough nextEnvironment) middle ∧
      ListFaults functionMode program middleContext evidence source nextEnvironment middle rest finalContext reason after) := by
  cases functionMode with
  | false =>
      cases fault with
      | head fault => exact .inl ⟨rfl, fault⟩
      | tail head tail => exact .inr ⟨_, _, _, head, tail⟩
  | true =>
      cases fault with
      | singleton fault | head fault => exact .inl ⟨rfl, fault⟩
      | tailExpression otherContains form _ =>
          have same := statement_shape unique otherContains form _ contains
          exact False.elim (notTail rfl rfl _ same)
      | tail head tail => exact .inr ⟨_, _, _, head, tail⟩

end Solcore.SourceSemantics.CoreLowering.ScalarStatementViews
