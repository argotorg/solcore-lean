import Solcore.SourceSemantics.CoreLowering.RecursiveNamedLoopContracts

/-! Statement-list inversion retains the original head and tail source
witnesses. A function singleton has no tail premise; only its empty nil
continuation is constructed, with size one bounded by the positive head.
These source sizes say nothing about native execution sizes. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedStatementSourceBounds
open Frontend SourceInference
open RecursiveNamedLoopContracts RecursiveNamedCallBounds

inductive Cons (program : Program) (mode : Bool) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (id : StatementId) (rest : List StatementId) (size : Nat) :
    SourceSemantics.Context → Dynamic.ControlOutcome → Dynamic.Heap → Prop where
  | next {headSize tailSize middleContext nextEnvironment middle finalContext outcome after}
      (head : SourceExecutionSize.StatementExecutes program headSize context evidence source environment before id
        middleContext (.fallthrough nextEnvironment) middle)
      (tail : ExecutesAt tailSize mode program middleContext evidence source nextEnvironment middle rest finalContext outcome after)
      (headSmaller : headSize < size) (tailSmaller : tailSize < size) :
      Cons program mode context evidence source environment before id rest size finalContext outcome after
  | terminal {headSize finalContext outcome after}
      (head : SourceExecutionSize.StatementExecutes program headSize context evidence source environment before id finalContext outcome after)
      (control : Dynamic.TerminalControl outcome) (headSmaller : headSize < size) :
      Cons program mode context evidence source environment before id rest size finalContext outcome after
  | fault {headSize reason after}
      (head : SourceExecutionSize.StatementFaults program headSize context evidence source environment before id reason after)
      (headSmaller : headSize < size) :
      Cons program mode context evidence source environment before id rest size context (.fault reason) after

private theorem statement_shape {source : TypedSource} {id : StatementId} {node : StatementNode}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node) :
    ∀ other, ContainsStatement source id other → other = node := by
  intro other present
  exact Option.some.inj ((lookupStatement?_complete unique present).symm.trans (lookupStatement?_complete unique contains))

/-- Every ordinary cons form uses its original measured children. The tail
expression singleton is handled separately by the lexical grammar. -/
theorem cons_inv {program : Program} {mode : Bool} {context finalContext : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : StatementId} {node : StatementNode} {rest : List StatementId}
    {size : Nat} {outcome : Dynamic.ControlOutcome}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (notTail : mode = true → rest = [] → ∀ expression, node.form ≠ .expression expression false)
    (trace : ExecutesAt size mode program context evidence source environment before (id :: rest) finalContext outcome after) :
    Cons program mode context evidence source environment before id rest size finalContext outcome after := by
  cases mode with
  | false =>
    cases trace with
    | control trace => cases trace with
      | cons head tail =>
        exact Cons.next (mode := false) head (.control tail)
          (SourceExecutionSize.child_lt_stepSize (by simp)) (SourceExecutionSize.child_lt_stepSize (by simp))
      | terminal head control => exact .terminal head control (SourceExecutionSize.child_lt_stepSize (by simp))
    | fault trace => cases trace with
      | head failed => exact .fault failed (SourceExecutionSize.child_lt_stepSize (by simp))
      | tail head failed =>
        exact Cons.next (mode := false) head (.fault failed)
          (SourceExecutionSize.child_lt_stepSize (by simp)) (SourceExecutionSize.child_lt_stepSize (by simp))
  | true =>
    cases trace with
    | control trace => cases trace with
      | tailExpression present form child =>
        have same := statement_shape unique contains _ present
        exact False.elim (notTail rfl rfl _ (same ▸ form))
      | singleton present notTailHead head =>
        cases outcome with
        | fallthrough nextEnvironment =>
          exact Cons.next (mode := true) head (.control .nil)
            (SourceExecutionSize.child_lt_stepSize (by simp)) (by
            have positive := head.positive
            simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil]
            omega)
        | returned value => exact .terminal head (.returned value) (SourceExecutionSize.child_lt_stepSize (by simp))
        | breaking nextEnvironment => exact .terminal head (.breaking nextEnvironment) (SourceExecutionSize.child_lt_stepSize (by simp))
        | continuing nextEnvironment => exact .terminal head (.continuing nextEnvironment) (SourceExecutionSize.child_lt_stepSize (by simp))
        | fault reason => exact .terminal head (.fault reason) (SourceExecutionSize.child_lt_stepSize (by simp))
      | cons head tail =>
        exact Cons.next (mode := true) head (.control tail)
          (SourceExecutionSize.child_lt_stepSize (by simp)) (SourceExecutionSize.child_lt_stepSize (by simp))
      | terminal head control => exact .terminal head control (SourceExecutionSize.child_lt_stepSize (by simp))
    | fault trace => cases trace with
      | singleton failed | head failed => exact .fault failed (SourceExecutionSize.child_lt_stepSize (by simp))
      | tailExpression present form child =>
        have same := statement_shape unique contains _ present
        exact False.elim (notTail rfl rfl _ (same ▸ form))
      | tail head failed =>
        exact Cons.next (mode := true) head (.fault failed)
          (SourceExecutionSize.child_lt_stepSize (by simp)) (SourceExecutionSize.child_lt_stepSize (by simp))

private theorem shape_form {source : TypedSource} {id : StatementId} {node : StatementNode}
    {form : StatementForm} (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (same : node.form = form) : ∀ other, ContainsStatement source id other → other.form = form := by
  intro other present
  exact (statement_shape unique contains other present) ▸ same

section StatementChildren
variable {program : Program} {size : Nat} {context finalContext : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
  {before after : Dynamic.Heap} {id : StatementId} {node : StatementNode} {outcome : Dynamic.ControlOutcome}
  (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)

include unique contains in
theorem return_value {expression : ExpressionId} (form : node.form = .returnStmt (some expression))
    (trace : SourceExecutionSize.StatementExecutes program size context evidence source environment before id finalContext outcome after) :
    finalContext = context ∧ ∃ child value, outcome = .returned value ∧
      SourceExecutionSize.ExpressionEvaluates program child context evidence source environment before expression value after ∧ child < size := by
  have shape := shape_form unique contains form
  clear contains form
  cases trace <;> have actualForm := shape _ (by assumption) <;> simp_all
  exact ⟨_, by assumption, SourceExecutionSize.child_lt_stepSize (by simp)⟩

include unique contains in
theorem expression_value {expression : ExpressionId} {semicolon : Bool} (form : node.form = .expression expression semicolon)
    (trace : SourceExecutionSize.StatementExecutes program size context evidence source environment before id finalContext outcome after) :
    finalContext = context ∧ outcome = .fallthrough environment ∧ ∃ child value,
      SourceExecutionSize.ExpressionEvaluates program child context evidence source environment before expression value after ∧ child < size := by
  have shape := shape_form unique contains form
  clear contains form
  cases trace <;> have actualForm := shape _ (by assumption) <;> simp_all
  exact ⟨_, ⟨_, by assumption⟩, SourceExecutionSize.child_lt_stepSize (by simp)⟩

include unique contains in
theorem initialized_value {binder : TypedBinder} {initializer : ExpressionId}
    (form : node.form = .letDecl binder (some initializer)) (mono : binder.scheme.quantified = [])
    (trace : SourceExecutionSize.StatementExecutes program size context evidence source environment before id finalContext outcome after) :
    BinderExtends source.owner context binder finalContext ∧ ∃ child value middle location,
      outcome = .fallthrough ((binder.id, location) :: environment) ∧
      SourceExecutionSize.ExpressionEvaluates program child context evidence source environment before initializer value middle ∧
      Dynamic.Heap.Allocates middle binder.scheme.body (some value) location after ∧ child < size := by
  have shape := shape_form unique contains form
  clear contains form
  cases trace <;> have actualForm := shape _ (by assumption) <;> simp_all
  exact ⟨_, _, _, by assumption, by assumption, SourceExecutionSize.child_lt_stepSize (by simp)⟩

include unique contains in
theorem block_value {statements : List StatementId} (form : node.form = .block statements)
    (trace : SourceExecutionSize.StatementExecutes program size context evidence source environment before id finalContext outcome after) :
    finalContext = context ∧ ∃ child innerContext innerOutcome,
      outcome = Dynamic.restoreControl environment innerOutcome ∧
      SourceExecutionSize.StatementsExecute program child context evidence source environment before statements innerContext innerOutcome after ∧ child < size := by
  have shape := shape_form unique contains form
  clear contains form
  cases trace <;> have actualForm := shape _ (by assumption) <;> simp_all
  exact ⟨_, _, _, rfl, by assumption, SourceExecutionSize.child_lt_stepSize (by simp)⟩

variable {reason : Dynamic.SemanticFault}

private theorem not_missing (found : ContainsStatement source id node) : ¬ Dynamic.StatementMissing source id :=
  fun absent => Dynamic.StatementAbsentIn.excludes_contains absent found

include unique contains in
theorem return_fault {expression : ExpressionId} (form : node.form = .returnStmt (some expression))
    (trace : SourceExecutionSize.StatementFaults program size context evidence source environment before id reason after) :
    ∃ child, SourceExecutionSize.ExpressionFaults program child context evidence source environment before expression reason after ∧ child < size := by
  have shape := shape_form unique contains form
  have present := not_missing contains
  clear contains form
  cases trace
  all_goals first
    | exact False.elim (present (by assumption))
    | have actualForm := shape _ (by assumption); simp_all
  exact ⟨_, by assumption, SourceExecutionSize.child_lt_stepSize (by simp)⟩

include unique contains in
theorem expression_fault {expression : ExpressionId} {semicolon : Bool} (form : node.form = .expression expression semicolon)
    (trace : SourceExecutionSize.StatementFaults program size context evidence source environment before id reason after) :
    ∃ child, SourceExecutionSize.ExpressionFaults program child context evidence source environment before expression reason after ∧ child < size := by
  have shape := shape_form unique contains form
  have present := not_missing contains
  clear contains form
  cases trace
  all_goals first
    | exact False.elim (present (by assumption))
    | have actualForm := shape _ (by assumption); simp_all
  exact ⟨_, by assumption, SourceExecutionSize.child_lt_stepSize (by simp)⟩

include unique contains in
theorem initialized_fault {binder : TypedBinder} {initializer : ExpressionId}
    (form : node.form = .letDecl binder (some initializer)) (mono : binder.scheme.quantified = [])
    (trace : SourceExecutionSize.StatementFaults program size context evidence source environment before id reason after) :
    ∃ child, SourceExecutionSize.ExpressionFaults program child context evidence source environment before initializer reason after ∧ child < size := by
  have shape := shape_form unique contains form
  have present := not_missing contains
  clear contains form
  cases trace
  all_goals first
    | exact False.elim (present (by assumption))
    | have actualForm := shape _ (by assumption); simp_all
  exact ⟨_, by assumption, SourceExecutionSize.child_lt_stepSize (by simp)⟩

include unique contains in
theorem block_fault {statements : List StatementId} (form : node.form = .block statements)
    (trace : SourceExecutionSize.StatementFaults program size context evidence source environment before id reason after) :
    ∃ child innerContext,
      SourceExecutionSize.StatementsFault program child context evidence source environment before statements innerContext reason after ∧ child < size := by
  have shape := shape_form unique contains form
  have present := not_missing contains
  clear contains form
  cases trace
  all_goals first
    | exact False.elim (present (by assumption))
    | have actualForm := shape _ (by assumption); simp_all
  exact ⟨_, ⟨_, by assumption⟩, SourceExecutionSize.child_lt_stepSize (by simp)⟩
end StatementChildren

/-- A real tail expression keeps its original expression child. An ordinary
singleton fault passes through the original measured statement fault first. -/
theorem tail_inv {program : Program} {size : Nat} {context finalContext : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : StatementId} {node : StatementNode} {expression : ExpressionId}
    {outcome : Dynamic.ControlOutcome}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (form : node.form = .expression expression false)
    (trace : FunctionOutcome program size context evidence source environment before [id] finalContext outcome after) :
    finalContext = context ∧ ∃ child expressionOutcome,
      ExpressionOutcome program child context evidence source environment before expression expressionOutcome after ∧
      outcome = (match expressionOutcome with | .value value => .returned value | .fault reason => .fault reason) ∧ child < size := by
  cases trace with
  | control trace => cases trace with
    | tailExpression present same evaluated =>
      rw [statement_shape unique contains _ present, form] at same
      cases same
      exact ⟨rfl, _, _, .value evaluated, rfl, SourceExecutionSize.child_lt_stepSize (by simp)⟩
    | singleton present notTail executed =>
      have same := statement_shape unique contains _ present
      exact False.elim (notTail _ (same ▸ form))
  | fault trace => cases trace with
    | tailExpression present same failed =>
      rw [statement_shape unique contains _ present, form] at same
      cases same
      exact ⟨rfl, _, _, .fault failed, rfl, SourceExecutionSize.child_lt_stepSize (by simp)⟩
    | singleton failed =>
      obtain ⟨child, evaluated, smaller⟩ := expression_fault unique contains form failed
      exact ⟨rfl, child, .fault _, .fault evaluated, rfl,
        Nat.lt_trans smaller (SourceExecutionSize.child_lt_stepSize (by simp))⟩

inductive IfTrace (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (condition : ExpressionId) (thenBody : List StatementId)
    (elseBody : Option (List StatementId)) (size : Nat) : Dynamic.ControlOutcome → Dynamic.Heap → Prop where
  | conditionFault {child reason after}
      (failed : SourceExecutionSize.ExpressionFaults program child context evidence source environment before condition reason after)
      (smaller : child < size) : IfTrace program context evidence source environment before condition thenBody elseBody size (.fault reason) after
  | conditionType {child value actual after}
      (evaluated : SourceExecutionSize.ExpressionEvaluates program child context evidence source environment before condition value after)
      (notBoolean : ¬ Dynamic.BooleanValue value) (runtimeType : Dynamic.ValueRuntimeType value actual)
      (smaller : child < size) : IfTrace program context evidence source environment before condition thenBody elseBody size (.fault (.typeMismatch .bool actual)) after
  | branch {conditionSize bodySize boolean middle finalContext outcome after}
      (conditionEvaluated : SourceExecutionSize.ExpressionEvaluates program conditionSize context evidence source environment before condition (.bool boolean) middle)
      (body : StatementsOutcome program bodySize context evidence source environment middle
        (if boolean then thenBody else elseBody.getD []) finalContext outcome after)
      (conditionSmaller : conditionSize < size) (bodySmaller : bodySize < size) :
      IfTrace program context evidence source environment before condition thenBody elseBody size (Dynamic.restoreControl environment outcome) after

/-- Conditional inversion retains the real condition and selected branch.
The missing else branch has only a size-one nil continuation. -/
theorem if_inv {program : Program} {size : Nat} {context finalContext : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : StatementId} {node : StatementNode} {condition : ExpressionId}
    {thenBody : List StatementId} {elseBody : Option (List StatementId)} {outcome : Dynamic.ControlOutcome}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (form : node.form = .ifThen condition thenBody elseBody)
    (trace : StatementOutcome program size context evidence source environment before id finalContext outcome after) :
    finalContext = context ∧ IfTrace program context evidence source environment before condition thenBody elseBody size outcome after := by
  have shape := shape_form unique contains form
  have present : ¬ Dynamic.StatementMissing source id := not_missing contains
  clear contains form
  cases trace with
  | control trace =>
    cases trace <;> have actualForm := shape _ (by assumption) <;> simp_all
    · exact .branch (boolean := true) (by assumption) (.control (by assumption))
        (SourceExecutionSize.child_lt_stepSize (by simp)) (SourceExecutionSize.child_lt_stepSize (by simp))
    · apply IfTrace.branch (boolean := false) (elseBody := none)
        (environment := environment) (outcome := .fallthrough environment) (finalContext := context)
        (by assumption) (.control .nil)
      · exact SourceExecutionSize.child_lt_stepSize (by simp)
      · have positive := (show SourceExecutionSize.ExpressionEvaluates _ _ _ _ _ _ _ _ _ _ from by assumption).positive
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil]
        omega
    · exact .branch (boolean := false) (by assumption) (.control (by assumption))
        (SourceExecutionSize.child_lt_stepSize (by simp)) (SourceExecutionSize.child_lt_stepSize (by simp))
  | fault trace =>
    cases trace
    all_goals first
      | exact False.elim (present (by assumption))
      | have actualForm := shape _ (by assumption); simp_all
    · exact .conditionFault (by assumption) (SourceExecutionSize.child_lt_stepSize (by simp))
    · exact .conditionType (by assumption) (by assumption) (by assumption) (SourceExecutionSize.child_lt_stepSize (by simp))
    · exact .branch (boolean := true) (by assumption) (.fault (by assumption))
        (SourceExecutionSize.child_lt_stepSize (by simp)) (SourceExecutionSize.child_lt_stepSize (by simp))
    · exact .branch (boolean := false) (by assumption) (.fault (by assumption))
        (SourceExecutionSize.child_lt_stepSize (by simp)) (SourceExecutionSize.child_lt_stepSize (by simp))

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedStatementSourceBounds
