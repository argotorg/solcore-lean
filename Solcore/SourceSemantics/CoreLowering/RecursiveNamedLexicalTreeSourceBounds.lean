import Solcore.SourceSemantics.CoreLowering.RecursiveNamedStatementSourceBounds
import Solcore.SourceSemantics.CoreLowering.TypedLexicalControlAllocation

/-! Views for the unchanged lexical Tree retain original source children and
their strict costs. Pure allocation stays an ordinary source receipt. Reflected
source costs are independent of the native costs used to select child laws. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedLexicalTreeSourceBounds
open Frontend SourceInference
open RecursiveNamedLoopContracts (ExecutesAt)
open RecursiveNamedCallBounds (ExpressionOutcome)

private theorem shape {source : TypedSource} {id : StatementId} {node : StatementNode}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node) :
    ∀ other, ContainsStatement source id other → other.form = node.form := by
  intro other present
  have same := Option.some.inj ((lookupStatement?_complete unique present).symm.trans found)
  exact congrArg StatementNode.form same

private theorem extension_eq {owner : Resolved.DeclarationId} {context left right : SourceSemantics.Context}
    {binder : TypedBinder} (first : BinderExtends owner context binder left)
    (second : BinderExtends owner context binder right) : left = right := by
  cases first; cases second; rfl

private theorem absent_statement {program : Program} {size : Nat} {context finalContext : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : StatementId} {node : StatementNode} {binder : TypedBinder}
    {outcome : Dynamic.ControlOutcome}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (form : node.form = .letDecl binder none)
    (trace : SourceExecutionSize.StatementExecutes program size context evidence source environment before id finalContext outcome after) :
    BinderExtends source.owner context binder finalContext ∧ ∃ location,
      outcome = .fallthrough ((binder.id, location) :: environment) ∧
      Dynamic.Heap.Allocates before binder.scheme.body none location after := by
  have shapes := shape unique found
  clear found
  cases trace <;> have same := shapes _ (by assumption) <;> simp_all

/-- An absent binding retains the original tail witness, including a fault
after the successful allocation. -/
theorem absent {mode : Bool} {program : Program} {size : Nat} {context nextContext finalContext : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : StatementId} {node : StatementNode} {binder : TypedBinder}
    {rest : List StatementId} {outcome : Dynamic.ControlOutcome}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (form : node.form = .letDecl binder none) (mono : binder.scheme.quantified = [])
    (extended : BinderExtends source.owner context binder nextContext)
    (trace : ExecutesAt size mode program context evidence source environment before (id :: rest) finalContext outcome after) :
    ∃ location middle tailSize, Dynamic.Heap.Allocates before binder.scheme.body none location middle ∧
      ExecutesAt tailSize mode program nextContext evidence source ((binder.id, location) :: environment)
        middle rest finalContext outcome after ∧ tailSize < size := by
  have view := RecursiveNamedStatementSourceBounds.cons_inv unique (lookupStatement?_sound found)
    (by intro _ _ expression; simp [form]) trace
  cases view with
  | next head tail _ tailSmaller =>
    obtain ⟨extension, location, same, allocated⟩ := absent_statement unique found form head
    cases extension_eq extended extension
    cases same
    exact ⟨location, _, _, allocated, tail, tailSmaller⟩
  | terminal head terminal _ =>
    obtain ⟨_, _, same, _⟩ := absent_statement unique found form head
    cases same; cases terminal
  | fault failed _ =>
    exact False.elim (ScalarStatementViews.letUninitialized_cannot_fault unique (lookupStatement?_sound found) form mono failed.sound)

/-- An initialized binding retains both original initializer and tail costs.
Initializer failure precedes the allocation and context extension. -/
theorem initialized {mode : Bool} {program : Program} {size : Nat} {context nextContext finalContext : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : StatementId} {node : StatementNode} {binder : TypedBinder}
    {initializer : ExpressionId} {rest : List StatementId} {outcome : Dynamic.ControlOutcome}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (form : node.form = .letDecl binder (some initializer)) (mono : binder.scheme.quantified = [])
    (extended : BinderExtends source.owner context binder nextContext)
    (trace : ExecutesAt size mode program context evidence source environment before (id :: rest) finalContext outcome after) :
    (∃ child reason, finalContext = context ∧ outcome = .fault reason ∧
      SourceExecutionSize.ExpressionFaults program child context evidence source environment before initializer reason after ∧ child < size) ∨
    (∃ child tailSize value location middle allocatedHeap,
      SourceExecutionSize.ExpressionEvaluates program child context evidence source environment before initializer value middle ∧
      Dynamic.Heap.Allocates middle binder.scheme.body (some value) location allocatedHeap ∧
      ExecutesAt tailSize mode program nextContext evidence source ((binder.id, location) :: environment)
        allocatedHeap rest finalContext outcome after ∧ child < size ∧ tailSize < size) := by
  have view := RecursiveNamedStatementSourceBounds.cons_inv unique (lookupStatement?_sound found)
    (by intro _ _ expression; simp [form]) trace
  cases view with
  | next head tail headSmaller tailSmaller =>
    obtain ⟨extension, child, value, middle, location, same, initial, allocated, smaller⟩ :=
      RecursiveNamedStatementSourceBounds.initialized_value unique (lookupStatement?_sound found) form mono head
    cases extension_eq extended extension
    cases same
    exact .inr ⟨child, _, value, location, middle, _, initial, allocated, tail, Nat.lt_trans smaller headSmaller, tailSmaller⟩
  | terminal head terminal _ =>
    obtain ⟨_, _, _, _, _, same, _, _, _⟩ :=
      RecursiveNamedStatementSourceBounds.initialized_value unique (lookupStatement?_sound found) form mono head
    cases same; cases terminal
  | fault failed smaller =>
    obtain ⟨child, initial, childSmaller⟩ :=
      RecursiveNamedStatementSourceBounds.initialized_fault unique (lookupStatement?_sound found) form mono failed
    exact .inl ⟨child, _, rfl, rfl, initial, Nat.lt_trans childSmaller smaller⟩

/-- Discard evaluates its expression before the original tail. -/
theorem discard {mode : Bool} {program : Program} {size : Nat} {context finalContext : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : StatementId} {node : StatementNode} {expression : ExpressionId}
    {semicolon : Bool} {rest : List StatementId} {outcome : Dynamic.ControlOutcome}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (form : node.form = .expression expression semicolon) (guard : (!semicolon && mode && rest.isEmpty) = false)
    (trace : ExecutesAt size mode program context evidence source environment before (id :: rest) finalContext outcome after) :
    (∃ child reason, finalContext = context ∧ outcome = .fault reason ∧
      SourceExecutionSize.ExpressionFaults program child context evidence source environment before expression reason after ∧ child < size) ∨
    (∃ child tailSize value middle,
      SourceExecutionSize.ExpressionEvaluates program child context evidence source environment before expression value middle ∧
      ExecutesAt tailSize mode program context evidence source environment middle rest finalContext outcome after ∧
      child < size ∧ tailSize < size) := by
  have view := RecursiveNamedStatementSourceBounds.cons_inv unique (lookupStatement?_sound found)
    (TypedScopedStatements.not_tail form guard) trace
  cases view with
  | next head tail headSmaller tailSmaller =>
    obtain ⟨rfl, same, child, value, initial, smaller⟩ :=
      RecursiveNamedStatementSourceBounds.expression_value unique (lookupStatement?_sound found) form head
    cases Dynamic.ControlOutcome.fallthrough.inj same
    exact .inr ⟨child, _, value, _, initial, tail, Nat.lt_trans smaller headSmaller, tailSmaller⟩
  | terminal head terminal _ =>
    obtain ⟨_, same, _, _, _⟩ :=
      RecursiveNamedStatementSourceBounds.expression_value unique (lookupStatement?_sound found) form head
    cases same; cases terminal
  | fault failed smaller =>
    obtain ⟨child, initial, childSmaller⟩ :=
      RecursiveNamedStatementSourceBounds.expression_fault unique (lookupStatement?_sound found) form failed
    exact .inl ⟨child, _, rfl, rfl, initial, Nat.lt_trans childSmaller smaller⟩

/-- A returning statement retains the original expression outcome and cost. -/
theorem returning {mode : Bool} {program : Program} {size : Nat} {context finalContext : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : StatementId} {node : StatementNode} {expression : ExpressionId}
    {rest : List StatementId} {outcome : Dynamic.ControlOutcome}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (form : node.form = .returnStmt (some expression))
    (trace : ExecutesAt size mode program context evidence source environment before (id :: rest) finalContext outcome after) :
    finalContext = context ∧ ∃ child expressionOutcome,
      ExpressionOutcome program child context evidence source environment before expression expressionOutcome after ∧
      outcome = (match expressionOutcome with | .value value => .returned value | .fault reason => .fault reason) ∧ child < size := by
  have view := RecursiveNamedStatementSourceBounds.cons_inv unique (lookupStatement?_sound found)
    (by intro _ _ expression; simp [form]) trace
  cases view with
  | next head _ _ _ =>
    obtain ⟨_, _, _, same, _, _⟩ :=
      RecursiveNamedStatementSourceBounds.return_value unique (lookupStatement?_sound found) form head
    cases same
  | terminal head _ smaller =>
    obtain ⟨rfl, child, value, rfl, initial, childSmaller⟩ :=
      RecursiveNamedStatementSourceBounds.return_value unique (lookupStatement?_sound found) form head
    exact ⟨rfl, child, .value value, .value initial, rfl, Nat.lt_trans childSmaller smaller⟩
  | fault failed smaller =>
    obtain ⟨child, initial, childSmaller⟩ :=
      RecursiveNamedStatementSourceBounds.return_fault unique (lookupStatement?_sound found) form failed
    exact ⟨rfl, child, .fault _, .fault initial, rfl, Nat.lt_trans childSmaller smaller⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedLexicalTreeSourceBounds
