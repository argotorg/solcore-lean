import Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodyFlow
import Solcore.SourceSemantics.CoreLowering.ScopedSourceBodyAdmission
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedStatementSyntaxFacts

/-! The compiler-issued tree supplies statement shape. Independent original
Source typing supplies annotations and lexical context changes. The remaining
inputs concern actual expression children and allocated binder declarations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodyFlow
open Core Frontend SourceInference
open CompatibleEncoding (bind_ok)

/-- The real compatible reader returns the original stored node. -/
theorem read_found {checked : SourceCoreCompatibleCatalog.Checked} {source : TypedSource}
    {id : StatementId} {node : StatementNode} {type : Ty}
    (accepted : SourceCoreCompatibleDataExpressions.readStatement checked source id = .ok (node, type)) :
    source.lookupStatement? id = some node := by
  unfold SourceCoreCompatibleDataExpressions.readStatement at accepted
  by_cases owner : id.occurrence.owner ≠ source.owner
  · simp [owner, throw, bind, Except.bind] at accepted
  · simp only [owner, ↓reduceIte, bind, Except.bind, pure, Except.pure] at accepted
    cases found : source.lookupStatement? id with
    | none => simp [found] at accepted
    | some actual =>
        simp only [found] at accepted
        obtain ⟨projected, _, same⟩ := bind_ok accepted
        cases same
        rfl

private theorem head_tail {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {rest : List StatementId} {facts : BodyFacts}
    (typed : StatementsHaveType source control context (id :: rest) final facts) :
    ∃ middle headFacts tailFacts, StatementHasType source control context id middle headFacts ∧
      StatementsHaveType source control middle rest final tailFacts := by
  cases typed with
  | singleton head => exact ⟨_, _, _, head, .nil _ _⟩
  | cons head tail => exact ⟨_, _, _, head, tail⟩

private theorem form_at {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {facts : StatementFacts} {node : StatementNode}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (typed : StatementHasType source control context id final facts) :
    Dynamic.StatementHasType.FormTyping source control context node.form final := by
  obtain ⟨actual, contains, original⟩ := Dynamic.StatementHasType.formTyping typed
  cases Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  exact original

private theorem returned_annotation {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {facts : StatementFacts}
    {node : StatementNode} {expression : Option ExpressionId}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (form : node.form = .returnStmt expression)
    (typed : StatementHasType source control context id final facts) : node.type = control.returnType := by
  cases typed
  all_goals
    have same := Option.some.inj ((lookupStatement?_complete unique (by assumption)).symm.trans found)
    cases same
    simp_all

/-- The support boundary is tested on the issued compiler tree. No separate
statement recognizer result or preconstructed body shape occurs here. -/
theorem Tree.scan {policy : SourceCoreLoops.Policy} {checked : SourceCoreCompatibleCatalog.Checked}
    {source : TypedSource} {result : Ty} {reasonAt : ExpressionId → Word} {mode : Bool} {escaped : Word}
    {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {statements : List StatementId} {code : Expr}
    (tree : Tree policy source result reasonAt mode escaped fuel scope statements code)
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement checked)
    (closed : tree.closed = true) (unique : NodeOccurrencesUnique source)
    {approved : ExpressionId → Prop}
    (children : ∀ child ∈ tree.children, approved child.expression)
    (bindings : ∀ binding ∈ tree.bindings, RecursiveNamedStatementSyntaxFacts.BinderReceipt source binding.binder)
    {control : ControlContext} {context final : SourceSemantics.Context} {facts : BodyFacts}
    (typed : StatementsHaveType source control context statements final facts) :
    ScopedSourceBodyAdmission.Scan source approved control.returnType mode statements := by
  induction tree generalizing control context final facts with
  | nil => cases closed
  | boundary => cases closed
  | returning read form statementType child generated childType =>
      have found := read_found (readPolicy ▸ read)
      obtain ⟨_, _, _, head, _⟩ := head_tail typed
      have annotation := returned_annotation unique found form head
      have original := form_at unique found head
      rw [form] at original
      cases original with
      | returnValue value =>
          obtain ⟨node, contains, same⟩ := value.stored_type
          exact .returning _ found form annotation (lookupExpression?_complete unique contains) same
            (children ⟨_, _, _, child, generated⟩ (by simp [Tree.children]))
  | returnUnit read form statementType unitType =>
      have found := read_found (readPolicy ▸ read)
      obtain ⟨_, _, _, head, _⟩ := head_tail typed
      have annotation := returned_annotation unique found form head
      have original := form_at unique found head
      rw [form] at original
      cases original with
      | returnUnit result => exact .returnUnit _ found form (annotation.trans result) result
  | initialized read form statementType projected child generated childType remaining allocated ih =>
      have found := read_found (readPolicy ▸ read)
      have binder := bindings ⟨_, _, _, projected⟩ (by simp [Tree.bindings])
      obtain ⟨_, _, _, head, tail⟩ := head_tail typed
      have original := form_at unique found head
      rw [form] at original
      cases original with
      | letInitialized value _ _ =>
          obtain ⟨node, contains, same⟩ := value.stored_type
          exact .initialized found form binder.1 binder.2.1 binder.2.2
            (lookupExpression?_complete unique contains) same
            (children ⟨_, _, _, child, generated⟩ (by simp [Tree.children]))
            (ih closed (fun child member => children child (by simp [Tree.children, member]))
              (fun binding member => bindings binding (by simp [Tree.bindings, member])) tail)
      | letInitializedGeneralized poly _ _ _ _ => exact False.elim (poly binder.2.1)
  | absent read form statementType projected remaining allocated ih =>
      have found := read_found (readPolicy ▸ read)
      have binder := bindings ⟨_, _, _, projected⟩ (by simp [Tree.bindings])
      obtain ⟨_, _, _, head, tail⟩ := head_tail typed
      have original := form_at unique found head
      rw [form] at original
      cases original with
      | letUninitialized _ _ =>
          exact .absent found form binder.1 binder.2.1 binder.2.2
            (ih closed (fun child member => children child (by simpa [Tree.children] using member))
              (fun binding member => bindings binding (by simp [Tree.bindings, member])) tail)


/-- A returned compiler branch has exactly its original expression child and
no executed suffix, even if the source root list retains dead statements. -/
theorem Tree.at_return {policy : SourceCoreLoops.Policy} {checked : SourceCoreCompatibleCatalog.Checked}
    {source : TypedSource} {result : Ty} {reasonAt : ExpressionId → Word} {mode : Bool} {escaped : Word}
    {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {id : StatementId} {rest : List StatementId}
    {code : Expr} {node : StatementNode} {expression : ExpressionId}
    (tree : Tree policy source result reasonAt mode escaped fuel scope (id :: rest) code)
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement checked)
    (found : source.lookupStatement? id = some node) (form : node.form = .returnStmt (some expression)) :
    tree.closed = true ∧ tree.bindings = [] ∧
      ∀ child ∈ tree.children, child.expression = expression := by
  cases tree with
  | returning read original statementType child generated childType =>
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      cases same
      simp_all [Tree.closed, Tree.bindings, Tree.children]
  | returnUnit read original statementType unitType =>
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      cases same
      simp_all
  | initialized read original statementType projected child generated childType tail allocated =>
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      cases same
      simp_all
  | absent read original statementType projected tail allocated =>
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      cases same
      simp_all
  | boundary read outside accepted =>
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      cases same
      simp only [form, expanded] at outside
      cases outside


theorem Tree.at_return_list {policy : SourceCoreLoops.Policy} {checked : SourceCoreCompatibleCatalog.Checked}
    {source : TypedSource} {result : Ty} {reasonAt : ExpressionId → Word} {mode : Bool} {escaped : Word}
    {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {statements : List StatementId}
    {id : StatementId} {rest : List StatementId} {code : Expr} {node : StatementNode} {expression : ExpressionId}
    (tree : Tree policy source result reasonAt mode escaped fuel scope statements code)
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement checked)
    (same : statements = id :: rest)
    (found : source.lookupStatement? id = some node) (form : node.form = .returnStmt (some expression)) :
    tree.closed = true ∧ tree.bindings = [] ∧
      ∀ child ∈ tree.children, child.expression = expression := by
  subst statements
  exact tree.at_return readPolicy found form

end Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodyFlow
