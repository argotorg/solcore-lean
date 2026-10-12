import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedLexicalTree

/-! Straight-line staged statements include lexical bindings and bare plain assignments.
The existing imperative compiler tree retains actual assignment heads; this
shape only limits the supported Source grammar. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBareAssignmentTree
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof

inductive Shape (source : TypedSource) : List StatementId → Prop where
  | nil : Shape source []
  | returnUnit {id node} (rest : List StatementId)
      (found : source.lookupStatement? id = some node) (form : node.form = .returnStmt none) :
      Shape source (id :: rest)
  | returnValue {id node expression} (rest : List StatementId)
      (found : source.lookupStatement? id = some node) (form : node.form = .returnStmt (some expression)) :
      Shape source (id :: rest)
  | tail {id node expression}
      (found : source.lookupStatement? id = some node) (form : node.form = .expression expression false) :
      Shape source [id]
  | discard {id node expression rest}
      (found : source.lookupStatement? id = some node) (form : node.form = .expression expression true)
      (remaining : Shape source rest) : Shape source (id :: rest)
  | absent {id node binder rest}
      (found : source.lookupStatement? id = some node) (form : node.form = .letDecl binder none)
      (remaining : Shape source rest) : Shape source (id :: rest)
  | initialized {id node binder expression rest}
      (found : source.lookupStatement? id = some node) (form : node.form = .letDecl binder (some expression))
      (remaining : Shape source rest) : Shape source (id :: rest)

  | assign {id node assignment rhs rest}
      (found : source.lookupStatement? id = some node)
      (form : node.form = .assignValue assignment .equal rhs)
      (bare : assignment.target.projections = [])
      (remaining : Shape source rest) : Shape source (id :: rest)

private theorem node_eq {source : TypedSource} {id : StatementId} {first second : StatementNode}
    (left : source.lookupStatement? id = some first)
    (right : source.lookupStatement? id = some second) : first = second :=
  Option.some.inj (left.symm.trans right)

/-- A supported continuing statement retains its exact tail shape. -/
theorem Shape.tail_of_let {source : TypedSource} {id : StatementId} {node : StatementNode}
    {binder : TypedBinder} {initializer : Option ExpressionId} {rest : List StatementId}
    (shape : Shape source (id :: rest))
    (found : source.lookupStatement? id = some node)
    (form : node.form = .letDecl binder initializer) : Shape source rest := by
  cases shape with
  | returnUnit _ actual same | returnValue _ actual same | tail actual same
  | discard actual same _ | assign actual same _ _ =>
      cases node_eq found actual
      rw [form] at same
      cases same
  | absent actual same remaining | initialized actual same remaining => exact remaining

theorem Shape.discard_tail {source : TypedSource} {id : StatementId} {node : StatementNode}
    {expression : ExpressionId} {semicolon : Bool} {rest : List StatementId}
    (shape : Shape source (id :: rest))
    (found : source.lookupStatement? id = some node)
    (form : node.form = .expression expression semicolon)
    (notTail : (!semicolon && true && rest.isEmpty) = false) :
    semicolon = true ∧ Shape source rest := by
  cases shape with
  | returnUnit _ actual same | returnValue _ actual same | absent actual same _
  | initialized actual same _ | assign actual same _ _ =>
      cases node_eq found actual
      rw [form] at same
      cases same
  | tail actual same =>
      cases node_eq found actual
      rw [form] at same
      cases same
      simp at notTail
  | discard actual same remaining =>
      cases node_eq found actual
      rw [form] at same
      cases same
      exact ⟨rfl, remaining⟩

theorem Shape.not_block {source : TypedSource} {id : StatementId} {node : StatementNode}
    {statements rest : List StatementId}
    (shape : Shape source (id :: rest))
    (found : source.lookupStatement? id = some node)
    (form : node.form = .block statements) : False := by
  cases shape with
  | returnUnit _ actual same | returnValue _ actual same | tail actual same
  | discard actual same _ | absent actual same _ | initialized actual same _ | assign actual same _ _ =>
      cases node_eq found actual
      rw [form] at same
      cases same

theorem Shape.not_if {source : TypedSource} {id : StatementId} {node : StatementNode}
    {condition : ExpressionId} {thenBody : List StatementId} {elseBody : Option (List StatementId)}
    {rest : List StatementId}
    (shape : Shape source (id :: rest))
    (found : source.lookupStatement? id = some node)
    (form : node.form = .ifThen condition thenBody elseBody) : False := by
  cases shape with
  | returnUnit _ actual same | returnValue _ actual same | tail actual same
  | discard actual same _ | absent actual same _ | initialized actual same _ | assign actual same _ _ =>
      cases node_eq found actual
      rw [form] at same
      cases same

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBareAssignmentTree
