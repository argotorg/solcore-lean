import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBareAssignmentShapeFacts

/-! The supported imperative fragment keeps branch arms in scoped mode. Its
shape is a restriction on original syntax, independent of execution. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBranchingTree
open Core Frontend SourceInference

inductive Shape (source : TypedSource) : Bool → List StatementId → Prop where
  | nil {mode} : Shape source mode []
  | returnUnit {mode id node} (rest : List StatementId)
      (found : source.lookupStatement? id = some node) (form : node.form = .returnStmt none) :
      Shape source mode (id :: rest)
  | returnValue {mode id node expression} (rest : List StatementId)
      (found : source.lookupStatement? id = some node) (form : node.form = .returnStmt (some expression)) :
      Shape source mode (id :: rest)
  | tail {id node expression}
      (found : source.lookupStatement? id = some node) (form : node.form = .expression expression false) :
      Shape source true [id]
  | discard {mode id node expression semicolon rest}
      (found : source.lookupStatement? id = some node) (form : node.form = .expression expression semicolon)
      (continuing : semicolon = true ∨ mode = false)
      (remaining : Shape source mode rest) : Shape source mode (id :: rest)
  | absent {mode id node binder rest}
      (found : source.lookupStatement? id = some node) (form : node.form = .letDecl binder none)
      (remaining : Shape source mode rest) : Shape source mode (id :: rest)
  | initialized {mode id node binder expression rest}
      (found : source.lookupStatement? id = some node) (form : node.form = .letDecl binder (some expression))
      (remaining : Shape source mode rest) : Shape source mode (id :: rest)
  | assign {mode id node assignment rhs rest}
      (found : source.lookupStatement? id = some node)
      (form : node.form = .assignValue assignment .equal rhs)
      (bare : assignment.target.projections = [])
      (remaining : Shape source mode rest) : Shape source mode (id :: rest)
  | conditional {mode id node condition thenBody elseBody rest}
      (found : source.lookupStatement? id = some node)
      (form : node.form = .ifThen condition thenBody elseBody)
      (left : Shape source false thenBody)
      (right : Shape source false (elseBody.getD []))
      (remaining : Shape source mode rest) : Shape source mode (id :: rest)

def allowedForm : StatementForm → Bool
  | .returnStmt _ | .expression _ _ | .letDecl _ _ | .ifThen _ _ _ => true
  | .assignValue assignment .equal _ => assignment.target.projections.isEmpty
  | _ => false

private theorem node_eq {source : TypedSource} {id : StatementId} {first second : StatementNode}
    (left : source.lookupStatement? id = some first)
    (right : source.lookupStatement? id = some second) : first = second :=
  Option.some.inj (left.symm.trans right)

theorem Shape.head_allowed {source mode id node rest}
    (shape : Shape source mode (id :: rest))
    (found : source.lookupStatement? id = some node) : allowedForm node.form = true := by
  cases shape with
  | returnUnit _ actual form | returnValue _ actual form | tail actual form
  | discard actual form _ _ | absent actual form _ | initialized actual form _
  | conditional actual form _ _ _ =>
      cases node_eq found actual
      simp only [form, allowedForm]
  | assign actual form bare _ =>
      cases node_eq found actual
      simp only [form, allowedForm, bare, List.isEmpty_nil]

theorem Shape.tail_of_let {source mode id node binder initializer rest}
    (shape : Shape source mode (id :: rest))
    (found : source.lookupStatement? id = some node)
    (form : node.form = .letDecl binder initializer) : Shape source mode rest := by
  cases shape with
  | returnUnit _ actual same | returnValue _ actual same | tail actual same
  | discard actual same _ _ | assign actual same _ _ | conditional actual same _ _ _ =>
      cases node_eq found actual
      rw [form] at same
      cases same
  | absent actual same remaining | initialized actual same remaining => exact remaining

theorem Shape.discard_tail {source mode id node expression semicolon rest}
    (shape : Shape source mode (id :: rest))
    (found : source.lookupStatement? id = some node)
    (form : node.form = .expression expression semicolon)
    (notTail : (!semicolon && mode && rest.isEmpty) = false) :
    (semicolon = true ∨ mode = false) ∧ Shape source mode rest := by
  cases shape with
  | returnUnit _ actual same | returnValue _ actual same | absent actual same _
  | initialized actual same _ | assign actual same _ _ | conditional actual same _ _ _ =>
      cases node_eq found actual
      rw [form] at same
      cases same
  | tail actual same =>
      cases node_eq found actual
      rw [form] at same
      cases same
      simp at notTail
  | discard actual same continuing remaining =>
      cases node_eq found actual
      rw [form] at same
      cases same
      exact ⟨continuing, remaining⟩

theorem Shape.assign_tail {source mode id node assignment operator rhs rest}
    (shape : Shape source mode (id :: rest)) (found : source.lookupStatement? id = some node)
    (form : node.form = .assignValue assignment operator rhs) :
    operator = .equal ∧ assignment.target.projections = [] ∧ Shape source mode rest := by
  cases shape with
  | returnUnit _ actual same | returnValue _ actual same | tail actual same
  | discard actual same _ _ | absent actual same _ | initialized actual same _
  | conditional actual same _ _ _ =>
      cases node_eq found actual
      rw [form] at same
      cases same
  | assign actual same bare remaining =>
      cases node_eq found actual
      rw [form] at same
      cases same
      exact ⟨rfl, bare, remaining⟩

theorem Shape.branches {source mode id node condition thenBody elseBody rest}
    (shape : Shape source mode (id :: rest)) (found : source.lookupStatement? id = some node)
    (form : node.form = .ifThen condition thenBody elseBody) :
    Shape source false thenBody ∧ Shape source false (elseBody.getD []) ∧ Shape source mode rest := by
  cases shape with
  | returnUnit _ actual same | returnValue _ actual same | tail actual same
  | discard actual same _ _ | absent actual same _ | initialized actual same _ | assign actual same _ _ =>
      cases node_eq found actual
      rw [form] at same
      cases same
  | conditional actual same left right remaining =>
      cases node_eq found actual
      rw [form] at same
      cases same
      exact ⟨left, right, remaining⟩

theorem Shape.not_block {source mode id node statements rest}
    (shape : Shape source mode (id :: rest)) (found : source.lookupStatement? id = some node)
    (form : node.form = .block statements) : False := by
  have no := shape.head_allowed found
  simp only [form, allowedForm, Bool.false_eq_true] at no

theorem Shape.of_bare {source statements}
    (shape : CallableIndexedOwnedPreparedStagedBareAssignmentTree.Shape source statements) :
    Shape source true statements := by
  induction shape with
  | nil => exact .nil
  | returnUnit rest found form => exact .returnUnit rest found form
  | returnValue rest found form => exact .returnValue rest found form
  | tail found form => exact .tail found form
  | discard found form _ ih => exact .discard found form (.inl rfl) ih
  | absent found form _ ih => exact .absent found form ih
  | initialized found form _ ih => exact .initialized found form ih
  | assign found form bare _ ih => exact .assign found form bare ih

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBranchingTree
