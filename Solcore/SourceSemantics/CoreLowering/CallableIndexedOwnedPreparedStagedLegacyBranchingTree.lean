import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBranchingTree
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBareAssignmentShapeFacts

/-! The supported imperative fragment keeps branch arms and loop bodies in scoped mode. Its
shape is a restriction on original syntax, independent of execution. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedLegacyBranchingTree
open Core Frontend SourceInference

/-- The staged header fragment uses genuine lexical items and bare equal or raw Word compound writes. -/
inductive ItemShape : List ForItemForm → Prop where
  | nil : ItemShape []
  | absent {binder rest} (remaining : ItemShape rest) :
      ItemShape (.letDecl binder none :: rest)
  | initialized {binder expression rest} (remaining : ItemShape rest) :
      ItemShape (.letDecl binder (some expression) :: rest)
  | discard {expression rest} (remaining : ItemShape rest) :
      ItemShape (.expression expression :: rest)
  | assign {assignment operator rhs rest}
      (profile : operator = .equal ∨ assignment.target.type = .word) (bare : assignment.target.projections = [])
      (remaining : ItemShape rest) : ItemShape (.assignValue assignment operator rhs :: rest)
  | bitNot {assignment rest}
      (profile : assignment.target.type = .word) (bare : assignment.target.projections = [])
      (remaining : ItemShape rest) : ItemShape (.assignBitNot assignment :: rest)

theorem ItemShape.let_tail {binder initializer rest}
    (shape : ItemShape (.letDecl binder initializer :: rest)) : ItemShape rest := by
  cases shape with
  | absent remaining | initialized remaining => exact remaining

theorem ItemShape.discard_tail {expression rest}
    (shape : ItemShape (.expression expression :: rest)) : ItemShape rest := by
  cases shape with | discard remaining => exact remaining

theorem ItemShape.assign_tail {assignment operator rhs rest}
    (shape : ItemShape (.assignValue assignment operator rhs :: rest)) :
    (operator = .equal ∨ assignment.target.type = .word) ∧ assignment.target.projections = [] ∧ ItemShape rest := by
  cases shape with | assign profile bare remaining => exact ⟨profile, bare, remaining⟩

theorem ItemShape.bitNot_tail {assignment rest}
    (shape : ItemShape (.assignBitNot assignment :: rest)) :
    assignment.target.type = .word ∧ assignment.target.projections = [] ∧ ItemShape rest := by
  cases shape with | bitNot profile bare remaining => exact ⟨profile, bare, remaining⟩

inductive Shape (source : TypedSource) : Bool → List StatementId → Prop where
  | nil {mode} : Shape source mode []
  | returnUnit {mode id node} (rest : List StatementId)
      (found : source.lookupStatement? id = some node) (form : node.form = .returnStmt none) :
      Shape source mode (id :: rest)
  | returnValue {mode id node expression} (rest : List StatementId)
      (found : source.lookupStatement? id = some node) (form : node.form = .returnStmt (some expression)) :
      Shape source mode (id :: rest)
  | breaking {mode id node} (rest : List StatementId)
      (found : source.lookupStatement? id = some node) (form : node.form = .breakStmt) :
      Shape source mode (id :: rest)
  | continuing {mode id node} (rest : List StatementId)
      (found : source.lookupStatement? id = some node) (form : node.form = .continueStmt) :
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
  | assign {mode id node assignment operator rhs rest}
      (found : source.lookupStatement? id = some node)
      (form : node.form = .assignValue assignment operator rhs)
      (profile : operator = .equal ∨ assignment.target.type = .word)
      (bare : assignment.target.projections = [])
      (remaining : Shape source mode rest) : Shape source mode (id :: rest)
  | bitNot {mode id node assignment rest}
      (found : source.lookupStatement? id = some node)
      (form : node.form = .assignBitNot assignment)
      (profile : assignment.target.type = .word)
      (bare : assignment.target.projections = [])
      (remaining : Shape source mode rest) : Shape source mode (id :: rest)
  | conditional {mode id node condition thenBody elseBody rest}
      (found : source.lookupStatement? id = some node)
      (form : node.form = .ifThen condition thenBody elseBody)
      (left : Shape source false thenBody)
      (right : Shape source false (elseBody.getD []))
      (remaining : Shape source mode rest) : Shape source mode (id :: rest)
  | whileLoop {mode id node condition body rest}
      (found : source.lookupStatement? id = some node)
      (form : node.form = .whileLoop condition body)
      (inner : Shape source false body)
      (remaining : Shape source mode rest) : Shape source mode (id :: rest)
  | block {mode id node body rest}
      (found : source.lookupStatement? id = some node)
      (form : node.form = .block body)
      (inner : Shape source false body)
      (remaining : Shape source mode rest) : Shape source mode (id :: rest)

  | matchWith {mode id node resolution rest}
      (found : source.lookupStatement? id = some node)
      (form : node.form = .matchWith resolution)
      (arms : ∀ arm ∈ resolution.cases, Shape source false arm.body)
      (fallback : ∀ statements, resolution.defaultBody = some statements → Shape source false statements)
      (remaining : Shape source mode rest) : Shape source mode (id :: rest)

  | forLoop {mode id node initializer condition post body rest}
      (found : source.lookupStatement? id = some node)
      (form : node.form = .forLoop initializer condition post body)
      (initial : ItemShape initializer) (after : ItemShape post)
      (inner : Shape source false body)
      (remaining : Shape source mode rest) : Shape source mode (id :: rest)

/-- Every actual compiler position retains its own supported syntax. -/
def PositionShape (source : TypedSource) : GenericImperativeMatch.Position → Prop
  | .statements mode statements => Shape source mode statements
  | .initializers items _ post statements =>
      ItemShape items ∧ ItemShape post ∧ Shape source false statements

def allowedForm : StatementForm → Bool
  | .returnStmt _ | .breakStmt | .continueStmt | .expression _ _ | .letDecl _ _ | .ifThen _ _ _ | .whileLoop _ _ | .block _ | .matchWith _ | .forLoop _ _ _ _ => true
  | .assignValue assignment operator _ =>
      (operator == .equal || assignment.target.type == .word) && assignment.target.projections.isEmpty
  | .assignBitNot assignment =>
      assignment.target.type == .word && assignment.target.projections.isEmpty

private theorem node_eq {source : TypedSource} {id : StatementId} {first second : StatementNode}
    (left : source.lookupStatement? id = some first)
    (right : source.lookupStatement? id = some second) : first = second :=
  Option.some.inj (left.symm.trans right)

theorem Shape.head_allowed {source mode id node rest}
    (shape : Shape source mode (id :: rest))
    (found : source.lookupStatement? id = some node) : allowedForm node.form = true := by
  cases shape with
  | returnUnit _ actual form | returnValue _ actual form | breaking _ actual form | continuing _ actual form | tail actual form
  | discard actual form _ _ | absent actual form _ | initialized actual form _
  | conditional actual form _ _ _ | whileLoop actual form _ _ | block actual form _ _
  | matchWith actual form _ _ _ | forLoop actual form _ _ _ _ =>
      cases node_eq found actual
      simp only [form, allowedForm]
  | assign actual form profile bare _ =>
      cases node_eq found actual
      rcases profile with rfl | word
      · simp [form, allowedForm, bare]
      · simp [form, allowedForm, bare, word]
  | bitNot actual form profile bare _ =>
      cases node_eq found actual
      simp [form, allowedForm, bare, profile]

theorem Shape.tail_of_let {source mode id node binder initializer rest}
    (shape : Shape source mode (id :: rest))
    (found : source.lookupStatement? id = some node)
    (form : node.form = .letDecl binder initializer) : Shape source mode rest := by
  cases shape with
  | forLoop actual same _ _ _ _ =>
      cases node_eq found actual
      rw [form] at same
      cases same
  | returnUnit _ actual same | returnValue _ actual same | breaking _ actual same | continuing _ actual same | tail actual same
  | discard actual same _ _ | assign actual same _ _ _ | bitNot actual same _ _ _ | conditional actual same _ _ _ | whileLoop actual same _ _ | block actual same _ _ | matchWith actual same _ _ _ =>
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
  | forLoop actual same _ _ _ _ =>
      cases node_eq found actual
      rw [form] at same
      cases same
  | returnUnit _ actual same | returnValue _ actual same | breaking _ actual same | continuing _ actual same | absent actual same _
  | initialized actual same _ | assign actual same _ _ _ | bitNot actual same _ _ _ | conditional actual same _ _ _ | whileLoop actual same _ _ | block actual same _ _ | matchWith actual same _ _ _ =>
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
    (operator = .equal ∨ assignment.target.type = .word) ∧ assignment.target.projections = [] ∧ Shape source mode rest := by
  cases shape with
  | forLoop actual same _ _ _ _ =>
      cases node_eq found actual
      rw [form] at same
      cases same
  | returnUnit _ actual same | returnValue _ actual same | breaking _ actual same | continuing _ actual same | tail actual same
  | discard actual same _ _ | absent actual same _ | initialized actual same _ | bitNot actual same _ _ _
  | conditional actual same _ _ _ | whileLoop actual same _ _ | block actual same _ _ | matchWith actual same _ _ _ =>
      cases node_eq found actual
      rw [form] at same
      cases same
  | assign actual same profile bare remaining =>
      cases node_eq found actual
      rw [form] at same
      cases same
      exact ⟨profile, bare, remaining⟩

theorem Shape.bitNot_tail {source mode id node assignment rest}
    (shape : Shape source mode (id :: rest)) (found : source.lookupStatement? id = some node)
    (form : node.form = .assignBitNot assignment) :
    assignment.target.type = .word ∧ assignment.target.projections = [] ∧ Shape source mode rest := by
  cases shape with
  | forLoop actual same _ _ _ _ =>
      cases node_eq found actual
      rw [form] at same
      cases same
  | returnUnit _ actual same | returnValue _ actual same | breaking _ actual same | continuing _ actual same | tail actual same
  | discard actual same _ _ | absent actual same _ | initialized actual same _ | assign actual same _ _ _
  | conditional actual same _ _ _ | whileLoop actual same _ _ | block actual same _ _ | matchWith actual same _ _ _ =>
      cases node_eq found actual
      rw [form] at same
      cases same
  | bitNot actual same profile bare remaining =>
      cases node_eq found actual
      rw [form] at same
      cases same
      exact ⟨profile, bare, remaining⟩

theorem Shape.branches {source mode id node condition thenBody elseBody rest}
    (shape : Shape source mode (id :: rest)) (found : source.lookupStatement? id = some node)
    (form : node.form = .ifThen condition thenBody elseBody) :
    Shape source false thenBody ∧ Shape source false (elseBody.getD []) ∧ Shape source mode rest := by
  cases shape with
  | forLoop actual same _ _ _ _ =>
      cases node_eq found actual
      rw [form] at same
      cases same
  | returnUnit _ actual same | returnValue _ actual same | breaking _ actual same | continuing _ actual same | tail actual same
  | discard actual same _ _ | absent actual same _ | initialized actual same _ | assign actual same _ _ _ | bitNot actual same _ _ _
  | whileLoop actual same _ _ | block actual same _ _ | matchWith actual same _ _ _ =>
      cases node_eq found actual
      rw [form] at same
      cases same
  | conditional actual same left right remaining =>
      cases node_eq found actual
      rw [form] at same
      cases same
      exact ⟨left, right, remaining⟩

theorem Shape.loop {source mode id node condition body rest}
    (shape : Shape source mode (id :: rest)) (found : source.lookupStatement? id = some node)
    (form : node.form = .whileLoop condition body) :
    Shape source false body ∧ Shape source mode rest := by
  cases shape with
  | forLoop actual same _ _ _ _ =>
      cases node_eq found actual
      rw [form] at same
      cases same
  | returnUnit _ actual same | returnValue _ actual same | breaking _ actual same | continuing _ actual same | tail actual same
  | discard actual same _ _ | absent actual same _ | initialized actual same _ | assign actual same _ _ _ | bitNot actual same _ _ _
  | conditional actual same _ _ _ | block actual same _ _ | matchWith actual same _ _ _ =>
      cases node_eq found actual
      rw [form] at same
      cases same
  | whileLoop actual same inner remaining =>
      cases node_eq found actual
      rw [form] at same
      cases same
      exact ⟨inner, remaining⟩

theorem Shape.block_children {source mode id node body rest}
    (shape : Shape source mode (id :: rest)) (found : source.lookupStatement? id = some node)
    (form : node.form = .block body) :
    Shape source false body ∧ Shape source mode rest := by
  cases shape with
  | forLoop actual same _ _ _ _ =>
      cases node_eq found actual
      rw [form] at same
      cases same
  | returnUnit _ actual same | returnValue _ actual same | breaking _ actual same | continuing _ actual same | tail actual same
  | discard actual same _ _ | absent actual same _ | initialized actual same _ | assign actual same _ _ _ | bitNot actual same _ _ _
  | conditional actual same _ _ _ | whileLoop actual same _ _ | matchWith actual same _ _ _ =>
      cases node_eq found actual
      rw [form] at same
      cases same
  | block actual same inner remaining =>
      cases node_eq found actual
      rw [form] at same
      cases same
      exact ⟨inner, remaining⟩

theorem Shape.match_children {source mode id node resolution rest}
    (shape : Shape source mode (id :: rest)) (found : source.lookupStatement? id = some node)
    (form : node.form = .matchWith resolution) :
    (∀ arm ∈ resolution.cases, Shape source false arm.body) ∧
    (∀ statements, resolution.defaultBody = some statements → Shape source false statements) ∧
    Shape source mode rest := by
  cases shape with
  | forLoop actual same _ _ _ _ =>
      cases node_eq found actual
      rw [form] at same
      cases same
  | returnUnit _ actual same | returnValue _ actual same | breaking _ actual same | continuing _ actual same | tail actual same
  | discard actual same _ _ | absent actual same _ | initialized actual same _ | assign actual same _ _ _ | bitNot actual same _ _ _
  | conditional actual same _ _ _ | whileLoop actual same _ _ | block actual same _ _ =>
      cases node_eq found actual
      rw [form] at same
      cases same
  | matchWith actual same arms fallback remaining =>
      cases node_eq found actual
      rw [form] at same
      cases same
      exact ⟨arms, fallback, remaining⟩

theorem Shape.match_request {source mode id node resolution rest parent type request childContext}
    (shape : Shape source mode (id :: rest)) (found : source.lookupStatement? id = some node)
    (form : node.form = .matchWith resolution)
    (context : GenericMatchChildren.ContextFor source parent type resolution.cases
      resolution.defaultBody request childContext) : Shape source false request.statements := by
  obtain ⟨arms, fallback, _⟩ := shape.match_children found form
  cases context with
  | arm member statements _ _ => rw [statements]; exact arms _ member
  | default statements => exact fallback _ statements

theorem Shape.for_children {source mode id node initializer condition post body rest}
    (shape : Shape source mode (id :: rest)) (found : source.lookupStatement? id = some node)
    (form : node.form = .forLoop initializer condition post body) :
    ItemShape initializer ∧ ItemShape post ∧ Shape source false body ∧ Shape source mode rest := by
  cases shape with
  | returnUnit _ actual same | returnValue _ actual same | breaking _ actual same | continuing _ actual same | tail actual same
  | discard actual same _ _ | absent actual same _ | initialized actual same _ | assign actual same _ _ _ | bitNot actual same _ _ _
  | conditional actual same _ _ _ | whileLoop actual same _ _ | block actual same _ _
  | matchWith actual same _ _ _ =>
      cases node_eq found actual
      rw [form] at same
      cases same
  | forLoop actual same initial after inner remaining =>
      cases node_eq found actual
      rw [form] at same
      cases same
      exact ⟨initial, after, inner, remaining⟩

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
  | assign found form bare _ ih => exact .assign found form (.inl rfl) bare ih

theorem ItemShape.forget {items} (shape : ItemShape items) :
    CallableIndexedOwnedPreparedStagedBranchingTree.ItemShape items := by
  induction shape with
  | nil => exact .nil
  | absent _ ih => exact .absent ih
  | initialized _ ih => exact .initialized ih
  | discard _ ih => exact .discard ih
  | assign profile bare _ ih => exact .assign profile bare ih
  | bitNot profile bare _ ih => exact .bitNot profile bare ih

theorem Shape.forget {source mode statements} (shape : Shape source mode statements) :
    CallableIndexedOwnedPreparedStagedBranchingTree.Shape source mode statements := by
  induction shape with
  | nil => exact .nil
  | returnUnit rest found form => exact .returnUnit rest found form
  | returnValue rest found form => exact .returnValue rest found form
  | breaking rest found form => exact .breaking rest found form
  | continuing rest found form => exact .continuing rest found form
  | tail found form => exact .tail found form
  | discard found form continuing _ ih => exact .discard found form continuing ih
  | absent found form _ ih => exact .absent found form ih
  | initialized found form _ ih => exact .initialized found form ih
  | assign found form profile bare _ ih => exact .assign found form profile bare ih
  | bitNot found form profile bare _ ih => exact .bitNot found form profile bare ih
  | conditional found form _ _ _ left right remaining => exact .conditional found form left right remaining
  | whileLoop found form _ _ inner remaining => exact .whileLoop found form inner remaining
  | block found form _ _ inner remaining => exact .block found form inner remaining
  | matchWith found form _ _ _ arms fallback remaining => exact .matchWith found form arms fallback remaining
  | forLoop found form initial after _ _ inner remaining => exact .forLoop found form initial.forget after.forget inner remaining

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedLegacyBranchingTree
