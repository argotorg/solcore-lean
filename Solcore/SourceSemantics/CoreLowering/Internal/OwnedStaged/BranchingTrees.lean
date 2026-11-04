import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.OrdinaryLambdas
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedTerminalBody
import Solcore.SourceSemantics.CoreLowering.GenericImperativeMatchTree
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBodyRestorationAdmission
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedExpressionBounds
import Solcore.SourceSemantics.Staging.RecursiveTraceSize
import Solcore.SourceSemantics.Staging.RecursiveBodyErasure
import Solcore.SourceSemantics.CoreLowering.TypedMixedNamedBodyMeaning

/-!
# Staged bounds: statement trees

Lexical, branching and bare-assignment trees of staged bodies, with their shape facts, Source inversion and exit receipts.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedLexicalTree
/-! The staged lexical fragment uses the existing compiler tree and actual
marked allocations. Only statement shapes admitted by the staged Source
relation are selected; expression receipts remain indexed by their genuine
lexical contexts. No semantic law is stored in this tree. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedLexicalTree
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

/-- Typed receipts are obtained from original Source typing during the actual
compiler-tree extraction, including every context reached after a let. -/
def TypedCertificate (source : TypedSource)
    (certificate : SourceSemantics.Context → GenericExpressionMeaning.Certificate)
    (context : SourceSemantics.Context) : GenericExpressionMeaning.Certificate :=
  fun scope id lowered => ∃ node, source.lookupExpression? id = some node ∧
    ExpressionHasType source context id node.type ∧ certificate context scope id lowered

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
  | discard actual same _ =>
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
  | initialized actual same _ =>
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
  | discard actual same _ | absent actual same _ | initialized actual same _ =>
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
  | discard actual same _ | absent actual same _ | initialized actual same _ =>
      cases node_eq found actual
      rw [form] at same
      cases same

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedLexicalTree
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBareAssignmentTree
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBareAssignmentShapeFacts
/-! Static restrictions of the bare assignment fragment. These facts select
actual statement forms; they do not assume execution or child meaning. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBareAssignmentTree
open Core Frontend SourceInference

/-- Only these original statement forms enter the straight-line fold. -/
def allowedForm : StatementForm → Bool
  | .returnStmt _ | .expression _ _ | .letDecl _ _ => true
  | .assignValue assignment .equal _ => assignment.target.projections.isEmpty
  | _ => false

theorem Shape.head_allowed {source : TypedSource} {id : StatementId} {node : StatementNode}
    {rest : List StatementId} (shape : Shape source (id :: rest))
    (found : source.lookupStatement? id = some node) : allowedForm node.form = true := by
  cases shape with
  | returnUnit _ actual form | returnValue _ actual form | tail actual form
  | discard actual form _ | absent actual form _ | initialized actual form _ =>
      cases node_eq found actual
      simp only [form, allowedForm]
  | assign actual form bare _ =>
      cases node_eq found actual
      simp only [form, allowedForm, bare, List.isEmpty_nil]

theorem Shape.assign_tail {source : TypedSource} {id : StatementId} {node : StatementNode}
    {assignment : AssignmentResolution} {operator : Solcore.Syntax.ValueAssignOp}
    {rhs : ExpressionId} {rest : List StatementId}
    (shape : Shape source (id :: rest)) (found : source.lookupStatement? id = some node)
    (form : node.form = .assignValue assignment operator rhs) :
    operator = .equal ∧ assignment.target.projections = [] ∧ Shape source rest := by
  cases shape with
  | returnUnit _ actual same | returnValue _ actual same | tail actual same
  | discard actual same _ | absent actual same _ | initialized actual same _ =>
      cases node_eq found actual
      rw [form] at same
      cases same
  | assign actual same bare remaining =>
      cases node_eq found actual
      rw [form] at same
      cases same
      exact ⟨rfl, bare, remaining⟩

/-- A lexical leaf of the imperative certificate has the original lexical
shape. No assignment is hidden under the leaf constructor. -/
theorem Shape.lexical_of_syntax {source : TypedSource} {expressions : ExpressionId → Prop}
    {context : SourceSemantics.Context} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty}
    (syntaxTree : GenericLexicalStatements.Syntax source expressions context mode statements expected)
    (shape : Shape source statements) (tailMode : mode = true) :
    CallableIndexedOwnedPreparedStagedLexicalTree.Shape source statements := by
  induction syntaxTree with
  | nil _ => exact .nil
  | returnUnit rest found form _ => exact .returnUnit rest found form
  | returnValue rest found form _ _ _ _ _ => exact .returnValue rest found form
  | tail found form _ _ _ _ _ => exact .tail found form
  | uninitialized found form _ _ _ _ _ ih => exact .absent found form (ih (shape.tail_of_let found form) tailMode)
  | initialized found form _ _ _ _ _ _ _ _ _ ih => exact .initialized found form (ih (shape.tail_of_let found form) tailMode)
  | discard found form notTail _ _ _ _ _ ih =>
      rw [tailMode] at notTail
      obtain ⟨same, remaining⟩ := shape.discard_tail found form notTail
      cases same
      exact .discard found form (ih remaining tailMode)
  | block found form _ _ _ _ _ | terminalBlock _ found form _ _ _ _ =>
      exact False.elim (shape.not_block found form)
  | ifThen found form _ _ _ _ _ _ _ _ _ _ _ | terminalIf _ found form _ _ _ _ _ _ _ _ _ _ _ =>
      exact False.elim (shape.not_if found form)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBareAssignmentTree
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBranchingTree
/-! The supported imperative fragment keeps branch arms and loop bodies in scoped mode. Its
shape is a restriction on original syntax, independent of execution. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBranchingTree
open Core Frontend SourceInference

/-- The staged header fragment uses genuine lexical items and equal or raw Word compound writes. -/
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
  | assignProjected {assignment operator rhs rest}
      (profile : operator = .equal ∨ assignment.target.type = .word) (projected : assignment.target.projections ≠ [])
      (remaining : ItemShape rest) : ItemShape (.assignValue assignment operator rhs :: rest)
  | bitNot {assignment rest}
      (profile : assignment.target.type = .word) (bare : assignment.target.projections = [])
      (remaining : ItemShape rest) : ItemShape (.assignBitNot assignment :: rest)
  | bitNotProjected {assignment rest}
      (profile : assignment.target.type = .word) (projected : assignment.target.projections ≠ [])
      (remaining : ItemShape rest) : ItemShape (.assignBitNot assignment :: rest)

theorem ItemShape.let_tail {binder initializer rest}
    (shape : ItemShape (.letDecl binder initializer :: rest)) : ItemShape rest := by
  cases shape with
  | absent remaining | initialized remaining => exact remaining

theorem ItemShape.discard_tail {expression rest}
    (shape : ItemShape (.expression expression :: rest)) : ItemShape rest := by
  cases shape with | discard remaining => exact remaining

theorem ItemShape.assignment_tail {assignment operator rhs rest}
    (shape : ItemShape (.assignValue assignment operator rhs :: rest)) :
    (operator = .equal ∨ assignment.target.type = .word) ∧ ItemShape rest := by
  cases shape with
  | assign profile _ remaining | assignProjected profile _ remaining => exact ⟨profile, remaining⟩

theorem ItemShape.assign_tail {assignment operator rhs rest}
    (shape : ItemShape (.assignValue assignment operator rhs :: rest))
    (bare : assignment.target.projections = []) :
    (operator = .equal ∨ assignment.target.type = .word) ∧ assignment.target.projections = [] ∧ ItemShape rest :=
  ⟨shape.assignment_tail.1, bare, shape.assignment_tail.2⟩

theorem ItemShape.unary_tail {assignment rest}
    (shape : ItemShape (.assignBitNot assignment :: rest)) :
    assignment.target.type = .word ∧ ItemShape rest := by
  cases shape with
  | bitNot profile _ remaining | bitNotProjected profile _ remaining => exact ⟨profile, remaining⟩

theorem ItemShape.bitNot_tail {assignment rest}
    (shape : ItemShape (.assignBitNot assignment :: rest)) (bare : assignment.target.projections = []) :
    assignment.target.type = .word ∧ assignment.target.projections = [] ∧ ItemShape rest :=
  ⟨shape.unary_tail.1, bare, shape.unary_tail.2⟩

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
  | assignProjected {mode id node assignment operator rhs rest}
      (found : source.lookupStatement? id = some node)
      (form : node.form = .assignValue assignment operator rhs)
      (profile : operator = .equal ∨ assignment.target.type = .word)
      (projected : assignment.target.projections ≠ [])
      (remaining : Shape source mode rest) : Shape source mode (id :: rest)
  | bitNot {mode id node assignment rest}
      (found : source.lookupStatement? id = some node)
      (form : node.form = .assignBitNot assignment)
      (profile : assignment.target.type = .word)
      (bare : assignment.target.projections = [])
      (remaining : Shape source mode rest) : Shape source mode (id :: rest)
  | bitNotProjected {mode id node assignment rest}
      (found : source.lookupStatement? id = some node)
      (form : node.form = .assignBitNot assignment)
      (profile : assignment.target.type = .word)
      (projected : assignment.target.projections ≠ [])
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
      operator == .equal || assignment.target.type == .word
  | .assignBitNot assignment =>
      assignment.target.type == .word

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
  | assign actual form profile _ _ | assignProjected actual form profile _ _ =>
      cases node_eq found actual
      rcases profile with rfl | word
      · simp [form, allowedForm]
      · simp [form, allowedForm, word]
  | bitNot actual form profile _ _ | bitNotProjected actual form profile _ _ =>
      cases node_eq found actual
      simp [form, allowedForm, profile]

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
  | discard actual same _ _ | assign actual same _ _ _ | assignProjected actual same _ _ _ | bitNot actual same _ _ _ | bitNotProjected actual same _ _ _ | conditional actual same _ _ _ | whileLoop actual same _ _ | block actual same _ _ | matchWith actual same _ _ _ =>
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
  | initialized actual same _ | assign actual same _ _ _ | assignProjected actual same _ _ _ | bitNot actual same _ _ _ | bitNotProjected actual same _ _ _ | conditional actual same _ _ _ | whileLoop actual same _ _ | block actual same _ _ | matchWith actual same _ _ _ =>
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

theorem Shape.assignment_tail {source mode id node assignment operator rhs rest}
    (shape : Shape source mode (id :: rest)) (found : source.lookupStatement? id = some node)
    (form : node.form = .assignValue assignment operator rhs) :
    (operator = .equal ∨ assignment.target.type = .word) ∧ Shape source mode rest := by
  cases shape with
  | forLoop actual same _ _ _ _ =>
      cases node_eq found actual
      rw [form] at same
      cases same
  | returnUnit _ actual same | returnValue _ actual same | breaking _ actual same | continuing _ actual same | tail actual same
  | discard actual same _ _ | absent actual same _ | initialized actual same _ | bitNot actual same _ _ _ | bitNotProjected actual same _ _ _
  | conditional actual same _ _ _ | whileLoop actual same _ _ | block actual same _ _ | matchWith actual same _ _ _ =>
      cases node_eq found actual
      rw [form] at same
      cases same
  | assign actual same profile _ remaining | assignProjected actual same profile _ remaining =>
      cases node_eq found actual
      rw [form] at same
      cases same
      exact ⟨profile, remaining⟩

theorem Shape.assign_tail {source mode id node assignment operator rhs rest}
    (shape : Shape source mode (id :: rest)) (found : source.lookupStatement? id = some node)
    (form : node.form = .assignValue assignment operator rhs) (bare : assignment.target.projections = []) :
    (operator = .equal ∨ assignment.target.type = .word) ∧ assignment.target.projections = [] ∧ Shape source mode rest :=
  ⟨(shape.assignment_tail found form).1, bare, (shape.assignment_tail found form).2⟩

theorem Shape.unary_tail {source mode id node assignment rest}
    (shape : Shape source mode (id :: rest)) (found : source.lookupStatement? id = some node)
    (form : node.form = .assignBitNot assignment) :
    assignment.target.type = .word ∧ Shape source mode rest := by
  cases shape with
  | forLoop actual same _ _ _ _ =>
      cases node_eq found actual
      rw [form] at same
      cases same
  | returnUnit _ actual same | returnValue _ actual same | breaking _ actual same | continuing _ actual same | tail actual same
  | discard actual same _ _ | absent actual same _ | initialized actual same _ | assign actual same _ _ _ | assignProjected actual same _ _ _
  | conditional actual same _ _ _ | whileLoop actual same _ _ | block actual same _ _ | matchWith actual same _ _ _ =>
      cases node_eq found actual
      rw [form] at same
      cases same
  | bitNot actual same profile _ remaining | bitNotProjected actual same profile _ remaining =>
      cases node_eq found actual
      rw [form] at same
      cases same
      exact ⟨profile, remaining⟩

theorem Shape.bitNot_tail {source mode id node assignment rest}
    (shape : Shape source mode (id :: rest)) (found : source.lookupStatement? id = some node)
    (form : node.form = .assignBitNot assignment) (bare : assignment.target.projections = []) :
    assignment.target.type = .word ∧ assignment.target.projections = [] ∧ Shape source mode rest :=
  ⟨(shape.unary_tail found form).1, bare, (shape.unary_tail found form).2⟩

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
  | discard actual same _ _ | absent actual same _ | initialized actual same _ | assign actual same _ _ _ | assignProjected actual same _ _ _ | bitNot actual same _ _ _ | bitNotProjected actual same _ _ _
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
  | discard actual same _ _ | absent actual same _ | initialized actual same _ | assign actual same _ _ _ | assignProjected actual same _ _ _ | bitNot actual same _ _ _ | bitNotProjected actual same _ _ _
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
  | discard actual same _ _ | absent actual same _ | initialized actual same _ | assign actual same _ _ _ | assignProjected actual same _ _ _ | bitNot actual same _ _ _ | bitNotProjected actual same _ _ _
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
  | discard actual same _ _ | absent actual same _ | initialized actual same _ | assign actual same _ _ _ | assignProjected actual same _ _ _ | bitNot actual same _ _ _ | bitNotProjected actual same _ _ _
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
  | discard actual same _ _ | absent actual same _ | initialized actual same _ | assign actual same _ _ _ | assignProjected actual same _ _ _ | bitNot actual same _ _ _ | bitNotProjected actual same _ _ _
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

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBranchingTree
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBodyRestorationAdmission
/-! The same saved physical caller restoration transports a staged body
post. Successful typing uses an authentic context-support receipt. Both
fault tags retain their exact outcome and the returned pool's stable rows. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBodyRestorationAdmission
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedBodyRestorationAdmission (bridge)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {caller body : ProtectedStateTransition.Index}

/-- No stage failure is converted into a semantic failure. The body and
caller contexts stay distinct until their genuine support receipt is used. -/
theorem restore_post (saved : State headers keys caller) (reached : State headers keys body)
    (selected : Fin keys.length) {bodyContext callerContext : SourceSemantics.Context}
    {type : TypeSystem.Ty} {outcome : Staging.Recursive.Outcome}
    (savedRows : StableRows saved)
    (post : CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
      bridge bodyContext type outcome reached)
    (supports : Dynamic.TypeContextSupports bodyContext callerContext)
    (restoredFrame : AdministrativePreserved caller.mapping caller.store body.mapping
      (CallableIndexedOwnedBodyRestoration.finalIndex (body := body) saved selected).store) :
    CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge callerContext type outcome
      (CallableIndexedOwnedBodyRestoration.returned saved reached selected) := by
  cases outcome with
  | value value =>
    exact CallableIndexedOwnedBodyRestorationAdmission.restore_post
      saved reached selected savedRows post supports restoredFrame
  | fault failure =>
    cases failure with
    | semantic reason =>
      exact CallableIndexedOwnedBodyRestorationAdmission.restore_fault_post
        saved reached selected savedRows restoredFrame
    | stage origin call reason =>
      exact CallableIndexedOwnedBodyRestorationAdmission.restore_rows
        saved reached selected savedRows restoredFrame

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBodyRestorationAdmission
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedLegacyBranchingTree
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBareAssignmentSourceInversion
/-! Original bare assignment traces retain the pre-RHS cell snapshot and the
actual post-RHS write. A live target excludes target lookup failures without
assuming anything about the RHS outcome. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBareAssignmentSourceInversion
open Frontend SourceInference Staging.Recursive

private theorem target_functional {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {place : PlaceResolution} {left right : Dynamic.ResolvedPlace}
    (first : BareTarget environment heap place left)
    (second : BareTarget environment heap place right) : left = right := by
  cases first with
  | intro _ leftLookup leftRead leftValue =>
    cases second with
    | intro _ rightLookup rightRead rightValue =>
      have locationEq := leftLookup.functional rightLookup
      cases locationEq
      have cellEq := leftRead.functional rightRead
      cases cellEq
      have valueEq := leftValue.functional rightValue
      cases valueEq
      rfl

/-- The actual Source rule retains RHS failure, operand rejection after a
successful RHS, or the genuine write and suffix. The target snapshot is fixed. -/
theorem child_and_tail {program : Program} {registry : Registry} {invocation : Scope}
    {context finalContext : SourceSemantics.Context} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : StatementId} {rest : List StatementId}
    {node : StatementNode} {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    {target : Dynamic.ResolvedPlace} {size : Nat} {outcome : BodyOutcome}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .assignValue assignment operator rhs)
    (snapshot : BareTarget environment before assignment.target target)
    (trace : Size.Statements program registry size invocation context environment before
      (id :: rest) finalContext outcome after) :
    (∃ childSize failure,
      size = Size.stepSize [childSize] ∧ finalContext = context ∧ outcome = .fault failure ∧
      Size.Expression program registry childSize invocation context environment before rhs (.fault failure) after) ∨
    (∃ childSize right currentCell initial currentSelected,
      size = Size.stepSize [childSize] ∧ finalContext = context ∧
      outcome = .fault (.semantic (.invalidAssignmentOperands operator)) ∧
      Size.Expression program registry childSize invocation context environment before rhs (.value right) after ∧
      Dynamic.Heap.Reads after target.location currentCell ∧ currentCell.type = target.rootType ∧
      Dynamic.RootInitialValue currentCell initial ∧ Dynamic.ProjectionsRead initial target.projections currentSelected ∧
      Dynamic.AssignmentOperandsInvalid operator target.selected right) ∨
    (∃ childSize tailSize value middle written updated,
      size = Size.stepSize [childSize, tailSize] ∧
      Size.Expression program registry childSize invocation context environment before rhs (.value value) middle ∧
      Dynamic.ResolvedPlaceWrites
        (fun _ replacement => Dynamic.AssignmentValueApplies operator target.selected value replacement)
        middle target updated written ∧
      Size.Statements program registry tailSize invocation context environment written rest finalContext outcome after) := by
  have shape {other : StatementNode} (present : ContainsStatement invocation.source id other) :
      other.form = .assignValue assignment operator rhs := by
    have same := Option.some.inj ((lookupStatement?_complete unique present).symm.trans found)
    cases same
    exact form
  cases trace with
  | breaking actual same | continuing actual same
  | blockBreaking actual same _ | blockContinuing actual same _
  | ifBreaking actual same _ _ | ifContinuing actual same _ _
  | matchBreaking actual same _ | matchContinuing actual same _
  | returnUnit actual same | returnValue actual same _ | returnFault actual same _
  | tail actual same _ | discard actual same _ _ | expressionFault actual same _
  | forInitializerFault actual same _ | forReturned actual same _ _ | forFault actual same _ _
  | forFallthrough actual same _ _ _
  | matchReturned actual same _ | matchFault actual same _ | matchFallthrough actual same _ _
  | blockReturned actual same _ | blockFault actual same _ | blockFallthrough actual same _ _
  | whileReturned actual same _ | whileFault actual same _ | whileFallthrough actual same _ _
  | ifConditionFault actual same _ | ifReturned actual same _ _ | ifFault actual same _ _
  | ifFallthrough actual same _ _ _
  | letGeneralized actual same _ _ _ _ _
  | letUninitialized actual same _ _ _ _ | letInitialized actual same _ _ _ _ _
  | bitNotProjected actual same _ _ _ _ _
  | bitNotProjectedRootFault actual same _ _
  | bitNotProjectedKeysFault actual same _ _ _
  | bitNotProjectedGetterFault actual same _ _ _
  | bitNotBare actual same _ _ _ | bitNotBareFault actual same _ _
  | letFault actual same _ _ =>
      have impossible := (shape actual).symm.trans same
      cases impossible
  | assignProjected actual same projected _ _ _ _ _
  | assignProjectedRootFault actual same projected _
  | assignProjectedKeysFault actual same projected _ _
  | assignProjectedGetterFault actual same projected _ _
  | assignProjectedRhsFault actual same projected _ _ _
  | assignProjectedWriteFault actual same projected _ _ _ _ =>
      cases (shape actual).symm.trans same
      have empty : assignment.target.projections = [] := by cases snapshot; assumption
      exact (projected empty).elim
  | assignBare actual same actualSnapshot child write remaining =>
      have equal := (shape actual).symm.trans same
      cases equal
      have targetEq := target_functional snapshot actualSnapshot
      cases targetEq
      exact .inr (.inr ⟨_, _, _, _, _, _, rfl, child, write, remaining⟩)
  | assignBareOperands actual same actualSnapshot child currentRead rootType initialValue pathRead invalid =>
      have equal := (shape actual).symm.trans same
      cases equal
      have targetEq := target_functional snapshot actualSnapshot
      cases targetEq
      exact .inr (.inl ⟨_, _, _, _, _, rfl, rfl, rfl, child,
        currentRead, rootType, initialValue, pathRead, invalid⟩)
  | assignBareFault actual same _ child =>
      have equal := (shape actual).symm.trans same
      cases equal
      exact .inl ⟨_, _, rfl, rfl, rfl, child⟩
  | assignBareUnbound actual same _ missing =>
      have equal := (shape actual).symm.trans same
      cases equal
      cases snapshot with
      | intro _ lookup _ _ => exact False.elim (missing.excludes_lookup lookup)
  | assignBareDangling actual same _ lookup missing =>
      have equal := (shape actual).symm.trans same
      cases equal
      cases snapshot with
      | intro _ actualLookup read _ =>
          have locationEq := lookup.functional actualLookup
          cases locationEq
          exact False.elim (missing.excludes_read read)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBareAssignmentSourceInversion
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBodyExitReceipts
/-! Exact lexical exits for staged bodies that keep their initial context.
Discard-sequence body bounds already return map/world and Source metadata
extensions. Those concrete receipts construct the unchanged lexical witness;
the original staged trace supplies ordinary control independently. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBodyExitReceipts
open Core Frontend SourceInference GeneralHeap

variable {checked : SourceCoreCompatibleCatalog.Checked} {definitions : DataEnvironment}
  {mapping finalMap : LocationMap} {world finalWorld : StoreTyping} {administrative : Core.Context}
  {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {environment : Dynamic.Environment} {canonical : Environment} {before after : Dynamic.Heap}

/-- The actual body extensions validate the unchanged original lexical scope. -/
theorem lexical_unchanged
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog)
      mapping world administrative scope environment canonical definitions)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
    (metadata : Dynamic.HeapMetadataExtend before after) (owner : Resolved.DeclarationId) :
    TypedStatementMixed.LexicalResult checked definitions finalMap finalWorld administrative owner
      context scope environment context after :=
  ⟨scope, environment, canonical, .here, environments.extend maps worlds, locals.mono metadata⟩

variable {program : Program} {stages : Staging.Recursive.Registry}
  {invocation : Staging.Recursive.Scope} {function : Dynamic.Closure}

/-- Successful staged control and genuine selected provenance construct the
full lexical exit expected by the existing parameter and invocation consumers. -/
theorem reached_returned
    (selected : stages.Closure function invocation)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog)
      mapping world administrative scope environment canonical definitions)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
    (metadata : Dynamic.HeapMetadataExtend before after)
    {resultContext : SourceSemantics.Context} {value : Dynamic.Value}
    (sameContext : resultContext = context)
    (trace : Staging.Recursive.Statements program stages invocation context environment before
      function.body resultContext (.returned value) after) :
    TypedMixedNamedBody.ReachedExit checked definitions finalMap finalWorld administrative
      program function context scope environment before after (.value value) := by
  subst resultContext
  refine ⟨context, .returned value, .control ?_, .returned value,
    lexical_unchanged environments locals maps worlds metadata function.source.owner⟩
  simpa only [stages.source selected, stages.evidence selected] using trace.returned_plain

/-- Ordinary semantic failure retains the same lexical receipt and prefix heap.
Stage rejection is excluded by the literal semantic outcome constructor. -/
theorem reached_semanticFault
    (selected : stages.Closure function invocation)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog)
      mapping world administrative scope environment canonical definitions)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
    (metadata : Dynamic.HeapMetadataExtend before after)
    {resultContext : SourceSemantics.Context} {reason : Dynamic.SemanticFault}
    (sameContext : resultContext = context)
    (trace : Staging.Recursive.Statements program stages invocation context environment before
      function.body resultContext (.fault (.semantic reason)) after) :
    TypedMixedNamedBody.ReachedExit checked definitions finalMap finalWorld administrative
      program function context scope environment before after (.fault reason) := by
  subst resultContext
  refine ⟨context, .fault reason, .fault ?_, .fault reason,
    lexical_unchanged environments locals maps worlds metadata function.source.owner⟩
  simpa only [stages.source selected, stages.evidence selected] using trace.semanticFault_plain

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBodyExitReceipts
end
