import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBareAssignmentTree
import Solcore.SourceSemantics.CoreLowering.GenericImperativeMatchTree

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

private theorem node_eq {source : TypedSource} {id : StatementId} {first second : StatementNode}
    (left : source.lookupStatement? id = some first)
    (right : source.lookupStatement? id = some second) : first = second :=
  Option.some.inj (left.symm.trans right)

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
