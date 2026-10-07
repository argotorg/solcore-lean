import Solcore.SourceSemantics.Static
import Solcore.SourceSemantics.WellFormed

/-! The argument and value slots used by the composite, tuple, and builtin
adapters are exposed. Their full original
Source typing row comes from the parent's genuine typing judgment, independently
of native types or compiler projections. No execution or support fold is added. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedStateExpressionOperandTyping
open Frontend SourceInference

/-- Ordered argument and value slots. Every call callee is excluded and handled
separately by its selected-call receipt; order and duplicates are retained. -/
def actualOperandIds : ExpressionForm → List ExpressionId
  | .group inner => [inner]
  | .tuple elements => elements
  | .unary _ operand => [operand]
  | .binary left _ right => [left, right]
  | .conditional condition thenBranch elseBranch => [condition, thenBranch, elseBranch]
  | .call _ arguments _ => arguments
  | .constructor _ arguments => arguments
  | .member base _ _ => [base]
  | .index base key => [base, key]
  | .literal _ | .integerLiteral _ _ | .reference _ _ | .lambda _ _ _ | .proxy _ => []

/-- One original typing inversion supplies every actual operand's Source row.
The row is retained in its original types, rather than identified with a native
parameter or projected type vector. -/
theorem operand_types {source : TypedSource} {context : Context}
    {id : ExpressionId} {node : ExpressionNode} {type : TypeSystem.Ty}
    (unique : NodeOccurrencesUnique source)
    (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source context id type) :
    ∃ types, ExpressionsHaveTypes source context (actualOperandIds node.form) types := by
  cases typed with
  | @intro _ _ actualNode rawType plan contains raw _ _ _ _ =>
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
    subst actualNode
    generalize formEq : node.form = form at raw ⊢
    cases raw with
    | literal _ | integerLiteral _ | reference _ | proxy _ | lambda _ _ _ _ =>
      exact ⟨[], .nil context⟩
    | group child => exact ⟨_, .cons child (.nil context)⟩
    | tuple children => exact ⟨_, children⟩
    | unary child _ => exact ⟨_, .cons child (.nil context)⟩
    | binary first second _ => exact ⟨_, .cons first (.cons second (.nil context))⟩
    | conditional condition thenBranch elseBranch =>
      exact ⟨_, .cons condition (.cons thenBranch (.cons elseBranch (.nil context)))⟩
    | directCall _ _ children | builtinCall _ children | indirectCall _ children _ =>
      exact ⟨_, children⟩
    | constructor _ children => exact ⟨_, children⟩
    | member child _ => exact ⟨_, .cons child (.nil context)⟩
    | index base key => exact ⟨_, .cons base (.cons key (.nil context))⟩

end Solcore.SourceSemantics.CoreLowering.ProtectedStateExpressionOperandTyping
