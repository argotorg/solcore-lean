import Solcore.Core.DerivedComparisons
import Solcore.Core.LocalFragmentTypingInsertionProperties

/-! Static local-fragment facts for the existing ordered Word less-than
expansion. Only the right operand needs the fragment restriction for typing
reflection; the left operand may use arbitrary Core syntax. -/

set_option autoImplicit false

namespace Solcore.Core

theorem Expr.LocalFragment.wordLt {left right : Expr}
    (leftFragment : left.LocalFragment) (rightFragment : right.LocalFragment) :
    (left.wordLt right).LocalFragment := by
  rw [Expr.wordLt_expansion]
  exact .letE leftFragment (.letE (rightFragment.weakenAt 0) (.binary .var .var))

/-- Invert the retained Word bindings, then recover typing of the original
right operand. Data definitions and the original context are arbitrary. -/
theorem HasType.wordLt_inv_local_right
    {context : Context} {left right : Expr} {type : Ty} {definitions : DataEnvironment}
    (typing : HasType context (left.wordLt right) type definitions)
    (rightFragment : right.LocalFragment) :
    type = .bool ∧ HasType context left .word definitions ∧
      HasType context right .word definitions := by
  rw [Expr.wordLt_expansion] at typing
  cases typing with
  | @letE _ _ _ _ leftType _ leftTyping innerTyping =>
      cases innerTyping with
      | @letE _ _ _ _ rightType _ rightTyping comparison =>
          cases comparison with
          | binary rightReference leftReference =>
              cases rightReference with
              | var foundRight =>
                  cases leftReference with
                  | var foundLeft =>
                      have rightTypeEq : rightType = .word := by
                        simpa [BinaryOp.leftType] using foundRight
                      have leftTypeEq : leftType = .word := by
                        simpa [BinaryOp.rightType] using foundLeft
                      cases rightTypeEq
                      cases leftTypeEq
                      exact ⟨rfl, leftTyping,
                        rightTyping.reflect_weakenAt_zero_localFragment rightFragment⟩

end Solcore.Core
