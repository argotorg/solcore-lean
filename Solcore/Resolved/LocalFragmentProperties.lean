import Solcore.Core.LocalRightWordLessTypingProperties
import Solcore.Resolved.Expr

/-! Existing resolved lowering produces only the independent local Core
fragment. This structural bridge does not use either language's evaluation
correspondence and introduces no dependency from Core back to Resolved. -/

set_option autoImplicit false

namespace Solcore.Resolved

theorem Lowers.localFragment {scope : List LocalId} {expr : Expr} {core : Core.Expr}
    (lowered : Lowers scope expr core) : Core.Expr.LocalFragment core := by
  induction lowered with
  | unit => exact .unit
  | bool => exact .bool
  | word => exact .word
  | var => exact .var
  | unary _ ih => exact .unary ih
  | binary _ _ leftIH rightIH => exact .binary leftIH rightIH
  | wordLt _ _ leftIH rightIH => exact leftIH.wordLt rightIH
  | letE _ _ valueIH bodyIH => exact .letE valueIH bodyIH
  | ifE _ _ _ conditionIH thenIH elseIH => exact .ifE conditionIH thenIH elseIH

end Solcore.Resolved
