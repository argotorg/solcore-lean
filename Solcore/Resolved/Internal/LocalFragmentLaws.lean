import Solcore.Core.Internal.LocalFragment
import Solcore.Resolved.Expr

/-!
# Lowering and the local fragment

Resolved lowering produces only the local Core fragment.

This stays apart from `Solcore.Resolved.Expr`: there, the import of the local fragment would put
`Internal/DerivedForms` and its `simp` lemmas under everything that imports `Resolved.Expr`.
-/

section
-- leanmerge: from Solcore.Resolved.LocalFragmentProperties
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
  | pair _ _ leftIH rightIH => exact .pair leftIH rightIH
  | unary _ ih => exact .unary ih
  | binary _ _ leftIH rightIH => exact .binary leftIH rightIH
  | wordLt _ _ leftIH rightIH => exact leftIH.wordLt rightIH
  | letE _ _ valueIH bodyIH => exact .letE valueIH bodyIH
  | ifE _ _ _ conditionIH thenIH elseIH => exact .ifE conditionIH thenIH elseIH

end Solcore.Resolved
end
