import Solcore.Frontend.RustHull.Effects

/-! The pinned Sonatina backend lowers `datacopy` and `codecopy` to the same
instruction. Their Core lowering also agrees, including missing-image errors. -/
set_option autoImplicit false

namespace Solcore.Frontend.RustHull.Effects

theorem lowerBuiltin_datacopy_eq_codecopy (scope : Scope)
    (destination source length : Core.Expr) :
    lowerBuiltin scope "datacopy" [destination, source, length] =
      lowerBuiltin scope "codecopy" [destination, source, length] := rfl

end Solcore.Frontend.RustHull.Effects
