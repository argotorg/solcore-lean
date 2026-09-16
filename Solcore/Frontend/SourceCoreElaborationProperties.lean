import Solcore.Frontend.SourceCoreElaboration

/-! Checked laws for the typed-source-to-Core elaboration boundary. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreElaboration

open SourceInference TypeSystem

@[simp] theorem lowerType_unit (site : ErrorSite) :
    lowerType site .unit = .ok .unit := by
  rfl

@[simp] theorem lowerType_bool (site : ErrorSite) :
    lowerType site .bool = .ok .bool := by
  rfl

@[simp] theorem lowerType_word (site : ErrorSite) :
    lowerType site .word = .ok .word := by
  rfl

theorem lowerType_product {site : ErrorSite} {left right : Ty}
    {loweredLeft loweredRight : Core.Ty}
    (leftAccepted : lowerType site left = .ok loweredLeft)
    (rightAccepted : lowerType site right = .ok loweredRight) :
    lowerType site (.product left right) =
      .ok (.product loweredLeft loweredRight) := by
  simp [lowerType, leftAccepted, rightAccepted, bind, Except.bind,
    pure, Pure.pure, Except.pure]

end Solcore.Frontend.SourceCoreElaboration
