import Solcore.Syntax.Parser.ExpressionAtomNumericWindowProperties
import Solcore.Syntax.Parser.ExpressionAtomBoundedBodyFuelTotalityProperties

/-! One actual recovering atom constructs a minimal fuel contract from its
two supplied children. Both rejected children must preserve endIndex because
their replacement carriers can become successful public recovery outcomes.
No source, token, byte-end, diagnostic, or validity frame is required. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

open ExpressionAtomInternals

/-- Success endIndex and progress hold on every State, independent of fuel.
Only the ordinary field uses the chosen atom budget and its two child bounds. -/
theorem expressionAtom_unrestrictedChildContract
    (nested : Parser Expr) (block : Parser Block) (nestedFuel bodyFuel atomFuel : Nat)
    (nestedContract : UnrestrictedFuelElementContract nested nestedFuel)
    (bodyContract : UnrestrictedFuelElementContract block bodyFuel)
    (nestedReject : ∀ {input rejected failure}, nested input = .reject failure rejected →
      rejected.window.endIndex = input.window.endIndex)
    (bodyReject : ∀ {input rejected failure}, block input = .reject failure rejected →
      rejected.window.endIndex = input.window.endIndex)
    (nestedBound : atomFuel ≤ nestedFuel + 1) (bodyBound : atomFuel ≤ bodyFuel + 1) :
    UnrestrictedFuelElementContract (expressionAtom nested block) atomFuel where
  endIndexOnSuccess := expressionAtom_endIndex_onSuccess nestedContract.endIndexOnSuccess nestedReject
    bodyContract.endIndexOnSuccess bodyReject
  cursorLtOnSuccess := expressionAtom_cursor_lt_onSuccess nested block
    (fun _ _ _ result => Nat.le_of_lt (nestedContract.cursorLtOnSuccess result))
    (fun _ _ _ result => Nat.le_of_lt (bodyContract.cursorLtOnSuccess result))
  ordinary input adequate := expressionAtom_ordinary_of_unrestrictedChildFuels nested block nestedFuel bodyFuel
    nestedContract bodyContract input (Nat.lt_of_lt_of_le adequate nestedBound) (Nat.lt_of_lt_of_le adequate bodyBound)

/-- Equal child budgets construct the next atom layer; this is a conditional
one-layer step, not a recursively closed expression or block contract. -/
theorem expressionAtom_unrestrictedChildContract_succ
    (nested : Parser Expr) (block : Parser Block) (fuel : Nat)
    (nestedContract : UnrestrictedFuelElementContract nested fuel)
    (bodyContract : UnrestrictedFuelElementContract block fuel)
    (nestedReject : ∀ {input rejected failure}, nested input = .reject failure rejected →
      rejected.window.endIndex = input.window.endIndex)
    (bodyReject : ∀ {input rejected failure}, block input = .reject failure rejected →
      rejected.window.endIndex = input.window.endIndex) :
    UnrestrictedFuelElementContract (expressionAtom nested block) (fuel + 1) :=
  expressionAtom_unrestrictedChildContract nested block fuel fuel (fuel + 1)
    nestedContract bodyContract nestedReject bodyReject (Nat.le_refl _) (Nat.le_refl _)

end Solcore.Syntax.Parser
