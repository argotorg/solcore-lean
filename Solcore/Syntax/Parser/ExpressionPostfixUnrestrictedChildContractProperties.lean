import Solcore.Syntax.Parser.ExpressionAtomUnrestrictedChildContractProperties
import Solcore.Syntax.Parser.ExpressionPostfixUnrestrictedFuelTotalityProperties
import Solcore.Syntax.Parser.PostfixNumericWindowProperties

/-! Actual atom-plus-postfix execution and its minimal contract are built from
nested-expression/body contracts. The intermediate atom contract is constructed,
not assumed. Rejected endIndex preservation is explicit because atom recovery
can turn a rejected carrier into success. No recursive closure is asserted. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

variable {nested : Parser Expr} {block : Parser Block}

/-- The minimum budget satisfies both child bounds and suffices to construct
the real atom contract internally. All remaining caller assumptions are on the
two supplied children; no atom contract or source/token frame is left abstract. -/
theorem expressionPostfix_ordinary_of_unrestrictedChildFuels
    (nested : Parser Expr) (block : Parser Block) (nestedFuel bodyFuel : Nat)
    (nestedContract : UnrestrictedFuelElementContract nested nestedFuel)
    (bodyContract : UnrestrictedFuelElementContract block bodyFuel)
    (nestedReject : ∀ {input rejected failure}, nested input = .reject failure rejected →
      rejected.window.endIndex = input.window.endIndex)
    (bodyReject : ∀ {input rejected failure}, block input = .reject failure rejected →
      rejected.window.endIndex = input.window.endIndex)
    (input : State) (nestedAdequate : input.remainingCount < nestedFuel + 1)
    (bodyAdequate : input.remainingCount < bodyFuel + 1) :
    (∃ value output, expressionPostfix nested block input = .ok value output) ∨
    (∃ failure rejected, expressionPostfix nested block input = .reject failure rejected) := by
  have atomContract := expressionAtom_unrestrictedChildContract nested block nestedFuel bodyFuel
    (min (nestedFuel + 1) (bodyFuel + 1)) nestedContract bodyContract nestedReject bodyReject
    (Nat.min_le_left _ _) (Nat.min_le_right _ _)
  exact expressionPostfix_ordinary_of_unrestrictedElementFuels nested block
    (min (nestedFuel + 1) (bodyFuel + 1)) nestedFuel atomContract nestedContract input
    (by omega) nestedAdequate

theorem expressionPostfix_ne_invariant_of_unrestrictedChildFuels
    (nested : Parser Expr) (block : Parser Block) (nestedFuel bodyFuel : Nat)
    (nestedContract : UnrestrictedFuelElementContract nested nestedFuel)
    (bodyContract : UnrestrictedFuelElementContract block bodyFuel)
    (nestedReject : ∀ {input rejected failure}, nested input = .reject failure rejected →
      rejected.window.endIndex = input.window.endIndex)
    (bodyReject : ∀ {input rejected failure}, block input = .reject failure rejected →
      rejected.window.endIndex = input.window.endIndex)
    (input : State) (nestedAdequate : input.remainingCount < nestedFuel + 1)
    (bodyAdequate : input.remainingCount < bodyFuel + 1) (error : ParserInvariantError) :
    expressionPostfix nested block input ≠ .invariant error := by
  intro failed
  rcases expressionPostfix_ordinary_of_unrestrictedChildFuels nested block nestedFuel bodyFuel
      nestedContract bodyContract nestedReject bodyReject input nestedAdequate bodyAdequate with
    ⟨value, output, result⟩ | ⟨failure, rejected, result⟩ <;> rw [result] at failed <;> contradiction

/-- Successful postfix replies preserve endIndex and advance strictly on all
States. Fuel bounds restrict only the ordinary field of the resulting contract. -/
theorem expressionPostfix_unrestrictedChildContract
    (nested : Parser Expr) (block : Parser Block) (nestedFuel bodyFuel postfixFuel : Nat)
    (nestedContract : UnrestrictedFuelElementContract nested nestedFuel)
    (bodyContract : UnrestrictedFuelElementContract block bodyFuel)
    (nestedReject : ∀ {input rejected failure}, nested input = .reject failure rejected →
      rejected.window.endIndex = input.window.endIndex)
    (bodyReject : ∀ {input rejected failure}, block input = .reject failure rejected →
      rejected.window.endIndex = input.window.endIndex)
    (nestedBound : postfixFuel ≤ nestedFuel + 1) (bodyBound : postfixFuel ≤ bodyFuel + 1) :
    UnrestrictedFuelElementContract (expressionPostfix nested block) postfixFuel := by
  have nestedFrame : Parser.PreservesEndIndex nested :=
    .of_success_reject nestedContract.endIndexOnSuccess nestedReject
  have bodyFrame : Parser.PreservesEndIndex block :=
    .of_success_reject bodyContract.endIndexOnSuccess bodyReject
  exact {
    endIndexOnSuccess := (expressionPostfix_preservesEndIndex nested block
      (expressionAtom_preservesEndIndex nested block nestedFrame bodyFrame) nestedFrame).endIndex_eq_of_ok
    cursorLtOnSuccess := ExpressionAtomInternals.expressionPostfix_cursor_lt_onSuccess nested block
      (fun _ _ _ result => Nat.le_of_lt (nestedContract.cursorLtOnSuccess result))
      (fun _ _ _ result => Nat.le_of_lt (bodyContract.cursorLtOnSuccess result))
    ordinary input adequate := expressionPostfix_ordinary_of_unrestrictedChildFuels nested block nestedFuel bodyFuel
      nestedContract bodyContract nestedReject bodyReject input
      (Nat.lt_of_lt_of_le adequate nestedBound) (Nat.lt_of_lt_of_le adequate bodyBound)
  }

/-- Equal child budgets close one actual postfix layer at the successor
budget, without promoting either supplied child to a recursive implementation. -/
theorem expressionPostfix_unrestrictedChildContract_succ
    (nested : Parser Expr) (block : Parser Block) (fuel : Nat)
    (nestedContract : UnrestrictedFuelElementContract nested fuel)
    (bodyContract : UnrestrictedFuelElementContract block fuel)
    (nestedReject : ∀ {input rejected failure}, nested input = .reject failure rejected →
      rejected.window.endIndex = input.window.endIndex)
    (bodyReject : ∀ {input rejected failure}, block input = .reject failure rejected →
      rejected.window.endIndex = input.window.endIndex) :
    UnrestrictedFuelElementContract (expressionPostfix nested block) (fuel + 1) :=
  expressionPostfix_unrestrictedChildContract nested block fuel fuel (fuel + 1)
    nestedContract bodyContract nestedReject bodyReject (Nat.le_refl _) (Nat.le_refl _)

end Solcore.Syntax.Parser
