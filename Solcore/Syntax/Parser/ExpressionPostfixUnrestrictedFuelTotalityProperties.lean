import Solcore.Syntax.Parser.PostfixTailUnrestrictedFuelTotalityProperties

/-! Bounded ordinary execution for the actual atom-plus-postfix composition.
The pointwise form only constrains successful atom remaining counts; a stronger
corollary consumes a separately supplied atom contract. This file does not
construct that contract or establish recursive expression/block totality. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

open ExpressionAtomInternals

/-- No atom source, token, diagnostic, or rejected-state frame is needed.
Only its ordinary outcome here and the bound at each successful endpoint matter. -/
theorem expressionPostfix_ordinary_of_atomOutcome_bound
    (nested : Parser Expr) (block : Parser Block) (nestedFuel : Nat)
    (nestedContract : UnrestrictedFuelElementContract nested nestedFuel) (input : State)
    (atomOrdinary :
      (∃ base next, expressionAtom nested block input = .ok base next) ∨
      (∃ failure rejected, expressionAtom nested block input = .reject failure rejected))
    (afterAtomBound : ∀ {base next}, expressionAtom nested block input = .ok base next →
      next.remainingCount < nestedFuel + 1) :
    (∃ value output, expressionPostfix nested block input = .ok value output) ∨
    (∃ failure rejected, expressionPostfix nested block input = .reject failure rejected) := by
  rcases atomOrdinary with ⟨base, next, atomResult⟩ | ⟨failure, rejected, atomResult⟩
  · rcases postfixTail_production_ordinary_of_unrestrictedElementFuel nested block nestedFuel
        nestedContract base next (afterAtomBound atomResult) with
      ⟨value, output, tailResult⟩ | ⟨failure, rejected, tailResult⟩
    · exact .inl ⟨value, output, by simp only [expressionPostfix, atomResult, tailResult]⟩
    · exact .inr ⟨failure, rejected, by simp only [expressionPostfix, atomResult, tailResult]⟩
  · exact .inr ⟨failure, rejected, by simp only [expressionPostfix, atomResult]⟩

theorem expressionPostfix_ne_invariant_of_atomOutcome_bound
    (nested : Parser Expr) (block : Parser Block) (nestedFuel : Nat)
    (nestedContract : UnrestrictedFuelElementContract nested nestedFuel) (input : State)
    (atomOrdinary :
      (∃ base next, expressionAtom nested block input = .ok base next) ∨
      (∃ failure rejected, expressionAtom nested block input = .reject failure rejected))
    (afterAtomBound : ∀ {base next}, expressionAtom nested block input = .ok base next →
      next.remainingCount < nestedFuel + 1) (error : ParserInvariantError) :
    expressionPostfix nested block input ≠ .invariant error := by
  intro failed
  rcases expressionPostfix_ordinary_of_atomOutcome_bound nested block nestedFuel nestedContract
      input atomOrdinary afterAtomBound with
    ⟨value, output, result⟩ | ⟨failure, rejected, result⟩ <;>
    rw [result] at failed <;> contradiction

/-- The actual atom contract is an explicit premise, not a consequence of the
nested contract. Its strict progress and unchanged endIndex transfer the second
input bound to the atom's successful endpoint on arbitrary numerical States. -/
theorem expressionPostfix_ordinary_of_unrestrictedElementFuels
    (nested : Parser Expr) (block : Parser Block) (atomFuel nestedFuel : Nat)
    (atomContract : UnrestrictedFuelElementContract (expressionAtom nested block) atomFuel)
    (nestedContract : UnrestrictedFuelElementContract nested nestedFuel) (input : State)
    (atomAdequate : input.remainingCount < atomFuel)
    (nestedAdequate : input.remainingCount < nestedFuel + 1) :
    (∃ value output, expressionPostfix nested block input = .ok value output) ∨
    (∃ failure rejected, expressionPostfix nested block input = .reject failure rejected) :=
  expressionPostfix_ordinary_of_atomOutcome_bound nested block nestedFuel nestedContract input
    (atomContract.ordinary input atomAdequate)
    (fun result => atomContract.remainingCount_lt_of_success result nestedAdequate)

theorem expressionPostfix_ne_invariant_of_unrestrictedElementFuels
    (nested : Parser Expr) (block : Parser Block) (atomFuel nestedFuel : Nat)
    (atomContract : UnrestrictedFuelElementContract (expressionAtom nested block) atomFuel)
    (nestedContract : UnrestrictedFuelElementContract nested nestedFuel) (input : State)
    (atomAdequate : input.remainingCount < atomFuel)
    (nestedAdequate : input.remainingCount < nestedFuel + 1) (error : ParserInvariantError) :
    expressionPostfix nested block input ≠ .invariant error :=
  expressionPostfix_ne_invariant_of_atomOutcome_bound nested block nestedFuel nestedContract input
    (atomContract.ordinary input atomAdequate)
    (fun result => atomContract.remainingCount_lt_of_success result nestedAdequate) error

end Solcore.Syntax.Parser
