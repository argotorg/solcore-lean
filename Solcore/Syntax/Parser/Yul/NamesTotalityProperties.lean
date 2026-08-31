import Solcore.Syntax.Parser.Yul.Common
import Solcore.Syntax.Parser.Yul.LeafTotalityProperties
import Solcore.Syntax.Parser.InvariantFreeProperties
import Solcore.Syntax.Parser.DelimitedFuelTotalityProperties

/-! Totality for nonempty inline-Yul name sequences. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem finishYulNames_ordinary (first last : YulIdentifier)
    (tailRev : List YulIdentifier) :
    Parser.Ordinary (finishYulNames first last tailRev) := by
  intro input
  exact Or.inl ⟨_, input, rfl⟩

theorem yulNamesTail_ordinary_of_remainingCount_lt
    (first : YulIdentifier) :
    ∀ fuel last tailRev input,
      input.ValidFor → input.remainingCount < fuel →
      (∃ names next,
        yulNamesTail first fuel last tailRev input = .ok names next) ∨
      (∃ failure next,
        yulNamesTail first fuel last tailRev input = .reject failure next) := by
  intro fuel
  induction fuel with
  | zero =>
      intro last tailRev input inputValid adequate
      omega
  | succ fuel inductionHypothesis =>
      intro last tailRev input inputValid adequate
      unfold yulNamesTail
      split
      · cases commaResult : symbol .comma .yulStatement input with
        | invariant error =>
            exact False.elim
              (symbol_ne_invariant .comma .yulStatement input error
                commaResult)
        | reject failure rejected =>
            exact Or.inr ⟨failure, rejected, rfl⟩
        | ok comma afterComma =>
            have commaReply := symbol_validFor .comma .yulStatement
              input inputValid
            rw [commaResult] at commaReply
            have commaWindow := symbol_preservesTokenWindow .comma
              .yulStatement input
            rw [commaResult] at commaWindow
            have commaProgress := acceptToken_cursor_lt_onSuccess
              (.symbol .comma) .yulStatement (· == .symbol .comma)
                commaResult
            have afterCommaAdequate : afterComma.remainingCount < fuel :=
              remainingCount_lt_after_strict_progress commaReply.2.1
                commaWindow.2 commaProgress adequate
            cases nameResult : yulName afterComma with
            | invariant error =>
                exact False.elim
                  (yulName_ordinary.ne_invariant afterComma error nameResult)
            | reject failure rejected =>
                exact Or.inr ⟨failure, rejected, by
                  simp only [nameResult]⟩
            | ok name next =>
                have nameReply := yulName_validFor afterComma commaReply.2.1
                rw [nameResult] at nameReply
                have nameWindow := yulName_preservesTokenWindow afterComma
                rw [nameResult] at nameWindow
                have nextAdequate : next.remainingCount < fuel :=
                  remainingCount_lt_of_cursor_le nameWindow.2
                    (Nat.le_of_lt (yulName_cursor_lt_onSuccess nameResult))
                      afterCommaAdequate
                rcases inductionHypothesis name (name :: tailRev) next
                    nameReply.2.1 nextAdequate with
                  ⟨names, final, recursiveResult⟩ |
                  ⟨failure, rejected, recursiveResult⟩
                · exact Or.inl ⟨names, final, by
                    simp only [nameResult]
                    exact recursiveResult⟩
                · exact Or.inr ⟨failure, rejected, by
                    simp only [nameResult]
                    exact recursiveResult⟩
      · exact finishYulNames_ordinary first last tailRev input

theorem yulNames_invariantFreeOnValid :
    Parser.InvariantFreeOnValid yulNames := by
  intro input inputValid
  rcases yulName_ordinary input with
    ⟨first, next, firstResult⟩ | ⟨failure, rejected, firstResult⟩
  · have firstReply := yulName_validFor input inputValid
    rw [firstResult] at firstReply
    rcases yulNamesTail_ordinary_of_remainingCount_lt first
        (next.remainingCount + 1) first [] next firstReply.2.1 (by omega) with
      ⟨names, final, tailResult⟩ | ⟨failure, rejected, tailResult⟩
    · exact Or.inl ⟨names, final, by
        simp only [yulNames, firstResult]
        exact tailResult⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [yulNames, firstResult]
        exact tailResult⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [yulNames, firstResult]⟩

theorem yulNames_cursor_lt_onSuccess {input next : State}
    {names : YulNameSequence} (parsed : yulNames input = .ok names next) :
    input.cursor < next.cursor :=
  (yulNames_ok_state_shape parsed).choose_spec.2.2.2

theorem yulNames_elementTotalityContract :
    ElementTotalityContract yulNames := {
  validFor := yulNames_validFor.mono (fun _ _ _ => trivial)
  preservesTokenWindow := yulNames_preservesTokenWindow
  cursorLtOnSuccess := yulNames_cursor_lt_onSuccess
  invariantFree := yulNames_invariantFreeOnValid.ne_invariant
}

end Solcore.Syntax.Parser
