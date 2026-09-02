import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties
import Solcore.Syntax.Parser.ImportTerminatorOrdinarySuccessSoundnessProperties

/-! Exact ordinary-rejection reflection for import terminators. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every executable import-terminator rejection is the exact nonconsuming
endpoint where both the semicolon and top-item-start guards are absent. -/
theorem importTerminator_reject_ordinaryOutcome_sound (lastSpan : SourceSpan)
    {input rejected : State} {failure : Failure}
    (result : ImportInternals.terminator lastSpan input =
      .reject failure rejected) :
    DeclarativeGrammar.ImportTerminatorRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold ImportInternals.terminator at result
  by_cases semicolonPresent : isSymbol input .semicolon = true
  · rcases symbol_eq_ok_of_isSymbol_eq_true .semicolon .importDecl
        semicolonPresent with ⟨token, semicolonResult⟩
    simp [semicolonPresent, semicolonResult] at result
  · have semicolonAbsent : isSymbol input .semicolon = false :=
      Bool.eq_false_iff.mpr semicolonPresent
    simp only [semicolonAbsent, Bool.false_eq_true, if_false] at result
    by_cases topItemPresent : atTopItemStart input = true
    · simp [topItemPresent] at result
    · have topItemAbsent : atTopItemStart input = false :=
        Bool.eq_false_iff.mpr topItemPresent
      simp only [topItemAbsent, Bool.false_eq_true, if_false] at result
      unfold rejectAt at result
      cases result
      exact .missing
        (symbolAbsentAt_of_isSymbol_eq_false .semicolon semicolonAbsent)
        (importTerminatorTopItemStartAbsentAt_of_atTopItemStart_eq_false
          topItemAbsent)

end Solcore.Syntax.Parser
