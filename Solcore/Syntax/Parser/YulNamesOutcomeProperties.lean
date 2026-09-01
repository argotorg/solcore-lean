import Solcore.Syntax.Parser.YulNameOutcomeProperties
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties
import Solcore.Syntax.Parser.Yul.Common

/-!
Executable ordinary-success and exact binary-rejection bridges for nonempty
inline-Yul name sequences.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Executable finishing preserves forward order and does not consume input. -/
theorem finishYulNames_success_ordinary_sound
    (first last : YulIdentifier) (tailRev : List YulIdentifier)
    {input next : State} {names : YulNameSequence}
    (result : finishYulNames first last tailRev input = .ok names next) :
    DeclarativeGrammar.FinishYulNamesOrdinaryParses first last tailRev
      input.declarativeRemainder {
        span := names.span
        names := names.names
      } next.declarativeRemainder := by
  unfold finishYulNames at result
  cases result
  exact .parsed

/-- Every executable ordinary tail success records the comma-prioritized,
forward-order sequence, independently of diagnostics. -/
theorem yulNamesTail_success_ordinary_sound (first : YulIdentifier) :
    ∀ fuel last tailRev, ∀ {input next : State} {names : YulNameSequence},
      yulNamesTail first fuel last tailRev input = .ok names next →
      DeclarativeGrammar.YulNamesTailOrdinaryParses first
        input.declarativeRemainder last tailRev {
          span := names.span
          names := names.names
        } next.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro last tailRev input next names result
      simp [yulNamesTail] at result
  | succ fuel inductionHypothesis =>
      intro last tailRev input next names result
      unfold yulNamesTail at result
      by_cases commaPresent : isSymbol input .comma = true
      · simp only [commaPresent, if_true] at result
        rcases symbol_eq_ok_of_isSymbol_eq_true .comma .yulStatement
            commaPresent with ⟨comma, commaResult⟩
        simp only [commaResult] at result
        cases nameResult : yulName
            { input with cursor := input.cursor + 1 } with
        | invariant error => simp [nameResult] at result
        | reject failure rejected => simp [nameResult] at result
        | ok name afterName =>
            simp only [nameResult] at result
            have nameParsed := yulName_success_ordinary_sound nameResult
            have tailParsed := inductionHypothesis name (name :: tailRev)
              result
            have nameInput :
                DeclarativeGrammar.YulNameOrdinaryParses {
                  input.declarativeRemainder with
                    cursor := input.cursor + 1
                } name afterName.declarativeRemainder := by
              simpa [State.declarativeRemainder] using nameParsed
            exact .next comma.span
              (symbol_ok_tokenAt .comma .yulStatement commaResult).1
              nameInput tailParsed
      · have commaFalse : isSymbol input .comma = false :=
          Bool.eq_false_iff.mpr commaPresent
        simp only [commaFalse, Bool.false_eq_true, if_false] at result
        exact .done
          (symbolAbsentAt_of_isSymbol_eq_false .comma commaFalse)
          (finishYulNames_success_ordinary_sound first last tailRev result)

/-- Every executable ordinary tail rejection records whether the name directly
after this comma rejected or a later comma/name pair rejected. -/
theorem yulNamesTail_reject_sound (first : YulIdentifier) :
    ∀ fuel last tailRev, ∀ {input rejected : State} {failure : Failure},
      yulNamesTail first fuel last tailRev input = .reject failure rejected →
      DeclarativeGrammar.YulNamesTailRejects first
        input.declarativeRemainder last tailRev
          rejected.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro last tailRev input rejected failure result
      simp [yulNamesTail] at result
  | succ fuel inductionHypothesis =>
      intro last tailRev input rejected failure result
      unfold yulNamesTail at result
      by_cases commaPresent : isSymbol input .comma = true
      · simp only [commaPresent, if_true] at result
        rcases symbol_eq_ok_of_isSymbol_eq_true .comma .yulStatement
            commaPresent with ⟨comma, commaResult⟩
        simp only [commaResult] at result
        cases nameResult : yulName
            { input with cursor := input.cursor + 1 } with
        | invariant error => simp [nameResult] at result
        | reject nameFailure nameRejected =>
            simp only [nameResult] at result
            cases result
            exact .commaNameRejected comma.span
              (symbol_ok_tokenAt .comma .yulStatement commaResult).1
              (by simpa [State.declarativeRemainder] using
                yulName_reject_sound nameResult)
        | ok name afterName =>
            simp only [nameResult] at result
            have nameParsed := yulName_success_ordinary_sound nameResult
            have nameInput :
                DeclarativeGrammar.YulNameOrdinaryParses {
                  input.declarativeRemainder with
                    cursor := input.cursor + 1
                } name afterName.declarativeRemainder := by
              simpa [State.declarativeRemainder] using nameParsed
            exact .laterRejected comma.span
              (symbol_ok_tokenAt .comma .yulStatement commaResult).1
              nameInput
              (inductionHypothesis name (name :: tailRev) result)
      · have commaFalse : isSymbol input .comma = false :=
          Bool.eq_false_iff.mpr commaPresent
        simp [commaFalse, finishYulNames] at result

/-- Every executable public sequence success follows the ordinary nonempty
sequence relation. -/
theorem yulNames_success_ordinary_sound {input next : State}
    {names : YulNameSequence} (result : yulNames input = .ok names next) :
    DeclarativeGrammar.YulNamesOrdinaryParses input.declarativeRemainder {
      span := names.span
      names := names.names
    } next.declarativeRemainder := by
  unfold yulNames at result
  cases firstResult : yulName input with
  | invariant error => simp [firstResult] at result
  | reject failure rejected => simp [firstResult] at result
  | ok first afterFirst =>
      simp only [firstResult] at result
      exact .parsed (yulName_success_ordinary_sound firstResult)
        (yulNamesTail_success_ordinary_sound first
          (afterFirst.remainingCount + 1) first [] result)

/-- Every executable public sequence rejection is either its first-name
rejection or an exact later tail rejection. -/
theorem yulNames_reject_sound {input rejected : State} {failure : Failure}
    (result : yulNames input = .reject failure rejected) :
    DeclarativeGrammar.YulNamesRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold yulNames at result
  cases firstResult : yulName input with
  | invariant error => simp [firstResult] at result
  | reject firstFailure firstRejected =>
      simp only [firstResult] at result
      cases result
      exact .firstRejected (yulName_reject_sound firstResult)
  | ok first afterFirst =>
      simp only [firstResult] at result
      exact .tailRejected (yulName_success_ordinary_sound firstResult)
        (yulNamesTail_reject_sound first (afterFirst.remainingCount + 1)
          first [] result)

end Solcore.Syntax.Parser
