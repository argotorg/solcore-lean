import Solcore.Syntax.Parser.DelimitedNoTrailingSoundnessProperties

/-! Success soundness for possibly empty lists that reject a trailing comma. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/--
Every successful list that allows empty contents but rejects a trailing comma
follows the independent prioritized grammar. Element parsers may diagnose.
-/
theorem delimitedNoTrailing_allowEmpty_success_sound {α : Type}
    (opening closing : Symbol) (element : Parser α)
    (elementParses : DeclarativeGrammar.Remainder → α →
      DeclarativeGrammar.Remainder → Prop)
    (context : ParseContext) (phase : ParserPhase)
    (elementSound : ∀ {input next : State} {value : α},
      element input = .ok value next →
        elementParses input.declarativeRemainder value
          next.declarativeRemainder)
    (elementShape : Parser.PreservesTokenWindow element)
    {input next : State} {values : DelimitedList α}
    (result : delimitedNoTrailing opening closing true element context phase
      input = .ok values next) :
    DeclarativeGrammar.NoTrailingDelimitedListParses opening closing
      elementParses input.declarativeRemainder values
      next.declarativeRemainder := by
  unfold delimitedNoTrailing delimitedWithPolicy at result
  cases openingResult : symbol opening context input with
  | invariant error => simp [openingResult] at result
  | reject failure rejected => simp [openingResult] at result
  | ok openingToken afterOpening =>
      have openingSound := symbol_ok_tokenAt opening context openingResult
      simp only [openingResult, Bool.true_and] at result
      split at result
      next closingPresent =>
        unfold closeDelimited at result
        cases closingResult : symbol closing context afterOpening with
        | invariant error => simp [closingResult] at result
        | reject failure rejected => simp [closingResult] at result
        | ok closingToken afterClosing =>
            have closingSound := symbol_ok_tokenAt closing context
              closingResult
            simp only [closingResult] at result
            cases result
            have closingTokenInput :
                DeclarativeGrammar.TokenAt input.tokens
                  input.window.endIndex (input.cursor + 1) {
                    span := closingToken.span
                    value := .symbol closing
                  } := by
              simpa only [openingSound.2, State.tokens, State.window,
                State.cursor] using closingSound.1
            have grammar :=
              DeclarativeGrammar.NoTrailingDelimitedListParses.empty
                (opening := opening) (closing := closing)
                (elementParses := elementParses)
                (input := input.declarativeRemainder)
                openingToken.span closingToken.span openingSound.1
                closingTokenInput
            simpa only [closingSound.2, openingSound.2,
              State.declarativeRemainder, State.tokens, State.window,
              State.cursor, List.reverse_nil, Nat.add_assoc, Nat.reduceAdd]
              using grammar
      next closingAbsent =>
        have closingAbsentBool : isSymbol afterOpening closing = false := by
          simp_all
        have closingAbsentAtAfterOpening :=
          symbolAbsentAt_of_isSymbol_eq_false closing closingAbsentBool
        have closingAbsentAtInput :
            DeclarativeGrammar.TokenKindAbsentAt input.tokens
              input.window.endIndex (input.cursor + 1) (.symbol closing) := by
          simpa only [openingSound.2, State.tokens, State.window,
            State.cursor] using closingAbsentAtAfterOpening
        have nonemptyResult :
            delimitedNoTrailing opening closing false element context phase
                input = .ok values next := by
          unfold delimitedNoTrailing delimitedWithPolicy
          simp only [openingResult, Bool.false_and, Bool.false_eq_true,
            if_false]
          exact result
        exact DeclarativeGrammar.NoTrailingDelimitedListParses.nonempty
          closingAbsentAtInput
          (delimitedNoTrailing_nonempty_success_sound opening closing element
            elementParses context phase elementSound elementShape
            nonemptyResult)

end Solcore.Syntax.Parser
