import Solcore.Syntax.Parser.DeclarativePrimitiveProperties
import Solcore.Syntax.Parser.Delimited

/-! Success soundness for nonempty lists that reject a trailing comma. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Closing fixes the final token, forward elements, cover, and remainder. -/
private theorem closeDelimited_noTrailing_success_sound {α : Type}
    (opening : Token) (closing : Symbol) (context : ParseContext)
    (elementsRev : List α) {input next : State}
    {values : DelimitedList α}
    (result : closeDelimited opening closing context elementsRev input =
      .ok values next) :
    ∃ closingSpan,
      DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
        input.cursor {
          span := closingSpan
          value := .symbol closing
        } ∧
      next.declarativeRemainder = {
        input.declarativeRemainder with cursor := input.cursor + 1
      } ∧
      values.elements = elementsRev.reverse ∧
      values.span = SourceSpan.cover opening.span closingSpan := by
  unfold closeDelimited at result
  cases closingResult : symbol closing context input with
  | invariant error => simp [closingResult] at result
  | reject failure rejected => simp [closingResult] at result
  | ok token afterClosing =>
      have sound := symbol_ok_tokenAt closing context closingResult
      simp only [closingResult] at result
      cases result
      refine ⟨token.span, sound.1, ?_, rfl, rfl⟩
      rw [sound.2]
      rfl

/-- Successful no-trailing tails recover their forward-order suffix. -/
private theorem afterDelimitedElement_noTrailing_success_sound {α : Type}
    (element : Parser α)
    (elementParses : DeclarativeGrammar.Remainder → α →
      DeclarativeGrammar.Remainder → Prop)
    (elementSound : ∀ {input next : State} {value : α},
      element input = .ok value next →
        elementParses input.declarativeRemainder value
          next.declarativeRemainder)
    (closing : Symbol) (context : ParseContext) (phase : ParserPhase)
    (opening : Token) :
    ∀ fuel elementsRev input values next,
      afterDelimitedElement element closing false context phase opening
          fuel elementsRev input = .ok values next →
      ∃ suffix closingSpan,
        values.elements = elementsRev.reverse ++ suffix ∧
        values.span = SourceSpan.cover opening.span closingSpan ∧
        DeclarativeGrammar.NoTrailingDelimitedTailParses closing
          elementParses input.declarativeRemainder suffix closingSpan
          next.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro elementsRev input values next result
      simp [afterDelimitedElement] at result
  | succ fuel inductionHypothesis =>
      intro elementsRev input values next result
      unfold afterDelimitedElement at result
      split at result
      · cases commaResult : symbol .comma context input with
        | invariant error => simp [commaResult] at result
        | reject failure rejected => simp [commaResult] at result
        | ok comma afterComma =>
            have commaSound := symbol_ok_tokenAt .comma context commaResult
            simp only [commaResult, Bool.false_and, Bool.false_eq_true,
              if_false] at result
            cases elementResult : element afterComma with
            | invariant error => simp [elementResult] at result
            | reject failure rejected => simp [elementResult] at result
            | ok value afterElement =>
                have valueGrammar := elementSound elementResult
                simp only [elementResult] at result
                split at result
                · rcases inductionHypothesis (value :: elementsRev)
                    afterElement values next result with
                    ⟨suffix, closingSpan, elementsEq, spanEq, tailGrammar⟩
                  have valueGrammarInput : elementParses {
                      input.declarativeRemainder with
                        cursor := input.cursor + 1
                    } value afterElement.declarativeRemainder := by
                    simpa only [commaSound.2, State.declarativeRemainder,
                      State.tokens, State.window, State.cursor] using
                      valueGrammar
                  have valueProgress :
                      afterComma.cursor < afterElement.cursor := by
                    assumption
                  have valueProgressInput :
                      input.cursor + 1 < afterElement.cursor := by
                    simpa only [commaSound.2, State.cursor] using valueProgress
                  refine ⟨value :: suffix, closingSpan, ?_, spanEq, ?_⟩
                  · calc
                      values.elements =
                          (value :: elementsRev).reverse ++ suffix :=
                        elementsEq
                      _ = elementsRev.reverse ++ (value :: suffix) := by
                        simp [List.reverse_cons, List.append_assoc]
                  · exact .next commaSound.1 valueGrammarInput
                      valueProgressInput tailGrammar
                · contradiction
      · have commaAbsentBool : isSymbol input .comma = false := by
          simp_all
        have commaAbsent := symbolAbsentAt_of_isSymbol_eq_false .comma
          commaAbsentBool
        split at result
        · rcases closeDelimited_noTrailing_success_sound opening closing
              context elementsRev result with
            ⟨closingSpan, closingToken, finalEq, elementsEq, spanEq⟩
          refine ⟨[], closingSpan, by simpa using elementsEq, spanEq, ?_⟩
          rw [finalEq]
          exact .close commaAbsent closingToken
        · unfold rejectAt at result
          contradiction

/--
Every successful nonempty list that rejects a trailing comma follows the
independent grammar. Element parsers may emit diagnostics.
-/
theorem delimitedNoTrailing_nonempty_success_sound {α : Type}
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
    (result : delimitedNoTrailing opening closing false element context phase
      input = .ok values next) :
    DeclarativeGrammar.NonemptyNoTrailingDelimitedListParses opening closing
      elementParses input.declarativeRemainder values
      next.declarativeRemainder := by
  have outputShape := delimitedWithPolicy_preservesTokenWindow opening closing
    false false element context phase elementShape input
  have policyResult : delimitedWithPolicy opening closing false false element
      context phase input = .ok values next := by
    simpa only [delimitedNoTrailing] using result
  rw [policyResult] at outputShape
  unfold delimitedNoTrailing delimitedWithPolicy at result
  cases openingResult : symbol opening context input with
  | invariant error => simp [openingResult] at result
  | reject failure rejected => simp [openingResult] at result
  | ok openingToken afterOpening =>
      have openingSound := symbol_ok_tokenAt opening context openingResult
      simp only [openingResult, Bool.false_and, Bool.false_eq_true, if_false]
        at result
      cases elementResult : element afterOpening with
      | invariant error => simp [elementResult] at result
      | reject failure rejected => simp [elementResult] at result
      | ok first afterFirst =>
          have firstGrammar := elementSound elementResult
          simp only [elementResult] at result
          split at result
          · rcases afterDelimitedElement_noTrailing_success_sound element
                elementParses elementSound closing context phase openingToken
                (afterOpening.remainingCount + 1) [first] afterFirst values next
                result with
              ⟨rest, closingSpan, elementsEq, spanEq, tailGrammar⟩
            have firstGrammarInput : elementParses {
                input.declarativeRemainder with cursor := input.cursor + 1
              } first afterFirst.declarativeRemainder := by
              simpa only [openingSound.2, State.declarativeRemainder,
                State.tokens, State.window, State.cursor] using firstGrammar
            have firstProgress : afterOpening.cursor < afterFirst.cursor := by
              assumption
            have firstProgressInput :
                input.cursor + 1 < afterFirst.cursor := by
              simpa only [openingSound.2, State.cursor] using firstProgress
            unfold DeclarativeGrammar.NonemptyNoTrailingDelimitedListParses
            refine ⟨openingToken.span, first, afterFirst.declarativeRemainder,
              rest, closingSpan, outputShape.1,
              congrArg TokenWindow.endIndex outputShape.2, openingSound.1,
              firstGrammarInput, firstProgressInput, tailGrammar, ?_, spanEq⟩
            simpa using elementsEq
          · contradiction

end Solcore.Syntax.Parser
