import Solcore.Syntax.Parser.EnumConstructorSoundnessProperties
import Solcore.Syntax.Parser.EnumElementTotalityProperties

/-! Success soundness for the fuel-bounded enum-body loop. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.EnumInternals

private theorem bind_ok_components {α β : Type} {first : Parser α}
    {next : α → Parser β} {input final : State} {value : β}
    (parsed : (first >>= next) input = .ok value final) :
    ∃ firstValue afterFirst,
      first input = .ok firstValue afterFirst ∧
        next firstValue afterFirst = .ok value final := by
  change (match first input with
    | .ok firstValue afterFirst => next firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value final at parsed
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      rw [firstResult] at parsed
      exact ⟨firstValue, afterFirst, rfl, parsed⟩
  | reject failure rejected =>
      rw [firstResult] at parsed
      contradiction
  | invariant error =>
      rw [firstResult] at parsed
      contradiction

private theorem closeEnumBody_success_sound (opening : Token)
    (constructorsRev : List EnumConstructor) {input next : State}
    {body : EnumBody}
    (result : closeEnumBody opening constructorsRev input = .ok body next) :
    ∃ closingSpan,
      body = {
        span := SourceSpan.cover opening.span closingSpan
        constructors := constructorsRev.reverse
      } ∧
      DeclarativeGrammar.ExactTokenParses (.symbol .rightBrace)
        input.declarativeRemainder closingSpan next.declarativeRemainder := by
  unfold closeEnumBody at result
  rcases bind_ok_components result with
    ⟨closing, afterClosing, closingResult, finished⟩
  cases finished
  exact ⟨closing.span, rfl,
    symbol_success_exactTokenParses .rightBrace .topItem closingResult⟩

private theorem tail_close_of_exact
    {input output : DeclarativeGrammar.Remainder}
    {closingSpan : SourceSpan}
    (commaAbsent : DeclarativeGrammar.TokenKindAbsentAt
      input.tokens input.endIndex input.cursor (.symbol .comma))
    (closing : DeclarativeGrammar.ExactTokenParses (.symbol .rightBrace)
      input closingSpan output) :
    DeclarativeGrammar.TrailingDelimitedTailParses .rightBrace
      DeclarativeGrammar.EnumConstructorParses input [] closingSpan output := by
  rcases closing with ⟨closingToken, rfl⟩
  exact .close commaAbsent closingToken

private theorem tail_trailing_of_exact
    {input afterComma output : DeclarativeGrammar.Remainder}
    {commaSpan closingSpan : SourceSpan}
    (comma : DeclarativeGrammar.ExactTokenParses (.symbol .comma)
      input commaSpan afterComma)
    (closing : DeclarativeGrammar.ExactTokenParses (.symbol .rightBrace)
      afterComma closingSpan output) :
    DeclarativeGrammar.TrailingDelimitedTailParses .rightBrace
      DeclarativeGrammar.EnumConstructorParses input [] closingSpan output := by
  rcases comma with ⟨commaToken, rfl⟩
  rcases closing with ⟨closingToken, rfl⟩
  exact .trailing commaToken closingToken

private theorem tail_next_of_exact
    {input afterComma afterElement output : DeclarativeGrammar.Remainder}
    {commaSpan closingSpan : SourceSpan} {element : EnumConstructor}
    {elements : List EnumConstructor}
    (comma : DeclarativeGrammar.ExactTokenParses (.symbol .comma)
      input commaSpan afterComma)
    (closingAbsent : DeclarativeGrammar.TokenKindAbsentAt afterComma.tokens
      afterComma.endIndex afterComma.cursor (.symbol .rightBrace))
    (elementParsed : DeclarativeGrammar.EnumConstructorParses
      afterComma element afterElement)
    (progress : afterComma.cursor < afterElement.cursor)
    (tail : DeclarativeGrammar.TrailingDelimitedTailParses .rightBrace
      DeclarativeGrammar.EnumConstructorParses afterElement elements
        closingSpan output) :
    DeclarativeGrammar.TrailingDelimitedTailParses .rightBrace
      DeclarativeGrammar.EnumConstructorParses input (element :: elements)
        closingSpan output := by
  rcases comma with ⟨commaToken, rfl⟩
  exact .next commaToken closingAbsent elementParsed progress tail

private theorem enumConstructors_success_sound_strong (opening : Token) :
    ∀ fuel constructorsRev input body next,
      enumConstructors opening fuel constructorsRev input = .ok body next →
        ∃ rest closingSpan,
          body = {
            span := SourceSpan.cover opening.span closingSpan
            constructors := constructorsRev.reverse ++ rest
          } ∧
          DeclarativeGrammar.TrailingDelimitedTailParses .rightBrace
            DeclarativeGrammar.EnumConstructorParses
              input.declarativeRemainder rest closingSpan
                next.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro constructorsRev input body next result
      simp [enumConstructors] at result
  | succ fuel inductionHypothesis =>
      intro constructorsRev input body next result
      unfold enumConstructors at result
      cases commaPresent : isSymbol input .comma with
      | false =>
          simp only [commaPresent, Bool.false_eq_true, if_false] at result
          rcases closeEnumBody_success_sound opening constructorsRev result with
            ⟨closingSpan, bodyEq, closingGrammar⟩
          refine ⟨[], closingSpan, ?_,
            tail_close_of_exact
              (symbolAbsentAt_of_isSymbol_eq_false .comma commaPresent)
              closingGrammar⟩
          simpa using bodyEq
      | true =>
          simp only [commaPresent, if_true] at result
          cases commaResult : symbol .comma .topItem input with
          | invariant error => simp [commaResult] at result
          | reject failure rejected => simp [commaResult] at result
          | ok comma afterComma =>
              simp only [commaResult] at result
              have commaGrammar :=
                symbol_success_exactTokenParses .comma .topItem commaResult
              cases closingPresent : isSymbol afterComma .rightBrace with
              | true =>
                  simp only [closingPresent, if_true] at result
                  rcases closeEnumBody_success_sound opening constructorsRev
                      result with ⟨closingSpan, bodyEq, closingGrammar⟩
                  refine ⟨[], closingSpan, ?_,
                    tail_trailing_of_exact commaGrammar closingGrammar⟩
                  simpa using bodyEq
              | false =>
                  simp only [closingPresent, Bool.false_eq_true, if_false]
                    at result
                  cases constructorResult : enumConstructor afterComma with
                  | invariant error => simp [constructorResult] at result
                  | reject failure rejected =>
                      simp [constructorResult] at result
                  | ok constructor afterConstructor =>
                      simp only [constructorResult] at result
                      by_cases progress :
                          afterComma.cursor < afterConstructor.cursor
                      · simp only [progress, if_true] at result
                        rcases inductionHypothesis
                            (constructor :: constructorsRev) afterConstructor
                            body next result with
                          ⟨rest, closingSpan, bodyEq, tailGrammar⟩
                        refine ⟨constructor :: rest, closingSpan, ?_,
                          tail_next_of_exact commaGrammar
                            (symbolAbsentAt_of_isSymbol_eq_false .rightBrace
                              closingPresent)
                            (enumConstructor_success_sound constructorResult)
                            progress tailGrammar⟩
                        simpa [List.reverse_cons, List.append_assoc] using bodyEq
                      · simp only [progress, if_false] at result
                        contradiction

private theorem enumBody_empty_of_exact
    {input afterOpening output : DeclarativeGrammar.Remainder}
    {openingSpan closingSpan : SourceSpan}
    (opening : DeclarativeGrammar.ExactTokenParses (.symbol .leftBrace)
      input openingSpan afterOpening)
    (closing : DeclarativeGrammar.ExactTokenParses (.symbol .rightBrace)
      afterOpening closingSpan output) :
    DeclarativeGrammar.EnumBodyParses input
      (SourceSpan.cover openingSpan closingSpan) [] output := by
  unfold DeclarativeGrammar.EnumBodyParses
  rcases opening with ⟨openingToken, rfl⟩
  rcases closing with ⟨closingToken, rfl⟩
  exact .empty openingSpan closingSpan openingToken closingToken

/-- Every successful enum body follows the exact forward constructor grammar. -/
theorem enumBody_success_sound {input next : State} {body : EnumBody}
    (result : enumBody input = .ok body next) :
    DeclarativeGrammar.EnumBodyParses input.declarativeRemainder body.span
      body.constructors next.declarativeRemainder := by
  have outputShape := enumBody_preservesTokenWindow input
  rw [result] at outputShape
  unfold enumBody at result
  cases openingResult : symbol .leftBrace .topItem input with
  | invariant error => simp [openingResult] at result
  | reject failure rejected => simp [openingResult] at result
  | ok opening afterOpening =>
      simp only [openingResult] at result
      have openingSound := symbol_ok_tokenAt .leftBrace .topItem openingResult
      have openingGrammar :=
        symbol_success_exactTokenParses .leftBrace .topItem openingResult
      cases emptyPresent : isSymbol afterOpening .rightBrace with
      | true =>
          simp only [emptyPresent, if_true] at result
          rcases closeEnumBody_success_sound opening [] result with
            ⟨closingSpan, bodyEq, closingGrammar⟩
          rw [bodyEq]
          simpa using enumBody_empty_of_exact openingGrammar closingGrammar
      | false =>
          simp only [emptyPresent, Bool.false_eq_true, if_false] at result
          cases firstResult : enumConstructor afterOpening with
          | invariant error => simp [firstResult] at result
          | reject failure rejected => simp [firstResult] at result
          | ok first afterFirst =>
              simp only [firstResult] at result
              rcases enumConstructors_success_sound_strong opening
                  (afterFirst.remainingCount + 1) [first] afterFirst body next
                  result with ⟨rest, closingSpan, bodyEq, tailGrammar⟩
              rw [bodyEq]
              apply DeclarativeGrammar.TrailingDelimitedListParses.nonempty
              · have absent := symbolAbsentAt_of_isSymbol_eq_false
                    .rightBrace emptyPresent
                simpa only [openingSound.2, State.declarativeRemainder,
                  State.tokens, State.window, State.cursor] using absent
              · unfold DeclarativeGrammar.NonemptyTrailingDelimitedListParses
                refine ⟨opening.span, first, afterFirst.declarativeRemainder,
                  rest, closingSpan, outputShape.1,
                  congrArg TokenWindow.endIndex outputShape.2,
                  openingSound.1, ?_, ?_, tailGrammar, by simp, rfl⟩
                · simpa only [openingSound.2, State.declarativeRemainder,
                    State.tokens, State.window, State.cursor] using
                    enumConstructor_success_sound firstResult
                · have progress := enumConstructor_cursor_lt_onSuccess
                    firstResult
                  simpa only [openingSound.2, State.declarativeRemainder,
                    State.cursor] using progress

/-- Enum-body grammar soundness composes with source validity. -/
theorem enumBody_success_sound_and_validFor {input next : State}
    {body : EnumBody} (inputValid : input.ValidFor)
    (result : enumBody input = .ok body next) :
    DeclarativeGrammar.EnumBodyParses input.declarativeRemainder body.span
        body.constructors next.declarativeRemainder ∧
      EnumBody.ValidFor input.file body := by
  refine ⟨enumBody_success_sound result, ?_⟩
  have valid := enumBody_validFor input inputValid
  rw [result] at valid
  exact valid.1

end Solcore.Syntax.Parser.EnumInternals
