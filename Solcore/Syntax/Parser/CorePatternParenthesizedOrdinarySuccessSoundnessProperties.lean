import Solcore.Syntax.DeclarativeCorePatternParenthesizedOutcomeGrammar
import Solcore.Syntax.Parser.CorePatternBasicSoundnessProperties

/-! Unconditional ordinary-success reflection for parenthesized patterns. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PatternInternals

/-- Successful tuple-tail execution follows the exact forward-order grammar.
Fuel exhaustion and non-progress cannot inhabit this theorem. -/
theorem patternTupleTail_success_ordinary_sound_strong
    (nested : Parser Pattern)
    (nestedOrdinary : DeclarativeGrammar.Remainder → Pattern →
      DeclarativeGrammar.Remainder → Prop)
    (nestedSuccessSound : ∀ {input output : State} {pattern : Pattern},
      nested input = .ok pattern output → nestedOrdinary
        input.declarativeRemainder pattern output.declarativeRemainder)
    (opening : Token) : ∀ fuel elementsRev input pattern output,
      patternTupleTail nested opening fuel elementsRev input =
        .ok pattern output →
      ∃ suffix closingSpan,
        pattern = DeclarativeGrammar.closeParenthesizedPattern opening.span
          closingSpan (elementsRev.reverse ++ suffix) ∧
        DeclarativeGrammar.ParenthesizedPatternTupleTailParses nestedOrdinary
          input.declarativeRemainder suffix closingSpan
            output.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro elementsRev input pattern output result
      simp [patternTupleTail] at result
  | succ fuel inductionHypothesis =>
      intro elementsRev input pattern output result
      unfold patternTupleTail at result
      cases commaResult : symbol .comma .pattern input with
      | invariant error => simp [commaResult] at result
      | reject failure rejected => simp [commaResult] at result
      | ok comma afterComma =>
          simp only [commaResult] at result
          have commaParsed := symbol_success_exactTokenParses .comma
            .pattern commaResult
          split at result
          · rcases closePatternTuple_success_sound opening elementsRev result
                with ⟨closingSpan, patternEq, closingParsed⟩
            exact ⟨[], closingSpan, by simpa using patternEq,
              .trailing comma.span closingSpan commaParsed closingParsed⟩
          · have closingAbsentBool :
                isSymbol afterComma .rightParen = false := by simp_all
            have closingAbsent := symbolAbsentAt_of_isSymbol_eq_false
              .rightParen closingAbsentBool
            cases elementResult : nested afterComma with
            | invariant error => simp [elementResult] at result
            | reject failure rejected => simp [elementResult] at result
            | ok element afterElement =>
                simp only [elementResult] at result
                split at result
                next noProgress => contradiction
                next progressBranch =>
                  have elementProgress :
                      afterComma.cursor < afterElement.cursor :=
                    Nat.lt_of_not_ge progressBranch
                  have elementGrammar := nestedSuccessSound elementResult
                  split at result
                  next commaPresent =>
                    rcases inductionHypothesis (element :: elementsRev)
                        afterElement pattern output result with
                      ⟨suffix, closingSpan, patternEq, tailGrammar⟩
                    refine ⟨element :: suffix, closingSpan, ?_,
                      .next comma.span closingSpan commaParsed closingAbsent
                        elementGrammar (by
                          simpa [State.declarativeRemainder] using
                            elementProgress) tailGrammar⟩
                    simpa [List.reverse_cons, List.append_assoc] using
                      patternEq
                  next commaAbsentBranch =>
                    rcases closePatternTuple_success_sound opening
                        (element :: elementsRev) result with
                      ⟨closingSpan, patternEq, closingParsed⟩
                    have commaAbsent := symbolAbsentAt_of_isSymbol_eq_false
                      .comma (input := afterElement) (by simp_all)
                    refine ⟨[element], closingSpan, ?_,
                      .final comma.span closingSpan commaParsed closingAbsent
                        elementGrammar (by
                          simpa [State.declarativeRemainder] using
                            elementProgress) commaAbsent closingParsed⟩
                    simpa [List.reverse_cons, List.append_assoc] using
                      patternEq

/-- Every executable success has the exact empty, group, or tuple shape. -/
theorem parenthesizedPattern_success_ordinary_sound
    (nested : Parser Pattern)
    (nestedOrdinary : DeclarativeGrammar.Remainder → Pattern →
      DeclarativeGrammar.Remainder → Prop)
    (nestedSuccessSound : ∀ {input output : State} {pattern : Pattern},
      nested input = .ok pattern output → nestedOrdinary
        input.declarativeRemainder pattern output.declarativeRemainder)
    {input output : State} {pattern : Pattern}
    (result : parenthesizedPattern nested input = .ok pattern output) :
    DeclarativeGrammar.ParenthesizedPatternOrdinaryParses nestedOrdinary
      input.declarativeRemainder pattern output.declarativeRemainder := by
  unfold parenthesizedPattern at result
  cases openingResult : symbol .leftParen .pattern input with
  | invariant error => simp [openingResult] at result
  | reject failure rejected => simp [openingResult] at result
  | ok opening afterOpening =>
      simp only [openingResult] at result
      have openingParsed := symbol_success_exactTokenParses .leftParen
        .pattern openingResult
      split at result
      · rcases closePatternTuple_success_sound opening [] result with
          ⟨closingSpan, patternEq, closingParsed⟩
        subst pattern
        exact .empty opening.span closingSpan openingParsed closingParsed
      · have closingAbsentBool :
            isSymbol afterOpening .rightParen = false := by simp_all
        have closingAbsent := symbolAbsentAt_of_isSymbol_eq_false .rightParen
          closingAbsentBool
        cases firstResult : nested afterOpening with
        | invariant error => simp [firstResult] at result
        | reject failure rejected => simp [firstResult] at result
        | ok first afterFirst =>
            simp only [firstResult] at result
            split at result
            next noProgress => contradiction
            next progressBranch =>
              have firstProgress : afterOpening.cursor < afterFirst.cursor :=
                Nat.lt_of_not_ge progressBranch
              have firstGrammar := nestedSuccessSound firstResult
              split at result
              next commaPresent =>
                rcases patternTupleTail_success_ordinary_sound_strong nested
                    nestedOrdinary nestedSuccessSound opening
                      (afterFirst.remainingCount + 1) [first] afterFirst
                        pattern output result with
                  ⟨rest, closingSpan, patternEq, tailGrammar⟩
                subst pattern
                simpa using
                  (DeclarativeGrammar.ParenthesizedPatternParses.tuple
                    opening.span closingSpan openingParsed closingAbsent
                      firstGrammar (by
                        simpa [State.declarativeRemainder] using firstProgress)
                        tailGrammar)
              next commaAbsentBranch =>
                rcases closePatternTuple_success_sound opening [first] result
                    with ⟨closingSpan, patternEq, closingParsed⟩
                have commaAbsent := symbolAbsentAt_of_isSymbol_eq_false
                  .comma (input := afterFirst) (by simp_all)
                subst pattern
                exact .group opening.span closingSpan openingParsed
                  closingAbsent firstGrammar (by
                    simpa [State.declarativeRemainder] using firstProgress)
                      commaAbsent closingParsed

end Solcore.Syntax.Parser.PatternInternals
