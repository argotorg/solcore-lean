import Solcore.Syntax.DeclarativeCoreParenthesizedOutcomeGrammar
import Solcore.Syntax.Parser.DeclarativePrimitiveProperties
import Solcore.Syntax.Parser.Expression.Atom

/-! Unconditional ordinary-success reflection for Core parentheses. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

private theorem bind_success_components {alpha beta : Type}
    {first : Parser alpha} {nextParser : alpha → Parser beta}
    {input final : State} {value : beta}
    (result : (first >>= nextParser) input = .ok value final) :
    ∃ firstValue afterFirst,
      first input = .ok firstValue afterFirst ∧
        nextParser firstValue afterFirst = .ok value final := by
  change (match first input with
    | .ok firstValue afterFirst => nextParser firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value final at result
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      rw [firstResult] at result
      exact ⟨firstValue, afterFirst, rfl, result⟩
  | reject failure rejected => rw [firstResult] at result; contradiction
  | invariant error => rw [firstResult] at result; contradiction

private theorem closeParenthesizedExpression_eq_tuple_of_length_ne_one
    (openingSpan closingSpan : SourceSpan) (elements : List Expr)
    (lengthNe : elements.length ≠ 1) :
    DeclarativeGrammar.closeParenthesizedExpression openingSpan closingSpan
      elements = {
        span := SourceSpan.cover openingSpan closingSpan
        value := .tuple {
          span := SourceSpan.cover openingSpan closingSpan
          elements
        }
      } := by
  unfold DeclarativeGrammar.closeParenthesizedExpression
  cases elements with
  | nil => rfl
  | cons head tail =>
      cases tail with
      | nil => simp at lengthNe
      | cons second rest => rfl

private theorem closeTuple_success_ordinary_sound (opening : Token)
    (elementsRev : List Expr) {input output : State} {expression : Expr}
    (result : closeTuple opening elementsRev input = .ok expression output) :
    ∃ closingSpan,
      expression = DeclarativeGrammar.closeParenthesizedExpression
        opening.span closingSpan elementsRev.reverse ∧
      DeclarativeGrammar.ExactTokenParses (.symbol .rightParen)
        input.declarativeRemainder closingSpan
          output.declarativeRemainder := by
  unfold closeTuple at result
  rcases bind_success_components result with
    ⟨closing, afterClosing, closingResult, finished⟩
  have closingParsed := symbol_success_exactTokenParses .rightParen
    .expression closingResult
  cases elementsRev with
  | nil =>
      cases finished
      exact ⟨closing.span, by
        simp [DeclarativeGrammar.closeParenthesizedExpression],
          closingParsed⟩
  | cons head tail =>
      cases tail with
      | nil =>
          cases finished
          exact ⟨closing.span, by
            simp [DeclarativeGrammar.closeParenthesizedExpression],
              closingParsed⟩
      | cons second rest =>
          cases finished
          refine ⟨closing.span, ?_, closingParsed⟩
          rw [closeParenthesizedExpression_eq_tuple_of_length_ne_one]
          simp

/-- Successful tuple-tail execution follows the exact source-order ordinary
tail grammar. Fuel exhaustion and no-progress cannot inhabit this theorem. -/
theorem tupleTail_success_ordinary_sound_strong
    (nested : Parser Expr)
    (nestedOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (nestedSuccessSound : ∀ {input output : State} {expression : Expr},
      nested input = .ok expression output → nestedOrdinary
        input.declarativeRemainder expression output.declarativeRemainder)
    (opening : Token) : ∀ fuel elementsRev input expression output,
      tupleTail nested opening fuel elementsRev input = .ok expression output →
      ∃ suffix closingSpan,
        expression = DeclarativeGrammar.closeParenthesizedExpression
          opening.span closingSpan (elementsRev.reverse ++ suffix) ∧
        DeclarativeGrammar.ParenthesizedTupleTailParses nestedOrdinary
          input.declarativeRemainder suffix closingSpan
            output.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro elementsRev input expression output result
      simp [tupleTail] at result
  | succ fuel inductionHypothesis =>
      intro elementsRev input expression output result
      unfold tupleTail at result
      cases commaResult : symbol .comma .expression input with
      | invariant error => simp [commaResult] at result
      | reject failure rejected => simp [commaResult] at result
      | ok comma afterComma =>
          simp only [commaResult] at result
          have commaParsed := symbol_success_exactTokenParses .comma
            .expression commaResult
          split at result
          · rcases closeTuple_success_ordinary_sound opening elementsRev
                result with ⟨closingSpan, expressionEq, closingParsed⟩
            exact ⟨[], closingSpan, by simpa using expressionEq,
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
                next elementProgress =>
                  have elementGrammar := nestedSuccessSound elementResult
                  split at result
                  next commaPresent =>
                    rcases inductionHypothesis (element :: elementsRev)
                        afterElement expression output result with
                      ⟨suffix, closingSpan, expressionEq, tailGrammar⟩
                    refine ⟨element :: suffix, closingSpan, ?_,
                      .next comma.span closingSpan commaParsed closingAbsent
                        elementGrammar (by
                          simpa [State.declarativeRemainder] using
                            elementProgress) tailGrammar⟩
                    simpa [List.reverse_cons, List.append_assoc] using
                      expressionEq
                  next commaAbsentBranch =>
                    rcases closeTuple_success_ordinary_sound opening
                        (element :: elementsRev) result with
                      ⟨closingSpan, expressionEq, closingParsed⟩
                    have commaAbsent := symbolAbsentAt_of_isSymbol_eq_false
                      .comma (input := afterElement) (by simp_all)
                    refine ⟨[element], closingSpan, ?_,
                      .final comma.span closingSpan commaParsed closingAbsent
                        elementGrammar (by
                          simpa [State.declarativeRemainder] using
                            elementProgress) commaAbsent closingParsed⟩
                    simpa [List.reverse_cons, List.append_assoc] using
                      expressionEq
                next noProgress => contradiction

/-- Every executable parenthesized success follows the exact empty, group,
or tuple ordinary grammar without requiring diagnostic freedom. -/
theorem parenthesized_success_ordinary_sound
    (nested : Parser Expr)
    (nestedOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (nestedSuccessSound : ∀ {input output : State} {expression : Expr},
      nested input = .ok expression output → nestedOrdinary
        input.declarativeRemainder expression output.declarativeRemainder)
    {input output : State} {expression : Expr}
    (result : parenthesized nested input = .ok expression output) :
    DeclarativeGrammar.ParenthesizedExpressionOrdinaryParses nestedOrdinary
      input.declarativeRemainder expression output.declarativeRemainder := by
  unfold parenthesized at result
  cases openingResult : symbol .leftParen .expression input with
  | invariant error => simp [openingResult] at result
  | reject failure rejected => simp [openingResult] at result
  | ok opening afterOpening =>
      simp only [openingResult] at result
      have openingParsed := symbol_success_exactTokenParses .leftParen
        .expression openingResult
      split at result
      · rcases closeTuple_success_ordinary_sound opening [] result with
          ⟨closingSpan, expressionEq, closingParsed⟩
        subst expression
        exact .empty opening.span closingSpan openingParsed closingParsed
      · have closingAbsentBool :
            isSymbol afterOpening .rightParen = false := by simp_all
        have closingAbsent := symbolAbsentAt_of_isSymbol_eq_false
          .rightParen closingAbsentBool
        cases elementResult : nested afterOpening with
        | invariant error => simp [elementResult] at result
        | reject failure rejected => simp [elementResult] at result
        | ok first afterFirst =>
            simp only [elementResult] at result
            split at result
            next noProgress => contradiction
            next progressBranch =>
              have firstProgress : afterOpening.cursor < afterFirst.cursor :=
                Nat.lt_of_not_ge progressBranch
              have firstGrammar := nestedSuccessSound elementResult
              split at result
              next commaPresent =>
                rcases tupleTail_success_ordinary_sound_strong nested
                    nestedOrdinary nestedSuccessSound opening
                      (afterFirst.remainingCount + 1) [first] afterFirst
                        expression output result with
                  ⟨rest, closingSpan, expressionEq, tailGrammar⟩
                subst expression
                simpa using
                  (DeclarativeGrammar.ParenthesizedExpressionParses.tuple
                    opening.span closingSpan openingParsed closingAbsent
                      firstGrammar (by
                        simpa [State.declarativeRemainder] using firstProgress)
                        tailGrammar)
              next commaAbsentBranch =>
                rcases closeTuple_success_ordinary_sound opening [first]
                    result with
                  ⟨closingSpan, expressionEq, closingParsed⟩
                have commaAbsent := symbolAbsentAt_of_isSymbol_eq_false
                  .comma (input := afterFirst) (by simp_all)
                subst expression
                exact .group opening.span closingSpan openingParsed
                  closingAbsent firstGrammar (by
                    simpa [State.declarativeRemainder] using firstProgress)
                      commaAbsent closingParsed

end Solcore.Syntax.Parser.ExpressionAtomInternals
