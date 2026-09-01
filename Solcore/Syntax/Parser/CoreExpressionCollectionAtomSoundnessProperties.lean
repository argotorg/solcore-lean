import Solcore.Syntax.DeclarativeCoreCollectionAtomGrammar
import Solcore.Syntax.Parser.CoreExpressionCollectionAtomDiagnosticReflectionProperties
import Solcore.Syntax.Parser.DeclarativePrimitiveProperties
import Solcore.Syntax.Parser.DelimitedNoTrailingAllowEmptyDiagnosticFreeSoundnessProperties
import Solcore.Syntax.Parser.Expression.AtomProperties

/-!
Exact diagnostic-free soundness for parenthesized and array Core atoms.
-/

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

private theorem closeTuple_success_sound (opening : Token)
    (elementsRev : List Expr) {input next : State} {value : Expr}
    (result : closeTuple opening elementsRev input = .ok value next) :
    ∃ closingSpan,
      value = DeclarativeGrammar.closeParenthesizedExpression opening.span
        closingSpan elementsRev.reverse ∧
      DeclarativeGrammar.ExactTokenParses (.symbol .rightParen)
        input.declarativeRemainder closingSpan next.declarativeRemainder := by
  unfold closeTuple at result
  rcases bind_success_components result with
    ⟨closing, afterClosing, closingResult, finished⟩
  have closingParsed := symbol_success_exactTokenParses .rightParen
    .expression closingResult
  cases elementsRev with
  | nil =>
      cases finished
      exact ⟨closing.span, by
        simp [DeclarativeGrammar.closeParenthesizedExpression], closingParsed⟩
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

private theorem tupleTail_success_sound_strong
    (nested : Parser Expr)
    (nestedParses : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested)
    (nestedSound : ∀ {input next : State} {value : Expr},
      next.diagnosticsRev = [] → nested input = .ok value next →
      nestedParses input.declarativeRemainder value
        next.declarativeRemainder)
    (opening : Token) : ∀ fuel elementsRev input value next,
      next.diagnosticsRev = [] →
      tupleTail nested opening fuel elementsRev input = .ok value next →
      ∃ suffix closingSpan,
        value = DeclarativeGrammar.closeParenthesizedExpression opening.span
          closingSpan (elementsRev.reverse ++ suffix) ∧
        DeclarativeGrammar.ParenthesizedTupleTailParses nestedParses
          input.declarativeRemainder suffix closingSpan
            next.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro elementsRev input value next diagnosticFree result
      simp [tupleTail] at result
  | succ fuel inductionHypothesis =>
      intro elementsRev input value next diagnosticFree result
      unfold tupleTail at result
      cases commaResult : symbol .comma .expression input with
      | invariant error => simp [commaResult] at result
      | reject failure rejected => simp [commaResult] at result
      | ok comma afterComma =>
          simp only [commaResult] at result
          have commaParsed := symbol_success_exactTokenParses .comma
            .expression commaResult
          split at result
          · rcases closeTuple_success_sound opening elementsRev result with
              ⟨closingSpan, valueEq, closingParsed⟩
            exact ⟨[], closingSpan, by simpa using valueEq,
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
                  split at result
                  next commaPresent =>
                    rcases inductionHypothesis (element :: elementsRev)
                        afterElement value next diagnosticFree result with
                      ⟨suffix, closingSpan, valueEq, tailGrammar⟩
                    have afterElementFree :=
                      tupleTail_reflectsDiagnosticFreeOnSuccess nested
                        nestedReflects opening fuel (element :: elementsRev)
                          afterElement value next result diagnosticFree
                    have elementGrammar := nestedSound afterElementFree
                      elementResult
                    refine ⟨element :: suffix, closingSpan, ?_,
                      .next comma.span closingSpan commaParsed closingAbsent
                        elementGrammar (by
                          simpa [State.declarativeRemainder] using
                            elementProgress) tailGrammar⟩
                    simpa [List.reverse_cons, List.append_assoc] using valueEq
                  next commaAbsentBranch =>
                    rcases closeTuple_success_sound opening
                        (element :: elementsRev) result with
                      ⟨closingSpan, valueEq, closingParsed⟩
                    have afterElementFree :=
                      closeTuple_reflectsDiagnosticFreeOnSuccess opening
                        (element :: elementsRev) afterElement value next result
                          diagnosticFree
                    have elementGrammar := nestedSound afterElementFree
                      elementResult
                    have commaAbsent := symbolAbsentAt_of_isSymbol_eq_false
                      .comma (input := afterElement) (by simp_all)
                    refine ⟨[element], closingSpan, ?_,
                      .final comma.span closingSpan commaParsed closingAbsent
                        elementGrammar (by
                          simpa [State.declarativeRemainder] using
                            elementProgress) commaAbsent
                          closingParsed⟩
                    simpa [List.reverse_cons, List.append_assoc] using valueEq
                next noProgress => contradiction

/-- Every diagnostic-free parenthesized success follows its exact grammar. -/
theorem parenthesized_success_sound
    (nested : Parser Expr)
    (nestedParses : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested)
    (nestedSound : ∀ {input next : State} {value : Expr},
      next.diagnosticsRev = [] → nested input = .ok value next →
      nestedParses input.declarativeRemainder value
        next.declarativeRemainder)
    {input next : State} {value : Expr}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : parenthesized nested input = .ok value next) :
    DeclarativeGrammar.ParenthesizedExpressionParses nestedParses
      input.declarativeRemainder value next.declarativeRemainder := by
  unfold parenthesized at result
  cases openingResult : symbol .leftParen .expression input with
  | invariant error => simp [openingResult] at result
  | reject failure rejected => simp [openingResult] at result
  | ok opening afterOpening =>
      simp only [openingResult] at result
      have openingParsed := symbol_success_exactTokenParses .leftParen
        .expression openingResult
      split at result
      · rcases closeTuple_success_sound opening [] result with
          ⟨closingSpan, valueEq, closingParsed⟩
        subst value
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
              split at result
              next commaPresent =>
                rcases tupleTail_success_sound_strong nested nestedParses
                    nestedReflects nestedSound opening
                      (afterFirst.remainingCount + 1) [first] afterFirst value
                        next diagnosticFree result with
                  ⟨rest, closingSpan, valueEq, tailGrammar⟩
                have afterFirstFree :=
                  tupleTail_reflectsDiagnosticFreeOnSuccess nested
                    nestedReflects opening (afterFirst.remainingCount + 1)
                      [first] afterFirst value next result diagnosticFree
                have firstGrammar := nestedSound afterFirstFree elementResult
                subst value
                simpa using (DeclarativeGrammar.ParenthesizedExpressionParses.tuple
                  opening.span closingSpan openingParsed closingAbsent
                    firstGrammar (by
                      simpa [State.declarativeRemainder] using
                        firstProgress) tailGrammar)
              next commaAbsentBranch =>
                rcases closeTuple_success_sound opening [first] result with
                  ⟨closingSpan, valueEq, closingParsed⟩
                have afterFirstFree :=
                  closeTuple_reflectsDiagnosticFreeOnSuccess opening [first]
                    afterFirst value next result diagnosticFree
                have firstGrammar := nestedSound afterFirstFree elementResult
                have commaAbsent := symbolAbsentAt_of_isSymbol_eq_false
                  .comma (input := afterFirst) (by simp_all)
                subst value
                exact .group opening.span closingSpan openingParsed
                  closingAbsent firstGrammar (by
                    simpa [State.declarativeRemainder] using
                      firstProgress) commaAbsent
                    closingParsed

/-- Every diagnostic-free array success follows its no-trailing grammar. -/
theorem arrayLiteral_success_sound
    (nested : Parser Expr)
    (nestedParses : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested)
    (nestedSound : ∀ {input next : State} {value : Expr},
      next.diagnosticsRev = [] → nested input = .ok value next →
      nestedParses input.declarativeRemainder value
        next.declarativeRemainder)
    (nestedShape : Parser.PreservesTokenWindow nested)
    {input next : State} {value : Expr}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : arrayLiteral nested input = .ok value next) :
    DeclarativeGrammar.ArrayLiteralExpressionParses nestedParses
      input.declarativeRemainder value next.declarativeRemainder := by
  unfold arrayLiteral at result
  rcases bind_success_components result with
    ⟨values, afterValues, valuesResult, finished⟩
  cases finished
  exact .parsed
    (delimitedNoTrailing_allowEmpty_success_sound_of_diagnosticFree
      .leftBracket .rightBracket nested nestedParses .expression .expression
        nestedSound nestedReflects nestedShape diagnosticFree valuesResult)

end Solcore.Syntax.Parser.ExpressionAtomInternals
