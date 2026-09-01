import Solcore.Syntax.DeclarativeCorePatternBasicGrammar
import Solcore.Syntax.Parser.CorePatternBasicDiagnosticReflectionProperties
import Solcore.Syntax.Parser.DeclarativePrimitiveProperties
import Solcore.Syntax.Parser.PatternProperties

/-!
Exact diagnostic-free soundness for basic Core pattern leaves and
parenthesized patterns.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PatternInternals

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

/-- Every successful wildcard pattern consumes its exact marker token. -/
theorem wildcardPattern_success_sound {input next : State}
    {pattern : Pattern}
    (result : wildcardPattern input = .ok pattern next) :
    DeclarativeGrammar.WildcardPatternParses input.declarativeRemainder
      pattern next.declarativeRemainder := by
  unfold wildcardPattern at result
  rcases bind_success_components result with
    ⟨marker, afterMarker, markerResult, finished⟩
  cases finished
  exact .parsed marker.span
    (symbol_success_exactTokenParses .underscore .pattern markerResult)

/-- Every successful literal pattern follows the exact literal grammar. -/
theorem literalPattern_success_sound {input next : State}
    {pattern : Pattern}
    (result : literalPattern input = .ok pattern next) :
    DeclarativeGrammar.LiteralPatternParses input.declarativeRemainder
      pattern next.declarativeRemainder := by
  unfold literalPattern at result
  rcases bind_success_components result with
    ⟨literal, afterLiteral, literalResult, finished⟩
  cases finished
  exact .parsed (coreLiteral_success_sound literalResult)

/-- Every successful Boolean binder follows the exact builtin grammar. -/
theorem booleanBinderPattern_success_sound {input next : State}
    {pattern : Pattern}
    (result : booleanBinderPattern input = .ok pattern next) :
    DeclarativeGrammar.BooleanBinderPatternParses input.declarativeRemainder
      pattern next.declarativeRemainder := by
  unfold booleanBinderPattern at result
  rcases bind_success_components result with
    ⟨name, afterName, nameResult, finished⟩
  cases finished
  exact .parsed (booleanIdentifier_success_sound nameResult)

private theorem closeParenthesizedPattern_eq_tuple_of_length_ne_one
    (openingSpan closingSpan : SourceSpan) (elements : List Pattern)
    (lengthNe : elements.length ≠ 1) :
    DeclarativeGrammar.closeParenthesizedPattern openingSpan closingSpan
      elements = {
        span := SourceSpan.cover openingSpan closingSpan
        value := .tuple {
          span := SourceSpan.cover openingSpan closingSpan
          elements
        }
      } := by
  unfold DeclarativeGrammar.closeParenthesizedPattern
  cases elements with
  | nil => rfl
  | cons head tail =>
      cases tail with
      | nil => simp at lengthNe
      | cons second rest => rfl

theorem closePatternTuple_success_sound (opening : Token)
    (elementsRev : List Pattern) {input next : State} {value : Pattern}
    (result : closePatternTuple opening elementsRev input = .ok value next) :
    ∃ closingSpan,
      value = DeclarativeGrammar.closeParenthesizedPattern opening.span
        closingSpan elementsRev.reverse ∧
      DeclarativeGrammar.ExactTokenParses (.symbol .rightParen)
        input.declarativeRemainder closingSpan next.declarativeRemainder := by
  unfold closePatternTuple at result
  rcases bind_success_components result with
    ⟨closing, afterClosing, closingResult, finished⟩
  have closingParsed := symbol_success_exactTokenParses .rightParen
    .pattern closingResult
  cases elementsRev with
  | nil =>
      cases finished
      exact ⟨closing.span, by
        simp [DeclarativeGrammar.closeParenthesizedPattern], closingParsed⟩
  | cons head tail =>
      cases tail with
      | nil =>
          cases finished
          exact ⟨closing.span, by
            simp [DeclarativeGrammar.closeParenthesizedPattern],
              closingParsed⟩
      | cons second rest =>
          cases finished
          refine ⟨closing.span, ?_, closingParsed⟩
          rw [closeParenthesizedPattern_eq_tuple_of_length_ne_one]
          simp

theorem patternTupleTail_success_sound
    (nested : Parser Pattern)
    (nestedParses : DeclarativeGrammar.Remainder → Pattern →
      DeclarativeGrammar.Remainder → Prop)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested)
    (nestedSound : ∀ {input next : State} {value : Pattern},
      next.diagnosticsRev = [] → nested input = .ok value next →
      nestedParses input.declarativeRemainder value
        next.declarativeRemainder)
    (opening : Token) : ∀ fuel elementsRev input value next,
      next.diagnosticsRev = [] →
      patternTupleTail nested opening fuel elementsRev input =
        .ok value next →
      ∃ suffix closingSpan,
        value = DeclarativeGrammar.closeParenthesizedPattern opening.span
          closingSpan (elementsRev.reverse ++ suffix) ∧
        DeclarativeGrammar.ParenthesizedPatternTupleTailParses nestedParses
          input.declarativeRemainder suffix closingSpan
            next.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro elementsRev input value next diagnosticFree result
      simp [patternTupleTail] at result
  | succ fuel inductionHypothesis =>
      intro elementsRev input value next diagnosticFree result
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
              with ⟨closingSpan, valueEq, closingParsed⟩
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
                next noProgress => contradiction
                next progressBranch =>
                  have elementProgress :
                      afterComma.cursor < afterElement.cursor :=
                    Nat.lt_of_not_ge progressBranch
                  split at result
                  next commaPresent =>
                    rcases inductionHypothesis (element :: elementsRev)
                        afterElement value next diagnosticFree result with
                      ⟨suffix, closingSpan, valueEq, tailGrammar⟩
                    have afterElementFree :=
                      patternTupleTail_reflectsDiagnosticFreeOnSuccess nested
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
                    rcases closePatternTuple_success_sound opening
                        (element :: elementsRev) result with
                      ⟨closingSpan, valueEq, closingParsed⟩
                    have afterElementFree :=
                      closePatternTuple_reflectsDiagnosticFreeOnSuccess
                        opening (element :: elementsRev) afterElement value
                          next result diagnosticFree
                    have elementGrammar := nestedSound afterElementFree
                      elementResult
                    have commaAbsent := symbolAbsentAt_of_isSymbol_eq_false
                      .comma (input := afterElement) (by simp_all)
                    refine ⟨[element], closingSpan, ?_,
                      .final comma.span closingSpan commaParsed closingAbsent
                        elementGrammar (by
                          simpa [State.declarativeRemainder] using
                            elementProgress) commaAbsent closingParsed⟩
                    simpa [List.reverse_cons, List.append_assoc] using valueEq

/-- Every diagnostic-free parenthesized success follows its exact grammar. -/
theorem parenthesizedPattern_success_sound
    (nested : Parser Pattern)
    (nestedParses : DeclarativeGrammar.Remainder → Pattern →
      DeclarativeGrammar.Remainder → Prop)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested)
    (nestedSound : ∀ {input next : State} {value : Pattern},
      next.diagnosticsRev = [] → nested input = .ok value next →
      nestedParses input.declarativeRemainder value
        next.declarativeRemainder)
    {input next : State} {value : Pattern}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : parenthesizedPattern nested input = .ok value next) :
    DeclarativeGrammar.ParenthesizedPatternParses nestedParses
      input.declarativeRemainder value next.declarativeRemainder := by
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
                rcases patternTupleTail_success_sound nested
                    nestedParses nestedReflects nestedSound opening
                      (afterFirst.remainingCount + 1) [first] afterFirst value
                        next diagnosticFree result with
                  ⟨rest, closingSpan, valueEq, tailGrammar⟩
                have afterFirstFree :=
                  patternTupleTail_reflectsDiagnosticFreeOnSuccess nested
                    nestedReflects opening (afterFirst.remainingCount + 1)
                      [first] afterFirst value next result diagnosticFree
                have firstGrammar := nestedSound afterFirstFree elementResult
                subst value
                simpa using
                  (DeclarativeGrammar.ParenthesizedPatternParses.tuple
                    opening.span closingSpan openingParsed closingAbsent
                      firstGrammar (by
                        simpa [State.declarativeRemainder] using
                          firstProgress) tailGrammar)
              next commaAbsentBranch =>
                rcases closePatternTuple_success_sound opening [first]
                    result with ⟨closingSpan, valueEq, closingParsed⟩
                have afterFirstFree :=
                  closePatternTuple_reflectsDiagnosticFreeOnSuccess opening
                    [first] afterFirst value next result diagnosticFree
                have firstGrammar := nestedSound afterFirstFree elementResult
                have commaAbsent := symbolAbsentAt_of_isSymbol_eq_false
                  .comma (input := afterFirst) (by simp_all)
                subst value
                exact .group opening.span closingSpan openingParsed
                  closingAbsent firstGrammar (by
                    simpa [State.declarativeRemainder] using firstProgress)
                      commaAbsent closingParsed

end Solcore.Syntax.Parser.PatternInternals
