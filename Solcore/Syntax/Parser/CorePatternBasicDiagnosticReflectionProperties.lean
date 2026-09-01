import Solcore.Syntax.Parser.CoreLiteralSoundnessProperties
import Solcore.Syntax.Parser.DiagnosticReflectionProperties
import Solcore.Syntax.Parser.Pattern

/-!
Diagnostic reflection for basic Core pattern leaves and parenthesized
patterns.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PatternInternals

/-- Wildcard-pattern success never removes an earlier diagnostic. -/
theorem wildcardPattern_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess wildcardPattern := by
  unfold wildcardPattern
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (symbol_reflectsDiagnosticFreeOnSuccess .underscore .pattern)
  intro marker
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

/-- Literal-pattern success never removes an earlier diagnostic. -/
theorem literalPattern_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess literalPattern := by
  unfold literalPattern
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    coreLiteral_reflectsDiagnosticFreeOnSuccess
  intro literal
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

/-- Boolean-binder success never removes an earlier diagnostic. -/
theorem booleanBinderPattern_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess booleanBinderPattern := by
  unfold booleanBinderPattern
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    booleanIdentifier_reflectsDiagnosticFreeOnSuccess
  intro name
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

/-- Closing a pattern tuple never removes an earlier diagnostic. -/
theorem closePatternTuple_reflectsDiagnosticFreeOnSuccess
    (opening : Token) (elementsRev : List Pattern) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (closePatternTuple opening elementsRev) := by
  unfold closePatternTuple
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (symbol_reflectsDiagnosticFreeOnSuccess .rightParen .pattern)
  intro closing
  cases elementsRev with
  | nil => exact Parser.pure_reflectsDiagnosticFreeOnSuccess _
  | cons head tail =>
      cases tail with
      | nil => exact Parser.pure_reflectsDiagnosticFreeOnSuccess _
      | cons second rest => exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

/-- Tuple-tail success reflects through every nested pattern. -/
theorem patternTupleTail_reflectsDiagnosticFreeOnSuccess
    (nested : Parser Pattern)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested)
    (opening : Token) : ∀ fuel elementsRev,
      Parser.ReflectsDiagnosticFreeOnSuccess
        (patternTupleTail nested opening fuel elementsRev) := by
  intro fuel
  induction fuel with
  | zero =>
      intro elementsRev input value next result diagnosticFree
      simp [patternTupleTail] at result
  | succ fuel inductionHypothesis =>
      intro elementsRev input value next result diagnosticFree
      unfold patternTupleTail at result
      cases commaResult : symbol .comma .pattern input with
      | invariant error => simp [commaResult] at result
      | reject failure rejected => simp [commaResult] at result
      | ok comma afterComma =>
          simp only [commaResult] at result
          split at result
          · have afterCommaFree :=
              closePatternTuple_reflectsDiagnosticFreeOnSuccess opening
                elementsRev afterComma value next result diagnosticFree
            exact symbol_reflectsDiagnosticFreeOnSuccess .comma .pattern
              input comma afterComma commaResult afterCommaFree
          · cases elementResult : nested afterComma with
            | invariant error => simp [elementResult] at result
            | reject failure rejected => simp [elementResult] at result
            | ok element afterElement =>
                simp only [elementResult] at result
                split at result
                · contradiction
                · split at result
                  · have afterElementFree := inductionHypothesis
                        (element :: elementsRev) afterElement value next result
                          diagnosticFree
                    have afterCommaFree := nestedReflects afterComma element
                      afterElement elementResult afterElementFree
                    exact symbol_reflectsDiagnosticFreeOnSuccess .comma
                      .pattern input comma afterComma commaResult
                        afterCommaFree
                  · have afterElementFree :=
                        closePatternTuple_reflectsDiagnosticFreeOnSuccess
                          opening (element :: elementsRev) afterElement value
                            next result diagnosticFree
                    have afterCommaFree := nestedReflects afterComma element
                      afterElement elementResult afterElementFree
                    exact symbol_reflectsDiagnosticFreeOnSuccess .comma
                      .pattern input comma afterComma commaResult
                        afterCommaFree

/-- Parenthesized-pattern success reflects through its nested parser. -/
theorem parenthesizedPattern_reflectsDiagnosticFreeOnSuccess
    (nested : Parser Pattern)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested) :
    Parser.ReflectsDiagnosticFreeOnSuccess (parenthesizedPattern nested) := by
  intro input value next result diagnosticFree
  unfold parenthesizedPattern at result
  cases openingResult : symbol .leftParen .pattern input with
  | invariant error => simp [openingResult] at result
  | reject failure rejected => simp [openingResult] at result
  | ok opening afterOpening =>
      simp only [openingResult] at result
      split at result
      · have afterOpeningFree :=
          closePatternTuple_reflectsDiagnosticFreeOnSuccess opening []
            afterOpening value next result diagnosticFree
        exact symbol_reflectsDiagnosticFreeOnSuccess .leftParen .pattern
          input opening afterOpening openingResult afterOpeningFree
      · cases elementResult : nested afterOpening with
        | invariant error => simp [elementResult] at result
        | reject failure rejected => simp [elementResult] at result
        | ok first afterFirst =>
            simp only [elementResult] at result
            split at result
            · contradiction
            · split at result
              · have afterFirstFree :=
                    patternTupleTail_reflectsDiagnosticFreeOnSuccess nested
                      nestedReflects opening (afterFirst.remainingCount + 1)
                        [first] afterFirst value next result diagnosticFree
                have afterOpeningFree := nestedReflects afterOpening first
                  afterFirst elementResult afterFirstFree
                exact symbol_reflectsDiagnosticFreeOnSuccess .leftParen
                  .pattern input opening afterOpening openingResult
                    afterOpeningFree
              · have afterFirstFree :=
                    closePatternTuple_reflectsDiagnosticFreeOnSuccess opening
                      [first] afterFirst value next result diagnosticFree
                have afterOpeningFree := nestedReflects afterOpening first
                  afterFirst elementResult afterFirstFree
                exact symbol_reflectsDiagnosticFreeOnSuccess .leftParen
                  .pattern input opening afterOpening openingResult
                    afterOpeningFree

end Solcore.Syntax.Parser.PatternInternals
