import Solcore.Syntax.Parser.DiagnosticReflectionProperties
import Solcore.Syntax.Parser.Expression.Atom

/-!
Diagnostic reflection for parenthesized and array Core expression atoms.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

theorem closeTuple_reflectsDiagnosticFreeOnSuccess
    (opening : Token) (elementsRev : List Expr) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (closeTuple opening elementsRev) := by
  unfold closeTuple
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (symbol_reflectsDiagnosticFreeOnSuccess .rightParen .expression)
  intro closing
  cases elementsRev with
  | nil => exact Parser.pure_reflectsDiagnosticFreeOnSuccess _
  | cons head tail =>
      cases tail with
      | nil => exact Parser.pure_reflectsDiagnosticFreeOnSuccess _
      | cons second rest => exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

/-- Tuple-tail success reflects diagnostic freedom through every element. -/
theorem tupleTail_reflectsDiagnosticFreeOnSuccess
    (nested : Parser Expr)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested)
    (opening : Token) : ∀ fuel elementsRev,
      Parser.ReflectsDiagnosticFreeOnSuccess
        (tupleTail nested opening fuel elementsRev) := by
  intro fuel
  induction fuel with
  | zero =>
      intro elementsRev input value next result
      simp [tupleTail] at result
  | succ fuel inductionHypothesis =>
      intro elementsRev input value next result diagnosticFree
      unfold tupleTail at result
      cases commaResult : symbol .comma .expression input with
      | invariant error => simp [commaResult] at result
      | reject failure rejected => simp [commaResult] at result
      | ok comma afterComma =>
          simp only [commaResult] at result
          split at result
          · have afterCommaFree :=
              closeTuple_reflectsDiagnosticFreeOnSuccess opening elementsRev
                afterComma value next result diagnosticFree
            exact symbol_reflectsDiagnosticFreeOnSuccess .comma .expression
              input comma afterComma commaResult afterCommaFree
          · cases elementResult : nested afterComma with
            | invariant error => simp [elementResult] at result
            | reject failure rejected => simp [elementResult] at result
            | ok element afterElement =>
                simp only [elementResult] at result
                split at result
                · split at result
                  · have afterElementFree := inductionHypothesis
                        (element :: elementsRev) afterElement value next result
                          diagnosticFree
                    have afterCommaFree := nestedReflects afterComma element
                      afterElement elementResult afterElementFree
                    exact symbol_reflectsDiagnosticFreeOnSuccess .comma
                      .expression input comma afterComma commaResult
                        afterCommaFree
                  · have afterElementFree :=
                        closeTuple_reflectsDiagnosticFreeOnSuccess opening
                          (element :: elementsRev) afterElement value next
                            result diagnosticFree
                    have afterCommaFree := nestedReflects afterComma element
                      afterElement elementResult afterElementFree
                    exact symbol_reflectsDiagnosticFreeOnSuccess .comma
                      .expression input comma afterComma commaResult
                        afterCommaFree
                · contradiction

/-- Parenthesized atom success reflects through its nested parser. -/
theorem parenthesized_reflectsDiagnosticFreeOnSuccess
    (nested : Parser Expr)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested) :
    Parser.ReflectsDiagnosticFreeOnSuccess (parenthesized nested) := by
  intro input value next result diagnosticFree
  unfold parenthesized at result
  cases openingResult : symbol .leftParen .expression input with
  | invariant error => simp [openingResult] at result
  | reject failure rejected => simp [openingResult] at result
  | ok opening afterOpening =>
      simp only [openingResult] at result
      split at result
      · have afterOpeningFree :=
          closeTuple_reflectsDiagnosticFreeOnSuccess opening [] afterOpening
            value next result diagnosticFree
        exact symbol_reflectsDiagnosticFreeOnSuccess .leftParen .expression
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
                    tupleTail_reflectsDiagnosticFreeOnSuccess nested
                      nestedReflects opening (afterFirst.remainingCount + 1)
                        [first] afterFirst value next result diagnosticFree
                have afterOpeningFree := nestedReflects afterOpening first
                  afterFirst elementResult afterFirstFree
                exact symbol_reflectsDiagnosticFreeOnSuccess .leftParen
                  .expression input opening afterOpening openingResult
                    afterOpeningFree
              · have afterFirstFree :=
                    closeTuple_reflectsDiagnosticFreeOnSuccess opening [first]
                      afterFirst value next result diagnosticFree
                have afterOpeningFree := nestedReflects afterOpening first
                  afterFirst elementResult afterFirstFree
                exact symbol_reflectsDiagnosticFreeOnSuccess .leftParen
                  .expression input opening afterOpening openingResult
                    afterOpeningFree

/-- Array atom success reflects through every nested element. -/
theorem arrayLiteral_reflectsDiagnosticFreeOnSuccess
    (nested : Parser Expr)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested) :
    Parser.ReflectsDiagnosticFreeOnSuccess (arrayLiteral nested) := by
  unfold arrayLiteral
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (delimitedNoTrailing_reflectsDiagnosticFreeOnSuccess .leftBracket
      .rightBracket true nested .expression .expression nestedReflects)
  intro values
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

end Solcore.Syntax.Parser.ExpressionAtomInternals
