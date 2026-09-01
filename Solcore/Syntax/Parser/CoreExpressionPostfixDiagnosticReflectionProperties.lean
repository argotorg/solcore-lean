import Solcore.Syntax.Parser.DiagnosticReflectionProperties
import Solcore.Syntax.Parser.Expression.Atom

/-!
Backward propagation of diagnostic freedom through Core postfix parsing.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

/-- A successful postfix tail cannot erase an incoming diagnostic. -/
theorem postfixTail_reflectsDiagnosticFreeOnSuccess
    (nested : Parser Expr) (block : Parser Block)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested) :
    ∀ fuel base,
      Parser.ReflectsDiagnosticFreeOnSuccess
        (postfixTail nested block fuel base) := by
  intro fuel
  induction fuel with
  | zero =>
      intro base input expression next result diagnosticFree
      simp [postfixTail] at result
  | succ fuel inductionHypothesis =>
      intro base input expression next result diagnosticFree
      unfold postfixTail at result
      by_cases indexed : isSymbol input .leftBracket
      · simp only [indexed, if_true] at result
        cases openingResult : symbol .leftBracket .expression input with
        | invariant error => simp [openingResult] at result
        | reject failure rejected => simp [openingResult] at result
        | ok opening afterOpening =>
            simp only [openingResult] at result
            cases indexResult : nested afterOpening with
            | invariant error => simp [indexResult] at result
            | reject failure rejected => simp [indexResult] at result
            | ok index afterIndex =>
                simp only [indexResult] at result
                cases closingResult : symbol .rightBracket .expression
                    afterIndex with
                | invariant error => simp [closingResult] at result
                | reject failure rejected => simp [closingResult] at result
                | ok closing afterClosing =>
                    simp only [closingResult] at result
                    have afterClosingFree := inductionHypothesis {
                      span := SourceSpan.cover base.span closing.span
                      value := .index base
                        (SourceSpan.cover opening.span closing.span) index
                    } afterClosing expression next result diagnosticFree
                    have afterIndexFree :=
                      symbol_reflectsDiagnosticFreeOnSuccess .rightBracket
                        .expression afterIndex closing afterClosing
                          closingResult afterClosingFree
                    have afterOpeningFree := nestedReflects afterOpening index
                      afterIndex indexResult afterIndexFree
                    exact symbol_reflectsDiagnosticFreeOnSuccess .leftBracket
                      .expression input opening afterOpening openingResult
                        afterOpeningFree
      · simp only [indexed, Bool.false_eq_true, if_false] at result
        by_cases called : isSymbol input .leftParen
        · simp only [called, if_true] at result
          cases argumentsResult :
              delimitedNoTrailing .leftParen .rightParen true nested
                .expression .expression input with
          | invariant error => simp [argumentsResult] at result
          | reject failure rejected => simp [argumentsResult] at result
          | ok arguments afterArguments =>
              simp only [argumentsResult] at result
              have afterArgumentsFree := inductionHypothesis {
                span := SourceSpan.cover base.span arguments.span
                value := .call base arguments
              } afterArguments expression next result diagnosticFree
              exact delimitedNoTrailing_reflectsDiagnosticFreeOnSuccess
                .leftParen .rightParen true nested .expression .expression
                  nestedReflects input arguments afterArguments
                    argumentsResult afterArgumentsFree
        · simp only [called, Bool.false_eq_true, if_false] at result
          by_cases field : isSymbol input .dot
          · simp only [field, if_true] at result
            cases dotResult : symbol .dot .expression input with
            | invariant error => simp [dotResult] at result
            | reject failure rejected => simp [dotResult] at result
            | ok dot afterDot =>
                simp only [dotResult] at result
                cases nameResult : identifier .expression afterDot with
                | invariant error => simp [nameResult] at result
                | reject failure rejected => simp [nameResult] at result
                | ok name afterName =>
                    simp only [nameResult] at result
                    have afterNameFree := inductionHypothesis {
                      span := SourceSpan.cover base.span name.span
                      value := .field base dot.span name
                    } afterName expression next result diagnosticFree
                    have afterDotFree :=
                      identifier_reflectsDiagnosticFreeOnSuccess .expression
                        afterDot name afterName nameResult afterNameFree
                    exact symbol_reflectsDiagnosticFreeOnSuccess .dot
                      .expression input dot afterDot dotResult afterDotFree
          · simp only [field] at result
            cases result
            exact diagnosticFree

end Solcore.Syntax.Parser.ExpressionAtomInternals

namespace Solcore.Syntax.Parser

/-- Complete postfix parsing reflects diagnostic freedom through its atom and
all recursively parsed suffix contents. -/
theorem expressionPostfix_reflectsDiagnosticFreeOnSuccess
    (nested : Parser Expr) (block : Parser Block)
    (atomReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (expressionAtom nested block))
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (expressionPostfix nested block) := by
  intro input expression next result diagnosticFree
  unfold expressionPostfix at result
  cases atomResult : expressionAtom nested block input with
  | invariant error => simp [atomResult] at result
  | reject failure rejected => simp [atomResult] at result
  | ok base afterAtom =>
      simp only [atomResult] at result
      have afterAtomFree :=
        ExpressionAtomInternals.postfixTail_reflectsDiagnosticFreeOnSuccess
          nested block nestedReflects (afterAtom.remainingCount + 1) base
            afterAtom expression next result diagnosticFree
      exact atomReflects input base afterAtom atomResult afterAtomFree

end Solcore.Syntax.Parser
