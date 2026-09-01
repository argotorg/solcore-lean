import Solcore.Syntax.Parser.CoreForItemDiagnosticReflectionProperties
import Solcore.Syntax.Parser.CoreBlockSoundnessProperties
import Solcore.Syntax.Parser.Statement.Control

/-!
Backward propagation of diagnostic freedom through Core `for` item lists and
complete `for` statements.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ControlInternals

theorem forItemsTail_reflectsDiagnosticFreeOnSuccess
    (expression : Parser Expr) (stop : Symbol)
    (expressionReflects : Parser.ReflectsDiagnosticFreeOnSuccess expression) :
    ∀ fuel itemsRev,
      Parser.ReflectsDiagnosticFreeOnSuccess
        (forItemsTail expression stop fuel itemsRev) := by
  intro fuel
  induction fuel with
  | zero =>
      intro itemsRev input items next result diagnosticFree
      simp [forItemsTail] at result
  | succ fuel inductionHypothesis =>
      intro itemsRev input items next result diagnosticFree
      unfold forItemsTail at result
      by_cases commaPresent : isSymbol input .comma
      · simp only [commaPresent, if_true] at result
        cases commaResult : symbol .comma .statement input with
        | invariant error => simp [commaResult] at result
        | reject failure rejected => simp [commaResult] at result
        | ok comma afterComma =>
            simp only [commaResult] at result
            by_cases stopPresent : isSymbol afterComma stop
            · simp only [stopPresent, if_true] at result
              unfold rejectAt at result
              contradiction
            · have stopAbsent : isSymbol afterComma stop = false :=
                Bool.eq_false_iff.mpr stopPresent
              simp only [stopAbsent, Bool.false_eq_true, if_false] at result
              cases itemResult : forItem expression afterComma with
              | invariant error => simp [itemResult] at result
              | reject failure rejected => simp [itemResult] at result
              | ok item afterItem =>
                  simp only [itemResult] at result
                  by_cases progress : afterItem.cursor > afterComma.cursor
                  · simp only [progress, if_true] at result
                    have afterItemFree := inductionHypothesis
                      (item :: itemsRev) afterItem items next result
                        diagnosticFree
                    have afterCommaFree :=
                      forItem_reflectsDiagnosticFreeOnSuccess expression
                        expressionReflects afterComma item afterItem itemResult
                          afterItemFree
                    exact symbol_reflectsDiagnosticFreeOnSuccess .comma
                      .statement input comma afterComma commaResult
                        afterCommaFree
                  · simp only [progress, if_false] at result
                    contradiction
      · have commaAbsent : isSymbol input .comma = false :=
          Bool.eq_false_iff.mpr commaPresent
        simp only [commaAbsent, Bool.false_eq_true, if_false] at result
        cases result
        exact diagnosticFree

theorem forItems_reflectsDiagnosticFreeOnSuccess
    (expression : Parser Expr) (stop : Symbol)
    (expressionReflects : Parser.ReflectsDiagnosticFreeOnSuccess expression) :
    Parser.ReflectsDiagnosticFreeOnSuccess (forItems expression stop) := by
  intro input items next result diagnosticFree
  unfold forItems at result
  by_cases stopPresent : isSymbol input stop
  · simp only [stopPresent, if_true] at result
    cases result
    exact diagnosticFree
  · have stopAbsent : isSymbol input stop = false :=
      Bool.eq_false_iff.mpr stopPresent
    simp only [stopAbsent, Bool.false_eq_true, if_false] at result
    cases itemResult : forItem expression input with
    | invariant error => simp [itemResult] at result
    | reject failure rejected => simp [itemResult] at result
    | ok first afterFirst =>
        simp only [itemResult] at result
        have afterFirstFree :=
          forItemsTail_reflectsDiagnosticFreeOnSuccess expression stop
            expressionReflects (afterFirst.remainingCount + 1) [first]
              afterFirst items next result diagnosticFree
        exact forItem_reflectsDiagnosticFreeOnSuccess expression
          expressionReflects input first afterFirst itemResult afterFirstFree

end Solcore.Syntax.Parser.ControlInternals

namespace Solcore.Syntax.Parser

theorem forStatement_reflectsDiagnosticFreeOnSuccess
    (statement : Parser Statement) (expression : Parser Expr)
    (statementReflects : Parser.ReflectsDiagnosticFreeOnSuccess statement)
    (expressionReflects : Parser.ReflectsDiagnosticFreeOnSuccess expression) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (forStatement statement expression) := by
  unfold forStatement
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (keyword_reflectsDiagnosticFreeOnSuccess .forKw .statement)
  intro marker
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (symbol_reflectsDiagnosticFreeOnSuccess .leftParen .statement)
  intro opening
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (ControlInternals.forItems_reflectsDiagnosticFreeOnSuccess expression
      .semicolon expressionReflects)
  intro initializer
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (symbol_reflectsDiagnosticFreeOnSuccess .semicolon .statement)
  intro firstSemicolon
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess expressionReflects
  intro condition
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (symbol_reflectsDiagnosticFreeOnSuccess .semicolon .statement)
  intro secondSemicolon
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (ControlInternals.forItems_reflectsDiagnosticFreeOnSuccess expression
      .rightParen expressionReflects)
  intro post
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (symbol_reflectsDiagnosticFreeOnSuccess .rightParen .statement)
  intro closing
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (coreBlock_reflectsDiagnosticFreeOnSuccess statement .require
      statementReflects)
  intro body
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

end Solcore.Syntax.Parser
