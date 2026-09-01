import Solcore.Syntax.Parser.DiagnosticReflectionProperties
import Solcore.Syntax.Parser.Yul.Common

/-!
Backward propagation of diagnostic freedom through raw Yul block closing and
item iteration.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

theorem closeYulBlock_reflectsDiagnosticFreeOnSuccess
    (opening : Token) (bodyRev : List YulStmt) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (closeYulBlock opening bodyRev) := by
  intro input body next result diagnosticFree
  unfold closeYulBlock at result
  cases closingResult : symbol .rightBrace .yulStatement input with
  | invariant error => simp [closingResult] at result
  | reject failure rejected => simp [closingResult] at result
  | ok closing afterClosing =>
      simp only [closingResult] at result
      cases result
      exact symbol_reflectsDiagnosticFreeOnSuccess .rightBrace .yulStatement
        input closing next closingResult diagnosticFree

theorem yulBlockItems_reflectsDiagnosticFreeOnSuccess
    (statement : Parser YulStmt)
    (statementReflects : Parser.ReflectsDiagnosticFreeOnSuccess statement)
    (opening : Token) : ∀ fuel bodyRev,
      Parser.ReflectsDiagnosticFreeOnSuccess
        (yulBlockItems statement opening fuel bodyRev) := by
  intro fuel
  induction fuel with
  | zero =>
      intro bodyRev input body next result diagnosticFree
      simp [yulBlockItems] at result
  | succ fuel inductionHypothesis =>
      intro bodyRev input body next result diagnosticFree
      unfold yulBlockItems at result
      cases closingPresent : isSymbol input .rightBrace with
      | true =>
          simp only [closingPresent, if_true] at result
          exact closeYulBlock_reflectsDiagnosticFreeOnSuccess opening bodyRev
            input body next result diagnosticFree
      | false =>
          simp only [closingPresent, Bool.false_eq_true, if_false] at result
          cases ended : input.atEnd with
          | true =>
              simp only [ended, if_true] at result
              cases closingResult : symbol .rightBrace .yulStatement input <;>
                simp [closingResult] at result
          | false =>
              simp only [ended, Bool.false_eq_true, if_false] at result
              cases statementResult : statement input with
              | invariant error => simp [statementResult] at result
              | reject failure rejected => simp [statementResult] at result
              | ok item afterItem =>
                  simp only [statementResult] at result
                  by_cases progress : afterItem.cursor > input.cursor
                  · simp only [progress, if_true] at result
                    have afterItemFree := inductionHypothesis
                      (item :: bodyRev) afterItem body next result
                        diagnosticFree
                    exact statementReflects input item afterItem
                      statementResult afterItemFree
                  · simp only [progress, if_false] at result
                    contradiction

theorem yulBlock_reflectsDiagnosticFreeOnSuccess
    (statement : Parser YulStmt)
    (statementReflects : Parser.ReflectsDiagnosticFreeOnSuccess statement) :
    Parser.ReflectsDiagnosticFreeOnSuccess (yulBlock statement) := by
  intro input body next result diagnosticFree
  unfold yulBlock at result
  cases openingResult : symbol .leftBrace .yulStatement input with
  | invariant error => simp [openingResult] at result
  | reject failure rejected => simp [openingResult] at result
  | ok opening afterOpening =>
      simp only [openingResult] at result
      have afterOpeningFree :=
        yulBlockItems_reflectsDiagnosticFreeOnSuccess statement
          statementReflects opening (afterOpening.remainingCount + 1) []
            afterOpening body next result diagnosticFree
      exact symbol_reflectsDiagnosticFreeOnSuccess .leftBrace .yulStatement
        input opening afterOpening openingResult afterOpeningFree

end Solcore.Syntax.Parser
