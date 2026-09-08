import Solcore.Syntax.Parser.ExpressionAtomNumericWindowProperties

/-! Postfix suffixes preserve only the numeric endIndex of their supplied
children. Successful and rejected replies are both framed; source, tokens,
endByte, diagnostics, cursor progress, validity, and ordinary execution are
deliberately not required by this structural layer. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace ExpressionAtomInternals

theorem postfixTail_preservesEndIndex (nested : Parser Expr) (block : Parser Block)
    (child : Parser.PreservesEndIndex nested) :
    ∀ fuel base, Parser.PreservesEndIndex (postfixTail nested block fuel base) := by
  intro fuel
  induction fuel with
  | zero => intro base input; trivial
  | succ fuel ih =>
      intro base input
      unfold postfixTail
      split
      · cases openingResult : symbol .leftBracket .expression input with
        | invariant error => trivial
        | reject failure rejected =>
            exact (symbol_preservesTokenWindow .leftBracket .expression).preservesEndIndex.endIndex_eq_of_reject openingResult
        | ok opening afterOpening =>
            have openingFrame := (symbol_preservesTokenWindow .leftBracket .expression).preservesEndIndex.endIndex_eq_of_ok openingResult
            simp only
            cases childResult : nested afterOpening with
            | invariant error => trivial
            | reject failure rejected => exact (child.endIndex_eq_of_reject childResult).trans openingFrame
            | ok index afterIndex =>
                have indexFrame := child.endIndex_eq_of_ok childResult
                simp only
                cases closingResult : symbol .rightBracket .expression afterIndex with
                | invariant error => trivial
                | reject failure rejected =>
                    exact ((symbol_preservesTokenWindow .rightBracket .expression).preservesEndIndex.endIndex_eq_of_reject closingResult).trans
                      (indexFrame.trans openingFrame)
                | ok closing afterClosing =>
                    have closingFrame := (symbol_preservesTokenWindow .rightBracket .expression).preservesEndIndex.endIndex_eq_of_ok closingResult
                    exact (ih _ afterClosing).trans (closingFrame.trans (indexFrame.trans openingFrame))
      · split
        · have argumentsFrame := delimitedWithPolicy_preservesEndIndex .leftParen .rightParen true false
            nested .expression .expression child
          cases argumentResult : delimitedNoTrailing .leftParen .rightParen true nested .expression .expression input with
          | invariant error => trivial
          | reject failure rejected => exact argumentsFrame.endIndex_eq_of_reject argumentResult
          | ok arguments afterArguments => exact (ih _ afterArguments).trans (argumentsFrame.endIndex_eq_of_ok argumentResult)
        · split
          · cases dotResult : symbol .dot .expression input with
            | invariant error => trivial
            | reject failure rejected =>
                exact (symbol_preservesTokenWindow .dot .expression).preservesEndIndex.endIndex_eq_of_reject dotResult
            | ok dot afterDot =>
                have dotFrame := (symbol_preservesTokenWindow .dot .expression).preservesEndIndex.endIndex_eq_of_ok dotResult
                simp only
                cases nameResult : identifier .expression afterDot with
                | invariant error => trivial
                | reject failure rejected =>
                    exact ((identifier_preservesTokenWindow .expression).preservesEndIndex.endIndex_eq_of_reject nameResult).trans dotFrame
                | ok name afterName =>
                    exact (ih _ afterName).trans
                      (((identifier_preservesTokenWindow .expression).preservesEndIndex.endIndex_eq_of_ok nameResult).trans dotFrame)
          · rfl

end ExpressionAtomInternals

/-- Actual production fuel is irrelevant to this numeric frame. The atom
frame is explicit here; separate child laws can construct it without a source frame. -/
theorem expressionPostfix_preservesEndIndex (nested : Parser Expr) (block : Parser Block)
    (atomFrame : Parser.PreservesEndIndex (expressionAtom nested block))
    (nestedFrame : Parser.PreservesEndIndex nested) :
    Parser.PreservesEndIndex (expressionPostfix nested block) := by
  intro input
  unfold expressionPostfix
  cases atomResult : expressionAtom nested block input with
  | invariant error => trivial
  | reject failure rejected => exact atomFrame.endIndex_eq_of_reject atomResult
  | ok base next =>
      exact (ExpressionAtomInternals.postfixTail_preservesEndIndex nested block nestedFrame
        (next.remainingCount + 1) base next).trans (atomFrame.endIndex_eq_of_ok atomResult)

end Solcore.Syntax.Parser
