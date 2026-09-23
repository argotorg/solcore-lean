import Solcore.Syntax.Parser.DelimitedNumericWindowProperties
import Solcore.Syntax.Parser.Expression.Atom

/-! Raw collection atoms retain the numeric endIndex of both ordinary
outcomes under only the same child law. Their children may change file,
tokens, byte endpoints, and diagnostics or return invariants. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

theorem closeTuple_preservesEndIndex (opening : Token) (values : List Expr) :
    Parser.PreservesEndIndex (closeTuple opening values) := by
  unfold closeTuple
  apply bind_preservesEndIndex (symbol_preservesTokenWindow .rightParen .expression).preservesEndIndex
  intro closing input
  split <;> rfl

theorem tupleTail_preservesEndIndex (nested : Parser Expr)
    (child : Parser.PreservesEndIndex nested) (opening : Token) :
    ∀ fuel values, Parser.PreservesEndIndex (tupleTail nested opening fuel values) := by
  intro fuel
  induction fuel with
  | zero => intro values input; trivial
  | succ fuel ih =>
      intro values input
      unfold tupleTail
      cases commaResult : symbol .comma .expression input with
      | invariant error => trivial
      | reject failure rejected => exact (symbol_preservesTokenWindow .comma .expression).preservesEndIndex.endIndex_eq_of_reject commaResult
      | ok comma afterComma =>
          have commaFrame := (symbol_preservesTokenWindow .comma .expression).preservesEndIndex.endIndex_eq_of_ok commaResult
          simp only
          split
          · exact (closeTuple_preservesEndIndex opening values afterComma).trans commaFrame
          · cases childResult : nested afterComma with
            | invariant error => trivial
            | reject failure rejected => exact (child.endIndex_eq_of_reject childResult).trans commaFrame
            | ok value next =>
                have childFrame := child.endIndex_eq_of_ok childResult
                simp only
                split
                · split
                  · exact (ih (value :: values) next).trans (childFrame.trans commaFrame)
                  · exact (closeTuple_preservesEndIndex opening (value :: values) next).trans (childFrame.trans commaFrame)
                · trivial

theorem parenthesized_preservesEndIndex (nested : Parser Expr)
    (child : Parser.PreservesEndIndex nested) : Parser.PreservesEndIndex (parenthesized nested) := by
  intro input
  unfold parenthesized
  cases openingResult : symbol .leftParen .expression input with
  | invariant error => trivial
  | reject failure rejected => exact (symbol_preservesTokenWindow .leftParen .expression).preservesEndIndex.endIndex_eq_of_reject openingResult
  | ok opening afterOpening =>
      have openingFrame := (symbol_preservesTokenWindow .leftParen .expression).preservesEndIndex.endIndex_eq_of_ok openingResult
      simp only
      split
      · exact (closeTuple_preservesEndIndex opening [] afterOpening).trans openingFrame
      · cases childResult : nested afterOpening with
        | invariant error => trivial
        | reject failure rejected => exact (child.endIndex_eq_of_reject childResult).trans openingFrame
        | ok first next =>
            have childFrame := child.endIndex_eq_of_ok childResult
            simp only
            split
            · trivial
            · split
              · exact (tupleTail_preservesEndIndex nested child opening
                  (next.remainingCount + 1) [first] next).trans (childFrame.trans openingFrame)
              · exact (closeTuple_preservesEndIndex opening [first] next).trans (childFrame.trans openingFrame)

theorem optionalDotConstructorArguments_preservesEndIndex (nested : Parser Expr)
    (child : Parser.PreservesEndIndex nested) :
    Parser.PreservesEndIndex (optionalDotConstructorArguments nested) := by
  intro input
  unfold optionalDotConstructorArguments
  simp only [bind, getState]
  split
  · exact bind_preservesEndIndex
      (delimitedWithPolicy_preservesEndIndex .leftParen .rightParen true false nested .expression .expression child)
      (fun _ => pure_preservesEndIndex _) input
  · rfl

theorem dotConstructor_preservesEndIndex (nested : Parser Expr)
    (child : Parser.PreservesEndIndex nested) : Parser.PreservesEndIndex (dotConstructor nested) := by
  unfold dotConstructor
  apply bind_preservesEndIndex (symbol_preservesTokenWindow .dot .expression).preservesEndIndex
  intro dot
  apply bind_preservesEndIndex expressionName_preservesTokenWindow.preservesEndIndex
  intro name
  apply bind_preservesEndIndex (optionalDotConstructorArguments_preservesEndIndex nested child)
  intro arguments
  exact pure_preservesEndIndex _

theorem arrayLiteral_preservesEndIndex (nested : Parser Expr)
    (child : Parser.PreservesEndIndex nested) : Parser.PreservesEndIndex (arrayLiteral nested) := by
  unfold arrayLiteral
  apply bind_preservesEndIndex
    (delimitedWithPolicy_preservesEndIndex .leftBracket .rightBracket true false nested .expression .expression child)
  intro values
  exact pure_preservesEndIndex _

end Solcore.Syntax.Parser.ExpressionAtomInternals
