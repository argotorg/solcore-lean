import Solcore.Syntax.Parser.ExpressionCollectionNumericWindowProperties

/-! Selected raw atoms and public recovery retain the numeric token endpoint
when successful and rejected recursive children do. Reject frames are crucial:
public recovery retains the failed child's carrier and window when rewinding
the cursor. No source, token-carrier, or endByte assumption is imposed. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace ExpressionAtomInternals

theorem lambdaExpression_preservesEndIndex (block : Parser Block)
    (child : Parser.PreservesEndIndex block) : Parser.PreservesEndIndex (lambdaExpression block) := by
  unfold lambdaExpression
  apply bind_preservesEndIndex (keyword_preservesTokenWindow .lamKw .expression).preservesEndIndex
  intro marker
  apply bind_preservesEndIndex
    (delimitedWithPolicy_preservesEndIndex .leftParen .rightParen true true lambdaParameter .parameter .expression
      lambdaParameter_preservesTokenWindow.preservesEndIndex)
  intro parameters
  apply bind_preservesEndIndex optionalLambdaReturnType_preservesTokenWindow.preservesEndIndex
  intro returnType
  apply bind_preservesEndIndex child
  intro body
  exact pure_preservesEndIndex _

theorem expressionAtomCore_preservesEndIndex (nested : Parser Expr) (block : Parser Block)
    (nestedFrame : Parser.PreservesEndIndex nested) (blockFrame : Parser.PreservesEndIndex block) :
    Parser.PreservesEndIndex (expressionAtomCore nested block) := by
  intro input
  unfold expressionAtomCore
  split
  · exact literalExpression_preservesTokenWindow.preservesEndIndex input
  · split
    · exact identifierExpression_preservesTokenWindow.preservesEndIndex input
    · split
      · exact dotConstructor_preservesEndIndex nested nestedFrame input
      · split
        · exact proxyExpression_preservesTokenWindow.preservesEndIndex input
        · split
          · exact parenthesized_preservesEndIndex nested nestedFrame input
          · split
            · exact arrayLiteral_preservesEndIndex nested nestedFrame input
            · split
              · exact lambdaExpression_preservesEndIndex block blockFrame input
              · rfl

end ExpressionAtomInternals

open ExpressionAtomInternals

theorem expressionAtom_preservesEndIndex (nested : Parser Expr) (block : Parser Block)
    (nestedFrame : Parser.PreservesEndIndex nested) (blockFrame : Parser.PreservesEndIndex block) :
    Parser.PreservesEndIndex (expressionAtom nested block) := by
  intro input
  unfold expressionAtom
  cases coreResult : expressionAtomCore nested block input with
  | invariant error => trivial
  | ok value next => exact (expressionAtomCore_preservesEndIndex nested block nestedFrame blockFrame).endIndex_eq_of_ok coreResult
  | reject failure failed =>
      have coreFrame := (expressionAtomCore_preservesEndIndex nested block nestedFrame blockFrame).endIndex_eq_of_reject coreResult
      simp only
      split
      · exact coreFrame
      · exact (recoverAtom_preservesTokenWindow.preservesEndIndex _).trans coreFrame

/-- Numeric child success and rejection laws alone suffice, including when
public success is obtained by recovering from a rejected nested/body parser. -/
theorem expressionAtom_endIndex_onSuccess {nested : Parser Expr} {block : Parser Block}
    (nestedSuccess : ∀ {input output value}, nested input = .ok value output →
      output.window.endIndex = input.window.endIndex)
    (nestedReject : ∀ {input rejected failure}, nested input = .reject failure rejected →
      rejected.window.endIndex = input.window.endIndex)
    (blockSuccess : ∀ {input output value}, block input = .ok value output →
      output.window.endIndex = input.window.endIndex)
    (blockReject : ∀ {input rejected failure}, block input = .reject failure rejected →
      rejected.window.endIndex = input.window.endIndex)
    {input output : State} {value : Expr}
    (result : expressionAtom nested block input = .ok value output) :
    output.window.endIndex = input.window.endIndex :=
  (expressionAtom_preservesEndIndex nested block
    (.of_success_reject nestedSuccess nestedReject) (.of_success_reject blockSuccess blockReject)).endIndex_eq_of_ok result

theorem expressionAtom_endIndex_onReject {nested : Parser Expr} {block : Parser Block}
    (nestedSuccess : ∀ {input output value}, nested input = .ok value output →
      output.window.endIndex = input.window.endIndex)
    (nestedReject : ∀ {input rejected failure}, nested input = .reject failure rejected →
      rejected.window.endIndex = input.window.endIndex)
    (blockSuccess : ∀ {input output value}, block input = .ok value output →
      output.window.endIndex = input.window.endIndex)
    (blockReject : ∀ {input rejected failure}, block input = .reject failure rejected →
      rejected.window.endIndex = input.window.endIndex)
    {input rejected : State} {failure : Failure}
    (result : expressionAtom nested block input = .reject failure rejected) :
    rejected.window.endIndex = input.window.endIndex :=
  (expressionAtom_preservesEndIndex nested block
    (.of_success_reject nestedSuccess nestedReject) (.of_success_reject blockSuccess blockReject)).endIndex_eq_of_reject result

end Solcore.Syntax.Parser
