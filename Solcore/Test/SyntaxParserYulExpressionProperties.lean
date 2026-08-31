import Solcore.Syntax.Parser.Yul.ExpressionProperties

/-! External compile consumers for inline-Yul expression-layer contracts. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @YulExpr.ValidFor
example := @optionalYulCallArguments_validFor
example := @rejectedMeta_validFor
example := @rejectedMeta_yulExpr_validFor

example : Parser.StartsAtCurrentTokenOnSuccess yulName (·.span) :=
  yulName_startsAtCurrentTokenOnSuccess

example : Parser.StartsAtCurrentTokenOnSuccess yulLiteral (·.span) :=
  yulLiteral_startsAtCurrentTokenOnSuccess

example : Parser.StartsAtCurrentTokenOnSuccess rejectedMeta (·.span) :=
  rejectedMeta_startsAtCurrentTokenOnSuccess

example (nested : Parser YulExpr)
    (valid : nested.ValidFor YulExpr.ValidFor)
    (preserves : Parser.PreservesTokensOnSuccess nested) :
    (yulExpressionCore nested).ValidFor YulExpr.ValidFor :=
  yulExpressionCore_validFor nested valid preserves

example (nested : Parser YulExpr) :
    Parser.StartsAtCurrentTokenOnSuccess
      (yulExpressionCore nested) (·.span) :=
  yulExpressionCore_startsAtCurrentTokenOnSuccess nested

example (nested : Parser YulExpr)
    (preserves : Parser.PreservesTokensOnSuccess nested) :
    Parser.PreservesTokensOnSuccess (yulExpressionCore nested) :=
  yulExpressionCore_preservesTokensOnSuccess nested preserves

example (nested : Parser YulExpr)
    (shape : Parser.PreservesTokenWindow nested) :
    Parser.PreservesTokenWindow (yulExpressionCore nested) :=
  yulExpressionCore_preservesTokenWindow nested shape

example (nested : Parser YulExpr)
    (shape : Parser.PreservesTokenWindow nested)
    {input failedState : State} {failure : Failure}
    (rejected : yulExpressionCore nested input =
      .reject failure failedState) :
    failedState.tokens = input.tokens ∧
      failedState.window = input.window :=
  yulExpressionCore_reject_preservesTokenWindow nested shape rejected

example (nested : Parser YulExpr) :
    Parser.CursorMonotoneOnSuccess (yulExpressionCore nested) :=
  yulExpressionCore_cursorMonotoneOnSuccess nested

example (nested : Parser YulExpr) {input next : State} {expression : YulExpr}
    (parsed : yulExpressionCore nested input = .ok expression next) :
    input.cursor < next.cursor :=
  yulExpressionCore_cursor_lt_onSuccess nested parsed

example := @YulExpressionInternals.finishRecovered_validFor
example := @YulExpressionInternals.recoverAux_validFor
example := @YulExpressionInternals.recoverAux_ok_state_shape

example (first last : SourceSpan) (fuel : Nat) :
    Parser.PreservesTokensOnSuccess
      (YulExpressionInternals.recoverAux first last fuel) :=
  YulExpressionInternals.recoverAux_preservesTokensOnSuccess first last fuel

example (first last : SourceSpan) (fuel : Nat) :
    Parser.CursorMonotoneOnSuccess
      (YulExpressionInternals.recoverAux first last fuel) :=
  YulExpressionInternals.recoverAux_cursorMonotoneOnSuccess first last fuel

example (nested : Parser YulExpr)
    (valid : nested.ValidFor YulExpr.ValidFor)
    (preserves : Parser.PreservesTokensOnSuccess nested)
    (rejectShape : ∀ input failure failedState,
      yulExpressionCore nested input = .reject failure failedState →
      failedState.tokens = input.tokens ∧ failedState.window = input.window) :
    (YulExpressionInternals.layer nested).ValidFor YulExpr.ValidFor :=
  YulExpressionInternals.layer_validFor nested valid preserves rejectShape

example : yulExpression.ValidFor YulExpr.ValidFor :=
  yulExpression_validFor

example : Parser.PreservesTokenWindow yulExpression :=
  yulExpression_preservesTokenWindow

example : Parser.PreservesTokensOnSuccess yulExpression :=
  yulExpression_preservesTokensOnSuccess

example : Parser.CursorMonotoneOnSuccess yulExpression :=
  yulExpression_cursorMonotoneOnSuccess

example : Parser.StartsAtCurrentTokenOnSuccess yulExpression (·.span) :=
  yulExpression_startsAtCurrentTokenOnSuccess

end Tests
