import Solcore.Syntax.Parser.Expression.Atom
import Solcore.Syntax.Parser.LambdaParameterCoreTotalityProperties

/-! Totality for lambda expressions over an abstract block parser. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

private theorem lambdaParameters_invariantFreeOnValid :
    Parser.InvariantFreeOnValid
      (delimited .leftParen .rightParen true lambdaParameter
        .parameter .expression) := by
  intro input inputValid
  exact delimited_ordinary .leftParen .rightParen true lambdaParameter
    .parameter .expression lambdaParameter_elementTotalityContract input
      inputValid

/-- A lambda is ordinary whenever its supplied block parser is ordinary. -/
theorem lambdaExpression_invariantFreeOnValid (block : Parser Block)
    (blockValid : block.ValidFor (fun _ _ => True))
    (blockFree : Parser.InvariantFreeOnValid block) :
    Parser.InvariantFreeOnValid (lambdaExpression block) := by
  unfold lambdaExpression
  apply Parser.bind_invariantFreeOnValid
    (keyword_validFor .lamKw .expression)
    (keyword_ordinary .lamKw .expression).invariantFreeOnValid
  intro marker
  apply Parser.bind_invariantFreeOnValid
    ((delimited_validFor LambdaParameter.ValidFor .leftParen .rightParen true
      lambdaParameter .parameter .expression lambdaParameter_validFor
        lambdaParameter_preservesTokensOnSuccess).mono (fun _ _ _ => trivial))
    lambdaParameters_invariantFreeOnValid
  intro parameters
  apply Parser.bind_invariantFreeOnValid
    (optionalLambdaReturnType_validFor.mono (fun _ _ _ => trivial))
    optionalLambdaReturnType_invariantFreeOnValid
  intro returnType
  apply Parser.bind_invariantFreeOnValid blockValid blockFree
  intro body
  exact Parser.pure_invariantFreeOnValid ({
    span := SourceSpan.cover marker.span body.span
    value := .lambda marker.span parameters returnType body
  } : Expr)

theorem lambdaExpression_ne_invariant (block : Parser Block)
    (blockValid : block.ValidFor (fun _ _ => True))
    (blockFree : Parser.InvariantFreeOnValid block)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    lambdaExpression block input ≠ .invariant error :=
  Parser.InvariantFreeOnValid.ne_invariant
    (lambdaExpression_invariantFreeOnValid block blockValid blockFree)
      input inputValid error

/-- Package lambda syntax and totality for use by expression-atom dispatch. -/
theorem lambdaExpression_elementTotalityContract
    (block : Parser Block)
    (statementValid : SourceFile → Statement → Prop)
    (blockValid : block.ValidFor (Block.ValidFor statementValid))
    (blockWindow : Parser.PreservesTokenWindow block)
    (blockCursor : Parser.CursorMonotoneOnSuccess block)
    (blockStarts : Parser.StartsAtCurrentTokenOnSuccess block (·.span))
    (blockFree : Parser.InvariantFreeOnValid block) :
    ElementTotalityContract (lambdaExpression block) := {
  validFor := (lambdaExpression_validFor block statementValid blockValid
    blockStarts).mono (fun _ _ _ => trivial)
  preservesTokenWindow := lambdaExpression_preservesTokenWindow block
    lambdaParameter_preservesTokenWindow blockWindow
  cursorLtOnSuccess := lambdaExpression_cursor_lt_onSuccess block blockCursor
  invariantFree := (lambdaExpression_invariantFreeOnValid block
    (blockValid.mono (fun _ _ _ => trivial)) blockFree).ne_invariant
}

end Solcore.Syntax.Parser.ExpressionAtomInternals
