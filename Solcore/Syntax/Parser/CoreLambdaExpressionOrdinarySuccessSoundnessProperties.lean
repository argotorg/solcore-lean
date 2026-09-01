import Solcore.Syntax.Parser.CoreLambdaReturnTypeOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.DelimitedAllowEmptySoundnessProperties
import Solcore.Syntax.Parser.ParameterProperties

/-! Unconditional ordinary-success reflection for Core lambda expressions. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

/-- Every executable lambda success retains its exact marker, source-order
parameters, optional return, body, outer span, AST, and final remainder. -/
theorem lambdaExpression_success_ordinary_sound
    (block : Parser Block)
    (parameterOrdinary : DeclarativeGrammar.Remainder → LambdaParameter →
      DeclarativeGrammar.Remainder → Prop)
    (typeOrdinary : DeclarativeGrammar.Remainder → TypeExpr →
      DeclarativeGrammar.Remainder → Prop)
    (blockOrdinary : DeclarativeGrammar.Remainder → Block →
      DeclarativeGrammar.Remainder → Prop)
    (parameterSuccessSound :
      ∀ {input output : State} {parameter : LambdaParameter},
        lambdaParameter input = .ok parameter output →
          parameterOrdinary input.declarativeRemainder parameter
            output.declarativeRemainder)
    (parameterShape : Parser.PreservesTokenWindow lambdaParameter)
    (typeSuccessSound : ∀ {input output : State} {type : TypeExpr},
      typeExpr input = .ok type output → typeOrdinary
        input.declarativeRemainder type output.declarativeRemainder)
    (blockSuccessSound : ∀ {input output : State} {body : Block},
      block input = .ok body output → blockOrdinary
        input.declarativeRemainder body output.declarativeRemainder)
    {input output : State} {expression : Expr}
    (result : lambdaExpression block input = .ok expression output) :
    DeclarativeGrammar.LambdaExpressionOrdinaryParses parameterOrdinary
      typeOrdinary blockOrdinary input.declarativeRemainder expression
        output.declarativeRemainder := by
  unfold lambdaExpression at result
  cases markerResult : keyword .lamKw .expression input with
  | invariant error => simp [bind, markerResult] at result
  | reject failure rejected => simp [bind, markerResult] at result
  | ok marker afterMarker =>
      simp only [bind, markerResult] at result
      cases parametersResult : delimited .leftParen .rightParen true
          lambdaParameter .parameter .expression afterMarker with
      | invariant error => simp [parametersResult] at result
      | reject failure rejected => simp [parametersResult] at result
      | ok parameters afterParameters =>
          simp only [parametersResult] at result
          cases returnResult : optionalLambdaReturnType afterParameters with
          | invariant error => simp [returnResult] at result
          | reject failure rejected => simp [returnResult] at result
          | ok returnType afterReturn =>
              simp only [returnResult] at result
              cases bodyResult : block afterReturn with
              | invariant error => simp [bodyResult] at result
              | reject failure rejected => simp [bodyResult] at result
              | ok body afterBody =>
                  simp only [bodyResult, pure] at result
                  cases result
                  exact .parsed marker.span
                    (keyword_success_exactTokenParses .lamKw .expression
                      markerResult)
                    (delimited_allowEmpty_trailing_success_sound .leftParen
                      .rightParen lambdaParameter parameterOrdinary .parameter
                        .expression parameterSuccessSound parameterShape
                          parametersResult)
                    (optionalLambdaReturnType_success_ordinary_sound
                      typeOrdinary typeSuccessSound returnResult)
                    (blockSuccessSound bodyResult)

end Solcore.Syntax.Parser.ExpressionAtomInternals
