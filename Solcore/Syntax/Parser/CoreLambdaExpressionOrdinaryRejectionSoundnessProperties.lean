import Solcore.Syntax.Parser.CoreLambdaExpressionOrdinarySuccessSoundnessProperties
import Solcore.Syntax.Parser.CoreTypeOutcomePrimitiveProperties
import Solcore.Syntax.Parser.DelimitedListRejectionSoundnessProperties

/-! Exact guarded ordinary-rejection reflection for Core lambda expressions. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

/-- Under the atom dispatcher's positive lambda guard, every executable
rejection occurs exactly in the parameter list, optional return, or body. -/
theorem lambdaExpression_reject_ordinary_sound
    (block : Parser Block)
    (parameterOrdinary : DeclarativeGrammar.Remainder → LambdaParameter →
      DeclarativeGrammar.Remainder → Prop)
    (parameterRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (typeOrdinary : DeclarativeGrammar.Remainder → TypeExpr →
      DeclarativeGrammar.Remainder → Prop)
    (typeRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (blockRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (parameterSuccessSound :
      ∀ {input output : State} {parameter : LambdaParameter},
        lambdaParameter input = .ok parameter output →
          parameterOrdinary input.declarativeRemainder parameter
            output.declarativeRemainder)
    (parameterRejectSound :
      ∀ {input rejected : State} {failure : Failure},
        lambdaParameter input = .reject failure rejected →
          parameterRejects input.declarativeRemainder
            rejected.declarativeRemainder)
    (parameterShape : Parser.PreservesTokenWindow lambdaParameter)
    (typeSuccessSound : ∀ {input output : State} {type : TypeExpr},
      typeExpr input = .ok type output → typeOrdinary
        input.declarativeRemainder type output.declarativeRemainder)
    (typeRejectSound : ∀ {input rejected : State} {failure : Failure},
      typeExpr input = .reject failure rejected → typeRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    (blockRejectSound : ∀ {input rejected : State} {failure : Failure},
      block input = .reject failure rejected → blockRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (markerPresent : isKeyword input .lamKw = true)
    (result : lambdaExpression block input = .reject failure rejected) :
    DeclarativeGrammar.LambdaExpressionRejects parameterOrdinary
      parameterRejects typeOrdinary typeRejects blockRejects
        input.declarativeRemainder rejected.declarativeRemainder := by
  rcases keyword_eq_ok_of_isKeyword_eq_true .lamKw .expression markerPresent
    with ⟨marker, markerResult⟩
  unfold lambdaExpression at result
  simp only [bind, markerResult] at result
  cases parametersResult : delimited .leftParen .rightParen true
      lambdaParameter .parameter .expression
        { input with cursor := input.cursor + 1 } with
  | invariant error => simp [parametersResult] at result
  | reject parametersFailure parametersRejected =>
      simp only [parametersResult] at result
      cases result
      exact .parametersRejected marker.span
        (keyword_success_exactTokenParses .lamKw .expression markerResult)
        (delimited_reject_sound .leftParen .rightParen true lambdaParameter
          parameterOrdinary parameterRejects .parameter .expression
            parameterSuccessSound parameterRejectSound parametersResult)
  | ok parameters afterParameters =>
      simp only [parametersResult] at result
      have parametersParsed := delimited_allowEmpty_trailing_success_sound
        .leftParen .rightParen lambdaParameter parameterOrdinary .parameter
          .expression parameterSuccessSound parameterShape parametersResult
      cases returnResult : optionalLambdaReturnType afterParameters with
      | invariant error => simp [returnResult] at result
      | reject returnFailure returnRejected =>
          simp only [returnResult] at result
          cases result
          exact .returnTypeRejected marker.span
            (keyword_success_exactTokenParses .lamKw .expression markerResult)
            parametersParsed
            (optionalLambdaReturnType_reject_ordinary_sound typeOrdinary
              typeRejects typeRejectSound returnResult)
      | ok returnType afterReturn =>
          simp only [returnResult] at result
          have returnParsed := optionalLambdaReturnType_success_ordinary_sound
            typeOrdinary typeSuccessSound returnResult
          cases bodyResult : block afterReturn with
          | invariant error => simp [bodyResult] at result
          | ok body afterBody => simp [bodyResult, pure] at result
          | reject bodyFailure bodyRejected =>
              simp only [bodyResult] at result
              cases result
              exact .bodyRejected marker.span
                (keyword_success_exactTokenParses .lamKw .expression
                  markerResult)
                parametersParsed returnParsed (blockRejectSound bodyResult)

end Solcore.Syntax.Parser.ExpressionAtomInternals
