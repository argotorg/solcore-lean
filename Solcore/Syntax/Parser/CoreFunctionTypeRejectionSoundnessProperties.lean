import Solcore.Syntax.Parser.CoreTypeOutcomePrimitiveProperties
import Solcore.Syntax.Parser.DelimitedListRejectionSoundnessProperties
import Solcore.Syntax.Parser.TypeFunctionSoundnessProperties

/-! Exact ordinary-rejection reflection for Core function types. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Optional function returns can reject only in the delimited return-type
list after the positively guarded contextual marker. -/
theorem TypeFunctionInternals.parseFunctionReturns_reject_type_sound
    (nested : Parser TypeExpr)
    (nestedRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (nestedSuccessSound : ∀ {input next : State} {value : TypeExpr},
      nested input = .ok value next →
        DeclarativeGrammar.TypeExprParses input.declarativeRemainder value
          next.declarativeRemainder)
    (nestedRejectSound : ∀ {input rejected : State} {failure : Failure},
      nested input = .reject failure rejected →
        nestedRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : TypeFunctionInternals.parseFunctionReturns nested input =
      .reject failure rejected) :
    DeclarativeGrammar.FunctionTypeReturnsRejects nestedRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold TypeFunctionInternals.parseFunctionReturns getState at result
  simp only [bind] at result
  split at result
  next markerPresent =>
    rcases contextual_eq_ok_of_isContextual_eq_true .returns .typeExpr
        markerPresent with ⟨marker, markerResult⟩
    simp only [markerResult] at result
    cases valuesResult : delimited .leftParen .rightParen true nested
        .typeExpr .typeExpr { input with cursor := input.cursor + 1 } with
    | invariant error => simp [valuesResult] at result
    | ok values afterValues => simp [valuesResult, pure] at result
    | reject valuesFailure valuesRejected =>
        simp only [valuesResult] at result
        cases result
        exact .valuesRejected marker.span
          (contextual_success_exactTokenParses .returns .typeExpr markerResult)
          (delimited_reject_sound .leftParen .rightParen true nested
            DeclarativeGrammar.TypeExprParses nestedRejects .typeExpr .typeExpr
            nestedSuccessSound nestedRejectSound valuesResult)
  next markerAbsent =>
    simp [pure] at result

/-- A selected function-type branch rejects first in its parameter list, then
in its optional returns list after exact ordinary parameter success. -/
theorem parseFunctionType_reject_type_sound
    (nested : Parser TypeExpr)
    (nestedRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (nestedSuccessSound : ∀ {input next : State} {value : TypeExpr},
      nested input = .ok value next →
        DeclarativeGrammar.TypeExprParses input.declarativeRemainder value
          next.declarativeRemainder)
    (nestedRejectSound : ∀ {input rejected : State} {failure : Failure},
      nested input = .reject failure rejected →
        nestedRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    (nestedShape : Parser.PreservesTokenWindow nested)
    {input rejected : State} {failure : Failure}
    (keywordPresent : isKeyword input .functionKw = true)
    (result : parseFunctionType nested input = .reject failure rejected) :
    DeclarativeGrammar.FunctionTypeRejects nestedRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  rcases keyword_eq_ok_of_isKeyword_eq_true .functionKw .typeExpr
      keywordPresent with ⟨keywordToken, keywordResult⟩
  unfold parseFunctionType at result
  simp only [bind, keywordResult] at result
  cases parametersResult : delimited .leftParen .rightParen true nested
      .typeExpr .typeExpr { input with cursor := input.cursor + 1 } with
  | invariant error => simp [parametersResult] at result
  | reject parametersFailure parametersRejected =>
      simp only [parametersResult] at result
      cases result
      exact .parametersRejected keywordToken.span
        (keyword_success_exactTokenParses .functionKw .typeExpr keywordResult)
        (delimited_reject_sound .leftParen .rightParen true nested
          DeclarativeGrammar.TypeExprParses nestedRejects .typeExpr .typeExpr
          nestedSuccessSound nestedRejectSound parametersResult)
  | ok parameters afterParameters =>
      simp only [parametersResult] at result
      cases returnsResult :
          TypeFunctionInternals.parseFunctionReturns nested afterParameters with
      | invariant error => simp [returnsResult] at result
      | ok returns afterReturns => simp [returnsResult, pure] at result
      | reject returnsFailure returnsRejected =>
          simp only [returnsResult] at result
          cases result
          exact .returnsRejected keywordToken.span
            (keyword_success_exactTokenParses .functionKw .typeExpr
              keywordResult)
            (delimited_allowEmpty_trailing_success_sound .leftParen
              .rightParen nested DeclarativeGrammar.TypeExprParses .typeExpr
              .typeExpr nestedSuccessSound nestedShape parametersResult)
            (TypeFunctionInternals.parseFunctionReturns_reject_type_sound
              nested nestedRejects nestedSuccessSound nestedRejectSound
              returnsResult)

end Solcore.Syntax.Parser
