import Solcore.Syntax.Parser.YulBlockOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.YulFunctionSignatureOrdinaryOutcomeSoundnessProperties

/-! Executable ordinary outcomes for complete inline-Yul functions. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem keyword_eq_ok_of_isKeyword_eq_true (value : HardKeyword)
    (context : ParseContext) {input : State}
    (present : isKeyword input value = true) :
    ∃ token, keyword value context input =
      .ok token { input with cursor := input.cursor + 1 } := by
  unfold isKeyword State.peekKind? at present
  cases found : input.peek? with
  | none => simp [found] at present
  | some token =>
      simp only [found, Option.map_some] at present
      change (token.value == .keyword value) = true at present
      refine ⟨token, ?_⟩
      unfold keyword acceptToken
      simp only [found, present, ↓reduceIte]

private theorem keyword_reject_tokenKindAbsentAt (value : HardKeyword)
    (context : ParseContext) {input rejected : State} {failure : Failure}
    (result : keyword value context input = .reject failure rejected) :
    DeclarativeGrammar.TokenKindAbsentAt input.tokens input.window.endIndex
      input.cursor (.keyword value) := by
  by_cases present : isKeyword input value = true
  · rcases keyword_eq_ok_of_isKeyword_eq_true value context present with
      ⟨token, parsed⟩
    rw [parsed] at result
    contradiction
  · exact keywordAbsentAt_of_isKeyword_eq_false value
      (Bool.eq_false_iff.mpr present)

private theorem keyword_reject_state_eq (value : HardKeyword)
    (context : ParseContext) {input rejected : State} {failure : Failure}
    (result : keyword value context input = .reject failure rejected) :
    rejected = input :=
  acceptToken_reject_state_shape (.keyword value) context
    (· == .keyword value) result

/-- Every executable function success follows the complete ordinary grammar. -/
theorem yulFunctionStatement_success_ordinary_sound
    (statement : Parser YulStmt)
    (statementOrdinary : DeclarativeGrammar.Remainder → YulStmt →
      DeclarativeGrammar.Remainder → Prop)
    (statementSuccessSound : ∀ {input output : State} {value : YulStmt},
      statement input = .ok value output →
        statementOrdinary input.declarativeRemainder value
          output.declarativeRemainder)
    {input output : State} {value : YulStmt}
    (result : yulFunctionStatement statement input = .ok value output) :
    DeclarativeGrammar.YulFunctionStatementOrdinaryParses statementOrdinary
      input.declarativeRemainder value output.declarativeRemainder := by
  unfold yulFunctionStatement at result
  cases markerResult : keyword .functionKw .yulStatement input with
  | invariant error => simp [bind, markerResult] at result
  | reject failure rejected => simp [bind, markerResult] at result
  | ok marker afterMarker =>
      simp only [bind, markerResult] at result
      cases nameResult : yulName afterMarker with
      | invariant error => simp [nameResult] at result
      | reject failure rejected => simp [nameResult] at result
      | ok name afterName =>
          simp only [nameResult] at result
          cases parametersResult : yulParameters afterName with
          | invariant error => simp [parametersResult] at result
          | reject failure rejected => simp [parametersResult] at result
          | ok parameters afterParameters =>
              simp only [parametersResult] at result
              cases returnsResult : YulControl.returns afterParameters with
              | invariant error => simp [returnsResult] at result
              | reject failure rejected => simp [returnsResult] at result
              | ok returnsValue afterReturns =>
                  simp only [returnsResult] at result
                  cases bodyResult : yulBlock statement afterReturns with
                  | invariant error => simp [bodyResult] at result
                  | reject failure rejected => simp [bodyResult] at result
                  | ok body afterBody =>
                      simp only [bodyResult, pure] at result
                      cases result
                      exact .parsed marker.span body.span
                        (keyword_success_exactTokenParses .functionKw
                          .yulStatement markerResult)
                        (yulName_success_ordinary_sound nameResult)
                        (yulParameters_success_ordinary_sound parametersResult)
                        (YulControl.returns_success_ordinary_sound
                          returnsResult)
                        (yulBlock_success_ordinary_sound statement
                          statementOrdinary statementSuccessSound bodyResult)

/-- Every executable function rejection identifies the exact first rejecting
signature or body stage and retains that rejected remainder. -/
theorem yulFunctionStatement_reject_ordinary_sound
    (statement : Parser YulStmt)
    (statementOrdinary : DeclarativeGrammar.Remainder → YulStmt →
      DeclarativeGrammar.Remainder → Prop)
    (statementRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (statementSuccessSound : ∀ {input output : State} {value : YulStmt},
      statement input = .ok value output → statementOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (statementRejectSound : ∀ {input rejected : State} {failure : Failure},
      statement input = .reject failure rejected → statementRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : yulFunctionStatement statement input = .reject failure rejected) :
    DeclarativeGrammar.YulFunctionStatementRejects statementOrdinary
      statementRejects input.declarativeRemainder
        rejected.declarativeRemainder := by
  unfold yulFunctionStatement at result
  cases markerResult : keyword .functionKw .yulStatement input with
  | invariant error => simp [bind, markerResult] at result
  | reject markerFailure markerRejected =>
      have rejectedEq := keyword_reject_state_eq .functionKw .yulStatement
        markerResult
      subst markerRejected
      simp only [bind, markerResult] at result
      cases result
      exact .markerMissing (keyword_reject_tokenKindAbsentAt .functionKw
        .yulStatement markerResult)
  | ok marker afterMarker =>
      simp only [bind, markerResult] at result
      have markerParsed := keyword_success_exactTokenParses .functionKw
        .yulStatement markerResult
      cases nameResult : yulName afterMarker with
      | invariant error => simp [nameResult] at result
      | reject nameFailure nameRejected =>
          simp only [nameResult] at result
          cases result
          exact .nameRejected marker.span markerParsed
            (yulName_reject_sound nameResult)
      | ok name afterName =>
          simp only [nameResult] at result
          have nameParsed := yulName_success_ordinary_sound nameResult
          cases parametersResult : yulParameters afterName with
          | invariant error => simp [parametersResult] at result
          | reject parametersFailure parametersRejected =>
              simp only [parametersResult] at result
              cases result
              exact .parametersRejected marker.span markerParsed nameParsed
                (yulParameters_reject_ordinary_sound parametersResult)
          | ok parameters afterParameters =>
              simp only [parametersResult] at result
              have parametersParsed :=
                yulParameters_success_ordinary_sound parametersResult
              cases returnsResult : YulControl.returns afterParameters with
              | invariant error => simp [returnsResult] at result
              | reject returnsFailure returnsRejected =>
                  simp only [returnsResult] at result
                  cases result
                  exact .returnsRejected marker.span markerParsed nameParsed
                    parametersParsed
                    (YulControl.returns_reject_ordinary_sound returnsResult)
              | ok returnsValue afterReturns =>
                  simp only [returnsResult] at result
                  have returnsParsed :=
                    YulControl.returns_success_ordinary_sound returnsResult
                  cases bodyResult : yulBlock statement afterReturns with
                  | invariant error => simp [bodyResult] at result
                  | ok body afterBody => simp [bodyResult, pure] at result
                  | reject bodyFailure bodyRejected =>
                      simp only [bodyResult] at result
                      cases result
                      exact .bodyRejected marker.span markerParsed nameParsed
                        parametersParsed returnsParsed
                        (yulBlock_reject_ordinary_sound statement
                          statementOrdinary statementRejects
                          statementSuccessSound statementRejectSound bodyResult)

end Solcore.Syntax.Parser
