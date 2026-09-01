import Solcore.Syntax.DeclarativeYulStatementBasicOutcomeProperties
import Solcore.Syntax.Parser.CoreYulStatementBasicSoundnessProperties
import Solcore.Syntax.Parser.DelimitedAllowEmptySoundnessProperties
import Solcore.Syntax.Parser.DelimitedListRejectionSoundnessProperties
import Solcore.Syntax.Parser.YulExpressionPublicFuelSoundnessProperties

/-!
Unconditional executable ordinary-success and exact-rejection bridges for the
nonrecursive basic inline-Yul statement primaries.
-/

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
      simp only [found, present, if_true]

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
    rejected = input := by
  unfold keyword at result
  exact acceptToken_reject_state_shape (.keyword value) context
    (· == .keyword value) result

/-- Every executable expression-statement success follows the public ordinary
expression relation, independently of diagnostics. -/
theorem yulExpressionStatement_success_ordinary_sound
    {input output : State} {statement : YulStmt}
    (result : yulExpressionStatement input = .ok statement output) :
    DeclarativeGrammar.YulExpressionStatementOrdinaryParses
      input.declarativeRemainder statement output.declarativeRemainder := by
  unfold yulExpressionStatement at result
  cases expressionResult : yulExpression input with
  | invariant error => simp [bind, expressionResult] at result
  | reject failure rejected => simp [bind, expressionResult] at result
  | ok expression afterExpression =>
      simp only [bind, expressionResult, pure] at result
      cases result
      exact .parsed (yulExpression_success_ordinary_sound expressionResult)

/-- Every executable expression-statement rejection retains the exact public
expression rejection remainder. -/
theorem yulExpressionStatement_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : yulExpressionStatement input = .reject failure rejected) :
    DeclarativeGrammar.YulExpressionStatementRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold yulExpressionStatement at result
  cases expressionResult : yulExpression input with
  | invariant error => simp [bind, expressionResult] at result
  | ok expression afterExpression =>
      simp [bind, expressionResult, pure] at result
  | reject expressionFailure expressionRejected =>
      simp only [bind, expressionResult] at result
      cases result
      exact .expressionRejected (yulExpression_reject_sound expressionResult)

/-- Every executable source-level `return(...)` success preserves the exact
synthesized call, span, and allow-empty/trailing ordinary arguments. -/
theorem yulReturnBuiltin_success_ordinary_sound
    {input output : State} {statement : YulStmt}
    (result : yulReturnBuiltin input = .ok statement output) :
    DeclarativeGrammar.YulReturnBuiltinOrdinaryParses
      input.declarativeRemainder statement output.declarativeRemainder := by
  unfold yulReturnBuiltin at result
  cases markerResult : keyword .returnKw .yulStatement input with
  | invariant error => simp [bind, markerResult] at result
  | reject failure rejected => simp [bind, markerResult] at result
  | ok marker afterMarker =>
      simp only [bind, markerResult] at result
      cases argumentsResult : delimited .leftParen .rightParen true yulExpression
          .yulExpression .yul afterMarker with
      | invariant error => simp [argumentsResult] at result
      | reject failure rejected => simp [argumentsResult] at result
      | ok arguments afterArguments =>
          simp only [argumentsResult, pure] at result
          cases result
          exact .parsed marker.span
            (keyword_success_exactTokenParses .returnKw .yulStatement
              markerResult)
            (delimited_allowEmpty_trailing_success_sound .leftParen .rightParen
              yulExpression DeclarativeGrammar.YulExpressionOrdinaryParses
              .yulExpression .yul yulExpression_success_ordinary_sound
              yulExpression_preservesTokenWindow argumentsResult)

/-- Every executable source-level `return(...)` rejection records the exact
missing keyword or rejected allow-empty/trailing argument remainder. -/
theorem yulReturnBuiltin_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : yulReturnBuiltin input = .reject failure rejected) :
    DeclarativeGrammar.YulReturnBuiltinRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold yulReturnBuiltin at result
  cases markerResult : keyword .returnKw .yulStatement input with
  | invariant error => simp [bind, markerResult] at result
  | reject markerFailure markerRejected =>
      have markerRejectedEq := keyword_reject_state_eq .returnKw .yulStatement
        markerResult
      subst markerRejected
      simp only [bind, markerResult] at result
      cases result
      exact .markerMissing
        (keyword_reject_tokenKindAbsentAt .returnKw .yulStatement markerResult)
  | ok marker afterMarker =>
      simp only [bind, markerResult] at result
      cases argumentsResult : delimited .leftParen .rightParen true yulExpression
          .yulExpression .yul afterMarker with
      | invariant error => simp [argumentsResult] at result
      | ok arguments afterArguments =>
          simp [argumentsResult, pure] at result
      | reject argumentsFailure argumentsRejected =>
          simp only [argumentsResult] at result
          cases result
          exact .argumentsRejected marker.span
            (keyword_success_exactTokenParses .returnKw .yulStatement
              markerResult)
            (delimited_reject_sound .leftParen .rightParen true yulExpression
              DeclarativeGrammar.YulExpressionOrdinaryParses
              DeclarativeGrammar.YulExpressionRejects .yulExpression .yul
              yulExpression_success_ordinary_sound yulExpression_reject_sound
              argumentsResult)

/-- Every executable keyword-only control success is one exact ordinary token
transition. -/
theorem yulControlToken_success_ordinary_sound
    (keywordValue : HardKeyword) (statementValue : YulStmtValue)
    {input output : State} {statement : YulStmt}
    (result : yulControlToken keywordValue statementValue input =
      .ok statement output) :
    DeclarativeGrammar.YulControlTokenOrdinaryParses keywordValue statementValue
      input.declarativeRemainder statement output.declarativeRemainder :=
  yulControlToken_success_sound keywordValue statementValue result

/-- Every executable keyword-only control rejection is nonconsuming exact
evidence that its keyword is absent. -/
theorem yulControlToken_reject_ordinaryOutcome_sound
    (keywordValue : HardKeyword) (statementValue : YulStmtValue)
    {input rejected : State} {failure : Failure}
    (result : yulControlToken keywordValue statementValue input =
      .reject failure rejected) :
    DeclarativeGrammar.YulControlTokenRejects keywordValue
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold yulControlToken at result
  cases markerResult : keyword keywordValue .yulStatement input with
  | invariant error => simp [bind, markerResult] at result
  | ok marker afterMarker => simp [bind, markerResult, pure] at result
  | reject markerFailure markerRejected =>
      have markerRejectedEq := keyword_reject_state_eq keywordValue
        .yulStatement markerResult
      subst markerRejected
      simp only [bind, markerResult] at result
      cases result
      exact .keywordMissing
        (keyword_reject_tokenKindAbsentAt keywordValue .yulStatement
          markerResult)

/-- Executable expression-statement outcomes expose their declarative contract. -/
theorem yulExpressionStatement_publicOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.YulExpressionStatementOrdinaryParses
      DeclarativeGrammar.YulExpressionStatementRejects :=
  DeclarativeGrammar.yulExpressionStatementDeterministicOutcomeSpec

/-- Executable source-level return outcomes expose their declarative contract. -/
theorem yulReturnBuiltin_publicOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.YulReturnBuiltinOrdinaryParses
      DeclarativeGrammar.YulReturnBuiltinRejects :=
  DeclarativeGrammar.yulReturnBuiltinDeterministicOutcomeSpec

/-- Executable keyword-only controls expose their declarative contract. -/
theorem yulControlToken_publicOutcomeSpec
    (keywordValue : HardKeyword) (statementValue : YulStmtValue) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.YulControlTokenOrdinaryParses keywordValue
        statementValue)
      (DeclarativeGrammar.YulControlTokenRejects keywordValue) :=
  DeclarativeGrammar.yulControlTokenDeterministicOutcomeSpec keywordValue
    statementValue

end Solcore.Syntax.Parser
