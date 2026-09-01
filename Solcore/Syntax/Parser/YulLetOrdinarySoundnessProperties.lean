import Solcore.Syntax.DeclarativeYulLetOrdinaryOutcomeProperties
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties
import Solcore.Syntax.Parser.YulExpressionPublicFuelSoundnessProperties
import Solcore.Syntax.Parser.YulExpressionRejectionSoundnessProperties
import Solcore.Syntax.Parser.YulNamesOutcomeProperties
import Solcore.Syntax.Parser.Yul.Statement

/-!
Executable ordinary-success and exact rejection bridges for public inline-Yul
`let` declarations.
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

/-- Every executable optional-initializer success follows exact ordinary
`:=` priority, without a diagnostic-freedom premise. -/
theorem yulLetInitializer_success_ordinary_sound
    {input output : State} {initializer : Option YulExpr}
    (result : yulLetInitializer input = .ok initializer output) :
    DeclarativeGrammar.YulLetInitializerOrdinaryParses
      input.declarativeRemainder initializer output.declarativeRemainder := by
  unfold yulLetInitializer getState at result
  simp only [bind] at result
  by_cases present : isSymbol input .colonEqual
  · simp only [present, if_true] at result
    rcases symbol_eq_ok_of_isSymbol_eq_true .colonEqual .yulStatement
        present with ⟨operator, operatorResult⟩
    simp only [operatorResult] at result
    cases valueResult : yulExpression
        { input with cursor := input.cursor + 1 } with
    | invariant error => simp [valueResult] at result
    | reject failure rejected => simp [valueResult] at result
    | ok value afterValue =>
        simp only [valueResult, pure] at result
        cases result
        exact .present operator.span
          (symbol_success_exactTokenParses .colonEqual .yulStatement
            operatorResult)
          (yulExpression_success_ordinary_sound valueResult)
  · have absent : isSymbol input .colonEqual = false :=
      Bool.eq_false_iff.mpr present
    simp only [absent, Bool.false_eq_true, if_false, pure] at result
    cases result
    exact .absent
      (symbolAbsentAt_of_isSymbol_eq_false .colonEqual absent)

/-- Every executable optional-initializer rejection is exactly a present
operator followed by public expression rejection. -/
theorem yulLetInitializer_reject_sound
    {input rejected : State} {failure : Failure}
    (result : yulLetInitializer input = .reject failure rejected) :
    DeclarativeGrammar.YulLetInitializerRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold yulLetInitializer getState at result
  simp only [bind] at result
  by_cases present : isSymbol input .colonEqual
  · simp only [present, if_true] at result
    rcases symbol_eq_ok_of_isSymbol_eq_true .colonEqual .yulStatement
        present with ⟨operator, operatorResult⟩
    simp only [operatorResult] at result
    cases valueResult : yulExpression
        { input with cursor := input.cursor + 1 } with
    | invariant error => simp [valueResult] at result
    | ok value output => simp [valueResult, pure] at result
    | reject valueFailure valueRejected =>
        simp only [valueResult] at result
        cases result
        exact .expressionRejected operator.span
          (symbol_success_exactTokenParses .colonEqual .yulStatement
            operatorResult)
          (yulExpression_reject_sound valueResult)
  · have absent : isSymbol input .colonEqual = false :=
      Bool.eq_false_iff.mpr present
    simp [absent, pure] at result

/-- Every executable public `let` success follows the complete ordinary
declaration grammar. -/
theorem yulLetStatement_success_ordinary_sound
    {input output : State} {statement : YulStmt}
    (result : yulLetStatement input = .ok statement output) :
    DeclarativeGrammar.YulLetStatementOrdinaryParses
      input.declarativeRemainder statement output.declarativeRemainder := by
  unfold yulLetStatement at result
  cases markerResult : keyword .letKw .yulStatement input with
  | invariant error => simp [bind, markerResult] at result
  | reject markerFailure markerRejected =>
      simp [bind, markerResult] at result
  | ok marker afterMarker =>
      simp only [bind, markerResult] at result
      cases namesResult : yulNames afterMarker with
      | invariant error => simp [namesResult] at result
      | reject namesFailure namesRejected => simp [namesResult] at result
      | ok names afterNames =>
          simp only [namesResult] at result
          cases initializerResult : yulLetInitializer afterNames with
          | invariant error => simp [initializerResult] at result
          | reject initializerFailure initializerRejected =>
              simp [initializerResult] at result
          | ok initializer afterInitializer =>
              simp only [initializerResult, pure] at result
              cases result
              exact .parsed marker.span
                (keyword_success_exactTokenParses .letKw .yulStatement
                  markerResult)
                (yulNames_success_ordinary_sound namesResult)
                (yulLetInitializer_success_ordinary_sound initializerResult)

/-- Every executable public `let` rejection records its exact marker, names,
or present-initializer rejection stage. -/
theorem yulLetStatement_reject_sound
    {input rejected : State} {failure : Failure}
    (result : yulLetStatement input = .reject failure rejected) :
    DeclarativeGrammar.YulLetStatementRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold yulLetStatement at result
  cases markerResult : keyword .letKw .yulStatement input with
  | invariant error => simp [bind, markerResult] at result
  | reject markerFailure markerRejected =>
      have rejectedEq := keyword_reject_state_eq .letKw .yulStatement
        markerResult
      subst markerRejected
      simp only [bind, markerResult] at result
      cases result
      exact .markerRejected
        (keyword_reject_tokenKindAbsentAt .letKw .yulStatement markerResult)
  | ok marker afterMarker =>
      simp only [bind, markerResult] at result
      have markerParsed := keyword_success_exactTokenParses .letKw
        .yulStatement markerResult
      cases namesResult : yulNames afterMarker with
      | invariant error => simp [namesResult] at result
      | reject namesFailure namesRejected =>
          simp only [namesResult] at result
          cases result
          exact .namesRejected marker.span markerParsed
            (yulNames_reject_sound namesResult)
      | ok names afterNames =>
          simp only [namesResult] at result
          have namesParsed := yulNames_success_ordinary_sound namesResult
          cases initializerResult : yulLetInitializer afterNames with
          | invariant error => simp [initializerResult] at result
          | ok initializer afterInitializer =>
              simp [initializerResult, pure] at result
          | reject initializerFailure initializerRejected =>
              simp only [initializerResult] at result
              cases result
              exact .initializerRejected marker.span markerParsed namesParsed
                (yulLetInitializer_reject_sound initializerResult)

/-- Public deterministic outcome contract for optional Yul `let`
initialization. -/
theorem yulLetInitializer_publicOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.YulLetInitializerOrdinaryParses
      DeclarativeGrammar.YulLetInitializerRejects :=
  DeclarativeGrammar.yulLetInitializerDeterministicOutcomeSpec

/-- Public deterministic outcome contract for complete Yul `let`
declarations. -/
theorem yulLetStatement_publicOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.YulLetStatementOrdinaryParses
      DeclarativeGrammar.YulLetStatementRejects :=
  DeclarativeGrammar.yulLetStatementDeterministicOutcomeSpec

end Solcore.Syntax.Parser
