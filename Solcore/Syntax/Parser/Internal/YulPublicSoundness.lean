import Solcore.Syntax.Internal.YulStatementOutcomes
import Solcore.Syntax.Parser.Internal.DelimitedSoundness
import Solcore.Syntax.Parser.Internal.YulAssignmentSoundness
import Solcore.Syntax.Parser.Internal.YulBlockSoundness
import Solcore.Syntax.Parser.Internal.YulStatementSoundness
import Solcore.Syntax.Parser.Internal.YulExpressionSoundness
import Solcore.Syntax.Grammar.YulOrdinary
import Solcore.Syntax.Grammar.YulFuel
import Solcore.Syntax.Parser.Internal.YulTotality
import Solcore.Syntax.Internal.SignatureOutcomes

/-!
Soundness of the parsers of Yul statements at the public boundary: each success and each
rejection has its declarative derivation, and diagnostic-free runs reflect their grammar.
-/

section
-- leanmerge: from Solcore.Syntax.Parser.YulLetOrdinarySoundnessProperties
/-!
Executable ordinary-success and exact rejection bridges for public inline-Yul
`let` declarations.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem keyword_eq_ok_of_isKeyword_eq_true_variant (value : HardKeyword)
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

private theorem keyword_reject_tokenKindAbsentAt_variant (value : HardKeyword)
    (context : ParseContext) {input rejected : State} {failure : Failure}
    (result : keyword value context input = .reject failure rejected) :
    DeclarativeGrammar.TokenKindAbsentAt input.tokens input.window.endIndex
      input.cursor (.keyword value) := by
  by_cases present : isKeyword input value = true
  · rcases keyword_eq_ok_of_isKeyword_eq_true_variant value context present with
      ⟨token, parsed⟩
    rw [parsed] at result
    contradiction
  · exact keywordAbsentAt_of_isKeyword_eq_false value
      (Bool.eq_false_iff.mpr present)

private theorem keyword_reject_state_eq_variant (value : HardKeyword)
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
      have rejectedEq := keyword_reject_state_eq_variant .letKw .yulStatement
        markerResult
      subst markerRejected
      simp only [bind, markerResult] at result
      cases result
      exact .markerRejected
        (keyword_reject_tokenKindAbsentAt_variant .letKw .yulStatement markerResult)
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
end

section
-- leanmerge: from Solcore.Syntax.Parser.YulIfStatementOrdinaryOutcomeSoundnessProperties
/-! Executable ordinary-success and rejection bridges for Yul `if`. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every executable `if` success follows the ordinary expression and block
relations without a diagnostic-freedom premise. -/
theorem yulIfStatement_success_ordinary_sound
    (statement : Parser YulStmt)
    (statementOrdinary : DeclarativeGrammar.Remainder → YulStmt →
      DeclarativeGrammar.Remainder → Prop)
    (statementSuccessSound : ∀ {input output : State} {value : YulStmt},
      statement input = .ok value output →
        statementOrdinary input.declarativeRemainder value
          output.declarativeRemainder)
    {input output : State} {value : YulStmt}
    (result : yulIfStatement statement input = .ok value output) :
    DeclarativeGrammar.YulIfStatementOrdinaryParses statementOrdinary
      input.declarativeRemainder value output.declarativeRemainder := by
  unfold yulIfStatement at result
  cases markerResult : keyword .ifKw .yulStatement input with
  | invariant error => simp [bind, markerResult] at result
  | reject failure rejected => simp [bind, markerResult] at result
  | ok marker afterMarker =>
      simp only [bind, markerResult] at result
      cases conditionResult : yulExpression afterMarker with
      | invariant error => simp [conditionResult] at result
      | reject failure rejected => simp [conditionResult] at result
      | ok condition afterCondition =>
          simp only [conditionResult] at result
          cases bodyResult : yulBlock statement afterCondition with
          | invariant error => simp [bodyResult] at result
          | reject failure rejected => simp [bodyResult] at result
          | ok body afterBody =>
              simp only [bodyResult, pure] at result
              cases result
              exact .parsed marker.span
                (keyword_success_exactTokenParses .ifKw .yulStatement
                  markerResult)
                (yulExpression_success_ordinary_sound conditionResult)
                (yulBlock_success_ordinary_sound statement statementOrdinary
                  statementSuccessSound bodyResult)

/-- Every executable `if` rejection identifies its exact sequential stage and
retains the rejected remainder reported there. -/
theorem yulIfStatement_reject_ordinary_sound
    (statement : Parser YulStmt)
    (statementOrdinary : DeclarativeGrammar.Remainder → YulStmt →
      DeclarativeGrammar.Remainder → Prop)
    (statementRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (statementSuccessSound : ∀ {input output : State} {value : YulStmt},
      statement input = .ok value output →
        statementOrdinary input.declarativeRemainder value
          output.declarativeRemainder)
    (statementRejectSound : ∀ {input rejected : State} {failure : Failure},
      statement input = .reject failure rejected →
        statementRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : yulIfStatement statement input = .reject failure rejected) :
    DeclarativeGrammar.YulIfStatementRejects statementOrdinary
      statementRejects input.declarativeRemainder
        rejected.declarativeRemainder := by
  unfold yulIfStatement at result
  cases markerResult : keyword .ifKw .yulStatement input with
  | invariant error => simp [bind, markerResult] at result
  | reject markerFailure markerRejected =>
      have rejectedEq := keyword_reject_state_eq .ifKw .yulStatement
        markerResult
      subst markerRejected
      simp only [bind, markerResult] at result
      cases result
      exact .markerMissing
        (keyword_reject_tokenKindAbsentAt .ifKw .yulStatement markerResult)
  | ok marker afterMarker =>
      simp only [bind, markerResult] at result
      cases conditionResult : yulExpression afterMarker with
      | invariant error => simp [conditionResult] at result
      | reject conditionFailure conditionRejected =>
          simp only [conditionResult] at result
          cases result
          exact .conditionRejected marker.span
            (keyword_success_exactTokenParses .ifKw .yulStatement
              markerResult)
            (yulExpression_reject_sound conditionResult)
      | ok condition afterCondition =>
          simp only [conditionResult] at result
          cases bodyResult : yulBlock statement afterCondition with
          | invariant error => simp [bodyResult] at result
          | reject bodyFailure bodyRejected =>
              simp only [bodyResult] at result
              cases result
              exact .bodyRejected marker.span
                (keyword_success_exactTokenParses .ifKw .yulStatement
                  markerResult)
                (yulExpression_success_ordinary_sound conditionResult)
                (yulBlock_reject_ordinary_sound statement statementOrdinary
                  statementRejects statementSuccessSound statementRejectSound
                  bodyResult)
          | ok body afterBody => simp [bodyResult, pure] at result

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.YulForStatementOrdinaryOutcomeSoundnessProperties
/-! Executable ordinary-success and rejection bridges for Yul `for`. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every executable `for` success follows the ordinary expression and block
relations without a diagnostic-freedom premise. -/
theorem yulForStatement_success_ordinary_sound
    (statement : Parser YulStmt)
    (statementOrdinary : DeclarativeGrammar.Remainder → YulStmt →
      DeclarativeGrammar.Remainder → Prop)
    (statementSuccessSound : ∀ {input output : State} {value : YulStmt},
      statement input = .ok value output →
        statementOrdinary input.declarativeRemainder value
          output.declarativeRemainder)
    {input output : State} {value : YulStmt}
    (result : yulForStatement statement input = .ok value output) :
    DeclarativeGrammar.YulForStatementOrdinaryParses statementOrdinary
      input.declarativeRemainder value output.declarativeRemainder := by
  unfold yulForStatement at result
  cases markerResult : keyword .forKw .yulStatement input with
  | invariant error => simp [bind, markerResult] at result
  | reject failure rejected => simp [bind, markerResult] at result
  | ok marker afterMarker =>
      simp only [bind, markerResult] at result
      cases initializerResult : yulBlock statement afterMarker with
      | invariant error => simp [initializerResult] at result
      | reject failure rejected => simp [initializerResult] at result
      | ok initializer afterInitializer =>
          simp only [initializerResult] at result
          cases conditionResult : yulExpression afterInitializer with
          | invariant error => simp [conditionResult] at result
          | reject failure rejected => simp [conditionResult] at result
          | ok condition afterCondition =>
              simp only [conditionResult] at result
              cases postResult : yulBlock statement afterCondition with
              | invariant error => simp [postResult] at result
              | reject failure rejected => simp [postResult] at result
              | ok post afterPost =>
                  simp only [postResult] at result
                  cases bodyResult : yulBlock statement afterPost with
                  | invariant error => simp [bodyResult] at result
                  | reject failure rejected => simp [bodyResult] at result
                  | ok body afterBody =>
                      simp only [bodyResult, pure] at result
                      cases result
                      exact .parsed marker.span
                        (keyword_success_exactTokenParses .forKw .yulStatement
                          markerResult)
                        (yulBlock_success_ordinary_sound statement
                          statementOrdinary statementSuccessSound
                          initializerResult)
                        (yulExpression_success_ordinary_sound conditionResult)
                        (yulBlock_success_ordinary_sound statement
                          statementOrdinary statementSuccessSound postResult)
                        (yulBlock_success_ordinary_sound statement
                          statementOrdinary statementSuccessSound bodyResult)

/-- Every executable `for` rejection identifies its exact sequential stage and
retains the rejected remainder reported there. -/
theorem yulForStatement_reject_ordinary_sound
    (statement : Parser YulStmt)
    (statementOrdinary : DeclarativeGrammar.Remainder → YulStmt →
      DeclarativeGrammar.Remainder → Prop)
    (statementRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (statementSuccessSound : ∀ {input output : State} {value : YulStmt},
      statement input = .ok value output →
        statementOrdinary input.declarativeRemainder value
          output.declarativeRemainder)
    (statementRejectSound : ∀ {input rejected : State} {failure : Failure},
      statement input = .reject failure rejected →
        statementRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : yulForStatement statement input = .reject failure rejected) :
    DeclarativeGrammar.YulForStatementRejects statementOrdinary
      statementRejects input.declarativeRemainder
        rejected.declarativeRemainder := by
  unfold yulForStatement at result
  cases markerResult : keyword .forKw .yulStatement input with
  | invariant error => simp [bind, markerResult] at result
  | reject markerFailure markerRejected =>
      have rejectedEq := keyword_reject_state_eq .forKw .yulStatement
        markerResult
      subst markerRejected
      simp only [bind, markerResult] at result
      cases result
      exact .markerMissing
        (keyword_reject_tokenKindAbsentAt .forKw .yulStatement markerResult)
  | ok marker afterMarker =>
      simp only [bind, markerResult] at result
      cases initializerResult : yulBlock statement afterMarker with
      | invariant error => simp [initializerResult] at result
      | reject initializerFailure initializerRejected =>
          simp only [initializerResult] at result
          cases result
          exact .initializerRejected marker.span
            (keyword_success_exactTokenParses .forKw .yulStatement
              markerResult)
            (yulBlock_reject_ordinary_sound statement statementOrdinary
              statementRejects statementSuccessSound statementRejectSound
              initializerResult)
      | ok initializer afterInitializer =>
          simp only [initializerResult] at result
          cases conditionResult : yulExpression afterInitializer with
          | invariant error => simp [conditionResult] at result
          | reject conditionFailure conditionRejected =>
              simp only [conditionResult] at result
              cases result
              exact .conditionRejected marker.span
                (keyword_success_exactTokenParses .forKw .yulStatement
                  markerResult)
                (yulBlock_success_ordinary_sound statement statementOrdinary
                  statementSuccessSound initializerResult)
                (yulExpression_reject_sound conditionResult)
          | ok condition afterCondition =>
              simp only [conditionResult] at result
              cases postResult : yulBlock statement afterCondition with
              | invariant error => simp [postResult] at result
              | reject postFailure postRejected =>
                  simp only [postResult] at result
                  cases result
                  exact .postRejected marker.span
                    (keyword_success_exactTokenParses .forKw .yulStatement
                      markerResult)
                    (yulBlock_success_ordinary_sound statement
                      statementOrdinary statementSuccessSound
                      initializerResult)
                    (yulExpression_success_ordinary_sound conditionResult)
                    (yulBlock_reject_ordinary_sound statement
                      statementOrdinary statementRejects statementSuccessSound
                      statementRejectSound postResult)
              | ok post afterPost =>
                  simp only [postResult] at result
                  cases bodyResult : yulBlock statement afterPost with
                  | invariant error => simp [bodyResult] at result
                  | reject bodyFailure bodyRejected =>
                      simp only [bodyResult] at result
                      cases result
                      exact .bodyRejected marker.span
                        (keyword_success_exactTokenParses .forKw .yulStatement
                          markerResult)
                        (yulBlock_success_ordinary_sound statement
                          statementOrdinary statementSuccessSound
                          initializerResult)
                        (yulExpression_success_ordinary_sound conditionResult)
                        (yulBlock_success_ordinary_sound statement
                          statementOrdinary statementSuccessSound postResult)
                        (yulBlock_reject_ordinary_sound statement
                          statementOrdinary statementRejects
                          statementSuccessSound statementRejectSound
                          bodyResult)
                  | ok body afterBody => simp [bodyResult, pure] at result

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.YulFunctionSignatureOrdinaryOutcomeSoundnessProperties
/-! Executable ordinary outcomes for inline-Yul function signatures. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Successful parameters retain ordinary diagnosed names and exact order. -/
theorem yulParameters_success_ordinary_sound {input output : State}
    {parameters : DelimitedList YulIdentifier}
    (result : yulParameters input = .ok parameters output) :
    DeclarativeGrammar.YulParametersOrdinaryParses
      input.declarativeRemainder parameters output.declarativeRemainder := by
  unfold yulParameters at result
  unfold DeclarativeGrammar.YulParametersOrdinaryParses
  exact delimited_allowEmpty_trailing_success_sound .leftParen .rightParen
    yulName DeclarativeGrammar.YulNameOrdinaryParses .yulStatement .yul
    yulName_success_ordinary_sound yulName_preservesTokenWindow result

/-- Rejected parameters retain the exact nested or delimiter remainder. -/
theorem yulParameters_reject_ordinary_sound
    {input rejected : State} {failure : Failure}
    (result : yulParameters input = .reject failure rejected) :
    DeclarativeGrammar.YulParametersRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold yulParameters at result
  exact delimited_reject_sound .leftParen .rightParen true yulName
    DeclarativeGrammar.YulNameOrdinaryParses
    DeclarativeGrammar.YulNameRejects .yulStatement .yul
    yulName_success_ordinary_sound yulName_reject_sound result

namespace YulControl

/-- Successful return clauses retain arrow, names, span, order, and output. -/
theorem returnClause_success_ordinary_sound {input output : State}
    {clause : YulReturnClause}
    (result : returnClause input = .ok clause output) :
    DeclarativeGrammar.YulReturnClauseOrdinaryParses
      input.declarativeRemainder clause output.declarativeRemainder := by
  unfold returnClause at result
  cases arrowResult : symbol .arrow .yulStatement input with
  | invariant error => simp [bind, arrowResult] at result
  | reject failure rejected => simp [bind, arrowResult] at result
  | ok arrow afterArrow =>
      simp only [bind, arrowResult] at result
      cases namesResult : yulNames afterArrow with
      | invariant error => simp [namesResult] at result
      | reject failure rejected => simp [namesResult] at result
      | ok names afterNames =>
          simp only [namesResult, pure] at result
          cases result
          exact .parsed arrow.span
            (symbol_success_exactTokenParses .arrow .yulStatement arrowResult)
            (yulNames_success_ordinary_sound namesResult)

/-- Rejected return clauses record arrow absence or rejected names. -/
theorem returnClause_reject_ordinary_sound
    {input rejected : State} {failure : Failure}
    (result : returnClause input = .reject failure rejected) :
    DeclarativeGrammar.YulReturnClauseRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold returnClause at result
  cases arrowResult : symbol .arrow .yulStatement input with
  | invariant error => simp [bind, arrowResult] at result
  | reject arrowFailure arrowRejected =>
      have rejectedEq := symbol_reject_state_eq .arrow .yulStatement
        arrowResult
      subst arrowRejected
      simp only [bind, arrowResult] at result
      cases result
      exact .arrowMissing
        (symbol_reject_tokenKindAbsentAt .arrow .yulStatement arrowResult)
  | ok arrow afterArrow =>
      simp only [bind, arrowResult] at result
      cases namesResult : yulNames afterArrow with
      | invariant error => simp [namesResult] at result
      | ok names afterNames => simp [namesResult, pure] at result
      | reject namesFailure namesRejected =>
          simp only [namesResult] at result
          cases result
          exact .namesRejected arrow.span
            (symbol_success_exactTokenParses .arrow .yulStatement arrowResult)
            (yulNames_reject_sound namesResult)

/-- Successful optional returns follow exact arrow priority. -/
theorem returns_success_ordinary_sound {input output : State}
    {returnsValue : Option YulReturnClause}
    (result : returns input = .ok returnsValue output) :
    DeclarativeGrammar.YulReturnsOrdinaryParses input.declarativeRemainder
      returnsValue output.declarativeRemainder := by
  unfold returns getState at result
  simp only [bind] at result
  by_cases present : isSymbol input .arrow
  · simp only [present, if_true] at result
    cases clauseResult : returnClause input with
    | invariant error => simp [clauseResult] at result
    | reject failure rejected => simp [clauseResult] at result
    | ok clause afterClause =>
        simp only [clauseResult, pure] at result
        cases result
        exact .present (returnClause_success_ordinary_sound clauseResult)
  · have absent : isSymbol input .arrow = false :=
      Bool.eq_false_iff.mpr present
    simp only [absent, Bool.false_eq_true, if_false, pure] at result
    cases result
    exact .absent (symbolAbsentAt_of_isSymbol_eq_false .arrow absent)

/-- Optional returns reject only in the preferred arrow branch's names. -/
theorem returns_reject_ordinary_sound
    {input rejected : State} {failure : Failure}
    (result : returns input = .reject failure rejected) :
    DeclarativeGrammar.YulReturnsRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold returns getState at result
  simp only [bind] at result
  by_cases present : isSymbol input .arrow
  · simp only [present, if_true] at result
    rcases symbol_eq_ok_of_isSymbol_eq_true .arrow .yulStatement present with
      ⟨arrow, arrowResult⟩
    unfold returnClause at result
    simp only [bind, arrowResult] at result
    cases namesResult : yulNames { input with cursor := input.cursor + 1 } with
    | invariant error => simp [namesResult] at result
    | ok names afterNames => simp [namesResult, pure] at result
    | reject namesFailure namesRejected =>
        simp only [namesResult] at result
        cases result
        exact .namesRejected arrow.span
          (symbol_success_exactTokenParses .arrow .yulStatement arrowResult)
          (yulNames_reject_sound namesResult)
  · have absent : isSymbol input .arrow = false :=
      Bool.eq_false_iff.mpr present
    simp [absent, pure] at result

end YulControl

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.YulFunctionOrdinaryOutcomeSoundnessProperties
/-! Executable ordinary outcomes for complete inline-Yul functions. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

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
      have rejectedEq := keyword_reject_state_eq_variant .functionKw .yulStatement
        markerResult
      subst markerRejected
      simp only [bind, markerResult] at result
      cases result
      exact .markerMissing (keyword_reject_tokenKindAbsentAt_variant .functionKw
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
end

section
-- leanmerge: from Solcore.Syntax.Parser.YulSwitchCaseArmOrdinaryOutcomeSoundnessProperties
/-! Executable ordinary-success and rejection bridges for one Yul case arm. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.YulControl

private theorem rejectAt_rejected_state_eq {alpha : Type}
    {input rejected : State} {failure : Failure}
    {expected : NonemptyList ParseExpectation} {context : ParseContext}
    (result : (rejectAt input expected context : Reply alpha) =
      .reject failure rejected) : rejected = input := by
  unfold rejectAt at result
  cases result
  rfl

private theorem yulLiteral_ne_reject_of_startsYulLiteral
    {input rejected : State} {failure : Failure}
    (starts : startsYulLiteral input = true)
    (result : yulLiteral input = .reject failure rejected) : False := by
  unfold startsYulLiteral State.peekKind? at starts
  unfold yulLiteral at result
  cases found : input.peek? with
  | none => simp [found] at starts
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found, Option.map_some] at starts result
      all_goals try { contradiction }
      case keyword keyword =>
        cases keyword <;> simp only at starts result
        all_goals try { unfold rejectAt at result; contradiction }
        all_goals contradiction

private theorem yulLiteral_reject_state_eq
    {input rejected : State} {failure : Failure}
    (result : yulLiteral input = .reject failure rejected) :
    rejected = input := by
  unfold yulLiteral at result
  cases found : input.peek? with
  | none =>
      simp only [found] at result
      exact rejectAt_rejected_state_eq result
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found] at result
      all_goals try { exact rejectAt_rejected_state_eq result }
      all_goals try { contradiction }
      case keyword keyword =>
        cases keyword <;> simp only at result
        all_goals try { exact rejectAt_rejected_state_eq result }
        all_goals contradiction

private theorem bind_ok_components {alpha beta : Type}
    {first : Parser alpha} {next : alpha → Parser beta}
    {input final : State} {value : beta}
    (parsed : (first >>= next) input = .ok value final) :
    ∃ firstValue afterFirst,
      first input = .ok firstValue afterFirst ∧
        next firstValue afterFirst = .ok value final := by
  change (match first input with
    | .ok firstValue afterFirst => next firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value final at parsed
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      rw [firstResult] at parsed
      exact ⟨firstValue, afterFirst, rfl, parsed⟩
  | reject failure rejected => rw [firstResult] at parsed; contradiction
  | invariant error => rw [firstResult] at parsed; contradiction

/-- Every executable case-arm success follows the ordinary recursive block
relation, independently of diagnostics. -/
theorem caseArm_success_ordinary_sound
    (statement : Parser YulStmt)
    (statementOrdinary : DeclarativeGrammar.Remainder → YulStmt →
      DeclarativeGrammar.Remainder → Prop)
    (statementSuccessSound : ∀ {input output : State} {value : YulStmt},
      statement input = .ok value output →
        statementOrdinary input.declarativeRemainder value
          output.declarativeRemainder)
    {input output : State} {arm : YulCase}
    (result : caseArm statement input = .ok arm output) :
    DeclarativeGrammar.YulCaseArmOrdinaryParses statementOrdinary
      input.declarativeRemainder arm output.declarativeRemainder := by
  unfold caseArm at result
  rcases bind_ok_components result with
    ⟨marker, afterMarker, markerResult, literalStage⟩
  rcases bind_ok_components literalStage with
    ⟨literal, afterLiteral, literalResult, bodyStage⟩
  rcases bind_ok_components bodyStage with
    ⟨body, afterBody, bodyResult, finished⟩
  cases finished
  exact .parsed marker.span body.span
    (keyword_success_exactTokenParses .caseKw .yulStatement markerResult)
    (yulLiteral_success_sound literalResult)
    (yulBlock_success_ordinary_sound statement statementOrdinary
      statementSuccessSound bodyResult)

/-- Every executable case-arm rejection identifies its exact sequential
stage and rejected remainder. -/
theorem caseArm_reject_ordinary_sound
    (statement : Parser YulStmt)
    (statementOrdinary : DeclarativeGrammar.Remainder → YulStmt →
      DeclarativeGrammar.Remainder → Prop)
    (statementRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (statementSuccessSound : ∀ {input output : State} {value : YulStmt},
      statement input = .ok value output →
        statementOrdinary input.declarativeRemainder value
          output.declarativeRemainder)
    (statementRejectSound : ∀ {input rejected : State} {failure : Failure},
      statement input = .reject failure rejected →
        statementRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : caseArm statement input = .reject failure rejected) :
    DeclarativeGrammar.YulCaseArmRejects statementOrdinary statementRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold caseArm at result
  cases markerResult : keyword .caseKw .yulStatement input with
  | invariant error => simp [bind, markerResult] at result
  | reject markerFailure markerRejected =>
      have rejectedEq := keyword_reject_state_eq .caseKw .yulStatement
        markerResult
      subst markerRejected
      simp only [bind, markerResult] at result
      cases result
      exact .markerMissing
        (keyword_reject_tokenKindAbsentAt .caseKw .yulStatement markerResult)
  | ok marker afterMarker =>
      simp only [bind, markerResult] at result
      cases literalResult : yulLiteral afterMarker with
      | invariant error => simp [literalResult] at result
      | reject literalFailure literalRejected =>
          have rejectedEq := yulLiteral_reject_state_eq literalResult
          subst literalRejected
          simp only [literalResult] at result
          cases result
          exact .literalMissing marker.span
            (keyword_success_exactTokenParses .caseKw .yulStatement
              markerResult)
            (fun starts => yulLiteral_ne_reject_of_startsYulLiteral
              (startsYulLiteral_eq_true_of_yulLiteralStartsAt starts)
              literalResult)
      | ok literal afterLiteral =>
          simp only [literalResult] at result
          cases bodyResult : yulBlock statement afterLiteral with
          | invariant error => simp [bodyResult] at result
          | reject bodyFailure bodyRejected =>
              simp only [bodyResult] at result
              cases result
              exact .bodyRejected marker.span
                (keyword_success_exactTokenParses .caseKw .yulStatement
                  markerResult)
                (yulLiteral_success_sound literalResult)
                (yulBlock_reject_ordinary_sound statement statementOrdinary
                  statementRejects statementSuccessSound statementRejectSound
                  bodyResult)
          | ok body afterBody => simp [bodyResult, pure] at result

end Solcore.Syntax.Parser.YulControl
end

section
-- leanmerge: from Solcore.Syntax.Parser.YulSwitchDefaultOrdinaryOutcomeSoundnessProperties
/-!
Executable ordinary-success and rejection bridges for the prioritized
optional `default` arm of a Yul switch.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.YulControl

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

/-- Every optional-default success retains exact keyword priority and its
ordinary recursive block. -/
theorem optionalDefault_success_ordinary_sound
    (statement : Parser YulStmt)
    (statementOrdinary : DeclarativeGrammar.Remainder → YulStmt →
      DeclarativeGrammar.Remainder → Prop)
    (statementSuccessSound : ∀ {input output : State} {value : YulStmt},
      statement input = .ok value output →
        statementOrdinary input.declarativeRemainder value
          output.declarativeRemainder)
    {input output : State} {defaultBody : Option YulParsedBlock}
    (result : optionalDefault statement input = .ok defaultBody output) :
    DeclarativeGrammar.OptionalYulDefaultOrdinaryParses statementOrdinary
      input.declarativeRemainder (defaultBody.map (fun body => body.span))
        (defaultBody.map (fun body => body.body))
          output.declarativeRemainder := by
  unfold optionalDefault getState at result
  simp only [bind] at result
  by_cases present : isKeyword input .defaultKw
  · simp only [present, if_true] at result
    cases markerResult : keyword .defaultKw .yulStatement input with
    | invariant error => simp [markerResult] at result
    | reject failure rejected =>
        rcases keyword_eq_ok_of_isKeyword_eq_true .defaultKw .yulStatement
            present with ⟨marker, successfulMarker⟩
        rw [successfulMarker] at markerResult
        contradiction
    | ok marker afterMarker =>
        simp only [markerResult] at result
        cases bodyResult : yulBlock statement afterMarker with
        | invariant error => simp [bodyResult] at result
        | reject failure rejected => simp [bodyResult] at result
        | ok body afterBody =>
            simp only [bodyResult, pure] at result
            cases result
            exact .present marker.span body.span
              (keyword_success_exactTokenParses .defaultKw .yulStatement
                markerResult)
              (yulBlock_success_ordinary_sound statement statementOrdinary
                statementSuccessSound bodyResult)
  · have absent : isKeyword input .defaultKw = false :=
      Bool.eq_false_iff.mpr present
    simp only [absent, Bool.false_eq_true, if_false, pure] at result
    cases result
    exact .absent
      (keywordAbsentAt_of_isKeyword_eq_false .defaultKw absent)

/-- The guarded optional default rejects exactly when its braced body
rejects, retaining that body's rejected remainder. -/
theorem optionalDefault_reject_ordinary_sound
    (statement : Parser YulStmt)
    (statementOrdinary : DeclarativeGrammar.Remainder → YulStmt →
      DeclarativeGrammar.Remainder → Prop)
    (statementRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (statementSuccessSound : ∀ {input output : State} {value : YulStmt},
      statement input = .ok value output →
        statementOrdinary input.declarativeRemainder value
          output.declarativeRemainder)
    (statementRejectSound : ∀ {input rejected : State} {failure : Failure},
      statement input = .reject failure rejected →
        statementRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : optionalDefault statement input = .reject failure rejected) :
    DeclarativeGrammar.OptionalYulDefaultRejects statementOrdinary
      statementRejects input.declarativeRemainder
        rejected.declarativeRemainder := by
  unfold optionalDefault getState at result
  simp only [bind] at result
  by_cases present : isKeyword input .defaultKw
  · simp only [present, if_true] at result
    cases markerResult : keyword .defaultKw .yulStatement input with
    | invariant error => simp [markerResult] at result
    | reject markerFailure markerRejected =>
        rcases keyword_eq_ok_of_isKeyword_eq_true .defaultKw .yulStatement
            present with ⟨marker, successfulMarker⟩
        rw [successfulMarker] at markerResult
        contradiction
    | ok marker afterMarker =>
        simp only [markerResult] at result
        cases bodyResult : yulBlock statement afterMarker with
        | invariant error => simp [bodyResult] at result
        | reject bodyFailure bodyRejected =>
            simp only [bodyResult] at result
            cases result
            exact .bodyRejected marker.span
              (keyword_success_exactTokenParses .defaultKw .yulStatement
                markerResult)
              (yulBlock_reject_ordinary_sound statement statementOrdinary
                statementRejects statementSuccessSound statementRejectSound
                bodyResult)
        | ok body afterBody => simp [bodyResult, pure] at result
  · have absent : isKeyword input .defaultKw = false :=
      Bool.eq_false_iff.mpr present
    simp [absent, pure] at result

end Solcore.Syntax.Parser.YulControl
end

section
-- leanmerge: from Solcore.Syntax.Parser.YulSwitchCaseListOrdinaryOutcomeSoundnessProperties
/-!
Executable ordinary-success and rejection bridges for the fuel-bounded,
reverse-accumulating Yul switch case loop.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.YulControl

private theorem keywordPresentAt_of_isKeyword_eq_true (value : HardKeyword)
    {input : State} (present : isKeyword input value = true) :
    ∃ span, DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
      input.cursor { span, value := .keyword value } := by
  rcases keyword_eq_ok_of_isKeyword_eq_true value .yulStatement present with
    ⟨token, result⟩
  have parsed := keyword_success_exactTokenParses value .yulStatement result
  exact ⟨token.span, parsed.1⟩

/-- The executable reverse accumulator is the prefix of the returned cases;
the ordinary relation describes the remaining forward maximal suffix. -/
theorem caseList_success_ordinary_sound
    (statement : Parser YulStmt)
    (statementOrdinary : DeclarativeGrammar.Remainder → YulStmt →
      DeclarativeGrammar.Remainder → Prop)
    (statementSuccessSound : ∀ {input output : State} {value : YulStmt},
      statement input = .ok value output →
        statementOrdinary input.declarativeRemainder value
          output.declarativeRemainder) :
    ∀ fuel casesRev input cases output,
      caseList statement fuel casesRev input = .ok cases output →
      ∃ suffix,
        cases = casesRev.reverse ++ suffix ∧
        DeclarativeGrammar.YulCaseListOrdinaryParses statementOrdinary
          input.declarativeRemainder suffix output.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro casesRev input cases output result
      simp [caseList] at result
  | succ fuel inductionHypothesis =>
      intro casesRev input cases output result
      unfold caseList at result
      cases casePresent : isKeyword input .caseKw with
      | false =>
          simp only [casePresent, Bool.false_eq_true, if_false] at result
          cases result
          exact ⟨[], by simp,
            .done (keywordAbsentAt_of_isKeyword_eq_false .caseKw
              casePresent)⟩
      | true =>
          simp only [casePresent, if_true] at result
          cases armResult : caseArm statement input with
          | invariant error => simp [armResult] at result
          | reject failure rejected => simp [armResult] at result
          | ok arm afterArm =>
              simp only [armResult] at result
              by_cases progress : afterArm.cursor > input.cursor
              · simp only [progress, if_true] at result
                rcases inductionHypothesis (arm :: casesRev) afterArm cases
                    output result with ⟨suffix, casesEq, tailGrammar⟩
                refine ⟨arm :: suffix, ?_,
                  .next
                    (caseArm_success_ordinary_sound statement
                      statementOrdinary statementSuccessSound armResult)
                    (by simpa [State.declarativeRemainder] using progress)
                    tailGrammar⟩
                simpa [List.reverse_cons, List.append_assoc] using casesEq
              · simp only [progress, if_false] at result
                contradiction

/-- Every executable case-list rejection records the first rejected arm
after its exact ordinary prefix. -/
theorem caseList_reject_ordinary_sound
    (statement : Parser YulStmt)
    (statementOrdinary : DeclarativeGrammar.Remainder → YulStmt →
      DeclarativeGrammar.Remainder → Prop)
    (statementRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (statementSuccessSound : ∀ {input output : State} {value : YulStmt},
      statement input = .ok value output →
        statementOrdinary input.declarativeRemainder value
          output.declarativeRemainder)
    (statementRejectSound : ∀ {input rejected : State} {failure : Failure},
      statement input = .reject failure rejected →
        statementRejects input.declarativeRemainder
          rejected.declarativeRemainder) :
    ∀ fuel casesRev input failure rejected,
      caseList statement fuel casesRev input = .reject failure rejected →
      DeclarativeGrammar.YulCaseListRejects statementOrdinary
        statementRejects input.declarativeRemainder
          rejected.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro casesRev input failure rejected result
      simp [caseList] at result
  | succ fuel inductionHypothesis =>
      intro casesRev input failure rejected result
      unfold caseList at result
      cases casePresent : isKeyword input .caseKw with
      | false =>
          simp [casePresent] at result
      | true =>
          simp only [casePresent, if_true] at result
          cases armResult : caseArm statement input with
          | invariant error => simp [armResult] at result
          | reject armFailure armRejected =>
              simp only [armResult] at result
              cases result
              exact .firstRejected
                (keywordPresentAt_of_isKeyword_eq_true .caseKw casePresent)
                (caseArm_reject_ordinary_sound statement statementOrdinary
                  statementRejects statementSuccessSound statementRejectSound
                  armResult)
          | ok arm afterArm =>
              simp only [armResult] at result
              by_cases progress : afterArm.cursor > input.cursor
              · simp only [progress, if_true] at result
                exact .laterRejected
                  (caseArm_success_ordinary_sound statement statementOrdinary
                    statementSuccessSound armResult)
                  (by simpa [State.declarativeRemainder] using progress)
                  (inductionHypothesis (arm :: casesRev) afterArm failure
                    rejected result)
              · simp only [progress, if_false] at result
                contradiction

end Solcore.Syntax.Parser.YulControl
end

section
-- leanmerge: from Solcore.Syntax.Parser.YulSwitchOrdinaryOutcomeSoundnessProperties
/-!
Executable ordinary-success and exact-rejection bridges for complete inline-
Yul switches, including the diagnosed empty-case `.error` success.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem yulSwitchEnd_map_eq (scrutineeSpan : SourceSpan)
    (cases : List YulCase) (defaultBody : Option YulParsedBlock) :
    DeclarativeGrammar.yulSwitchEnd scrutineeSpan cases
        (defaultBody.map (fun body => body.span)) =
      match defaultBody with
      | some body => body.span
      | none => match cases.reverse with
        | last :: _ => last.span
        | [] => scrutineeSpan := by
  cases defaultBody <;> rfl

private theorem bind_ok_components {alpha beta : Type}
    {first : Parser alpha} {next : alpha → Parser beta}
    {input final : State} {value : beta}
    (parsed : (first >>= next) input = .ok value final) :
    ∃ firstValue afterFirst,
      first input = .ok firstValue afterFirst ∧
        next firstValue afterFirst = .ok value final := by
  change (match first input with
    | .ok firstValue afterFirst => next firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value final at parsed
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      rw [firstResult] at parsed
      exact ⟨firstValue, afterFirst, rfl, parsed⟩
  | reject failure rejected => rw [firstResult] at parsed; contradiction
  | invariant error => rw [firstResult] at parsed; contradiction

/-- Every executable switch success follows the ordinary switch relation.
The mandatory no-case diagnostic is erased only from the declarative
remainder, while its `.error` value and exact output cursor are retained. -/
theorem yulSwitchStatement_success_ordinary_sound
    (statement : Parser YulStmt)
    (statementOrdinary : DeclarativeGrammar.Remainder → YulStmt →
      DeclarativeGrammar.Remainder → Prop)
    (statementSuccessSound : ∀ {input output : State} {value : YulStmt},
      statement input = .ok value output →
        statementOrdinary input.declarativeRemainder value
          output.declarativeRemainder)
    {input output : State} {value : YulStmt}
    (result : yulSwitchStatement statement input = .ok value output) :
    DeclarativeGrammar.YulSwitchStatementOrdinaryParses statementOrdinary
      input.declarativeRemainder value output.declarativeRemainder := by
  unfold yulSwitchStatement at result
  rcases bind_ok_components result with
    ⟨marker, afterMarker, markerResult, scrutineeStage⟩
  rcases bind_ok_components scrutineeStage with
    ⟨scrutinee, afterScrutinee, scrutineeResult, casesStage⟩
  rcases bind_ok_components casesStage with
    ⟨cases, afterCases, casesResult, defaultStage⟩
  rcases bind_ok_components defaultStage with
    ⟨defaultBody, afterDefault, defaultResult, finished⟩
  have markerParsed := keyword_success_exactTokenParses .switchKw
    .yulStatement markerResult
  have scrutineeParsed := yulExpression_success_ordinary_sound
    scrutineeResult
  rcases YulControl.caseList_success_ordinary_sound statement
      statementOrdinary statementSuccessSound
      (afterScrutinee.remainingCount + 1) [] afterScrutinee cases afterCases
      casesResult with ⟨suffix, casesEq, casesParsed⟩
  have suffixEq : suffix = cases := by simpa using casesEq.symm
  subst suffix
  have defaultParsed := YulControl.optionalDefault_success_ordinary_sound
    statement statementOrdinary statementSuccessSound defaultResult
  have endEq := yulSwitchEnd_map_eq scrutinee.span cases defaultBody
  cases cases with
  | nil =>
      rcases bind_ok_components finished with
        ⟨emitted, afterEmit, emittedResult, completed⟩
      cases completed
      unfold emitDiagnostic modifyState at emittedResult
      cases emittedResult
      have ordinary :=
        DeclarativeGrammar.YulSwitchStatementOrdinaryParses.empty
          marker.span markerParsed scrutineeParsed casesParsed defaultParsed
      rw [endEq] at ordinary
      change DeclarativeGrammar.YulSwitchStatementOrdinaryParses
        statementOrdinary input.declarativeRemainder _
          afterDefault.declarativeRemainder
      exact ordinary
  | cons head tail =>
      cases finished
      have ordinary :=
        DeclarativeGrammar.YulSwitchStatementOrdinaryParses.nonempty
          marker.span markerParsed scrutineeParsed casesParsed defaultParsed
      rw [endEq] at ordinary
      exact ordinary

/-- Every executable switch rejection identifies its exact sequential stage
and retains the rejected remainder reported by that stage. -/
theorem yulSwitchStatement_reject_ordinary_sound
    (statement : Parser YulStmt)
    (statementOrdinary : DeclarativeGrammar.Remainder → YulStmt →
      DeclarativeGrammar.Remainder → Prop)
    (statementRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (statementSuccessSound : ∀ {input output : State} {value : YulStmt},
      statement input = .ok value output →
        statementOrdinary input.declarativeRemainder value
          output.declarativeRemainder)
    (statementRejectSound : ∀ {input rejected : State} {failure : Failure},
      statement input = .reject failure rejected →
        statementRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : yulSwitchStatement statement input = .reject failure rejected) :
    DeclarativeGrammar.YulSwitchStatementRejects statementOrdinary
      statementRejects input.declarativeRemainder
        rejected.declarativeRemainder := by
  unfold yulSwitchStatement at result
  cases markerResult : keyword .switchKw .yulStatement input with
  | invariant error => simp [bind, markerResult] at result
  | reject markerFailure markerRejected =>
      have rejectedEq := keyword_reject_state_eq .switchKw .yulStatement
        markerResult
      subst markerRejected
      simp only [bind, markerResult] at result
      cases result
      exact .markerMissing
        (keyword_reject_tokenKindAbsentAt .switchKw .yulStatement
          markerResult)
  | ok marker afterMarker =>
      simp only [bind, markerResult] at result
      cases scrutineeResult : yulExpression afterMarker with
      | invariant error => simp [scrutineeResult] at result
      | reject scrutineeFailure scrutineeRejected =>
          simp only [scrutineeResult] at result
          cases result
          exact .scrutineeRejected marker.span
            (keyword_success_exactTokenParses .switchKw .yulStatement
              markerResult)
            (yulExpression_reject_sound scrutineeResult)
      | ok scrutinee afterScrutinee =>
          simp only [scrutineeResult] at result
          cases casesResult : YulControl.caseList statement
              (afterScrutinee.remainingCount + 1) [] afterScrutinee with
          | invariant error => simp [casesResult] at result
          | reject casesFailure casesRejected =>
              have casesRejection :=
                YulControl.caseList_reject_ordinary_sound statement
                  statementOrdinary statementRejects statementSuccessSound
                  statementRejectSound (afterScrutinee.remainingCount + 1) []
                  afterScrutinee casesFailure casesRejected casesResult
              simp only [casesResult] at result
              cases result
              exact .casesRejected marker.span
                (keyword_success_exactTokenParses .switchKw .yulStatement
                  markerResult)
                (yulExpression_success_ordinary_sound scrutineeResult)
                casesRejection
          | ok cases afterCases =>
              simp only [casesResult] at result
              cases defaultResult : YulControl.optionalDefault statement
                  afterCases with
              | invariant error => simp [defaultResult] at result
              | reject defaultFailure defaultRejected =>
                  have defaultRejection :=
                    YulControl.optionalDefault_reject_ordinary_sound
                      statement statementOrdinary statementRejects
                      statementSuccessSound statementRejectSound
                      defaultResult
                  simp only [defaultResult] at result
                  cases result
                  rcases YulControl.caseList_success_ordinary_sound statement
                      statementOrdinary statementSuccessSound
                      (afterScrutinee.remainingCount + 1) [] afterScrutinee
                      cases afterCases casesResult with
                    ⟨suffix, casesEq, casesParsed⟩
                  have suffixEq : suffix = cases := by
                    simpa using casesEq.symm
                  subst suffix
                  exact .defaultRejected marker.span
                    (keyword_success_exactTokenParses .switchKw .yulStatement
                      markerResult)
                    (yulExpression_success_ordinary_sound scrutineeResult)
                    casesParsed
                    defaultRejection
              | ok defaultBody afterDefault =>
                  simp only [defaultResult] at result
                  cases cases <;> simp [emitDiagnostic, modifyState, pure]
                    at result

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.YulNameStatementOrdinarySoundnessProperties
/-!
Executable ordinary-success and exact-rejection bridges for the name-start
assignment-or-expression branch of the Yul statement dispatcher.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every successful executable name choice records either assignment success
or exact assignment rejection followed by expression success at the original
input. -/
theorem yulNameStatementChoice_success_ordinary_sound
    {input output : State} {statement : YulStmt}
    (result : orElse yulAssignment yulExpressionStatement input =
      .ok statement output) :
    DeclarativeGrammar.YulNameStatementOrdinaryParses
      input.declarativeRemainder statement output.declarativeRemainder := by
  unfold orElse at result
  cases assignmentResult : yulAssignment input with
  | invariant error => simp [assignmentResult] at result
  | ok assignment afterAssignment =>
      simp only [assignmentResult] at result
      cases result
      exact .primary
        (yulAssignment_success_ordinary_sound assignmentResult)
  | reject assignmentFailure assignmentRejected =>
      simp only [assignmentResult] at result
      exact .fallback
        (yulAssignment_reject_ordinaryOutcome_sound assignmentResult)
        (yulExpressionStatement_success_ordinary_sound result)

/-- Every executable name-choice rejection retains both exact branch
rejections and is nonconsuming because public expression rejection is
nonconsuming. -/
theorem yulNameStatementChoice_reject_sound
    {input rejected : State} {failure : Failure}
    (result : orElse yulAssignment yulExpressionStatement input =
      .reject failure rejected) :
    DeclarativeGrammar.YulNameStatementRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold orElse at result
  cases assignmentResult : yulAssignment input with
  | invariant error => simp [assignmentResult] at result
  | ok assignment afterAssignment => simp [assignmentResult] at result
  | reject assignmentFailure assignmentRejected =>
      simp only [assignmentResult] at result
      have assignmentRejection :=
        yulAssignment_reject_ordinaryOutcome_sound assignmentResult
      have expressionRejection :=
        yulExpressionStatement_reject_ordinaryOutcome_sound result
      cases expressionRejection with
      | expressionRejected rejectedExpression =>
          have outputEq := rejectedExpression.output_eq
          rw [outputEq]
          exact .both assignmentRejection
            (.expressionRejected rejectedExpression)

/-- The concrete name-choice executable exposes its declarative outcome
contract. -/
theorem yulNameStatementChoice_publicOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.YulNameStatementOrdinaryParses
      DeclarativeGrammar.YulNameStatementRejects :=
  DeclarativeGrammar.yulNameStatementDeterministicOutcomeSpec

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.YulStatementCoreOrdinaryTailSoundnessProperties
/-! Executable ordinary outcomes for the suffix after the `leave` guard. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- The exact executable suffix of `yulStatementCore` after a false `leave`
guard. -/
def yulStatementCoreAfterLeave : Parser YulStmt := fun state =>
  let fallback := yulExpressionStatement
  if isKeyword state .breakKw then
    recognizedYulStatementOrFallback
      (yulControlToken .breakKw .break) fallback state
  else if isKeyword state .continueKw then
    recognizedYulStatementOrFallback
      (yulControlToken .continueKw .continue) fallback state
  else if startsYulName state then
    orElse yulAssignment fallback state
  else
    fallback state

private theorem keyword_guard_of_true (value : HardKeyword) {input : State}
    (present : isKeyword input value = true) :
    DeclarativeGrammar.YulStatementCoreTokenAt input.declarativeRemainder
      (.keyword value) := by
  rcases keyword_eq_ok_of_isKeyword_eq_true_variant value .yulStatement present with
    ⟨token, result⟩
  exact ⟨token.span,
    (keyword_success_exactTokenParses value .yulStatement result).1⟩

/-- Every successful suffix execution selects its exact ordinary core branch. -/
theorem yulStatementCoreAfterLeave_success_ordinary_sound
    (statementOrdinary : DeclarativeGrammar.Remainder → YulStmt →
      DeclarativeGrammar.Remainder → Prop)
    (statementRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    {input output : State} {statement : YulStmt}
    (beforeLeave : DeclarativeGrammar.YulStatementCorePrefixAbsent
      input.declarativeRemainder .leaveGuard)
    (leaveAbsent : DeclarativeGrammar.TokenKindAbsentAt input.tokens
      input.window.endIndex input.cursor (.keyword .leaveKw))
    (result : yulStatementCoreAfterLeave input = .ok statement output) :
    DeclarativeGrammar.YulStatementCoreOrdinaryParses statementOrdinary
      statementRejects input.declarativeRemainder statement
        output.declarativeRemainder := by
  unfold yulStatementCoreAfterLeave at result
  have beforeBreak : DeclarativeGrammar.YulStatementCorePrefixAbsent
      input.declarativeRemainder .breakGuard :=
    .afterLeave beforeLeave leaveAbsent
  by_cases breakPresent : isKeyword input .breakKw
  · simp only [breakPresent, if_true] at result
    have parsed := recognizedYulStatementOrFallback_success_ordinary_sound
      (yulControlToken .breakKw .break) yulExpressionStatement
      (DeclarativeGrammar.YulControlTokenOrdinaryParses .breakKw .break)
      DeclarativeGrammar.YulExpressionStatementOrdinaryParses
      (DeclarativeGrammar.YulControlTokenRejects .breakKw)
      (yulControlToken_success_ordinary_sound .breakKw .break)
      (yulControlToken_reject_ordinaryOutcome_sound .breakKw .break)
      yulExpressionStatement_success_ordinary_sound result
    exact ⟨.breakGuard, .break beforeBreak
      (keyword_guard_of_true .breakKw breakPresent) parsed⟩
  · have breakFalse : isKeyword input .breakKw = false :=
      Bool.eq_false_iff.mpr breakPresent
    simp only [breakFalse, Bool.false_eq_true, if_false] at result
    have beforeContinue : DeclarativeGrammar.YulStatementCorePrefixAbsent
        input.declarativeRemainder .continueGuard := .afterBreak beforeBreak
      (keywordAbsentAt_of_isKeyword_eq_false .breakKw breakFalse)
    by_cases continuePresent : isKeyword input .continueKw
    · simp only [continuePresent, if_true] at result
      have parsed := recognizedYulStatementOrFallback_success_ordinary_sound
        (yulControlToken .continueKw .continue) yulExpressionStatement
        (DeclarativeGrammar.YulControlTokenOrdinaryParses
          .continueKw .continue)
        DeclarativeGrammar.YulExpressionStatementOrdinaryParses
        (DeclarativeGrammar.YulControlTokenRejects .continueKw)
        (yulControlToken_success_ordinary_sound .continueKw .continue)
        (yulControlToken_reject_ordinaryOutcome_sound .continueKw .continue)
        yulExpressionStatement_success_ordinary_sound result
      exact ⟨.continueGuard, .continue beforeContinue
        (keyword_guard_of_true .continueKw continuePresent) parsed⟩
    · have continueFalse : isKeyword input .continueKw = false :=
        Bool.eq_false_iff.mpr continuePresent
      simp only [continueFalse, Bool.false_eq_true, if_false] at result
      have beforeName : DeclarativeGrammar.YulStatementCorePrefixAbsent
          input.declarativeRemainder .nameGuard :=
        .afterContinue beforeContinue
          (keywordAbsentAt_of_isKeyword_eq_false .continueKw continueFalse)
      by_cases namePresent : startsYulName input
      · simp only [namePresent, if_true] at result
        exact ⟨.nameGuard, .nameChoice beforeName
          (yulNameStartAt_of_startsYulName_eq_true namePresent)
          (yulNameStatementChoice_success_ordinary_sound result)⟩
      · have nameFalse : startsYulName input = false :=
          Bool.eq_false_iff.mpr namePresent
        simp only [nameFalse, Bool.false_eq_true, if_false] at result
        exact ⟨.fallback, .expressionFallback
          (.afterName beforeName
            (yulNameStartAbsentAt_of_startsYulName_eq_false nameFalse))
          (yulExpressionStatement_success_ordinary_sound result)⟩

/-- Every suffix rejection selects its exact both-rejected core branch. -/
theorem yulStatementCoreAfterLeave_reject_ordinary_sound
    (statementOrdinary : DeclarativeGrammar.Remainder → YulStmt →
      DeclarativeGrammar.Remainder → Prop)
    (statementRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    {input rejected : State} {failure : Failure}
    (beforeLeave : DeclarativeGrammar.YulStatementCorePrefixAbsent
      input.declarativeRemainder .leaveGuard)
    (leaveAbsent : DeclarativeGrammar.TokenKindAbsentAt input.tokens
      input.window.endIndex input.cursor (.keyword .leaveKw))
    (result : yulStatementCoreAfterLeave input = .reject failure rejected) :
    DeclarativeGrammar.YulStatementCoreRejects statementOrdinary
      statementRejects input.declarativeRemainder
        rejected.declarativeRemainder := by
  unfold yulStatementCoreAfterLeave at result
  have beforeBreak : DeclarativeGrammar.YulStatementCorePrefixAbsent
      input.declarativeRemainder .breakGuard :=
    .afterLeave beforeLeave leaveAbsent
  by_cases breakPresent : isKeyword input .breakKw
  · simp only [breakPresent, if_true] at result
    exact ⟨.breakGuard, .break beforeBreak
      (keyword_guard_of_true .breakKw breakPresent)
      (recognizedYulStatementOrFallback_reject_sound
        (yulControlToken .breakKw .break) yulExpressionStatement
        (DeclarativeGrammar.YulControlTokenRejects .breakKw)
        DeclarativeGrammar.YulExpressionStatementRejects
        (yulControlToken_reject_ordinaryOutcome_sound .breakKw .break)
        yulExpressionStatement_reject_ordinaryOutcome_sound result)⟩
  · have breakFalse : isKeyword input .breakKw = false :=
      Bool.eq_false_iff.mpr breakPresent
    simp only [breakFalse, Bool.false_eq_true, if_false] at result
    have beforeContinue : DeclarativeGrammar.YulStatementCorePrefixAbsent
        input.declarativeRemainder .continueGuard := .afterBreak beforeBreak
      (keywordAbsentAt_of_isKeyword_eq_false .breakKw breakFalse)
    by_cases continuePresent : isKeyword input .continueKw
    · simp only [continuePresent, if_true] at result
      exact ⟨.continueGuard, .continue beforeContinue
        (keyword_guard_of_true .continueKw continuePresent)
        (recognizedYulStatementOrFallback_reject_sound
          (yulControlToken .continueKw .continue) yulExpressionStatement
          (DeclarativeGrammar.YulControlTokenRejects .continueKw)
          DeclarativeGrammar.YulExpressionStatementRejects
          (yulControlToken_reject_ordinaryOutcome_sound .continueKw .continue)
          yulExpressionStatement_reject_ordinaryOutcome_sound result)⟩
    · have continueFalse : isKeyword input .continueKw = false :=
        Bool.eq_false_iff.mpr continuePresent
      simp only [continueFalse, Bool.false_eq_true, if_false] at result
      have beforeName : DeclarativeGrammar.YulStatementCorePrefixAbsent
          input.declarativeRemainder .nameGuard :=
        .afterContinue beforeContinue
          (keywordAbsentAt_of_isKeyword_eq_false .continueKw continueFalse)
      by_cases namePresent : startsYulName input
      · simp only [namePresent, if_true] at result
        exact ⟨.nameGuard, .nameChoice beforeName
          (yulNameStartAt_of_startsYulName_eq_true namePresent)
          (yulNameStatementChoice_reject_sound result)⟩
      · have nameFalse : startsYulName input = false :=
          Bool.eq_false_iff.mpr namePresent
        simp only [nameFalse, Bool.false_eq_true, if_false] at result
        exact ⟨.fallback, .expressionFallback
          (.afterName beforeName
            (yulNameStartAbsentAt_of_startsYulName_eq_false nameFalse))
          (yulExpressionStatement_reject_ordinaryOutcome_sound result)⟩

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.YulStatementCoreOrdinarySuccessSoundnessProperties
/-! Unconditional ordinary-success reflection for `yulStatementCore`. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem symbol_guard_of_true (value : Symbol) {input : State}
    (present : isSymbol input value = true) :
    DeclarativeGrammar.YulStatementCoreTokenAt input.declarativeRemainder
      (.symbol value) := by
  rcases symbol_eq_ok_of_isSymbol_eq_true value .yulStatement present with
    ⟨token, result⟩
  exact ⟨token.span,
    (symbol_success_exactTokenParses value .yulStatement result).1⟩

/-- Every executable core success follows its exact prioritized ordinary
branch, including transactional expression fallback. -/
theorem yulStatementCore_success_ordinary_sound
    (nested : Parser YulStmt)
    (statementOrdinary : DeclarativeGrammar.Remainder → YulStmt →
      DeclarativeGrammar.Remainder → Prop)
    (statementRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (nestedSuccessSound : ∀ {input output : State} {statement : YulStmt},
      nested input = .ok statement output →
        statementOrdinary input.declarativeRemainder statement
          output.declarativeRemainder)
    (nestedRejectSound : ∀ {input rejected : State} {failure : Failure},
      nested input = .reject failure rejected →
        statementRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    {input output : State} {statement : YulStmt}
    (result : yulStatementCore nested input = .ok statement output) :
    DeclarativeGrammar.YulStatementCoreOrdinaryParses statementOrdinary
      statementRejects input.declarativeRemainder statement
        output.declarativeRemainder := by
  unfold yulStatementCore at result
  by_cases blockPresent : isSymbol input .leftBrace
  · simp only [blockPresent, if_true] at result
    have parsed := recognizedYulStatementOrFallback_success_ordinary_sound
      (yulBlockStatement nested) yulExpressionStatement
      (DeclarativeGrammar.YulBlockStatementOrdinaryParses statementOrdinary)
      DeclarativeGrammar.YulExpressionStatementOrdinaryParses
      (DeclarativeGrammar.YulBlockStatementRejects statementOrdinary
        statementRejects)
      (yulBlockStatement_success_ordinary_sound nested statementOrdinary
        nestedSuccessSound)
      (yulBlockStatement_reject_ordinary_sound nested statementOrdinary
        statementRejects nestedSuccessSound nestedRejectSound)
      yulExpressionStatement_success_ordinary_sound result
    exact ⟨.blockGuard, .block .start
      (symbol_guard_of_true .leftBrace blockPresent) parsed⟩
  · have blockFalse : isSymbol input .leftBrace = false :=
      Bool.eq_false_iff.mpr blockPresent
    simp only [blockFalse, Bool.false_eq_true, if_false] at result
    have beforeLet : DeclarativeGrammar.YulStatementCorePrefixAbsent
        input.declarativeRemainder .letGuard := .afterBlock .start
      (symbolAbsentAt_of_isSymbol_eq_false .leftBrace blockFalse)
    by_cases letPresent : isKeyword input .letKw
    · simp only [letPresent, if_true] at result
      have parsed := recognizedYulStatementOrFallback_success_ordinary_sound
        yulLetStatement yulExpressionStatement
        DeclarativeGrammar.YulLetStatementOrdinaryParses
        DeclarativeGrammar.YulExpressionStatementOrdinaryParses
        DeclarativeGrammar.YulLetStatementRejects
        yulLetStatement_success_ordinary_sound yulLetStatement_reject_sound
        yulExpressionStatement_success_ordinary_sound result
      exact ⟨.letGuard, .letDecl beforeLet
        (keyword_guard_of_true .letKw letPresent) parsed⟩
    · have letFalse : isKeyword input .letKw = false :=
        Bool.eq_false_iff.mpr letPresent
      simp only [letFalse, Bool.false_eq_true, if_false] at result
      have beforeIf : DeclarativeGrammar.YulStatementCorePrefixAbsent
          input.declarativeRemainder .ifGuard := .afterLet beforeLet
        (keywordAbsentAt_of_isKeyword_eq_false .letKw letFalse)
      by_cases ifPresent : isKeyword input .ifKw
      · simp only [ifPresent, if_true] at result
        have parsed := recognizedYulStatementOrFallback_success_ordinary_sound
          (yulIfStatement nested) yulExpressionStatement
          (DeclarativeGrammar.YulIfStatementOrdinaryParses statementOrdinary)
          DeclarativeGrammar.YulExpressionStatementOrdinaryParses
          (DeclarativeGrammar.YulIfStatementRejects statementOrdinary
            statementRejects)
          (yulIfStatement_success_ordinary_sound nested statementOrdinary
            nestedSuccessSound)
          (yulIfStatement_reject_ordinary_sound nested statementOrdinary
            statementRejects nestedSuccessSound nestedRejectSound)
          yulExpressionStatement_success_ordinary_sound result
        exact ⟨.ifGuard, .ifThen beforeIf
          (keyword_guard_of_true .ifKw ifPresent) parsed⟩
      · have ifFalse : isKeyword input .ifKw = false :=
          Bool.eq_false_iff.mpr ifPresent
        simp only [ifFalse, Bool.false_eq_true, if_false] at result
        have beforeFor : DeclarativeGrammar.YulStatementCorePrefixAbsent
            input.declarativeRemainder .forGuard := .afterIf beforeIf
          (keywordAbsentAt_of_isKeyword_eq_false .ifKw ifFalse)
        by_cases forPresent : isKeyword input .forKw
        · simp only [forPresent, if_true] at result
          have parsed := recognizedYulStatementOrFallback_success_ordinary_sound
            (yulForStatement nested) yulExpressionStatement
            (DeclarativeGrammar.YulForStatementOrdinaryParses
              statementOrdinary)
            DeclarativeGrammar.YulExpressionStatementOrdinaryParses
            (DeclarativeGrammar.YulForStatementRejects statementOrdinary
              statementRejects)
            (yulForStatement_success_ordinary_sound nested statementOrdinary
              nestedSuccessSound)
            (yulForStatement_reject_ordinary_sound nested statementOrdinary
              statementRejects nestedSuccessSound nestedRejectSound)
            yulExpressionStatement_success_ordinary_sound result
          exact ⟨.forGuard, .forLoop beforeFor
            (keyword_guard_of_true .forKw forPresent) parsed⟩
        · have forFalse : isKeyword input .forKw = false :=
            Bool.eq_false_iff.mpr forPresent
          simp only [forFalse, Bool.false_eq_true, if_false] at result
          have beforeSwitch : DeclarativeGrammar.YulStatementCorePrefixAbsent
              input.declarativeRemainder .switchGuard := .afterFor beforeFor
            (keywordAbsentAt_of_isKeyword_eq_false .forKw forFalse)
          by_cases switchPresent : isKeyword input .switchKw
          · simp only [switchPresent, if_true] at result
            have parsed :=
              recognizedYulStatementOrFallback_success_ordinary_sound
                (yulSwitchStatement nested) yulExpressionStatement
                (DeclarativeGrammar.YulSwitchStatementOrdinaryParses
                  statementOrdinary)
                DeclarativeGrammar.YulExpressionStatementOrdinaryParses
                (DeclarativeGrammar.YulSwitchStatementRejects
                  statementOrdinary statementRejects)
                (yulSwitchStatement_success_ordinary_sound nested
                  statementOrdinary nestedSuccessSound)
                (yulSwitchStatement_reject_ordinary_sound nested
                  statementOrdinary statementRejects nestedSuccessSound
                    nestedRejectSound)
                yulExpressionStatement_success_ordinary_sound result
            exact ⟨.switchGuard, .switch beforeSwitch
              (keyword_guard_of_true .switchKw switchPresent) parsed⟩
          · have switchFalse : isKeyword input .switchKw = false :=
              Bool.eq_false_iff.mpr switchPresent
            simp only [switchFalse, Bool.false_eq_true, if_false] at result
            have beforeFunction :
                DeclarativeGrammar.YulStatementCorePrefixAbsent
                  input.declarativeRemainder .functionGuard :=
              .afterSwitch beforeSwitch
                (keywordAbsentAt_of_isKeyword_eq_false .switchKw switchFalse)
            by_cases functionPresent : isKeyword input .functionKw
            · simp only [functionPresent, if_true] at result
              have parsed :=
                recognizedYulStatementOrFallback_success_ordinary_sound
                  (yulFunctionStatement nested) yulExpressionStatement
                  (DeclarativeGrammar.YulFunctionStatementOrdinaryParses
                    statementOrdinary)
                  DeclarativeGrammar.YulExpressionStatementOrdinaryParses
                  (DeclarativeGrammar.YulFunctionStatementRejects
                    statementOrdinary statementRejects)
                  (yulFunctionStatement_success_ordinary_sound nested
                    statementOrdinary nestedSuccessSound)
                  (yulFunctionStatement_reject_ordinary_sound nested
                    statementOrdinary statementRejects nestedSuccessSound
                      nestedRejectSound)
                  yulExpressionStatement_success_ordinary_sound result
              exact ⟨.functionGuard, .functionDef beforeFunction
                (keyword_guard_of_true .functionKw functionPresent) parsed⟩
            · have functionFalse : isKeyword input .functionKw = false :=
                Bool.eq_false_iff.mpr functionPresent
              simp only [functionFalse, Bool.false_eq_true, if_false] at result
              have beforeReturn :
                  DeclarativeGrammar.YulStatementCorePrefixAbsent
                    input.declarativeRemainder .returnGuard :=
                .afterFunction beforeFunction
                  (keywordAbsentAt_of_isKeyword_eq_false .functionKw
                    functionFalse)
              by_cases returnPresent : isKeyword input .returnKw
              · simp only [returnPresent, if_true] at result
                have parsed :=
                  recognizedYulStatementOrFallback_success_ordinary_sound
                    yulReturnBuiltin yulExpressionStatement
                    DeclarativeGrammar.YulReturnBuiltinOrdinaryParses
                    DeclarativeGrammar.YulExpressionStatementOrdinaryParses
                    DeclarativeGrammar.YulReturnBuiltinRejects
                    yulReturnBuiltin_success_ordinary_sound
                    yulReturnBuiltin_reject_ordinaryOutcome_sound
                    yulExpressionStatement_success_ordinary_sound result
                exact ⟨.returnGuard, .returnBuiltin beforeReturn
                  (keyword_guard_of_true .returnKw returnPresent) parsed⟩
              · have returnFalse : isKeyword input .returnKw = false :=
                  Bool.eq_false_iff.mpr returnPresent
                simp only [returnFalse, Bool.false_eq_true, if_false] at result
                have beforeLeave :
                    DeclarativeGrammar.YulStatementCorePrefixAbsent
                      input.declarativeRemainder .leaveGuard :=
                  .afterReturn beforeReturn
                    (keywordAbsentAt_of_isKeyword_eq_false .returnKw
                      returnFalse)
                by_cases leavePresent : isKeyword input .leaveKw
                · simp only [leavePresent, if_true] at result
                  have parsed :=
                    recognizedYulStatementOrFallback_success_ordinary_sound
                      (yulControlToken .leaveKw .leave) yulExpressionStatement
                      (DeclarativeGrammar.YulControlTokenOrdinaryParses
                        .leaveKw .leave)
                      DeclarativeGrammar.YulExpressionStatementOrdinaryParses
                      (DeclarativeGrammar.YulControlTokenRejects .leaveKw)
                      (yulControlToken_success_ordinary_sound .leaveKw .leave)
                      (yulControlToken_reject_ordinaryOutcome_sound .leaveKw
                        .leave)
                      yulExpressionStatement_success_ordinary_sound result
                  exact ⟨.leaveGuard, .leave beforeLeave
                    (keyword_guard_of_true .leaveKw leavePresent) parsed⟩
                · have leaveFalse : isKeyword input .leaveKw = false :=
                    Bool.eq_false_iff.mpr leavePresent
                  simp only [leaveFalse, Bool.false_eq_true, if_false]
                    at result
                  change yulStatementCoreAfterLeave input =
                    .ok statement output at result
                  exact yulStatementCoreAfterLeave_success_ordinary_sound
                    statementOrdinary statementRejects beforeLeave
                    (keywordAbsentAt_of_isKeyword_eq_false .leaveKw leaveFalse)
                    result

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.YulStatementCoreOrdinaryRejectSoundnessProperties
/-! Exact ordinary-rejection reflection for `yulStatementCore`. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every executable core rejection identifies the exact selected branch and
retains both transactional branch rejections. -/
theorem yulStatementCore_reject_ordinary_sound
    (nested : Parser YulStmt)
    (statementOrdinary : DeclarativeGrammar.Remainder → YulStmt →
      DeclarativeGrammar.Remainder → Prop)
    (statementRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (nestedSuccessSound : ∀ {input output : State} {statement : YulStmt},
      nested input = .ok statement output →
        statementOrdinary input.declarativeRemainder statement
          output.declarativeRemainder)
    (nestedRejectSound : ∀ {input rejected : State} {failure : Failure},
      nested input = .reject failure rejected →
        statementRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : yulStatementCore nested input = .reject failure rejected) :
    DeclarativeGrammar.YulStatementCoreRejects statementOrdinary
      statementRejects input.declarativeRemainder
        rejected.declarativeRemainder := by
  unfold yulStatementCore at result
  by_cases blockPresent : isSymbol input .leftBrace
  · simp only [blockPresent, if_true] at result
    exact ⟨.blockGuard, .block .start
      (symbol_guard_of_true .leftBrace blockPresent)
      (recognizedYulStatementOrFallback_reject_sound
        (yulBlockStatement nested) yulExpressionStatement
        (DeclarativeGrammar.YulBlockStatementRejects statementOrdinary
          statementRejects)
        DeclarativeGrammar.YulExpressionStatementRejects
        (yulBlockStatement_reject_ordinary_sound nested statementOrdinary
          statementRejects nestedSuccessSound nestedRejectSound)
        yulExpressionStatement_reject_ordinaryOutcome_sound result)⟩
  · have blockFalse : isSymbol input .leftBrace = false :=
      Bool.eq_false_iff.mpr blockPresent
    simp only [blockFalse, Bool.false_eq_true, if_false] at result
    have beforeLet : DeclarativeGrammar.YulStatementCorePrefixAbsent
        input.declarativeRemainder .letGuard := .afterBlock .start
      (symbolAbsentAt_of_isSymbol_eq_false .leftBrace blockFalse)
    by_cases letPresent : isKeyword input .letKw
    · simp only [letPresent, if_true] at result
      exact ⟨.letGuard, .letDecl beforeLet
        (keyword_guard_of_true .letKw letPresent)
        (recognizedYulStatementOrFallback_reject_sound yulLetStatement
          yulExpressionStatement DeclarativeGrammar.YulLetStatementRejects
          DeclarativeGrammar.YulExpressionStatementRejects
          yulLetStatement_reject_sound
          yulExpressionStatement_reject_ordinaryOutcome_sound result)⟩
    · have letFalse : isKeyword input .letKw = false :=
        Bool.eq_false_iff.mpr letPresent
      simp only [letFalse, Bool.false_eq_true, if_false] at result
      have beforeIf : DeclarativeGrammar.YulStatementCorePrefixAbsent
          input.declarativeRemainder .ifGuard := .afterLet beforeLet
        (keywordAbsentAt_of_isKeyword_eq_false .letKw letFalse)
      by_cases ifPresent : isKeyword input .ifKw
      · simp only [ifPresent, if_true] at result
        exact ⟨.ifGuard, .ifThen beforeIf
          (keyword_guard_of_true .ifKw ifPresent)
          (recognizedYulStatementOrFallback_reject_sound
            (yulIfStatement nested) yulExpressionStatement
            (DeclarativeGrammar.YulIfStatementRejects statementOrdinary
              statementRejects)
            DeclarativeGrammar.YulExpressionStatementRejects
            (yulIfStatement_reject_ordinary_sound nested statementOrdinary
              statementRejects nestedSuccessSound nestedRejectSound)
            yulExpressionStatement_reject_ordinaryOutcome_sound result)⟩
      · have ifFalse : isKeyword input .ifKw = false :=
          Bool.eq_false_iff.mpr ifPresent
        simp only [ifFalse, Bool.false_eq_true, if_false] at result
        have beforeFor : DeclarativeGrammar.YulStatementCorePrefixAbsent
            input.declarativeRemainder .forGuard := .afterIf beforeIf
          (keywordAbsentAt_of_isKeyword_eq_false .ifKw ifFalse)
        by_cases forPresent : isKeyword input .forKw
        · simp only [forPresent, if_true] at result
          exact ⟨.forGuard, .forLoop beforeFor
            (keyword_guard_of_true .forKw forPresent)
            (recognizedYulStatementOrFallback_reject_sound
              (yulForStatement nested) yulExpressionStatement
              (DeclarativeGrammar.YulForStatementRejects statementOrdinary
                statementRejects)
              DeclarativeGrammar.YulExpressionStatementRejects
              (yulForStatement_reject_ordinary_sound nested statementOrdinary
                statementRejects nestedSuccessSound nestedRejectSound)
              yulExpressionStatement_reject_ordinaryOutcome_sound result)⟩
        · have forFalse : isKeyword input .forKw = false :=
            Bool.eq_false_iff.mpr forPresent
          simp only [forFalse, Bool.false_eq_true, if_false] at result
          have beforeSwitch : DeclarativeGrammar.YulStatementCorePrefixAbsent
              input.declarativeRemainder .switchGuard := .afterFor beforeFor
            (keywordAbsentAt_of_isKeyword_eq_false .forKw forFalse)
          by_cases switchPresent : isKeyword input .switchKw
          · simp only [switchPresent, if_true] at result
            exact ⟨.switchGuard, .switch beforeSwitch
              (keyword_guard_of_true .switchKw switchPresent)
              (recognizedYulStatementOrFallback_reject_sound
                (yulSwitchStatement nested) yulExpressionStatement
                (DeclarativeGrammar.YulSwitchStatementRejects
                  statementOrdinary statementRejects)
                DeclarativeGrammar.YulExpressionStatementRejects
                (yulSwitchStatement_reject_ordinary_sound nested
                  statementOrdinary statementRejects nestedSuccessSound
                    nestedRejectSound)
                yulExpressionStatement_reject_ordinaryOutcome_sound result)⟩
          · have switchFalse : isKeyword input .switchKw = false :=
              Bool.eq_false_iff.mpr switchPresent
            simp only [switchFalse, Bool.false_eq_true, if_false] at result
            have beforeFunction :
                DeclarativeGrammar.YulStatementCorePrefixAbsent
                  input.declarativeRemainder .functionGuard :=
              .afterSwitch beforeSwitch
                (keywordAbsentAt_of_isKeyword_eq_false .switchKw switchFalse)
            by_cases functionPresent : isKeyword input .functionKw
            · simp only [functionPresent, if_true] at result
              exact ⟨.functionGuard, .functionDef beforeFunction
                (keyword_guard_of_true .functionKw functionPresent)
                (recognizedYulStatementOrFallback_reject_sound
                  (yulFunctionStatement nested) yulExpressionStatement
                  (DeclarativeGrammar.YulFunctionStatementRejects
                    statementOrdinary statementRejects)
                  DeclarativeGrammar.YulExpressionStatementRejects
                  (yulFunctionStatement_reject_ordinary_sound nested
                    statementOrdinary statementRejects nestedSuccessSound
                      nestedRejectSound)
                  yulExpressionStatement_reject_ordinaryOutcome_sound
                    result)⟩
            · have functionFalse : isKeyword input .functionKw = false :=
                Bool.eq_false_iff.mpr functionPresent
              simp only [functionFalse, Bool.false_eq_true, if_false] at result
              have beforeReturn :
                  DeclarativeGrammar.YulStatementCorePrefixAbsent
                    input.declarativeRemainder .returnGuard :=
                .afterFunction beforeFunction
                  (keywordAbsentAt_of_isKeyword_eq_false .functionKw
                    functionFalse)
              by_cases returnPresent : isKeyword input .returnKw
              · simp only [returnPresent, if_true] at result
                exact ⟨.returnGuard, .returnBuiltin beforeReturn
                  (keyword_guard_of_true .returnKw returnPresent)
                  (recognizedYulStatementOrFallback_reject_sound
                    yulReturnBuiltin yulExpressionStatement
                    DeclarativeGrammar.YulReturnBuiltinRejects
                    DeclarativeGrammar.YulExpressionStatementRejects
                    yulReturnBuiltin_reject_ordinaryOutcome_sound
                    yulExpressionStatement_reject_ordinaryOutcome_sound
                      result)⟩
              · have returnFalse : isKeyword input .returnKw = false :=
                  Bool.eq_false_iff.mpr returnPresent
                simp only [returnFalse, Bool.false_eq_true, if_false] at result
                have beforeLeave :
                    DeclarativeGrammar.YulStatementCorePrefixAbsent
                      input.declarativeRemainder .leaveGuard :=
                  .afterReturn beforeReturn
                    (keywordAbsentAt_of_isKeyword_eq_false .returnKw
                      returnFalse)
                by_cases leavePresent : isKeyword input .leaveKw
                · simp only [leavePresent, if_true] at result
                  exact ⟨.leaveGuard, .leave beforeLeave
                    (keyword_guard_of_true .leaveKw leavePresent)
                    (recognizedYulStatementOrFallback_reject_sound
                      (yulControlToken .leaveKw .leave) yulExpressionStatement
                      (DeclarativeGrammar.YulControlTokenRejects .leaveKw)
                      DeclarativeGrammar.YulExpressionStatementRejects
                      (yulControlToken_reject_ordinaryOutcome_sound .leaveKw
                        .leave)
                      yulExpressionStatement_reject_ordinaryOutcome_sound
                        result)⟩
                · have leaveFalse : isKeyword input .leaveKw = false :=
                    Bool.eq_false_iff.mpr leavePresent
                  simp only [leaveFalse, Bool.false_eq_true, if_false]
                    at result
                  change yulStatementCoreAfterLeave input =
                    .reject failure rejected at result
                  exact yulStatementCoreAfterLeave_reject_ordinary_sound
                    statementOrdinary statementRejects beforeLeave
                    (keywordAbsentAt_of_isKeyword_eq_false .leaveKw leaveFalse)
                    result

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.YulStatementFuelOrdinarySoundnessProperties
/-! Ordinary outcome reflection for recursive fuel-indexed Yul statements. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Success and rejection reflection are proved together because one
recursive core layer needs both outcomes of its preceding fuel. -/
theorem yulStatementWithFuel_ordinaryOutcome_sound : ∀ fuel,
    (∀ {input output : State} {statement : YulStmt},
      yulStatementWithFuel fuel input = .ok statement output →
        DeclarativeGrammar.YulStatementOrdinaryParsesWithFuel fuel
          input.declarativeRemainder statement output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      yulStatementWithFuel fuel input = .reject failure rejected →
        DeclarativeGrammar.YulStatementRejectsWithFuel fuel
          input.declarativeRemainder rejected.declarativeRemainder) := by
  intro fuel
  induction fuel with
  | zero =>
      constructor
      · intro input output statement result
        simp [yulStatementWithFuel] at result
      · intro input rejected failure result
        simp [yulStatementWithFuel] at result
  | succ fuel inductionHypothesis =>
      have nestedShape := yulStatementWithFuel_preservesTokenWindow fuel
      have coreShape := yulStatementCore_preservesTokenWindow
        (yulStatementWithFuel fuel) nestedShape
      have terminatedShape := yulStatementTerminated_preservesTokenWindow
        (yulStatementWithFuel fuel) coreShape
      have coreSuccessSound : ∀ {input output : State}
          {statement : YulStmt},
          yulStatementCore (yulStatementWithFuel fuel) input =
              .ok statement output →
            DeclarativeGrammar.YulStatementCoreOrdinaryParses
              (DeclarativeGrammar.YulStatementOrdinaryParsesWithFuel fuel)
              (DeclarativeGrammar.YulStatementRejectsWithFuel fuel)
              input.declarativeRemainder statement
                output.declarativeRemainder := by
        intro input output statement coreResult
        exact yulStatementCore_success_ordinary_sound
          (yulStatementWithFuel fuel)
          (DeclarativeGrammar.YulStatementOrdinaryParsesWithFuel fuel)
          (DeclarativeGrammar.YulStatementRejectsWithFuel fuel)
          inductionHypothesis.1 inductionHypothesis.2 coreResult
      have coreRejectSound : ∀ {input rejected : State} {failure : Failure},
          yulStatementCore (yulStatementWithFuel fuel) input =
              .reject failure rejected →
            DeclarativeGrammar.YulStatementCoreRejects
              (DeclarativeGrammar.YulStatementOrdinaryParsesWithFuel fuel)
              (DeclarativeGrammar.YulStatementRejectsWithFuel fuel)
              input.declarativeRemainder rejected.declarativeRemainder := by
        intro input rejected failure coreResult
        exact yulStatementCore_reject_ordinary_sound
          (yulStatementWithFuel fuel)
          (DeclarativeGrammar.YulStatementOrdinaryParsesWithFuel fuel)
          (DeclarativeGrammar.YulStatementRejectsWithFuel fuel)
          inductionHypothesis.1 inductionHypothesis.2 coreResult
      have terminatedSuccessSound : ∀ {input output : State}
          {statement : YulStmt},
          yulStatementTerminated (yulStatementWithFuel fuel) input =
              .ok statement output →
            DeclarativeGrammar.YulStatementTerminatedOrdinaryParses
              (DeclarativeGrammar.YulStatementCoreOrdinaryParses
                (DeclarativeGrammar.YulStatementOrdinaryParsesWithFuel fuel)
                (DeclarativeGrammar.YulStatementRejectsWithFuel fuel))
              input.declarativeRemainder statement
                output.declarativeRemainder := by
        intro input output statement terminatedResult
        exact yulStatementTerminated_success_ordinary_sound
          (yulStatementWithFuel fuel)
          (DeclarativeGrammar.YulStatementCoreOrdinaryParses
            (DeclarativeGrammar.YulStatementOrdinaryParsesWithFuel fuel)
            (DeclarativeGrammar.YulStatementRejectsWithFuel fuel))
          coreSuccessSound terminatedResult
      have terminatedRejectSound : ∀ {input rejected : State}
          {failure : Failure},
          yulStatementTerminated (yulStatementWithFuel fuel) input =
              .reject failure rejected →
            DeclarativeGrammar.YulStatementCoreRejects
              (DeclarativeGrammar.YulStatementOrdinaryParsesWithFuel fuel)
              (DeclarativeGrammar.YulStatementRejectsWithFuel fuel)
              input.declarativeRemainder rejected.declarativeRemainder := by
        intro input rejected failure terminatedResult
        exact yulStatementTerminated_reject_ordinary_sound
          (yulStatementWithFuel fuel)
          (DeclarativeGrammar.YulStatementCoreRejects
            (DeclarativeGrammar.YulStatementOrdinaryParsesWithFuel fuel)
            (DeclarativeGrammar.YulStatementRejectsWithFuel fuel))
          coreRejectSound terminatedResult
      constructor
      · intro input output statement result
        apply (DeclarativeGrammar.YulStatementOrdinaryParsesWithFuel.succ_iff).2
        exact yulStatementLayer_success_ordinary_sound
          (yulStatementWithFuel fuel)
          (DeclarativeGrammar.YulStatementTerminatedOrdinaryParses
            (DeclarativeGrammar.YulStatementCoreOrdinaryParses
              (DeclarativeGrammar.YulStatementOrdinaryParsesWithFuel fuel)
              (DeclarativeGrammar.YulStatementRejectsWithFuel fuel)))
          (DeclarativeGrammar.YulStatementCoreRejects
            (DeclarativeGrammar.YulStatementOrdinaryParsesWithFuel fuel)
            (DeclarativeGrammar.YulStatementRejectsWithFuel fuel))
          terminatedSuccessSound terminatedRejectSound terminatedShape result
      · intro input rejected failure result
        apply (DeclarativeGrammar.YulStatementRejectsWithFuel.succ_iff).2
        exact yulStatementLayer_reject_sound (yulStatementWithFuel fuel)
          terminatedShape result

/-- Every successful executable statement at explicit fuel follows the
ordinary declarative relation at that same fuel. -/
theorem yulStatementWithFuel_success_ordinary_sound (fuel : Nat)
    {input output : State} {statement : YulStmt}
    (result : yulStatementWithFuel fuel input = .ok statement output) :
    DeclarativeGrammar.YulStatementOrdinaryParsesWithFuel fuel
      input.declarativeRemainder statement output.declarativeRemainder :=
  (yulStatementWithFuel_ordinaryOutcome_sound fuel).1 result

/-- Every executable rejection at explicit fuel follows the exact declarative
rejection at that same fuel. -/
theorem yulStatementWithFuel_reject_ordinary_sound (fuel : Nat)
    {input rejected : State} {failure : Failure}
    (result : yulStatementWithFuel fuel input = .reject failure rejected) :
    DeclarativeGrammar.YulStatementRejectsWithFuel fuel
      input.declarativeRemainder rejected.declarativeRemainder :=
  (yulStatementWithFuel_ordinaryOutcome_sound fuel).2 result

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.YulStatementPublicFuelSoundnessProperties
/-! Concrete public-fuel soundness for `yulStatement`. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- The executable `remainingCount + 1` is exactly the parser-independent
public statement fuel on the same active token window and cursor. -/
@[simp] theorem yulStatement_executableFuel_eq_publicFuel (input : State) :
    input.remainingCount + 1 =
      DeclarativeGrammar.yulStatementPublicFuel
        input.declarativeRemainder := by
  rfl

/-- Every diagnostic-free public statement success follows the clean grammar
at the exact public fuel selected from its input remainder. -/
theorem yulStatement_success_clean_sound
    {input output : State} {statement : YulStmt}
    (diagnosticFree : output.diagnosticsRev = [])
    (result : yulStatement input = .ok statement output) :
    DeclarativeGrammar.YulStatementParses input.declarativeRemainder statement
      output.declarativeRemainder := by
  unfold yulStatement at result
  unfold DeclarativeGrammar.YulStatementParses
  rw [← yulStatement_executableFuel_eq_publicFuel input]
  exact yulStatementWithFuel_success_clean_sound
    (input.remainingCount + 1) diagnosticFree result

/-- Every public statement success follows the ordinary public grammar,
including diagnosed recovery success. -/
theorem yulStatement_success_ordinary_sound
    {input output : State} {statement : YulStmt}
    (result : yulStatement input = .ok statement output) :
    DeclarativeGrammar.YulStatementOrdinaryParses
      input.declarativeRemainder statement output.declarativeRemainder := by
  unfold yulStatement at result
  unfold DeclarativeGrammar.YulStatementOrdinaryParses
  rw [← yulStatement_executableFuel_eq_publicFuel input]
  exact yulStatementWithFuel_success_ordinary_sound
    (input.remainingCount + 1) result

/-- Every public statement rejection follows the exact public fuel-indexed
rejection relation. -/
theorem yulStatement_reject_ordinary_sound
    {input rejected : State} {failure : Failure}
    (result : yulStatement input = .reject failure rejected) :
    DeclarativeGrammar.YulStatementPublicRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold yulStatement at result
  unfold DeclarativeGrammar.YulStatementPublicRejects
  rw [← yulStatement_executableFuel_eq_publicFuel input]
  exact yulStatementWithFuel_reject_ordinary_sound
    (input.remainingCount + 1) result

/-- Public executable rejection is equivalently the concrete nonconsuming
outer statement boundary. -/
theorem yulStatement_reject_boundary_sound
    {input rejected : State} {failure : Failure}
    (result : yulStatement input = .reject failure rejected) :
    DeclarativeGrammar.YulStatementRejects input.declarativeRemainder
      rejected.declarativeRemainder :=
  DeclarativeGrammar.yulStatementPublicRejects_iff.mp
    (yulStatement_reject_ordinary_sound result)

/-- Re-export full ordinary statement exactness at each recursive fuel. -/
theorem yulStatementWithFuel_exactOutcomeSpec (fuel : Nat) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.YulStatementOrdinaryParsesWithFuel fuel)
      (DeclarativeGrammar.YulStatementRejectsWithFuel fuel) :=
  DeclarativeGrammar.yulStatementExactOutcomeSpecWithFuel fuel

/-- Fixed-fuel executable successes agree on their complete statement result. -/
theorem yulStatementWithFuel_success_result_unique (fuel : Nat)
    {input leftOutput rightOutput : State} {left right : YulStmt}
    (leftResult : yulStatementWithFuel fuel input = .ok left leftOutput)
    (rightResult : yulStatementWithFuel fuel input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.YulStatementOrdinaryParsesWithFuel.result_unique
    (yulStatementWithFuel_success_ordinary_sound fuel leftResult)
    (yulStatementWithFuel_success_ordinary_sound fuel rightResult)

/-- Fixed-fuel executable rejections agree on the complete declarative endpoint. -/
theorem yulStatementWithFuel_reject_output_unique (fuel : Nat)
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : yulStatementWithFuel fuel input = .reject leftFailure leftOutput)
    (rightResult : yulStatementWithFuel fuel input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.YulStatementRejectsWithFuel.output_unique
    (yulStatementWithFuel_reject_ordinary_sound fuel leftResult)
    (yulStatementWithFuel_reject_ordinary_sound fuel rightResult)

/-- Re-export public statement exactness with the input-selected fuel relation. -/
theorem yulStatement_publicExactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.YulStatementOrdinaryParses
      DeclarativeGrammar.YulStatementPublicRejects :=
  DeclarativeGrammar.yulStatementPublicExactOutcomeSpec

/-- Exact public statements against the concrete recovery-boundary rejection. -/
theorem yulStatement_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.YulStatementOrdinaryParses
      DeclarativeGrammar.YulStatementRejects :=
  DeclarativeGrammar.yulStatementExactOutcomeSpec

/-- Public executable statement successes agree on their AST and remainder. -/
theorem yulStatement_success_result_unique
    {input leftOutput rightOutput : State} {left right : YulStmt}
    (leftResult : yulStatement input = .ok left leftOutput)
    (rightResult : yulStatement input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.YulStatementOrdinaryParses.result_unique
    (yulStatement_success_ordinary_sound leftResult)
    (yulStatement_success_ordinary_sound rightResult)

/-- Public executable statement rejections agree on their complete endpoint. -/
theorem yulStatement_reject_output_unique
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : yulStatement input = .reject leftFailure leftOutput)
    (rightResult : yulStatement input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.YulStatementPublicRejects.output_unique
    (yulStatement_reject_ordinary_sound leftResult)
    (yulStatement_reject_ordinary_sound rightResult)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.YulBodyPublicSoundnessProperties
/-! Concrete clean and ordinary outcome soundness for public `yulBody`. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every diagnostic-free public body success follows the concrete clean Yul
body grammar. -/
theorem yulBody_success_clean_sound
    {input output : State} {body : YulParsedBlock}
    (diagnosticFree : output.diagnosticsRev = [])
    (result : yulBody input = .ok body output) :
    DeclarativeGrammar.YulBodyParses input.declarativeRemainder body.span
      body.body output.declarativeRemainder :=
  yulBlock_success_sound yulStatement
    DeclarativeGrammar.YulStatementParses
    yulStatement_reflectsDiagnosticFreeOnSuccess
    yulStatement_success_clean_sound diagnosticFree result

/-- Every public body success, including diagnosed statement recovery,
follows the concrete ordinary Yul body grammar. -/
theorem yulBody_success_ordinary_sound
    {input output : State} {body : YulParsedBlock}
    (result : yulBody input = .ok body output) :
    DeclarativeGrammar.YulBodyOrdinaryParses input.declarativeRemainder
      body.span body.body output.declarativeRemainder :=
  yulBlock_success_ordinary_sound yulStatement
    DeclarativeGrammar.YulStatementOrdinaryParses
    yulStatement_success_ordinary_sound result

/-- Every public body rejection follows the exact opening, item-prefix, or
closing-boundary rejection trace. -/
theorem yulBody_reject_ordinary_sound
    {input rejected : State} {failure : Failure}
    (result : yulBody input = .reject failure rejected) :
    DeclarativeGrammar.YulBodyRejects input.declarativeRemainder
      rejected.declarativeRemainder :=
  yulBlock_reject_ordinary_sound yulStatement
    DeclarativeGrammar.YulStatementOrdinaryParses
    DeclarativeGrammar.YulStatementRejects
    yulStatement_success_ordinary_sound yulStatement_reject_boundary_sound
    result

/-- Package an executable body success for the public deterministic outcome
contract. -/
theorem yulBody_success_outcome_sound
    {input output : State} {body : YulParsedBlock}
    (result : yulBody input = .ok body output) :
    DeclarativeGrammar.YulBodyOutcomeParses input.declarativeRemainder {
      span := body.span
      body := body.body
    } output.declarativeRemainder :=
  yulBody_success_ordinary_sound result

/-- Deterministic parser-independent outcomes exposed beside the executable
public body bridges. -/
theorem yulBody_publicOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.YulBodyOutcomeParses
      DeclarativeGrammar.YulBodyRejects :=
  DeclarativeGrammar.yulBodyDeterministicOutcomeSpec

/-- Re-export fully exact public Yul body values and rejecting endpoints. -/
theorem yulBody_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.YulBodyOutcomeParses
      DeclarativeGrammar.YulBodyRejects :=
  DeclarativeGrammar.yulBodyExactOutcomeSpec

/-- Public executable bodies agree on their complete span, body, and remainder. -/
theorem yulBody_success_result_unique
    {input leftOutput rightOutput : State} {left right : YulParsedBlock}
    (leftResult : yulBody input = .ok left leftOutput)
    (rightResult : yulBody input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder := by
  rcases DeclarativeGrammar.YulBodyOrdinaryParses.result_unique
    (yulBody_success_ordinary_sound leftResult)
    (yulBody_success_ordinary_sound rightResult) with ⟨spanEq, bodyEq, outputEq⟩
  refine ⟨?_, outputEq⟩
  cases left
  cases right
  simp_all

/-- Public executable bodies agree on the complete first-failure endpoint. -/
theorem yulBody_reject_output_unique
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : yulBody input = .reject leftFailure leftOutput)
    (rightResult : yulBody input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.YulBodyRejects.output_unique
    (yulBody_reject_ordinary_sound leftResult)
    (yulBody_reject_ordinary_sound rightResult)

end Solcore.Syntax.Parser
end
