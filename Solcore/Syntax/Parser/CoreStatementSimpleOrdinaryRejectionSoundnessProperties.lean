import Solcore.Syntax.Parser.CoreStatementSimpleOrdinarySuccessSoundnessProperties
import Solcore.Syntax.Parser.YulKeywordRejectionSoundnessProperties

/-! Exact executable rejection for canonical Core `let` and `return`. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every executable `let` rejection records the first failing stage and its
exact rejected remainder. -/
theorem letStatement_reject_ordinary_sound
    (expression : Parser Expr)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSuccessSound : ∀ {input output : State} {value : Expr},
      expression input = .ok value output → expressionOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (expressionRejectSound : ∀ {input rejected : State}
      {failure : Failure}, expression input = .reject failure rejected →
        expressionRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : letStatement expression input = .reject failure rejected) :
    DeclarativeGrammar.LetStatementRejects expressionOrdinary
      expressionRejects DeclarativeGrammar.TypeExprRejects
        input.declarativeRemainder rejected.declarativeRemainder := by
  unfold letStatement at result
  cases markerResult : keyword .letKw .statement input with
  | invariant error => simp [bind, markerResult] at result
  | reject markerFailure markerRejected =>
      have markerRejectedEq := keyword_reject_state_eq .letKw .statement
        markerResult
      subst markerRejected
      simp only [bind, markerResult] at result
      cases result
      exact .markerRejected
        (keyword_reject_tokenKindAbsentAt .letKw .statement markerResult)
  | ok marker afterMarker =>
      simp only [bind, markerResult] at result
      have markerParsed := keyword_success_exactTokenParses .letKw .statement
        markerResult
      cases nameResult : identifier .statement afterMarker with
      | invariant error => simp [nameResult] at result
      | reject nameFailure nameRejected =>
          simp only [nameResult] at result
          cases result
          exact .nameRejected marker.span markerParsed
            (identifier_reject_sound .statement nameResult)
      | ok name afterName =>
          simp only [nameResult] at result
          have nameParsed := identifier_success_sound .statement nameResult
          cases typeResult : StatementSimpleInternals.optionalLetType afterName
              with
          | invariant error => simp [typeResult] at result
          | reject typeFailure typeRejected =>
              simp only [typeResult] at result
              cases result
              exact .typeRejected marker.span markerParsed nameParsed
                (StatementSimpleInternals.optionalLetType_reject_ordinary_sound
                  typeResult)
          | ok type afterType =>
              simp only [typeResult] at result
              have typeParsed :=
                StatementSimpleInternals.optionalLetType_success_ordinary_sound
                  typeResult
              cases initializerResult :
                  StatementSimpleInternals.optionalLetInitializer expression
                    afterType with
              | invariant error => simp [initializerResult] at result
              | reject initializerFailure initializerRejected =>
                  simp only [initializerResult] at result
                  cases result
                  exact .initializerRejected marker.span markerParsed
                    nameParsed typeParsed
                    (StatementSimpleInternals.optionalLetInitializer_reject_ordinary_sound
                      expression expressionRejects expressionRejectSound
                        initializerResult)
              | ok initializer afterInitializer =>
                  simp only [initializerResult] at result
                  have initializerParsed :=
                    StatementSimpleInternals.optionalLetInitializer_success_ordinary_sound
                      expression expressionOrdinary expressionSuccessSound
                        initializerResult
                  cases semicolonResult : symbol .semicolon .statement
                      afterInitializer with
                  | invariant error => simp [semicolonResult] at result
                  | ok semicolon output =>
                      simp [semicolonResult, pure] at result
                  | reject semicolonFailure semicolonRejected =>
                      have semicolonRejectedEq := symbol_reject_state_eq
                        .semicolon .statement semicolonResult
                      subst semicolonRejected
                      simp only [semicolonResult] at result
                      cases result
                      exact .semicolonRejected marker.span markerParsed
                        nameParsed typeParsed initializerParsed
                        (symbol_reject_tokenKindAbsentAt .semicolon .statement
                          semicolonResult)

/-- Every executable `return` rejection records marker, optional-value, or
required-semicolon failure in parser priority order. -/
theorem returnStatement_reject_ordinary_sound
    (expression : Parser Expr)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSuccessSound : ∀ {input output : State} {value : Expr},
      expression input = .ok value output → expressionOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (expressionRejectSound : ∀ {input rejected : State}
      {failure : Failure}, expression input = .reject failure rejected →
        expressionRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : returnStatement expression input = .reject failure rejected) :
    DeclarativeGrammar.ReturnStatementRejects expressionOrdinary
      expressionRejects input.declarativeRemainder
        rejected.declarativeRemainder := by
  unfold returnStatement at result
  cases markerResult : keyword .returnKw .statement input with
  | invariant error => simp [bind, markerResult] at result
  | reject markerFailure markerRejected =>
      have markerRejectedEq := keyword_reject_state_eq .returnKw .statement
        markerResult
      subst markerRejected
      simp only [bind, markerResult] at result
      cases result
      exact .markerRejected
        (keyword_reject_tokenKindAbsentAt .returnKw .statement markerResult)
  | ok marker afterMarker =>
      simp only [bind, markerResult] at result
      have markerParsed := keyword_success_exactTokenParses .returnKw
        .statement markerResult
      cases valueResult : StatementSimpleInternals.optionalReturnValue
          expression afterMarker with
      | invariant error => simp [valueResult] at result
      | reject valueFailure valueRejected =>
          simp only [valueResult] at result
          cases result
          exact .valueRejected marker.span markerParsed
            (StatementSimpleInternals.optionalReturnValue_reject_ordinary_sound
              expression expressionRejects expressionRejectSound valueResult)
      | ok value afterValue =>
          simp only [valueResult] at result
          have valueParsed :=
            StatementSimpleInternals.optionalReturnValue_success_ordinary_sound
              expression expressionOrdinary expressionSuccessSound valueResult
          cases semicolonResult : symbol .semicolon .statement afterValue with
          | invariant error => simp [semicolonResult] at result
          | ok semicolon output => simp [semicolonResult, pure] at result
          | reject semicolonFailure semicolonRejected =>
              have semicolonRejectedEq := symbol_reject_state_eq .semicolon
                .statement semicolonResult
              subst semicolonRejected
              simp only [semicolonResult] at result
              cases result
              exact .semicolonRejected marker.span markerParsed valueParsed
                (symbol_reject_tokenKindAbsentAt .semicolon .statement
                  semicolonResult)

end Solcore.Syntax.Parser
