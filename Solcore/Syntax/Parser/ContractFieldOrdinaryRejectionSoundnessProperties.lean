import Solcore.Syntax.Parser.ContractFieldInitializerOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.CoreIdentifierOutcomeSoundnessProperties
import Solcore.Syntax.Parser.CoreTypeOutcomeSoundnessProperties

/-! Exact executable rejection for contract storage fields. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser
namespace ContractInternals

/-- Every executable field rejection records the first rejecting stage and its
exact remainder. -/
theorem contractField_reject_ordinaryOutcome_sound
    (expression : Parser Expr)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSuccessSound : ∀ {input output : State} {value : Expr},
      expression input = .ok value output →
        expressionOrdinary input.declarativeRemainder value
          output.declarativeRemainder)
    (expressionRejectSound : ∀ {input rejected : State}
      {failure : Failure}, expression input = .reject failure rejected →
        expressionRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : contractField expression input = .reject failure rejected) :
    DeclarativeGrammar.ContractFieldRejects expressionOrdinary
      expressionRejects input.declarativeRemainder
        rejected.declarativeRemainder := by
  unfold contractField at result
  cases nameResult : identifier .contractMember input with
  | invariant error => simp [bind, nameResult] at result
  | reject nameFailure nameRejected =>
      simp only [bind, nameResult] at result
      cases result
      exact .nameRejected (identifier_reject_sound .contractMember nameResult)
  | ok name afterName =>
      simp only [bind, nameResult] at result
      have nameParsed := identifier_success_sound .contractMember nameResult
      cases colonResult : symbol .colon .contractMember afterName with
      | invariant error => simp [colonResult] at result
      | reject colonFailure colonRejected =>
          have colonRejectedEq := symbol_reject_state_eq .colon
            .contractMember colonResult
          subst colonRejected
          simp only [colonResult] at result
          cases result
          exact .colonMissing nameParsed
            (symbol_reject_tokenKindAbsentAt .colon .contractMember
              colonResult)
      | ok colon afterColon =>
          simp only [colonResult] at result
          have colonParsed := symbol_success_exactTokenParses .colon
            .contractMember colonResult
          cases typeResult : typeExpr afterColon with
          | invariant error => simp [typeResult] at result
          | reject typeFailure typeRejected =>
              simp only [typeResult] at result
              cases result
              exact .typeRejected colon.span nameParsed colonParsed
                (typeExpr_ordinaryOutcome_sound.2 typeResult)
          | ok type afterType =>
              simp only [typeResult] at result
              have typeParsed := typeExpr_ordinaryOutcome_sound.1 typeResult
              cases initializerResult : optionalFieldInitializer expression
                  afterType with
              | invariant error => simp [initializerResult] at result
              | reject initializerFailure initializerRejected =>
                  simp only [initializerResult] at result
                  cases result
                  exact .initializerRejected colon.span nameParsed colonParsed
                    typeParsed
                    (optionalFieldInitializer_reject_ordinaryOutcome_sound
                      expression expressionRejects expressionRejectSound
                        initializerResult)
              | ok initializer afterInitializer =>
                  simp only [initializerResult] at result
                  have initializerParsed :=
                    optionalFieldInitializer_success_ordinaryOutcome_sound
                      expression expressionOrdinary expressionSuccessSound
                        initializerResult
                  cases semicolonResult : symbol .semicolon .contractMember
                      afterInitializer with
                  | invariant error => simp [semicolonResult] at result
                  | ok semicolon output =>
                      simp [semicolonResult, pure] at result
                  | reject semicolonFailure semicolonRejected =>
                      have semicolonRejectedEq := symbol_reject_state_eq
                        .semicolon .contractMember semicolonResult
                      subst semicolonRejected
                      simp only [semicolonResult] at result
                      cases result
                      exact .semicolonMissing colon.span nameParsed colonParsed
                        typeParsed initializerParsed
                        (symbol_reject_tokenKindAbsentAt .semicolon
                          .contractMember semicolonResult)

end ContractInternals
end Solcore.Syntax.Parser
