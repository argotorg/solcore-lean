import Solcore.Syntax.Parser.ContractFieldInitializerOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.CoreIdentifierOutcomeSoundnessProperties
import Solcore.Syntax.Parser.CoreTypeOutcomeSoundnessProperties

/-! Executable ordinary success for contract storage fields. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem bind_ok_components {alpha beta : Type}
    {first : Parser alpha} {next : alpha → Parser beta}
    {input output : State} {value : beta}
    (result : (first >>= next) input = .ok value output) :
    ∃ firstValue afterFirst,
      first input = .ok firstValue afterFirst ∧
        next firstValue afterFirst = .ok value output := by
  change (match first input with
    | .ok firstValue afterFirst => next firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value output at result
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      rw [firstResult] at result
      exact ⟨firstValue, afterFirst, rfl, result⟩
  | reject failure rejected => rw [firstResult] at result; contradiction
  | invariant error => rw [firstResult] at result; contradiction

namespace ContractInternals

/-- Every executable field success records its exact name, colon, public Core
type, prioritized optional initializer, semicolon, AST, span, and remainder. -/
theorem contractField_success_ordinaryOutcome_sound
    (expression : Parser Expr)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSuccessSound : ∀ {input output : State} {value : Expr},
      expression input = .ok value output →
        expressionOrdinary input.declarativeRemainder value
          output.declarativeRemainder)
    {input output : State} {field : ContractField}
    (result : contractField expression input = .ok field output) :
    DeclarativeGrammar.ContractFieldOrdinaryParses expressionOrdinary
      input.declarativeRemainder field output.declarativeRemainder := by
  unfold contractField at result
  rcases bind_ok_components result with
    ⟨name, afterName, nameResult, colonStage⟩
  rcases bind_ok_components colonStage with
    ⟨colon, afterColon, colonResult, typeStage⟩
  rcases bind_ok_components typeStage with
    ⟨type, afterType, typeResult, initializerStage⟩
  rcases bind_ok_components initializerStage with
    ⟨initializer, afterInitializer, initializerResult, semicolonStage⟩
  rcases bind_ok_components semicolonStage with
    ⟨semicolon, afterSemicolon, semicolonResult, finished⟩
  cases finished
  exact .parsed colon.span semicolon.span
    (identifier_success_sound .contractMember nameResult)
    (symbol_success_exactTokenParses .colon .contractMember colonResult)
    (typeExpr_ordinaryOutcome_sound.1 typeResult)
    (optionalFieldInitializer_success_ordinaryOutcome_sound expression
      expressionOrdinary expressionSuccessSound initializerResult)
    (symbol_success_exactTokenParses .semicolon .contractMember
      semicolonResult)

end ContractInternals
end Solcore.Syntax.Parser
