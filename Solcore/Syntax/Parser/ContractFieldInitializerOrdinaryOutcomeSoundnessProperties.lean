import Solcore.Syntax.DeclarativeContractFieldExactnessProperties
import Solcore.Syntax.Parser.Contract
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties

/-! Executable ordinary outcomes for optional contract-field initializers. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser
namespace ContractInternals

/-- Every successful optional initializer preserves the exact `=` lookahead
priority and the supplied expression success relation. -/
theorem optionalFieldInitializer_success_ordinaryOutcome_sound
    (expression : Parser Expr)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSuccessSound : ∀ {input output : State} {value : Expr},
      expression input = .ok value output →
        expressionOrdinary input.declarativeRemainder value
          output.declarativeRemainder)
    {input output : State} {initializer : Option Expr}
    (result : optionalFieldInitializer expression input =
      .ok initializer output) :
    DeclarativeGrammar.OptionalContractFieldInitializerOrdinaryParses
      expressionOrdinary input.declarativeRemainder initializer
        output.declarativeRemainder := by
  unfold optionalFieldInitializer getState at result
  simp only [bind] at result
  by_cases present : isSymbol input .equal
  · rcases Solcore.Syntax.Parser.symbol_eq_ok_of_isSymbol_eq_true
      .equal .contractMember present
      with ⟨equal, equalResult⟩
    simp only [present, if_true, equalResult] at result
    cases expressionResult : expression
        { input with cursor := input.cursor + 1 } with
    | invariant error => simp [expressionResult] at result
    | reject failure rejected => simp [expressionResult] at result
    | ok value afterValue =>
        simp only [expressionResult, pure] at result
        cases result
        exact .present equal.span
          (symbol_success_exactTokenParses .equal .contractMember equalResult)
          (expressionSuccessSound expressionResult)
  · have absent : isSymbol input .equal = false :=
      Bool.eq_false_iff.mpr present
    simp only [absent, Bool.false_eq_true, if_false, pure] at result
    cases result
    exact .absent (symbolAbsentAt_of_isSymbol_eq_false .equal absent)

/-- Every optional-initializer rejection follows a present exact `=` and the
supplied expression rejection; the absent branch cannot reject. -/
theorem optionalFieldInitializer_reject_ordinaryOutcome_sound
    (expression : Parser Expr)
    (expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (expressionRejectSound : ∀ {input rejected : State} {failure : Failure},
      expression input = .reject failure rejected →
        expressionRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : optionalFieldInitializer expression input =
      .reject failure rejected) :
    DeclarativeGrammar.OptionalContractFieldInitializerRejects
      expressionRejects input.declarativeRemainder
        rejected.declarativeRemainder := by
  unfold optionalFieldInitializer getState at result
  simp only [bind] at result
  by_cases present : isSymbol input .equal
  · rcases Solcore.Syntax.Parser.symbol_eq_ok_of_isSymbol_eq_true
      .equal .contractMember present
      with ⟨equal, equalResult⟩
    simp only [present, if_true, equalResult] at result
    cases expressionResult : expression
        { input with cursor := input.cursor + 1 } with
    | invariant error => simp [expressionResult] at result
    | ok value afterValue => simp [expressionResult, pure] at result
    | reject expressionFailure expressionRejected =>
        simp only [expressionResult] at result
        cases result
        exact .expressionRejected equal.span
          (symbol_success_exactTokenParses .equal .contractMember equalResult)
          (expressionRejectSound expressionResult)
  · have absent : isSymbol input .equal = false :=
      Bool.eq_false_iff.mpr present
    simp [absent, pure] at result

/-- Package exact executable optional-initializer success and rejection. -/
theorem optionalFieldInitializer_ordinaryOutcome_sound
    (expression : Parser Expr)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSuccessSound : ∀ {input output : State} {value : Expr},
      expression input = .ok value output →
        expressionOrdinary input.declarativeRemainder value
          output.declarativeRemainder)
    (expressionRejectSound : ∀ {input rejected : State} {failure : Failure},
      expression input = .reject failure rejected →
        expressionRejects input.declarativeRemainder
          rejected.declarativeRemainder) :
    (∀ {input output : State} {initializer : Option Expr},
      optionalFieldInitializer expression input = .ok initializer output →
        DeclarativeGrammar.OptionalContractFieldInitializerOrdinaryParses
          expressionOrdinary input.declarativeRemainder initializer
            output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      optionalFieldInitializer expression input = .reject failure rejected →
        DeclarativeGrammar.OptionalContractFieldInitializerRejects
          expressionRejects input.declarativeRemainder
            rejected.declarativeRemainder) :=
  ⟨optionalFieldInitializer_success_ordinaryOutcome_sound expression
      expressionOrdinary expressionSuccessSound,
    optionalFieldInitializer_reject_ordinaryOutcome_sound expression
      expressionRejects expressionRejectSound⟩

/-- Re-export the parameterized deterministic optional-initializer contract. -/
theorem optionalFieldInitializer_ordinaryOutcomeSpec
    {expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop}
    {expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (expressionOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      expressionOrdinary expressionRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.OptionalContractFieldInitializerOrdinaryParses
        expressionOrdinary)
      (DeclarativeGrammar.OptionalContractFieldInitializerRejects
        expressionRejects) :=
  DeclarativeGrammar.optionalContractFieldInitializerDeterministicOutcomeSpec
    expressionOutcomes

/-- Re-export exact optional-initializer outcomes from an exact expression
contract. -/
theorem optionalFieldInitializer_exactOutcomeSpec
    {expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop}
    {expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (expressionOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      expressionOrdinary expressionRejects) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.OptionalContractFieldInitializerOrdinaryParses
        expressionOrdinary)
      (DeclarativeGrammar.OptionalContractFieldInitializerRejects
        expressionRejects) :=
  DeclarativeGrammar.optionalContractFieldInitializerExactOutcomeSpec
    expressionOutcomes

/-- Under an exact expression contract, two executable initializer successes
have the same value and declarative remainder. -/
theorem optionalFieldInitializer_success_result_unique
    (expression : Parser Expr)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (expressionOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      expressionOrdinary expressionRejects)
    (expressionSuccessSound : ∀ {input output : State} {value : Expr},
      expression input = .ok value output →
        expressionOrdinary input.declarativeRemainder value
          output.declarativeRemainder)
    {input leftOutput rightOutput : State}
    {left right : Option Expr}
    (leftResult : optionalFieldInitializer expression input =
      .ok left leftOutput)
    (rightResult : optionalFieldInitializer expression input =
      .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (optionalFieldInitializer_exactOutcomeSpec expressionOutcomes)
    |>.successResultUnique
      (optionalFieldInitializer_success_ordinaryOutcome_sound expression
        expressionOrdinary expressionSuccessSound leftResult)
      (optionalFieldInitializer_success_ordinaryOutcome_sound expression
        expressionOrdinary expressionSuccessSound rightResult)

/-- Under an exact expression contract, two executable initializer
rejections have the same declarative endpoint. -/
theorem optionalFieldInitializer_reject_output_unique
    (expression : Parser Expr)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (expressionOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      expressionOrdinary expressionRejects)
    (expressionRejectSound : ∀ {input rejected : State}
      {failure : Failure}, expression input = .reject failure rejected →
        expressionRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : optionalFieldInitializer expression input =
      .reject leftFailure leftOutput)
    (rightResult : optionalFieldInitializer expression input =
      .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (optionalFieldInitializer_exactOutcomeSpec expressionOutcomes)
    |>.rejectOutputUnique
      (optionalFieldInitializer_reject_ordinaryOutcome_sound expression
        expressionRejects expressionRejectSound leftResult)
      (optionalFieldInitializer_reject_ordinaryOutcome_sound expression
        expressionRejects expressionRejectSound rightResult)

end ContractInternals
end Solcore.Syntax.Parser
