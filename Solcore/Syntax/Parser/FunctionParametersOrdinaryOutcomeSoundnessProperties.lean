import Solcore.Syntax.DeclarativeFunctionParametersExactnessProperties
import Solcore.Syntax.Parser.CoreTypeOutcomeSoundnessProperties
import Solcore.Syntax.Parser.DelimitedAllowEmptySoundnessProperties
import Solcore.Syntax.Parser.DelimitedListRejectionSoundnessProperties
import Solcore.Syntax.Parser.FunctionParameterOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.Signature

/-! Executable ordinary outcomes for recovery-aware function parameters. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every successful parameter list retains exact delimiters, order, recovery
outcomes, and final remainder. -/
theorem functionParameters_success_ordinaryOutcome_sound
    {input output : State}
    {parameters : DelimitedList FunctionParameter}
    (result : functionParameters input = .ok parameters output) :
    DeclarativeGrammar.FunctionParametersOrdinaryParses
      input.declarativeRemainder parameters output.declarativeRemainder := by
  unfold functionParameters at result
  unfold DeclarativeGrammar.FunctionParametersOrdinaryParses
  exact delimited_allowEmpty_trailing_success_sound .leftParen .rightParen
    namedParameter
    (DeclarativeGrammar.FunctionParameterOrdinaryParses
      DeclarativeGrammar.TypeExprOrdinaryParses
      DeclarativeGrammar.TypeExprRejects)
    .parameter .topLevel
    (namedParameter_success_ordinaryOutcome_sound
      DeclarativeGrammar.TypeExprOrdinaryParses
      DeclarativeGrammar.TypeExprRejects typeExpr_ordinaryOutcome_sound.1
      typeExpr_ordinaryOutcome_sound.2)
    namedParameter_preservesTokenWindow result

/-- Every rejected parameter list records its exact delimiter or nested
named-parameter rejection endpoint. -/
theorem functionParameters_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : functionParameters input = .reject failure rejected) :
    DeclarativeGrammar.FunctionParametersRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold functionParameters at result
  exact delimited_reject_sound .leftParen .rightParen true namedParameter
    (DeclarativeGrammar.FunctionParameterOrdinaryParses
      DeclarativeGrammar.TypeExprOrdinaryParses
      DeclarativeGrammar.TypeExprRejects)
    (DeclarativeGrammar.FunctionParameterRejects
      DeclarativeGrammar.TypeExprRejects)
    .parameter .topLevel
    (namedParameter_success_ordinaryOutcome_sound
      DeclarativeGrammar.TypeExprOrdinaryParses
      DeclarativeGrammar.TypeExprRejects typeExpr_ordinaryOutcome_sound.1
      typeExpr_ordinaryOutcome_sound.2)
    (namedParameter_reject_ordinaryOutcome_sound
      DeclarativeGrammar.TypeExprRejects typeExpr_ordinaryOutcome_sound.2)
    result

/-- Package executable function-parameter-list success and rejection. -/
theorem functionParameters_ordinaryOutcome_sound :
    (∀ {input output : State}
      {parameters : DelimitedList FunctionParameter},
      functionParameters input = .ok parameters output →
        DeclarativeGrammar.FunctionParametersOrdinaryParses
          input.declarativeRemainder parameters output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      functionParameters input = .reject failure rejected →
        DeclarativeGrammar.FunctionParametersRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨functionParameters_success_ordinaryOutcome_sound,
    functionParameters_reject_ordinaryOutcome_sound⟩

/-- Re-export the deterministic parser-independent list outcome contract. -/
theorem functionParameters_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.FunctionParametersOrdinaryParses
      DeclarativeGrammar.FunctionParametersRejects :=
  DeclarativeGrammar.functionParametersDeterministicOutcomeSpec

/-- Re-export full function-parameter-list AST and rejection-endpoint
functionality. -/
theorem functionParameters_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.FunctionParametersOrdinaryParses
      DeclarativeGrammar.FunctionParametersRejects :=
  DeclarativeGrammar.functionParametersExactOutcomeSpec

/-- Two successful executable reflections have the same parameter-list AST
and final declarative remainder. -/
theorem functionParameters_success_result_unique
    {input leftOutput rightOutput : State}
    {left right : DelimitedList FunctionParameter}
    (leftResult : functionParameters input = .ok left leftOutput)
    (rightResult : functionParameters input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.FunctionParametersOrdinaryParses.result_unique
    (functionParameters_success_ordinaryOutcome_sound leftResult)
    (functionParameters_success_ordinaryOutcome_sound rightResult)

/-- Two rejected executable reflections have the same first failing
declarative endpoint. -/
theorem functionParameters_reject_output_unique
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : functionParameters input = .reject leftFailure leftOutput)
    (rightResult : functionParameters input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.FunctionParametersRejects.output_unique
    (functionParameters_reject_ordinaryOutcome_sound leftResult)
    (functionParameters_reject_ordinaryOutcome_sound rightResult)

end Solcore.Syntax.Parser
