import Solcore.Syntax.DeclarativeDelimitedTrailingExactnessProperties
import Solcore.Syntax.DeclarativeFunctionParameterExactnessProperties
import Solcore.Syntax.DeclarativeFunctionParametersOutcomeProperties

/-! Exact values for recovery-aware function-parameter lists. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Recovery-aware function-parameter lists have fully exact outcomes. -/
theorem functionParametersExactOutcomeSpec :
    ExactDeterministicOutcomeSpec FunctionParametersOrdinaryParses
      FunctionParametersRejects :=
  trailingDelimitedListExactOutcomeSpec .leftParen .rightParen
    (functionParameterExactOutcomeSpec typeExprExactOutcomeSpec)

/-- A complete function-parameter list fixes its AST and final remainder. -/
theorem FunctionParametersOrdinaryParses.result_unique
    {input : Remainder}
    {left right : DelimitedList Syntax.FunctionParameter}
    {afterLeft afterRight : Remainder}
    (leftParsed : FunctionParametersOrdinaryParses input left afterLeft)
    (rightParsed : FunctionParametersOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  functionParametersExactOutcomeSpec.successResultUnique leftParsed
    rightParsed

/-- A complete function-parameter list fixes its delimited-list AST. -/
theorem FunctionParametersOrdinaryParses.value_unique
    {input : Remainder}
    {left right : DelimitedList Syntax.FunctionParameter}
    {afterLeft afterRight : Remainder}
    (leftParsed : FunctionParametersOrdinaryParses input left afterLeft)
    (rightParsed : FunctionParametersOrdinaryParses input right afterRight) :
    left = right :=
  functionParametersExactOutcomeSpec.successValueUnique leftParsed
    rightParsed

/-- Function-parameter-list rejection has one exact failing endpoint. -/
theorem FunctionParametersRejects.output_unique
    {input left right : Remainder}
    (leftRejected : FunctionParametersRejects input left)
    (rightRejected : FunctionParametersRejects input right) : left = right :=
  functionParametersExactOutcomeSpec.rejectOutputUnique leftRejected
    rightRejected

end Solcore.Syntax.DeclarativeGrammar
