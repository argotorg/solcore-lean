import Solcore.Syntax.Parser.CoreBlockPublicExactnessProperties

/-! External consumers of unconditional exact Core terms and block boundaries. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserCoreTermExactnessProperties

open Solcore.Syntax
open Solcore.Syntax.Parser

example (fuel : Nat) : DeclarativeGrammar.ExactDeterministicOutcomeSpec
    (DeclarativeGrammar.CoreExpressionOrdinaryParsesWithFuel fuel)
    (DeclarativeGrammar.CoreExpressionRejectsWithFuel fuel) :=
  TermInternals.coreExpressionWithFuel_exactOutcomeSpec fuel

example : DeclarativeGrammar.ExactDeterministicOutcomeSpec
    DeclarativeGrammar.CoreExpressionOrdinaryParses
    DeclarativeGrammar.CoreExpressionPublicRejects :=
  expression_exactOutcomeSpec

-- Compare an executable success with any independently derived grammar result.
example {input output : State} {actual expected : Expr}
    {afterExpected : DeclarativeGrammar.Remainder}
    (result : expression input = .ok actual output)
    (expectedParsed : DeclarativeGrammar.CoreExpressionOrdinaryParses
      input.declarativeRemainder expected afterExpected) :
    actual = expected ∧ output.declarativeRemainder = afterExpected :=
  expression_exactOutcomeSpec.successResultUnique
    (expression_success_ordinary_sound result) expectedParsed

example {input output : State} {failure : Failure}
    {expected : DeclarativeGrammar.Remainder}
    (result : expression input = .reject failure output)
    (expectedRejected : DeclarativeGrammar.CoreExpressionPublicRejects
      input.declarativeRemainder expected) :
    output.declarativeRemainder = expected :=
  expression_exactOutcomeSpec.rejectOutputUnique
    (expression_reject_ordinary_sound result) expectedRejected

example := @TermInternals.coreExpressionWithFuel_success_result_unique
example := @TermInternals.coreExpressionWithFuel_reject_output_unique
example := @expression_success_result_unique
example := @expression_reject_output_unique

example (fuel : Nat) : DeclarativeGrammar.ExactDeterministicOutcomeSpec
    (DeclarativeGrammar.CorePatternOrdinaryParsesWithFuel fuel)
    (DeclarativeGrammar.CorePatternRejectsWithFuel fuel) :=
  TermInternals.corePatternWithFuel_exactOutcomeSpec fuel

example : DeclarativeGrammar.ExactDeterministicOutcomeSpec
    DeclarativeGrammar.CorePatternOrdinaryParses
    DeclarativeGrammar.CorePatternPublicRejects :=
  pattern_exactOutcomeSpec

-- Compare an executable success with any independently derived grammar result.
example {input output : State} {actual expected : Pattern}
    {afterExpected : DeclarativeGrammar.Remainder}
    (result : pattern input = .ok actual output)
    (expectedParsed : DeclarativeGrammar.CorePatternOrdinaryParses
      input.declarativeRemainder expected afterExpected) :
    actual = expected ∧ output.declarativeRemainder = afterExpected :=
  pattern_exactOutcomeSpec.successResultUnique
    (pattern_success_ordinary_sound result) expectedParsed

example {input output : State} {failure : Failure}
    {expected : DeclarativeGrammar.Remainder}
    (result : pattern input = .reject failure output)
    (expectedRejected : DeclarativeGrammar.CorePatternPublicRejects
      input.declarativeRemainder expected) :
    output.declarativeRemainder = expected :=
  pattern_exactOutcomeSpec.rejectOutputUnique
    (pattern_reject_ordinary_sound result) expectedRejected

example := @TermInternals.corePatternWithFuel_success_result_unique
example := @TermInternals.corePatternWithFuel_reject_output_unique
example := @pattern_success_result_unique
example := @pattern_reject_output_unique

example (fuel : Nat) : DeclarativeGrammar.ExactDeterministicOutcomeSpec
    (DeclarativeGrammar.CoreStatementOrdinaryParsesWithFuel fuel)
    (DeclarativeGrammar.CoreStatementRejectsWithFuel fuel) :=
  TermInternals.coreStatementWithFuel_exactOutcomeSpec fuel

example : DeclarativeGrammar.ExactDeterministicOutcomeSpec
    DeclarativeGrammar.CoreStatementOrdinaryParses
    DeclarativeGrammar.CoreStatementPublicRejects :=
  statement_exactOutcomeSpec

-- Compare an executable success with any independently derived grammar result.
example {input output : State} {actual expected : Statement}
    {afterExpected : DeclarativeGrammar.Remainder}
    (result : statement input = .ok actual output)
    (expectedParsed : DeclarativeGrammar.CoreStatementOrdinaryParses
      input.declarativeRemainder expected afterExpected) :
    actual = expected ∧ output.declarativeRemainder = afterExpected :=
  statement_exactOutcomeSpec.successResultUnique
    (statement_success_ordinary_sound result) expectedParsed

example {input output : State} {failure : Failure}
    {expected : DeclarativeGrammar.Remainder}
    (result : statement input = .reject failure output)
    (expectedRejected : DeclarativeGrammar.CoreStatementPublicRejects
      input.declarativeRemainder expected) :
    output.declarativeRemainder = expected :=
  statement_exactOutcomeSpec.rejectOutputUnique
    (statement_reject_ordinary_sound result) expectedRejected

example := @TermInternals.coreStatementWithFuel_success_result_unique
example := @TermInternals.coreStatementWithFuel_reject_output_unique
example := @statement_success_result_unique
example := @statement_reject_output_unique

example (policy : TailExpressionPolicy) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.CoreBlockPublicOrdinaryParses policy.declarative)
      (DeclarativeGrammar.CoreBlockPublicRejects policy.declarative) :=
  block_exactOutcomeSpec policy

example (policy : TailExpressionPolicy)
    {input output : State} {actual expected : Block}
    {afterExpected : DeclarativeGrammar.Remainder}
    (result : block policy input = .ok actual output)
    (expectedParsed : DeclarativeGrammar.CoreBlockPublicOrdinaryParses
      policy.declarative input.declarativeRemainder expected afterExpected) :
    actual = expected ∧ output.declarativeRemainder = afterExpected :=
  (block_exactOutcomeSpec policy).successResultUnique
    (block_success_ordinary_sound policy result) expectedParsed

example (policy : TailExpressionPolicy)
    {input output : State} {failure : Failure}
    {expected : DeclarativeGrammar.Remainder}
    (result : block policy input = .reject failure output)
    (expectedRejected : DeclarativeGrammar.CoreBlockPublicRejects
      policy.declarative input.declarativeRemainder expected) :
    output.declarativeRemainder = expected :=
  (block_exactOutcomeSpec policy).rejectOutputUnique
    (block_reject_ordinary_sound policy result) expectedRejected

example := @block_success_result_unique
example := @block_reject_output_unique

example (policy : TailExpressionPolicy) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.IsolatedCoreBlockPublicOrdinaryParses policy.declarative)
      (DeclarativeGrammar.IsolatedCoreBlockPublicRejects policy.declarative) :=
  isolatedCoreBlockPublic_exactOutcomeSpec policy

example (policy : TailExpressionPolicy)
    {input output : State} {actual expected : Block}
    {afterExpected : DeclarativeGrammar.Remainder}
    (result : isolateBlock (block policy) input = .ok actual output)
    (expectedParsed : DeclarativeGrammar.IsolatedCoreBlockPublicOrdinaryParses
      policy.declarative input.declarativeRemainder expected afterExpected) :
    actual = expected ∧ output.declarativeRemainder = afterExpected :=
  (isolatedCoreBlockPublic_exactOutcomeSpec policy).successResultUnique
    (isolatedCoreBlockPublic_success_ordinary_sound policy result) expectedParsed

example (policy : TailExpressionPolicy)
    {input output : State} {failure : Failure}
    {expected : DeclarativeGrammar.Remainder}
    (result : isolateBlock (block policy) input = .reject failure output)
    (expectedRejected : DeclarativeGrammar.IsolatedCoreBlockPublicRejects
      policy.declarative input.declarativeRemainder expected) :
    output.declarativeRemainder = expected :=
  (isolatedCoreBlockPublic_exactOutcomeSpec policy).rejectOutputUnique
    (isolatedCoreBlockPublic_reject_ordinary_sound policy result) expectedRejected

example := @isolatedCoreBlockPublic_success_result_unique
example := @isolatedCoreBlockPublic_reject_output_unique

end Solcore.Test.SyntaxParserCoreTermExactnessProperties
