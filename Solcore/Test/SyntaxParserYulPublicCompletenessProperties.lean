import Solcore.Syntax.Parser.YulPublicCompletenessProperties

/-! Independent forward and reverse consumers for public Yul completeness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserYulPublicCompletenessProperties

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @yulExpression_ordinary_success_iff
example := @yulExpression_ordinary_reject_iff

example {input : State} (inputValid : input.ValidFor)
    {value : YulExpr} {remainder : DeclarativeGrammar.Remainder}
    (expected : DeclarativeGrammar.YulExpressionOrdinaryParses input.declarativeRemainder value remainder) :
    ∃ output, yulExpression input = .ok value output ∧
      output.declarativeRemainder = remainder :=
  (yulExpression_ordinary_success_iff inputValid).mp expected

example {input output : State} (inputValid : input.ValidFor)
    {value : YulExpr} {remainder : DeclarativeGrammar.Remainder}
    (result : yulExpression input = .ok value output)
    (remainderEq : output.declarativeRemainder = remainder) :
    DeclarativeGrammar.YulExpressionOrdinaryParses input.declarativeRemainder value remainder :=
  (yulExpression_ordinary_success_iff inputValid).mpr ⟨output, result, remainderEq⟩

example {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder}
    (expected : DeclarativeGrammar.YulExpressionPublicRejects input.declarativeRemainder rejected) :
    ∃ failure output, yulExpression input = .reject failure output ∧
      output.declarativeRemainder = rejected :=
  (yulExpression_ordinary_reject_iff inputValid).mp expected

example {input output : State} (inputValid : input.ValidFor)
    {failure : Failure} {rejected : DeclarativeGrammar.Remainder}
    (result : yulExpression input = .reject failure output)
    (remainderEq : output.declarativeRemainder = rejected) :
    DeclarativeGrammar.YulExpressionPublicRejects input.declarativeRemainder rejected :=
  (yulExpression_ordinary_reject_iff inputValid).mpr ⟨failure, output, result, remainderEq⟩

example := @yulStatement_ordinary_success_iff
example := @yulStatement_ordinary_reject_iff

example {input : State} (inputValid : input.ValidFor)
    {value : YulStmt} {remainder : DeclarativeGrammar.Remainder}
    (expected : DeclarativeGrammar.YulStatementOrdinaryParses input.declarativeRemainder value remainder) :
    ∃ output, yulStatement input = .ok value output ∧
      output.declarativeRemainder = remainder :=
  (yulStatement_ordinary_success_iff inputValid).mp expected

example {input output : State} (inputValid : input.ValidFor)
    {value : YulStmt} {remainder : DeclarativeGrammar.Remainder}
    (result : yulStatement input = .ok value output)
    (remainderEq : output.declarativeRemainder = remainder) :
    DeclarativeGrammar.YulStatementOrdinaryParses input.declarativeRemainder value remainder :=
  (yulStatement_ordinary_success_iff inputValid).mpr ⟨output, result, remainderEq⟩

example {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder}
    (expected : DeclarativeGrammar.YulStatementPublicRejects input.declarativeRemainder rejected) :
    ∃ failure output, yulStatement input = .reject failure output ∧
      output.declarativeRemainder = rejected :=
  (yulStatement_ordinary_reject_iff inputValid).mp expected

example {input output : State} (inputValid : input.ValidFor)
    {failure : Failure} {rejected : DeclarativeGrammar.Remainder}
    (result : yulStatement input = .reject failure output)
    (remainderEq : output.declarativeRemainder = rejected) :
    DeclarativeGrammar.YulStatementPublicRejects input.declarativeRemainder rejected :=
  (yulStatement_ordinary_reject_iff inputValid).mpr ⟨failure, output, result, remainderEq⟩

example := @yulBody_ordinary_success_iff
example := @yulBody_ordinary_reject_iff

example {input : State} (inputValid : input.ValidFor)
    {value : YulParsedBlock} {remainder : DeclarativeGrammar.Remainder}
    (expected : DeclarativeGrammar.YulBodyOrdinaryParses input.declarativeRemainder value.span value.body remainder) :
    ∃ output, yulBody input = .ok value output ∧
      output.declarativeRemainder = remainder :=
  (yulBody_ordinary_success_iff inputValid).mp expected

example {input output : State} (inputValid : input.ValidFor)
    {value : YulParsedBlock} {remainder : DeclarativeGrammar.Remainder}
    (result : yulBody input = .ok value output)
    (remainderEq : output.declarativeRemainder = remainder) :
    DeclarativeGrammar.YulBodyOrdinaryParses input.declarativeRemainder value.span value.body remainder :=
  (yulBody_ordinary_success_iff inputValid).mpr ⟨output, result, remainderEq⟩

example {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder}
    (expected : DeclarativeGrammar.YulBodyRejects input.declarativeRemainder rejected) :
    ∃ failure output, yulBody input = .reject failure output ∧
      output.declarativeRemainder = rejected :=
  (yulBody_ordinary_reject_iff inputValid).mp expected

example {input output : State} (inputValid : input.ValidFor)
    {failure : Failure} {rejected : DeclarativeGrammar.Remainder}
    (result : yulBody input = .reject failure output)
    (remainderEq : output.declarativeRemainder = rejected) :
    DeclarativeGrammar.YulBodyRejects input.declarativeRemainder rejected :=
  (yulBody_ordinary_reject_iff inputValid).mpr ⟨failure, output, result, remainderEq⟩

example := @yulExpression_boundary_reject_iff
example := @yulStatement_boundary_reject_iff

end Solcore.Test.SyntaxParserYulPublicCompletenessProperties
