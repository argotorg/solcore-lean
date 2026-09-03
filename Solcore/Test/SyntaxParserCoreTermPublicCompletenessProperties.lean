import Solcore.Syntax.Parser.CoreTermPublicCompletenessProperties

/-! Compile-time consumers of exact ordinary grammar correspondence. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserCoreTermPublicCompletenessProperties

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @ordinary_success_iff_exists_ok
example := @ordinary_reject_iff_exists_reject
example := @expression_ordinary_success_iff
example := @expression_ordinary_reject_iff
example := @pattern_ordinary_success_iff
example := @pattern_ordinary_reject_iff
example := @statement_ordinary_success_iff
example := @statement_ordinary_reject_iff

example {input : State} (inputValid : input.ValidFor)
    {value : Expr} {remainder : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.CoreExpressionOrdinaryParses
      input.declarativeRemainder value remainder) :
    ∃ output, expression input = .ok value output ∧
      output.declarativeRemainder = remainder :=
  (expression_ordinary_success_iff inputValid).mp parsed

example {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder}
    (rejection : DeclarativeGrammar.CoreExpressionPublicRejects
      input.declarativeRemainder rejected) :
    ∃ failure output, expression input = .reject failure output ∧
      output.declarativeRemainder = rejected :=
  (expression_ordinary_reject_iff inputValid).mp rejection

example {input : State} (inputValid : input.ValidFor)
    {value : Pattern} {remainder : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.CorePatternOrdinaryParses
      input.declarativeRemainder value remainder) :
    ∃ output, pattern input = .ok value output ∧
      output.declarativeRemainder = remainder :=
  (pattern_ordinary_success_iff inputValid).mp parsed

example {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder}
    (rejection : DeclarativeGrammar.CorePatternPublicRejects
      input.declarativeRemainder rejected) :
    ∃ failure output, pattern input = .reject failure output ∧
      output.declarativeRemainder = rejected :=
  (pattern_ordinary_reject_iff inputValid).mp rejection

example {input : State} (inputValid : input.ValidFor)
    {value : Statement} {remainder : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.CoreStatementOrdinaryParses
      input.declarativeRemainder value remainder) :
    ∃ output, statement input = .ok value output ∧
      output.declarativeRemainder = remainder :=
  (statement_ordinary_success_iff inputValid).mp parsed

example {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder}
    (rejection : DeclarativeGrammar.CoreStatementPublicRejects
      input.declarativeRemainder rejected) :
    ∃ failure output, statement input = .reject failure output ∧
      output.declarativeRemainder = rejected :=
  (statement_ordinary_reject_iff inputValid).mp rejection

end Solcore.Test.SyntaxParserCoreTermPublicCompletenessProperties
