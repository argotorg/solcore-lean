import Solcore.Syntax.Parser.CoreTypeCompletenessProperties
import Solcore.Syntax.Parser.CoreLambdaParameterCompletenessProperties
import Solcore.Syntax.Parser.CoreBlockPublicCompletenessProperties

/-! Compile-time consumers for type, lambda parameter, and policy-preserving
raw and isolated block grammar correspondence. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserCoreAuxiliaryCompletenessProperties

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @typeExpr_ordinary_success_iff
example := @typeExpr_ordinary_reject_iff
example := @lambdaParameter_ordinary_success_iff
example := @lambdaParameter_ordinary_reject_iff
example := @block_ordinary_success_iff
example := @block_ordinary_reject_iff
example := @isolatedCoreBlockPublic_ordinary_success_iff
example := @isolatedCoreBlockPublic_ordinary_reject_iff

example {input : State} (inputValid : input.ValidFor)
    {value : TypeExpr} {remainder : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.TypeExprOrdinaryParses
      input.declarativeRemainder value remainder) :
    ∃ output, typeExpr input = .ok value output ∧
      output.declarativeRemainder = remainder :=
  (typeExpr_ordinary_success_iff inputValid).mp parsed

example {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder}
    (rejection : DeclarativeGrammar.TypeExprRejects
      input.declarativeRemainder rejected) :
    ∃ failure output, typeExpr input = .reject failure output ∧
      output.declarativeRemainder = rejected :=
  (typeExpr_ordinary_reject_iff inputValid).mp rejection

example {input : State} (inputValid : input.ValidFor)
    {value : LambdaParameter} {remainder : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.LambdaParameterOrdinaryParses
      DeclarativeGrammar.TypeExprOrdinaryParses DeclarativeGrammar.TypeExprRejects
        input.declarativeRemainder value remainder) :
    ∃ output, lambdaParameter input = .ok value output ∧
      output.declarativeRemainder = remainder :=
  (lambdaParameter_ordinary_success_iff inputValid).mp parsed

example {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder}
    (rejection : DeclarativeGrammar.LambdaParameterRejects
      DeclarativeGrammar.TypeExprRejects input.declarativeRemainder rejected) :
    ∃ failure output, lambdaParameter input = .reject failure output ∧
      output.declarativeRemainder = rejected :=
  (lambdaParameter_ordinary_reject_iff inputValid).mp rejection

example (policy : TailExpressionPolicy)
    {input : State} (inputValid : input.ValidFor)
    {value : Block} {remainder : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.CoreBlockPublicOrdinaryParses policy.declarative
      input.declarativeRemainder value remainder) :
    ∃ output, block policy input = .ok value output ∧
      output.declarativeRemainder = remainder :=
  (block_ordinary_success_iff policy inputValid).mp parsed

example (policy : TailExpressionPolicy)
    {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder}
    (rejection : DeclarativeGrammar.CoreBlockPublicRejects policy.declarative
      input.declarativeRemainder rejected) :
    ∃ failure output, block policy input = .reject failure output ∧
      output.declarativeRemainder = rejected :=
  (block_ordinary_reject_iff policy inputValid).mp rejection

example (policy : TailExpressionPolicy)
    {input : State} (inputValid : input.ValidFor)
    {value : Block} {remainder : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.IsolatedCoreBlockPublicOrdinaryParses
      policy.declarative input.declarativeRemainder value remainder) :
    ∃ output, isolateBlock (block policy) input = .ok value output ∧
      output.declarativeRemainder = remainder :=
  (isolatedCoreBlockPublic_ordinary_success_iff policy inputValid).mp parsed

example (policy : TailExpressionPolicy)
    {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder}
    (rejection : DeclarativeGrammar.IsolatedCoreBlockPublicRejects
      policy.declarative input.declarativeRemainder rejected) :
    ∃ failure output, isolateBlock (block policy) input = .reject failure output ∧
      output.declarativeRemainder = rejected :=
  (isolatedCoreBlockPublic_ordinary_reject_iff policy inputValid).mp rejection

end Solcore.Test.SyntaxParserCoreAuxiliaryCompletenessProperties
