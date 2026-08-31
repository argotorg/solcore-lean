import Solcore.Syntax.Parser.ExpressionUnaryTotalityProperties

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserExpressionUnaryTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.ExpressionInternals

example := @unaryOperators_exists_ok_of_remainingCount_lt
example := @unaryOperators_ordinary_of_remainingCount_lt
example := @unaryOperators_ne_invariant_of_remainingCount_lt
example := @unaryOperators_production_exists_ok
example := @unaryOperators_production_ordinary
example := @unaryOperators_production_invariantFreeOnValid
example := @unaryOperators_production_ne_invariant

example (operatorsRev : List (Located UnaryOp)) :
    Parser.Ordinary (fun state =>
      unaryOperators (state.remainingCount + 1) operatorsRev state) :=
  unaryOperators_production_ordinary operatorsRev

end Solcore.Test.SyntaxParserExpressionUnaryTotalityProperties
