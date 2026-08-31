import Solcore.Syntax.Parser.ContractFieldTotalityProperties

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserContractFieldTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.ContractInternals

example (expressionParser : Parser Expr)
    (expressionFree : Parser.InvariantFreeOnValid expressionParser) :
    Parser.InvariantFreeOnValid
      (optionalFieldInitializer expressionParser) :=
  optionalFieldInitializer_invariantFreeOnValid expressionParser expressionFree

example (expressionParser : Parser Expr)
    (expressionFree : Parser.InvariantFreeOnValid expressionParser)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    contractField expressionParser input ≠ .invariant error :=
  contractField_ne_invariant expressionParser expressionFree input inputValid
    error

end Solcore.Test.SyntaxParserContractFieldTotalityProperties
