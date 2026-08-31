import Solcore.Syntax.Parser.Operator

/-! External visibility checks for the operator-parts parser. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserOperatorInternals

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @OperatorInternals.operatorParts

example (context : ParseContext) (partsRev : List String) (state : State) :
    OperatorInternals.operatorParts context 0 partsRev state =
      .invariant (.fuelExhausted .topLevel state.currentSpan) :=
  rfl

end Solcore.Test.SyntaxParserOperatorInternals
