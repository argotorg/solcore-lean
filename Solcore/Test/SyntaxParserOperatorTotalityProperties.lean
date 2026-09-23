import Solcore.Syntax.Parser.Operator

/-! External consumers for operator-selector totality contracts. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserOperatorTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.OperatorInternals

example := @operatorParts_ordinary_of_remainingCount_lt
example := @operatorParts_ne_invariant_of_remainingCount_lt
example := @operatorParts_production_ordinary
example := @operatorParts_production_ne_invariant
example := @operatorSelector_ordinary
example := @operatorSelector_ne_invariant
example := @selectorName_ordinary
example := @selectorName_ne_invariant
example := @operatorSelector_elementTotalityContract
example := @selectorName_elementTotalityContract

example (context : ParseContext) :
    ElementTotalityContract (selectorName context) :=
  selectorName_elementTotalityContract context

end Solcore.Test.SyntaxParserOperatorTotalityProperties
