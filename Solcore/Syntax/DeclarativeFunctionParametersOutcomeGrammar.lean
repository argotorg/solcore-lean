import Solcore.Syntax.DeclarativeCoreTypeOutcomeGrammar
import Solcore.Syntax.DeclarativeFunctionParameterOutcomeGrammar

/-!
Parser-independent ordinary outcomes for recovery-aware named function
parameter lists.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Possibly empty, allow-trailing named parameters, including exact Core and
recovery outcomes under the canonical public type relations. -/
def FunctionParametersOrdinaryParses
    (input : Remainder) (parameters : DelimitedList Syntax.FunctionParameter)
    (output : Remainder) : Prop :=
  TrailingDelimitedListParses .leftParen .rightParen
    (FunctionParameterOrdinaryParses TypeExprOrdinaryParses TypeExprRejects)
      input parameters output

/-- Exact rejection of the recovery-aware named-parameter list. -/
abbrev FunctionParametersRejects :=
  DelimitedListRejects .leftParen .rightParen true true
    (FunctionParameterOrdinaryParses TypeExprOrdinaryParses TypeExprRejects)
    (FunctionParameterRejects TypeExprRejects)

end Solcore.Syntax.DeclarativeGrammar
