import Solcore.Syntax.DeclarativeNamedParameterTraceGrammar
import Solcore.Syntax.DeclarativeLambdaParameterTraceGrammar
import Solcore.Syntax.DeclarativeDelimitedTrailingTraceGrammar
import Solcore.Syntax.DeclarativeDelimitedTrailingRejectionTraceGrammar

/-! Parenthesized parameter lists allow empty lists and a trailing comma.
Their child traces include public parameter recovery and any committed reports.
These aliases describe the lists only, not signatures or lambda expressions. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

abbrev FunctionParametersTraceParses :=
  TrailingDelimitedListTraceParses .leftParen .rightParen true NamedParameterTraceParses

abbrev FunctionParametersTraceRejects :=
  TrailingDelimitedListTraceRejects .leftParen .rightParen true .parameter
    NamedParameterTraceParses NamedParameterTraceRejects

abbrev LambdaParametersTraceParses :=
  TrailingDelimitedListTraceParses .leftParen .rightParen true LambdaParameterTraceParses

abbrev LambdaParametersTraceRejects :=
  TrailingDelimitedListTraceRejects .leftParen .rightParen true .parameter
    LambdaParameterTraceParses LambdaParameterTraceRejects

end Solcore.Syntax.DeclarativeGrammar
