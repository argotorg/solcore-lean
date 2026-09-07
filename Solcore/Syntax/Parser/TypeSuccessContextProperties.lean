import Solcore.Syntax.Parser.NamedTypeTraceProperties
import Solcore.Syntax.Parser.MappingTypeTraceProperties
import Solcore.Syntax.Parser.ComptimeTypeSuccessTraceProperties
import Solcore.Syntax.Parser.ProxyTypeSuccessTraceProperties
import Solcore.Syntax.Parser.TupleTypeSuccessTraceProperties
import Solcore.Syntax.Parser.FunctionTypeSuccessTraceProperties

/-! Successful recursive types retain their source and complete active window
on every state, without a validity assumption. This frame alone is not a
recursive diagnostic-trace soundness or completeness theorem. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

theorem typeExprWithFuel_success_context (fuel : Nat) :
    ParserSuccessContext (typeExprWithFuel fuel) := by
  induction fuel with
  | zero =>
      intro input output value result
      simp [typeExprWithFuel] at result
  | succ fuel ih =>
      intro input output value result
      simp only [typeExprWithFuel] at result
      split at result
      · exact parseFunctionType_success_context ih result
      · split at result
        · exact parseComptimeType_success_context ih result
        · split at result
          · exact parseMappingType_success_context ih result
          · split at result
            · exact parseProxyType_success_context ih result
            · split at result
              · exact parseTupleType_success_context ih result
              · split at result
                · exact parseNamedType_success_context ih result
                · simp [rejectAt] at result

theorem typeExpr_success_context : ParserSuccessContext typeExpr := by
  intro input output value result
  exact typeExprWithFuel_success_context (input.remainingCount + 1) result

end Solcore.Syntax.Parser
