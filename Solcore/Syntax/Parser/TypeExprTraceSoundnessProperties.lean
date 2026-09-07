import Solcore.Syntax.DeclarativeTypeExprTraceInductionProperties
import Solcore.Syntax.Parser.TypeDispatchSuccessTraceProperties
import Solcore.Syntax.Parser.TypeDispatchRejectionTraceProperties

/-! Every actual successful or rejected recursive type execution has the
fuel-free independent trace, on arbitrary states and with every prior event
preserved. Resource induction is confined to execution soundness; neither
completeness nor existence of a successful/rejected outcome is asserted. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

open DeclarativeGrammar

private theorem typeTraceSoundAtFuel (fuel : Nat) :
    ParserTraceSuccessSound (typeExprWithFuel fuel) TypeExprTraceParses ∧
    ParserTraceRejectSound (typeExprWithFuel fuel) TypeExprTraceRejects := by
  induction fuel with
  | zero =>
      constructor
      · intro input output value result
        simp [typeExprWithFuel] at result
      · intro input rejected failure result
        simp [typeExprWithFuel] at result
  | succ fuel ih =>
      constructor
      · intro input output value result
        rcases typeExprWithFuel_dispatch_trace_success_sound fuel ih.1 result with
          ⟨trace, step, events⟩
        exact ⟨trace, TypeExprTraceParses.roll step, events⟩
      · intro input rejected failure result
        rcases typeExprWithFuel_dispatch_reject_trace_sound fuel ih.1 ih.2 result with
          ⟨trace, step, events⟩
        exact ⟨trace, TypeExprTraceRejects.roll step, events⟩

theorem typeExprWithFuel_trace_success_sound (fuel : Nat) :
    ParserTraceSuccessSound (typeExprWithFuel fuel) TypeExprTraceParses :=
  (typeTraceSoundAtFuel fuel).1

theorem typeExprWithFuel_reject_trace_sound (fuel : Nat) :
    ParserTraceRejectSound (typeExprWithFuel fuel) TypeExprTraceRejects :=
  (typeTraceSoundAtFuel fuel).2

theorem typeExpr_trace_success_sound : ParserTraceSuccessSound typeExpr TypeExprTraceParses := by
  intro input output value result
  exact typeExprWithFuel_trace_success_sound (input.remainingCount + 1) result

theorem typeExpr_reject_trace_sound : ParserTraceRejectSound typeExpr TypeExprTraceRejects := by
  intro input rejected failure result
  exact typeExprWithFuel_reject_trace_sound (input.remainingCount + 1) result

end Solcore.Syntax.Parser
