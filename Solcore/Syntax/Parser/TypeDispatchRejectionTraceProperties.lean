import Solcore.Syntax.DeclarativeTypeDispatchTraceGrammar
import Solcore.Syntax.Parser.TypeDispatchSelectionTraceProperties
import Solcore.Syntax.Parser.FunctionTypeRejectionTraceProperties
import Solcore.Syntax.Parser.ComptimeTypeRejectionTraceProperties
import Solcore.Syntax.Parser.MappingTypeRejectionTraceCompletenessProperties
import Solcore.Syntax.Parser.ProxyTypeRejectionTraceProperties
import Solcore.Syntax.Parser.TupleTypeRejectionTraceProperties
import Solcore.Syntax.Parser.NamedTypeRejectionTraceProperties
import Solcore.Syntax.Parser.TypeSuccessContextProperties

/-! Exact rejection of one positive-fuel type-dispatch layer. Earlier guards
select a raw branch, or the final silent expected-typeExpr failure. Nested
success/rejection contracts are explicit, while the fixed child's frame is
unconditional; no general recursive production trace is asserted. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

open DeclarativeGrammar TypeDispatchTraceInternals

variable {nested : Parser TypeExpr}
  {elementTrace : SourceId → Nat → Remainder → TypeExpr → Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

namespace TypeDispatchTraceInternals

theorem raw_reject_trace_sound
    (successSound : ParserTraceSuccessSound nested elementTrace)
    (rejectSound : ParserTraceRejectSound nested elementRejects)
    (contextFrame : ParserSuccessContext nested) (branch : TypeDispatchBranch) :
    ParserTraceRejectSound (rawParser nested branch) (TypeDispatchRawTraceRejects elementTrace elementRejects branch) := by
  cases branch with
  | function => exact parseFunctionType_reject_trace_sound successSound rejectSound contextFrame
  | comptime => exact parseComptimeType_reject_trace_sound successSound rejectSound contextFrame
  | mapping => exact parseMappingType_reject_trace_sound successSound rejectSound contextFrame
  | proxy => exact parseProxyType_reject_trace_sound rejectSound
  | tuple => exact parseTupleType_reject_trace_sound successSound rejectSound contextFrame
  | named => exact parseNamedType_reject_trace_sound successSound rejectSound contextFrame
  | final =>
      intro input rejected failure result
      have reported := rejectAt_reject_reports { head := .typeExpr, tail := [] } .typeExpr result
      have same : rejected = input := by
        unfold rawParser rejectAt at result
        cases result
        rfl
      subst rejected
      exact ⟨[], .rejected reported.1, by simp only [List.append_nil]⟩

theorem raw_trace_reject_complete
    (successComplete : ParserTraceSuccessComplete nested elementTrace)
    (rejectComplete : ParserTraceRejectComplete nested elementRejects)
    (contextFrame : ParserSuccessContext nested) (branch : TypeDispatchBranch) :
    ParserTraceRejectComplete (rawParser nested branch) (TypeDispatchRawTraceRejects elementTrace elementRejects branch) := by
  cases branch with
  | function => exact parseFunctionType_trace_reject_complete successComplete rejectComplete contextFrame
  | comptime => exact parseComptimeType_trace_reject_complete successComplete rejectComplete contextFrame
  | mapping => exact parseMappingType_trace_reject_complete successComplete rejectComplete contextFrame
  | proxy => exact parseProxyType_trace_reject_complete rejectComplete
  | tuple => exact parseTupleType_trace_reject_complete successComplete rejectComplete contextFrame
  | named => exact parseNamedType_trace_reject_complete successComplete rejectComplete contextFrame
  | final =>
      intro input after report trace rejection
      cases rejection with
      | rejected reported =>
          rcases (rejectAt_reports_iff (alpha := TypeExpr)).mp reported with ⟨failure, result, reportEq⟩
          exact ⟨failure, input, result, rfl, reportEq, by simp only [List.append_nil]⟩

end TypeDispatchTraceInternals

theorem typeExprWithFuel_dispatch_reject_trace_sound (fuel : Nat)
    (successSound : ParserTraceSuccessSound (typeExprWithFuel fuel) elementTrace)
    (rejectSound : ParserTraceRejectSound (typeExprWithFuel fuel) elementRejects) :
    ParserTraceRejectSound (typeExprWithFuel (fuel + 1)) (TypeDispatchTraceRejects elementTrace elementRejects) := by
  intro input rejected failure result
  rw [typeExprWithFuel_eq_selected_raw] at result
  rcases raw_reject_trace_sound successSound rejectSound (typeExprWithFuel_success_context fuel)
      (selectedBranch input) result with
    ⟨trace, rejection, events⟩
  exact ⟨trace, .selected (selectedBranch input) (selectedBranch_selects input) rejection, events⟩

theorem typeExprWithFuel_dispatch_trace_reject_complete (fuel : Nat)
    (successComplete : ParserTraceSuccessComplete (typeExprWithFuel fuel) elementTrace)
    (rejectComplete : ParserTraceRejectComplete (typeExprWithFuel fuel) elementRejects) :
    ParserTraceRejectComplete (typeExprWithFuel (fuel + 1)) (TypeDispatchTraceRejects elementTrace elementRejects) := by
  intro input after report trace rejection
  cases rejection with
  | selected branch selection raw =>
      rcases raw_trace_reject_complete successComplete rejectComplete (typeExprWithFuel_success_context fuel) branch raw with
        ⟨failure, rejected, result, afterEq, reportEq, events⟩
      exact ⟨failure, rejected, (typeExprWithFuel_eq_raw_of_selection fuel selection).trans result,
        afterEq, reportEq, events⟩

theorem typeExprWithFuel_dispatch_trace_reject_iff (fuel : Nat)
    (successSound : ParserTraceSuccessSound (typeExprWithFuel fuel) elementTrace)
    (rejectSound : ParserTraceRejectSound (typeExprWithFuel fuel) elementRejects)
    (successComplete : ParserTraceSuccessComplete (typeExprWithFuel fuel) elementTrace)
    (rejectComplete : ParserTraceRejectComplete (typeExprWithFuel fuel) elementRejects)
    {input : State} {after : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    TypeDispatchTraceRejects elementTrace elementRejects input.file.id input.window.endByte
      input.declarativeRemainder after report trace ↔
    ∃ failure rejected, typeExprWithFuel (fuel + 1) input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
      rejected.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact typeExprWithFuel_dispatch_trace_reject_complete fuel successComplete rejectComplete
  · rintro ⟨failure, rejected, result, afterEq, reportEq, events⟩
    rcases typeExprWithFuel_dispatch_reject_trace_sound fuel successSound rejectSound result with
      ⟨actualTrace, rejection, actualEvents⟩
    have same := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, reportEq, same] using rejection

theorem typeExprWithFuel_dispatch_trace_reject_failure_iff (fuel : Nat)
    (successSound : ParserTraceSuccessSound (typeExprWithFuel fuel) elementTrace)
    (rejectSound : ParserTraceRejectSound (typeExprWithFuel fuel) elementRejects)
    (successComplete : ParserTraceSuccessComplete (typeExprWithFuel fuel) elementTrace)
    (rejectComplete : ParserTraceRejectComplete (typeExprWithFuel fuel) elementRejects)
    {input : State} {after : Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    TypeDispatchTraceRejects elementTrace elementRejects input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
    ∃ rejected, typeExprWithFuel (fuel + 1) input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace := by
  rw [typeExprWithFuel_dispatch_trace_reject_iff fuel successSound rejectSound successComplete rejectComplete]
  constructor
  · rintro ⟨actual, rejected, result, afterEq, reportEq, events⟩
    cases Failure.toDiagnostic_injective reportEq
    exact ⟨rejected, result, afterEq, events⟩
  · rintro ⟨rejected, result, afterEq, events⟩
    exact ⟨failure, rejected, result, afterEq, rfl, events⟩

end Solcore.Syntax.Parser
