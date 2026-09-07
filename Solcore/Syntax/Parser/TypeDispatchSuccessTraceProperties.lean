import Solcore.Syntax.DeclarativeTypeDispatchTraceGrammar
import Solcore.Syntax.Parser.TypeDispatchSelectionTraceProperties
import Solcore.Syntax.Parser.FunctionTypeSuccessTraceProperties
import Solcore.Syntax.Parser.ComptimeTypeSuccessTraceProperties
import Solcore.Syntax.Parser.MappingTypeTraceProperties
import Solcore.Syntax.Parser.ProxyTypeSuccessTraceProperties
import Solcore.Syntax.Parser.TupleTypeSuccessTraceProperties
import Solcore.Syntax.Parser.NamedTypeTraceProperties
import Solcore.Syntax.Parser.TypeSuccessContextProperties

/-! One positive-fuel dispatch layer composes the six raw success contracts.
The recursive child is the actual preceding-fuel parser, whose success contracts
remain explicit; its frame is unconditional. This is not a complete recursive
production trace theorem. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

open DeclarativeGrammar TypeDispatchTraceInternals

variable {nested : Parser TypeExpr}
  {elementTrace : SourceId → Nat → Remainder → TypeExpr → Remainder → List ParseDiagnostic → Prop}

namespace TypeDispatchTraceInternals

theorem raw_trace_success_sound
    (successSound : ParserTraceSuccessSound nested elementTrace)
    (contextFrame : ParserSuccessContext nested) (branch : TypeDispatchBranch) :
    ParserTraceSuccessSound (rawParser nested branch) (TypeDispatchRawTraceParses elementTrace branch) := by
  cases branch with
  | function => exact parseFunctionType_trace_success_sound successSound contextFrame
  | comptime => exact parseComptimeType_trace_success_sound successSound
  | mapping => exact parseMappingType_trace_success_sound successSound contextFrame
  | proxy => exact parseProxyType_trace_success_sound successSound
  | tuple => exact parseTupleType_trace_success_sound successSound contextFrame
  | named => exact parseNamedType_trace_success_sound successSound contextFrame
  | final => intro input output value result; simp [rawParser, rejectAt] at result

theorem raw_trace_success_complete
    (successComplete : ParserTraceSuccessComplete nested elementTrace)
    (contextFrame : ParserSuccessContext nested) (branch : TypeDispatchBranch) :
    ParserTraceSuccessComplete (rawParser nested branch) (TypeDispatchRawTraceParses elementTrace branch) := by
  cases branch with
  | function => exact parseFunctionType_trace_success_complete successComplete contextFrame
  | comptime => exact parseComptimeType_trace_success_complete successComplete
  | mapping => exact parseMappingType_trace_success_complete successComplete contextFrame
  | proxy => exact parseProxyType_trace_success_complete successComplete
  | tuple => exact parseTupleType_trace_success_complete successComplete contextFrame
  | named => exact parseNamedType_trace_success_complete successComplete contextFrame
  | final => intro input value after trace parsed; exact False.elim parsed

theorem raw_success_context
    (contextFrame : ParserSuccessContext nested) (branch : TypeDispatchBranch) :
    ParserSuccessContext (rawParser nested branch) := by
  cases branch with
  | function => exact parseFunctionType_success_context contextFrame
  | comptime => exact parseComptimeType_success_context contextFrame
  | mapping => exact parseMappingType_success_context contextFrame
  | proxy => exact parseProxyType_success_context contextFrame
  | tuple => exact parseTupleType_success_context contextFrame
  | named => exact parseNamedType_success_context contextFrame
  | final => intro input output value result; simp [rawParser, rejectAt] at result

end TypeDispatchTraceInternals

theorem typeExprWithFuel_dispatch_trace_success_sound (fuel : Nat)
    (successSound : ParserTraceSuccessSound (typeExprWithFuel fuel) elementTrace) :
    ParserTraceSuccessSound (typeExprWithFuel (fuel + 1)) (TypeDispatchTraceParses elementTrace) := by
  intro input output value result
  rw [typeExprWithFuel_eq_selected_raw] at result
  rcases raw_trace_success_sound successSound (typeExprWithFuel_success_context fuel) (selectedBranch input) result with
    ⟨trace, parsed, events⟩
  exact ⟨trace, .selected (selectedBranch input) (selectedBranch_selects input) parsed, events⟩

theorem typeExprWithFuel_dispatch_trace_success_complete (fuel : Nat)
    (successComplete : ParserTraceSuccessComplete (typeExprWithFuel fuel) elementTrace) :
    ParserTraceSuccessComplete (typeExprWithFuel (fuel + 1)) (TypeDispatchTraceParses elementTrace) := by
  intro input value after trace parsed
  cases parsed with
  | selected branch selection raw =>
      rcases raw_trace_success_complete successComplete (typeExprWithFuel_success_context fuel) branch raw with
        ⟨output, result, afterEq, events⟩
      exact ⟨output, (typeExprWithFuel_eq_raw_of_selection fuel selection).trans result, afterEq, events⟩

theorem typeExprWithFuel_dispatch_success_context (fuel : Nat) :
    ParserSuccessContext (typeExprWithFuel (fuel + 1)) :=
  typeExprWithFuel_success_context (fuel + 1)

theorem typeExprWithFuel_dispatch_trace_success_iff (fuel : Nat)
    (successSound : ParserTraceSuccessSound (typeExprWithFuel fuel) elementTrace)
    (successComplete : ParserTraceSuccessComplete (typeExprWithFuel fuel) elementTrace)
    {input : State} {value : TypeExpr} {after : Remainder} {trace : List ParseDiagnostic} :
    TypeDispatchTraceParses elementTrace input.file.id input.window.endByte
      input.declarativeRemainder value after trace ↔
    ∃ output, typeExprWithFuel (fuel + 1) input = .ok value output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact typeExprWithFuel_dispatch_trace_success_complete fuel successComplete
  · rintro ⟨output, result, afterEq, events⟩
    rcases typeExprWithFuel_dispatch_trace_success_sound fuel successSound result with
      ⟨actualTrace, parsed, actualEvents⟩
    have same := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, same] using parsed

end Solcore.Syntax.Parser
