import Solcore.Syntax.DeclarativeTupleTypeTraceGrammar
import Solcore.Syntax.Parser.DelimitedTrailingTraceCompletenessProperties
import Solcore.Syntax.Parser.DelimitedTrailingTraceContextProperties
import Solcore.Syntax.Parser.Type

/-! Actual tuple types preserve the full list span and every ordered child event.
Empty and singleton lists remain tuple types. Only nested success contracts and
the successful source/full-window frame are needed. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

variable {nested : Parser TypeExpr}
  {typeTrace : SourceId → Nat → DeclarativeGrammar.Remainder → TypeExpr →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}

theorem parseTupleType_success_iff_list {input output : State} {value : TypeExpr} :
    parseTupleType nested input = .ok value output ↔
    ∃ values, delimited .leftParen .rightParen true nested .typeExpr .typeExpr input =
      .ok values output ∧ value = DeclarativeGrammar.tupleTypeTraceValue values := by
  constructor
  · intro result
    cases listResult : delimited .leftParen .rightParen true nested .typeExpr .typeExpr input with
    | reject => simp [parseTupleType, bind, listResult] at result
    | invariant => simp [parseTupleType, bind, listResult] at result
    | ok values next =>
        simp only [parseTupleType, bind, listResult, pure] at result
        cases result
        exact ⟨values, rfl, rfl⟩
  · rintro ⟨values, result, rfl⟩
    simp only [parseTupleType, bind, result, pure, DeclarativeGrammar.tupleTypeTraceValue]

theorem parseTupleType_trace_success_sound
    (successSound : ParserTraceSuccessSound nested typeTrace)
    (contextFrame : ParserSuccessContext nested) :
    ParserTraceSuccessSound (parseTupleType nested)
      (DeclarativeGrammar.TupleTypeTraceParses typeTrace) := by
  intro input output value result
  rcases parseTupleType_success_iff_list.mp result with ⟨values, listResult, rfl⟩
  rcases delimited_trace_success_sound successSound contextFrame
      .leftParen .rightParen true .typeExpr .typeExpr listResult with ⟨trace, parsed, events⟩
  exact ⟨trace, .parsed parsed, events⟩

theorem parseTupleType_trace_success_complete
    (successComplete : ParserTraceSuccessComplete nested typeTrace)
    (contextFrame : ParserSuccessContext nested) :
    ParserTraceSuccessComplete (parseTupleType nested)
      (DeclarativeGrammar.TupleTypeTraceParses typeTrace) := by
  intro input value after trace parsed
  cases parsed with
  | parsed elements =>
      rcases delimited_trace_success_complete successComplete contextFrame
          .leftParen .rightParen true .typeExpr .typeExpr elements with
        ⟨output, result, afterEq, events⟩
      exact ⟨output, parseTupleType_success_iff_list.mpr ⟨_, result, rfl⟩, afterEq, events⟩

theorem parseTupleType_success_context (contextFrame : ParserSuccessContext nested) :
    ParserSuccessContext (parseTupleType nested) := by
  intro input output value result
  rcases parseTupleType_success_iff_list.mp result with ⟨values, listResult, _⟩
  exact delimited_success_context contextFrame .leftParen .rightParen true
    .typeExpr .typeExpr listResult

theorem parseTupleType_trace_success_iff
    (successSound : ParserTraceSuccessSound nested typeTrace)
    (successComplete : ParserTraceSuccessComplete nested typeTrace)
    (contextFrame : ParserSuccessContext nested)
    {input : State} {value : TypeExpr} {after : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic} :
    DeclarativeGrammar.TupleTypeTraceParses typeTrace input.file.id input.window.endByte
      input.declarativeRemainder value after trace ↔
    ∃ output, parseTupleType nested input = .ok value output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact parseTupleType_trace_success_complete successComplete contextFrame
  · rintro ⟨output, result, afterEq, events⟩
    rcases parseTupleType_trace_success_sound successSound contextFrame result with
      ⟨actualTrace, parsed, actualEvents⟩
    have same := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, same] using parsed

end Solcore.Syntax.Parser
