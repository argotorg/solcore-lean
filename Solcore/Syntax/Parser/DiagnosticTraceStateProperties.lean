import Solcore.Syntax.Parser.DiagnosticTraceContracts

/-! Exact state reconstruction retains all remainder fields, including its
token carrier and end index. Replacing it by a cursor-only update requires
explicit carrier equalities. These are state equalities, not parser contracts. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.State

open DeclarativeGrammar

theorem eq_of_file_endByte_remainder_diagnostics
    {left right : State} (fileEq : left.file = right.file)
    (endByteEq : left.window.endByte = right.window.endByte)
    (remainderEq : left.declarativeRemainder = right.declarativeRemainder)
    (diagnosticsEq : left.diagnostics = right.diagnostics) : left = right := by
  cases left with
  | mk leftFile leftTokens leftCursor leftWindow leftDiagnostics =>
      cases right with
      | mk rightFile rightTokens rightCursor rightWindow rightDiagnostics =>
          cases leftWindow
          cases rightWindow
          simp only [declarativeRemainder, Remainder.mk.injEq] at remainderEq
          rcases remainderEq with ⟨rfl, rfl, rfl⟩
          have reversed := congrArg List.reverse diagnosticsEq
          simp only [diagnostics, List.reverse_reverse] at reversed
          cases fileEq
          cases endByteEq
          cases reversed
          rfl

def traceResult (input : State) (after : Remainder) (trace : List ParseDiagnostic) : State := {
  file := input.file
  tokens := after.tokens
  cursor := after.cursor
  window := { endIndex := after.endIndex, endByte := input.window.endByte }
  diagnosticsRev := trace.reverse ++ input.diagnosticsRev
}

theorem traceResult_declarativeRemainder (input : State) (after : Remainder) (trace : List ParseDiagnostic) :
    (input.traceResult after trace).declarativeRemainder = after := rfl

theorem traceResult_diagnostics (input : State) (after : Remainder) (trace : List ParseDiagnostic) :
    (input.traceResult after trace).diagnostics = input.diagnostics ++ trace := by
  simp only [traceResult, diagnostics, List.reverse_append, List.reverse_reverse]

theorem eq_traceResult_of_fields {input output : State} {after : Remainder} {trace : List ParseDiagnostic}
    (fileEq : output.file = input.file) (endByteEq : output.window.endByte = input.window.endByte)
    (remainderEq : output.declarativeRemainder = after)
    (events : output.diagnostics = input.diagnostics ++ trace) :
    output = input.traceResult after trace :=
  eq_of_file_endByte_remainder_diagnostics fileEq endByteEq
    (remainderEq.trans (input.traceResult_declarativeRemainder after trace).symm)
    (events.trans (input.traceResult_diagnostics after trace).symm)

theorem traceResult_eq_cursor_update {input : State} {after : Remainder} (trace : List ParseDiagnostic)
    (tokensEq : after.tokens = input.tokens) (endIndexEq : after.endIndex = input.window.endIndex) :
    input.traceResult after trace =
      { input with cursor := after.cursor, diagnosticsRev := trace.reverse ++ input.diagnosticsRev } := by
  cases input
  rename_i file tokens cursor window diagnosticsRev
  cases window
  simp only [traceResult, tokensEq, endIndexEq]

end Solcore.Syntax.Parser.State
