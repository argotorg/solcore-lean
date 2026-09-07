import Solcore.Syntax.Parser.LiteralSuccessTraceProperties
import Solcore.Syntax.Parser.PrimitiveRejectionDiagnosticProperties

/-! Exact silent Core-literal rejection, retaining the complete input state. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

theorem coreLiteral_eq_rejectAt_of_absence {input : State}
    (absent : DeclarativeGrammar.CoreLiteralAbsentAt input.declarativeRemainder) :
    coreLiteral input = rejectAt input { head := .coreLiteral, tail := [] } .expression := by
  unfold coreLiteral
  cases found : input.peek? with
  | none => rfl
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> try rfl
      case decimalLiteral spelling =>
        exact False.elim (absent.1 ⟨span, spelling, tokenAt_of_peek?_eq_some found⟩)
      case hexadecimalLiteral spelling =>
        exact False.elim (absent.2.1 ⟨span, spelling, tokenAt_of_peek?_eq_some found⟩)
      case stringLiteral spelling =>
        exact False.elim (absent.2.2 ⟨span, spelling, tokenAt_of_peek?_eq_some found⟩)

theorem coreLiteral_reject_trace_sound {input rejected : State} {failure : Failure}
    (result : coreLiteral input = .reject failure rejected) :
    DeclarativeGrammar.CoreLiteralTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder rejected.declarativeRemainder failure.toDiagnostic [] ∧ rejected = input := by
  have same := coreLiteral_reject_state_eq result
  subst rejected
  have absent := coreLiteral_reject_coreLiteralAbsentAt result
  have direct := (coreLiteral_eq_rejectAt_of_absence absent).symm.trans result
  exact ⟨⟨.absent absent, (rejectAt_reports_iff (alpha := CoreLiteral)).mpr
    ⟨failure, direct, rfl⟩, rfl⟩, rfl⟩

/-- Exact rejection fixes the whole retained state, empty emitted trace,
remainder, and full report under the literal-specific expectation. -/
theorem coreLiteral_trace_reject_iff
    {input : State} {after : DeclarativeGrammar.Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.CoreLiteralTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder after diagnostic trace ↔
    ∃ failure, coreLiteral input = .reject failure input ∧
      after = input.declarativeRemainder ∧ failure.toDiagnostic = diagnostic ∧ trace = [] := by
  constructor
  · rintro ⟨ordinary, reported, events⟩
    cases ordinary with
    | absent absent =>
        rcases (rejectAt_reports_iff (alpha := CoreLiteral)).mp reported with ⟨failure, result, reportEq⟩
        exact ⟨failure, (coreLiteral_eq_rejectAt_of_absence absent).trans result, rfl, reportEq, events⟩
  · rintro ⟨failure, result, rfl, rfl, rfl⟩
    exact (coreLiteral_reject_trace_sound result).1

theorem coreLiteral_trace_reject_failure_iff
    {input : State} {after : DeclarativeGrammar.Remainder} {failure : Failure}
    {trace : List ParseDiagnostic} :
    DeclarativeGrammar.CoreLiteralTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
    coreLiteral input = .reject failure input ∧ after = input.declarativeRemainder ∧ trace = [] := by
  constructor
  · intro traced
    rcases coreLiteral_trace_reject_iff.mp traced with ⟨actual, result, afterEq, reportEq, events⟩
    have same := Failure.toDiagnostic_injective reportEq
    subst actual
    exact ⟨result, afterEq, events⟩
  · rintro ⟨result, afterEq, events⟩
    exact coreLiteral_trace_reject_iff.mpr ⟨failure, result, afterEq, rfl, events⟩

end Solcore.Syntax.Parser
