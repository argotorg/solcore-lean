import Solcore.Syntax.Parser.ExpressionNameTraceProperties
import Solcore.Syntax.Parser.CoreExpressionNameOutcomeSoundnessProperties

/-! Exact identifier fallback failure after both Boolean guards are absent. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

theorem expressionName_reject_trace_sound
    {input rejected : State} {failure : Failure}
    (result : expressionName input = .reject failure rejected) :
    DeclarativeGrammar.ExpressionNameTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder rejected.declarativeRemainder failure.toDiagnostic [] ∧ rejected = input := by
  have ordinary := expressionName_reject_ordinary_sound result
  have classify : ∀ {before after : DeclarativeGrammar.Remainder},
      DeclarativeGrammar.ExpressionNameRejects before after →
        DeclarativeGrammar.BooleanPatternAbsentAt before := by
    intro before after rejected
    cases rejected with
    | absent missing => exact ⟨missing.1, missing.2.1⟩
  have absent := classify ordinary
  have checked := (expressionName_eq_identifier_of_booleanAbsent absent).symm.trans result
  have shape := identifier_reject_state_eq .expression checked
  subst rejected
  have reported := (identifier_reject_reports_iff .expression).mpr ⟨failure, checked, rfl⟩
  exact ⟨⟨absent, .absent reported.1, reported.2, rfl⟩, rfl⟩

/-- Boolean-first rejection retains the entire input state, reports an
identifier expectation in expression context, and emits no spelling event. -/
theorem expressionName_trace_reject_iff
    {input : State} {after : DeclarativeGrammar.Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.ExpressionNameTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder after diagnostic trace ↔
    ∃ failure, expressionName input = .reject failure input ∧
      after = input.declarativeRemainder ∧ failure.toDiagnostic = diagnostic ∧ trace = [] := by
  constructor
  · rintro ⟨booleanAbsent, nameRejected, reported, events⟩
    cases nameRejected with
    | absent absent =>
        rcases (identifier_reject_reports_iff .expression).mp ⟨absent, reported⟩ with
          ⟨failure, result, reportEq⟩
        exact ⟨failure, (expressionName_eq_identifier_of_booleanAbsent booleanAbsent).trans result,
          rfl, reportEq, events⟩
  · rintro ⟨failure, result, rfl, rfl, rfl⟩
    exact (expressionName_reject_trace_sound result).1

theorem expressionName_trace_reject_failure_iff
    {input : State} {after : DeclarativeGrammar.Remainder} {failure : Failure}
    {trace : List ParseDiagnostic} :
    DeclarativeGrammar.ExpressionNameTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
    expressionName input = .reject failure input ∧ after = input.declarativeRemainder ∧ trace = [] := by
  constructor
  · intro traced
    rcases expressionName_trace_reject_iff.mp traced with ⟨actual, result, afterEq, reportEq, events⟩
    have same := Failure.toDiagnostic_injective reportEq
    subst actual
    exact ⟨result, afterEq, events⟩
  · rintro ⟨result, afterEq, events⟩
    exact expressionName_trace_reject_iff.mpr ⟨failure, result, afterEq, rfl, events⟩

end Solcore.Syntax.Parser.ExpressionAtomInternals
