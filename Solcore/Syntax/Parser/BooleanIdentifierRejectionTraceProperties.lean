import Solcore.Syntax.Parser.CoreLiteralRejectionTraceProperties

/-! Exact Boolean rejection retains the whole input and expression expectation. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

theorem booleanIdentifier_eq_rejectAt_of_absence {input : State}
    (absent : DeclarativeGrammar.BooleanPatternAbsentAt input.declarativeRemainder) :
    booleanIdentifier input = rejectAt input { head := .expression, tail := [] } .expression := by
  unfold booleanIdentifier
  cases found : input.peek? with
  | none => rfl
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> try rfl
      case keyword keyword =>
        cases keyword <;> try rfl
        case trueKw => exact False.elim (absent.1 ⟨span, tokenAt_of_peek?_eq_some found⟩)
        case falseKw => exact False.elim (absent.2 ⟨span, tokenAt_of_peek?_eq_some found⟩)

theorem booleanIdentifier_reject_absent {input rejected : State} {failure : Failure}
    (result : booleanIdentifier input = .reject failure rejected) :
    DeclarativeGrammar.BooleanPatternAbsentAt input.declarativeRemainder := by
  constructor
  · rintro ⟨span, token⟩
    have success := booleanIdentifier_eq_ok_of_ordinary (.trueKeyword token)
    rw [success] at result
    contradiction
  · rintro ⟨span, token⟩
    have success := booleanIdentifier_eq_ok_of_ordinary (.falseKeyword token)
    rw [success] at result
    contradiction

theorem booleanIdentifier_reject_state_eq {input rejected : State} {failure : Failure}
    (result : booleanIdentifier input = .reject failure rejected) : rejected = input := by
  rw [booleanIdentifier_eq_rejectAt_of_absence (booleanIdentifier_reject_absent result)] at result
  unfold rejectAt at result
  cases result
  rfl

theorem booleanIdentifier_reject_trace_sound {input rejected : State} {failure : Failure}
    (result : booleanIdentifier input = .reject failure rejected) :
    DeclarativeGrammar.BooleanIdentifierTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder rejected.declarativeRemainder failure.toDiagnostic [] ∧ rejected = input := by
  have same := booleanIdentifier_reject_state_eq result
  subst rejected
  have absent := booleanIdentifier_reject_absent result
  have direct := (booleanIdentifier_eq_rejectAt_of_absence absent).symm.trans result
  exact ⟨⟨absent, rfl, (rejectAt_reports_iff (alpha := Identifier)).mpr
    ⟨failure, direct, rfl⟩, rfl⟩, rfl⟩

theorem booleanIdentifier_trace_reject_iff
    {input : State} {after : DeclarativeGrammar.Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.BooleanIdentifierTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder after diagnostic trace ↔
    ∃ failure, booleanIdentifier input = .reject failure input ∧
      after = input.declarativeRemainder ∧ failure.toDiagnostic = diagnostic ∧ trace = [] := by
  constructor
  · rintro ⟨absent, rfl, reported, events⟩
    rcases (rejectAt_reports_iff (alpha := Identifier)).mp reported with ⟨failure, result, reportEq⟩
    exact ⟨failure, (booleanIdentifier_eq_rejectAt_of_absence absent).trans result, rfl, reportEq, events⟩
  · rintro ⟨failure, result, rfl, rfl, rfl⟩
    exact (booleanIdentifier_reject_trace_sound result).1

theorem booleanIdentifier_trace_reject_failure_iff
    {input : State} {after : DeclarativeGrammar.Remainder} {failure : Failure}
    {trace : List ParseDiagnostic} :
    DeclarativeGrammar.BooleanIdentifierTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
    booleanIdentifier input = .reject failure input ∧ after = input.declarativeRemainder ∧ trace = [] := by
  constructor
  · intro traced
    rcases booleanIdentifier_trace_reject_iff.mp traced with ⟨actual, result, afterEq, reportEq, events⟩
    have same := Failure.toDiagnostic_injective reportEq
    subst actual
    exact ⟨result, afterEq, events⟩
  · rintro ⟨result, afterEq, events⟩
    exact booleanIdentifier_trace_reject_iff.mpr ⟨failure, result, afterEq, rfl, events⟩

end Solcore.Syntax.Parser
