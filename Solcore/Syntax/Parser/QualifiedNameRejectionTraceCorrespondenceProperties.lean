import Solcore.Syntax.Parser.QualifiedNameRejectionTraceCompletenessProperties

/-! Exact rejection correspondence, including full uncommitted Failure data,
arbitrary earlier events, raw reverse prefixes, and actual production fuel. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace QualifiedNameInternals

theorem qualifiedNameTail_trace_reject_iff
    (context : ParseContext) (phase : ParserPhase) (first last : Identifier)
    (fuel : Nat) (tailRev : List Identifier) {input : State}
    (adequate : input.remainingCount < fuel)
    {after : DeclarativeGrammar.Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.DottedIdentifierTailTraceRejects context input.file.id input.window.endByte
      input.declarativeRemainder after report trace ↔
    ∃ failure rejected, qualifiedNameTail context phase first fuel last tailRev input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
      rejected.diagnostics = input.diagnostics ++ trace := by
  constructor
  · intro rejection
    exact qualifiedNameTail_trace_reject_complete context phase first last fuel tailRev rejection adequate
  · rintro ⟨failure, rejected, result, afterEq, reportEq, events⟩
    rcases qualifiedNameTail_reject_trace_sound context phase first fuel last tailRev input failure rejected result with
      ⟨actualTrace, rejection, actualEvents⟩
    have same := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, reportEq, same] using rejection

theorem qualifiedNameTail_trace_reject_failure_iff
    (context : ParseContext) (phase : ParserPhase) (first last : Identifier)
    (fuel : Nat) (tailRev : List Identifier) {input : State}
    (adequate : input.remainingCount < fuel)
    {after : DeclarativeGrammar.Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.DottedIdentifierTailTraceRejects context input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
    ∃ rejected, qualifiedNameTail context phase first fuel last tailRev input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace := by
  rw [qualifiedNameTail_trace_reject_iff context phase first last fuel tailRev adequate]
  constructor
  · rintro ⟨actual, rejected, result, afterEq, reportEq, events⟩
    cases Failure.toDiagnostic_injective reportEq
    exact ⟨rejected, result, afterEq, events⟩
  · rintro ⟨rejected, result, afterEq, events⟩
    exact ⟨failure, rejected, result, afterEq, rfl, events⟩

theorem qualifiedNameTail_production_trace_reject_iff
    (context : ParseContext) (phase : ParserPhase) (first last : Identifier)
    (tailRev : List Identifier) {input : State}
    {after : DeclarativeGrammar.Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.DottedIdentifierTailTraceRejects context input.file.id input.window.endByte
      input.declarativeRemainder after report trace ↔
    ∃ failure rejected,
      qualifiedNameTail context phase first (input.remainingCount + 1) last tailRev input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
      rejected.diagnostics = input.diagnostics ++ trace :=
  qualifiedNameTail_trace_reject_iff context phase first last (input.remainingCount + 1) tailRev (by omega)

theorem qualifiedNameTail_production_trace_reject_failure_iff
    (context : ParseContext) (phase : ParserPhase) (first last : Identifier)
    (tailRev : List Identifier) {input : State}
    {after : DeclarativeGrammar.Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.DottedIdentifierTailTraceRejects context input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
    ∃ rejected,
      qualifiedNameTail context phase first (input.remainingCount + 1) last tailRev input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace :=
  qualifiedNameTail_trace_reject_failure_iff context phase first last (input.remainingCount + 1) tailRev (by omega)

end QualifiedNameInternals

theorem qualifiedName_trace_reject_iff (context : ParseContext) (phase : ParserPhase)
    {input : State} {after : DeclarativeGrammar.Remainder}
    {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.QualifiedNameTraceRejects context input.file.id input.window.endByte
      input.declarativeRemainder after report trace ↔
    ∃ failure rejected, qualifiedName context phase input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
      rejected.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact qualifiedName_trace_reject_complete context phase
  · rintro ⟨failure, rejected, result, afterEq, reportEq, events⟩
    rcases qualifiedName_reject_trace_sound context phase result with ⟨actualTrace, rejection, actualEvents⟩
    have same := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, reportEq, same] using rejection

theorem qualifiedName_trace_reject_failure_iff (context : ParseContext) (phase : ParserPhase)
    {input : State} {after : DeclarativeGrammar.Remainder}
    {failure : Failure} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.QualifiedNameTraceRejects context input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
    ∃ rejected, qualifiedName context phase input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace := by
  rw [qualifiedName_trace_reject_iff context phase]
  constructor
  · rintro ⟨actual, rejected, result, afterEq, reportEq, events⟩
    cases Failure.toDiagnostic_injective reportEq
    exact ⟨rejected, result, afterEq, events⟩
  · rintro ⟨rejected, result, afterEq, events⟩
    exact ⟨failure, rejected, result, afterEq, rfl, events⟩

end Solcore.Syntax.Parser
