import Solcore.Syntax.Parser.QualifiedNameRejectionTraceSoundnessProperties
import Solcore.Syntax.Parser.DelimitedClosingTraceProperties

/-! Independent missing-name traces execute with sufficient raw-tail fuel
and with the public parser's actual post-first-name production fuel. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace QualifiedNameInternals

open DelimitedTraceInternals

theorem qualifiedNameTail_trace_reject_complete
    (context : ParseContext) (phase : ParserPhase) (first last : Identifier)
    (fuel : Nat) (tailRev : List Identifier)
    {input : State} {after : DeclarativeGrammar.Remainder}
    {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : DeclarativeGrammar.DottedIdentifierTailTraceRejects context
      input.file.id input.window.endByte input.declarativeRemainder after report trace)
    (adequate : input.remainingCount < fuel) :
    ∃ failure rejected, qualifiedNameTail context phase first fuel last tailRev input =
      .reject failure rejected ∧ rejected.declarativeRemainder = after ∧
      failure.toDiagnostic = report ∧ rejected.diagnostics = input.diagnostics ++ trace := by
  induction fuel generalizing last tailRev input after report trace with
  | zero => omega
  | succ fuel ih =>
      cases rejection with
      | componentRejected dotSpan dot absent reported =>
          have dotResult := symbol_eq_ok_of_exactTokenParses .dot context dot
          have present := symbol_present .dot dot
          rcases dot with ⟨dotToken, rfl⟩
          rcases (identifier_reject_reports_iff context
              (input := { input with cursor := input.cursor + 1 })).mp ⟨absent, reported⟩ with
            ⟨failure, childResult, reportEq⟩
          exact ⟨failure, { input with cursor := input.cursor + 1 },
            by simp only [qualifiedNameTail, present, if_true, dotResult, childResult],
            rfl, reportEq, by simp only [List.append_nil]; rfl⟩
      | laterRejected dotSpan dot name tail =>
          rename_i afterDot afterComponent component headTrace tailTrace
          have dotResult := symbol_eq_ok_of_exactTokenParses .dot context dot
          have present := symbol_present .dot dot
          rcases dot with ⟨dotToken, rfl⟩
          rcases (identifier_trace_success_iff context
              (input := { input with cursor := input.cursor + 1 })).mp name with
            ⟨next, childResult, afterEq, headEvents⟩
          have frame := identifier_success_context_eq context childResult
          have tailAtNext : DeclarativeGrammar.DottedIdentifierTailTraceRejects context
              next.file.id next.window.endByte next.declarativeRemainder after report tailTrace := by
            simpa only [frame.1, frame.2, afterEq] using tail
          have nextAdequate : next.remainingCount < fuel := by
            have inside : input.cursor < input.window.endIndex := dotToken.1
            have nextCursor := (DeclarativeGrammar.identifierTraceParses_iff.mp name).1.2.2.2
            change afterComponent.cursor = input.cursor + 1 + 1 at nextCursor
            have cursorEq : next.cursor = afterComponent.cursor := congrArg DeclarativeGrammar.Remainder.cursor afterEq
            simp only [State.remainingCount, frame.2] at adequate ⊢
            omega
          rcases ih component (component :: tailRev) tailAtNext nextAdequate with
            ⟨failure, rejected, result, finalEq, reportEq, events⟩
          refine ⟨failure, rejected, ?_, finalEq, reportEq, ?_⟩
          · simpa only [qualifiedNameTail, present, if_true, dotResult, childResult] using result
          · rw [events, headEvents]; exact List.append_assoc _ _ _

theorem qualifiedNameTail_production_trace_reject_complete
    (context : ParseContext) (phase : ParserPhase) (first last : Identifier) (tailRev : List Identifier)
    {input : State} {after : DeclarativeGrammar.Remainder}
    {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : DeclarativeGrammar.DottedIdentifierTailTraceRejects context
      input.file.id input.window.endByte input.declarativeRemainder after report trace) :
    ∃ failure rejected, qualifiedNameTail context phase first (input.remainingCount + 1) last tailRev input =
      .reject failure rejected ∧ rejected.declarativeRemainder = after ∧
      failure.toDiagnostic = report ∧ rejected.diagnostics = input.diagnostics ++ trace :=
  qualifiedNameTail_trace_reject_complete context phase first last (input.remainingCount + 1)
    tailRev rejection (by omega)

end QualifiedNameInternals

theorem qualifiedName_trace_reject_complete (context : ParseContext) (phase : ParserPhase) :
    ParserTraceRejectComplete (qualifiedName context phase)
      (DeclarativeGrammar.QualifiedNameTraceRejects context) := by
  intro input after report trace rejection
  cases rejection with
  | firstRejected absent reported =>
      rcases (identifier_reject_reports_iff context).mp ⟨absent, reported⟩ with
        ⟨failure, result, reportEq⟩
      exact ⟨failure, input, by simp only [qualifiedName, result], rfl, reportEq, by simp⟩
  | tailRejected head tail =>
      rcases (identifier_trace_success_iff context).mp head with ⟨next, firstResult, afterEq, firstEvents⟩
      have frame := identifier_success_context_eq context firstResult
      have tailAtNext := tail
      rw [← afterEq, ← frame.1, ← frame.2] at tailAtNext
      rcases QualifiedNameInternals.qualifiedNameTail_production_trace_reject_complete context phase
          _ _ [] tailAtNext with ⟨failure, rejected, result, finalEq, reportEq, events⟩
      refine ⟨failure, rejected, ?_, finalEq, reportEq, ?_⟩
      · simpa only [qualifiedName, firstResult] using result
      · rw [events, firstEvents]; exact List.append_assoc _ _ _

end Solcore.Syntax.Parser
