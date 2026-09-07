import Solcore.Syntax.Parser.QualifiedNameTraceSoundnessProperties
import Solcore.Syntax.Parser.DelimitedClosingTraceProperties

/-! Checked qualified names execute every independent trace at production fuel. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace QualifiedNameInternals

open DelimitedTraceInternals

theorem qualifiedNameTail_trace_success_complete
    (context : ParseContext) (phase : ParserPhase) (first last : Identifier)
    (fuel : Nat) (tailRev : List Identifier)
    {input : State} {components : List Identifier} {after : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic}
    (parsed : DeclarativeGrammar.DottedIdentifierTailTraceParses input.file.id input.window.endByte
      input.declarativeRemainder components after trace)
    (adequate : input.remainingCount < fuel) :
    ∃ output, qualifiedNameTail context phase first fuel last tailRev input = .ok
        (DeclarativeGrammar.qualifiedNameFromSuffix first last tailRev.reverse components) output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  induction fuel generalizing last tailRev input components after trace with
  | zero => omega
  | succ fuel ih =>
      cases parsed with
      | done stopped =>
          exact ⟨input, by simp only [qualifiedNameTail, symbol_absent .dot stopped,
            Bool.false_eq_true, if_false, finishQualifiedName, DeclarativeGrammar.qualifiedNameFromSuffix,
            DeclarativeGrammar.finalIdentifier, List.append_nil], rfl, by simp⟩
      | next dotSpan dot name tail =>
          rename_i afterDot afterComponent component components headTrace tailTrace
          have dotResult := symbol_eq_ok_of_exactTokenParses .dot context dot
          have dotPresent := symbol_present .dot dot
          rcases dot with ⟨dotToken, rfl⟩
          rcases (identifier_trace_success_iff context
              (input := { input with cursor := input.cursor + 1 })).mp name with
            ⟨next, childResult, afterEq, childEvents⟩
          have frame := identifier_success_context_eq context childResult
          have tailAtNext : DeclarativeGrammar.DottedIdentifierTailTraceParses next.file.id next.window.endByte
              next.declarativeRemainder components after tailTrace := by
            simpa only [frame.1, frame.2, afterEq] using tail
          have nextAdequate : next.remainingCount < fuel := by
            have inside : input.cursor < input.window.endIndex := dotToken.1
            have nextCursor := (DeclarativeGrammar.identifierTraceParses_iff.mp name).1.2.2.2
            change afterComponent.cursor = input.cursor + 1 + 1 at nextCursor
            have cursorEq : next.cursor = afterComponent.cursor := congrArg DeclarativeGrammar.Remainder.cursor afterEq
            simp only [State.remainingCount, frame.2] at adequate ⊢
            omega
          rcases ih component (component :: tailRev) tailAtNext nextAdequate with
            ⟨output, result, finalEq, events⟩
          refine ⟨output, ?_, finalEq, ?_⟩
          · simp only [qualifiedNameTail, dotPresent, if_true, dotResult, childResult]
            simpa only [DeclarativeGrammar.qualifiedNameFromSuffix, DeclarativeGrammar.finalIdentifier,
              List.reverse_cons, List.append_assoc, List.singleton_append] using result
          · rw [events, childEvents]; exact List.append_assoc _ _ _

theorem qualifiedNameTail_production_trace_success_complete
    (context : ParseContext) (phase : ParserPhase) (first last : Identifier) (tailRev : List Identifier)
    {input : State} {components : List Identifier} {after : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic}
    (parsed : DeclarativeGrammar.DottedIdentifierTailTraceParses input.file.id input.window.endByte
      input.declarativeRemainder components after trace) :
    ∃ output, qualifiedNameTail context phase first (input.remainingCount + 1) last tailRev input = .ok
        (DeclarativeGrammar.qualifiedNameFromSuffix first last tailRev.reverse components) output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace :=
  qualifiedNameTail_trace_success_complete context phase first last (input.remainingCount + 1)
    tailRev parsed (by omega)

end QualifiedNameInternals

theorem qualifiedName_trace_success_complete (context : ParseContext) (phase : ParserPhase) :
    ParserTraceSuccessComplete (qualifiedName context phase) DeclarativeGrammar.QualifiedNameTraceParses := by
  intro input name after trace parsed
  cases parsed with
  | parsed head tail =>
      rcases (identifier_trace_success_iff context).mp head with ⟨next, firstResult, afterEq, firstEvents⟩
      have frame := identifier_success_context_eq context firstResult
      have tailAtNext := tail
      rw [← afterEq, ← frame.1, ← frame.2] at tailAtNext
      rcases QualifiedNameInternals.qualifiedNameTail_production_trace_success_complete context phase
          _ _ [] tailAtNext with ⟨output, result, finalEq, events⟩
      refine ⟨output, ?_, finalEq, ?_⟩
      · simpa only [qualifiedName, firstResult, DeclarativeGrammar.tracedQualifiedName,
          List.reverse_nil] using result
      · rw [events, firstEvents]; exact List.append_assoc _ _ _

end Solcore.Syntax.Parser
