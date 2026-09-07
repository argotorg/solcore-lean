import Solcore.Syntax.DeclarativeQualifiedNameRejectionTraceProperties
import Solcore.Syntax.Parser.QualifiedNameTraceSoundnessProperties
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties

/-! Every rejected qualified name retains the precise missing-name report
without committing it, after all previously emitted checked-name events. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace QualifiedNameInternals

theorem qualifiedNameTail_reject_trace_sound
    (context : ParseContext) (phase : ParserPhase) (first : Identifier) :
    ∀ fuel last tailRev input failure rejected,
      qualifiedNameTail context phase first fuel last tailRev input = .reject failure rejected →
      ∃ trace, DeclarativeGrammar.DottedIdentifierTailTraceRejects context
        input.file.id input.window.endByte input.declarativeRemainder
        rejected.declarativeRemainder failure.toDiagnostic trace ∧
        rejected.diagnostics = input.diagnostics ++ trace := by
  intro fuel
  induction fuel with
  | zero => intro last tailRev input failure rejected result; simp [qualifiedNameTail] at result
  | succ fuel ih =>
      intro last tailRev input failure rejected result
      unfold qualifiedNameTail at result
      split at result
      · rename_i present
        rcases symbol_eq_ok_of_isSymbol_eq_true .dot context present with ⟨dot, dotResult⟩
        have dotParsed := symbol_success_exactTokenParses .dot context dotResult
        simp only [dotResult] at result
        cases childResult : identifier context { input with cursor := input.cursor + 1 } with
        | invariant error => simp [childResult] at result
        | reject childFailure childRejected =>
            simp only [childResult] at result
            cases result
            have unchanged := identifier_reject_state_eq context childResult
            subst rejected
            rcases (identifier_reject_reports_iff context).mpr ⟨_, childResult, rfl⟩ with
              ⟨absent, reported⟩
            exact ⟨[], .componentRejected dot.span dotParsed absent reported,
              by simp only [List.append_nil]; rfl⟩
        | ok component next =>
            simp only [childResult] at result
            rcases identifier_success_trace_sound context childResult with ⟨headTrace, name, headEvents⟩
            have frame := identifier_success_context_eq context childResult
            rcases ih component (component :: tailRev) next failure rejected result with
              ⟨tailTrace, tail, events⟩
            refine ⟨headTrace ++ tailTrace, .laterRejected dot.span dotParsed name ?_, ?_⟩
            · simpa only [frame.1, frame.2] using tail
            · rw [events, headEvents]; exact List.append_assoc _ _ _
      · unfold finishQualifiedName at result
        contradiction

end QualifiedNameInternals

theorem qualifiedName_reject_trace_sound (context : ParseContext) (phase : ParserPhase) :
    ParserTraceRejectSound (qualifiedName context phase)
      (DeclarativeGrammar.QualifiedNameTraceRejects context) := by
  intro input rejected failure result
  unfold qualifiedName at result
  cases firstResult : identifier context input with
  | invariant error => simp [firstResult] at result
  | reject firstFailure firstRejected =>
      simp only [firstResult] at result
      cases result
      have unchanged := identifier_reject_state_eq context firstResult
      subst rejected
      rcases (identifier_reject_reports_iff context).mpr ⟨_, firstResult, rfl⟩ with
        ⟨absent, reported⟩
      exact ⟨[], .firstRejected absent reported, by simp⟩
  | ok first next =>
      simp only [firstResult] at result
      rcases identifier_success_trace_sound context firstResult with ⟨firstTrace, head, firstEvents⟩
      have frame := identifier_success_context_eq context firstResult
      rcases QualifiedNameInternals.qualifiedNameTail_reject_trace_sound context phase first
          (next.remainingCount + 1) first [] next failure rejected result with
        ⟨tailTrace, tail, events⟩
      refine ⟨firstTrace ++ tailTrace, .tailRejected head ?_, ?_⟩
      · simpa only [frame.1, frame.2] using tail
      · rw [events, firstEvents]; exact List.append_assoc _ _ _

end Solcore.Syntax.Parser
