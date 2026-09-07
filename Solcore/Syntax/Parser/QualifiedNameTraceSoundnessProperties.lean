import Solcore.Syntax.DeclarativeQualifiedNameTraceProperties
import Solcore.Syntax.Parser.IdentifierTraceProperties
import Solcore.Syntax.Parser.PragmaItemsContextProperties
import Solcore.Syntax.Parser.ExactTokenPrimitiveSuccessTraceProperties
import Solcore.Syntax.Parser.DiagnosticTraceContracts
import Solcore.Syntax.Parser.Name

/-! Unconditional exact checked-name traces and unchanged diagnostic context. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace QualifiedNameInternals

theorem qualifiedNameTail_success_trace_sound
    (context : ParseContext) (phase : ParserPhase) (first : Identifier) :
    ∀ fuel last tailRev input name output,
      qualifiedNameTail context phase first fuel last tailRev input = .ok name output →
      ∃ components trace,
        name = DeclarativeGrammar.qualifiedNameFromSuffix first last tailRev.reverse components ∧
        DeclarativeGrammar.DottedIdentifierTailTraceParses input.file.id input.window.endByte
          input.declarativeRemainder components output.declarativeRemainder trace ∧
        output.diagnostics = input.diagnostics ++ trace ∧
        output.file = input.file ∧ output.window = input.window := by
  intro fuel
  induction fuel with
  | zero => intro last tailRev input name output result; simp [qualifiedNameTail] at result
  | succ fuel ih =>
      intro last tailRev input name output result
      unfold qualifiedNameTail at result
      split at result
      · cases dotResult : symbol .dot context input with
        | invariant error => simp [dotResult] at result
        | reject failure rejected => simp [dotResult] at result
        | ok dot afterDot =>
            have dotParsed := symbol_success_exactTokenParses .dot context dotResult
            have dotState := (symbol_ok_tokenAt .dot context dotResult).2
            subst afterDot
            simp only [dotResult] at result
            cases childResult : identifier context { input with cursor := input.cursor + 1 } with
            | invariant error => simp [childResult] at result
            | reject failure rejected => simp [childResult] at result
            | ok component next =>
                simp only [childResult] at result
                rcases identifier_success_trace_sound context childResult with ⟨headTrace, child, childEq⟩
                have frame := identifier_success_context_eq context childResult
                rcases ih component (component :: tailRev) next name output result with
                  ⟨components, tailTrace, nameEq, tail, events, fileEq, windowEq⟩
                refine ⟨component :: components, headTrace ++ tailTrace, ?_,
                  .next dot.span dotParsed child ?_, ?_, fileEq.trans frame.1, windowEq.trans frame.2⟩
                · simpa only [DeclarativeGrammar.qualifiedNameFromSuffix, DeclarativeGrammar.finalIdentifier,
                    List.reverse_cons, List.append_assoc, List.singleton_append] using nameEq
                · simpa only [frame.1, frame.2] using tail
                · rw [events, childEq]; exact List.append_assoc _ _ _
      · rename_i noDot
        have stopped := symbolAbsentAt_of_isSymbol_eq_false .dot (Bool.eq_false_iff.mpr noDot)
        unfold finishQualifiedName at result
        cases result
        exact ⟨[], [], by simp [DeclarativeGrammar.qualifiedNameFromSuffix, DeclarativeGrammar.finalIdentifier],
          .done stopped, by simp, rfl, rfl⟩

theorem qualifiedNameTail_success_context (context : ParseContext) (phase : ParserPhase)
    (first last : Identifier) (fuel : Nat) (tailRev : List Identifier)
    {input output : State} {name : QualifiedName}
    (result : qualifiedNameTail context phase first fuel last tailRev input = .ok name output) :
    output.file = input.file ∧ output.window = input.window := by
  rcases qualifiedNameTail_success_trace_sound context phase first fuel last tailRev input name output result with
    ⟨_, _, _, _, _, frame⟩
  exact frame

end QualifiedNameInternals

theorem qualifiedName_trace_success_sound (context : ParseContext) (phase : ParserPhase) :
    ParserTraceSuccessSound (qualifiedName context phase) DeclarativeGrammar.QualifiedNameTraceParses := by
  intro input output name result
  unfold qualifiedName at result
  cases firstResult : identifier context input with
  | invariant error => simp [firstResult] at result
  | reject failure rejected => simp [firstResult] at result
  | ok first next =>
      simp only [firstResult] at result
      rcases identifier_success_trace_sound context firstResult with ⟨firstTrace, head, firstEq⟩
      have frame := identifier_success_context_eq context firstResult
      rcases QualifiedNameInternals.qualifiedNameTail_success_trace_sound context phase first
          (next.remainingCount + 1) first [] next name output result with
        ⟨components, tailTrace, nameEq, tail, events, _⟩
      refine ⟨firstTrace ++ tailTrace, ?_, ?_⟩
      · rw [nameEq]
        exact .parsed head (by simpa only [frame.1, frame.2] using tail)
      · rw [events, firstEq]; exact List.append_assoc _ _ _

theorem qualifiedName_success_context (context : ParseContext) (phase : ParserPhase) :
    ParserSuccessContext (qualifiedName context phase) := by
  intro input output name result
  unfold qualifiedName at result
  cases firstResult : identifier context input with
  | invariant error => simp [firstResult] at result
  | reject failure rejected => simp [firstResult] at result
  | ok first next =>
      simp only [firstResult] at result
      have firstFrame := identifier_success_context_eq context firstResult
      have tailFrame := QualifiedNameInternals.qualifiedNameTail_success_context context phase
        first first (next.remainingCount + 1) [] result
      exact ⟨tailFrame.1.trans firstFrame.1, tailFrame.2.trans firstFrame.2⟩

end Solcore.Syntax.Parser
