import Solcore.Syntax.DeclarativePragmaTraceProperties
import Solcore.Syntax.Parser.ExactTokenPrimitiveSuccessTraceProperties
import Solcore.Syntax.Parser.IdentifierTraceProperties
import Solcore.Syntax.Parser.PragmaItemsOrdinaryOutcomeSoundnessProperties

/-! Exact forward diagnostic suffixes from successful pragma item scans. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PragmaInternals

/-- Any successful tail adds precisely the events of its new suffix, never
re-emitting diagnostics for identifiers already in the reverse accumulator. -/
theorem pragmaItemsTail_success_diagnosticTrace :
    ∀ fuel itemsRev input items output,
      pragmaItemsTail fuel itemsRev input = .ok items output →
      ∃ suffix trace,
        items = itemsRev.reverse ++ suffix ∧
        DeclarativeGrammar.IdentifierListDiagnosticTrace suffix trace ∧
        output.diagnostics = input.diagnostics ++ trace := by
  intro fuel
  induction fuel with
  | zero =>
      intro itemsRev input items output result
      simp [pragmaItemsTail] at result
  | succ fuel ih =>
      intro itemsRev input items output result
      unfold pragmaItemsTail at result
      split at result
      · cases commaResult : symbol .comma .pragmaDecl input with
        | invariant error => simp [commaResult] at result
        | reject failure rejected => simp [commaResult] at result
        | ok comma afterComma =>
            have commaSilent := acceptToken_success_diagnostics_eq
              (.symbol .comma) .pragmaDecl (· == .symbol .comma) commaResult
            simp only [commaResult] at result
            split at result
            · cases result
              exact ⟨[], [], by simp, .nil,
                by simpa only [List.append_nil] using commaSilent⟩
            · cases itemResult : identifier .pragmaDecl afterComma with
              | invariant error => simp [itemResult] at result
              | reject failure rejected => simp [itemResult] at result
              | ok item afterItem =>
                  simp only [itemResult] at result
                  rcases ih (item :: itemsRev) afterItem items output result with
                    ⟨suffix, tailTrace, itemsEq, tailDiagnostics, tailEq⟩
                  rcases identifier_success_diagnosticTrace .pragmaDecl itemResult with
                    ⟨headTrace, headDiagnostics, headEq⟩
                  refine ⟨item :: suffix, headTrace ++ tailTrace, ?_,
                    .cons headDiagnostics tailDiagnostics, ?_⟩
                  · simpa only [List.reverse_cons, List.append_assoc,
                      List.singleton_append] using itemsEq
                  · rw [tailEq, headEq, commaSilent, List.append_assoc]
      · cases result
        exact ⟨[], [], by simp, .nil, by simp⟩

/-- Production tail success combines the independent suffix grammar with
exact new events while leaving the pre-existing accumulator prefix outside it. -/
theorem pragmaItemsTail_production_success_trace_sound
    (itemsRev : List Identifier) {input output : State} {items : List Identifier}
    (result : pragmaItemsTail (input.remainingCount + 1) itemsRev input =
      .ok items output) :
    ∃ suffix trace,
      items = itemsRev.reverse ++ suffix ∧
      DeclarativeGrammar.PragmaItemsTailTraceParses input.declarativeRemainder
        suffix output.declarativeRemainder trace ∧
      output.diagnostics = input.diagnostics ++ trace := by
  rcases pragmaItemsTail_production_success_ordinaryOutcome_sound itemsRev result with
    ⟨suffix, itemsEq, ordinary⟩
  rcases pragmaItemsTail_success_diagnosticTrace (input.remainingCount + 1)
      itemsRev input items output result with
    ⟨tracedSuffix, trace, tracedItemsEq, diagnostics, diagnosticEq⟩
  have suffixEq : tracedSuffix = suffix :=
    List.append_cancel_left (tracedItemsEq.symm.trans itemsEq)
  subst tracedSuffix
  exact ⟨suffix, trace, itemsEq, ⟨ordinary, diagnostics⟩, diagnosticEq⟩

/-- Complete item scanning emits only the ordered per-name diagnostic events. -/
theorem pragmaItems_success_diagnosticTrace
    {input output : State} {items : List Identifier}
    (result : pragmaItems input = .ok items output) :
    ∃ trace, DeclarativeGrammar.IdentifierListDiagnosticTrace items trace ∧
      output.diagnostics = input.diagnostics ++ trace := by
  unfold pragmaItems at result
  split at result
  · cases result
    exact ⟨[], .nil, by simp⟩
  · cases firstResult : identifier .pragmaDecl input with
    | invariant error => simp [firstResult] at result
    | reject failure rejected => simp [firstResult] at result
    | ok first afterFirst =>
        simp only [firstResult] at result
        rcases pragmaItemsTail_success_diagnosticTrace (afterFirst.remainingCount + 1)
            [first] afterFirst items output result with
          ⟨suffix, tailTrace, itemsEq, tailDiagnostics, tailEq⟩
        have itemsForm : items = first :: suffix := by simpa using itemsEq
        subst items
        rcases identifier_success_diagnosticTrace .pragmaDecl firstResult with
          ⟨headTrace, headDiagnostics, headEq⟩
        exact ⟨headTrace ++ tailTrace, .cons headDiagnostics tailDiagnostics,
          by rw [tailEq, headEq, List.append_assoc]⟩

/-- Independent item events fix the exact added diagnostic sequence. -/
theorem pragmaItems_success_diagnostics_eq_of_trace
    {input output : State} {items : List Identifier} {trace : List ParseDiagnostic}
    (result : pragmaItems input = .ok items output)
    (diagnostics : DeclarativeGrammar.IdentifierListDiagnosticTrace items trace) :
    output.diagnostics = input.diagnostics ++ trace := by
  rcases pragmaItems_success_diagnosticTrace result with
    ⟨actual, actualTrace, actualEq⟩
  simpa only [actualTrace.trace_unique diagnostics] using actualEq

/-- Executable item success derives the full independent AST, remainder,
and trace relation without assuming the input diagnostics are empty. -/
theorem pragmaItems_success_trace_sound
    {input output : State} {items : List Identifier}
    (result : pragmaItems input = .ok items output) :
    ∃ trace, DeclarativeGrammar.PragmaItemsTraceParses input.declarativeRemainder
        items output.declarativeRemainder trace ∧
      output.diagnostics = input.diagnostics ++ trace := by
  rcases pragmaItems_success_diagnosticTrace result with ⟨trace, diagnostics, diagnosticEq⟩
  exact ⟨trace, ⟨pragmaItems_success_ordinaryOutcome_sound result, diagnostics⟩,
    diagnosticEq⟩

end Solcore.Syntax.Parser.PragmaInternals
