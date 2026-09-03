import Solcore.Syntax.Parser.PragmaItemsTraceCompletenessProperties
import Solcore.Syntax.Parser.PragmaDeclarationOrdinaryOutcomeSoundnessProperties

/-! Complete pragma success traces: raw names and punctuation remain silent. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem bind_ok_components {alpha beta : Type}
    {first : Parser alpha} {next : alpha → Parser beta}
    {input output : State} {value : beta}
    (result : (first >>= next) input = .ok value output) :
    ∃ firstValue afterFirst,
      first input = .ok firstValue afterFirst ∧
        next firstValue afterFirst = .ok value output := by
  change (match first input with
    | .ok firstValue afterFirst => next firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value output at result
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      rw [firstResult] at result
      exact ⟨firstValue, afterFirst, rfl, result⟩
  | reject failure rejected => rw [firstResult] at result; contradiction
  | invariant error => rw [firstResult] at result; contradiction

/-- Only the checked item identifiers emit events during a successful pragma.
The raw pragma name contributes none, even when its spelling has a hyphen. -/
theorem pragmaDecl_success_diagnosticTrace
    {input output : State} {declaration : PragmaDecl}
    (result : pragmaDecl input = .ok declaration output) :
    ∃ trace, DeclarativeGrammar.IdentifierListDiagnosticTrace
        declaration.value.items trace ∧
      output.diagnostics = input.diagnostics ++ trace := by
  unfold pragmaDecl at result
  rcases bind_ok_components result with
    ⟨pragmaKeyword, afterKeyword, keywordResult, nameStage⟩
  rcases bind_ok_components nameStage with
    ⟨name, afterName, nameResult, itemsStage⟩
  rcases bind_ok_components itemsStage with
    ⟨items, afterItems, itemsResult, semicolonStage⟩
  rcases bind_ok_components semicolonStage with
    ⟨semicolon, afterSemicolon, semicolonResult, finished⟩
  cases finished
  have keywordSilent := acceptToken_success_diagnostics_eq
    (.keyword .pragmaKw) .pragmaDecl (· == .keyword .pragmaKw) keywordResult
  have nameSilent := rawIdentifier_success_diagnostics_eq .pragmaDecl nameResult
  have semicolonSilent := acceptToken_success_diagnostics_eq
    (.symbol .semicolon) .pragmaDecl (· == .symbol .semicolon) semicolonResult
  rcases PragmaInternals.pragmaItems_success_diagnosticTrace itemsResult with
    ⟨trace, diagnostics, diagnosticEq⟩
  exact ⟨trace, diagnostics,
    by rw [semicolonSilent, diagnosticEq, nameSilent, keywordSilent]⟩

/-- An independent item trace determines the complete added pragma diagnostics. -/
theorem pragmaDecl_success_diagnostics_eq_of_trace
    {input output : State} {declaration : PragmaDecl} {trace : List ParseDiagnostic}
    (result : pragmaDecl input = .ok declaration output)
    (diagnostics : DeclarativeGrammar.IdentifierListDiagnosticTrace
      declaration.value.items trace) :
    output.diagnostics = input.diagnostics ++ trace := by
  rcases pragmaDecl_success_diagnosticTrace result with ⟨actual, actualTrace, actualEq⟩
  simpa only [actualTrace.trace_unique diagnostics] using actualEq

/-- Every successful pragma derives the complete independent traced grammar. -/
theorem pragmaDecl_success_trace_sound
    {input output : State} {declaration : PragmaDecl}
    (result : pragmaDecl input = .ok declaration output) :
    ∃ trace, DeclarativeGrammar.PragmaDeclTraceParses input.declarativeRemainder
        declaration output.declarativeRemainder trace ∧
      output.diagnostics = input.diagnostics ++ trace := by
  rcases pragmaDecl_success_diagnosticTrace result with ⟨trace, diagnostics, diagnosticEq⟩
  exact ⟨trace, ⟨pragmaDecl_success_ordinaryOutcome_sound result, diagnostics⟩,
    diagnosticEq⟩

private theorem pragmaDecl_success_ordinary_iff
    {input : State} {declaration : PragmaDecl} {remainder : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.PragmaDeclOrdinaryParses input.declarativeRemainder
        declaration remainder ↔
      ∃ output, pragmaDecl input = .ok declaration output ∧
        output.declarativeRemainder = remainder :=
  ordinary_success_iff_exists_ok pragmaDecl pragmaDecl_exactOutcomeSpec
    (pragmaDecl_ne_invariant input)
    pragmaDecl_success_ordinaryOutcome_sound pragmaDecl_reject_ordinaryOutcome_sound

/-- Independent pragma AST, remainder, and ordered diagnostic trace are
equivalent to exact executable success, preserving every prior diagnostic. -/
theorem pragmaDecl_trace_success_iff
    {input : State} {declaration : PragmaDecl} {remainder : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic} :
    DeclarativeGrammar.PragmaDeclTraceParses input.declarativeRemainder
        declaration remainder trace ↔
      ∃ output, pragmaDecl input = .ok declaration output ∧
        output.declarativeRemainder = remainder ∧
        output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · rintro ⟨ordinary, diagnostics⟩
    rcases pragmaDecl_success_ordinary_iff.mp ordinary with ⟨output, result, after⟩
    exact ⟨output, result, after, pragmaDecl_success_diagnostics_eq_of_trace result diagnostics⟩
  · rintro ⟨output, result, after, diagnosticEq⟩
    refine ⟨pragmaDecl_success_ordinary_iff.mpr ⟨output, result, after⟩, ?_⟩
    rcases pragmaDecl_success_diagnosticTrace result with ⟨actual, diagnostics, actualEq⟩
    have traceEq : actual = trace := List.append_cancel_left
      (actualEq.symm.trans diagnosticEq)
    simpa only [traceEq] using diagnostics

end Solcore.Syntax.Parser
