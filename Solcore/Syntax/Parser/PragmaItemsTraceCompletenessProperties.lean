import Solcore.Syntax.Parser.PragmaItemsTraceProperties

/-! Complete independent success traces for pragma suffixes and item lists. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PragmaInternals

private theorem pragmaItemsTail_production_success_ordinary_iff
    (itemsRev : List Identifier) {input : State} {suffix : List Identifier}
    {remainder : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.PragmaItemsTailOrdinaryParses
      input.declarativeRemainder suffix remainder ↔
      ∃ output, pragmaItemsTail (input.remainingCount + 1) itemsRev input =
        .ok (itemsRev.reverse ++ suffix) output ∧
        output.declarativeRemainder = remainder := by
  constructor
  · intro ordinary
    cases result : pragmaItemsTail (input.remainingCount + 1) itemsRev input with
    | ok items output =>
        rcases pragmaItemsTail_production_success_ordinaryOutcome_sound itemsRev result with
          ⟨actual, itemsEq, parsed⟩
        rcases pragmaItemsTail_exactOutcomeSpec.successResultUnique parsed ordinary with
          ⟨suffixEq, after⟩
        exact ⟨output, by simp only [itemsEq, suffixEq], after⟩
    | reject failure rejected =>
        exact False.elim (pragmaItemsTail_exactOutcomeSpec.successRejectDisjoint
          (pragmaItemsTail_production_reject_ordinaryOutcome_sound itemsRev result)
          ⟨suffix, remainder, ordinary⟩)
    | invariant error =>
        exact False.elim (pragmaItemsTail_production_ne_invariant itemsRev input error result)
  · rintro ⟨output, result, after⟩
    rcases pragmaItemsTail_production_success_ordinaryOutcome_sound itemsRev result with
      ⟨actual, itemsEq, parsed⟩
    have suffixEq : suffix = actual := List.append_cancel_left itemsEq
    simpa only [← suffixEq, after] using parsed

/-- With a fixed accumulated prefix, only independently traced suffix items
contribute new diagnostics to a successful production-tail execution. -/
theorem pragmaItemsTail_production_success_diagnostics_eq_of_trace
    (itemsRev : List Identifier) {input output : State}
    {suffix : List Identifier} {trace : List ParseDiagnostic}
    (result : pragmaItemsTail (input.remainingCount + 1) itemsRev input =
      .ok (itemsRev.reverse ++ suffix) output)
    (diagnostics : DeclarativeGrammar.IdentifierListDiagnosticTrace suffix trace) :
    output.diagnostics = input.diagnostics ++ trace := by
  rcases pragmaItemsTail_production_success_trace_sound itemsRev result with
    ⟨actual, actualTrace, itemsEq, parsed, actualEq⟩
  have suffixEq : suffix = actual := List.append_cancel_left itemsEq
  subst actual
  simpa only [parsed.2.trace_unique diagnostics] using actualEq

/-- Independent suffix AST, remainder, and trace correspond exactly to
production-tail success, with the fixed prefix outside the new event sequence. -/
theorem pragmaItemsTail_production_trace_success_iff
    (itemsRev : List Identifier) {input : State} {suffix : List Identifier}
    {remainder : DeclarativeGrammar.Remainder} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.PragmaItemsTailTraceParses
      input.declarativeRemainder suffix remainder trace ↔
      ∃ output, pragmaItemsTail (input.remainingCount + 1) itemsRev input =
        .ok (itemsRev.reverse ++ suffix) output ∧
        output.declarativeRemainder = remainder ∧
        output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · rintro ⟨ordinary, diagnostics⟩
    rcases (pragmaItemsTail_production_success_ordinary_iff itemsRev).mp ordinary with
      ⟨output, result, after⟩
    exact ⟨output, result, after,
      pragmaItemsTail_production_success_diagnostics_eq_of_trace itemsRev result diagnostics⟩
  · rintro ⟨output, result, after, diagnosticEq⟩
    refine ⟨(pragmaItemsTail_production_success_ordinary_iff itemsRev).mpr
      ⟨output, result, after⟩, ?_⟩
    rcases DeclarativeGrammar.identifierListDiagnosticTrace_total suffix with
      ⟨actual, diagnostics⟩
    have actualEq := pragmaItemsTail_production_success_diagnostics_eq_of_trace
      itemsRev result diagnostics
    have traceEq : actual = trace := List.append_cancel_left
      (actualEq.symm.trans diagnosticEq)
    simpa only [traceEq] using diagnostics

private theorem pragmaItems_success_ordinary_iff
    {input : State} {items : List Identifier} {remainder : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.PragmaItemsOrdinaryParses input.declarativeRemainder items remainder ↔
      ∃ output, pragmaItems input = .ok items output ∧
        output.declarativeRemainder = remainder :=
  ordinary_success_iff_exists_ok pragmaItems pragmaItems_exactOutcomeSpec
    (pragmaItems_ne_invariant input)
    pragmaItems_success_ordinaryOutcome_sound pragmaItems_reject_ordinaryOutcome_sound

/-- Complete item grammar and diagnostic order correspond exactly to execution,
including empty lists and silent trailing commas. -/
theorem pragmaItems_trace_success_iff
    {input : State} {items : List Identifier} {remainder : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic} :
    DeclarativeGrammar.PragmaItemsTraceParses input.declarativeRemainder items remainder trace ↔
      ∃ output, pragmaItems input = .ok items output ∧
        output.declarativeRemainder = remainder ∧
        output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · rintro ⟨ordinary, diagnostics⟩
    rcases pragmaItems_success_ordinary_iff.mp ordinary with ⟨output, result, after⟩
    exact ⟨output, result, after, pragmaItems_success_diagnostics_eq_of_trace result diagnostics⟩
  · rintro ⟨output, result, after, diagnosticEq⟩
    refine ⟨pragmaItems_success_ordinary_iff.mpr ⟨output, result, after⟩, ?_⟩
    rcases pragmaItems_success_diagnosticTrace result with ⟨actual, diagnostics, actualEq⟩
    have traceEq : actual = trace := List.append_cancel_left
      (actualEq.symm.trans diagnosticEq)
    simpa only [traceEq] using diagnostics

end Solcore.Syntax.Parser.PragmaInternals
