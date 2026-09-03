import Solcore.Syntax.DeclarativePragmaItemsRejectionTraceProperties
import Solcore.Syntax.Parser.PragmaItemsTraceProperties

/-! Exact uncommitted reports and committed prefix events for item rejection. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PragmaInternals

private theorem identifier_success_context_eq (context : ParseContext)
    {input output : State} {name : Identifier}
    (result : identifier context input = .ok name output) :
    output.file = input.file ∧ output.window = input.window := by
  unfold identifier at result
  cases raw : rawIdentifier context input with
  | reject failure rejected => simp [raw] at result
  | invariant error => simp [raw] at result
  | ok parsed afterName =>
      rcases rawIdentifier_ok_tokenAt context raw with ⟨_, rfl⟩
      simp only [raw] at result
      split at result <;> cases result <;> exact ⟨rfl, rfl⟩

private theorem identifier_rejected_report
    {input rejected : State} {failure : Failure}
    (result : identifier .pragmaDecl input = .reject failure rejected) :
    DeclarativeGrammar.RejectAtReports input.file.id input.window.endByte
      { head := .identifier, tail := [] } .pragmaDecl
      rejected.declarativeRemainder failure.toDiagnostic := by
  have stateEq := identifier_reject_state_eq .pragmaDecl result
  subst rejected
  exact ((identifier_reject_reports_iff .pragmaDecl).mpr ⟨failure, result, rfl⟩).2

/-- Rejection at any fuel retains exactly the events of newly checked names.
The accumulator never contributes events, and the final failure is not emitted. -/
theorem pragmaItemsTail_reject_trace_sound :
    ∀ fuel itemsRev input failure rejected,
      pragmaItemsTail fuel itemsRev input = .reject failure rejected →
      ∃ trace,
        DeclarativeGrammar.PragmaItemsTailTraceRejects input.file.id input.window.endByte
          input.declarativeRemainder rejected.declarativeRemainder
          failure.toDiagnostic trace ∧
        rejected.diagnostics = input.diagnostics ++ trace := by
  intro fuel
  induction fuel with
  | zero =>
      intro itemsRev input failure rejected result
      simp [pragmaItemsTail] at result
  | succ fuel ih =>
      intro itemsRev input failure rejected result
      unfold pragmaItemsTail at result
      cases commaPresent : isSymbol input .comma with
      | false => simp [commaPresent] at result
      | true =>
          rcases symbol_eq_ok_of_isSymbol_eq_true .comma .pragmaDecl commaPresent with
            ⟨comma, commaResult⟩
          simp only [commaPresent, if_true, commaResult] at result
          split at result
          · contradiction
          · rename_i semicolonAbsent
            cases itemResult : identifier .pragmaDecl
                { input with cursor := input.cursor + 1 } with
            | invariant error => simp [itemResult] at result
            | reject itemFailure itemRejected =>
                simp only [itemResult] at result
                cases result
                refine ⟨[], ⟨[], .identifierRejected comma.span
                  (symbol_success_exactTokenParses .comma .pragmaDecl commaResult)
                  (symbolAbsentAt_of_isSymbol_eq_false .semicolon
                    (by simpa using semicolonAbsent))
                  (identifier_reject_sound .pragmaDecl itemResult), .nil,
                  identifier_rejected_report
                    (input := { input with cursor := input.cursor + 1 }) itemResult⟩, ?_⟩
                simpa only [List.append_nil, State.diagnostics] using
                  identifier_reject_diagnostics_eq .pragmaDecl itemResult
            | ok item afterItem =>
                simp only [itemResult] at result
                rcases ih (item :: itemsRev) afterItem failure rejected result with
                  ⟨tailTrace, ⟨consumed, tailParsed, tailEvents, report⟩, tailEq⟩
                rcases identifier_success_diagnosticTrace .pragmaDecl itemResult with
                  ⟨headTrace, headEvents, headEq⟩
                rcases identifier_success_context_eq .pragmaDecl itemResult with
                  ⟨fileEq, windowEq⟩
                refine ⟨headTrace ++ tailTrace,
                  ⟨item :: consumed, .laterRejected comma.span
                    (symbol_success_exactTokenParses .comma .pragmaDecl commaResult)
                    (symbolAbsentAt_of_isSymbol_eq_false .semicolon
                      (by simpa using semicolonAbsent))
                    (identifier_success_sound .pragmaDecl itemResult) tailParsed,
                    .cons headEvents tailEvents, ?_⟩, ?_⟩
                · simpa only [fileEq, windowEq] using report
                · rw [tailEq, headEq, List.append_assoc]
                  rfl

/-- Full item rejection includes the first successful checked name and every
later successful item in order, with no event for the rejected identifier. -/
theorem pragmaItems_reject_trace_sound
    {input rejected : State} {failure : Failure}
    (result : pragmaItems input = .reject failure rejected) :
    ∃ trace,
      DeclarativeGrammar.PragmaItemsTraceRejects input.file.id input.window.endByte
        input.declarativeRemainder rejected.declarativeRemainder
        failure.toDiagnostic trace ∧
      rejected.diagnostics = input.diagnostics ++ trace := by
  unfold pragmaItems at result
  split at result
  · contradiction
  · rename_i semicolonAbsent
    cases firstResult : identifier .pragmaDecl input with
    | invariant error => simp [firstResult] at result
    | reject firstFailure firstRejected =>
        simp only [firstResult] at result
        cases result
        refine ⟨[], ⟨[], .firstIdentifierRejected
          (symbolAbsentAt_of_isSymbol_eq_false .semicolon
            (by simpa using semicolonAbsent))
          (identifier_reject_sound .pragmaDecl firstResult), .nil,
          identifier_rejected_report firstResult⟩, ?_⟩
        simpa only [List.append_nil] using
          identifier_reject_diagnostics_eq .pragmaDecl firstResult
    | ok first afterFirst =>
        simp only [firstResult] at result
        rcases pragmaItemsTail_reject_trace_sound (afterFirst.remainingCount + 1)
            [first] afterFirst failure rejected result with
          ⟨tailTrace, ⟨consumed, tailParsed, tailEvents, report⟩, tailEq⟩
        rcases identifier_success_diagnosticTrace .pragmaDecl firstResult with
          ⟨headTrace, headEvents, headEq⟩
        rcases identifier_success_context_eq .pragmaDecl firstResult with
          ⟨fileEq, windowEq⟩
        refine ⟨headTrace ++ tailTrace,
          ⟨first :: consumed, .tailRejected
            (symbolAbsentAt_of_isSymbol_eq_false .semicolon
              (by simpa using semicolonAbsent))
            (identifier_success_sound .pragmaDecl firstResult) tailParsed,
            .cons headEvents tailEvents, ?_⟩, ?_⟩
        · simpa only [fileEq, windowEq] using report
        · rw [tailEq, headEq, List.append_assoc]

end Solcore.Syntax.Parser.PragmaInternals
