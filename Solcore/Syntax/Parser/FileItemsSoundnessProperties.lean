import Solcore.Syntax.Parser.DeclarativePrimitiveProperties
import Solcore.Syntax.Parser.FileRecoveryProperties

/-! Diagnostic-free soundness for complete-file item accumulation. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

private theorem parseItems_success_sound_strong
    (itemParses : DeclarativeGrammar.Remainder → TopItem →
      DeclarativeGrammar.Remainder → Prop)
    (itemSound : ∀ {input next : State} {item : TopItem},
      next.diagnosticsRev = [] →
      parseItemsItem input = .ok item next →
      itemParses input.declarativeRemainder item next.declarativeRemainder)
    (itemReflectsDiagnosticFree : ∀ {input next : State} {item : TopItem},
      parseItemsItem input = .ok item next →
      next.diagnosticsRev = [] →
      input.diagnosticsRev = []) :
    ∀ fuel itemsRev input items next,
      next.diagnosticsRev = [] →
      parseItems fuel itemsRev input = .ok items next →
      input.diagnosticsRev = [] ∧
        ∃ suffix,
          items = itemsRev.reverse ++ suffix ∧
          DeclarativeGrammar.TopItemsParses itemParses
            input.declarativeRemainder suffix next.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro itemsRev input items next diagnosticFree parsed
      simp [parseItems] at parsed
  | succ fuel inductionHypothesis =>
      intro itemsRev input items next diagnosticFree parsed
      unfold parseItems at parsed
      split at parsed
      · rename_i atEnd
        cases parsed
        refine ⟨diagnosticFree, [], by simp, ?_⟩
        apply DeclarativeGrammar.TopItemsParses.done
        simpa [State.atEnd, State.declarativeRemainder] using atEnd
      · cases itemResult : parseItemsItem input with
        | invariant error =>
            simp [itemResult] at parsed
        | ok item afterItem =>
            simp only [itemResult] at parsed
            split at parsed
            · rename_i progress
              rcases inductionHypothesis (item :: itemsRev) afterItem
                  items next diagnosticFree parsed with
                ⟨afterItemDiagnosticFree, suffix, itemsEq, restGrammar⟩
              have inputDiagnosticFree :=
                itemReflectsDiagnosticFree itemResult
                  afterItemDiagnosticFree
              have itemGrammar := itemSound afterItemDiagnosticFree itemResult
              refine ⟨inputDiagnosticFree, item :: suffix, ?_, ?_⟩
              · rw [itemsEq]
                simp [List.reverse_cons, List.append_assoc]
              · exact DeclarativeGrammar.TopItemsParses.next itemGrammar
                  (by simpa [State.declarativeRemainder] using progress)
                  restGrammar
            · simp at parsed
        | reject failure failedState =>
            simp only [itemResult] at parsed
            let rewound : State := {
              failedState with cursor := input.cursor
            }
            change (if atTopItemStart input then
                .ok itemsRev.reverse (rewound.emit failure.toDiagnostic)
              else
                match recoverTopItem rewound with
                | .ok item next => parseItems fuel (item :: itemsRev) next
                | .reject recoveryFailure next =>
                    .reject recoveryFailure next
                | .invariant error => .invariant error) =
              .ok items next at parsed
            split at parsed
            · cases parsed
              simp [State.emit] at diagnosticFree
            · cases recoveryResult : recoverTopItem rewound with
              | invariant error =>
                  simp [recoveryResult] at parsed
              | reject recoveryFailure rejected =>
                  simp [recoveryResult] at parsed
              | ok recovered afterRecovery =>
                  simp only [recoveryResult] at parsed
                  rcases inductionHypothesis (recovered :: itemsRev)
                      afterRecovery items next diagnosticFree parsed with
                    ⟨recoveryDiagnosticFree, suffix, itemsEq, restGrammar⟩
                  exact False.elim
                    (recoverTopItem_diagnostics_ne_nil_onSuccess
                      recoveryResult recoveryDiagnosticFree)

/--
If successful item parsing is sound and cannot erase an incoming diagnostic,
a diagnostic-free successful file loop recognizes exactly the forward suffix
added after its existing reverse accumulator.
-/
theorem parseItems_success_sound_of_diagnosticFree
    (itemParses : DeclarativeGrammar.Remainder → TopItem →
      DeclarativeGrammar.Remainder → Prop)
    (itemSound : ∀ {input next : State} {item : TopItem},
      next.diagnosticsRev = [] →
      parseItemsItem input = .ok item next →
      itemParses input.declarativeRemainder item next.declarativeRemainder)
    (itemReflectsDiagnosticFree : ∀ {input next : State} {item : TopItem},
      parseItemsItem input = .ok item next →
      next.diagnosticsRev = [] →
      input.diagnosticsRev = [])
    {fuel : Nat} {itemsRev : List TopItem} {input next : State}
    {items : List TopItem}
    (diagnosticFree : next.diagnosticsRev = [])
    (parsed : parseItems fuel itemsRev input = .ok items next) :
    ∃ suffix,
      items = itemsRev.reverse ++ suffix ∧
      DeclarativeGrammar.TopItemsParses itemParses
        input.declarativeRemainder suffix next.declarativeRemainder :=
  (parseItems_success_sound_strong itemParses itemSound
    itemReflectsDiagnosticFree fuel itemsRev input items next
    diagnosticFree parsed).2

end Solcore.Syntax.Parser.FileInternals
