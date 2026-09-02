import Solcore.Syntax.DeclarativeSelectedAliasOutcomeGrammar
import Solcore.Syntax.Parser.CoreIdentifierOutcomeSoundnessProperties
import Solcore.Syntax.Parser.CoreTypeOutcomePrimitiveProperties
import Solcore.Syntax.Parser.Import

/-! Exact executable rejection reflection for selected-import aliases. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every executable selected-alias rejection is the missing identifier after
its positively guarded and exactly consumed `as` marker. -/
theorem selectedAlias_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : ImportInternals.selectedAlias input = .reject failure rejected) :
    DeclarativeGrammar.SelectedAliasRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold ImportInternals.selectedAlias getState at result
  simp only [bind] at result
  by_cases present : isKeyword input .asKw = true
  · rcases keyword_eq_ok_of_isKeyword_eq_true .asKw .importDecl present with
      ⟨marker, markerResult⟩
    simp only [present, if_true, markerResult] at result
    cases nameResult : identifier .importDecl
        { input with cursor := input.cursor + 1 } with
    | invariant error => simp [nameResult] at result
    | ok name afterName => simp [nameResult, pure] at result
    | reject nameFailure nameRejected =>
        simp only [nameResult] at result
        cases result
        exact .nameRejected marker.span
          (keyword_success_exactTokenParses .asKw .importDecl markerResult)
          (identifier_reject_sound .importDecl nameResult)
  · have absent : isKeyword input .asKw = false :=
      Bool.eq_false_iff.mpr present
    simp [absent, pure] at result

end Solcore.Syntax.Parser
