import Solcore.Syntax.DeclarativeTransactionalFallbackOutcomeProperties
import Solcore.Syntax.Parser.DeclarativePrimitiveProperties
import Solcore.Syntax.Parser.Yul.Statement

/-!
Executable outcome bridges for recognized inline-Yul statement fallback.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every wrapper success follows the preferred ordinary relation or exact
preferred rejection followed by fallback ordinary success at the original
input. -/
theorem recognizedYulStatementOrFallback_success_ordinary_sound
    (primary fallback : Parser YulStmt)
    (primaryParses fallbackParses : DeclarativeGrammar.Remainder → YulStmt →
      DeclarativeGrammar.Remainder → Prop)
    (primaryRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (primarySuccessSound : ∀ {input output : State} {value : YulStmt},
      primary input = .ok value output → primaryParses
        input.declarativeRemainder value output.declarativeRemainder)
    (primaryRejectSound : ∀ {input rejected : State} {failure : Failure},
      primary input = .reject failure rejected → primaryRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    (fallbackSuccessSound : ∀ {input output : State} {value : YulStmt},
      fallback input = .ok value output → fallbackParses
        input.declarativeRemainder value output.declarativeRemainder)
    {input output : State} {value : YulStmt}
    (result : recognizedYulStatementOrFallback primary fallback input =
      .ok value output) :
    DeclarativeGrammar.TransactionalFallbackOrdinaryParses primaryParses
      primaryRejects fallbackParses input.declarativeRemainder value
        output.declarativeRemainder := by
  unfold recognizedYulStatementOrFallback at result
  cases primaryResult : primary input with
  | ok primaryValue afterPrimary =>
      simp only [primaryResult] at result
      cases result
      exact .primary (primarySuccessSound primaryResult)
  | invariant error => simp [primaryResult] at result
  | reject primaryFailure primaryRejected =>
      simp only [primaryResult] at result
      cases fallbackResult : fallback input with
      | invariant error => simp [fallbackResult] at result
      | reject fallbackFailure fallbackRejected =>
          simp [fallbackResult] at result
      | ok fallbackValue afterFallback =>
          simp only [fallbackResult] at result
          let reset : State := {
            afterFallback with diagnosticsRev := input.diagnosticsRev
          }
          have parsed :
              DeclarativeGrammar.TransactionalFallbackOrdinaryParses
                primaryParses primaryRejects fallbackParses
                input.declarativeRemainder fallbackValue
                  afterFallback.declarativeRemainder :=
            .fallback (primaryRejectSound primaryResult)
              (fallbackSuccessSound fallbackResult)
          change Reply.ok fallbackValue
            (reset.emit primaryFailure.toDiagnostic) = .ok value output
              at result
          cases result
          simpa [reset, State.emit, State.declarativeRemainder] using parsed

/-- A wrapper rejection decomposes into both branch rejections.  The returned
failure is exactly the preferred failure, and the returned state is the
original input state. -/
theorem recognizedYulStatementOrFallback_reject_decomposition
    (primary fallback : Parser YulStmt)
    {input rejected : State} {failure : Failure}
    (result : recognizedYulStatementOrFallback primary fallback input =
      .reject failure rejected) :
    ∃ primaryRejected fallbackFailure fallbackRejected,
      primary input = .reject failure primaryRejected ∧
        fallback input = .reject fallbackFailure fallbackRejected ∧
        rejected = input := by
  unfold recognizedYulStatementOrFallback at result
  cases primaryResult : primary input with
  | ok primaryValue afterPrimary => simp [primaryResult] at result
  | invariant error => simp [primaryResult] at result
  | reject primaryFailure primaryRejected =>
      simp only [primaryResult] at result
      cases fallbackResult : fallback input with
      | ok fallbackValue afterFallback => simp [fallbackResult] at result
      | invariant error => simp [fallbackResult] at result
      | reject fallbackFailure fallbackRejected =>
          simp only [fallbackResult] at result
          cases result
          exact ⟨primaryRejected, fallbackFailure, fallbackRejected,
            rfl, rfl, rfl⟩

/-- Every wrapper rejection follows the exact both-rejected relation and is
non-consuming even when either branch reported a different rejected state. -/
theorem recognizedYulStatementOrFallback_reject_sound
    (primary fallback : Parser YulStmt)
    (primaryRejects fallbackRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (primaryRejectSound : ∀ {input rejected : State} {failure : Failure},
      primary input = .reject failure rejected → primaryRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    (fallbackRejectSound : ∀ {input rejected : State} {failure : Failure},
      fallback input = .reject failure rejected → fallbackRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : recognizedYulStatementOrFallback primary fallback input =
      .reject failure rejected) :
    DeclarativeGrammar.TransactionalFallbackRejects primaryRejects
      fallbackRejects input.declarativeRemainder
        rejected.declarativeRemainder := by
  rcases recognizedYulStatementOrFallback_reject_decomposition primary
      fallback result with
    ⟨primaryRejected, fallbackFailure, fallbackRejected, primaryResult,
      fallbackResult, rejectedEq⟩
  subst rejected
  exact .both (primaryRejectSound primaryResult)
    (fallbackRejectSound fallbackResult)

end Solcore.Syntax.Parser
