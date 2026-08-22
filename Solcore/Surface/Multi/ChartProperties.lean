import Solcore.Surface.Multi.Chart
import Solcore.Surface.Multi.ParserJudgment

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Solcore.Workspace
open Grammar

/-- A normalized Phase-B observation denotes exactly one declarative guard
decision, provided its positive bit and G02 pipe bit are exact. -/
theorem guardEvidence_iff_classified_observation
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (key : GuardInstanceKey tokens)
    (positive pipeAtSite : Bool)
    (positiveExact :
      positive = true ↔ GuardEvidence file tokens key .positive)
    (pipeExact :
      key.guard = .G02_matchArmBoundary →
        (pipeAtSite = true ↔
          SymbolAtBoundary file tokens key.siteCursor .pipe))
    (decision : GuardDecision) :
    Chart.classifyGuardObservation key.guard positive pipeAtSite =
        decision ↔
      GuardEvidence file tokens key decision := by
  have classifiedEvidence : GuardEvidence file tokens key
      (Chart.classifyGuardObservation key.guard positive pipeAtSite) := by
    rcases key with ⟨guard, contextStart, siteCursor, ordered⟩
    by_cases selected : positive = true
    · have evidence := positiveExact.mp selected
      simpa [Chart.classifyGuardObservation, selected] using evidence
    · have positiveFalse : positive = false :=
        Bool.eq_false_iff.mpr selected
      have notPositive : ¬ GuardEvidence file tokens
          { guard := guard, contextStart := contextStart,
            siteCursor := siteCursor, ordered := ordered }
          .positive := by
        intro evidence
        exact selected (positiveExact.mpr evidence)
      cases guard with
      | G01_statementIf =>
          simp only [Chart.classifyGuardObservation, positiveFalse,
            Bool.false_eq_true, ↓reduceIte]
          refine ⟨owned, ?_⟩
          intro evidence
          exact notPositive ⟨owned, evidence⟩
      | G02_matchArmBoundary =>
          by_cases pipeSelected : pipeAtSite = true
          · have pipeEvidence := (pipeExact rfl).mp pipeSelected
            simp only [Chart.classifyGuardObservation, positiveFalse,
              Bool.false_eq_true, ↓reduceIte, pipeSelected]
            refine ⟨owned, pipeEvidence, ?_⟩
            intro evidence
            exact notPositive ⟨owned, evidence⟩
          · have pipeFalse : pipeAtSite = false :=
              Bool.eq_false_iff.mpr pipeSelected
            have noPipe :
                ¬ SymbolAtBoundary file tokens siteCursor .pipe := by
              intro evidence
              exact pipeSelected ((pipeExact rfl).mpr evidence)
            simp only [Chart.classifyGuardObservation, positiveFalse,
              Bool.false_eq_true, ↓reduceIte, pipeFalse]
            exact ⟨owned, noPipe⟩
      | G03_parameterComptime =>
          simp only [Chart.classifyGuardObservation, positiveFalse,
            Bool.false_eq_true, ↓reduceIte]
          refine ⟨owned, ?_⟩
          intro evidence
          exact notPositive ⟨owned, evidence⟩
      | G04_letComptime =>
          simp only [Chart.classifyGuardObservation, positiveFalse,
            Bool.false_eq_true, ↓reduceIte]
          refine ⟨owned, ?_⟩
          intro evidence
          exact notPositive ⟨owned, evidence⟩
      | G05_typeComptime =>
          simp only [Chart.classifyGuardObservation, positiveFalse,
            Bool.false_eq_true, ↓reduceIte]
          refine ⟨owned, ?_⟩
          intro evidence
          exact notPositive ⟨owned, evidence⟩
      | G06_patternComptime =>
          simp only [Chart.classifyGuardObservation, positiveFalse,
            Bool.false_eq_true, ↓reduceIte]
          refine ⟨owned, ?_⟩
          intro evidence
          exact notPositive ⟨owned, evidence⟩
      | G07_leadingDotArguments =>
          simp only [Chart.classifyGuardObservation, positiveFalse,
            Bool.false_eq_true, ↓reduceIte]
          refine ⟨owned, ?_⟩
          intro evidence
          exact notPositive ⟨owned, evidence⟩
      | G08_terminalExpression =>
          simp only [Chart.classifyGuardObservation, positiveFalse,
            Bool.false_eq_true, ↓reduceIte]
          refine ⟨owned, ?_⟩
          intro evidence
          exact notPositive ⟨owned, evidence⟩
      | G09_genericContext =>
          simp only [Chart.classifyGuardObservation, positiveFalse,
            Bool.false_eq_true, ↓reduceIte]
          refine ⟨owned, ?_⟩
          intro evidence
          exact notPositive ⟨owned, evidence⟩
  constructor
  · intro selected
    simpa only [selected] using classifiedEvidence
  · intro evidence
    exact GuardEvidence.functional classifiedEvidence evidence

/-- Pointwise-exact normalized observations assemble a correct final table. -/
theorem phaseBCorrect_of_exact_guard_observations
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (positive pipeAtSite : GuardInstanceKey tokens → Bool)
    (positiveExact : ∀ key,
      positive key = true ↔
        GuardEvidence file tokens key .positive)
    (pipeExact : ∀ key,
      key.guard = .G02_matchArmBoundary →
        (pipeAtSite key = true ↔
          SymbolAtBoundary file tokens key.siteCursor .pipe)) :
    PhaseBCorrect file tokens (fun key =>
      .final (Chart.classifyGuardObservation key.guard
        (positive key) (pipeAtSite key))) := by
  intro key decision
  rw [GuardMemoState.final.injEq]
  exact guardEvidence_iff_classified_observation owned key
    (positive key) (pipeAtSite key) (positiveExact key)
      (pipeExact key) decision

end Solcore.Surface.Multi
