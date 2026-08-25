import Solcore.Surface.Multi.RootlessNormalizationDottedRank

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar
open Solcore.Workspace

/-- A component/origin/phase potential. The boundary count separates
components, while one phase row separates adjacent origins. -/
def frontierDottedLexicographicPotential {tokens : List Token}
    (phaseWidth : Nat) (component phase : DottedRhs → Nat) :
    FrontierDottedGrammarPotential tokens :=
  fun dotted origin _current =>
    component dotted * (tokens.length + 2) * phaseWidth +
      (origin.val * phaseWidth + phase dotted)

private theorem frontierDottedLexicographic_local_lt
    {tokens : List Token} {phaseWidth : Nat}
    {phase : DottedRhs → Nat} (dotted : DottedRhs)
    (origin : Boundary tokens) (phaseBound : phase dotted < phaseWidth) :
    origin.val * phaseWidth + phase dotted <
      (tokens.length + 2) * phaseWidth := by
  calc
    origin.val * phaseWidth + phase dotted <
        origin.val * phaseWidth + phaseWidth :=
      Nat.add_lt_add_left phaseBound _
    _ = (origin.val + 1) * phaseWidth := by
      simp only [Nat.add_mul, Nat.one_mul]
    _ ≤ (tokens.length + 2) * phaseWidth :=
      Nat.mul_le_mul_right phaseWidth origin.isLt

/-- A strict component drop dominates every origin and phase coordinate. -/
theorem frontierDottedLexicographicPotential_lt_of_component
    {tokens : List Token} {phaseWidth : Nat}
    {component phase : DottedRhs → Nat}
    {before after : DottedRhs}
    (beforeOrigin beforeCurrent afterOrigin afterCurrent : Boundary tokens)
    (componentLt : component after < component before)
    (afterPhaseBound : phase after < phaseWidth) :
    frontierDottedLexicographicPotential phaseWidth component phase
        after afterOrigin afterCurrent <
      frontierDottedLexicographicPotential phaseWidth component phase
        before beforeOrigin beforeCurrent := by
  have localLt := frontierDottedLexicographic_local_lt
    after afterOrigin afterPhaseBound
  have componentStep : component after + 1 ≤ component before :=
    componentLt
  have blockLe :
      (component after + 1) * (tokens.length + 2) * phaseWidth ≤
        component before * (tokens.length + 2) * phaseWidth := by
    exact Nat.mul_le_mul_right phaseWidth
      (Nat.mul_le_mul_right (tokens.length + 2) componentStep)
  unfold frontierDottedLexicographicPotential
  calc
    component after * (tokens.length + 2) * phaseWidth +
          (afterOrigin.val * phaseWidth + phase after) <
        component after * (tokens.length + 2) * phaseWidth +
          (tokens.length + 2) * phaseWidth :=
      Nat.add_lt_add_left localLt _
    _ = (component after + 1) * (tokens.length + 2) * phaseWidth := by
      simp only [Nat.add_mul, Nat.one_mul]
    _ ≤ component before * (tokens.length + 2) * phaseWidth := blockLe
    _ ≤ component before * (tokens.length + 2) * phaseWidth +
          (beforeOrigin.val * phaseWidth + phase before) := by omega

/-- Inside one component and origin, a strict phase drop is a potential
drop. -/
theorem frontierDottedLexicographicPotential_lt_of_phase
    {tokens : List Token} {phaseWidth : Nat}
    {component phase : DottedRhs → Nat}
    {before after : DottedRhs}
    (beforeOrigin beforeCurrent afterOrigin afterCurrent : Boundary tokens)
    (componentEq : component after = component before)
    (originEq : afterOrigin = beforeOrigin)
    (phaseLt : phase after < phase before) :
    frontierDottedLexicographicPotential phaseWidth component phase
        after afterOrigin afterCurrent <
      frontierDottedLexicographicPotential phaseWidth component phase
        before beforeOrigin beforeCurrent := by
  subst afterOrigin
  unfold frontierDottedLexicographicPotential
  rw [componentEq]
  omega

/-- Inside one component, moving to a strictly earlier origin dominates the
entire bounded phase row. -/
theorem frontierDottedLexicographicPotential_lt_of_origin
    {tokens : List Token} {phaseWidth : Nat}
    {component phase : DottedRhs → Nat}
    {before after : DottedRhs}
    (beforeOrigin beforeCurrent afterOrigin afterCurrent : Boundary tokens)
    (componentEq : component after = component before)
    (originLt : afterOrigin.val < beforeOrigin.val)
    (afterPhaseBound : phase after < phaseWidth) :
    frontierDottedLexicographicPotential phaseWidth component phase
        after afterOrigin afterCurrent <
      frontierDottedLexicographicPotential phaseWidth component phase
        before beforeOrigin beforeCurrent := by
  have rowLt :
      afterOrigin.val * phaseWidth + phase after <
        beforeOrigin.val * phaseWidth + phase before := by
    calc
      afterOrigin.val * phaseWidth + phase after <
          afterOrigin.val * phaseWidth + phaseWidth :=
        Nat.add_lt_add_left afterPhaseBound _
      _ = (afterOrigin.val + 1) * phaseWidth := by
        simp only [Nat.add_mul, Nat.one_mul]
      _ ≤ beforeOrigin.val * phaseWidth :=
        Nat.mul_le_mul_right phaseWidth originLt
      _ ≤ beforeOrigin.val * phaseWidth + phase before :=
        Nat.le_add_right _ _
  unfold frontierDottedLexicographicPotential
  rw [componentEq]
  exact Nat.add_lt_add_left rowLt _

/-- Closed component and phase bounds fit the concrete potential inside the
finite dotted-frame search range. -/
theorem frontierDottedLexicographicPotential_bounded
    {tokens : List Token} {phaseWidth componentMax : Nat}
    {component phase : DottedRhs → Nat}
    (componentBound : ∀ dotted, component dotted ≤ componentMax)
    (phaseBound : ∀ dotted, phase dotted < phaseWidth)
    (capacity : (componentMax + 1) * phaseWidth ≤ D * 2) :
    ∀ (dotted : DottedRhs) (origin current : Boundary tokens),
      frontierDottedLexicographicPotential phaseWidth component phase
          dotted origin current <
        frontierDottedGrammarFrameCount tokens + 1 := by
  intro dotted origin current
  have localLt := frontierDottedLexicographic_local_lt
    dotted origin (phaseBound dotted)
  have componentStep : component dotted + 1 ≤ componentMax + 1 :=
    Nat.succ_le_succ (componentBound dotted)
  have firstBound :
      (component dotted + 1) * (tokens.length + 2) * phaseWidth ≤
        (componentMax + 1) * phaseWidth * (tokens.length + 2) := by
    calc
      (component dotted + 1) * (tokens.length + 2) * phaseWidth =
          (component dotted + 1) * phaseWidth * (tokens.length + 2) := by
        ac_rfl
      _ ≤ (componentMax + 1) * phaseWidth * (tokens.length + 2) :=
        Nat.mul_le_mul_right (tokens.length + 2)
          (Nat.mul_le_mul_right phaseWidth componentStep)
  have capacityBound :
      (componentMax + 1) * phaseWidth * (tokens.length + 2) ≤
        D * (tokens.length + 2) * (tokens.length + 2) := by
    have twoLe : D * 2 ≤ D * (tokens.length + 2) :=
      Nat.mul_le_mul_left D (by omega)
    exact Nat.mul_le_mul_right (tokens.length + 2)
      (Nat.le_trans capacity twoLe)
  unfold frontierDottedLexicographicPotential
  rw [frontierDottedGrammarFrameCount, allDottedRhs_length]
  calc
    component dotted * (tokens.length + 2) * phaseWidth +
          (origin.val * phaseWidth + phase dotted) <
        component dotted * (tokens.length + 2) * phaseWidth +
          (tokens.length + 2) * phaseWidth :=
      Nat.add_lt_add_left localLt _
    _ = (component dotted + 1) * (tokens.length + 2) * phaseWidth := by
      simp only [Nat.add_mul, Nat.one_mul]
    _ ≤ (componentMax + 1) * phaseWidth * (tokens.length + 2) := firstBound
    _ ≤ D * (tokens.length + 2) * (tokens.length + 2) := capacityBound
    _ < D * (tokens.length + 2) * (tokens.length + 2) + 1 := Nat.lt_succ_self _

/-- Static transition orientations construct all three exact contextual rank
tables for the component/origin/phase potential. -/
theorem frontierDottedLexicographicRankTables_eq_true
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens) {memo : GuardMemo tokens}
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo) (cursor : Boundary tokens)
    (greatest : GreatestReachableCursor
      file tokens memo correct final cursor)
    (phaseWidth : Nat) (component phase : DottedRhs → Nat)
    (phaseBound : ∀ dotted, phase dotted < phaseWidth)
    (predictionComponent : ∀ (waiting : ContextualItemKey tokens)
      (production : ProductionId),
      NextSymbol waiting.raw (.nonterminal production.lhs) →
      production.rhs ≠ [] →
      component (frontierZeroSpanPredictedDotted production) <
        component (frontierDottedRhsOfItem waiting.raw))
    (epsilonComponent : ∀ (waiting : ContextualItemKey tokens)
      (production : ProductionId) (after : ContextualItemKey tokens),
      NextSymbol waiting.raw (.nonterminal production.lhs) →
      production.rhs = [] →
      AdvanceItem waiting.raw waiting.raw.current after.raw →
      component (frontierDottedRhsOfItem after.raw) <
        component (frontierDottedRhsOfItem waiting.raw))
    (completionOrientation : ∀ (parent finished after :
      ContextualItemKey tokens),
      ContextualActivationParent
        file tokens memo correct final parent finished →
      CompleteItem finished.raw →
      AdvanceItem parent.raw finished.raw.current after.raw →
      component (frontierDottedRhsOfItem after.raw) <
          component (frontierDottedRhsOfItem finished.raw) ∨
        component (frontierDottedRhsOfItem after.raw) =
            component (frontierDottedRhsOfItem finished.raw) ∧
          (after.raw.origin.val < finished.raw.origin.val ∨
            after.raw.origin = finished.raw.origin ∧
              phase (frontierDottedRhsOfItem after.raw) <
                phase (frontierDottedRhsOfItem finished.raw))) :
    frontierDottedCompletionRankTable owned correct final cursor
          (frontierDottedLexicographicPotential
            phaseWidth component phase) = true ∧
      frontierDottedEpsilonRankTable owned correct final cursor
          (frontierDottedLexicographicPotential
            phaseWidth component phase) = true ∧
        frontierDottedPredictionRankTable owned correct final cursor
          (frontierDottedLexicographicPotential
            phaseWidth component phase) = true := by
  let potential := frontierDottedLexicographicPotential
    (tokens := tokens) phaseWidth component phase
  have prediction : frontierDottedPredictionRankTable
      owned correct final cursor potential = true := by
    apply frontierDottedPredictionRankTable_eq_true_of_decreases
    intro waiting production _reached _current next _enabled nonempty
    apply frontierDottedGrammarRank_lt_predicted_of_potential_lt
    exact frontierDottedLexicographicPotential_lt_of_component
      waiting.raw.origin waiting.raw.current waiting.raw.current
      waiting.raw.current (predictionComponent waiting production next nonempty)
      (phaseBound _)
  have epsilon : frontierDottedEpsilonRankTable
      owned correct final cursor potential = true := by
    apply frontierDottedEpsilonRankTable_eq_true_of_decreases
    intro waiting production after _waitingReached _waitingCurrent next
      _enabled epsilonProduction _afterReached _afterCurrent advance
    apply frontierDottedGrammarRank_lt_of_advancePotential potential advance
    exact frontierDottedLexicographicPotential_lt_of_component
      waiting.raw.origin waiting.raw.current after.raw.origin
      after.raw.current
      (epsilonComponent waiting production after next epsilonProduction
        advance)
      (phaseBound _)
  have completion : frontierDottedCompletionRankTable
      owned correct final cursor potential = true := by
    apply frontierDottedCompletionRankTable_eq_true_of_continuations
      owned correct final cursor greatest potential
    intro parent finished after activated complete advance
    apply frontierDottedGrammarRank_continuation_lt_of_potential_lt
      potential advance
    rcases completionOrientation parent finished after activated complete
        advance with componentLt | ⟨componentEq, originLt | phaseLt⟩
    · exact frontierDottedLexicographicPotential_lt_of_component
        finished.raw.origin finished.raw.current after.raw.origin
        after.raw.current componentLt (phaseBound _)
    · exact frontierDottedLexicographicPotential_lt_of_origin
        finished.raw.origin finished.raw.current after.raw.origin
        after.raw.current componentEq originLt (phaseBound _)
    · exact frontierDottedLexicographicPotential_lt_of_phase
        finished.raw.origin finished.raw.current after.raw.origin
        after.raw.current componentEq phaseLt.1 phaseLt.2
  exact ⟨completion, epsilon, prediction⟩

/-- A closed static component/phase certificate directly witnesses success of
the exhaustive bounded dotted-rank search. -/
theorem boundedFrontierDottedGrammarRankSearchSucceeds_of_lexicographic
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens) {memo : GuardMemo tokens}
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo) (cursor : Boundary tokens)
    (greatest : GreatestReachableCursor
      file tokens memo correct final cursor)
    (phaseWidth componentMax : Nat) (component phase : DottedRhs → Nat)
    (componentBound : ∀ dotted, component dotted ≤ componentMax)
    (phaseBound : ∀ dotted, phase dotted < phaseWidth)
    (capacity : (componentMax + 1) * phaseWidth ≤ D * 2)
    (predictionComponent : ∀ (waiting : ContextualItemKey tokens)
      (production : ProductionId),
      NextSymbol waiting.raw (.nonterminal production.lhs) →
      production.rhs ≠ [] →
      component (frontierZeroSpanPredictedDotted production) <
        component (frontierDottedRhsOfItem waiting.raw))
    (epsilonComponent : ∀ (waiting : ContextualItemKey tokens)
      (production : ProductionId) (after : ContextualItemKey tokens),
      NextSymbol waiting.raw (.nonterminal production.lhs) →
      production.rhs = [] →
      AdvanceItem waiting.raw waiting.raw.current after.raw →
      component (frontierDottedRhsOfItem after.raw) <
        component (frontierDottedRhsOfItem waiting.raw))
    (completionOrientation : ∀ (parent finished after :
      ContextualItemKey tokens),
      ContextualActivationParent
        file tokens memo correct final parent finished →
      CompleteItem finished.raw →
      AdvanceItem parent.raw finished.raw.current after.raw →
      component (frontierDottedRhsOfItem after.raw) <
          component (frontierDottedRhsOfItem finished.raw) ∨
        component (frontierDottedRhsOfItem after.raw) =
            component (frontierDottedRhsOfItem finished.raw) ∧
          (after.raw.origin.val < finished.raw.origin.val ∨
            after.raw.origin = finished.raw.origin ∧
              phase (frontierDottedRhsOfItem after.raw) <
                phase (frontierDottedRhsOfItem finished.raw))) :
    BoundedFrontierDottedGrammarRankSearchSucceeds
      owned correct final cursor := by
  let potential := frontierDottedLexicographicPotential
    (tokens := tokens) phaseWidth component phase
  have tables := frontierDottedLexicographicRankTables_eq_true
    owned correct final cursor greatest phaseWidth component phase phaseBound
    predictionComponent epsilonComponent completionOrientation
  exact boundedFrontierDottedGrammarRankSearchSucceeds_of_potential
    owned correct final cursor potential
    (frontierDottedLexicographicPotential_bounded
      componentBound phaseBound capacity)
    tables.1 tables.2.1 tables.2.2

end Solcore.Surface.Multi
