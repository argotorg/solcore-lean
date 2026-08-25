import Solcore.Surface.Multi.RootlessNormalizationDottedLexicographic
import Solcore.Surface.Multi.RootlessNormalizationDottedStaticPotential

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar
open Solcore.Workspace

private theorem frontierDottedRhsOfItem_eq_staticTotalityAdvance
    {tokens : List Token} {before after : DottedItem tokens}
    {next : Boundary tokens}
    (incomplete : before.dot.val < before.production.rhs.length)
    (advance : AdvanceItem before next after) :
    frontierDottedRhsOfItem after =
      dottedStaticAdvance
        (frontierDottedRhsOfItem before) incomplete := by
  cases before with
  | mk beforeProduction beforeDot beforeOrigin beforeCurrent =>
      cases after with
      | mk afterProduction afterDot afterOrigin afterCurrent =>
          simp only [AdvanceItem] at advance
          rcases advance with ⟨production, dot, _origin, _current⟩
          subst afterProduction
          simp only [frontierDottedRhsOfItem,
            dottedStaticAdvance]
          congr 1
          exact Fin.ext dot

private theorem frontierDottedRhsOfItem_eq_staticTotalityComplete
    {tokens : List Token} {item : DottedItem tokens}
    (complete : CompleteItem item) :
    frontierDottedRhsOfItem item =
      dottedStaticComplete item.production := by
  cases item with
  | mk production dot origin current =>
      simp only [CompleteItem] at complete
      simp only [frontierDottedRhsOfItem,
        dottedStaticComplete]
      congr 1
      exact Fin.ext complete

private theorem dottedStaticPrefixConsumes_sound_for_totality
    (dotted : DottedRhs)
    (consumes : dottedStaticPrefixConsumes dotted = true) :
    (dotted.production.rhs.take dotted.dot.val).all
        dottedStaticNullableSymbol ≠ true := by
  have notNullable :=
    (dottedStaticPrefixConsumes_eq_true_iff dotted).mp consumes
  simpa [dottedStaticPrefixNullable] using notNullable

private theorem dottedStaticCompletionOrientation_of_certificate
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    (nullableClosed : ∀ production : ProductionId,
      production.rhs.all dottedStaticNullableSymbol = true →
        dottedStaticNullableSymbol (.nonterminal production.lhs) = true)
    (completionCertificate : ∀ (waiting : DottedRhs)
      (child : ProductionId)
      (incomplete : waiting.dot.val < waiting.production.rhs.length),
      waiting.production.rhs[waiting.dot.val]? =
          some (.nonterminal child.lhs) →
        DottedStaticCompletionDecrease
          waiting child incomplete)
    (parent finished after : ContextualItemKey tokens)
    (activated : ContextualActivationParent
      file tokens memo correct final parent finished)
    (complete : CompleteItem finished.raw)
    (advance : AdvanceItem parent.raw finished.raw.current after.raw) :
    dottedStaticComponentRank (frontierDottedRhsOfItem after.raw) <
        dottedStaticComponentRank (frontierDottedRhsOfItem finished.raw) ∨
      dottedStaticComponentRank (frontierDottedRhsOfItem after.raw) =
          dottedStaticComponentRank (frontierDottedRhsOfItem finished.raw) ∧
        (after.raw.origin.val < finished.raw.origin.val ∨
          after.raw.origin = finished.raw.origin ∧
            dottedStaticPhase (frontierDottedRhsOfItem after.raw) <
              dottedStaticPhase
                (frontierDottedRhsOfItem finished.raw)) := by
  have afterEq := frontierDottedRhsOfItem_eq_staticTotalityAdvance
    activated.2.1.1 advance
  have finishedEq :=
    frontierDottedRhsOfItem_eq_staticTotalityComplete complete
  have static := completionCertificate
    (frontierDottedRhsOfItem parent.raw) finished.raw.production
    activated.2.1.1 activated.2.1.2
  simp only [DottedStaticCompletionDecrease] at static
  rw [← afterEq, ← finishedEq] at static
  rcases static with componentLt | ⟨componentEq, phaseLt | consumes⟩
  · exact Or.inl componentLt
  · refine Or.inr ⟨componentEq, ?_⟩
    by_cases sameOrigin : after.raw.origin = finished.raw.origin
    · exact Or.inr ⟨sameOrigin, phaseLt⟩
    · apply Or.inl
      have originLe := contextualActivationParent_origin_le activated
      have differentValues :
          parent.raw.origin.val ≠ finished.raw.origin.val := by
        intro equalValues
        apply sameOrigin
        exact advance.2.2.1.trans (Fin.ext equalValues)
      rw [advance.2.2.1]
      exact Nat.lt_of_le_of_ne originLe differentValues
  · refine Or.inr ⟨componentEq, Or.inl ?_⟩
    exact contextualCompletionContinuation_origin_lt_of_prefixConsumes
      dottedStaticNullableSymbol nullableClosed
      dottedStaticPrefixConsumes
      dottedStaticPrefixConsumes_sound_for_totality
      activated advance consumes

/-- Fixed-grammar bounds and the three sparse edge certificates close the
unconditional bounded dotted-rank search. -/
theorem boundedFrontierDottedGrammarRankSearchSucceeds_of_staticCertificates
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens) {memo : GuardMemo tokens}
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo) (cursor : Boundary tokens)
    (greatest : GreatestReachableCursor
      file tokens memo correct final cursor)
    (componentBound : ∀ dotted,
      dottedStaticComponentRank dotted ≤ dottedStaticComponentMax)
    (phaseBound : ∀ dotted,
      dottedStaticPhase dotted < dottedStaticPhaseWidth)
    (capacity :
      (dottedStaticComponentMax + 1) * dottedStaticPhaseWidth ≤ D * 2)
    (nullableClosed : ∀ production : ProductionId,
      production.rhs.all dottedStaticNullableSymbol = true →
        dottedStaticNullableSymbol (.nonterminal production.lhs) = true)
    (predictionCertificate : ∀ (waiting : DottedRhs)
      (child : ProductionId),
      waiting.production.rhs[waiting.dot.val]? =
          some (.nonterminal child.lhs) →
      child.rhs ≠ [] →
      dottedStaticComponentRank (frontierZeroSpanPredictedDotted child) <
        dottedStaticComponentRank waiting)
    (epsilonCertificate : ∀ (waiting : DottedRhs)
      (child : ProductionId)
      (incomplete : waiting.dot.val < waiting.production.rhs.length),
      waiting.production.rhs[waiting.dot.val]? =
          some (.nonterminal child.lhs) →
      child.rhs = [] →
      dottedStaticComponentRank
          (dottedStaticAdvance waiting incomplete) <
        dottedStaticComponentRank waiting)
    (completionCertificate : ∀ (waiting : DottedRhs)
      (child : ProductionId)
      (incomplete : waiting.dot.val < waiting.production.rhs.length),
      waiting.production.rhs[waiting.dot.val]? =
          some (.nonterminal child.lhs) →
        DottedStaticCompletionDecrease
          waiting child incomplete) :
    BoundedFrontierDottedGrammarRankSearchSucceeds
      owned correct final cursor := by
  apply boundedFrontierDottedGrammarRankSearchSucceeds_of_lexicographic
    owned correct final cursor greatest dottedStaticPhaseWidth
    dottedStaticComponentMax dottedStaticComponentRank dottedStaticPhase
    componentBound phaseBound capacity
  · intro waiting production next nonempty
    exact predictionCertificate _ _ next.2 nonempty
  · intro waiting production after next epsilonProduction advance
    have decreases := epsilonCertificate
      (frontierDottedRhsOfItem waiting.raw) production next.1 next.2
      epsilonProduction
    have afterEq := frontierDottedRhsOfItem_eq_staticTotalityAdvance
      next.1 advance
    rwa [← afterEq] at decreases
  · exact dottedStaticCompletionOrientation_of_certificate
      nullableClosed completionCertificate

/-- The fixed rank bounds and nullability closure leave only the three
static edge-orientation extractors to discharge. -/
theorem boundedFrontierDottedGrammarRankSearchSucceeds_of_staticEdges
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens) {memo : GuardMemo tokens}
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo) (cursor : Boundary tokens)
    (greatest : GreatestReachableCursor
      file tokens memo correct final cursor)
    (predictionCertificate : ∀ (waiting : DottedRhs)
      (child : ProductionId),
      waiting.production.rhs[waiting.dot.val]? =
          some (.nonterminal child.lhs) →
      child.rhs ≠ [] →
      dottedStaticComponentRank (dottedStaticStart child) <
        dottedStaticComponentRank waiting)
    (epsilonCertificate : ∀ (waiting : DottedRhs)
      (child : ProductionId)
      (incomplete : waiting.dot.val < waiting.production.rhs.length),
      waiting.production.rhs[waiting.dot.val]? =
          some (.nonterminal child.lhs) →
      child.rhs = [] →
      dottedStaticComponentRank (dottedStaticAdvance waiting incomplete) <
        dottedStaticComponentRank waiting)
    (completionCertificate : ∀ (waiting : DottedRhs)
      (child : ProductionId)
      (incomplete : waiting.dot.val < waiting.production.rhs.length),
      waiting.production.rhs[waiting.dot.val]? =
          some (.nonterminal child.lhs) →
        DottedStaticCompletionDecrease waiting child incomplete) :
    BoundedFrontierDottedGrammarRankSearchSucceeds
      owned correct final cursor := by
  apply boundedFrontierDottedGrammarRankSearchSucceeds_of_staticCertificates
    owned correct final cursor greatest dottedStaticComponentRank_le_max
    dottedStaticPhase_lt_width dottedStaticCapacity
    dottedStaticNullableSymbol_closed
  · simpa only [dottedStaticStart, frontierZeroSpanPredictedDotted]
      using predictionCertificate
  · exact epsilonCertificate
  · exact completionCertificate

end Solcore.Surface.Multi
