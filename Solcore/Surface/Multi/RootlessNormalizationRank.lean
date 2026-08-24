import Solcore.Surface.Multi.ParserJudgment

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar
open Solcore.Workspace

/-- The dot-zero child introduced by one nonterminal prediction. -/
def FrontierPredictedItem {tokens : List Token}
    (waiting : ContextualItemKey tokens) (production : ProductionId) :
    ContextualItemKey tokens := {
  raw := {
    production := production
    dot := ⟨0, Nat.zero_lt_succ _⟩
    origin := waiting.raw.current
    current := waiting.raw.current
  }
  context := descendContext waiting production
}

/-- The exact decreasing facts still needed after the exhaustive frontier
split.  Completion either exposes the canonical whole-file module root or
continues at a lower rank; epsilon completion and nonempty prediction also
decrease that same rank. -/
structure FrontierNormalizationRanking
    (file : WorkspaceFile) (tokens : List Token)
    (memo : GuardMemo tokens)
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo)
    (cursor : Boundary tokens)
    (rank : ContextualItemKey tokens → Nat) : Prop where
  complete : ∀ waiting,
    FrontierReach file tokens memo correct final cursor waiting →
    CompleteItem waiting.raw →
    waiting = CanonicalCompleteRootItem tokens .module
        (Boundary.start tokens) (Boundary.afterLogicalEOF tokens) .plain ∨
      ∃ after : ContextualItemKey tokens,
        FrontierReach file tokens memo correct final cursor after ∧
        rank after < rank waiting
  epsilon : ∀ waiting production after,
    FrontierReach file tokens memo correct final cursor waiting →
    NextSymbol waiting.raw (.nonterminal production.lhs) →
    EnabledProductionInstance file tokens memo correct final {
      production := production
      origin := waiting.raw.current
      context := descendContext waiting production
    } →
    production.rhs = [] →
    FrontierReach file tokens memo correct final cursor after →
    AdvanceItem waiting.raw waiting.raw.current after.raw →
    rank after < rank waiting
  prediction : ∀ waiting production,
    FrontierReach file tokens memo correct final cursor waiting →
    NextSymbol waiting.raw (.nonterminal production.lhs) →
    EnabledProductionInstance file tokens memo correct final {
      production := production
      origin := waiting.raw.current
      context := descendContext waiting production
    } →
    production.rhs ≠ [] →
    FrontierReach file tokens memo correct final cursor
      (FrontierPredictedItem waiting production) →
    rank (FrontierPredictedItem waiting production) < rank waiting

/-- One existential packages the remaining grammar-specific normalization
argument after enabled-production coverage has been supplied. -/
def RankedFrontierNormalization
    (file : WorkspaceFile) (tokens : List Token)
    (memo : GuardMemo tokens)
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo)
    (cursor : Boundary tokens) : Prop :=
  ∃ rank : ContextualItemKey tokens → Nat,
    FrontierNormalizationRanking
      file tokens memo correct final cursor rank

/-- Ranked normalization of the finite frontier either reaches a terminal
wait or exposes the canonical completed module root. -/
theorem terminalFrontierWait_or_completeModuleRoot_of_rankedNormalization
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {cursor : Boundary tokens}
    (greatest : GreatestReachableCursor
      file tokens memo correct final cursor)
    (coverage : ∀ waiting,
      FrontierReach file tokens memo correct final cursor waiting →
      EnabledNonterminalCoverageAt
        file tokens memo correct final waiting)
    (ranked : RankedFrontierNormalization
      file tokens memo correct final cursor) :
    TerminalFrontierWait file tokens memo correct final cursor ∨
      ContextualReach file tokens memo correct final
        (CanonicalCompleteRootItem tokens .module
          (Boundary.start tokens) (Boundary.afterLogicalEOF tokens) .plain) := by
  rcases ranked with ⟨rank, ranking⟩
  have normalize : ∀ fuel item,
      rank item = fuel →
      FrontierReach file tokens memo correct final cursor item →
      TerminalFrontierWait file tokens memo correct final cursor ∨
        ContextualReach file tokens memo correct final
          (CanonicalCompleteRootItem tokens .module
            (Boundary.start tokens) (Boundary.afterLogicalEOF tokens)
            .plain) := by
    intro fuel
    induction fuel using Nat.strongRecOn with
    | ind fuel induction =>
        intro item rankEq frontier
        have step := frontierNormalizationStep_of_coverage frontier
          (coverage item frontier)
        rcases step with complete |
            ⟨terminal, next, enabled⟩ |
            ⟨production, after, next, enabled, epsilon,
              afterFrontier, advance⟩ |
            ⟨production, next, enabled, nonempty, predictedFrontier⟩
        · rcases ranking.complete item frontier complete with
            rootEq | ⟨after, afterFrontier, decreases⟩
          · exact Or.inr (rootEq ▸ frontier.2.1)
          · exact induction (rank after) (by omega)
              after rfl afterFrontier
        · exact Or.inl ⟨item, terminal, frontier, next, enabled⟩
        · have decreases := ranking.epsilon item production after
            frontier next enabled epsilon afterFrontier advance
          exact induction (rank after) (by omega)
            after rfl afterFrontier
        · change FrontierReach file tokens memo correct final cursor
            (FrontierPredictedItem item production) at predictedFrontier
          have decreases := ranking.prediction item production
            frontier next enabled nonempty predictedFrontier
          exact induction (rank (FrontierPredictedItem item production))
            (by omega) (FrontierPredictedItem item production) rfl
            predictedFrontier
  rcases greatest.1 with ⟨item, reached, current⟩
  exact normalize (rank item) item rfl ⟨greatest, reached, current⟩

/-- If the canonical completed module root is absent, ranked normalization
must terminate at an enabled terminal wait on the greatest cursor. -/
theorem terminalFrontierWait_of_rootless_rankedNormalization
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {cursor : Boundary tokens}
    (greatest : GreatestReachableCursor
      file tokens memo correct final cursor)
    (coverage : ∀ waiting,
      FrontierReach file tokens memo correct final cursor waiting →
      EnabledNonterminalCoverageAt
        file tokens memo correct final waiting)
    (ranked : RankedFrontierNormalization
      file tokens memo correct final cursor)
    (rootAbsent : ¬ ContextualReach file tokens memo correct final
      (CanonicalCompleteRootItem tokens .module
        (Boundary.start tokens) (Boundary.afterLogicalEOF tokens) .plain)) :
    TerminalFrontierWait file tokens memo correct final cursor := by
  rcases terminalFrontierWait_or_completeModuleRoot_of_rankedNormalization
      greatest coverage ranked with waiting | rootReached
  · exact waiting
  · exact (rootAbsent rootReached).elim


end Solcore.Surface.Multi
