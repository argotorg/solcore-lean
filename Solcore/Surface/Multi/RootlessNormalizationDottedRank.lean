import Solcore.Surface.Multi.RootlessNormalizationGrammarRank

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar
open Solcore.Workspace

/-- Boundary-free dotted coordinate of one raw contextual item. -/
def frontierDottedRhsOfItem {tokens : List Token}
    (item : DottedItem tokens) : DottedRhs := {
  production := item.production
  dot := item.dot
}

/-- A grammar potential with an independent coordinate at every dot. -/
abbrev FrontierDottedGrammarPotential (tokens : List Token) :=
  DottedRhs → Boundary tokens → Boundary tokens → Nat

/-- The raw dotted rank has no fixed remainder offset: advance, prediction,
and completion edges may interleave nullable call and return states freely. -/
def frontierRawDottedGrammarRank {tokens : List Token}
    (potential : FrontierDottedGrammarPotential tokens)
    (item : DottedItem tokens) : Nat :=
  potential (frontierDottedRhsOfItem item) item.origin item.current

/-- Context is intentionally projected away while the dot remains visible. -/
def frontierDottedGrammarRank {tokens : List Token}
    (potential : FrontierDottedGrammarPotential tokens)
    (item : ContextualItemKey tokens) : Nat :=
  frontierRawDottedGrammarRank potential item.raw

/-- A strict dotted-coordinate inequality is exactly a contextual rank
descent. -/
theorem frontierDottedGrammarRank_lt_of_potential_lt
    {tokens : List Token}
    (potential : FrontierDottedGrammarPotential tokens)
    {before after : ContextualItemKey tokens}
    (decreases :
      potential (frontierDottedRhsOfItem after.raw)
          after.raw.origin after.raw.current <
        potential (frontierDottedRhsOfItem before.raw)
          before.raw.origin before.raw.current) :
    frontierDottedGrammarRank potential after <
      frontierDottedGrammarRank potential before :=
  decreases

/-- The dot-zero prediction coordinate may be compared directly with its
waiting dotted coordinate. -/
theorem frontierDottedGrammarRank_lt_predicted_of_potential_lt
    {tokens : List Token}
    (potential : FrontierDottedGrammarPotential tokens)
    (waiting : ContextualItemKey tokens) (production : ProductionId)
    (decreases :
      potential (frontierZeroSpanPredictedDotted production)
          waiting.raw.current waiting.raw.current <
        potential (frontierDottedRhsOfItem waiting.raw)
          waiting.raw.origin waiting.raw.current) :
    frontierDottedGrammarRank potential
        (FrontierPredictedItem waiting production) <
      frontierDottedGrammarRank potential waiting := by
  exact decreases

/-- An actual dot advance descends whenever its two independent dotted
coordinates are oriented that way. -/
theorem frontierDottedGrammarRank_lt_of_advancePotential
    {tokens : List Token}
    (potential : FrontierDottedGrammarPotential tokens)
    {before after : ContextualItemKey tokens}
    {next : Boundary tokens}
    (_advance : AdvanceItem before.raw next after.raw)
    (decreases :
      potential (frontierDottedRhsOfItem after.raw)
          after.raw.origin after.raw.current <
        potential (frontierDottedRhsOfItem before.raw)
          before.raw.origin before.raw.current) :
    frontierDottedGrammarRank potential after <
      frontierDottedGrammarRank potential before :=
  decreases

/-- A materialized completion continuation likewise reduces to its exact
dotted-coordinate comparison. -/
theorem frontierDottedGrammarRank_continuation_lt_of_potential_lt
    {tokens : List Token}
    (potential : FrontierDottedGrammarPotential tokens)
    {parent finished after : ContextualItemKey tokens}
    (_advance : AdvanceItem parent.raw finished.raw.current after.raw)
    (decreases :
      potential (frontierDottedRhsOfItem after.raw)
          after.raw.origin after.raw.current <
        potential (frontierDottedRhsOfItem finished.raw)
          finished.raw.origin finished.raw.current) :
    frontierDottedGrammarRank potential after <
      frontierDottedGrammarRank potential finished :=
  decreases

private def dottedNextSymbolDecision
    {tokens : List Token} (item : DottedItem tokens)
    (symbol : GrammarSymbol) : Decidable (NextSymbol item symbol) := by
  unfold NextSymbol
  infer_instance

private def dottedCompleteItemDecision
    {tokens : List Token} (item : DottedItem tokens) :
    Decidable (CompleteItem item) := by
  unfold CompleteItem
  infer_instance

/-- One exact nonempty-prediction cell for a dotted potential. -/
def frontierDottedPredictionRankCell
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {memo : GuardMemo tokens}
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo) (cursor : Boundary tokens)
    (potential : FrontierDottedGrammarPotential tokens)
    (waiting : ContextualItemKey tokens) (production : ProductionId) : Bool :=
  let child : ProductionInstanceKey tokens := {
    production := production
    origin := waiting.raw.current
    context := descendContext waiting production
  }
  letI : Decidable
      (ContextualReach file tokens memo correct final waiting) :=
    contextualReachDecision owned correct final waiting
  letI : Decidable
      (NextSymbol waiting.raw (.nonterminal production.lhs)) :=
    dottedNextSymbolDecision waiting.raw (.nonterminal production.lhs)
  letI : Decidable
      (EnabledProductionInstance file tokens memo correct final child) :=
    enabledProductionInstanceDecision correct final child
  if ContextualReach file tokens memo correct final waiting then
    if waiting.raw.current = cursor then
      if NextSymbol waiting.raw (.nonterminal production.lhs) then
        if EnabledProductionInstance file tokens memo correct final child then
          if production.rhs ≠ [] then
            decide (frontierDottedGrammarRank potential
                (FrontierPredictedItem waiting production) <
              frontierDottedGrammarRank potential waiting)
          else true
        else true
      else true
    else true
  else true

/-- Exact finite prediction table for a dotted potential. -/
def frontierDottedPredictionRankTable
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {memo : GuardMemo tokens}
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo) (cursor : Boundary tokens)
    (potential : FrontierDottedGrammarPotential tokens) : Bool :=
  (allContextualItems tokens).all fun waiting =>
    allProductionIds.all fun production =>
      frontierDottedPredictionRankCell owned correct final cursor
        potential waiting production

/-- A checked dotted prediction table supplies every selected edge. -/
theorem frontierDottedPredictionRank_lt_of_table
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {memo : GuardMemo tokens}
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo) (cursor : Boundary tokens)
    (potential : FrontierDottedGrammarPotential tokens)
    (checked : frontierDottedPredictionRankTable
      owned correct final cursor potential = true)
    (waiting : ContextualItemKey tokens) (production : ProductionId)
    (reached : ContextualReach file tokens memo correct final waiting)
    (current : waiting.raw.current = cursor)
    (next : NextSymbol waiting.raw (.nonterminal production.lhs))
    (enabled : EnabledProductionInstance file tokens memo correct final {
      production := production
      origin := waiting.raw.current
      context := descendContext waiting production
    }) (nonempty : production.rhs ≠ []) :
    frontierDottedGrammarRank potential
        (FrontierPredictedItem waiting production) <
      frontierDottedGrammarRank potential waiting := by
  have row := (List.all_eq_true.mp checked) waiting
    (allContextualItems_complete waiting)
  have cell := (List.all_eq_true.mp row) production
    (allProductionIds_complete production)
  simp only [frontierDottedPredictionRankCell] at cell
  rw [if_pos reached, if_pos current, if_pos next, if_pos enabled,
    if_pos nonempty] at cell
  exact decide_eq_true_iff.mp cell

/-- One possible lower reached item on the same dotted-rank frontier. -/
def frontierDottedLowerRankCell
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {memo : GuardMemo tokens}
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo) (cursor : Boundary tokens)
    (potential : FrontierDottedGrammarPotential tokens)
    (waiting after : ContextualItemKey tokens) : Bool :=
  letI : Decidable
      (ContextualReach file tokens memo correct final after) :=
    contextualReachDecision owned correct final after
  if ContextualReach file tokens memo correct final after then
    if after.raw.current = cursor then
      decide (frontierDottedGrammarRank potential after <
        frontierDottedGrammarRank potential waiting)
    else false
  else false

/-- The dotted lower-rank cell exposes its three exact facts. -/
theorem frontierDottedLowerRankCell_eq_true_iff
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens) {memo : GuardMemo tokens}
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo) (cursor : Boundary tokens)
    (potential : FrontierDottedGrammarPotential tokens)
    (waiting after : ContextualItemKey tokens) :
    frontierDottedLowerRankCell owned correct final cursor potential
        waiting after = true ↔
      ContextualReach file tokens memo correct final after ∧
        after.raw.current = cursor ∧
        frontierDottedGrammarRank potential after <
          frontierDottedGrammarRank potential waiting := by
  simp [frontierDottedLowerRankCell]

/-- One exact completed-item cell for a dotted potential. -/
def frontierDottedCompletionRankCell
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {memo : GuardMemo tokens}
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo) (cursor : Boundary tokens)
    (potential : FrontierDottedGrammarPotential tokens)
    (waiting : ContextualItemKey tokens) : Bool :=
  letI : Decidable
      (ContextualReach file tokens memo correct final waiting) :=
    contextualReachDecision owned correct final waiting
  letI : Decidable (CompleteItem waiting.raw) :=
    dottedCompleteItemDecision waiting.raw
  if ContextualReach file tokens memo correct final waiting then
    if waiting.raw.current = cursor then
      if CompleteItem waiting.raw then
        decide (waiting = CanonicalCompleteRootItem tokens .module
            (Boundary.start tokens) (Boundary.afterLogicalEOF tokens) .plain) ||
          (allContextualItems tokens).any fun after =>
            frontierDottedLowerRankCell owned correct final cursor potential
              waiting after
      else true
    else true
  else true

/-- Exact finite completion table for a dotted potential. -/
def frontierDottedCompletionRankTable
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {memo : GuardMemo tokens}
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo) (cursor : Boundary tokens)
    (potential : FrontierDottedGrammarPotential tokens) : Bool :=
  (allContextualItems tokens).all fun waiting =>
    frontierDottedCompletionRankCell owned correct final cursor
      potential waiting

/-- A checked dotted completion table supplies the root or a lower
continuation. -/
theorem frontierDottedCompletionRank_of_table
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {memo : GuardMemo tokens}
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo) (cursor : Boundary tokens)
    (potential : FrontierDottedGrammarPotential tokens)
    (checked : frontierDottedCompletionRankTable
      owned correct final cursor potential = true)
    (waiting : ContextualItemKey tokens)
    (frontier : FrontierReach file tokens memo correct final cursor waiting)
    (complete : CompleteItem waiting.raw) :
    waiting = CanonicalCompleteRootItem tokens .module
        (Boundary.start tokens) (Boundary.afterLogicalEOF tokens) .plain ∨
      ∃ after : ContextualItemKey tokens,
        FrontierReach file tokens memo correct final cursor after ∧
        frontierDottedGrammarRank potential after <
          frontierDottedGrammarRank potential waiting := by
  have cell := (List.all_eq_true.mp checked) waiting
    (allContextualItems_complete waiting)
  simp only [frontierDottedCompletionRankCell] at cell
  rw [if_pos frontier.2.1, if_pos frontier.2.2, if_pos complete,
    Bool.or_eq_true] at cell
  rcases cell with root | lower
  · exact Or.inl (decide_eq_true_iff.mp root)
  · rcases List.any_eq_true.mp lower with ⟨after, _member, lower⟩
    have facts := (frontierDottedLowerRankCell_eq_true_iff
      owned correct final cursor potential waiting after).mp lower
    exact Or.inr ⟨after, ⟨frontier.1, facts.1, facts.2.1⟩, facts.2.2⟩

private def dottedAdvanceItemDecision
    {tokens : List Token} (before : DottedItem tokens)
    (next : Boundary tokens) (after : DottedItem tokens) :
    Decidable (AdvanceItem before next after) := by
  unfold AdvanceItem
  infer_instance

/-- One exact direct-epsilon advance cell for a dotted potential. -/
def frontierDottedEpsilonRankCell
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {memo : GuardMemo tokens}
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo) (cursor : Boundary tokens)
    (potential : FrontierDottedGrammarPotential tokens)
    (waiting : ContextualItemKey tokens) (production : ProductionId)
    (after : ContextualItemKey tokens) : Bool :=
  let child : ProductionInstanceKey tokens := {
    production := production
    origin := waiting.raw.current
    context := descendContext waiting production
  }
  letI : Decidable
      (ContextualReach file tokens memo correct final waiting) :=
    contextualReachDecision owned correct final waiting
  letI : Decidable
      (ContextualReach file tokens memo correct final after) :=
    contextualReachDecision owned correct final after
  letI : Decidable
      (NextSymbol waiting.raw (.nonterminal production.lhs)) :=
    dottedNextSymbolDecision waiting.raw (.nonterminal production.lhs)
  letI : Decidable
      (EnabledProductionInstance file tokens memo correct final child) :=
    enabledProductionInstanceDecision correct final child
  letI : Decidable
      (AdvanceItem waiting.raw waiting.raw.current after.raw) :=
    dottedAdvanceItemDecision waiting.raw waiting.raw.current after.raw
  if ContextualReach file tokens memo correct final waiting then
    if waiting.raw.current = cursor then
      if NextSymbol waiting.raw (.nonterminal production.lhs) then
        if EnabledProductionInstance file tokens memo correct final child then
          if production.rhs = [] then
            if ContextualReach file tokens memo correct final after then
              if after.raw.current = cursor then
                if AdvanceItem waiting.raw waiting.raw.current after.raw then
                  decide (frontierDottedGrammarRank potential after <
                    frontierDottedGrammarRank potential waiting)
                else true
              else true
            else true
          else true
        else true
      else true
    else true
  else true

/-- Exact finite direct-epsilon advance table for a dotted potential. -/
def frontierDottedEpsilonRankTable
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {memo : GuardMemo tokens}
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo) (cursor : Boundary tokens)
    (potential : FrontierDottedGrammarPotential tokens) : Bool :=
  (allContextualItems tokens).all fun waiting =>
    allProductionIds.all fun production =>
      (allContextualItems tokens).all fun after =>
        frontierDottedEpsilonRankCell owned correct final cursor potential
          waiting production after

/-- A checked dotted epsilon table supplies every selected direct advance. -/
theorem frontierDottedEpsilonRank_lt_of_table
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {memo : GuardMemo tokens}
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo) (cursor : Boundary tokens)
    (potential : FrontierDottedGrammarPotential tokens)
    (checked : frontierDottedEpsilonRankTable
      owned correct final cursor potential = true)
    (waiting : ContextualItemKey tokens) (production : ProductionId)
    (after : ContextualItemKey tokens)
    (waitingReached : ContextualReach
      file tokens memo correct final waiting)
    (waitingCurrent : waiting.raw.current = cursor)
    (next : NextSymbol waiting.raw (.nonterminal production.lhs))
    (enabled : EnabledProductionInstance file tokens memo correct final {
      production := production
      origin := waiting.raw.current
      context := descendContext waiting production
    }) (epsilon : production.rhs = [])
    (afterReached : ContextualReach file tokens memo correct final after)
    (afterCurrent : after.raw.current = cursor)
    (advance : AdvanceItem waiting.raw waiting.raw.current after.raw) :
    frontierDottedGrammarRank potential after <
      frontierDottedGrammarRank potential waiting := by
  have waitingRow := (List.all_eq_true.mp checked) waiting
    (allContextualItems_complete waiting)
  have productionRow := (List.all_eq_true.mp waitingRow) production
    (allProductionIds_complete production)
  have cell := (List.all_eq_true.mp productionRow) after
    (allContextualItems_complete after)
  simp only [frontierDottedEpsilonRankCell] at cell
  rw [if_pos waitingReached, if_pos waitingCurrent, if_pos next,
    if_pos enabled, if_pos epsilon, if_pos afterReached,
    if_pos afterCurrent, if_pos advance] at cell
  exact decide_eq_true_iff.mp cell

/-- The three exact dotted tables construct every field of the abstract
frontier normalization ranking. -/
theorem frontierNormalizationRanking_of_dottedGrammarPotential
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo} {cursor : Boundary tokens}
    (potential : FrontierDottedGrammarPotential tokens)
    (completion : frontierDottedCompletionRankTable
      owned correct final cursor potential = true)
    (epsilon : frontierDottedEpsilonRankTable
      owned correct final cursor potential = true)
    (prediction : frontierDottedPredictionRankTable
      owned correct final cursor potential = true) :
    FrontierNormalizationRanking file tokens memo correct final cursor
      (frontierDottedGrammarRank potential) := by
  constructor
  · exact frontierDottedCompletionRank_of_table
      owned correct final cursor potential completion
  · intro waiting production after frontier next enabled epsilonProduction
      afterFrontier advance
    exact frontierDottedEpsilonRank_lt_of_table
      owned correct final cursor potential epsilon waiting production after
      frontier.2.1 frontier.2.2 next enabled epsilonProduction
      afterFrontier.2.1 afterFrontier.2.2 advance
  · intro waiting production frontier next enabled nonempty _predicted
    exact frontierDottedPredictionRank_lt_of_table
      owned correct final cursor potential prediction waiting production
      frontier.2.1 frontier.2.2 next enabled nonempty

/-- One dotted potential accepted by all three exact finite rank tables. -/
def DottedGrammarRankedFrontierNormalization
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (memo : GuardMemo tokens)
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo)
    (cursor : Boundary tokens) : Prop :=
  ∃ potential : FrontierDottedGrammarPotential tokens,
    frontierDottedCompletionRankTable
        owned correct final cursor potential = true ∧
      frontierDottedEpsilonRankTable
        owned correct final cursor potential = true ∧
      frontierDottedPredictionRankTable
        owned correct final cursor potential = true

/-- A three-table dotted certificate supplies abstract ranked
normalization. -/
theorem rankedFrontierNormalization_of_dottedGrammarRanked
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo} {cursor : Boundary tokens}
    (ranked : DottedGrammarRankedFrontierNormalization
      file tokens owned memo correct final cursor) :
    RankedFrontierNormalization file tokens memo correct final cursor := by
  rcases ranked with ⟨potential, completion, epsilon, prediction⟩
  exact ⟨frontierDottedGrammarRank potential,
    frontierNormalizationRanking_of_dottedGrammarPotential
      owned potential completion epsilon prediction⟩

end Solcore.Surface.Multi
