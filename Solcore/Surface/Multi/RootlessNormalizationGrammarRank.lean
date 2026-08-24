import Solcore.Surface.Multi.RootlessNormalizationRank
set_option autoImplicit false
namespace Solcore.Surface.Multi
open Grammar
open Solcore.Workspace
/-- The number of symbols still to the right of one dotted item. -/
def frontierRhsRemaining {tokens : List Token}
    (item : DottedItem tokens) : Nat :=
  item.production.rhs.length - item.dot.val
/-- A grammar-frame potential may depend on the production and input span,
but not on the dot or guard context.  The latter restriction makes one
epsilon completion preserve the coarse component definitionally. -/
abbrev FrontierGrammarPotential (tokens : List Token) :=
  ProductionId → Boundary tokens → Boundary tokens → Nat
/-- Lexicographic normalization rank: a finite grammar/span frame followed
by the number of symbols remaining in the current RHS. -/
def frontierRawGrammarRank {tokens : List Token}
    (potential : FrontierGrammarPotential tokens)
    (item : DottedItem tokens) : Nat :=
  (D + 1) * potential item.production item.origin item.current +
    frontierRhsRemaining item
/-- The contextual rank ignores guard context and uses the raw grammar
frame. -/
def frontierGrammarRank {tokens : List Token}
    (potential : FrontierGrammarPotential tokens)
    (item : ContextualItemKey tokens) : Nat :=
  frontierRawGrammarRank potential item.raw
/-- The same epsilon descent holds for every coarse grammar/span
potential, because `AdvanceItem` preserves that entire frame. -/
theorem frontierGrammarRank_lt_of_advance_withPotential
    {tokens : List Token}
    (potential : FrontierGrammarPotential tokens)
    {before after : ContextualItemKey tokens}
    {symbol : GrammarSymbol}
    (next : NextSymbol before.raw symbol)
    (advance : AdvanceItem before.raw before.raw.current after.raw) :
    frontierGrammarRank potential after <
      frontierGrammarRank potential before := by
  have inRange := next.1
  rcases advance with ⟨production, dot, origin, current⟩
  have lengthEq : after.raw.production.rhs.length =
      before.raw.production.rhs.length :=
    congrArg (fun selected => selected.rhs.length) production
  have potentialEq :
      potential after.raw.production after.raw.origin after.raw.current =
        potential before.raw.production before.raw.origin
          before.raw.current := by
    rw [production, origin, current]
  unfold frontierGrammarRank frontierRawGrammarRank frontierRhsRemaining
  rw [potentialEq]
  omega
private def nextSymbolDecision
    {tokens : List Token} (item : DottedItem tokens)
    (symbol : GrammarSymbol) : Decidable (NextSymbol item symbol) := by
  unfold NextSymbol
  infer_instance
/-- One executable prediction-rank cell.  Its antecedent is the exact
frontier-local prediction premise, apart from greatest-cursor evidence shared
by every row. -/
def frontierPredictionRankCell
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {memo : GuardMemo tokens}
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo) (cursor : Boundary tokens)
    (potential : FrontierGrammarPotential tokens)
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
    nextSymbolDecision waiting.raw (.nonterminal production.lhs)
  letI : Decidable
      (EnabledProductionInstance file tokens memo correct final child) :=
    enabledProductionInstanceDecision correct final child
  letI : Decidable (waiting.raw.current = cursor) := inferInstance
  letI : Decidable (production.rhs ≠ []) := inferInstance
  letI : Decidable
      (frontierGrammarRank potential (FrontierPredictedItem waiting production) <
        frontierGrammarRank potential waiting) := inferInstance
  if ContextualReach file tokens memo correct final waiting then
    if waiting.raw.current = cursor then
      if NextSymbol waiting.raw (.nonterminal production.lhs) then
        if EnabledProductionInstance file tokens memo correct final child then
          if production.rhs ≠ [] then
            decide (frontierGrammarRank potential
                (FrontierPredictedItem waiting production) <
              frontierGrammarRank potential waiting)
          else true
        else true
      else true
    else true
  else true
/-- All reached frontier predictions are checked over the public finite
contextual-item and production carriers. -/
def frontierPredictionRankTable
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {memo : GuardMemo tokens}
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo) (cursor : Boundary tokens)
    (potential : FrontierGrammarPotential tokens) : Bool :=
  (allContextualItems tokens).all fun waiting =>
    allProductionIds.all fun production =>
      frontierPredictionRankCell owned correct final cursor potential
        waiting production
theorem frontierPredictionRank_lt_of_table
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {memo : GuardMemo tokens}
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo) (cursor : Boundary tokens)
    (potential : FrontierGrammarPotential tokens)
    (checked : frontierPredictionRankTable
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
    frontierGrammarRank potential (FrontierPredictedItem waiting production) <
      frontierGrammarRank potential waiting := by
  have row := (List.all_eq_true.mp checked) waiting
    (allContextualItems_complete waiting)
  have cell := (List.all_eq_true.mp row) production
    (allProductionIds_complete production)
  simp only [frontierPredictionRankCell] at cell
  rw [if_pos reached, if_pos current, if_pos next, if_pos enabled,
    if_pos nonempty] at cell
  exact decide_eq_true_iff.mp cell
/-- A possible lower-rank reached item on the same frontier. -/
def frontierLowerRankCell
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {memo : GuardMemo tokens}
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo) (cursor : Boundary tokens)
    (potential : FrontierGrammarPotential tokens)
    (waiting after : ContextualItemKey tokens) : Bool :=
  letI : Decidable
      (ContextualReach file tokens memo correct final after) :=
    contextualReachDecision owned correct final after
  letI : Decidable (after.raw.current = cursor) := inferInstance
  letI : Decidable (frontierGrammarRank potential after <
      frontierGrammarRank potential waiting) := inferInstance
  if ContextualReach file tokens memo correct final after then
    if after.raw.current = cursor then
      decide (frontierGrammarRank potential after <
        frontierGrammarRank potential waiting)
    else false
  else false
theorem frontierLowerRankCell_eq_true_iff
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens) {memo : GuardMemo tokens}
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo) (cursor : Boundary tokens)
    (potential : FrontierGrammarPotential tokens)
    (waiting after : ContextualItemKey tokens) :
    frontierLowerRankCell owned correct final cursor potential waiting after =
        true ↔
      ContextualReach file tokens memo correct final after ∧
        after.raw.current = cursor ∧
        frontierGrammarRank potential after <
          frontierGrammarRank potential waiting := by
  simp [frontierLowerRankCell]
private def completeItemDecision {tokens : List Token}
    (item : DottedItem tokens) : Decidable (CompleteItem item) := by
  unfold CompleteItem
  infer_instance
/-- One completed-item cell searches the finite contextual carrier for a
lower continuation, unless the item is the canonical module root. -/
def frontierCompletionRankCell
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {memo : GuardMemo tokens}
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo) (cursor : Boundary tokens)
    (potential : FrontierGrammarPotential tokens)
    (waiting : ContextualItemKey tokens) : Bool :=
  letI : Decidable
      (ContextualReach file tokens memo correct final waiting) :=
    contextualReachDecision owned correct final waiting
  letI : Decidable (CompleteItem waiting.raw) :=
    completeItemDecision waiting.raw
  if ContextualReach file tokens memo correct final waiting then
    if waiting.raw.current = cursor then
      if CompleteItem waiting.raw then
        decide (waiting = CanonicalCompleteRootItem tokens .module
            (Boundary.start tokens) (Boundary.afterLogicalEOF tokens) .plain) ||
          (allContextualItems tokens).any fun after =>
            frontierLowerRankCell owned correct final cursor potential
              waiting after
      else true
    else true
  else true
/-- All completed frontier items pass their finite lower-continuation
search. -/
def frontierCompletionRankTable
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {memo : GuardMemo tokens}
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo) (cursor : Boundary tokens)
    (potential : FrontierGrammarPotential tokens) : Bool :=
  (allContextualItems tokens).all fun waiting =>
    frontierCompletionRankCell owned correct final cursor potential waiting
theorem frontierCompletionRank_of_table
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {memo : GuardMemo tokens}
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo) (cursor : Boundary tokens)
    (potential : FrontierGrammarPotential tokens)
    (checked : frontierCompletionRankTable
      owned correct final cursor potential = true)
    (waiting : ContextualItemKey tokens)
    (frontier : FrontierReach file tokens memo correct final cursor waiting)
    (complete : CompleteItem waiting.raw) :
    waiting = CanonicalCompleteRootItem tokens .module
        (Boundary.start tokens) (Boundary.afterLogicalEOF tokens) .plain ∨
      ∃ after : ContextualItemKey tokens,
        FrontierReach file tokens memo correct final cursor after ∧
        frontierGrammarRank potential after <
          frontierGrammarRank potential waiting := by
  have cell := (List.all_eq_true.mp checked) waiting
    (allContextualItems_complete waiting)
  simp only [frontierCompletionRankCell] at cell
  rw [if_pos frontier.2.1, if_pos frontier.2.2, if_pos complete,
    Bool.or_eq_true] at cell
  rcases cell with root | lower
  · exact Or.inl (decide_eq_true_iff.mp root)
  · rcases List.any_eq_true.mp lower with ⟨after, _member, lower⟩
    have facts := (frontierLowerRankCell_eq_true_iff
      owned correct final cursor potential waiting after).mp lower
    exact Or.inr ⟨after, ⟨frontier.1, facts.1, facts.2.1⟩, facts.2.2⟩
/-- The two finite tables and structural epsilon descent construct all three
fields of the abstract normalization ranking. -/
theorem frontierNormalizationRanking_of_grammarPotential
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo} {cursor : Boundary tokens}
    (potential : FrontierGrammarPotential tokens)
    (completion : frontierCompletionRankTable
      owned correct final cursor potential = true)
    (prediction : frontierPredictionRankTable
      owned correct final cursor potential = true) :
    FrontierNormalizationRanking file tokens memo correct final cursor
      (frontierGrammarRank potential) := by
  constructor
  · exact frontierCompletionRank_of_table owned correct final cursor
      potential completion
  · intro waiting production after _frontier next _enabled _epsilon
      _afterFrontier advance
    exact frontierGrammarRank_lt_of_advance_withPotential
      potential next advance
  · intro waiting production frontier next enabled nonempty _predicted
    exact frontierPredictionRank_lt_of_table owned correct final cursor
      potential prediction waiting production frontier.2.1 frontier.2.2
      next enabled nonempty
/-- The only residual is one finite grammar/span potential whose two
executable tables accept. -/
def GrammarRankedFrontierNormalization
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (memo : GuardMemo tokens)
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo)
    (cursor : Boundary tokens) : Prop :=
  ∃ potential : FrontierGrammarPotential tokens,
    frontierCompletionRankTable owned correct final cursor potential = true ∧
    frontierPredictionRankTable owned correct final cursor potential = true
theorem rankedFrontierNormalization_of_grammarRanked
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo} {cursor : Boundary tokens}
    (ranked : GrammarRankedFrontierNormalization
      file tokens owned memo correct final cursor) :
    RankedFrontierNormalization file tokens memo correct final cursor := by
  rcases ranked with ⟨potential, completion, prediction⟩
  exact ⟨frontierGrammarRank potential,
    frontierNormalizationRanking_of_grammarPotential
      owned potential completion prediction⟩
end Solcore.Surface.Multi
