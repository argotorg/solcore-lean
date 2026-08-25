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
/-- If a static completion weight is unchanged, the caller must begin
strictly before its child whenever zero-span callers select only strict
static completion edges. -/
theorem contextualActivationParent_origin_lt_of_equalCompletionWeight
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    (nullablePrefix : DottedRhs → Bool) (weight : DottedRhs → Nat)
    {parent finished after : ContextualItemKey tokens}
    (activated : ContextualActivationParent
      file tokens memo correct final parent finished)
    (_complete : CompleteItem finished.raw)
    (_advance : AdvanceItem parent.raw finished.raw.current after.raw)
    (equalWeight :
      weight (frontierDottedRhsOfItem after.raw) =
        weight (frontierDottedRhsOfItem finished.raw))
    (nullableAtOrigin : parent.raw.origin = parent.raw.current →
      nullablePrefix (frontierDottedRhsOfItem parent.raw) = true)
    (strictOfNullable :
      nullablePrefix (frontierDottedRhsOfItem parent.raw) = true →
      weight (frontierDottedRhsOfItem after.raw) <
        weight (frontierDottedRhsOfItem finished.raw)) :
    parent.raw.origin.val < finished.raw.origin.val := by
  have ordered := contextualActivationParent_origin_le activated
  apply Nat.lt_of_le_of_ne ordered
  intro equalOriginValue
  have equalOrigin : parent.raw.origin = finished.raw.origin :=
    Fin.ext equalOriginValue
  have parentAtOrigin : parent.raw.origin = parent.raw.current :=
    equalOrigin.trans activated.2.2.1.symm
  have decreases := strictOfNullable (nullableAtOrigin parentAtOrigin)
  exact (Nat.ne_of_lt decreases) equalWeight


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

/-- Pointwise descent for every enabled nonempty prediction makes the exact
dotted prediction table accept. -/
theorem frontierDottedPredictionRankTable_eq_true_of_decreases
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {memo : GuardMemo tokens}
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo) (cursor : Boundary tokens)
    (potential : FrontierDottedGrammarPotential tokens)
    (decreases : ∀ waiting production,
      ContextualReach file tokens memo correct final waiting →
      waiting.raw.current = cursor →
      NextSymbol waiting.raw (.nonterminal production.lhs) →
      EnabledProductionInstance file tokens memo correct final {
        production := production
        origin := waiting.raw.current
        context := descendContext waiting production
      } →
      production.rhs ≠ [] →
      frontierDottedGrammarRank potential
          (FrontierPredictedItem waiting production) <
        frontierDottedGrammarRank potential waiting) :
    frontierDottedPredictionRankTable
      owned correct final cursor potential = true := by
  apply List.all_eq_true.mpr
  intro waiting _waitingMember
  apply List.all_eq_true.mpr
  intro production _productionMember
  letI : Decidable
      (ContextualReach file tokens memo correct final waiting) :=
    contextualReachDecision owned correct final waiting
  letI : Decidable
      (NextSymbol waiting.raw (.nonterminal production.lhs)) :=
    dottedNextSymbolDecision waiting.raw (.nonterminal production.lhs)
  letI : Decidable
      (EnabledProductionInstance file tokens memo correct final {
        production := production
        origin := waiting.raw.current
        context := descendContext waiting production
      }) := enabledProductionInstanceDecision correct final _
  by_cases reached : ContextualReach file tokens memo correct final waiting
  · by_cases current : waiting.raw.current = cursor
    · by_cases next :
        NextSymbol waiting.raw (.nonterminal production.lhs)
      · by_cases enabled : EnabledProductionInstance file tokens memo
          correct final {
            production := production
            origin := waiting.raw.current
            context := descendContext waiting production
          }
        · by_cases nonempty : production.rhs ≠ []
          · simp only [frontierDottedPredictionRankCell, if_pos reached,
              if_pos current, if_pos next, if_pos enabled,
              if_pos nonempty, decide_eq_true_iff]
            exact decreases waiting production reached current next enabled
              nonempty
          · simp [frontierDottedPredictionRankCell, reached, current,
              next, nonempty]
        · have disabledAtCursor : ¬ EnabledProductionInstance file tokens
              memo correct final {
                production := production
                origin := cursor
                context := descendContext waiting production
              } := by
            intro enabledAtCursor
            apply enabled
            rw [current]
            exact enabledAtCursor
          simp [frontierDottedPredictionRankCell, reached, current, next,
            disabledAtCursor]
      · simp [frontierDottedPredictionRankCell, reached, current, next]
    · simp [frontierDottedPredictionRankCell, reached, current]
  · simp [frontierDottedPredictionRankCell, reached]

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

/-- Conversely, explicit normalization witnesses at a greatest frontier make
the exact dotted completion table accept. -/
theorem frontierDottedCompletionRankTable_eq_true_of_normalizes
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {memo : GuardMemo tokens}
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo) (cursor : Boundary tokens)
    (greatest : GreatestReachableCursor
      file tokens memo correct final cursor)
    (potential : FrontierDottedGrammarPotential tokens)
    (normalizes : ∀ waiting,
      FrontierReach file tokens memo correct final cursor waiting →
      CompleteItem waiting.raw →
      waiting = CanonicalCompleteRootItem tokens .module
          (Boundary.start tokens) (Boundary.afterLogicalEOF tokens) .plain ∨
        ∃ after : ContextualItemKey tokens,
          FrontierReach file tokens memo correct final cursor after ∧
          frontierDottedGrammarRank potential after <
            frontierDottedGrammarRank potential waiting) :
    frontierDottedCompletionRankTable
      owned correct final cursor potential = true := by
  apply List.all_eq_true.mpr
  intro waiting _waitingMember
  letI : Decidable
      (ContextualReach file tokens memo correct final waiting) :=
    contextualReachDecision owned correct final waiting
  letI : Decidable (CompleteItem waiting.raw) :=
    dottedCompleteItemDecision waiting.raw
  by_cases reached : ContextualReach file tokens memo correct final waiting
  · by_cases current : waiting.raw.current = cursor
    · by_cases complete : CompleteItem waiting.raw
      · simp only [frontierDottedCompletionRankCell, if_pos reached,
          if_pos current, if_pos complete, Bool.or_eq_true]
        rcases normalizes waiting ⟨greatest, reached, current⟩ complete with
          root | ⟨after, afterFrontier, decreases⟩
        · exact Or.inl (decide_eq_true_iff.mpr root)
        · apply Or.inr
          apply List.any_eq_true.mpr
          refine ⟨after, allContextualItems_complete after, ?_⟩
          apply (frontierDottedLowerRankCell_eq_true_iff
            owned correct final cursor potential waiting after).mpr
          exact ⟨afterFrontier.2.1, afterFrontier.2.2, decreases⟩
      · simp [frontierDottedCompletionRankCell, reached, current, complete]
    · simp [frontierDottedCompletionRankCell, reached, current]
  · simp [frontierDottedCompletionRankCell, reached]

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

/-- Pointwise descent for every direct epsilon advance makes the exact dotted
epsilon table accept. -/
theorem frontierDottedEpsilonRankTable_eq_true_of_decreases
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {memo : GuardMemo tokens}
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo) (cursor : Boundary tokens)
    (potential : FrontierDottedGrammarPotential tokens)
    (decreases : ∀ waiting production after,
      ContextualReach file tokens memo correct final waiting →
      waiting.raw.current = cursor →
      NextSymbol waiting.raw (.nonterminal production.lhs) →
      EnabledProductionInstance file tokens memo correct final {
        production := production
        origin := waiting.raw.current
        context := descendContext waiting production
      } →
      production.rhs = [] →
      ContextualReach file tokens memo correct final after →
      after.raw.current = cursor →
      AdvanceItem waiting.raw waiting.raw.current after.raw →
      frontierDottedGrammarRank potential after <
        frontierDottedGrammarRank potential waiting) :
    frontierDottedEpsilonRankTable
      owned correct final cursor potential = true := by
  apply List.all_eq_true.mpr
  intro waiting _waitingMember
  apply List.all_eq_true.mpr
  intro production _productionMember
  apply List.all_eq_true.mpr
  intro after _afterMember
  simp only [frontierDottedEpsilonRankCell]
  split
  next waitingReached =>
    split
    next waitingCurrent =>
      split
      next nextSymbol =>
        split
        next enabled =>
          split
          next epsilon =>
            split
            next afterReached =>
              split
              next afterCurrent =>
                split
                next advance =>
                  exact decide_eq_true_iff.mpr
                    (decreases waiting production after waitingReached
                      waitingCurrent nextSymbol enabled epsilon afterReached
                      afterCurrent advance)
                next => rfl
              next => rfl
            next => rfl
          next => rfl
        next => rfl
      next => rfl
    next => rfl
  next => rfl

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

/-- Number of dotted grammar/span coordinates in one finite potential. -/
def frontierDottedGrammarFrameCount (tokens : List Token) : Nat :=
  allDottedRhs.length * (tokens.length + 2) * (tokens.length + 2)

/-- One proof-free dotted grammar/span coordinate. -/
structure FrontierDottedGrammarFrame (tokens : List Token) where
  dotted : DottedRhs
  origin : Boundary tokens
  current : Boundary tokens
  deriving DecidableEq

/-- Every dotted grammar/span coordinate in stable order. -/
def allFrontierDottedGrammarFrames
    (tokens : List Token) : List (FrontierDottedGrammarFrame tokens) :=
  allDottedRhs.flatMap fun dotted =>
    (allParserBoundaries tokens).flatMap fun origin =>
      (allParserBoundaries tokens).map fun current =>
        { dotted, origin, current }

/-- Every dotted grammar/span coordinate occurs in the stable carrier. -/
theorem allFrontierDottedGrammarFrames_complete
    {tokens : List Token} (frame : FrontierDottedGrammarFrame tokens) :
    frame ∈ allFrontierDottedGrammarFrames tokens := by
  rw [allFrontierDottedGrammarFrames, List.mem_flatMap]
  refine ⟨frame.dotted, allDottedRhs_complete _, ?_⟩
  rw [List.mem_flatMap]
  refine ⟨frame.origin, allParserBoundaries_complete _, ?_⟩
  rw [List.mem_map]
  exact ⟨frame.current, allParserBoundaries_complete _, by cases frame; rfl⟩

private def frontierDottedGrammarFrameValue
    {tokens : List Token} (potential : FrontierDottedGrammarPotential tokens)
    (frame : FrontierDottedGrammarFrame tokens) : Nat :=
  potential frame.dotted frame.origin frame.current

private def frontierDottedGrammarPotentialLookup
    {tokens : List Token} :
    List (FrontierDottedGrammarFrame tokens) → List Nat →
      FrontierDottedGrammarFrame tokens → Nat
  | frame :: frames, value :: values, target =>
      if frame = target then value
      else frontierDottedGrammarPotentialLookup frames values target
  | _, _, _ => 0

private theorem frontierDottedGrammarPotentialLookup_map
    {tokens : List Token}
    (frames : List (FrontierDottedGrammarFrame tokens))
    (value : FrontierDottedGrammarFrame tokens → Nat)
    (target : FrontierDottedGrammarFrame tokens)
    (member : target ∈ frames) :
    frontierDottedGrammarPotentialLookup frames (frames.map value) target =
      value target := by
  induction frames with
  | nil => simp at member
  | cons frame frames induction =>
      by_cases equal : frame = target
      · subst target
        simp [frontierDottedGrammarPotentialLookup]
      · simp only [List.mem_cons] at member
        rcases member with equal' | member
        · exact (equal equal'.symm).elim
        · simp [frontierDottedGrammarPotentialLookup, equal,
            induction member]

/-- Interpret a value list over the stable dotted-frame carrier. -/
def frontierDottedGrammarPotentialOfValues
    (tokens : List Token) (values : List Nat) :
    FrontierDottedGrammarPotential tokens :=
  fun dotted origin current =>
    frontierDottedGrammarPotentialLookup
      (allFrontierDottedGrammarFrames tokens) values
      { dotted, origin, current }

/-- Tabulate a dotted potential in stable frame order. -/
def frontierDottedGrammarValuesOfPotential
    (tokens : List Token) (potential : FrontierDottedGrammarPotential tokens) :
    List Nat :=
  (allFrontierDottedGrammarFrames tokens).map
    (frontierDottedGrammarFrameValue potential)

/-- Stable dotted-frame tabulation followed by lookup is exact. -/
theorem frontierDottedGrammarPotentialOfValues_valuesOfPotential
    {tokens : List Token} (potential : FrontierDottedGrammarPotential tokens) :
    frontierDottedGrammarPotentialOfValues tokens
      (frontierDottedGrammarValuesOfPotential tokens potential) =
        potential := by
  funext dotted origin current
  exact frontierDottedGrammarPotentialLookup_map
    (allFrontierDottedGrammarFrames tokens)
    (frontierDottedGrammarFrameValue potential)
    { dotted, origin, current }
    (allFrontierDottedGrammarFrames_complete _)

/-- The stable dotted-frame carrier has its advertised cardinality. -/
theorem allFrontierDottedGrammarFrames_length (tokens : List Token) :
    (allFrontierDottedGrammarFrames tokens).length =
      frontierDottedGrammarFrameCount tokens := by
  have boundaryLength :
      (allParserBoundaries tokens).length = tokens.length + 2 := by
    simp [allParserBoundaries]
  have oneDotted : ∀ dotted : DottedRhs,
      ((allParserBoundaries tokens).flatMap fun origin =>
        (allParserBoundaries tokens).map fun current =>
          ({ dotted, origin, current } :
            FrontierDottedGrammarFrame tokens)).length =
        (tokens.length + 2) * (tokens.length + 2) := by
    intro dotted
    have generalOrigins : ∀ origins : List (Boundary tokens),
        (origins.flatMap fun origin =>
          (allParserBoundaries tokens).map fun current =>
            ({ dotted, origin, current } :
              FrontierDottedGrammarFrame tokens)).length =
          origins.length * (tokens.length + 2) := by
      intro origins
      induction origins with
      | nil => simp
      | cons origin origins induction =>
          simp [boundaryLength, induction, Nat.add_mul, Nat.add_comm]
    rw [generalOrigins, boundaryLength]
  have general : ∀ dotteds : List DottedRhs,
      (dotteds.flatMap fun dotted =>
        (allParserBoundaries tokens).flatMap fun origin =>
          (allParserBoundaries tokens).map fun current =>
            ({ dotted, origin, current } :
              FrontierDottedGrammarFrame tokens)).length =
        dotteds.length * (tokens.length + 2) *
          (tokens.length + 2) := by
    intro dotteds
    induction dotteds with
    | nil => simp
    | cons dotted dotteds induction =>
        simp [oneDotted, induction, Nat.add_mul, Nat.mul_assoc,
          Nat.add_comm]
  exact (general allDottedRhs).trans (by
    simp [frontierDottedGrammarFrameCount, Nat.mul_assoc])

/-- Exhaustively search the bounded dotted-potential space for acceptance by
all three exact normalization tables. -/
def boundedFrontierDottedGrammarPotential?
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {memo : GuardMemo tokens}
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo) (cursor : Boundary tokens) :
    Option (FrontierDottedGrammarPotential tokens) :=
  let count := frontierDottedGrammarFrameCount tokens
  let base := count + 1
  ((allBoundedNatLists count base).find? fun values =>
    let potential := frontierDottedGrammarPotentialOfValues tokens values
    frontierDottedCompletionRankTable
        owned correct final cursor potential &&
      (frontierDottedEpsilonRankTable
          owned correct final cursor potential &&
        frontierDottedPredictionRankTable
          owned correct final cursor potential)).map
    (frontierDottedGrammarPotentialOfValues tokens)

/-- Every returned dotted potential satisfies all three exact tables. -/
theorem boundedFrontierDottedGrammarPotential?_sound
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {memo : GuardMemo tokens}
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo) (cursor : Boundary tokens)
    {potential : FrontierDottedGrammarPotential tokens}
    (selected : boundedFrontierDottedGrammarPotential?
      owned correct final cursor = some potential) :
    frontierDottedCompletionRankTable
        owned correct final cursor potential = true ∧
      frontierDottedEpsilonRankTable
          owned correct final cursor potential = true ∧
        frontierDottedPredictionRankTable
          owned correct final cursor potential = true := by
  unfold boundedFrontierDottedGrammarPotential? at selected
  simp only [Option.map_eq_some_iff] at selected
  rcases selected with ⟨values, found, rfl⟩
  have accepted := List.find?_some found
  rw [Bool.and_eq_true, Bool.and_eq_true] at accepted
  exact accepted

/-- Any bounded accepting dotted potential is represented by the exhaustive
search. -/
theorem boundedFrontierDottedGrammarPotential?_isSome_of_bounded
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {memo : GuardMemo tokens}
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo) (cursor : Boundary tokens)
    (potential : FrontierDottedGrammarPotential tokens)
    (bounded : ∀ dotted origin current,
      potential dotted origin current <
        frontierDottedGrammarFrameCount tokens + 1)
    (completion : frontierDottedCompletionRankTable
      owned correct final cursor potential = true)
    (epsilon : frontierDottedEpsilonRankTable
      owned correct final cursor potential = true)
    (prediction : frontierDottedPredictionRankTable
      owned correct final cursor potential = true) :
    (boundedFrontierDottedGrammarPotential?
      owned correct final cursor).isSome = true := by
  unfold boundedFrontierDottedGrammarPotential?
  simp only [Option.isSome_map, List.find?_isSome]
  let values := frontierDottedGrammarValuesOfPotential tokens potential
  have length : values.length = frontierDottedGrammarFrameCount tokens := by
    simp [values, frontierDottedGrammarValuesOfPotential,
      allFrontierDottedGrammarFrames_length]
  have valuesBounded : ∀ value, value ∈ values →
      value < frontierDottedGrammarFrameCount tokens + 1 := by
    intro value member
    simp only [values, frontierDottedGrammarValuesOfPotential,
      List.mem_map] at member
    rcases member with ⟨frame, _frameMember, rfl⟩
    exact bounded frame.dotted frame.origin frame.current
  refine ⟨values, ?_, ?_⟩
  · simpa only [length] using
      (allBoundedNatLists_complete _ values valuesBounded)
  · rw [frontierDottedGrammarPotentialOfValues_valuesOfPotential]
    rw [Bool.and_eq_true, Bool.and_eq_true]
    exact ⟨completion, epsilon, prediction⟩

/-- Executable success residual for the bounded dotted-potential search. -/
def BoundedFrontierDottedGrammarRankSearchSucceeds
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {memo : GuardMemo tokens}
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo) (cursor : Boundary tokens) : Prop :=
  (boundedFrontierDottedGrammarPotential?
    owned correct final cursor).isSome = true

/-- A bounded three-table witness discharges dotted search success. -/
theorem boundedFrontierDottedGrammarRankSearchSucceeds_of_potential
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {memo : GuardMemo tokens}
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo) (cursor : Boundary tokens)
    (potential : FrontierDottedGrammarPotential tokens)
    (bounded : ∀ dotted origin current,
      potential dotted origin current <
        frontierDottedGrammarFrameCount tokens + 1)
    (completion : frontierDottedCompletionRankTable
      owned correct final cursor potential = true)
    (epsilon : frontierDottedEpsilonRankTable
      owned correct final cursor potential = true)
    (prediction : frontierDottedPredictionRankTable
      owned correct final cursor potential = true) :
    BoundedFrontierDottedGrammarRankSearchSucceeds
      owned correct final cursor :=
  boundedFrontierDottedGrammarPotential?_isSome_of_bounded
    owned correct final cursor potential bounded completion epsilon prediction

/-- Successful bounded dotted synthesis exposes its accepted three-table
certificate. -/
theorem dottedGrammarRankedFrontierNormalization_of_boundedSearch
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo} {cursor : Boundary tokens}
    (success : BoundedFrontierDottedGrammarRankSearchSucceeds
      owned correct final cursor) :
    DottedGrammarRankedFrontierNormalization
      file tokens owned memo correct final cursor := by
  unfold BoundedFrontierDottedGrammarRankSearchSucceeds at success
  rw [Option.isSome_iff_exists] at success
  rcases success with ⟨potential, selected⟩
  exact ⟨potential,
    boundedFrontierDottedGrammarPotential?_sound
      owned correct final cursor selected⟩

/-- Successful bounded dotted synthesis directly supplies abstract ranked
normalization. -/
theorem rankedFrontierNormalization_of_boundedDottedSearch
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo} {cursor : Boundary tokens}
    (success : BoundedFrontierDottedGrammarRankSearchSucceeds
      owned correct final cursor) :
    RankedFrontierNormalization file tokens memo correct final cursor :=
  rankedFrontierNormalization_of_dottedGrammarRanked owned
    (dottedGrammarRankedFrontierNormalization_of_boundedSearch
      owned success)

end Solcore.Surface.Multi
