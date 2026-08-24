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
/-- One executable enabled-coverage cell.  Only reached items on the selected
frontier impose a coverage obligation. -/
def frontierCoverageCell
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {memo : GuardMemo tokens}
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo) (cursor : Boundary tokens)
    (waiting : ContextualItemKey tokens) : Bool :=
  letI : Decidable
      (ContextualReach file tokens memo correct final waiting) :=
    contextualReachDecision owned correct final waiting
  letI : Decidable (waiting.raw.current = cursor) := inferInstance
  letI : Decidable
      (EnabledNonterminalCoverageAt
        file tokens memo correct final waiting) :=
    enabledNonterminalCoverageAtDecision correct final waiting
  if ContextualReach file tokens memo correct final waiting then
    if waiting.raw.current = cursor then
      decide (EnabledNonterminalCoverageAt
        file tokens memo correct final waiting)
    else true
  else true

/-- Coverage for every reached item on one frontier is checked over the public
finite contextual-item carrier. -/
def frontierCoverageTable
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {memo : GuardMemo tokens}
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo) (cursor : Boundary tokens) : Bool :=
  (allContextualItems tokens).all fun waiting =>
    frontierCoverageCell owned correct final cursor waiting

/-- Acceptance of the finite coverage table supplies the exact proposition
required by frontier normalization. -/
theorem enabledNonterminalCoverageAt_of_frontierCoverageTable
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {memo : GuardMemo tokens}
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo) (cursor : Boundary tokens)
    (checked : frontierCoverageTable owned correct final cursor = true)
    (waiting : ContextualItemKey tokens)
    (frontier : FrontierReach
      file tokens memo correct final cursor waiting) :
    EnabledNonterminalCoverageAt
      file tokens memo correct final waiting := by
  letI : Decidable
      (EnabledNonterminalCoverageAt
        file tokens memo correct final waiting) :=
    enabledNonterminalCoverageAtDecision correct final waiting
  have cell := (List.all_eq_true.mp checked) waiting
    (allContextualItems_complete waiting)
  simp only [frontierCoverageCell] at cell
  rw [if_pos frontier.2.1, if_pos frontier.2.2] at cell
  exact decide_eq_true_iff.mp cell

/-- Reached match-arm context readiness discharges every cell of the finite
coverage table through the fixed grammar classification. -/
theorem frontierCoverageTable_eq_true_of_reached_matchArmReady
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {memo : GuardMemo tokens}
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo) (cursor : Boundary tokens)
    (ready : ∀ waiting : ContextualItemKey tokens,
      ContextualReach file tokens memo correct final waiting →
        MatchArmPairContextReadyAt waiting) :
    frontierCoverageTable owned correct final cursor = true := by
  apply List.all_eq_true.mpr
  intro waiting _member
  letI : Decidable
      (ContextualReach file tokens memo correct final waiting) :=
    contextualReachDecision owned correct final waiting
  letI : Decidable (waiting.raw.current = cursor) := inferInstance
  letI : Decidable
      (EnabledNonterminalCoverageAt
        file tokens memo correct final waiting) :=
    enabledNonterminalCoverageAtDecision correct final waiting
  by_cases reached :
      ContextualReach file tokens memo correct final waiting
  · by_cases current : waiting.raw.current = cursor
    · simp only [frontierCoverageCell, if_pos reached, if_pos current]
      apply decide_eq_true_iff.mpr
      exact enabledNonterminalCoverageAt_of_anchored correct final waiting
        (anchoredNonterminalCoverageAt_of_reached_matchArmReady
          waiting reached (ready waiting reached))
    · simp [frontierCoverageCell, reached, current]
  · simp [frontierCoverageCell, reached]

/-- Executable check that a boundary is reached and bounds every reached
contextual item. -/
def greatestReachableCursorBool
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {memo : GuardMemo tokens}
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo) (cursor : Boundary tokens) : Bool :=
  ((allContextualItems tokens).any fun item =>
    letI : Decidable
        (ContextualReach file tokens memo correct final item) :=
      contextualReachDecision owned correct final item
    decide (ContextualReach file tokens memo correct final item) &&
      decide (item.raw.current = cursor)) &&
  ((allContextualItems tokens).all fun item =>
    letI : Decidable
        (ContextualReach file tokens memo correct final item) :=
      contextualReachDecision owned correct final item
    if ContextualReach file tokens memo correct final item then
      decide (item.raw.current.val ≤ cursor.val)
    else true)

/-- The finite greatest-cursor check is exact. -/
theorem greatestReachableCursorBool_eq_true_iff
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {memo : GuardMemo tokens}
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo) (cursor : Boundary tokens) :
    greatestReachableCursorBool owned correct final cursor = true ↔
      GreatestReachableCursor
        file tokens memo correct final cursor := by
  unfold greatestReachableCursorBool
  constructor
  · intro checked
    rw [Bool.and_eq_true] at checked
    rcases checked with ⟨reachedSome, bounded⟩
    constructor
    · rcases List.any_eq_true.mp reachedSome with
        ⟨item, _member, cell⟩
      letI : Decidable
          (ContextualReach file tokens memo correct final item) :=
        contextualReachDecision owned correct final item
      simp only [Bool.and_eq_true, decide_eq_true_iff] at cell
      exact ⟨item, cell.1, cell.2⟩
    · intro item reached
      have row := (List.all_eq_true.mp bounded) item
        (allContextualItems_complete item)
      letI : Decidable
          (ContextualReach file tokens memo correct final item) :=
        contextualReachDecision owned correct final item
      rw [if_pos reached] at row
      exact decide_eq_true_iff.mp row
  · intro greatest
    rw [Bool.and_eq_true]
    constructor
    · rcases greatest.1 with ⟨item, reached, current⟩
      apply List.any_eq_true.mpr
      refine ⟨item, allContextualItems_complete item, ?_⟩
      letI : Decidable
          (ContextualReach file tokens memo correct final item) :=
        contextualReachDecision owned correct final item
      simp [reached, current]
    · apply List.all_eq_true.mpr
      intro item _member
      letI : Decidable
          (ContextualReach file tokens memo correct final item) :=
        contextualReachDecision owned correct final item
      by_cases reached :
          ContextualReach file tokens memo correct final item
      · simp [reached, greatest.2 item reached]
      · simp [reached]

/-- Stable finite enumeration of all parser boundaries. -/
def allParserBoundaries (tokens : List Token) : List (Boundary tokens) :=
  List.ofFn id

/-- Every parser boundary occurs in the stable enumeration. -/
theorem allParserBoundaries_complete
    {tokens : List Token} (cursor : Boundary tokens) :
    cursor ∈ allParserBoundaries tokens := by
  rw [allParserBoundaries, List.mem_ofFn]
  exact ⟨cursor, rfl⟩

/-- Select the first boundary accepted by the exact greatest-cursor check. -/
def computedGreatestReachableCursor?
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {memo : GuardMemo tokens}
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo) : Option (Boundary tokens) :=
  (allParserBoundaries tokens).find? fun cursor =>
    greatestReachableCursorBool owned correct final cursor

/-- The finite greatest-cursor search always succeeds. -/
theorem computedGreatestReachableCursor?_isSome
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {memo : GuardMemo tokens}
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo) :
    (computedGreatestReachableCursor? owned correct final).isSome = true := by
  unfold computedGreatestReachableCursor?
  rw [List.find?_isSome]
  rcases chart_greatest_cursor_exists owned correct final with
    ⟨cursor, greatest⟩
  exact ⟨cursor, allParserBoundaries_complete cursor,
    (greatestReachableCursorBool_eq_true_iff
      owned correct final cursor).mpr greatest⟩

/-- Executable greatest reached boundary for the saturated chart. -/
def computedGreatestReachableCursor
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {memo : GuardMemo tokens}
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo) : Boundary tokens :=
  (computedGreatestReachableCursor? owned correct final).get
    (computedGreatestReachableCursor?_isSome owned correct final)

/-- The computed boundary satisfies the declarative greatest-cursor relation. -/
theorem computedGreatestReachableCursor_spec
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {memo : GuardMemo tokens}
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo) :
    GreatestReachableCursor file tokens memo correct final
      (computedGreatestReachableCursor owned correct final) := by
  have selected : computedGreatestReachableCursor? owned correct final =
      some (computedGreatestReachableCursor owned correct final) := by
    apply Option.eq_some_iff_get_eq.mpr
    exact ⟨computedGreatestReachableCursor?_isSome owned correct final, rfl⟩
  have accepted := List.find?_some selected
  exact (greatestReachableCursorBool_eq_true_iff owned correct final _).mp
    accepted

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

/-- Number of finite grammar/span coordinates available to a potential. -/
def frontierGrammarFrameCount (tokens : List Token) : Nat :=
  allProductionIds.length * (tokens.length + 2) * (tokens.length + 2)

/-- Stable mixed-radix index of one grammar/span coordinate. -/
def frontierGrammarFrameIndex {tokens : List Token}
    (production : ProductionId) (origin current : Boundary tokens) : Nat :=
  (production.index * (tokens.length + 2) + origin.val) *
      (tokens.length + 2) + current.val

/-- Interpret one natural number as a bounded value at every finite
grammar/span coordinate. -/
def frontierGrammarPotentialOfCode
    (tokens : List Token) (code : Nat) : FrontierGrammarPotential tokens :=
  fun production origin current =>
    let base := frontierGrammarFrameCount tokens + 1
    (code / base ^ frontierGrammarFrameIndex production origin current) % base

/-- Exhaustively search the finite bounded potential space for a code whose
completion and prediction tables both accept. -/
def boundedFrontierGrammarPotential?
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {memo : GuardMemo tokens}
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo) (cursor : Boundary tokens) :
    Option (FrontierGrammarPotential tokens) :=
  let count := frontierGrammarFrameCount tokens
  let base := count + 1
  ((List.range (base ^ count)).find? fun code =>
    let potential := frontierGrammarPotentialOfCode tokens code
    frontierCompletionRankTable owned correct final cursor potential &&
      frontierPredictionRankTable owned correct final cursor potential).map
    (frontierGrammarPotentialOfCode tokens)

/-- Every potential returned by the bounded search satisfies both exact
finite rank tables. -/
theorem boundedFrontierGrammarPotential?_sound
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {memo : GuardMemo tokens}
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo) (cursor : Boundary tokens)
    {potential : FrontierGrammarPotential tokens}
    (selected : boundedFrontierGrammarPotential?
      owned correct final cursor = some potential) :
    frontierCompletionRankTable
        owned correct final cursor potential = true ∧
      frontierPredictionRankTable
        owned correct final cursor potential = true := by
  unfold boundedFrontierGrammarPotential? at selected
  simp only [Option.map_eq_some_iff] at selected
  rcases selected with ⟨code, found, rfl⟩
  have accepted := List.find?_some found
  rw [Bool.and_eq_true] at accepted
  exact accepted

/-- The single exact residual left by bounded potential synthesis. -/
def BoundedFrontierGrammarRankSearchSucceeds
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {memo : GuardMemo tokens}
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo) (cursor : Boundary tokens) : Prop :=
  (boundedFrontierGrammarPotential?
    owned correct final cursor).isSome = true

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

/-- Successful bounded synthesis discharges the entire grammar-ranked
frontier residual without requiring a caller-supplied potential. -/
theorem grammarRankedFrontierNormalization_of_boundedSearch
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo} {cursor : Boundary tokens}
    (success : BoundedFrontierGrammarRankSearchSucceeds
      owned correct final cursor) :
    GrammarRankedFrontierNormalization
      file tokens owned memo correct final cursor := by
  unfold BoundedFrontierGrammarRankSearchSucceeds at success
  rw [Option.isSome_iff_exists] at success
  rcases success with ⟨potential, selected⟩
  exact ⟨potential,
    boundedFrontierGrammarPotential?_sound
      owned correct final cursor selected⟩

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
