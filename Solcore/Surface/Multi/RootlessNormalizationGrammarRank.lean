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

private theorem sublist_flatMap_of_mem
    {alpha beta : Type} (f : alpha → List beta)
    {value : alpha} {values : List alpha} (member : value ∈ values) :
    (f value).Sublist (values.flatMap f) := by
  induction values with
  | nil => simp at member
  | cons head tail induction =>
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact List.sublist_append_left _ _
      · exact (induction member).trans (List.sublist_append_right _ _)

/-- Every expanded RHS is bounded by the public dotted-position count. -/
theorem productionRhsLength_le_D (production : ProductionId) :
    production.rhs.length ≤ D := by
  let block : List DottedRhs :=
    (List.ofFn fun dot : Fin (production.rhs.length + 1) => dot).map
      fun dot => ({ production, dot } : DottedRhs)
  have sublist : block.Sublist allDottedRhs := by
    exact sublist_flatMap_of_mem
      (fun selected =>
        (List.ofFn fun dot : Fin (selected.rhs.length + 1) => dot).map
          fun dot => ({ production := selected, dot } : DottedRhs))
      (allProductionIds_complete production)
  have lengthLe := sublist.length_le
  have blockLength : block.length = production.rhs.length + 1 := by
    simp [block]
  rw [blockLength, allDottedRhs_length] at lengthLe
  omega

/-- Strict descent of a coarse grammar/span potential dominates every
possible dotted-RHS remainder. -/
theorem frontierRawGrammarRank_lt_of_potential_lt
    {tokens : List Token} (potential : FrontierGrammarPotential tokens)
    {before after : DottedItem tokens}
    (decreases : potential after.production after.origin after.current <
      potential before.production before.origin before.current) :
    frontierRawGrammarRank potential after <
      frontierRawGrammarRank potential before := by
  have remainingLe : frontierRhsRemaining after ≤ D :=
    Nat.le_trans (Nat.sub_le _ _) (productionRhsLength_le_D _)
  have potentialStep :
      potential after.production after.origin after.current + 1 ≤
        potential before.production before.origin before.current :=
    Nat.succ_le_of_lt decreases
  unfold frontierRawGrammarRank
  calc
    (D + 1) * potential after.production after.origin after.current +
          frontierRhsRemaining after ≤
        (D + 1) * potential after.production after.origin after.current + D :=
      Nat.add_le_add_left remainingLe _
    _ < (D + 1) * potential after.production after.origin after.current +
          (D + 1) := by omega
    _ = (D + 1) *
          (potential after.production after.origin after.current + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
    _ ≤ (D + 1) *
          potential before.production before.origin before.current :=
      Nat.mul_le_mul_left _ potentialStep
    _ ≤ (D + 1) *
          potential before.production before.origin before.current +
          frontierRhsRemaining before := Nat.le_add_right _ _

/-- A two-mode potential separates zero-span predictions from already
progressed frames, while retaining a finite production-local weight. -/
def frontierSpanPotential
    (width : Nat) (zero positive : ProductionId → Nat)
    {tokens : List Token} : FrontierGrammarPotential tokens :=
  fun production origin current =>
    if origin = current then zero production
    else (origin.val + 1) * width + positive production

/-- Once a waiting item has consumed input, its predicted zero-span child has
strictly smaller coarse potential whenever zero weights fit the production
carrier. -/
theorem frontierSpanPotential_predicted_lt_of_positiveSpan
    (width : Nat) (zero positive : ProductionId → Nat)
    (zeroBound : ∀ production, zero production < width)
    {tokens : List Token} (waiting : ContextualItemKey tokens)
    (production : ProductionId)
    (progress : waiting.raw.origin.val < waiting.raw.current.val) :
    frontierSpanPotential width zero positive production
        waiting.raw.current waiting.raw.current <
      frontierSpanPotential width zero positive waiting.raw.production
        waiting.raw.origin waiting.raw.current := by
  have different : waiting.raw.origin ≠ waiting.raw.current := by
    intro equal
    rw [equal] at progress
    omega
  simp only [frontierSpanPotential, if_neg different]
  exact Nat.lt_of_lt_of_le (zeroBound production)
    (calc
      width ≤ width + (waiting.raw.origin.val * width +
          positive waiting.raw.production) := Nat.le_add_right _ _
      _ = (waiting.raw.origin.val + 1) * width +
          positive waiting.raw.production := by
        simp [Nat.add_mul, Nat.add_comm, Nat.add_left_comm])

/-- Positive-span frontier prediction decreases the full grammar rank. -/
theorem frontierGrammarRank_lt_predicted_of_positiveSpan
    (width : Nat) (zero positive : ProductionId → Nat)
    (zeroBound : ∀ production, zero production < width)
    {tokens : List Token} (waiting : ContextualItemKey tokens)
    (production : ProductionId)
    (progress : waiting.raw.origin.val < waiting.raw.current.val) :
    frontierGrammarRank (frontierSpanPotential width zero positive)
        (FrontierPredictedItem waiting production) <
      frontierGrammarRank (frontierSpanPotential width zero positive)
        waiting := by
  apply frontierRawGrammarRank_lt_of_potential_lt
  exact frontierSpanPotential_predicted_lt_of_positiveSpan
    width zero positive zeroBound waiting production progress
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

/-- Reachability discharges every cell of the finite coverage table for the
fixed grammar. -/
theorem frontierCoverageTable_eq_true
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {memo : GuardMemo tokens}
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo) (cursor : Boundary tokens) :
    frontierCoverageTable owned correct final cursor = true := by
  exact frontierCoverageTable_eq_true_of_reached_matchArmReady
    owned correct final cursor fun waiting reached =>
      matchArmPairContextReadyAt_of_reached waiting reached

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

/-- For the span-separated potential, only zero-span prediction cells remain
to be established: every positive-span cell decreases automatically. -/
theorem frontierPredictionRankTable_eq_true_of_zeroSpan
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {memo : GuardMemo tokens}
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo) (cursor : Boundary tokens)
    (width : Nat) (zero positive : ProductionId → Nat)
    (zeroBound : ∀ production, zero production < width)
    (zeroSpan : ∀ waiting production,
      ContextualReach file tokens memo correct final waiting →
      waiting.raw.current = cursor →
      waiting.raw.origin = waiting.raw.current →
      NextSymbol waiting.raw (.nonterminal production.lhs) →
      EnabledProductionInstance file tokens memo correct final {
        production := production
        origin := waiting.raw.current
        context := descendContext waiting production
      } →
      production.rhs ≠ [] →
      frontierGrammarRank (frontierSpanPotential width zero positive)
          (FrontierPredictedItem waiting production) <
        frontierGrammarRank (frontierSpanPotential width zero positive)
          waiting) :
    frontierPredictionRankTable owned correct final cursor
      (frontierSpanPotential width zero positive) = true := by
  apply List.all_eq_true.mpr
  intro waiting _waitingMember
  apply List.all_eq_true.mpr
  intro production _productionMember
  letI : Decidable
      (ContextualReach file tokens memo correct final waiting) :=
    contextualReachDecision owned correct final waiting
  letI : Decidable
      (NextSymbol waiting.raw (.nonterminal production.lhs)) :=
    nextSymbolDecision waiting.raw (.nonterminal production.lhs)
  letI : Decidable
      (EnabledProductionInstance file tokens memo correct final {
        production := production
        origin := waiting.raw.current
        context := descendContext waiting production
      }) := enabledProductionInstanceDecision correct final _
  letI : Decidable (waiting.raw.current = cursor) := inferInstance
  letI : Decidable (production.rhs ≠ []) := inferInstance
  letI : Decidable
      (frontierGrammarRank (frontierSpanPotential width zero positive)
          (FrontierPredictedItem waiting production) <
        frontierGrammarRank (frontierSpanPotential width zero positive)
          waiting) := inferInstance
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
          · simp only [frontierPredictionRankCell, if_pos reached,
              if_pos current, if_pos next, if_pos enabled,
              if_pos nonempty, decide_eq_true_iff]
            by_cases atOrigin :
                waiting.raw.origin = waiting.raw.current
            · exact zeroSpan waiting production reached current atOrigin
                next enabled nonempty
            · have ordered := contextualReach_ordered reached
              have valueNe : waiting.raw.origin.val ≠
                  waiting.raw.current.val := by
                intro equal
                exact atOrigin (Fin.ext equal)
              exact frontierGrammarRank_lt_predicted_of_positiveSpan
                width zero positive zeroBound waiting production
                  (Nat.lt_of_le_of_ne ordered valueNe)
          · simp [frontierPredictionRankCell, reached, current, next,
              nonempty]
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
          simp [frontierPredictionRankCell, reached, current, next,
            disabledAtCursor]
      · simp [frontierPredictionRankCell, reached, current, next]
    · simp [frontierPredictionRankCell, reached, current]
  · simp [frontierPredictionRankCell, reached]
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

/-- One proof-free coordinate of a frontier grammar potential. -/
structure FrontierGrammarFrame (tokens : List Token) where
  production : ProductionId
  origin : Boundary tokens
  current : Boundary tokens
  deriving DecidableEq

/-- Every grammar/span coordinate in stable production/origin/current order. -/
def allFrontierGrammarFrames
    (tokens : List Token) : List (FrontierGrammarFrame tokens) :=
  allProductionIds.flatMap fun production =>
    (allParserBoundaries tokens).flatMap fun origin =>
      (allParserBoundaries tokens).map fun current =>
        { production, origin, current }

/-- Every frontier grammar coordinate occurs in the stable enumeration. -/
theorem allFrontierGrammarFrames_complete
    {tokens : List Token} (frame : FrontierGrammarFrame tokens) :
    frame ∈ allFrontierGrammarFrames tokens := by
  rw [allFrontierGrammarFrames, List.mem_flatMap]
  refine ⟨frame.production, allProductionIds_complete _, ?_⟩
  rw [List.mem_flatMap]
  refine ⟨frame.origin, allParserBoundaries_complete _, ?_⟩
  rw [List.mem_map]
  exact ⟨frame.current, allParserBoundaries_complete _, by cases frame; rfl⟩

/-- Enumerate all fixed-length lists whose entries are below one bound. -/
def allBoundedNatLists : Nat → Nat → List (List Nat)
  | 0, _ => [[]]
  | count + 1, bound =>
      (List.range bound).flatMap fun head =>
        (allBoundedNatLists count bound).map (head :: ·)

/-- Every pointwise bounded list occurs in the exhaustive list space. -/
theorem allBoundedNatLists_complete
    (bound : Nat) (values : List Nat)
    (bounded : ∀ value, value ∈ values → value < bound) :
    values ∈ allBoundedNatLists values.length bound := by
  induction values with
  | nil => simp [allBoundedNatLists]
  | cons head tail induction =>
      simp only [List.length_cons, allBoundedNatLists, List.mem_flatMap,
        List.mem_range, List.mem_map]
      refine ⟨head, bounded head (by simp), tail, ?_, rfl⟩
      apply induction
      intro value member
      exact bounded value (by simp [member])

private def frontierGrammarFrameValue
    {tokens : List Token} (potential : FrontierGrammarPotential tokens)
    (frame : FrontierGrammarFrame tokens) : Nat :=
  potential frame.production frame.origin frame.current

private def frontierGrammarPotentialLookup
    {tokens : List Token} :
    List (FrontierGrammarFrame tokens) → List Nat →
      FrontierGrammarFrame tokens → Nat
  | frame :: frames, value :: values, target =>
      if frame = target then value
      else frontierGrammarPotentialLookup frames values target
  | _, _, _ => 0

private theorem frontierGrammarPotentialLookup_map
    {tokens : List Token} (frames : List (FrontierGrammarFrame tokens))
    (value : FrontierGrammarFrame tokens → Nat)
    (target : FrontierGrammarFrame tokens) (member : target ∈ frames) :
    frontierGrammarPotentialLookup frames (frames.map value) target =
      value target := by
  induction frames with
  | nil => simp at member
  | cons frame frames induction =>
      by_cases equal : frame = target
      · subst target
        simp [frontierGrammarPotentialLookup]
      · simp only [List.mem_cons] at member
        rcases member with equal' | member
        · exact (equal equal'.symm).elim
        · simp [frontierGrammarPotentialLookup, equal,
            induction member]

/-- Interpret one value list over the stable grammar-frame enumeration. -/
def frontierGrammarPotentialOfValues
    (tokens : List Token) (values : List Nat) :
    FrontierGrammarPotential tokens :=
  fun production origin current =>
    frontierGrammarPotentialLookup (allFrontierGrammarFrames tokens) values
      { production, origin, current }

/-- Tabulate a potential in stable grammar-frame order. -/
def frontierGrammarValuesOfPotential
    (tokens : List Token) (potential : FrontierGrammarPotential tokens) :
    List Nat :=
  (allFrontierGrammarFrames tokens).map
    (frontierGrammarFrameValue potential)

/-- Stable tabulation followed by lookup recovers the original potential. -/
theorem frontierGrammarPotentialOfValues_valuesOfPotential
    {tokens : List Token} (potential : FrontierGrammarPotential tokens) :
    frontierGrammarPotentialOfValues tokens
      (frontierGrammarValuesOfPotential tokens potential) = potential := by
  funext production origin current
  exact frontierGrammarPotentialLookup_map
    (allFrontierGrammarFrames tokens) (frontierGrammarFrameValue potential)
    { production, origin, current }
    (allFrontierGrammarFrames_complete _)

/-- The stable frame enumeration has the advertised mixed-radix count. -/
theorem allFrontierGrammarFrames_length (tokens : List Token) :
    (allFrontierGrammarFrames tokens).length =
      frontierGrammarFrameCount tokens := by
  have lengthOfBoundaries :
      (allParserBoundaries tokens).length = tokens.length + 2 := by
    simp [allParserBoundaries]
  have oneProduction : ∀ production : ProductionId,
      ((allParserBoundaries tokens).flatMap fun origin =>
        (allParserBoundaries tokens).map fun current =>
          ({ production, origin, current } :
            FrontierGrammarFrame tokens)).length =
        (tokens.length + 2) * (tokens.length + 2) := by
    intro production
    have generalOrigins : ∀ origins : List (Boundary tokens),
        (origins.flatMap fun origin =>
          (allParserBoundaries tokens).map fun current =>
            ({ production, origin, current } :
              FrontierGrammarFrame tokens)).length =
          origins.length * (tokens.length + 2) := by
      intro origins
      induction origins with
      | nil => simp
      | cons origin origins induction =>
          simp [lengthOfBoundaries, induction, Nat.add_mul,
            Nat.add_comm]
    rw [generalOrigins, lengthOfBoundaries]
  have general : ∀ productions : List ProductionId,
      (productions.flatMap fun production =>
        (allParserBoundaries tokens).flatMap fun origin =>
          (allParserBoundaries tokens).map fun current =>
            ({ production, origin, current } :
              FrontierGrammarFrame tokens)).length =
        productions.length * (tokens.length + 2) *
          (tokens.length + 2) := by
    intro productions
    induction productions with
    | nil => simp
    | cons production productions induction =>
        simp [oneProduction, induction, Nat.add_mul, Nat.mul_assoc,
          Nat.add_comm]
  exact (general allProductionIds).trans (by
    simp [frontierGrammarFrameCount, Nat.mul_assoc])

/-- Exhaustively search the finite bounded potential space for a value list
whose completion and prediction tables both accept. -/
def boundedFrontierGrammarPotential?
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {memo : GuardMemo tokens}
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo) (cursor : Boundary tokens) :
    Option (FrontierGrammarPotential tokens) :=
  let count := frontierGrammarFrameCount tokens
  let base := count + 1
  ((allBoundedNatLists count base).find? fun values =>
    let potential := frontierGrammarPotentialOfValues tokens values
    frontierCompletionRankTable owned correct final cursor potential &&
      frontierPredictionRankTable owned correct final cursor potential).map
    (frontierGrammarPotentialOfValues tokens)

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
  rcases selected with ⟨values, found, rfl⟩
  have accepted := List.find?_some found
  rw [Bool.and_eq_true] at accepted
  exact accepted

/-- Any pointwise bounded accepting potential is represented by the finite
search, so its search result is nonempty. -/
theorem boundedFrontierGrammarPotential?_isSome_of_bounded
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {memo : GuardMemo tokens}
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo) (cursor : Boundary tokens)
    (potential : FrontierGrammarPotential tokens)
    (bounded : ∀ production origin current,
      potential production origin current <
        frontierGrammarFrameCount tokens + 1)
    (completion : frontierCompletionRankTable
      owned correct final cursor potential = true)
    (prediction : frontierPredictionRankTable
      owned correct final cursor potential = true) :
    (boundedFrontierGrammarPotential?
      owned correct final cursor).isSome = true := by
  unfold boundedFrontierGrammarPotential?
  simp only [Option.isSome_map, List.find?_isSome]
  let values := frontierGrammarValuesOfPotential tokens potential
  have length : values.length = frontierGrammarFrameCount tokens := by
    simp [values, frontierGrammarValuesOfPotential,
      allFrontierGrammarFrames_length]
  have valuesBounded : ∀ value, value ∈ values →
      value < frontierGrammarFrameCount tokens + 1 := by
    intro value member
    simp only [values, frontierGrammarValuesOfPotential,
      List.mem_map] at member
    rcases member with ⟨frame, _frameMember, rfl⟩
    exact bounded frame.production frame.origin frame.current
  refine ⟨values, ?_, ?_⟩
  · simpa only [length] using
      (allBoundedNatLists_complete _ values valuesBounded)
  · rw [frontierGrammarPotentialOfValues_valuesOfPotential]
    rw [Bool.and_eq_true]
    exact ⟨completion, prediction⟩

/-- The single exact residual left by bounded potential synthesis. -/
def BoundedFrontierGrammarRankSearchSucceeds
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {memo : GuardMemo tokens}
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo) (cursor : Boundary tokens) : Prop :=
  (boundedFrontierGrammarPotential?
    owned correct final cursor).isSome = true

/-- A bounded accepting potential discharges the exact search-success
residual; no separate mixed-radix representation proof is required. -/
theorem boundedFrontierGrammarRankSearchSucceeds_of_potential
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {memo : GuardMemo tokens}
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo) (cursor : Boundary tokens)
    (potential : FrontierGrammarPotential tokens)
    (bounded : ∀ production origin current,
      potential production origin current <
        frontierGrammarFrameCount tokens + 1)
    (completion : frontierCompletionRankTable
      owned correct final cursor potential = true)
    (prediction : frontierPredictionRankTable
      owned correct final cursor potential = true) :
    BoundedFrontierGrammarRankSearchSucceeds
      owned correct final cursor :=
  boundedFrontierGrammarPotential?_isSome_of_bounded
    owned correct final cursor potential bounded completion prediction

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
