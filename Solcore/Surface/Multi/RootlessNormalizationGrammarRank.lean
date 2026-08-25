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

/-- Once a waiting item has consumed input, its predicted nonempty zero-span
child has strictly smaller coarse potential whenever nonempty zero weights fit
the production carrier.  Epsilon weights remain unconstrained so completion
may place them above positive-span continuations. -/
theorem frontierSpanPotential_predicted_lt_of_positiveSpan
    (width : Nat) (zero positive : ProductionId → Nat)
    (zeroBound : ∀ production, production.rhs ≠ [] →
      zero production < width)
    {tokens : List Token} (waiting : ContextualItemKey tokens)
    (production : ProductionId)
    (nonempty : production.rhs ≠ [])
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
  exact Nat.lt_of_lt_of_le (zeroBound production nonempty)
    (calc
      width ≤ width + (waiting.raw.origin.val * width +
          positive waiting.raw.production) := Nat.le_add_right _ _
      _ = (waiting.raw.origin.val + 1) * width +
          positive waiting.raw.production := by
        simp [Nat.add_mul, Nat.add_comm, Nat.add_left_comm])

/-- Positive-span frontier prediction decreases the full grammar rank. -/
theorem frontierGrammarRank_lt_predicted_of_positiveSpan
    (width : Nat) (zero positive : ProductionId → Nat)
    (zeroBound : ∀ production, production.rhs ≠ [] →
      zero production < width)
    {tokens : List Token} (waiting : ContextualItemKey tokens)
    (production : ProductionId)
    (nonempty : production.rhs ≠ [])
    (progress : waiting.raw.origin.val < waiting.raw.current.val) :
    frontierGrammarRank (frontierSpanPotential width zero positive)
        (FrontierPredictedItem waiting production) <
      frontierGrammarRank (frontierSpanPotential width zero positive)
        waiting := by
  apply frontierRawGrammarRank_lt_of_potential_lt
  exact frontierSpanPotential_predicted_lt_of_positiveSpan
    width zero positive zeroBound waiting production nonempty progress

/-- A concrete two-band zero-span weight. Epsilon productions occupy a band
above every input boundary; nonempty productions reuse their local positive
weight. -/
def frontierEpsilonBandZero
    (tokens : List Token) (width : Nat) (positive : ProductionId → Nat)
    (production : ProductionId) : Nat :=
  if production.rhs = [] then (tokens.length + 3) * width
  else positive production

/-- Nonempty productions in the two-band construction retain the bound used
by positive-span prediction. -/
theorem frontierEpsilonBandZero_lt_width
    {tokens : List Token} {width : Nat}
    {positive : ProductionId → Nat} {production : ProductionId}
    (nonempty : production.rhs ≠ [])
    (bounded : positive production < width) :
    frontierEpsilonBandZero tokens width positive production < width := by
  simp [frontierEpsilonBandZero, nonempty, bounded]

/-- Every frame of a nonempty caller lies below an epsilon production's
zero-span band when local positive weights fit inside one row. -/
theorem frontierSpanPotential_nonempty_lt_epsilonBand
    {tokens : List Token} (width : Nat) (positive : ProductionId → Nat)
    (parent epsilon : ProductionId)
    (parentNonempty : parent.rhs ≠ [])
    (epsilonEmpty : epsilon.rhs = [])
    (bounded : positive parent < width)
    (origin current : Boundary tokens) :
    frontierSpanPotential width
        (frontierEpsilonBandZero tokens width positive) positive
        parent origin current <
      frontierEpsilonBandZero tokens width positive epsilon := by
  have rowLe : (origin.val + 2) * width ≤
      (tokens.length + 3) * width := by
    apply Nat.mul_le_mul_right
    omega
  have widthLe : width ≤ (tokens.length + 3) * width := by
    calc
      width = 1 * width := by simp
      _ ≤ (tokens.length + 3) * width :=
        Nat.mul_le_mul_right width (by omega)
  simp only [frontierSpanPotential, frontierEpsilonBandZero,
    if_neg parentNonempty, if_pos epsilonEmpty]
  split
  · exact Nat.lt_of_lt_of_le bounded widthLe
  · exact Nat.lt_of_lt_of_le
      (calc
        (origin.val + 1) * width + positive parent <
            (origin.val + 1) * width + width :=
          Nat.add_lt_add_left bounded _
        _ = (origin.val + 2) * width := by
          simp [Nat.add_mul, Nat.add_assoc]
          omega)
      rowLe

/-- A zero-span reached item has a nullable consumed prefix for every symbol
predicate closed under the expanded productions. -/
theorem contextualReach_zeroSpan_prefix_all_of_nullableClosure
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    (nullableSymbol : GrammarSymbol → Bool)
    (closed : ∀ production : ProductionId,
      (production.rhs.all nullableSymbol = true) →
        nullableSymbol (.nonterminal production.lhs) = true)
    {item : ContextualItemKey tokens}
    (reached : ContextualReach file tokens memo correct final item)
    (zeroSpan : item.raw.origin = item.raw.current) :
    (item.raw.production.rhs.take item.raw.dot.val).all
        nullableSymbol = true := by
  induction reached with
  | root => rfl
  | predict => rfl
  | scan before after cursor beforeReached structural induction =>
      rcases structural.1 with
        ⟨terminal, value, span, next, atCurrent, terminalAt,
          terminalMatches, advance⟩
      rcases advance with
        ⟨productionEq, dotEq, originEq, currentEq⟩
      have ordered := contextualReach_ordered beforeReached
      have zeroValues := congrArg Fin.val zeroSpan
      have beforeCurrentValues : before.raw.current.val = cursor.val := by
        rw [← atCurrent]
        rfl
      have originValues := congrArg Fin.val originEq
      have afterCurrentValues : after.raw.current.val = cursor.val + 1 := by
        rw [currentEq]
        rfl
      omega
  | complete waiting finished after shared waitingReached finishedReached
      structural waitingInduction finishedInduction =>
      rcases structural.1 with
        ⟨symbol, next, complete, lhsEq, waitingAtShared,
          finishedAtShared, advance⟩
      have waitingOrdered := contextualReach_ordered waitingReached
      have finishedOrdered := contextualReach_ordered finishedReached
      rcases advance with
        ⟨productionEq, dotEq, originEq, currentEq⟩
      have zeroValues := congrArg Fin.val zeroSpan
      have waitingAtValues := congrArg Fin.val waitingAtShared
      have finishedAtValues := congrArg Fin.val finishedAtShared
      have originValues := congrArg Fin.val originEq
      have currentValues := congrArg Fin.val currentEq
      have waitingZero : waiting.raw.origin = waiting.raw.current := by
        apply Fin.ext
        omega
      have finishedZero : finished.raw.origin = finished.raw.current := by
        apply Fin.ext
        omega
      have waitingNullable := waitingInduction waitingZero
      have finishedNullable := finishedInduction finishedZero
      rw [prefix_full_layout finished.raw complete] at finishedNullable
      have childNullable :
          nullableSymbol (.nonterminal finished.raw.production.lhs) = true :=
        closed finished.raw.production finishedNullable
      have exactNext : NextSymbol waiting.raw
          (.nonterminal finished.raw.production.lhs) := by
        rw [lhsEq]
        exact next
      have layout := prefix_complete_layout waiting.raw finished.raw
        after.raw exactNext ⟨productionEq, dotEq, originEq, currentEq⟩
      rw [← layout, List.all_append]
      simp only [waitingNullable, List.all_cons, childNullable,
        List.all_nil, Bool.and_true]

/-- A reached item whose consumed prefix is statically nonnullable must have
made strict source progress. -/
theorem contextualReach_origin_lt_current_of_prefix_not_all
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    (nullableSymbol : GrammarSymbol → Bool)
    (closed : ∀ production : ProductionId,
      (production.rhs.all nullableSymbol = true) →
        nullableSymbol (.nonterminal production.lhs) = true)
    {item : ContextualItemKey tokens}
    (reached : ContextualReach file tokens memo correct final item)
    (nonnullable :
      (item.raw.production.rhs.take item.raw.dot.val).all
          nullableSymbol ≠ true) :
    item.raw.origin.val < item.raw.current.val := by
  apply Nat.lt_of_le_of_ne (contextualReach_ordered reached)
  intro equalValues
  apply nonnullable
  exact contextualReach_zeroSpan_prefix_all_of_nullableClosure
    nullableSymbol closed reached (Fin.ext equalValues)

/-- One reached caller that introduced a contextual production instance. -/
def ContextualActivationParent
    (file : WorkspaceFile) (tokens : List Token)
    (memo : GuardMemo tokens)
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo)
    (parent child : ContextualItemKey tokens) : Prop :=
  ContextualReach file tokens memo correct final parent ∧
    NextSymbol parent.raw (.nonterminal child.raw.production.lhs) ∧
    parent.raw.current = child.raw.origin ∧
    child.context = descendContext parent child.raw.production

/-- Every reached item either belongs to the top-level module activation or
retains a reached caller. Scans and completions preserve that caller. -/
theorem contextualReach_rootOrActivationParent
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {item : ContextualItemKey tokens}
    (reached : ContextualReach file tokens memo correct final item) :
    (item.raw.production = .root .module ∧
      item.raw.origin = Boundary.start tokens ∧
      item.context = .plain) ∨
    ∃ parent, ContextualActivationParent
      file tokens memo correct final parent item := by
  induction reached with
  | root => exact Or.inl ⟨rfl, rfl, rfl⟩
  | predict waiting predicted reached next enabled induction =>
      exact Or.inr ⟨waiting, reached, next, rfl, rfl⟩
  | scan before after cursor reached structural induction =>
      rcases structural with ⟨valid, context⟩
      rcases valid with
        ⟨terminal, value, span, next, atCurrent, terminalAt,
          terminalMatches, advance⟩
      rcases advance with ⟨production, dot, origin, current⟩
      simpa only [ContextualActivationParent, production, origin,
        ← context] using induction
  | complete waiting finished after shared waitingReached finishedReached
      structural waitingInduction finishedInduction =>
      rcases structural with ⟨valid, finishedContext, afterContext⟩
      rcases valid with
        ⟨symbol, next, complete, lhs, waitingAt, finishedAt, advance⟩
      rcases advance with ⟨production, dot, origin, current⟩
      simpa only [ContextualActivationParent, production, origin,
        afterContext] using waitingInduction

/-- A reached module-root item always retains the initial source origin. -/
theorem contextualReach_moduleRoot_origin
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {item : ContextualItemKey tokens}
    (reached : ContextualReach file tokens memo correct final item)
    (production : item.raw.production = .root .module) :
    item.raw.origin = Boundary.start tokens := by
  rcases contextualReach_rootOrActivationParent reached with
    root | ⟨parent, activated⟩
  · exact root.2.1
  · have selected :
        parent.raw.production.rhs[parent.raw.dot.val]? =
          some (.nonterminal (.rule .module)) := by
      calc
        _ = some (.nonterminal item.raw.production.lhs) :=
          activated.2.1.2
        _ = _ := by rw [production]; rfl
    exact (ProductionId.rhs_no_moduleRule parent.raw.production
      (List.mem_of_getElem? selected)).elim

private theorem contextual_moduleEofAtom_complete_current
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {item : ContextualItemKey tokens}
    (reached : ContextualReach file tokens memo correct final item)
    (production : item.raw.production = .atom moduleEofAtomSite)
    (complete : CompleteItem item.raw) :
    item.raw.current = Boundary.afterLogicalEOF tokens := by
  induction reached with
  | root => contradiction
  | predict waiting predicted reached next enabled induction =>
      change predicted = .atom moduleEofAtomSite at production
      subst predicted
      simp [CompleteItem] at complete
  | scan before after cursor reached structural induction =>
      rcases structural.1 with
        ⟨terminal, value, span, next, atCurrent, terminalAt,
          terminalMatches, advance⟩
      have beforeProduction : before.raw.production =
          .atom moduleEofAtomSite := advance.1.symm.trans production
      have afterRhs : after.raw.production.rhs = [.terminal .endOfFile] :=
        (congrArg ProductionId.rhs production).trans
          ProductionId.rhs_moduleEofAtom
      have afterDot : after.raw.dot.val = 1 := by
        unfold CompleteItem at complete
        exact complete.trans (congrArg List.length afterRhs)
      have beforeDot : before.raw.dot.val = 0 := by
        rw [advance.2.1] at afterDot
        omega
      have terminalEq : terminal = .endOfFile := by
        have beforeRhs : before.raw.production.rhs =
            [.terminal .endOfFile] :=
          (congrArg ProductionId.rhs beforeProduction).trans
            ProductionId.rhs_moduleEofAtom
        have selected : before.raw.production.rhs[0]? =
            some (.terminal terminal) := by
          simpa [beforeDot] using next.2
        have lookupEq : before.raw.production.rhs[0]? =
            ([.terminal .endOfFile] : List GrammarSymbol)[0]? :=
          congrArg (fun rhs : List GrammarSymbol => rhs[0]?) beforeRhs
        rw [lookupEq] at selected
        simpa using (Option.some.inj selected).symm
      subst terminal
      cases value with
      | retained token => simp [TerminalMatches] at terminalMatches
      | endOfFile =>
          cases terminalAt with
          | endOfFile atEnd =>
              apply Fin.ext
              rw [advance.2.2.2]
              change cursor.val + 1 = tokens.length + 1
              omega
  | complete waiting finished after shared waitingReached finishedReached
      structural waitingInduction finishedInduction =>
      rcases structural.1 with
        ⟨symbol, next, childComplete, lhsEq, waitingAtShared,
          finishedAtShared, advance⟩
      have waitingProduction : waiting.raw.production =
          .atom moduleEofAtomSite := advance.1.symm.trans production
      have waitingRhs : waiting.raw.production.rhs =
          [.terminal .endOfFile] :=
        (congrArg ProductionId.rhs waitingProduction).trans
          ProductionId.rhs_moduleEofAtom
      have bound : waiting.raw.dot.val < 1 := by
        calc
          waiting.raw.dot.val < waiting.raw.production.rhs.length := next.1
          _ = 1 := congrArg List.length waitingRhs
      have dotZero : waiting.raw.dot.val = 0 := by omega
      have impossible : waiting.raw.production.rhs[0]? =
          some (.nonterminal symbol) := by
        simpa [dotZero] using next.2
      have lookupEq : waiting.raw.production.rhs[0]? =
          ([.terminal .endOfFile] : List GrammarSymbol)[0]? :=
        congrArg (fun rhs : List GrammarSymbol => rhs[0]?) waitingRhs
      rw [lookupEq] at impossible
      simp at impossible

private theorem contextual_moduleRootSequence_complete_current
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {item : ContextualItemKey tokens}
    (reached : ContextualReach file tokens memo correct final item)
    (production : item.raw.production = .seq moduleRootSequenceSite)
    (complete : CompleteItem item.raw) :
    item.raw.current = Boundary.afterLogicalEOF tokens := by
  induction reached with
  | root => contradiction
  | predict waiting predicted reached next enabled induction =>
      change predicted = .seq moduleRootSequenceSite at production
      subst predicted
      unfold CompleteItem at complete
      change 0 = (ProductionId.seq moduleRootSequenceSite).rhs.length
        at complete
      have rhsLength :
          (ProductionId.seq moduleRootSequenceSite).rhs.length = 2 :=
        congrArg List.length ProductionId.rhs_moduleRootSequence
      omega
  | scan before after cursor reached structural induction =>
      rcases structural.1 with
        ⟨terminal, value, span, next, atCurrent, terminalAt,
          terminalMatches, advance⟩
      have waitingProduction : before.raw.production =
          .seq moduleRootSequenceSite := advance.1.symm.trans production
      have waitingRhs :=
        (congrArg ProductionId.rhs waitingProduction).trans
          ProductionId.rhs_moduleRootSequence
      have afterRhs :=
        (congrArg ProductionId.rhs production).trans
          ProductionId.rhs_moduleRootSequence
      have afterDot : after.raw.dot.val = 2 := by
        unfold CompleteItem at complete
        exact complete.trans (congrArg List.length afterRhs)
      have beforeDot : before.raw.dot.val = 1 := by
        rw [advance.2.1] at afterDot
        omega
      have impossible : before.raw.production.rhs[1]? =
          some (.terminal terminal) := by
        simpa [beforeDot] using next.2
      rw [congrArg (fun rhs : List GrammarSymbol => rhs[1]?) waitingRhs]
        at impossible
      simp at impossible
  | complete waiting finished after shared waitingReached finishedReached
      structural waitingInduction finishedInduction =>
      rcases structural.1 with
        ⟨symbol, next, childComplete, lhsEq, waitingAtShared,
          finishedAtShared, advance⟩
      have waitingProduction : waiting.raw.production =
          .seq moduleRootSequenceSite := advance.1.symm.trans production
      have waitingRhs :=
        (congrArg ProductionId.rhs waitingProduction).trans
          ProductionId.rhs_moduleRootSequence
      have afterRhs :=
        (congrArg ProductionId.rhs production).trans
          ProductionId.rhs_moduleRootSequence
      have afterDot : after.raw.dot.val = 2 := by
        unfold CompleteItem at complete
        exact complete.trans (congrArg List.length afterRhs)
      have waitingDot : waiting.raw.dot.val = 1 := by
        rw [advance.2.1] at afterDot
        omega
      have selected : waiting.raw.production.rhs[1]? =
          some (.nonterminal symbol) := by
        simpa [waitingDot] using next.2
      rw [congrArg (fun rhs : List GrammarSymbol => rhs[1]?) waitingRhs]
        at selected
      have symbolEq : symbol = .aux moduleEofGrammarSite := by
        simpa using (Option.some.inj selected).symm
      have finishedProduction : finished.raw.production =
          .atom moduleEofAtomSite :=
        ProductionId.eq_moduleEofAtom_of_lhs finished.raw.production
          (lhsEq.trans symbolEq)
      exact advance.2.2.2.trans
        (contextual_moduleEofAtom_complete_current finishedReached
          finishedProduction childComplete)

/-- A reached complete module root spans exactly the whole logical token
stream. -/
theorem contextualReach_completeModule_interval
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {item : ContextualItemKey tokens}
    (reached : ContextualReach file tokens memo correct final item)
    (production : item.raw.production = .root .module)
    (complete : CompleteItem item.raw) :
    item.raw.origin = Boundary.start tokens ∧
      item.raw.current = Boundary.afterLogicalEOF tokens := by
  refine ⟨contextualReach_moduleRoot_origin reached production, ?_⟩
  induction reached with
  | root => simp [CompleteItem, ProductionId.rhs] at complete
  | predict waiting predicted reached next enabled induction =>
      change predicted = .root .module at production
      subst predicted
      simp [CompleteItem, ProductionId.rhs] at complete
  | scan before after cursor reached structural induction =>
      rcases structural.1 with
        ⟨terminal, value, span, next, atCurrent, terminalAt,
          terminalMatches, advance⟩
      have beforeProduction : before.raw.production = .root .module :=
        advance.1.symm.trans production
      have afterDot : after.raw.dot.val = 1 := by
        unfold CompleteItem at complete
        simpa [production, ProductionId.rhs] using complete
      have beforeDot : before.raw.dot.val = 0 := by
        rw [advance.2.1] at afterDot
        omega
      have impossible : before.raw.production.rhs[0]? =
          some (.terminal terminal) := by
        simpa [beforeDot] using next.2
      have lookupEq : before.raw.production.rhs[0]? =
          (ProductionId.root .module).rhs[0]? :=
        congrArg (fun selected : ProductionId => selected.rhs[0]?)
          beforeProduction
      rw [lookupEq] at impossible
      simp [ProductionId.rhs] at impossible
  | complete waiting finished after shared waitingReached finishedReached
      structural waitingInduction finishedInduction =>
      rcases structural.1 with
        ⟨symbol, next, childComplete, lhsEq, waitingAtShared,
          finishedAtShared, advance⟩
      have waitingProduction : waiting.raw.production = .root .module :=
        advance.1.symm.trans production
      have afterDot : after.raw.dot.val = 1 := by
        unfold CompleteItem at complete
        simpa [production, ProductionId.rhs] using complete
      have waitingDot : waiting.raw.dot.val = 0 := by
        rw [advance.2.1] at afterDot
        omega
      have selected : waiting.raw.production.rhs[0]? =
          some (.nonterminal symbol) := by
        simpa [waitingDot] using next.2
      have lookupEq : waiting.raw.production.rhs[0]? =
          (ProductionId.root .module).rhs[0]? :=
        congrArg (fun selected : ProductionId => selected.rhs[0]?)
          waitingProduction
      rw [lookupEq] at selected
      have symbolEq : symbol = .aux (GrammarSite.root .module) := by
        simpa [ProductionId.rhs] using
          (Option.some.inj selected).symm
      have finishedProduction := ProductionId.eq_moduleRootSequence_of_lhs
        finished.raw.production (lhsEq.trans symbolEq)
      exact advance.2.2.2.trans
        (contextual_moduleRootSequence_complete_current finishedReached
          finishedProduction childComplete)

/-- A reached module-root item always retains the plain guard context. -/
theorem contextualReach_moduleRoot_context
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {item : ContextualItemKey tokens}
    (reached : ContextualReach file tokens memo correct final item)
    (production : item.raw.production = .root .module) :
    item.context = .plain := by
  rcases contextualReach_rootOrActivationParent reached with
    root | ⟨parent, activated⟩
  · exact root.2.2
  · have selected :
        parent.raw.production.rhs[parent.raw.dot.val]? =
          some (.nonterminal (.rule .module)) := by
      calc
        _ = some (.nonterminal item.raw.production.lhs) :=
          activated.2.1.2
        _ = _ := by rw [production]; rfl
    exact (ProductionId.rhs_no_moduleRule parent.raw.production
      (List.mem_of_getElem? selected)).elim

/-- Every reached complete module root is the canonical whole-file root key. -/
theorem contextualReach_completeModule_eq_canonical
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {item : ContextualItemKey tokens}
    (reached : ContextualReach file tokens memo correct final item)
    (production : item.raw.production = .root .module)
    (complete : CompleteItem item.raw) :
    item = CanonicalCompleteRootItem tokens .module
      (Boundary.start tokens) (Boundary.afterLogicalEOF tokens) .plain := by
  have interval := contextualReach_completeModule_interval
    reached production complete
  have context := contextualReach_moduleRoot_context reached production
  cases item with
  | mk raw itemContext =>
      cases raw with
      | mk itemProduction itemDot itemOrigin itemCurrent =>
          dsimp only at production complete interval context ⊢
          subst itemProduction
          rcases interval with ⟨originEq, currentEq⟩
          cases originEq
          cases currentEq
          cases context
          have dotEq : itemDot = {
              val := (ProductionId.root .module).rhs.length
              isLt := Nat.lt_succ_self _
            } := Fin.ext complete
          cases dotEq
          rfl

/-- An epsilon production cannot move its cursor after prediction. -/
theorem contextualReach_epsilon_current_eq_origin
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {item : ContextualItemKey tokens}
    (reached : ContextualReach file tokens memo correct final item)
    (epsilon : item.raw.production.rhs = []) :
    item.raw.current = item.raw.origin := by
  induction reached with
  | root => simp [ProductionId.rhs] at epsilon
  | predict => rfl
  | scan before after cursor reached structural induction =>
      rcases structural.1 with
        ⟨terminal, value, span, next, atCurrent, terminalAt,
          terminalMatches, advance⟩
      have beforeEpsilon : before.raw.production.rhs = [] :=
        (congrArg ProductionId.rhs advance.1).symm.trans epsilon
      have zeroLength : before.raw.production.rhs.length = 0 :=
        congrArg List.length beforeEpsilon
      have bound := next.1
      have positiveLength : 0 < before.raw.production.rhs.length :=
        Nat.lt_of_le_of_lt (Nat.zero_le _) bound
      omega
  | complete waiting finished after shared waitingReached finishedReached
      structural waitingInduction finishedInduction =>
      rcases structural.1 with
        ⟨symbol, next, finishedComplete, lhs, waitingAt, finishedAt,
          advance⟩
      have waitingEpsilon : waiting.raw.production.rhs = [] :=
        (congrArg ProductionId.rhs advance.1).symm.trans epsilon
      have zeroLength : waiting.raw.production.rhs.length = 0 :=
        congrArg List.length waitingEpsilon
      have bound := next.1
      have positiveLength : 0 < waiting.raw.production.rhs.length :=
        Nat.lt_of_le_of_lt (Nat.zero_le _) bound
      omega

/-- Completing a reached non-root instance materializes its caller's
continuation at the same frontier. -/
theorem frontierReach_continuation_of_complete_nonroot
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {cursor : Boundary tokens} {finished : ContextualItemKey tokens}
    (frontier : FrontierReach
      file tokens memo correct final cursor finished)
    (complete : CompleteItem finished.raw)
    (nonroot : finished.raw.production ≠ .root .module) :
    ∃ parent after : ContextualItemKey tokens,
      ContextualActivationParent
        file tokens memo correct final parent finished ∧
      FrontierReach file tokens memo correct final cursor after ∧
      AdvanceItem parent.raw finished.raw.current after.raw := by
  rcases contextualReach_rootOrActivationParent frontier.2.1 with
      root | ⟨parent, activated⟩
  · exact (nonroot root.1).elim
  · let after : ContextualItemKey tokens := {
      raw := {
        production := parent.raw.production
        dot := ⟨parent.raw.dot.val + 1,
          Nat.succ_lt_succ activated.2.1.1⟩
        origin := parent.raw.origin
        current := finished.raw.current
      }
      context := parent.context
    }
    have advance :
        AdvanceItem parent.raw finished.raw.current after.raw := by
      exact ⟨rfl, rfl, rfl, rfl⟩
    have structural : ContextualPackedEdgeKey.StructurallyValid file tokens
        (.completed parent finished after parent.raw.current) := by
      constructor
      · exact ⟨finished.raw.production.lhs, activated.2.1, complete,
          rfl, rfl, activated.2.2.1.symm, advance⟩
      · exact ⟨activated.2.2.2, rfl⟩
    have afterReached :
        ContextualReach file tokens memo correct final after := by
      exact .complete parent finished after parent.raw.current
        activated.1 frontier.2.1 structural
    refine ⟨parent, after, activated, ⟨frontier.1, afterReached, ?_⟩,
      advance⟩
    exact advance.2.2.2.trans frontier.2.2

/-- A completed epsilon instance always hands control back to a lower caller
frame under the concrete two-band potential. -/
theorem frontierGrammarRank_continuation_lt_of_complete_epsilonBand
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {cursor : Boundary tokens} {finished : ContextualItemKey tokens}
    (width : Nat) (positive : ProductionId → Nat)
    (positiveBound : ∀ production, production.rhs ≠ [] →
      positive production < width)
    (frontier : FrontierReach
      file tokens memo correct final cursor finished)
    (complete : CompleteItem finished.raw)
    (epsilon : finished.raw.production.rhs = []) :
    ∃ after : ContextualItemKey tokens,
      FrontierReach file tokens memo correct final cursor after ∧
      frontierGrammarRank
          (frontierSpanPotential width
            (frontierEpsilonBandZero tokens width positive) positive)
          after <
        frontierGrammarRank
          (frontierSpanPotential width
            (frontierEpsilonBandZero tokens width positive) positive)
          finished := by
  have nonroot : finished.raw.production ≠ .root .module := by
    intro root
    rw [root] at epsilon
    simp [ProductionId.rhs] at epsilon
  rcases frontierReach_continuation_of_complete_nonroot
      frontier complete nonroot with
    ⟨parent, after, activated, afterFrontier, advance⟩
  have parentNonempty : parent.raw.production.rhs ≠ [] := by
    intro parentEmpty
    have zeroLength : parent.raw.production.rhs.length = 0 :=
      congrArg List.length parentEmpty
    have bound := activated.2.1.1
    have positiveLength : 0 < parent.raw.production.rhs.length :=
      Nat.lt_of_le_of_lt (Nat.zero_le _) bound
    omega
  have finishedAtOrigin :
      finished.raw.current = finished.raw.origin :=
    contextualReach_epsilon_current_eq_origin frontier.2.1 epsilon
  refine ⟨after, afterFrontier, ?_⟩
  apply frontierRawGrammarRank_lt_of_potential_lt
  have parentBelow := frontierSpanPotential_nonempty_lt_epsilonBand
    width positive parent.raw.production finished.raw.production
    parentNonempty epsilon (positiveBound _ parentNonempty)
    parent.raw.origin finished.raw.current
  rcases advance with ⟨production, dot, origin, current⟩
  simp only [production, origin, current, frontierSpanPotential,
    if_pos finishedAtOrigin.symm]
  exact parentBelow
/-- An activation caller starts no later than the child that it introduced. -/
theorem contextualActivationParent_origin_le
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {parent child : ContextualItemKey tokens}
    (activated : ContextualActivationParent
      file tokens memo correct final parent child) :
    parent.raw.origin.val ≤ child.raw.origin.val := by
  have ordered := contextualReach_ordered activated.1
  rw [activated.2.2.1] at ordered
  exact ordered

/-- Returning to a caller from a strictly later child-origin decreases the
span row, independently of the productions' relative local weights. -/
theorem frontierSpanPotential_continuation_lt_of_earlierOrigin
    {tokens : List Token}
    (width : Nat) (zero positive : ProductionId → Nat)
    (parent finished after : ContextualItemKey tokens)
    (bounded : positive parent.raw.production < width)
    (progress : finished.raw.origin.val < finished.raw.current.val)
    (earlier : parent.raw.origin.val < finished.raw.origin.val)
    (advance : AdvanceItem parent.raw finished.raw.current after.raw) :
    frontierSpanPotential width zero positive after.raw.production
        after.raw.origin after.raw.current <
      frontierSpanPotential width zero positive finished.raw.production
        finished.raw.origin finished.raw.current := by
  have afterDifferent : parent.raw.origin ≠ finished.raw.current := by
    intro equal
    have valueEqual := congrArg Fin.val equal
    omega
  have finishedDifferent :
      finished.raw.origin ≠ finished.raw.current := by
    intro equal
    have valueEqual := congrArg Fin.val equal
    omega
  have rows : (parent.raw.origin.val + 2) * width ≤
      (finished.raw.origin.val + 1) * width := by
    apply Nat.mul_le_mul_right
    omega
  rcases advance with ⟨production, dot, origin, current⟩
  simp only [production, origin, current, frontierSpanPotential,
    if_neg afterDifferent, if_neg finishedDifferent]
  calc
    (parent.raw.origin.val + 1) * width +
          positive parent.raw.production <
        (parent.raw.origin.val + 1) * width + width :=
      Nat.add_lt_add_left bounded _
    _ = (parent.raw.origin.val + 2) * width := by
      simp [Nat.add_mul, Nat.add_assoc]
      omega
    _ ≤ (finished.raw.origin.val + 1) * width := rows
    _ ≤ (finished.raw.origin.val + 1) * width +
          positive finished.raw.production := Nat.le_add_right _ _

/-- When caller and completed child share an origin, their local positive
weights are exactly the remaining coarse comparison. -/
theorem frontierSpanPotential_continuation_lt_of_equalOrigin
    {tokens : List Token}
    (width : Nat) (zero positive : ProductionId → Nat)
    (parent finished after : ContextualItemKey tokens)
    (progress : finished.raw.origin.val < finished.raw.current.val)
    (sameOrigin : parent.raw.origin = finished.raw.origin)
    (decreases : positive parent.raw.production <
      positive finished.raw.production)
    (advance : AdvanceItem parent.raw finished.raw.current after.raw) :
    frontierSpanPotential width zero positive after.raw.production
        after.raw.origin after.raw.current <
      frontierSpanPotential width zero positive finished.raw.production
        finished.raw.origin finished.raw.current := by
  have finishedDifferent :
      finished.raw.origin ≠ finished.raw.current := by
    intro equal
    have valueEqual := congrArg Fin.val equal
    omega
  rcases advance with ⟨production, dot, origin, current⟩
  simp only [production, origin, current, frontierSpanPotential,
    if_neg finishedDifferent, sameOrigin]
  exact Nat.add_lt_add_left decreases _

/-- Positive-span completion reduces to a finite same-origin production
comparison; strictly earlier callers are discharged by the span rows. -/
theorem frontierGrammarRank_continuation_lt_of_complete_positiveSpan
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {cursor : Boundary tokens} {finished : ContextualItemKey tokens}
    (width : Nat) (zero positive : ProductionId → Nat)
    (positiveBound : ∀ production, positive production < width)
    (frontier : FrontierReach
      file tokens memo correct final cursor finished)
    (complete : CompleteItem finished.raw)
    (nonroot : finished.raw.production ≠ .root .module)
    (progress : finished.raw.origin.val < finished.raw.current.val)
    (sameOriginDecreases : ∀ parent,
      ContextualActivationParent
        file tokens memo correct final parent finished →
      parent.raw.origin = finished.raw.origin →
      positive parent.raw.production < positive finished.raw.production) :
    ∃ after : ContextualItemKey tokens,
      FrontierReach file tokens memo correct final cursor after ∧
      frontierGrammarRank (frontierSpanPotential width zero positive) after <
        frontierGrammarRank (frontierSpanPotential width zero positive)
          finished := by
  rcases frontierReach_continuation_of_complete_nonroot
      frontier complete nonroot with
    ⟨parent, after, activated, afterFrontier, advance⟩
  refine ⟨after, afterFrontier, ?_⟩
  apply frontierRawGrammarRank_lt_of_potential_lt
  have ordered := contextualActivationParent_origin_le activated
  by_cases earlier :
      parent.raw.origin.val < finished.raw.origin.val
  · exact frontierSpanPotential_continuation_lt_of_earlierOrigin
      width zero positive parent finished after
      (positiveBound _) progress earlier advance
  · have valueEqual : parent.raw.origin.val =
        finished.raw.origin.val := by omega
    have sameOrigin : parent.raw.origin = finished.raw.origin :=
      Fin.ext valueEqual
    exact frontierSpanPotential_continuation_lt_of_equalOrigin
      width zero positive parent finished after progress sameOrigin
      (sameOriginDecreases parent activated sameOrigin) advance

/-- One exact same-origin completion cell. Only reached completed frontier
children and their activation callers impose a local production-weight edge. -/
def frontierSameOriginCompletionRankCell
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {memo : GuardMemo tokens}
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo) (cursor : Boundary tokens)
    (positive : ProductionId → Nat)
    (finished parent : ContextualItemKey tokens) : Bool :=
  letI : Decidable
      (ContextualReach file tokens memo correct final finished) :=
    contextualReachDecision owned correct final finished
  letI : Decidable
      (ContextualReach file tokens memo correct final parent) :=
    contextualReachDecision owned correct final parent
  letI : Decidable
      (NextSymbol parent.raw
        (.nonterminal finished.raw.production.lhs)) :=
    by unfold NextSymbol; exact inferInstance
  letI : Decidable (CompleteItem finished.raw) := by
    unfold CompleteItem
    exact inferInstance
  letI : Decidable (ContextualActivationParent
      file tokens memo correct final parent finished) := by
    unfold ContextualActivationParent
    exact inferInstance
  if ContextualReach file tokens memo correct final finished then
    if finished.raw.current = cursor then
      if CompleteItem finished.raw then
        if ContextualActivationParent
            file tokens memo correct final parent finished then
          if parent.raw.origin = finished.raw.origin then
            decide (positive parent.raw.production <
              positive finished.raw.production)
          else true
        else true
      else true
    else true
  else true

/-- Finite exact dependency graph for same-origin completion on one
frontier. -/
def frontierSameOriginCompletionRankTable
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {memo : GuardMemo tokens}
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo) (cursor : Boundary tokens)
    (positive : ProductionId → Nat) : Bool :=
  (allContextualItems tokens).all fun finished =>
    (allContextualItems tokens).all fun parent =>
      frontierSameOriginCompletionRankCell
        owned correct final cursor positive finished parent

/-- An accepted same-origin completion table supplies every selected local
production-weight edge. -/
theorem frontierSameOriginCompletionRank_lt_of_table
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {memo : GuardMemo tokens}
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo) (cursor : Boundary tokens)
    (positive : ProductionId → Nat)
    (checked : frontierSameOriginCompletionRankTable
      owned correct final cursor positive = true)
    (finished parent : ContextualItemKey tokens)
    (reached : ContextualReach file tokens memo correct final finished)
    (current : finished.raw.current = cursor)
    (complete : CompleteItem finished.raw)
    (activated : ContextualActivationParent
      file tokens memo correct final parent finished)
    (sameOrigin : parent.raw.origin = finished.raw.origin) :
    positive parent.raw.production < positive finished.raw.production := by
  have row := (List.all_eq_true.mp checked) finished
    (allContextualItems_complete finished)
  have cell := (List.all_eq_true.mp row) parent
    (allContextualItems_complete parent)
  letI : Decidable
      (ContextualReach file tokens memo correct final finished) :=
    contextualReachDecision owned correct final finished
  letI : Decidable
      (ContextualReach file tokens memo correct final parent) :=
    contextualReachDecision owned correct final parent
  letI : Decidable
      (NextSymbol parent.raw
        (.nonterminal finished.raw.production.lhs)) :=
    by unfold NextSymbol; exact inferInstance
  letI : Decidable (CompleteItem finished.raw) := by
    unfold CompleteItem
    exact inferInstance
  letI : Decidable (ContextualActivationParent
      file tokens memo correct final parent finished) := by
    unfold ContextualActivationParent
    exact inferInstance
  simp only [frontierSameOriginCompletionRankCell] at cell
  rw [if_pos reached, if_pos current, if_pos complete,
    if_pos activated, if_pos sameOrigin] at cell
  exact decide_eq_true_iff.mp cell

/-- A checked finite same-origin graph discharges every positive-span
completion continuation. -/
theorem frontierGrammarRank_continuation_lt_of_positiveSpanTable
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {memo : GuardMemo tokens}
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo)
    (cursor : Boundary tokens) (finished : ContextualItemKey tokens)
    (width : Nat) (zero positive : ProductionId → Nat)
    (positiveBound : ∀ production, positive production < width)
    (checked : frontierSameOriginCompletionRankTable
      owned correct final cursor positive = true)
    (frontier : FrontierReach
      file tokens memo correct final cursor finished)
    (complete : CompleteItem finished.raw)
    (nonroot : finished.raw.production ≠ .root .module)
    (progress : finished.raw.origin.val < finished.raw.current.val) :
    ∃ after : ContextualItemKey tokens,
      FrontierReach file tokens memo correct final cursor after ∧
      frontierGrammarRank (frontierSpanPotential width zero positive) after <
        frontierGrammarRank (frontierSpanPotential width zero positive)
          finished := by
  apply frontierGrammarRank_continuation_lt_of_complete_positiveSpan
    width zero positive positiveBound frontier complete nonroot progress
  intro parent activated sameOrigin
  exact frontierSameOriginCompletionRank_lt_of_table
    owned correct final cursor positive checked finished parent
    frontier.2.1 frontier.2.2 complete activated sameOrigin



/-- Boundary-free rank of one dotted production in the zero-span mode. -/
def frontierZeroSpanGrammarRank
    (zero : ProductionId → Nat) (dotted : DottedRhs) : Nat :=
  (D + 1) * zero dotted.production +
    (dotted.production.rhs.length - dotted.dot.val)

/-- The canonical dot-zero child of one boundary-free prediction cell. -/
def frontierZeroSpanPredictedDotted
    (production : ProductionId) : DottedRhs := {
  production := production
  dot := ⟨0, Nat.zero_lt_succ _⟩
}

/-- One admissible zero-span grammar edge checks strict prediction descent. -/
def frontierZeroSpanPredictionRankCell
    (admissible : DottedRhs → Bool) (zero : ProductionId → Nat)
    (waiting : DottedRhs) (production : ProductionId) : Bool :=
  if admissible waiting then
    if waiting.production.rhs[waiting.dot.val]? =
        some (.nonterminal production.lhs) then
      if production.rhs ≠ [] then
        decide (frontierZeroSpanGrammarRank zero
            (frontierZeroSpanPredictedDotted production) <
          frontierZeroSpanGrammarRank zero waiting)
      else true
    else true
  else true

/-- Finite zero-span dependency table over dotted productions. -/
def frontierZeroSpanPredictionRankTable
    (admissible : DottedRhs → Bool)
    (zero : ProductionId → Nat) : Bool :=
  allDottedRhs.all fun waiting =>
    allProductionIds.all fun production =>
      frontierZeroSpanPredictionRankCell admissible zero waiting production

/-- An accepted zero-span table supplies every selected admissible edge. -/
theorem frontierZeroSpanPredictionRank_lt_of_table
    (admissible : DottedRhs → Bool) (zero : ProductionId → Nat)
    (checked : frontierZeroSpanPredictionRankTable admissible zero = true)
    (waiting : DottedRhs) (production : ProductionId)
    (waitingAdmissible : admissible waiting = true)
    (next : waiting.production.rhs[waiting.dot.val]? =
      some (.nonterminal production.lhs))
    (nonempty : production.rhs ≠ []) :
    frontierZeroSpanGrammarRank zero
        (frontierZeroSpanPredictedDotted production) <
      frontierZeroSpanGrammarRank zero waiting := by
  have row := (List.all_eq_true.mp checked) waiting
    (allDottedRhs_complete waiting)
  have cell := (List.all_eq_true.mp row) production
    (allProductionIds_complete production)
  simp only [frontierZeroSpanPredictionRankCell] at cell
  rw [if_pos waitingAdmissible, if_pos next, if_pos nonempty] at cell
  exact decide_eq_true_iff.mp cell

/-- Exact finite membership test for dotted shapes represented by a reached
zero-span item on the selected frontier. -/
def frontierReachedZeroSpanDottedBool
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {memo : GuardMemo tokens}
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo) (cursor : Boundary tokens)
    (dotted : DottedRhs) : Bool :=
  (allContextualItems tokens).any fun waiting =>
    letI : Decidable
        (ContextualReach file tokens memo correct final waiting) :=
      contextualReachDecision owned correct final waiting
    decide (ContextualReach file tokens memo correct final waiting) &&
      decide (waiting.raw.current = cursor) &&
      decide (waiting.raw.origin = waiting.raw.current) &&
      decide ((⟨waiting.raw.production, waiting.raw.dot⟩ : DottedRhs) = dotted)

/-- Every reached zero-span frontier item activates its exact dotted shape. -/
theorem frontierReachedZeroSpanDottedBool_eq_true_of_reached
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {memo : GuardMemo tokens}
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo) (cursor : Boundary tokens)
    (waiting : ContextualItemKey tokens)
    (reached : ContextualReach file tokens memo correct final waiting)
    (current : waiting.raw.current = cursor)
    (atOrigin : waiting.raw.origin = waiting.raw.current) :
    frontierReachedZeroSpanDottedBool owned correct final cursor
      ⟨waiting.raw.production, waiting.raw.dot⟩ = true := by
  unfold frontierReachedZeroSpanDottedBool
  apply List.any_eq_true.mpr
  refine ⟨waiting, allContextualItems_complete waiting, ?_⟩
  letI : Decidable
      (ContextualReach file tokens memo correct final waiting) :=
    contextualReachDecision owned correct final waiting
  simp [reached, current, atOrigin]
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
    (zeroBound : ∀ production, production.rhs ≠ [] →
      zero production < width)
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
                  nonempty (Nat.lt_of_le_of_ne ordered valueNe)
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

/-- A finite boundary-free zero-span table, plus exact admissibility coverage,
discharges the complete contextual prediction table. -/
theorem frontierPredictionRankTable_eq_true_of_zeroSpanTable
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {memo : GuardMemo tokens}
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo) (cursor : Boundary tokens)
    (width : Nat) (zero positive : ProductionId → Nat)
    (zeroBound : ∀ production, production.rhs ≠ [] →
      zero production < width)
    (admissible : DottedRhs → Bool)
    (admissibleAt : ∀ waiting,
      ContextualReach file tokens memo correct final waiting →
      waiting.raw.current = cursor →
      waiting.raw.origin = waiting.raw.current →
      admissible {
        production := waiting.raw.production
        dot := waiting.raw.dot
      } = true)
    (checked : frontierZeroSpanPredictionRankTable
      admissible zero = true) :
    frontierPredictionRankTable owned correct final cursor
      (frontierSpanPotential width zero positive) = true := by
  apply frontierPredictionRankTable_eq_true_of_zeroSpan
    owned correct final cursor width zero positive zeroBound
  intro waiting production reached current atOrigin next _enabled nonempty
  let dotted : DottedRhs := {
    production := waiting.raw.production
    dot := waiting.raw.dot
  }
  have decreases := frontierZeroSpanPredictionRank_lt_of_table
    admissible zero checked dotted production
      (admissibleAt waiting reached current atOrigin) next.2 nonempty
  simpa only [dotted, frontierGrammarRank, frontierRawGrammarRank,
    frontierSpanPotential, FrontierPredictedItem,
    frontierZeroSpanGrammarRank, frontierZeroSpanPredictedDotted,
    frontierRhsRemaining, if_pos atOrigin, if_true] using decreases

/-- The exact reached-zero-span dotted graph is sufficient for every
contextual prediction row; no separate admissibility proof is exposed. -/
theorem frontierPredictionRankTable_eq_true_of_reachedZeroSpanTable
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {memo : GuardMemo tokens}
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo) (cursor : Boundary tokens)
    (width : Nat) (zero positive : ProductionId → Nat)
    (zeroBound : ∀ production, production.rhs ≠ [] →
      zero production < width)
    (checked : frontierZeroSpanPredictionRankTable
      (frontierReachedZeroSpanDottedBool owned correct final cursor)
      zero = true) :
    frontierPredictionRankTable owned correct final cursor
      (frontierSpanPotential width zero positive) = true := by
  apply frontierPredictionRankTable_eq_true_of_zeroSpanTable
    owned correct final cursor width zero positive zeroBound
      (frontierReachedZeroSpanDottedBool owned correct final cursor)
  · intro waiting reached current atOrigin
    exact frontierReachedZeroSpanDottedBool_eq_true_of_reached
      owned correct final cursor waiting reached current atOrigin
  · exact checked
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

/-- Conversely, any explicit normalization witness for every completed item
at a greatest frontier makes the finite completion table accept. -/
theorem frontierCompletionRankTable_eq_true_of_normalizes
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {memo : GuardMemo tokens}
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo) (cursor : Boundary tokens)
    (greatest : GreatestReachableCursor
      file tokens memo correct final cursor)
    (potential : FrontierGrammarPotential tokens)
    (normalizes : ∀ waiting,
      FrontierReach file tokens memo correct final cursor waiting →
      CompleteItem waiting.raw →
      waiting = CanonicalCompleteRootItem tokens .module
          (Boundary.start tokens) (Boundary.afterLogicalEOF tokens) .plain ∨
        ∃ after : ContextualItemKey tokens,
          FrontierReach file tokens memo correct final cursor after ∧
          frontierGrammarRank potential after <
            frontierGrammarRank potential waiting) :
    frontierCompletionRankTable
      owned correct final cursor potential = true := by
  apply List.all_eq_true.mpr
  intro waiting _waitingMember
  letI : Decidable
      (ContextualReach file tokens memo correct final waiting) :=
    contextualReachDecision owned correct final waiting
  letI : Decidable (CompleteItem waiting.raw) :=
    completeItemDecision waiting.raw
  by_cases reached : ContextualReach file tokens memo correct final waiting
  · by_cases current : waiting.raw.current = cursor
    · by_cases complete : CompleteItem waiting.raw
      · simp only [frontierCompletionRankCell, if_pos reached,
          if_pos current, if_pos complete, Bool.or_eq_true]
        rcases normalizes waiting ⟨greatest, reached, current⟩ complete with
          root | ⟨after, afterFrontier, decreases⟩
        · exact Or.inl (decide_eq_true_iff.mpr root)
        · apply Or.inr
          apply List.any_eq_true.mpr
          refine ⟨after, allContextualItems_complete after, ?_⟩
          apply (frontierLowerRankCell_eq_true_iff
            owned correct final cursor potential waiting after).mpr
          exact ⟨afterFrontier.2.1, afterFrontier.2.2, decreases⟩
      · simp [frontierCompletionRankCell, reached, current, complete]
    · simp [frontierCompletionRankCell, reached, current]
  · simp [frontierCompletionRankCell, reached]

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
