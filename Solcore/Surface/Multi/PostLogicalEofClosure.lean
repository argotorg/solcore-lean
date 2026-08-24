import Solcore.Surface.Multi.ChartProperties
import Solcore.Surface.Multi.RootlessNormalizationRank
import Lean.Elab.Tactic

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar
open Solcore.Workspace

private def postEofGrammarShapeBool : Bool :=
  allProductionIds.all fun production =>
    ((! production.rhs.contains (.terminal .endOfFile)) ||
      decide (production = .atom moduleEofAtomSite)) &&
    ((! production.rhs.contains
        (.nonterminal (.aux moduleEofGrammarSite))) ||
      decide (production = .seq moduleRootSequenceSite)) &&
    ((! production.rhs.contains
        (.nonterminal (.aux (GrammarSite.root .module)))) ||
      decide (production = .root .module))

set_option maxRecDepth 4000 in
private theorem postEofGrammarShapeBool_true :
    postEofGrammarShapeBool = true := by
  run_tac
    Lean.Meta.withTransparency .all do
      (← Lean.Elab.Tactic.getMainGoal).refl

private theorem ProductionId.postEof_shape (production : ProductionId) :
    (.terminal .endOfFile ∈ production.rhs →
      production = .atom moduleEofAtomSite) ∧
    (.nonterminal (.aux moduleEofGrammarSite) ∈ production.rhs →
      production = .seq moduleRootSequenceSite) ∧
    (.nonterminal (.aux (GrammarSite.root .module)) ∈ production.rhs →
      production = .root .module) := by
  have row := (List.all_eq_true.mp postEofGrammarShapeBool_true)
    production (allProductionIds_complete production)
  simp only [Bool.and_eq_true] at row
  refine ⟨?_, ?_, ?_⟩
  · intro member
    have accepted := row.1.1
    rw [Bool.or_eq_true] at accepted
    rcases accepted with absent | equal
    · have present : production.rhs.contains (.terminal .endOfFile) =
          true := List.contains_iff_mem.mpr member
      rw [present] at absent
      contradiction
    · exact of_decide_eq_true equal
  · intro member
    have accepted := row.1.2
    rw [Bool.or_eq_true] at accepted
    rcases accepted with absent | equal
    · have present : production.rhs.contains
          (.nonterminal (.aux moduleEofGrammarSite)) = true :=
        List.contains_iff_mem.mpr member
      rw [present] at absent
      contradiction
    · exact of_decide_eq_true equal
  · intro member
    have accepted := row.2
    rw [Bool.or_eq_true] at accepted
    rcases accepted with absent | equal
    · have present : production.rhs.contains
          (.nonterminal (.aux (GrammarSite.root .module))) = true :=
        List.contains_iff_mem.mpr member
      rw [present] at absent
      contradiction
    · exact of_decide_eq_true equal

private theorem Chart.OperationalContextualReach.afterLogicalEOF_shape
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens} {item : ContextualItemKey tokens}
    (reached : Chart.OperationalContextualReach file tokens memo item)
    (current : item.raw.current = Boundary.afterLogicalEOF tokens) :
    (item.raw.production = .atom moduleEofAtomSite ∧
        CompleteItem item.raw) ∨
      (item.raw.production = .seq moduleRootSequenceSite ∧
        CompleteItem item.raw) ∨
      (item.raw.production = .root .module ∧ CompleteItem item.raw) := by
  induction reached with
  | root =>
      have values := congrArg Fin.val current
      simp [Boundary.start, Boundary.afterLogicalEOF] at values
  | predict waiting predicted reached next enabled induction =>
      rcases induction current with
          ⟨production, complete⟩ | ⟨production, complete⟩ |
            ⟨production, complete⟩
      all_goals
        unfold NextSymbol at next
        unfold CompleteItem at complete
        omega
  | scan before after cursor reached structural induction =>
      rcases structural.1 with
        ⟨terminal, value, span, next, atCurrent, terminalAt,
          terminalMatches, advance⟩
      have cursorAtEnd : cursor.val = tokens.length := by
        have values := congrArg Fin.val current
        rw [advance.2.2.2] at values
        change cursor.val + 1 = tokens.length + 1 at values
        omega
      cases terminalAt with
      | retained token inRange lookup valid => omega
      | endOfFile atEnd =>
          have terminalEq : terminal = .endOfFile := by
            cases terminal <;> simp [TerminalMatches] at terminalMatches ⊢
          subst terminal
          have beforeProduction : before.raw.production =
              .atom moduleEofAtomSite :=
            (ProductionId.postEof_shape before.raw.production).1
              (List.mem_of_getElem? next.2)
          have afterProduction : after.raw.production =
              .atom moduleEofAtomSite :=
            advance.1.trans beforeProduction
          have beforeRhs : before.raw.production.rhs =
              [.terminal .endOfFile] :=
            (congrArg ProductionId.rhs beforeProduction).trans
              ProductionId.rhs_moduleEofAtom
          have beforeDot : before.raw.dot.val = 0 := by
            have bound := next.1
            have rhsLength : before.raw.production.rhs.length = 1 :=
              congrArg List.length beforeRhs
            omega
          exact Or.inl ⟨afterProduction, by
            unfold CompleteItem
            rw [advance.2.1, beforeDot]
            have afterRhs : after.raw.production.rhs =
                [.terminal .endOfFile] :=
              (congrArg ProductionId.rhs afterProduction).trans
                ProductionId.rhs_moduleEofAtom
            rw [congrArg List.length afterRhs]
            rfl⟩
  | complete waiting finished after shared waitingReached finishedReached
      structural waitingInduction finishedInduction =>
      rcases structural.1 with
        ⟨symbol, next, childComplete, lhsEq, waitingAtShared,
          finishedAtShared, advance⟩
      have finishedCurrent : finished.raw.current =
          Boundary.afterLogicalEOF tokens :=
        advance.2.2.2.symm.trans current
      rcases finishedInduction finishedCurrent with
          ⟨finishedProduction, finishedComplete⟩ |
          ⟨finishedProduction, finishedComplete⟩ |
          ⟨finishedProduction, finishedComplete⟩
      · have exactNext : waiting.raw.production.rhs[waiting.raw.dot.val]? =
            some (.nonterminal (.aux moduleEofGrammarSite)) := by
          calc
            _ = some (.nonterminal symbol) := next.2
            _ = some (.nonterminal finished.raw.production.lhs) := by
              rw [lhsEq]
            _ = _ := by
              rw [finishedProduction]
              rfl
        have waitingProduction : waiting.raw.production =
            .seq moduleRootSequenceSite :=
          (ProductionId.postEof_shape waiting.raw.production).2.1
            (List.mem_of_getElem? exactNext)
        have waitingRhs : waiting.raw.production.rhs =
            [.nonterminal (.aux moduleItemsGrammarSite),
              .nonterminal (.aux moduleEofGrammarSite)] :=
          (congrArg ProductionId.rhs waitingProduction).trans
            ProductionId.rhs_moduleRootSequence
        have waitingDot : waiting.raw.dot.val = 1 := by
          have bound := next.1
          have rhsLength : waiting.raw.production.rhs.length = 2 :=
            congrArg List.length waitingRhs
          have cases : waiting.raw.dot.val = 0 ∨
              waiting.raw.dot.val = 1 := by omega
          rcases cases with zero | one
          · have selected := exactNext
            rw [congrArg (fun rhs : List GrammarSymbol =>
              rhs[waiting.raw.dot.val]?) waitingRhs, zero] at selected
            simp [moduleItemsGrammarSite, moduleEofGrammarSite] at selected
          · exact one
        have afterProduction := advance.1.trans waitingProduction
        exact Or.inr (Or.inl ⟨afterProduction, by
          unfold CompleteItem
          rw [advance.2.1, waitingDot]
          have afterRhs : after.raw.production.rhs =
              [.nonterminal (.aux moduleItemsGrammarSite),
                .nonterminal (.aux moduleEofGrammarSite)] :=
            (congrArg ProductionId.rhs afterProduction).trans
              ProductionId.rhs_moduleRootSequence
          rw [congrArg List.length afterRhs]
          rfl⟩)
      · have exactNext : waiting.raw.production.rhs[waiting.raw.dot.val]? =
            some (.nonterminal (.aux (GrammarSite.root .module))) := by
          calc
            _ = some (.nonterminal symbol) := next.2
            _ = some (.nonterminal finished.raw.production.lhs) := by
              rw [lhsEq]
            _ = _ := by
              rw [finishedProduction]
              rfl
        have waitingProduction : waiting.raw.production = .root .module :=
          (ProductionId.postEof_shape waiting.raw.production).2.2
            (List.mem_of_getElem? exactNext)
        have waitingDot : waiting.raw.dot.val = 0 := by
          have bound := next.1
          have rhsLength : waiting.raw.production.rhs.length = 1 := by
            rw [waitingProduction]
            simp [ProductionId.rhs]
          omega
        have afterProduction := advance.1.trans waitingProduction
        exact Or.inr (Or.inr ⟨afterProduction, by
          unfold CompleteItem
          rw [advance.2.1, waitingDot]
          have afterRhs : after.raw.production.rhs =
              [.nonterminal (.aux (GrammarSite.root .module))] := by
            rw [afterProduction]
            rfl
          rw [congrArg List.length afterRhs]
          rfl⟩)
      · have exactNext : waiting.raw.production.rhs[waiting.raw.dot.val]? =
            some (.nonterminal (.rule .module)) := by
          calc
            _ = some (.nonterminal symbol) := next.2
            _ = some (.nonterminal finished.raw.production.lhs) := by
              rw [lhsEq]
            _ = _ := by
              rw [finishedProduction]
              rfl
        exact (ProductionId.rhs_no_moduleRule waiting.raw.production
          (List.mem_of_getElem? exactNext)).elim

private theorem Chart.OperationalContextualReach.no_terminal_afterLogicalEOF
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens} {item : ContextualItemKey tokens}
    (reached : Chart.OperationalContextualReach file tokens memo item)
    (current : item.raw.current = Boundary.afterLogicalEOF tokens)
    {terminal : TerminalSymbol}
    (next : NextSymbol item.raw (.terminal terminal)) : False := by
  rcases reached.afterLogicalEOF_shape current with
      ⟨production, complete⟩ | ⟨production, complete⟩ |
        ⟨production, complete⟩
  all_goals
    unfold NextSymbol at next
    unfold CompleteItem at complete
    omega

namespace Chart.ContextualWorklistResult

/-- The finite recognition ledger is closed past logical EOF when a retained
terminal expectation there entails retention of the canonical module root. -/
def PostLogicalEofTerminalClosed
    {file : WorkspaceFile} {tokens : List Token}
    (result : Chart.ContextualWorklistResult file tokens) : Prop :=
  result.expectedAtCurrent (Boundary.afterLogicalEOF tokens) ≠ [] →
    CanonicalCompleteRootItem tokens .module
      (Boundary.start tokens) (Boundary.afterLogicalEOF tokens) .plain ∈
        result.items

/-- Proof-free decision of the exact post-logical-EOF closure residual. -/
def postLogicalEofTerminalClosedBool
    {file : WorkspaceFile} {tokens : List Token}
    (result : Chart.ContextualWorklistResult file tokens) : Bool :=
  decide
      (result.expectedAtCurrent (Boundary.afterLogicalEOF tokens) = []) ||
    result.containsCompleteModuleRootItem

/-- The executable bit decides precisely the finite-ledger closure property. -/
theorem postLogicalEofTerminalClosedBool_eq_true_iff
    {file : WorkspaceFile} {tokens : List Token}
    (result : Chart.ContextualWorklistResult file tokens) :
    result.postLogicalEofTerminalClosedBool = true ↔
      result.PostLogicalEofTerminalClosed := by
  unfold postLogicalEofTerminalClosedBool PostLogicalEofTerminalClosed
  rw [Bool.or_eq_true, decide_eq_true_eq,
    containsCompleteModuleRootItem_eq_true_iff]
  by_cases empty :
      result.expectedAtCurrent (Boundary.afterLogicalEOF tokens) = []
  · simp [empty]
  · simp [empty]

/-- Extensional form of post-EOF closure over individual retained terminal
waits.  Greatest-cursor and guard premises are intentionally absent. -/
theorem postLogicalEofTerminalClosed_iff
    {file : WorkspaceFile} {tokens : List Token}
    (result : Chart.ContextualWorklistResult file tokens) :
    result.PostLogicalEofTerminalClosed ↔
      ∀ item terminal,
        item ∈ result.items →
        item.raw.current = Boundary.afterLogicalEOF tokens →
        NextSymbol item.raw (.terminal terminal) →
          CanonicalCompleteRootItem tokens .module
            (Boundary.start tokens) (Boundary.afterLogicalEOF tokens)
              .plain ∈ result.items := by
  constructor
  · intro closed item terminal member current next
    apply closed
    intro empty
    have expectedMember : terminal.expected ∈
        result.expectedAtCurrent (Boundary.afterLogicalEOF tokens) :=
      (expectedAtCurrent_mem_iff result
        (Boundary.afterLogicalEOF tokens) terminal.expected).mpr
          ⟨item, member, current, terminal, next, rfl⟩
    rw [empty] at expectedMember
    simp at expectedMember
  · intro closed nonempty
    obtain ⟨expected, expectedMember⟩ := List.exists_mem_of_ne_nil
      (result.expectedAtCurrent (Boundary.afterLogicalEOF tokens)) nonempty
    rcases (expectedAtCurrent_mem_iff result
      (Boundary.afterLogicalEOF tokens) expected).mp expectedMember with
      ⟨item, member, current, terminal, next, _expectedEq⟩
    exact closed item terminal member current next

end Chart.ContextualWorklistResult

private theorem contextualReach_enabledForPostEof
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {item : ContextualItemKey tokens}
    (reached : ContextualReach file tokens memo correct final item) :
    EnabledProductionInstance file tokens memo correct final {
      production := item.raw.production
      origin := item.raw.origin
      context := item.context
    } := by
  induction reached with
  | root =>
      intro guard polarity member
      simp [guardOf] at member
  | predict waiting predicted reached next enabled induction =>
      exact enabled
  | scan before after cursor reached structural induction =>
      rcases structural with ⟨valid, context⟩
      rcases valid with
        ⟨terminal, value, span, next, atCurrent, terminalAt,
          terminalMatches, advance⟩
      rcases advance with ⟨production, dot, origin, current⟩
      simpa only [production, origin, ← context] using induction
  | complete waiting finished after shared waitingReached finishedReached
      structural waitingInduction finishedInduction =>
      rcases structural with ⟨valid, finishedContext, afterContext⟩
      rcases valid with
        ⟨symbol, next, complete, lhs, waitingAt, finishedAt, advance⟩
      rcases advance with ⟨production, dot, origin, current⟩
      simpa only [production, origin, afterContext] using waitingInduction

/-- Exact worklist correspondence turns the finite post-EOF closure bit into
the declarative closure component consumed by rootless normalization. -/
theorem executeObservedContextualWorklistMulti?_postLogicalEofTerminalWaitForcesRoot_of_closed
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (result : Chart.ContextualWorklistResult file tokens)
    (selected : Chart.executeObservedContextualWorklistMulti?
      file tokens owned = some result)
    (closed : result.PostLogicalEofTerminalClosed) :
    let correct := executeObservedContextualWorklistMulti?_phaseBCorrect
      file tokens owned result selected
    let final := Chart.executeObservedContextualWorklistMulti?_allGuardsFinal
      file tokens owned result selected
    PostLogicalEofTerminalWaitForcesRoot
      file tokens result.memo correct final := by
  let correct := executeObservedContextualWorklistMulti?_phaseBCorrect
    file tokens owned result selected
  let final := Chart.executeObservedContextualWorklistMulti?_allGuardsFinal
    file tokens owned result selected
  change PostLogicalEofTerminalWaitForcesRoot
    file tokens result.memo correct final
  have correspondence :=
    executeObservedContextualWorklistMulti?_correspondence
      file tokens owned result selected
  change
    (∀ item, item ∈ result.items ↔
      ContextualReach file tokens result.memo correct final item) ∧ _
      at correspondence
  intro cursor _greatest waiting afterEof
  rcases waiting with ⟨item, terminal, frontier, next, _enabled⟩
  have current : item.raw.current = Boundary.afterLogicalEOF tokens := by
    calc
      item.raw.current = cursor := frontier.2.2
      _ = Boundary.afterLogicalEOF tokens := by
        apply Fin.ext
        simpa [Boundary.afterLogicalEOF] using afterEof
  have member : item ∈ result.items :=
    (correspondence.1 item).mpr frontier.2.1
  have rootMember :=
    (Chart.ContextualWorklistResult.postLogicalEofTerminalClosed_iff
      result).mp closed item terminal member current next
  exact (correspondence.1 _).mp rootMember

/-- On an exact observed-worklist result, the finite closure predicate is not
merely sufficient: it is precisely the remaining declarative post-EOF fact. -/
theorem executeObservedContextualWorklistMulti?_postLogicalEofTerminalClosed_iff
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (result : Chart.ContextualWorklistResult file tokens)
    (selected : Chart.executeObservedContextualWorklistMulti?
      file tokens owned = some result) :
    result.PostLogicalEofTerminalClosed ↔
      let correct := executeObservedContextualWorklistMulti?_phaseBCorrect
        file tokens owned result selected
      let final := Chart.executeObservedContextualWorklistMulti?_allGuardsFinal
        file tokens owned result selected
      PostLogicalEofTerminalWaitForcesRoot
        file tokens result.memo correct final := by
  constructor
  · exact
      executeObservedContextualWorklistMulti?_postLogicalEofTerminalWaitForcesRoot_of_closed
        file tokens owned result selected
  · intro forcesRoot
    let correct := executeObservedContextualWorklistMulti?_phaseBCorrect
      file tokens owned result selected
    let final := Chart.executeObservedContextualWorklistMulti?_allGuardsFinal
      file tokens owned result selected
    change PostLogicalEofTerminalWaitForcesRoot
      file tokens result.memo correct final at forcesRoot
    have correspondence :=
      executeObservedContextualWorklistMulti?_correspondence
        file tokens owned result selected
    change
      (∀ item, item ∈ result.items ↔
        ContextualReach file tokens result.memo correct final item) ∧ _
        at correspondence
    apply
      (Chart.ContextualWorklistResult.postLogicalEofTerminalClosed_iff
        result).mpr
    intro item terminal member current next
    have reached :
        ContextualReach file tokens result.memo correct final item :=
      (correspondence.1 item).mp member
    have greatest : GreatestReachableCursor
        file tokens result.memo correct final
          (Boundary.afterLogicalEOF tokens) := by
      constructor
      · exact ⟨item, reached, current⟩
      · intro candidate _candidateReached
        have bounded := candidate.raw.current.isLt
        change candidate.raw.current.val ≤ tokens.length + 1
        omega
    have enabled := contextualReach_enabledForPostEof reached
    have rootReached := forcesRoot (Boundary.afterLogicalEOF tokens)
      greatest ⟨item, terminal, ⟨greatest, reached, current⟩,
        next, enabled⟩ rfl
    exact (correspondence.1 _).mpr rootReached

/-- A saturated observed worklist has no terminal expectation past logical
EOF, so its finite post-EOF closure certificate is always set. -/
theorem executeObservedContextualWorklistMulti?_postLogicalEofTerminalClosedBool_eq_true
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (result : Chart.ContextualWorklistResult file tokens)
    (selected : Chart.executeObservedContextualWorklistMulti?
      file tokens owned = some result) :
    result.postLogicalEofTerminalClosedBool = true := by
  have sound :=
    Chart.executeObservedContextualWorklistMulti?_operational_sound
      file tokens owned result selected
  have empty : result.expectedAtCurrent
      (Boundary.afterLogicalEOF tokens) = [] := by
    rw [List.eq_nil_iff_forall_not_mem]
    intro expected member
    rcases (Chart.ContextualWorklistResult.expectedAtCurrent_mem_iff
      result (Boundary.afterLogicalEOF tokens) expected).mp member with
      ⟨item, itemMember, current, terminal, next, _expectedEq⟩
    exact (sound.1 item itemMember).no_terminal_afterLogicalEOF current next
  unfold Chart.ContextualWorklistResult.postLogicalEofTerminalClosedBool
  simp [empty]

/-- The single executable bit is exactly the original post-EOF residual for
the recognition result returned by the total worklist. -/
theorem executeObservedContextualWorklistMulti?_postLogicalEofTerminalClosedBool_eq_true_iff
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (result : Chart.ContextualWorklistResult file tokens)
    (selected : Chart.executeObservedContextualWorklistMulti?
      file tokens owned = some result) :
    result.postLogicalEofTerminalClosedBool = true ↔
      let correct := executeObservedContextualWorklistMulti?_phaseBCorrect
        file tokens owned result selected
      let final := Chart.executeObservedContextualWorklistMulti?_allGuardsFinal
        file tokens owned result selected
      PostLogicalEofTerminalWaitForcesRoot
        file tokens result.memo correct final :=
  (Chart.ContextualWorklistResult.postLogicalEofTerminalClosedBool_eq_true_iff
    result).trans
      (executeObservedContextualWorklistMulti?_postLogicalEofTerminalClosed_iff
        file tokens owned result selected)

end Solcore.Surface.Multi
