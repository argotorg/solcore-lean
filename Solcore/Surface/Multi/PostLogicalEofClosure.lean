import Solcore.Surface.Multi.ChartProperties
import Solcore.Surface.Multi.RootlessNormalizationRank

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar
open Solcore.Workspace

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
