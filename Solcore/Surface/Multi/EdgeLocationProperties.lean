import Solcore.Surface.Multi.LocationProperties

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Solcore.Workspace

namespace ScannedEdgeWitness

/-- A scan preserves the item origin and advances exactly across its matched
terminal cursor. -/
theorem sourceBoundaries
    {file : WorkspaceFile} {tokens : List Token}
    {before after : DottedItem tokens}
    {cursor : TerminalCursor tokens}
    (witness : ScannedEdgeWitness file tokens before after cursor) :
    after.origin = before.origin ∧
      witness.matched.cursor.beforeBoundary = before.current ∧
      after.current = witness.matched.cursor.afterBoundary := by
  rcases witness with
    ⟨terminal, matched, sameCursor, next, atCurrent, advance⟩
  exact ⟨advance.2.2.1, by simpa only [sameCursor] using atCurrent,
    advance.2.2.2⟩

/-- A scan appends its physical terminal anchor without leaving the advanced
chart interval.  End of input contributes the empty trace. -/
theorem sourceAnchorTrace_within
    {file : WorkspaceFile} {tokens : List Token}
    {before after : DottedItem tokens}
    {cursor : TerminalCursor tokens}
    (witness : ScannedEdgeWitness file tokens before after cursor)
    (owned : TokensOwnedBy file tokens)
    (beforeOrdered : before.origin.val ≤ before.current.val)
    {prior : SourceAnchorTrace file tokens}
    (priorInside : SourceAnchorTrace.Within prior
      before.origin before.current) :
    SourceAnchorTrace.Within
      (prior ++ witness.matched.sourceAnchorTrace owned)
      after.origin after.current := by
  have boundaries := witness.sourceBoundaries
  have priorInsideAfter : SourceAnchorTrace.Within prior
      after.origin before.current := by
    simpa only [boundaries.1] using priorInside
  have terminalInside := witness.matched.sourceAnchorTrace_within owned
    before.current after.current
    (by
      rw [← boundaries.2.1]
      exact Nat.le_refl _)
    (by
      rw [boundaries.2.2]
      exact Nat.le_refl _)
  have combinedBoundaries :
      after.origin.val ≤ before.current.val ∧
        before.current.val ≤ after.current.val := by
    constructor
    · simpa only [boundaries.1] using beforeOrdered
    · calc
        before.current.val = witness.matched.cursor.val := by
          rw [← boundaries.2.1]
          rfl
        _ ≤ witness.matched.cursor.val + 1 := Nat.le_succ _
        _ = after.current.val := by
          rw [boundaries.2.2]
          rfl
  exact SourceAnchorTrace.within_append_across
    priorInsideAfter terminalInside combinedBoundaries

/-- A scan preserves source order when it appends its terminal anchor. -/
theorem sourceAnchorTrace_ordered
    {file : WorkspaceFile} {tokens : List Token}
    {before after : DottedItem tokens}
    {cursor : TerminalCursor tokens}
    (witness : ScannedEdgeWitness file tokens before after cursor)
    (owned : TokensOwnedBy file tokens)
    {prior : SourceAnchorTrace file tokens}
    (priorInside : SourceAnchorTrace.Within prior
      before.origin before.current)
    (priorOrdered : SourceAnchorTrace.Ordered prior) :
    SourceAnchorTrace.Ordered
      (prior ++ witness.matched.sourceAnchorTrace owned) := by
  have boundaries := witness.sourceBoundaries
  have terminalInside := witness.matched.sourceAnchorTrace_within owned
    before.current after.current
    (by
      rw [← boundaries.2.1]
      exact Nat.le_refl _)
    (by
      rw [boundaries.2.2]
      exact Nat.le_refl _)
  exact SourceAnchorTrace.ordered_append_across
    priorInside terminalInside priorOrdered
      (witness.matched.sourceAnchorTrace_ordered owned)

end ScannedEdgeWitness

namespace CompletedEdgeWitness

/-- Completion joins the waiting and finished item intervals at the shared
boundary and preserves their outer endpoints. -/
theorem sourceBoundaries
    {tokens : List Token}
    {waiting finished after : DottedItem tokens}
    {shared : Boundary tokens}
    (witness : CompletedEdgeWitness tokens waiting finished after shared) :
    after.origin = waiting.origin ∧
      waiting.current = shared ∧
      finished.origin = shared ∧
      after.current = finished.current := by
  exact ⟨witness.advance.2.2.1, witness.waitingAtShared,
    witness.finishedAtShared, witness.advance.2.2.2⟩

/-- Completion keeps the concatenated waiting and child traces inside the
completed item interval. -/
theorem sourceAnchorTraces_within
    {file : WorkspaceFile} {tokens : List Token}
    {waiting finished after : DottedItem tokens}
    {shared : Boundary tokens}
    (witness : CompletedEdgeWitness tokens waiting finished after shared)
    (waitingOrdered : waiting.origin.val ≤ waiting.current.val)
    (finishedOrdered : finished.origin.val ≤ finished.current.val)
    {prior child : SourceAnchorTrace file tokens}
    (priorInside : SourceAnchorTrace.Within prior
      waiting.origin waiting.current)
    (childInside : SourceAnchorTrace.Within child
      finished.origin finished.current) :
    SourceAnchorTrace.Within (prior ++ child)
      after.origin after.current := by
  have boundaries := witness.sourceBoundaries
  have priorInsideAfter : SourceAnchorTrace.Within prior
      after.origin shared := by
    simpa only [boundaries.1, boundaries.2.1] using priorInside
  have childInsideAfter : SourceAnchorTrace.Within child
      shared after.current := by
    simpa only [boundaries.2.2.1, boundaries.2.2.2] using childInside
  have combinedBoundaries :
      after.origin.val ≤ shared.val ∧ shared.val ≤ after.current.val := by
    constructor
    · simpa only [boundaries.1, boundaries.2.1] using waitingOrdered
    · simpa only [boundaries.2.2.1, boundaries.2.2.2] using
        finishedOrdered
  exact SourceAnchorTrace.within_append_across
    priorInsideAfter childInsideAfter combinedBoundaries

/-- Completion preserves source order when it appends the child trace. -/
theorem sourceAnchorTraces_ordered
    {file : WorkspaceFile} {tokens : List Token}
    {waiting finished after : DottedItem tokens}
    {shared : Boundary tokens}
    (witness : CompletedEdgeWitness tokens waiting finished after shared)
    {prior child : SourceAnchorTrace file tokens}
    (priorInside : SourceAnchorTrace.Within prior
      waiting.origin waiting.current)
    (childInside : SourceAnchorTrace.Within child
      finished.origin finished.current)
    (priorOrdered : SourceAnchorTrace.Ordered prior)
    (childOrdered : SourceAnchorTrace.Ordered child) :
    SourceAnchorTrace.Ordered (prior ++ child) := by
  have boundaries := witness.sourceBoundaries
  have childInsideAfter : SourceAnchorTrace.Within child
      waiting.current after.current := by
    simpa only [boundaries.2.1, boundaries.2.2.1,
      boundaries.2.2.2] using childInside
  exact SourceAnchorTrace.ordered_append_across
    priorInside childInsideAfter priorOrdered childOrdered

end CompletedEdgeWitness

end Solcore.Surface.Multi
