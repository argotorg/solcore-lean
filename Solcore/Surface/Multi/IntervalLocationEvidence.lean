import Solcore.Surface.Multi.LocationProperties
import Solcore.Surface.Multi.SemanticLocation

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar
open Solcore.Workspace

/-- Source evidence for one semantic fragment over one parser interval.

`rootAnchors` certifies the semantic roots exposed to a future parent.  The
separate `trace` records every scanned physical terminal, including punctuation
that a semantic action may discard.  Keeping them separate avoids imposing an
incorrect non-overlap order between wrapper spans and their own tokens. -/
def IntervalLocationEvidence
    (file : WorkspaceFile) (tokens : List Token)
    (origin finish : Boundary tokens)
    (fragment : LocationFragment)
    (trace : SourceAnchorTrace file tokens) : Prop :=
  ∃ rootAnchors : SourceAnchorTrace file tokens,
    rootAnchors.spans = fragment.roots ∧
      rootAnchors.Within origin finish ∧
      trace.Within origin finish ∧
      trace.Ordered ∧
      fragment.ValidFor file ∧
      fragment.Nested

namespace IntervalLocationEvidence

/-- Semantic roots certified by interval evidence are contained by any source
span known to cover the same parser interval. -/
theorem rootsContainedBy
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {fragment : LocationFragment}
    {trace : SourceAnchorTrace file tokens}
    {outerSpan : SourceSpan}
    (tokensOrdered : TokenSpansOrdered tokens)
    (outer : ConsumedSpan file tokens origin finish outerSpan)
    (evidence : IntervalLocationEvidence file tokens origin finish
      fragment trace) :
    fragment.RootsContainedBy outerSpan := by
  rcases evidence with
    ⟨rootAnchors, rootSpans, rootsWithin, _traceWithin,
      _traceOrdered, _valid, _nested⟩
  intro root member
  have mappedMember : root ∈ rootAnchors.spans := by
    rw [rootSpans]
    exact member
  rw [SourceAnchorTrace.spans, List.mem_map] at mappedMember
  rcases mappedMember with ⟨anchor, anchorMember, rfl⟩
  exact anchor.containedBy tokensOrdered outer
    (rootsWithin anchor anchorMember)

/-- Every scanned physical span in the evidence is contained by a source span
covering the same parser interval. -/
theorem traceSpansContainedBy
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {fragment : LocationFragment}
    {trace : SourceAnchorTrace file tokens}
    {outerSpan : SourceSpan}
    (tokensOrdered : TokenSpansOrdered tokens)
    (outer : ConsumedSpan file tokens origin finish outerSpan)
    (evidence : IntervalLocationEvidence file tokens origin finish
      fragment trace) :
    ∀ span ∈ trace.spans, outerSpan.Contains span := by
  rcases evidence with
    ⟨_rootAnchors, _rootSpans, _rootsWithin, traceWithin,
      _traceOrdered, _valid, _nested⟩
  exact SourceAnchorTrace.spans_containedBy
    tokensOrdered outer traceWithin

/-- Interval evidence exposes source validity and direct AST nesting. -/
theorem validFor_and_nested
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {fragment : LocationFragment}
    {trace : SourceAnchorTrace file tokens}
    (evidence : IntervalLocationEvidence file tokens origin finish
      fragment trace) :
    fragment.ValidFor file ∧ fragment.Nested := by
  rcases evidence with
    ⟨_rootAnchors, _rootSpans, _rootsWithin, _traceWithin,
      _traceOrdered, valid, nested⟩
  exact ⟨valid, nested⟩

/-- Interval evidence exposes containment and order of its physical trace. -/
theorem trace_within_and_ordered
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {fragment : LocationFragment}
    {trace : SourceAnchorTrace file tokens}
    (evidence : IntervalLocationEvidence file tokens origin finish
      fragment trace) :
    trace.Within origin finish ∧ trace.Ordered := by
  rcases evidence with
    ⟨_rootAnchors, _rootSpans, _rootsWithin, traceWithin,
      traceOrdered, _valid, _nested⟩
  exact ⟨traceWithin, traceOrdered⟩

/-- The empty semantic value and empty trace are valid over every interval. -/
theorem empty
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens) :
    IntervalLocationEvidence file tokens origin finish
      LocationFragment.empty [] := by
  refine ⟨[], ?_, SourceAnchorTrace.within_nil,
    SourceAnchorTrace.within_nil, SourceAnchorTrace.ordered_nil,
    LocationFragment.empty_validFor file,
    LocationFragment.empty_nested⟩
  rfl

/-- Replace the semantic fragment by an equal view without changing its
interval or physical trace. -/
theorem replaceFragment
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {left right : LocationFragment}
    {trace : SourceAnchorTrace file tokens}
    (equality : left = right)
    (evidence : IntervalLocationEvidence file tokens origin finish
      left trace) :
    IntervalLocationEvidence file tokens origin finish right trace := by
  subst right
  exact evidence

/-- Widening a parser interval preserves all semantic and physical evidence. -/
theorem widen
    {file : WorkspaceFile} {tokens : List Token}
    {innerOrigin innerFinish outerOrigin outerFinish : Boundary tokens}
    {fragment : LocationFragment}
    {trace : SourceAnchorTrace file tokens}
    (evidence : IntervalLocationEvidence file tokens
      innerOrigin innerFinish fragment trace)
    (startsEarlier : outerOrigin.val ≤ innerOrigin.val)
    (finishesLater : innerFinish.val ≤ outerFinish.val) :
    IntervalLocationEvidence file tokens
      outerOrigin outerFinish fragment trace := by
  rcases evidence with
    ⟨rootAnchors, rootSpans, rootsWithin, traceWithin,
      traceOrdered, valid, nested⟩
  exact ⟨rootAnchors, rootSpans,
    SourceAnchorTrace.within_mono rootsWithin startsEarlier finishesLater,
    SourceAnchorTrace.within_mono traceWithin startsEarlier finishesLater,
    traceOrdered, valid, nested⟩

/-- Evidence for adjacent sibling values composes in grammar order. -/
theorem mergeAcross
    {file : WorkspaceFile} {tokens : List Token}
    {outerOrigin shared outerFinish : Boundary tokens}
    {leftFragment rightFragment : LocationFragment}
    {leftTrace rightTrace : SourceAnchorTrace file tokens}
    (left : IntervalLocationEvidence file tokens
      outerOrigin shared leftFragment leftTrace)
    (right : IntervalLocationEvidence file tokens
      shared outerFinish rightFragment rightTrace)
    (boundariesOrdered :
      outerOrigin.val ≤ shared.val ∧ shared.val ≤ outerFinish.val) :
    IntervalLocationEvidence file tokens outerOrigin outerFinish
      (LocationFragment.merge [leftFragment, rightFragment])
      (leftTrace ++ rightTrace) := by
  rcases left with
    ⟨leftRoots, leftRootSpans, leftRootsWithin, leftTraceWithin,
      leftTraceOrdered, leftValid, leftNested⟩
  rcases right with
    ⟨rightRoots, rightRootSpans, rightRootsWithin, rightTraceWithin,
      rightTraceOrdered, rightValid, rightNested⟩
  refine ⟨leftRoots ++ rightRoots, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [leftRootSpans, rightRootSpans]
  · exact SourceAnchorTrace.within_append_across
      leftRootsWithin rightRootsWithin boundariesOrdered
  · exact SourceAnchorTrace.within_append_across
      leftTraceWithin rightTraceWithin boundariesOrdered
  · exact SourceAnchorTrace.ordered_append_across
      leftTraceWithin rightTraceWithin leftTraceOrdered rightTraceOrdered
  · apply LocationFragment.merge_validFor
    intro fragment member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact leftValid
    · exact rightValid
  · apply LocationFragment.merge_nested
    intro fragment member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact leftNested
    · exact rightNested

/-- Any exposed semantic root proves that its containing parser interval
retains at least one physical token. -/
theorem occupied_of_roots_ne_nil
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {fragment : LocationFragment}
    {trace : SourceAnchorTrace file tokens}
    (evidence : IntervalLocationEvidence file tokens origin finish
      fragment trace)
    (hasRoot : fragment.roots ≠ []) :
    origin.val < Nat.min finish.val tokens.length := by
  rcases evidence with
    ⟨rootAnchors, rootSpans, rootsWithin, _traceWithin,
      _traceOrdered, _valid, _nested⟩
  cases rootAnchors with
  | nil =>
      exact (hasRoot (by simpa using rootSpans.symm)).elim
  | cons first rest =>
      have inside := rootsWithin first (by simp)
      have occupied := first.occupied.2
      change origin.val ≤ first.origin.val ∧
        first.finish.val ≤ finish.val at inside
      change first.origin.val <
        Nat.min first.finish.val tokens.length at occupied
      apply Nat.lt_min.mpr
      constructor
      · have beforeFinish : first.origin.val < first.finish.val :=
          Nat.lt_of_lt_of_le occupied (Nat.min_le_left _ _)
        omega
      · have beforeLength : first.origin.val < tokens.length :=
          Nat.lt_of_lt_of_le occupied (Nat.min_le_right _ _)
        omega

/-- An exact source anchor may become the semantic root for the value carried
by the same parser interval.  Existing child roots become its direct children,
while the physical terminal trace remains unchanged. -/
theorem located
    {file : WorkspaceFile} {tokens : List Token}
    (tokensOrdered : TokenSpansOrdered tokens)
    (anchor : SourceAnchor file tokens)
    {children : LocationFragment}
    {trace : SourceAnchorTrace file tokens}
    (evidence : IntervalLocationEvidence file tokens
      anchor.origin anchor.finish children trace)
    (contains : children.RootsContainedBy anchor.span) :
    IntervalLocationEvidence file tokens anchor.origin anchor.finish
      (LocationFragment.located anchor.span [children]) trace := by
  rcases evidence with
    ⟨childRoots, childRootSpans, childRootsWithin, traceWithin,
      traceOrdered, childValid, childNested⟩
  refine ⟨[anchor], ?_, ?_, traceWithin, traceOrdered, ?_, ?_⟩
  · rfl
  · intro selected member
    simp only [List.mem_singleton] at member
    subst selected
    exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  · intro span member
    rw [LocationFragment.located_spans] at member
    rcases List.mem_cons.mp member with outer | childMember
    · subst span
      exact anchor.span_validFor tokensOrdered
    · exact childValid span (by simpa using childMember)
  · intro containment member
    rw [LocationFragment.located_containments] at member
    rcases List.mem_append.mp member with direct | nestedMember
    · rw [List.mem_map] at direct
      rcases direct with ⟨child, childMember, rfl⟩
      exact contains child (by simpa using childMember)
    · exact childNested containment (by simpa using nestedMember)

/-- A checked consumed span becomes an exact source anchor whenever the
semantic input exposes a root, which also certifies interval occupancy. -/
theorem locatedByWitness
    {file : WorkspaceFile} {tokens : List Token}
    (tokensOrdered : TokenSpansOrdered tokens)
    {origin finish : Boundary tokens}
    (witness : ConsumedSpanWitness file tokens origin finish)
    {children : LocationFragment}
    {trace : SourceAnchorTrace file tokens}
    (evidence : IntervalLocationEvidence file tokens
      origin finish children trace)
    (hasRoot : children.roots ≠ []) :
    IntervalLocationEvidence file tokens origin finish
      (LocationFragment.located witness.span [children]) trace := by
  let anchor : SourceAnchor file tokens := {
    origin := origin
    finish := finish
    span := witness.span
    occupied := ⟨witness.consumed,
      occupied_of_roots_ne_nil evidence hasRoot⟩
  }
  exact located tokensOrdered anchor evidence
    (rootsContainedBy tokensOrdered witness.consumed evidence)

/-- Discarding a leading punctuation fragment from a semantic tuple preserves
the remaining value evidence and the complete physical trace. -/
theorem dropLeadingRaw
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {separator : SourceSpan}
    {fragment : LocationFragment}
    {trace : SourceAnchorTrace file tokens}
    (evidence : IntervalLocationEvidence file tokens origin finish
      (LocationFragment.merge [LocationFragment.raw separator, fragment])
      trace) :
    IntervalLocationEvidence file tokens origin finish fragment trace := by
  rcases evidence with
    ⟨rootAnchors, rootSpans, rootsWithin, traceWithin,
      traceOrdered, valid, nested⟩
  cases rootAnchors with
  | nil =>
      simp at rootSpans
  | cons first rest =>
      have rootShape :
          first.span = separator ∧
            SourceAnchorTrace.spans rest = fragment.roots := by
        simpa using rootSpans
      refine ⟨rest, rootShape.2, ?_, traceWithin, traceOrdered, ?_, ?_⟩
      · intro anchor member
        exact rootsWithin anchor (by simp [member])
      · exact LocationFragment.validFor_of_mem_merge
          (by simp) valid
      · exact LocationFragment.nested_of_mem_merge
          (by simp) nested

end IntervalLocationEvidence

namespace MatchedTerminal

/-- Every matched terminal has exact interval evidence.  Logical end of input
contributes the empty fragment and empty physical trace. -/
theorem locationEvidence
    {file : WorkspaceFile} {tokens : List Token}
    {terminal : TerminalSymbol}
    (owned : TokensOwnedBy file tokens)
    (matched : MatchedTerminal file tokens terminal) :
    IntervalLocationEvidence file tokens
      matched.cursor.beforeBoundary matched.cursor.afterBoundary
      matched.locationFragment (matched.sourceAnchorTrace owned) := by
  refine ⟨matched.sourceAnchorTrace owned, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · by_cases isEof : terminal = .endOfFile <;>
      simp [MatchedTerminal.locationFragment, isEof]
  · exact matched.sourceAnchorTrace_within owned
      matched.cursor.beforeBoundary matched.cursor.afterBoundary
      (Nat.le_refl _) (Nat.le_refl _)
  · exact matched.sourceAnchorTrace_within owned
      matched.cursor.beforeBoundary matched.cursor.afterBoundary
      (Nat.le_refl _) (Nat.le_refl _)
  · exact matched.sourceAnchorTrace_ordered owned
  · by_cases isEof : terminal = .endOfFile
    · subst terminal
      simp [MatchedTerminal.locationFragment,
        LocationFragment.ValidFor, LocationInventory.ValidFor]
    · simp [MatchedTerminal.locationFragment, isEof,
        LocationFragment.ValidFor, LocationInventory.ValidFor,
        matched.span_validFor]
  · by_cases isEof : terminal = .endOfFile <;>
      simp [MatchedTerminal.locationFragment, isEof,
        LocationFragment.Nested, LocationInventory.Nested]

end MatchedTerminal

end Solcore.Surface.Multi
