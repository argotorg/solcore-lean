import Solcore.Surface.Multi.IntervalLocationEvidence

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Solcore.Workspace

namespace LocationFragment

/-- Every location occurrence of the smaller fragment also occurs in the
larger fragment.  Multiplicity and order are irrelevant to validity and
nesting, while roots are re-anchored explicitly when evidence is restricted. -/
def IsSubfragmentOf (inner outer : LocationFragment) : Prop :=
  (∀ root ∈ inner.roots, root ∈ outer.roots) ∧
    (∀ span ∈ inner.inventory.spans, span ∈ outer.inventory.spans) ∧
    ∀ containment ∈ inner.inventory.containments,
      containment ∈ outer.inventory.containments

namespace IsSubfragmentOf

theorem refl (fragment : LocationFragment) :
    fragment.IsSubfragmentOf fragment := by
  exact ⟨fun _ member => member, fun _ member => member,
    fun _ member => member⟩

theorem trans {first second third : LocationFragment}
    (firstSecond : first.IsSubfragmentOf second)
    (secondThird : second.IsSubfragmentOf third) :
    first.IsSubfragmentOf third := by
  exact ⟨
    fun root member => secondThird.1 root (firstSecond.1 root member),
    fun span member => secondThird.2.1 span (firstSecond.2.1 span member),
    fun containment member =>
      secondThird.2.2 containment (firstSecond.2.2 containment member)⟩

theorem of_mem_merge
    {fragment : LocationFragment} {fragments : List LocationFragment}
    (member : fragment ∈ fragments) :
    fragment.IsSubfragmentOf (LocationFragment.merge fragments) := by
  refine ⟨?_, ?_, ?_⟩
  · intro root rootMember
    rw [LocationFragment.merge_roots, List.mem_flatMap]
    exact ⟨fragment, member, rootMember⟩
  · intro span spanMember
    rw [LocationFragment.merge_spans, List.mem_flatMap]
    exact ⟨fragment, member, spanMember⟩
  · intro containment containmentMember
    rw [LocationFragment.merge_containments, List.mem_flatMap]
    exact ⟨fragment, member, containmentMember⟩

/-- The empty fragment is a subfragment of every location fragment. -/
theorem empty (outer : LocationFragment) :
    LocationFragment.empty.IsSubfragmentOf outer := by
  exact ⟨by simp, by simp, by simp⟩

/-- Merge any finite family whose members are all subfragments of the same
outer fragment. -/
theorem merge
    {fragments : List LocationFragment} {outer : LocationFragment}
    (inside : ∀ fragment ∈ fragments,
      fragment.IsSubfragmentOf outer) :
    (LocationFragment.merge fragments).IsSubfragmentOf outer := by
  refine ⟨?_, ?_, ?_⟩
  · intro root member
    rw [LocationFragment.merge_roots, List.mem_flatMap] at member
    rcases member with ⟨fragment, fragmentMember, rootMember⟩
    exact (inside fragment fragmentMember).1 root rootMember
  · intro span member
    rw [LocationFragment.merge_spans, List.mem_flatMap] at member
    rcases member with ⟨fragment, fragmentMember, spanMember⟩
    exact (inside fragment fragmentMember).2.1 span spanMember
  · intro containment member
    rw [LocationFragment.merge_containments, List.mem_flatMap] at member
    rcases member with
      ⟨fragment, fragmentMember, containmentMember⟩
    exact (inside fragment fragmentMember).2.2 containment
      containmentMember

/-- Binary specialization of `merge`. -/
theorem merge_pair
    {first second outer : LocationFragment}
    (firstInside : first.IsSubfragmentOf outer)
    (secondInside : second.IsSubfragmentOf outer) :
    (LocationFragment.merge [first, second]).IsSubfragmentOf outer := by
  apply merge
  intro fragment member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  exact member.elim (fun equality => equality ▸ firstInside)
    (fun equality => equality ▸ secondInside)

/-- Map-shaped specialization used by retained semantic lists. -/
theorem merge_map
    {alpha : Type} {values : List alpha}
    {visit : alpha → LocationFragment} {outer : LocationFragment}
    (inside : ∀ value ∈ values,
      (visit value).IsSubfragmentOf outer) :
    (LocationFragment.merge (values.map visit)).IsSubfragmentOf outer := by
  apply merge
  intro fragment member
  rw [List.mem_map] at member
  rcases member with ⟨value, valueMember, rfl⟩
  exact inside value valueMember

/-- One mapped child is a subfragment of the complete mapped merge. -/
theorem of_mem_merge_map
    {alpha : Type} {value : alpha} {values : List alpha}
    {visit : alpha → LocationFragment}
    (member : value ∈ values) :
    (visit value).IsSubfragmentOf
  (LocationFragment.merge (values.map visit)) := by
  apply of_mem_merge
  exact List.mem_map_of_mem member

/-- A fragment containing a rooted subfragment is itself rooted. -/
theorem roots_ne_nil
    {inner outer : LocationFragment}
    (inside : inner.IsSubfragmentOf outer)
    (innerRooted : inner.roots ≠ []) :
    outer.roots ≠ [] := by
  intro outerEmpty
  obtain ⟨root, rootMember⟩ := List.exists_mem_of_ne_nil _ innerRooted
  have := inside.1 root rootMember
  rw [outerEmpty] at this
  simp at this

end IsSubfragmentOf

end LocationFragment

namespace SourceAnchorTrace

private theorem selectForSpans
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    (available : SourceAnchorTrace file tokens)
    (inside : available.Within origin finish) :
    ∀ roots : List SourceSpan,
      (∀ root ∈ roots, root ∈ available.spans) →
      ∃ selected : SourceAnchorTrace file tokens,
        selected.spans = roots ∧ selected.Within origin finish := by
  intro roots subset
  induction roots with
  | nil =>
      exact ⟨[], rfl, SourceAnchorTrace.within_nil⟩
  | cons root rest inductionHypothesis =>
      have rootAvailable := subset root (by simp)
      rw [SourceAnchorTrace.spans, List.mem_map] at rootAvailable
      rcases rootAvailable with ⟨anchor, anchorMember, anchorSpan⟩
      rcases inductionHypothesis
          (fun selected member => subset selected (by simp [member])) with
        ⟨selected, selectedSpans, selectedInside⟩
      refine ⟨anchor :: selected, ?_, ?_⟩
      · change anchor.span :: selected.spans = root :: rest
        rw [anchorSpan, selectedSpans]
      · intro selectedAnchor member
        simp only [List.mem_cons] at member
        rcases member with rfl | selectedMember
        · exact inside selectedAnchor anchorMember
        · exact selectedInside selectedAnchor selectedMember

end SourceAnchorTrace

namespace IntervalLocationEvidence

/-- Restrict semantic evidence to any fragment whose occurrences all come
from the original fragment.  The full physical trace is deliberately kept. -/
theorem restrict
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {inner outer : LocationFragment}
    {trace : SourceAnchorTrace file tokens}
    (subfragment : inner.IsSubfragmentOf outer)
    (evidence : IntervalLocationEvidence file tokens origin finish
      outer trace) :
    IntervalLocationEvidence file tokens origin finish inner trace := by
  rcases evidence with
    ⟨rootAnchors, rootSpans, rootsWithin, traceWithin,
      traceOrdered, outerValid, outerNested⟩
  have rootsAvailable :
      ∀ root ∈ inner.roots, root ∈ rootAnchors.spans := by
    intro root member
    rw [rootSpans]
    exact subfragment.1 root member
  rcases SourceAnchorTrace.selectForSpans rootAnchors rootsWithin
      inner.roots rootsAvailable with
    ⟨innerAnchors, innerSpans, innerWithin⟩
  refine ⟨innerAnchors, innerSpans, innerWithin, traceWithin,
    traceOrdered, ?_, ?_⟩
  · intro span member
    exact outerValid span (subfragment.2.1 span member)
  · intro containment member
    exact outerNested containment (subfragment.2.2 containment member)

/-- Restrict the semantic children and then place a checked source wrapper
around them.  Occupancy is retained from any root of the original fragment,
so the selected children themselves may be empty. -/
theorem restrictAndLocateByWitness
    {file : WorkspaceFile} {tokens : List Token}
    (tokensOrdered : TokenSpansOrdered tokens)
    {origin finish : Boundary tokens}
    (witness : ConsumedSpanWitness file tokens origin finish)
    {inner outer : LocationFragment}
    {trace : SourceAnchorTrace file tokens}
    (subfragment : inner.IsSubfragmentOf outer)
    (evidence : IntervalLocationEvidence file tokens origin finish
      outer trace)
    (hasOuterRoot : outer.roots ≠ []) :
    IntervalLocationEvidence file tokens origin finish
      (LocationFragment.located witness.span [inner]) trace := by
  have innerEvidence := restrict subfragment evidence
  let anchor : SourceAnchor file tokens := {
    origin := origin
    finish := finish
    span := witness.span
    occupied := ⟨witness.consumed,
      occupied_of_roots_ne_nil evidence hasOuterRoot⟩
  }
  exact located tokensOrdered anchor innerEvidence
    (rootsContainedBy tokensOrdered witness.consumed innerEvidence)

end IntervalLocationEvidence

end Solcore.Surface.Multi
