import Solcore.Surface.Multi.RuleIntervalLocationWrappedCases
import Solcore.Surface.Multi.EbnfLocationSubfragment

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar
open Solcore.Workspace

namespace RuleReduction.WrappedLocation

private theorem ofIdentifier_terminal_eq
    {file : WorkspaceFile} {tokens : List Token}
    (matched : MatchedTerminal file tokens (.category .identifier))
    (value : Identifier) :
    LocationFragment.ofIdentifier
        (RuleReduction.terminalLoc matched value) =
      matched.locationFragment := by
  exact LocationFragment.leaf_eq_raw matched.span

private theorem leaf_terminal_eq
    {file : WorkspaceFile} {tokens : List Token} {terminal : TerminalSymbol}
    (matched : MatchedTerminal file tokens terminal)
    (notEndOfFile : terminal ≠ .endOfFile) :
    LocationFragment.leaf matched.span = matched.locationFragment := by
  unfold MatchedTerminal.locationFragment
  rw [if_neg notEndOfFile]
  exact LocationFragment.leaf_eq_raw matched.span

private theorem input_roots_ne_nil_of_inside
    {file : WorkspaceFile} {tokens : List Token}
    {expression : EbnfExpr} {input : EbnfValue file tokens expression}
    {fragment : LocationFragment}
    (inside : EbnfValue.ContainsLocationFragment file tokens input fragment)
    (fragmentRooted : fragment.roots ≠ []) :
    input.locationFragment.roots ≠ [] :=
  LocationFragment.IsSubfragmentOf.roots_ne_nil
    inside.locationFragment_isSubfragment fragmentRooted

private theorem ofTypeExprList_eq_ofList (values : List TypeExpr) :
    LocationFragment.ofTypeExprList values =
      LocationFragment.ofList LocationFragment.ofTypeExpr values := by
  induction values with
  | nil => exact LocationFragment.merge_nil.symm
  | cons head tail inductionHypothesis =>
      apply LocationFragment.eq_of_fields <;>
        simp [LocationFragment.ofTypeExprList, LocationFragment.ofList,
          inductionHypothesis]

private theorem ofTypeExprArguments_some_eq_ofNonempty
    (values : NonemptyList TypeExpr) :
    LocationFragment.ofTypeExprArguments (some values) =
      LocationFragment.ofNonempty LocationFragment.ofTypeExpr values := by
  simp [LocationFragment.ofTypeExprArguments, LocationFragment.ofNonempty,
    ofTypeExprList_eq_ofList]

private theorem ofStatementList_eq_ofList (values : List Statement) :
    LocationFragment.ofStatementList values =
      LocationFragment.ofList LocationFragment.ofStatement values := by
  induction values with
  | nil => exact LocationFragment.merge_nil.symm
  | cons head tail inductionHypothesis =>
      apply LocationFragment.eq_of_fields <;>
        simp [LocationFragment.ofStatementList, LocationFragment.ofList,
          inductionHypothesis]

private theorem ofNonempty_eq_ofList_firstRest
    {alpha : Type} (visit : alpha → LocationFragment)
    (values : NonemptyList alpha) :
    LocationFragment.ofNonempty visit values =
      LocationFragment.ofList visit (RuleReduction.firstRest values) := by
  unfold LocationFragment.ofNonempty LocationFragment.ofList
    RuleReduction.firstRest
  exact LocationFragment.merge_cons_as_pair _ _ |>.symm

private theorem pragma_output_none_eq
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {kind : PragmaKind}
    (kindToken : MatchedTerminal file tokens (.pragmaName kind))
    (witness : ConsumedSpanWitness file tokens origin finish) :
    RuleLocationView.ofRuleValue .pragmaDecl
      (sourceLoc witness {
        kind := RuleReduction.terminalLoc kindToken kind
        targets := []
      }) =
      LocationFragment.located witness.span
        [LocationFragment.leaf kindToken.span] := by
  rw [RuleLocationView.ofRuleValue]
  change LocationFragment.located witness.span
    [LocationFragment.leaf kindToken.span,
      LocationFragment.ofList LocationFragment.ofIdentifier []] = _
  apply LocationFragment.eq_of_fields <;>
    simp [LocationFragment.ofList]

private theorem pragma_output_some_eq
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {kind : PragmaKind}
    (kindToken : MatchedTerminal file tokens (.pragmaName kind))
    (values : NonemptyList (RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier))
    (witness : ConsumedSpanWitness file tokens origin finish) :
    let retained := values.map fun name =>
      RuleReduction.terminalLoc name.matched name.parsed
    RuleLocationView.ofRuleValue .pragmaDecl
      (sourceLoc witness {
        kind := RuleReduction.terminalLoc kindToken kind
        targets := RuleReduction.firstRest retained
      }) =
      LocationFragment.located witness.span [LocationFragment.merge
        [LocationFragment.leaf kindToken.span,
          LocationFragment.ofNonempty LocationFragment.ofIdentifier retained]] := by
  dsimp only
  rw [RuleLocationView.ofRuleValue]
  change LocationFragment.located witness.span
    [LocationFragment.leaf kindToken.span,
      LocationFragment.ofList LocationFragment.ofIdentifier
        (RuleReduction.firstRest
          (values.map fun name =>
            RuleReduction.terminalLoc name.matched name.parsed))] = _
  rw [← ofNonempty_eq_ofList_firstRest]
  exact (LocationFragment.located_merge _ _).symm

private theorem pragma_targets_core_inside
    {file : WorkspaceFile} {tokens : List Token}
    {expression : EbnfExpr} {input : EbnfValue file tokens expression}
    {kind : PragmaKind}
    (kindToken : MatchedTerminal file tokens (.pragmaName kind))
    (values : NonemptyList (RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier))
    (kindInside : EbnfValue.ContainsLocationFragment file tokens input
      kindToken.locationFragment)
    (headInside : EbnfValue.ContainsLocationFragment file tokens input
      values.head.matched.locationFragment)
    (tailInside : ∀ name, name ∈ values.tail →
      EbnfValue.ContainsLocationFragment file tokens input
        name.matched.locationFragment) :
    (LocationFragment.merge [
      LocationFragment.leaf kindToken.span,
      LocationFragment.ofNonempty LocationFragment.ofIdentifier
        (values.map fun name =>
          RuleReduction.terminalLoc name.matched name.parsed)
    ]).IsSubfragmentOf input.locationFragment := by
  apply LocationFragment.IsSubfragmentOf.merge_pair
  · rw [leaf_terminal_eq _ (by simp)]
    exact kindInside.locationFragment_isSubfragment
  · unfold LocationFragment.ofNonempty
    apply LocationFragment.IsSubfragmentOf.merge_pair
    · change (LocationFragment.ofIdentifier
          (RuleReduction.terminalLoc values.head.matched
            values.head.parsed)).IsSubfragmentOf _
      rw [ofIdentifier_terminal_eq]
      exact headInside.locationFragment_isSubfragment
    · unfold LocationFragment.ofList
      apply LocationFragment.IsSubfragmentOf.merge_map
      intro target targetMember
      change target ∈ (values.tail.map fun name =>
        RuleReduction.terminalLoc name.matched name.parsed) at targetMember
      rw [List.mem_map] at targetMember
      rcases targetMember with ⟨name, nameMember, rfl⟩
      rw [ofIdentifier_terminal_eq]
      exact (tailInside name nameMember).locationFragment_isSubfragment

private theorem identifier_nonempty_core_inside
    {file : WorkspaceFile} {tokens : List Token}
    {expression : EbnfExpr} {input : EbnfValue file tokens expression}
    (values : NonemptyList (RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier))
    (headInside : EbnfValue.ContainsLocationFragment file tokens input
      values.head.matched.locationFragment)
    (tailInside : ∀ name, name ∈ values.tail →
      EbnfValue.ContainsLocationFragment file tokens input
        name.matched.locationFragment) :
    (LocationFragment.ofNonempty LocationFragment.ofIdentifier
      (values.map fun name =>
        RuleReduction.terminalLoc name.matched name.parsed)
    ).IsSubfragmentOf input.locationFragment := by
  unfold LocationFragment.ofNonempty
  apply LocationFragment.IsSubfragmentOf.merge_pair
  · change (LocationFragment.ofIdentifier
        (RuleReduction.terminalLoc values.head.matched
          values.head.parsed)).IsSubfragmentOf _
    rw [ofIdentifier_terminal_eq]
    exact headInside.locationFragment_isSubfragment
  · unfold LocationFragment.ofList
    apply LocationFragment.IsSubfragmentOf.merge_map
    intro value member
    change value ∈ (values.tail.map fun name =>
      RuleReduction.terminalLoc name.matched name.parsed) at member
    rw [List.mem_map] at member
    rcases member with ⟨name, nameMember, rfl⟩
    rw [ofIdentifier_terminal_eq]
    exact (tailInside name nameMember).locationFragment_isSubfragment

private theorem type_nonempty_core_inside
    {file : WorkspaceFile} {tokens : List Token}
    {expression : EbnfExpr} {input : EbnfValue file tokens expression}
    (values : NonemptyList TypeExpr)
    (headInside : EbnfValue.ContainsLocationFragment file tokens input
      (RuleLocationView.ofRuleValue .type values.head))
    (tailInside : ∀ value, value ∈ values.tail →
      EbnfValue.ContainsLocationFragment file tokens input
        (RuleLocationView.ofRuleValue .type value)) :
    (LocationFragment.ofNonempty LocationFragment.ofTypeExpr values
    ).IsSubfragmentOf input.locationFragment := by
  unfold LocationFragment.ofNonempty
  apply LocationFragment.IsSubfragmentOf.merge_pair
  · exact headInside.locationFragment_isSubfragment
  · unfold LocationFragment.ofList
    apply LocationFragment.IsSubfragmentOf.merge_map
    intro value member
    exact (tailInside value member).locationFragment_isSubfragment

theorem moduleRefStandard_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (first : MatchedTerminal file tokens (.category .pathComponent))
    (rest : List
      (MatchedTerminal file tokens (.symbol .dot) ×
        RuleReduction.SpelledTerminalData file tokens
          (.category .pathComponent) PathSegment))
    (rootMarker : RuleReduction.MarkerProjects file tokens first .standardRoot)
    (restProjects : ∀ entry, entry ∈ rest →
      PathSegmentProjects entry.2.matched entry.2.spelling entry.2.parsed)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.moduleRefStandard origin finish first rest rootMarker
        restProjects witness) := by
  let retainedRest := rest.map fun entry =>
    RuleReduction.terminalLoc entry.2.matched entry.2.parsed
  let restCore := LocationFragment.merge
    (rest.map fun entry => entry.2.matched.locationFragment)
  let core := LocationFragment.merge [first.locationFragment, restCore]
  apply WrappedLocation.projectedInput witness core
  · rw [RuleLocationView.ofRuleValue]
    change LocationFragment.located witness.span
      [LocationFragment.leaf first.span,
        LocationFragment.ofList
          (fun component : Located PathSegment =>
            LocationFragment.leaf component.span) retainedRest] =
        LocationFragment.located witness.span [core]
    apply LocationFragment.eq_of_fields <;>
      simp [core, restCore, retainedRest, LocationFragment.ofList,
        LocationFragment.leaf, MatchedTerminal.locationFragment,
        RuleReduction.terminalLoc, Function.comp_def]
  · apply LocationFragment.IsSubfragmentOf.merge_pair
    · apply
        EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.choice ⟨1, by decide⟩
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.terminal _ _
    · unfold restCore
      apply LocationFragment.IsSubfragmentOf.merge_map
      intro entry entryMember
      apply
        EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.choice ⟨1, by decide⟩
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      apply EbnfValue.ContainsLocationFragment.star
      · exact List.mem_map_of_mem entryMember
      · apply EbnfValue.ContainsLocationFragment.group
        apply EbnfValue.ContainsLocationFragment.sequence
        apply EbnfValues.ContainsLocationFragment.tail
        apply EbnfValues.ContainsLocationFragment.head
        exact EbnfValue.ContainsLocationFragment.terminal _ _
  · apply input_roots_ne_nil_of_inside
    · apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.choice ⟨1, by decide⟩
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.terminal _ _
    · simp [MatchedTerminal.locationFragment]

theorem moduleRefExternal_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (atToken : MatchedTerminal file tokens (.symbol .at))
    (library : RuleReduction.SpelledTerminalData file tokens
      (.category .pathComponent) ExternalLibraryName)
    (dot : MatchedTerminal file tokens (.symbol .dot))
    (next : RuleReduction.SpelledTerminalData file tokens
      (.category .pathComponent) PathSegment)
    (rest : List
      (MatchedTerminal file tokens (.symbol .dot) ×
        RuleReduction.SpelledTerminalData file tokens
          (.category .pathComponent) PathSegment))
    (atMarker : RuleReduction.MarkerProjects file tokens atToken .externalSigil)
    (libraryProjects : ExternalLibraryProjects library.matched
      library.spelling library.parsed)
    (nextProjects : PathSegmentProjects next.matched
      next.spelling next.parsed)
    (restProjects : ∀ entry, entry ∈ rest →
      PathSegmentProjects entry.2.matched entry.2.spelling entry.2.parsed)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.moduleRefExternal origin finish atToken library dot next
        rest atMarker libraryProjects nextProjects restProjects witness) := by
  let components : NonemptyList (Located PathSegment) := {
    head := RuleReduction.terminalLoc next.matched next.parsed
    tail := rest.map fun entry =>
      RuleReduction.terminalLoc entry.2.matched entry.2.parsed
  }
  let componentCore := LocationFragment.ofNonempty
    (fun component : Located PathSegment =>
      LocationFragment.leaf component.span) components
  let core := LocationFragment.merge
    [LocationFragment.leaf atToken.span,
      LocationFragment.leaf library.matched.span, componentCore]
  apply WrappedLocation.projectedInput witness core
  · rw [RuleLocationView.ofRuleValue]
    change LocationFragment.located witness.span
      [LocationFragment.leaf atToken.span,
        LocationFragment.leaf library.matched.span, componentCore] =
        LocationFragment.located witness.span [core]
    exact (LocationFragment.located_merge _ _).symm
  · apply LocationFragment.IsSubfragmentOf.merge
    intro fragment member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · rw [leaf_terminal_eq _ (by decide)]
      apply
        EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.choice ⟨0, by decide⟩
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.terminal _ _
    · rw [leaf_terminal_eq _ (by decide)]
      apply
        EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.choice ⟨0, by decide⟩
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.terminal _ _
    · unfold componentCore LocationFragment.ofNonempty
      apply LocationFragment.IsSubfragmentOf.merge_pair
      · change (LocationFragment.leaf next.matched.span).IsSubfragmentOf _
        rw [leaf_terminal_eq _ (by decide)]
        apply
          EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
        apply EbnfValue.ContainsLocationFragment.transport (by rfl)
        apply EbnfValue.ContainsLocationFragment.choice ⟨0, by decide⟩
        apply EbnfValue.ContainsLocationFragment.sequence
        apply EbnfValues.ContainsLocationFragment.tail
        apply EbnfValues.ContainsLocationFragment.tail
        apply EbnfValues.ContainsLocationFragment.tail
        apply EbnfValues.ContainsLocationFragment.head
        exact EbnfValue.ContainsLocationFragment.terminal _ _
      · unfold LocationFragment.ofList
        apply LocationFragment.IsSubfragmentOf.merge_map
        intro component componentMember
        change component ∈ (rest.map fun entry =>
          RuleReduction.terminalLoc entry.2.matched entry.2.parsed) at componentMember
        rw [List.mem_map] at componentMember
        rcases componentMember with ⟨entry, entryMember, rfl⟩
        change (LocationFragment.leaf entry.2.matched.span).IsSubfragmentOf _
        rw [leaf_terminal_eq _ (by decide)]
        apply
          EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
        apply EbnfValue.ContainsLocationFragment.transport (by rfl)
        apply EbnfValue.ContainsLocationFragment.choice ⟨0, by decide⟩
        apply EbnfValue.ContainsLocationFragment.sequence
        apply EbnfValues.ContainsLocationFragment.tail
        apply EbnfValues.ContainsLocationFragment.tail
        apply EbnfValues.ContainsLocationFragment.tail
        apply EbnfValues.ContainsLocationFragment.tail
        apply EbnfValues.ContainsLocationFragment.head
        apply EbnfValue.ContainsLocationFragment.star
        · exact List.mem_map_of_mem entryMember
        · apply EbnfValue.ContainsLocationFragment.group
          apply EbnfValue.ContainsLocationFragment.sequence
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.head
          exact EbnfValue.ContainsLocationFragment.terminal _ _
  · apply input_roots_ne_nil_of_inside
    · apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.choice ⟨0, by decide⟩
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.terminal _ _
    · simp [MatchedTerminal.locationFragment]

theorem moduleRefLibraryRoot_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (first : MatchedTerminal file tokens (.category .pathComponent))
    (nextDot : MatchedTerminal file tokens (.symbol .dot))
    (next : RuleReduction.SpelledTerminalData file tokens
      (.category .pathComponent) PathSegment)
    (remaining : List
      (MatchedTerminal file tokens (.symbol .dot) ×
        RuleReduction.SpelledTerminalData file tokens
          (.category .pathComponent) PathSegment))
    (rootMarker : RuleReduction.MarkerProjects file tokens first .libraryRoot)
    (nextProjects : PathSegmentProjects next.matched
      next.spelling next.parsed)
    (remainingProjects : ∀ entry, entry ∈ remaining →
      PathSegmentProjects entry.2.matched entry.2.spelling entry.2.parsed)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.moduleRefLibraryRoot origin finish first nextDot next
        remaining rootMarker nextProjects remainingProjects witness) := by
  let components : NonemptyList (Located PathSegment) := {
    head := RuleReduction.terminalLoc next.matched next.parsed
    tail := remaining.map fun entry =>
      RuleReduction.terminalLoc entry.2.matched entry.2.parsed
  }
  let componentCore := LocationFragment.ofNonempty
    (fun component : Located PathSegment =>
      LocationFragment.leaf component.span) components
  let core := LocationFragment.merge
    [LocationFragment.leaf first.span, componentCore]
  apply WrappedLocation.projectedInput witness core
  · rw [RuleLocationView.ofRuleValue]
    change LocationFragment.located witness.span
      [LocationFragment.leaf first.span, componentCore] =
        LocationFragment.located witness.span [core]
    exact (LocationFragment.located_merge _ _).symm
  · apply LocationFragment.IsSubfragmentOf.merge_pair
    · rw [leaf_terminal_eq _ (by decide)]
      apply
        EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.choice ⟨1, by decide⟩
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.terminal _ _
    · unfold componentCore LocationFragment.ofNonempty
      apply LocationFragment.IsSubfragmentOf.merge_pair
      · change (LocationFragment.leaf next.matched.span).IsSubfragmentOf _
        rw [leaf_terminal_eq _ (by decide)]
        apply
          EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
        apply EbnfValue.ContainsLocationFragment.transport (by rfl)
        apply EbnfValue.ContainsLocationFragment.choice ⟨1, by decide⟩
        apply EbnfValue.ContainsLocationFragment.sequence
        apply EbnfValues.ContainsLocationFragment.tail
        apply EbnfValues.ContainsLocationFragment.head
        apply EbnfValue.ContainsLocationFragment.star
        · exact List.mem_cons_self
        · apply EbnfValue.ContainsLocationFragment.group
          apply EbnfValue.ContainsLocationFragment.sequence
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.head
          exact EbnfValue.ContainsLocationFragment.terminal _ _
      · unfold LocationFragment.ofList
        apply LocationFragment.IsSubfragmentOf.merge_map
        intro component componentMember
        change component ∈ (remaining.map fun entry =>
          RuleReduction.terminalLoc entry.2.matched entry.2.parsed) at componentMember
        rw [List.mem_map] at componentMember
        rcases componentMember with ⟨entry, entryMember, rfl⟩
        change (LocationFragment.leaf entry.2.matched.span).IsSubfragmentOf _
        rw [leaf_terminal_eq _ (by decide)]
        apply
          EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
        apply EbnfValue.ContainsLocationFragment.transport (by rfl)
        apply EbnfValue.ContainsLocationFragment.choice ⟨1, by decide⟩
        apply EbnfValue.ContainsLocationFragment.sequence
        apply EbnfValues.ContainsLocationFragment.tail
        apply EbnfValues.ContainsLocationFragment.head
        apply EbnfValue.ContainsLocationFragment.star
        · simp only [List.mem_cons, List.mem_map]
          exact Or.inr ⟨entry, entryMember, rfl⟩
        · apply EbnfValue.ContainsLocationFragment.group
          apply EbnfValue.ContainsLocationFragment.sequence
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.head
          exact EbnfValue.ContainsLocationFragment.terminal _ _
  · apply input_roots_ne_nil_of_inside
    · apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.choice ⟨1, by decide⟩
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.terminal _ _
    · simp [MatchedTerminal.locationFragment]

theorem moduleRefRelativeOther_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (first : RuleReduction.SpelledTerminalData file tokens
      (.category .pathComponent) PathSegment)
    (rest : List
      (MatchedTerminal file tokens (.symbol .dot) ×
        RuleReduction.SpelledTerminalData file tokens
          (.category .pathComponent) PathSegment))
    (firstProjects : PathSegmentProjects first.matched
      first.spelling first.parsed)
    (restProjects : ∀ entry, entry ∈ rest →
      PathSegmentProjects entry.2.matched entry.2.spelling entry.2.parsed)
    (notStandard : first.spelling ≠ "std")
    (notLibrary : first.spelling ≠ "lib")
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.moduleRefRelativeOther origin finish first rest
        firstProjects restProjects notStandard notLibrary witness) := by
  let components : NonemptyList (Located PathSegment) := {
    head := RuleReduction.terminalLoc first.matched first.parsed
    tail := rest.map fun entry =>
      RuleReduction.terminalLoc entry.2.matched entry.2.parsed
  }
  let core := LocationFragment.ofNonempty
    (fun component : Located PathSegment =>
      LocationFragment.leaf component.span) components
  apply WrappedLocation.projectedInput witness core
  · rw [RuleLocationView.ofRuleValue]
    change LocationFragment.located witness.span
      [LocationFragment.ofNonempty
        (fun component : Located PathSegment =>
          LocationFragment.leaf component.span) components] =
        LocationFragment.located witness.span [core]
    rfl
  · unfold core LocationFragment.ofNonempty
    apply LocationFragment.IsSubfragmentOf.merge_pair
    · change (LocationFragment.leaf first.matched.span).IsSubfragmentOf _
      rw [leaf_terminal_eq _ (by decide)]
      apply
        EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.choice ⟨1, by decide⟩
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.terminal _ _
    · unfold LocationFragment.ofList
      apply LocationFragment.IsSubfragmentOf.merge_map
      intro component componentMember
      change component ∈ (rest.map fun entry =>
        RuleReduction.terminalLoc entry.2.matched entry.2.parsed) at componentMember
      rw [List.mem_map] at componentMember
      rcases componentMember with ⟨entry, entryMember, rfl⟩
      change (LocationFragment.leaf entry.2.matched.span).IsSubfragmentOf _
      rw [leaf_terminal_eq _ (by decide)]
      apply
        EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.choice ⟨1, by decide⟩
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      apply EbnfValue.ContainsLocationFragment.star
      · exact List.mem_map_of_mem entryMember
      · apply EbnfValue.ContainsLocationFragment.group
        apply EbnfValue.ContainsLocationFragment.sequence
        apply EbnfValues.ContainsLocationFragment.tail
        apply EbnfValues.ContainsLocationFragment.head
        exact EbnfValue.ContainsLocationFragment.terminal _ _
  · apply input_roots_ne_nil_of_inside
    · apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.choice ⟨1, by decide⟩
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.terminal _ _
    · simp [MatchedTerminal.locationFragment]

theorem importDeclModule_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (importKw : MatchedTerminal file tokens (.hardKeyword .importKw))
    (reference : ModuleReference)
    (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.importDeclModule origin finish importKw reference
        semicolon witness) := by
  let core := LocationFragment.ofModuleReference reference
  apply WrappedLocation.projectedInput witness core
  · rw [RuleLocationView.ofRuleValue,
      LocationFragment.ofImportDecl_mk]
    apply LocationFragment.eq_of_fields <;>
      simp [core, sourceLoc, LocationFragment.ofImportMode,
        LocationFragment.ofOption]
  · apply
      EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
    apply EbnfValue.ContainsLocationFragment.transport (by rfl)
    apply EbnfValue.ContainsLocationFragment.choice ⟨0, by decide⟩
    apply EbnfValue.ContainsLocationFragment.sequence
    apply EbnfValues.ContainsLocationFragment.tail
    apply EbnfValues.ContainsLocationFragment.head
    exact EbnfValue.ContainsLocationFragment.rule .moduleRef reference
  · apply input_roots_ne_nil_of_inside
    · apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.choice ⟨0, by decide⟩
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.rule .moduleRef reference
    · simp [RuleLocationView.ofRuleValue]

theorem importDeclAliased_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (importKw : MatchedTerminal file tokens (.hardKeyword .importKw))
    (reference : ModuleReference)
    (asKw : MatchedTerminal file tokens (.hardKeyword .asKw))
    (name : RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier)
    (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
    (nameProjects : IdentifierProjects name.matched name.spelling name.parsed)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.importDeclAliased origin finish importKw reference asKw
        name semicolon nameProjects witness) := by
  let alias := RuleReduction.terminalLoc name.matched name.parsed
  let core := LocationFragment.merge
    [LocationFragment.ofModuleReference reference,
      LocationFragment.ofIdentifier alias]
  apply WrappedLocation.projectedInput witness core
  · rw [RuleLocationView.ofRuleValue,
      LocationFragment.ofImportDecl_mk]
    simp [core, alias, sourceLoc, LocationFragment.ofImportMode,
      LocationFragment.ofOption]
  · apply LocationFragment.IsSubfragmentOf.merge_pair
    · apply
        EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.choice ⟨1, by decide⟩
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.rule .moduleRef reference
    · rw [ofIdentifier_terminal_eq]
      apply
        EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.choice ⟨1, by decide⟩
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.terminal _ _
  · apply input_roots_ne_nil_of_inside
    · apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.choice ⟨1, by decide⟩
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.rule .moduleRef reference
    · simp [RuleLocationView.ofRuleValue]

theorem exportDeclModule_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (exportKw : MatchedTerminal file tokens (.hardKeyword .exportKw))
    (reference : ModuleReference)
    (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.exportDeclModule origin finish exportKw reference
        semicolon witness) := by
  let core := LocationFragment.ofModuleReference reference
  apply WrappedLocation.projectedInput witness core
  · change LocationFragment.ofExportDecl
      ⟨witness.span, .module reference none⟩ =
        LocationFragment.located witness.span [core]
    rw [LocationFragment.ofExportDecl_module]
    apply LocationFragment.eq_of_fields <;>
      simp [core, LocationFragment.ofOption]
  · apply
      EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
    apply EbnfValue.ContainsLocationFragment.transport (by rfl)
    apply EbnfValue.ContainsLocationFragment.choice ⟨1, by decide⟩
    apply EbnfValue.ContainsLocationFragment.sequence
    apply EbnfValues.ContainsLocationFragment.tail
    apply EbnfValues.ContainsLocationFragment.head
    exact EbnfValue.ContainsLocationFragment.rule .moduleRef reference
  · apply input_roots_ne_nil_of_inside
    · apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.choice ⟨1, by decide⟩
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.rule .moduleRef reference
    · simp [RuleLocationView.ofRuleValue]

theorem exportDeclAliased_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (exportKw : MatchedTerminal file tokens (.hardKeyword .exportKw))
    (reference : ModuleReference)
    (asKw : MatchedTerminal file tokens (.hardKeyword .asKw))
    (name : RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier)
    (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
    (nameProjects : IdentifierProjects name.matched name.spelling name.parsed)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.exportDeclAliased origin finish exportKw reference asKw
        name semicolon nameProjects witness) := by
  let alias := RuleReduction.terminalLoc name.matched name.parsed
  let core := LocationFragment.merge
    [LocationFragment.ofModuleReference reference,
      LocationFragment.ofIdentifier alias]
  apply WrappedLocation.projectedInput witness core
  · change LocationFragment.ofExportDecl
      ⟨witness.span, .module reference (some alias)⟩ =
        LocationFragment.located witness.span [core]
    rw [LocationFragment.ofExportDecl_module]
    exact (LocationFragment.located_merge _ _).symm
  · apply LocationFragment.IsSubfragmentOf.merge_pair
    · apply
        EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.choice ⟨2, by decide⟩
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.rule .moduleRef reference
    · rw [ofIdentifier_terminal_eq]
      apply
        EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.choice ⟨2, by decide⟩
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.terminal _ _
  · apply input_roots_ne_nil_of_inside
    · apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.choice ⟨2, by decide⟩
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.rule .moduleRef reference
    · simp [RuleLocationView.ofRuleValue]

theorem importEntryAliased_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (name alias : RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier)
    (asKw : MatchedTerminal file tokens (.hardKeyword .asKw))
    (nameProjects : IdentifierProjects name.matched name.spelling name.parsed)
    (aliasProjects : IdentifierProjects alias.matched alias.spelling
      alias.parsed)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.importEntryAliased origin finish name alias asKw
        nameProjects aliasProjects witness) := by
  let retainedName := RuleReduction.terminalLoc name.matched name.parsed
  let retainedAlias := RuleReduction.terminalLoc alias.matched alias.parsed
  let core := LocationFragment.merge
    [LocationFragment.ofIdentifier retainedName,
      LocationFragment.ofIdentifier retainedAlias]
  apply WrappedLocation.projectedInput witness core
  · change LocationFragment.located witness.span
      [LocationFragment.ofIdentifier retainedName,
        LocationFragment.ofIdentifier retainedAlias] =
        LocationFragment.located witness.span [core]
    exact (LocationFragment.located_merge _ _).symm
  · apply LocationFragment.IsSubfragmentOf.merge_pair
    · rw [ofIdentifier_terminal_eq]
      apply
        EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.choice ⟨1, by decide⟩
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.terminal _ _
    · rw [ofIdentifier_terminal_eq]
      apply
        EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.choice ⟨1, by decide⟩
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      apply EbnfValue.ContainsLocationFragment.optional
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.terminal _ _
  · apply input_roots_ne_nil_of_inside
    · apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.choice ⟨1, by decide⟩
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.terminal _ _
    · simp [MatchedTerminal.locationFragment]

theorem constructorSelectionAll_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (openParen : MatchedTerminal file tokens (.symbol .leftParen))
    (star : MatchedTerminal file tokens (.symbol .star))
    (closeParen : MatchedTerminal file tokens (.symbol .rightParen))
    (starMarker : RuleReduction.MarkerProjects file tokens star .wildcard)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.constructorSelectionAll origin finish openParen star
        closeParen starMarker witness) := by
  let core := star.locationFragment
  apply WrappedLocation.projectedInput witness core
  · change LocationFragment.located witness.span
      [LocationFragment.leaf star.span] =
        LocationFragment.located witness.span [core]
    apply LocationFragment.eq_of_fields <;>
      simp [core, LocationFragment.leaf,
        MatchedTerminal.locationFragment]
  · apply
      EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
    apply EbnfValue.ContainsLocationFragment.transport (by rfl)
    apply EbnfValue.ContainsLocationFragment.choice ⟨0, by decide⟩
    apply EbnfValue.ContainsLocationFragment.sequence
    apply EbnfValues.ContainsLocationFragment.tail
    apply EbnfValues.ContainsLocationFragment.head
    exact EbnfValue.ContainsLocationFragment.terminal _ _
  · apply input_roots_ne_nil_of_inside
    · apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.choice ⟨0, by decide⟩
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.terminal _ _
    · simp [MatchedTerminal.locationFragment]

theorem constructorSelectionNamed_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (openParen : MatchedTerminal file tokens (.symbol .leftParen))
    (names : NonemptyList (RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier))
    (closeParen : MatchedTerminal file tokens (.symbol .rightParen))
    (headProjects : IdentifierProjects names.head.matched
      names.head.spelling names.head.parsed)
    (tailProjects : ∀ name, name ∈ names.tail →
      IdentifierProjects name.matched name.spelling name.parsed)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.constructorSelectionNamed origin finish openParen names
        closeParen headProjects tailProjects witness) := by
  let retained := names.map fun name =>
    RuleReduction.terminalLoc name.matched name.parsed
  let core := LocationFragment.ofNonempty
    LocationFragment.ofIdentifier retained
  apply WrappedLocation.projectedInput witness core
  · change LocationFragment.located witness.span
      [LocationFragment.ofNonempty LocationFragment.ofIdentifier retained] =
        LocationFragment.located witness.span [core]
    rfl
  · unfold core LocationFragment.ofNonempty
    apply LocationFragment.IsSubfragmentOf.merge_pair
    · change (LocationFragment.ofIdentifier
          (RuleReduction.terminalLoc names.head.matched
            names.head.parsed)).IsSubfragmentOf _
      rw [ofIdentifier_terminal_eq]
      apply
        EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.choice ⟨1, by decide⟩
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      apply EbnfValue.ContainsLocationFragment.list1Head
      exact EbnfValue.ContainsLocationFragment.terminal _ _
    · unfold LocationFragment.ofList
      apply LocationFragment.IsSubfragmentOf.merge_map
      intro value member
      change value ∈
        (names.tail.map fun name =>
          RuleReduction.terminalLoc name.matched name.parsed) at member
      rw [List.mem_map] at member
      rcases member with ⟨name, nameMember, rfl⟩
      rw [ofIdentifier_terminal_eq]
      apply
        EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.choice ⟨1, by decide⟩
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      apply EbnfValue.ContainsLocationFragment.list1Tail
      · exact List.mem_map_of_mem nameMember
      · exact EbnfValue.ContainsLocationFragment.terminal _ _
  · apply input_roots_ne_nil_of_inside
    · apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.choice ⟨1, by decide⟩
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      apply EbnfValue.ContainsLocationFragment.list1Head
      exact EbnfValue.ContainsLocationFragment.terminal _ _
    · simp [MatchedTerminal.locationFragment]

theorem pragmaDeclNoCoverageCondition_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (pragmaKw : MatchedTerminal file tokens (.hardKeyword .pragmaKw))
    (kindToken : MatchedTerminal file tokens
      (.pragmaName .noCoverageCondition))
    (targets : Option (NonemptyList
      (RuleReduction.SpelledTerminalData file tokens
        (.category .identifier) Identifier)))
    (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
    (targetProjects : ∀ values, targets = some values →
      IdentifierProjects values.head.matched
        values.head.spelling values.head.parsed ∧
      ∀ name, name ∈ values.tail →
        IdentifierProjects name.matched name.spelling name.parsed)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.pragmaDeclNoCoverageCondition origin finish pragmaKw
        kindToken targets semicolon targetProjects witness) := by
  cases targets with
  | none =>
      let core := LocationFragment.leaf kindToken.span
      apply WrappedLocation.projectedInput witness core
      · rw [RuleLocationView.ofRuleValue]
        change LocationFragment.located witness.span
          [LocationFragment.leaf kindToken.span,
            LocationFragment.ofList LocationFragment.ofIdentifier []] =
            LocationFragment.located witness.span [core]
        apply LocationFragment.eq_of_fields <;>
          simp [core, LocationFragment.ofList]
      · change (LocationFragment.leaf kindToken.span).IsSubfragmentOf _
        rw [leaf_terminal_eq _ (by decide)]
        apply
          EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
        apply EbnfValue.ContainsLocationFragment.transport (by rfl)
        apply EbnfValue.ContainsLocationFragment.choice ⟨0, by decide⟩
        apply EbnfValue.ContainsLocationFragment.sequence
        apply EbnfValues.ContainsLocationFragment.tail
        apply EbnfValues.ContainsLocationFragment.head
        exact EbnfValue.ContainsLocationFragment.terminal _ _
      · apply input_roots_ne_nil_of_inside
        · apply EbnfValue.ContainsLocationFragment.transport (by rfl)
          apply EbnfValue.ContainsLocationFragment.choice ⟨0, by decide⟩
          apply EbnfValue.ContainsLocationFragment.sequence
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.head
          exact EbnfValue.ContainsLocationFragment.terminal _ _
        · simp [MatchedTerminal.locationFragment]
  | some values =>
      let retained := values.map fun name =>
        RuleReduction.terminalLoc name.matched name.parsed
      let targetCore := LocationFragment.ofNonempty
        LocationFragment.ofIdentifier retained
      let core := LocationFragment.merge
        [LocationFragment.leaf kindToken.span, targetCore]
      apply WrappedLocation.projectedInput witness core
      · rw [RuleLocationView.ofRuleValue]
        change LocationFragment.located witness.span
          [LocationFragment.leaf kindToken.span,
            LocationFragment.ofList LocationFragment.ofIdentifier
              (RuleReduction.firstRest retained)] =
            LocationFragment.located witness.span [core]
        rw [← ofNonempty_eq_ofList_firstRest]
        exact (LocationFragment.located_merge _ _).symm
      · apply LocationFragment.IsSubfragmentOf.merge_pair
        · change (LocationFragment.leaf kindToken.span).IsSubfragmentOf _
          rw [leaf_terminal_eq _ (by decide)]
          apply
            EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
          apply EbnfValue.ContainsLocationFragment.transport (by rfl)
          apply EbnfValue.ContainsLocationFragment.choice ⟨0, by decide⟩
          apply EbnfValue.ContainsLocationFragment.sequence
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.head
          exact EbnfValue.ContainsLocationFragment.terminal _ _
        · unfold targetCore LocationFragment.ofNonempty
          apply LocationFragment.IsSubfragmentOf.merge_pair
          · change (LocationFragment.ofIdentifier
                (RuleReduction.terminalLoc values.head.matched
                  values.head.parsed)).IsSubfragmentOf _
            rw [ofIdentifier_terminal_eq]
            apply
              EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
            apply EbnfValue.ContainsLocationFragment.transport (by rfl)
            apply EbnfValue.ContainsLocationFragment.choice ⟨0, by decide⟩
            apply EbnfValue.ContainsLocationFragment.sequence
            apply EbnfValues.ContainsLocationFragment.tail
            apply EbnfValues.ContainsLocationFragment.tail
            apply EbnfValues.ContainsLocationFragment.head
            apply EbnfValue.ContainsLocationFragment.optional
            apply EbnfValue.ContainsLocationFragment.list1Head
            exact EbnfValue.ContainsLocationFragment.terminal _ _
          · unfold LocationFragment.ofList
            apply LocationFragment.IsSubfragmentOf.merge_map
            intro target targetMember
            change target ∈ (values.tail.map fun name =>
              RuleReduction.terminalLoc name.matched name.parsed) at targetMember
            rw [List.mem_map] at targetMember
            rcases targetMember with ⟨name, nameMember, rfl⟩
            rw [ofIdentifier_terminal_eq]
            apply
              EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
            apply EbnfValue.ContainsLocationFragment.transport (by rfl)
            apply EbnfValue.ContainsLocationFragment.choice ⟨0, by decide⟩
            apply EbnfValue.ContainsLocationFragment.sequence
            apply EbnfValues.ContainsLocationFragment.tail
            apply EbnfValues.ContainsLocationFragment.tail
            apply EbnfValues.ContainsLocationFragment.head
            apply EbnfValue.ContainsLocationFragment.optional
            apply EbnfValue.ContainsLocationFragment.list1Tail
            · exact List.mem_map_of_mem nameMember
            · exact EbnfValue.ContainsLocationFragment.terminal _ _
      · apply input_roots_ne_nil_of_inside
        · apply EbnfValue.ContainsLocationFragment.transport (by rfl)
          apply EbnfValue.ContainsLocationFragment.choice ⟨0, by decide⟩
          apply EbnfValue.ContainsLocationFragment.sequence
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.head
          exact EbnfValue.ContainsLocationFragment.terminal _ _
        · simp [MatchedTerminal.locationFragment]

theorem pragmaDeclNoPattersonCondition_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (pragmaKw : MatchedTerminal file tokens (.hardKeyword .pragmaKw))
    (kindToken : MatchedTerminal file tokens
      (.pragmaName .noPattersonCondition))
    (targets : Option (NonemptyList
      (RuleReduction.SpelledTerminalData file tokens
        (.category .identifier) Identifier)))
    (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
    (targetProjects : ∀ values, targets = some values →
      IdentifierProjects values.head.matched
        values.head.spelling values.head.parsed ∧
      ∀ name, name ∈ values.tail →
        IdentifierProjects name.matched name.spelling name.parsed)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.pragmaDeclNoPattersonCondition origin finish pragmaKw
        kindToken targets semicolon targetProjects witness) := by
  cases targets with
  | none =>
      let core := LocationFragment.leaf kindToken.span
      apply WrappedLocation.projectedInput witness core
      · simpa [core] using pragma_output_none_eq kindToken witness
      · change (LocationFragment.leaf kindToken.span).IsSubfragmentOf _
        rw [leaf_terminal_eq _ (by decide)]
        apply
          EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
        apply EbnfValue.ContainsLocationFragment.transport (by rfl)
        apply EbnfValue.ContainsLocationFragment.choice ⟨1, by decide⟩
        apply EbnfValue.ContainsLocationFragment.sequence
        apply EbnfValues.ContainsLocationFragment.tail
        apply EbnfValues.ContainsLocationFragment.head
        exact EbnfValue.ContainsLocationFragment.terminal _ _
      · apply input_roots_ne_nil_of_inside
        · apply EbnfValue.ContainsLocationFragment.transport (by rfl)
          apply EbnfValue.ContainsLocationFragment.choice ⟨1, by decide⟩
          apply EbnfValue.ContainsLocationFragment.sequence
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.head
          exact EbnfValue.ContainsLocationFragment.terminal _ _
        · simp [MatchedTerminal.locationFragment]
  | some values =>
      let core := LocationFragment.merge [
        LocationFragment.leaf kindToken.span,
        LocationFragment.ofNonempty LocationFragment.ofIdentifier
          (values.map fun name =>
            RuleReduction.terminalLoc name.matched name.parsed)]
      apply WrappedLocation.projectedInput witness core
      · simpa [core] using pragma_output_some_eq kindToken values witness
      · change (LocationFragment.merge [
          LocationFragment.leaf kindToken.span,
          LocationFragment.ofNonempty LocationFragment.ofIdentifier
            (values.map fun name =>
              RuleReduction.terminalLoc name.matched name.parsed)]
          ).IsSubfragmentOf _
        apply pragma_targets_core_inside kindToken values
        · apply EbnfValue.ContainsLocationFragment.transport (by rfl)
          apply EbnfValue.ContainsLocationFragment.choice ⟨1, by decide⟩
          apply EbnfValue.ContainsLocationFragment.sequence
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.head
          exact EbnfValue.ContainsLocationFragment.terminal _ _
        · apply EbnfValue.ContainsLocationFragment.transport (by rfl)
          apply EbnfValue.ContainsLocationFragment.choice ⟨1, by decide⟩
          apply EbnfValue.ContainsLocationFragment.sequence
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.head
          apply EbnfValue.ContainsLocationFragment.optional
          apply EbnfValue.ContainsLocationFragment.list1Head
          exact EbnfValue.ContainsLocationFragment.terminal _ _
        · intro name nameMember
          apply EbnfValue.ContainsLocationFragment.transport (by rfl)
          apply EbnfValue.ContainsLocationFragment.choice ⟨1, by decide⟩
          apply EbnfValue.ContainsLocationFragment.sequence
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.head
          apply EbnfValue.ContainsLocationFragment.optional
          apply EbnfValue.ContainsLocationFragment.list1Tail
          · exact List.mem_map_of_mem nameMember
          · exact EbnfValue.ContainsLocationFragment.terminal _ _
      · apply input_roots_ne_nil_of_inside
        · apply EbnfValue.ContainsLocationFragment.transport (by rfl)
          apply EbnfValue.ContainsLocationFragment.choice ⟨1, by decide⟩
          apply EbnfValue.ContainsLocationFragment.sequence
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.head
          exact EbnfValue.ContainsLocationFragment.terminal _ _
        · simp [MatchedTerminal.locationFragment]

theorem pragmaDeclNoBoundedVariableCondition_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (pragmaKw : MatchedTerminal file tokens (.hardKeyword .pragmaKw))
    (kindToken : MatchedTerminal file tokens
      (.pragmaName .noBoundedVariableCondition))
    (targets : Option (NonemptyList
      (RuleReduction.SpelledTerminalData file tokens
        (.category .identifier) Identifier)))
    (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
    (targetProjects : ∀ values, targets = some values →
      IdentifierProjects values.head.matched
        values.head.spelling values.head.parsed ∧
      ∀ name, name ∈ values.tail →
        IdentifierProjects name.matched name.spelling name.parsed)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.pragmaDeclNoBoundedVariableCondition origin finish
        pragmaKw kindToken targets semicolon targetProjects witness) := by
  cases targets with
  | none =>
      let core := LocationFragment.leaf kindToken.span
      apply WrappedLocation.projectedInput witness core
      · simpa [core] using pragma_output_none_eq kindToken witness
      · change (LocationFragment.leaf kindToken.span).IsSubfragmentOf _
        rw [leaf_terminal_eq _ (by decide)]
        apply
          EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
        apply EbnfValue.ContainsLocationFragment.transport (by rfl)
        apply EbnfValue.ContainsLocationFragment.choice ⟨2, by decide⟩
        apply EbnfValue.ContainsLocationFragment.sequence
        apply EbnfValues.ContainsLocationFragment.tail
        apply EbnfValues.ContainsLocationFragment.head
        exact EbnfValue.ContainsLocationFragment.terminal _ _
      · apply input_roots_ne_nil_of_inside
        · apply EbnfValue.ContainsLocationFragment.transport (by rfl)
          apply EbnfValue.ContainsLocationFragment.choice ⟨2, by decide⟩
          apply EbnfValue.ContainsLocationFragment.sequence
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.head
          exact EbnfValue.ContainsLocationFragment.terminal _ _
        · simp [MatchedTerminal.locationFragment]
  | some values =>
      let core := LocationFragment.merge [
        LocationFragment.leaf kindToken.span,
        LocationFragment.ofNonempty LocationFragment.ofIdentifier
          (values.map fun name =>
            RuleReduction.terminalLoc name.matched name.parsed)]
      apply WrappedLocation.projectedInput witness core
      · simpa [core] using pragma_output_some_eq kindToken values witness
      · change (LocationFragment.merge [
          LocationFragment.leaf kindToken.span,
          LocationFragment.ofNonempty LocationFragment.ofIdentifier
            (values.map fun name =>
              RuleReduction.terminalLoc name.matched name.parsed)]
          ).IsSubfragmentOf _
        apply pragma_targets_core_inside kindToken values
        · apply EbnfValue.ContainsLocationFragment.transport (by rfl)
          apply EbnfValue.ContainsLocationFragment.choice ⟨2, by decide⟩
          apply EbnfValue.ContainsLocationFragment.sequence
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.head
          exact EbnfValue.ContainsLocationFragment.terminal _ _
        · apply EbnfValue.ContainsLocationFragment.transport (by rfl)
          apply EbnfValue.ContainsLocationFragment.choice ⟨2, by decide⟩
          apply EbnfValue.ContainsLocationFragment.sequence
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.head
          apply EbnfValue.ContainsLocationFragment.optional
          apply EbnfValue.ContainsLocationFragment.list1Head
          exact EbnfValue.ContainsLocationFragment.terminal _ _
        · intro name nameMember
          apply EbnfValue.ContainsLocationFragment.transport (by rfl)
          apply EbnfValue.ContainsLocationFragment.choice ⟨2, by decide⟩
          apply EbnfValue.ContainsLocationFragment.sequence
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.head
          apply EbnfValue.ContainsLocationFragment.optional
          apply EbnfValue.ContainsLocationFragment.list1Tail
          · exact List.mem_map_of_mem nameMember
          · exact EbnfValue.ContainsLocationFragment.terminal _ _
      · apply input_roots_ne_nil_of_inside
        · apply EbnfValue.ContainsLocationFragment.transport (by rfl)
          apply EbnfValue.ContainsLocationFragment.choice ⟨2, by decide⟩
          apply EbnfValue.ContainsLocationFragment.sequence
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.head
          exact EbnfValue.ContainsLocationFragment.terminal _ _
        · simp [MatchedTerminal.locationFragment]

theorem pragmaDeclNoGenericInstanceFor_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (pragmaKw : MatchedTerminal file tokens (.hardKeyword .pragmaKw))
    (kindToken : MatchedTerminal file tokens
      (.pragmaName .noGenericInstanceFor))
    (targets : Option (NonemptyList
      (RuleReduction.SpelledTerminalData file tokens
        (.category .identifier) Identifier)))
    (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
    (targetProjects : ∀ values, targets = some values →
      IdentifierProjects values.head.matched
        values.head.spelling values.head.parsed ∧
      ∀ name, name ∈ values.tail →
        IdentifierProjects name.matched name.spelling name.parsed)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.pragmaDeclNoGenericInstanceFor origin finish pragmaKw
        kindToken targets semicolon targetProjects witness) := by
  cases targets with
  | none =>
      let core := LocationFragment.leaf kindToken.span
      apply WrappedLocation.projectedInput witness core
      · simpa [core] using pragma_output_none_eq kindToken witness
      · change (LocationFragment.leaf kindToken.span).IsSubfragmentOf _
        rw [leaf_terminal_eq _ (by decide)]
        apply
          EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
        apply EbnfValue.ContainsLocationFragment.transport (by rfl)
        apply EbnfValue.ContainsLocationFragment.choice ⟨3, by decide⟩
        apply EbnfValue.ContainsLocationFragment.sequence
        apply EbnfValues.ContainsLocationFragment.tail
        apply EbnfValues.ContainsLocationFragment.head
        exact EbnfValue.ContainsLocationFragment.terminal _ _
      · apply input_roots_ne_nil_of_inside
        · apply EbnfValue.ContainsLocationFragment.transport (by rfl)
          apply EbnfValue.ContainsLocationFragment.choice ⟨3, by decide⟩
          apply EbnfValue.ContainsLocationFragment.sequence
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.head
          exact EbnfValue.ContainsLocationFragment.terminal _ _
        · simp [MatchedTerminal.locationFragment]
  | some values =>
      let core := LocationFragment.merge [
        LocationFragment.leaf kindToken.span,
        LocationFragment.ofNonempty LocationFragment.ofIdentifier
          (values.map fun name =>
            RuleReduction.terminalLoc name.matched name.parsed)]
      apply WrappedLocation.projectedInput witness core
      · simpa [core] using pragma_output_some_eq kindToken values witness
      · change (LocationFragment.merge [
          LocationFragment.leaf kindToken.span,
          LocationFragment.ofNonempty LocationFragment.ofIdentifier
            (values.map fun name =>
              RuleReduction.terminalLoc name.matched name.parsed)]
          ).IsSubfragmentOf _
        apply pragma_targets_core_inside kindToken values
        · apply EbnfValue.ContainsLocationFragment.transport (by rfl)
          apply EbnfValue.ContainsLocationFragment.choice ⟨3, by decide⟩
          apply EbnfValue.ContainsLocationFragment.sequence
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.head
          exact EbnfValue.ContainsLocationFragment.terminal _ _
        · apply EbnfValue.ContainsLocationFragment.transport (by rfl)
          apply EbnfValue.ContainsLocationFragment.choice ⟨3, by decide⟩
          apply EbnfValue.ContainsLocationFragment.sequence
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.head
          apply EbnfValue.ContainsLocationFragment.optional
          apply EbnfValue.ContainsLocationFragment.list1Head
          exact EbnfValue.ContainsLocationFragment.terminal _ _
        · intro name nameMember
          apply EbnfValue.ContainsLocationFragment.transport (by rfl)
          apply EbnfValue.ContainsLocationFragment.choice ⟨3, by decide⟩
          apply EbnfValue.ContainsLocationFragment.sequence
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.head
          apply EbnfValue.ContainsLocationFragment.optional
          apply EbnfValue.ContainsLocationFragment.list1Tail
          · exact List.mem_map_of_mem nameMember
          · exact EbnfValue.ContainsLocationFragment.terminal _ _
      · apply input_roots_ne_nil_of_inside
        · apply EbnfValue.ContainsLocationFragment.transport (by rfl)
          apply EbnfValue.ContainsLocationFragment.choice ⟨3, by decide⟩
          apply EbnfValue.ContainsLocationFragment.sequence
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.head
          exact EbnfValue.ContainsLocationFragment.terminal _ _
        · simp [MatchedTerminal.locationFragment]

theorem localExportEntryAllFrom_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (reference : ModuleReference)
    (dot : MatchedTerminal file tokens (.symbol .dot))
    (star : MatchedTerminal file tokens (.symbol .star))
    (starMarker : RuleReduction.MarkerProjects file tokens star .wildcard)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.localExportEntryAllFrom origin finish reference dot star
        starMarker witness) := by
  let core := LocationFragment.merge
    [LocationFragment.ofModuleReference reference, star.locationFragment]
  apply WrappedLocation.projectedInput witness core
  · change LocationFragment.located witness.span
      [LocationFragment.ofModuleReference reference,
        LocationFragment.leaf star.span] =
        LocationFragment.located witness.span [core]
    apply LocationFragment.eq_of_fields <;>
      simp [core, LocationFragment.leaf,
        MatchedTerminal.locationFragment]
  · apply LocationFragment.IsSubfragmentOf.merge_pair
    · apply
        EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.choice ⟨2, by decide⟩
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.rule .moduleRef reference
    · apply
        EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.choice ⟨2, by decide⟩
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.terminal _ _
  · apply input_roots_ne_nil_of_inside
    · apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.choice ⟨2, by decide⟩
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.rule .moduleRef reference
    · simp [RuleLocationView.ofRuleValue]

theorem forallBinderBoundedWithoutArguments_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (name : RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier)
    (colon : MatchedTerminal file tokens (.symbol .colon))
    (className : QualifiedName)
    (nameProjects : IdentifierProjects name.matched name.spelling name.parsed)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.forallBinderBoundedWithoutArguments origin finish name
        colon className nameProjects witness) := by
  let retainedName := RuleReduction.terminalLoc name.matched name.parsed
  let core := LocationFragment.merge
    [LocationFragment.ofIdentifier retainedName,
      LocationFragment.ofQualifiedName className]
  apply WrappedLocation.projectedInput witness core
  · change LocationFragment.located witness.span
      [LocationFragment.ofIdentifier retainedName,
        LocationFragment.ofQualifiedName className,
        LocationFragment.empty] =
        LocationFragment.located witness.span [core]
    apply LocationFragment.eq_of_fields <;> simp [core]
  · apply LocationFragment.IsSubfragmentOf.merge_pair
    · rw [ofIdentifier_terminal_eq]
      apply
        EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.choice ⟨1, by decide⟩
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.terminal _ _
    · apply
        EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.choice ⟨1, by decide⟩
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.rule .qualifiedName className
  · apply input_roots_ne_nil_of_inside
    · apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.choice ⟨1, by decide⟩
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.terminal _ _
    · simp [MatchedTerminal.locationFragment]

theorem forallBinderBoundedWithArguments_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (name : RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier)
    (colon : MatchedTerminal file tokens (.symbol .colon))
    (className : QualifiedName)
    (openParen : MatchedTerminal file tokens (.symbol .leftParen))
    (arguments : NonemptyList TypeExpr)
    (closeParen : MatchedTerminal file tokens (.symbol .rightParen))
    (nameProjects : IdentifierProjects name.matched name.spelling name.parsed)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.forallBinderBoundedWithArguments origin finish name colon
        className openParen arguments closeParen nameProjects witness) := by
  let retainedName := RuleReduction.terminalLoc name.matched name.parsed
  let argumentCore := LocationFragment.ofNonempty
    LocationFragment.ofTypeExpr arguments
  let core := LocationFragment.merge
    [LocationFragment.ofIdentifier retainedName,
      LocationFragment.ofQualifiedName className, argumentCore]
  apply WrappedLocation.projectedInput witness core
  · rw [RuleLocationView.ofRuleValue, LocationFragment.ofForallBinder_mk]
    simp only [sourceLoc, RuleReduction.arguments]
    rw [ofTypeExprArguments_some_eq_ofNonempty]
    change LocationFragment.located witness.span
      [LocationFragment.ofIdentifier retainedName,
        LocationFragment.ofQualifiedName className, argumentCore] =
        LocationFragment.located witness.span [core]
    exact (LocationFragment.located_merge _ _).symm
  · apply LocationFragment.IsSubfragmentOf.merge
    intro fragment member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · rw [ofIdentifier_terminal_eq]
      apply
        EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.choice ⟨1, by decide⟩
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.terminal _ _
    · apply
        EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.choice ⟨1, by decide⟩
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.rule .qualifiedName className
    · unfold argumentCore LocationFragment.ofNonempty
      apply LocationFragment.IsSubfragmentOf.merge_pair
      · apply
          EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
        apply EbnfValue.ContainsLocationFragment.transport (by rfl)
        apply EbnfValue.ContainsLocationFragment.choice ⟨1, by decide⟩
        apply EbnfValue.ContainsLocationFragment.sequence
        apply EbnfValues.ContainsLocationFragment.tail
        apply EbnfValues.ContainsLocationFragment.tail
        apply EbnfValues.ContainsLocationFragment.tail
        apply EbnfValues.ContainsLocationFragment.head
        apply EbnfValue.ContainsLocationFragment.optional
        apply EbnfValue.ContainsLocationFragment.sequence
        apply EbnfValues.ContainsLocationFragment.tail
        apply EbnfValues.ContainsLocationFragment.head
        apply EbnfValue.ContainsLocationFragment.list1Head
        exact EbnfValue.ContainsLocationFragment.rule .type arguments.head
      · unfold LocationFragment.ofList
        apply LocationFragment.IsSubfragmentOf.merge_map
        intro argument argumentMember
        apply
          EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
        apply EbnfValue.ContainsLocationFragment.transport (by rfl)
        apply EbnfValue.ContainsLocationFragment.choice ⟨1, by decide⟩
        apply EbnfValue.ContainsLocationFragment.sequence
        apply EbnfValues.ContainsLocationFragment.tail
        apply EbnfValues.ContainsLocationFragment.tail
        apply EbnfValues.ContainsLocationFragment.tail
        apply EbnfValues.ContainsLocationFragment.head
        apply EbnfValue.ContainsLocationFragment.optional
        apply EbnfValue.ContainsLocationFragment.sequence
        apply EbnfValues.ContainsLocationFragment.tail
        apply EbnfValues.ContainsLocationFragment.head
        apply EbnfValue.ContainsLocationFragment.list1Tail
        · exact List.mem_map_of_mem argumentMember
        · exact EbnfValue.ContainsLocationFragment.rule .type argument
  · apply input_roots_ne_nil_of_inside
    · apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.choice ⟨1, by decide⟩
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.terminal _ _
    · simp [MatchedTerminal.locationFragment]

theorem predicateWithoutArguments_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens) (main : TypeExpr)
    (colon : MatchedTerminal file tokens (.symbol .colon))
    (className : QualifiedName)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.predicateWithoutArguments origin finish main colon
        className witness) := by
  let core := LocationFragment.merge
    [LocationFragment.ofTypeExpr main,
      LocationFragment.ofQualifiedName className]
  apply WrappedLocation.projectedInput witness core
  · rw [RuleLocationView.ofRuleValue, LocationFragment.ofPredicate_mk]
    apply LocationFragment.eq_of_fields <;>
      simp [core, sourceLoc, LocationFragment.ofTypeExprArguments]
  · apply LocationFragment.IsSubfragmentOf.merge_pair
    · apply
        EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.rule .typeAtom main
    · apply
        EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.rule .qualifiedName className
  · apply input_roots_ne_nil_of_inside
    · apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.rule .typeAtom main
    · simp [RuleLocationView.ofRuleValue]

theorem predicateWithArguments_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens) (main : TypeExpr)
    (colon : MatchedTerminal file tokens (.symbol .colon))
    (className : QualifiedName)
    (openParen : MatchedTerminal file tokens (.symbol .leftParen))
    (parameters : NonemptyList TypeExpr)
    (closeParen : MatchedTerminal file tokens (.symbol .rightParen))
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.predicateWithArguments origin finish main colon className
        openParen parameters closeParen witness) := by
  let parameterCore := LocationFragment.ofNonempty
    LocationFragment.ofTypeExpr parameters
  let core := LocationFragment.merge
    [LocationFragment.ofTypeExpr main,
      LocationFragment.ofQualifiedName className, parameterCore]
  apply WrappedLocation.projectedInput witness core
  · rw [RuleLocationView.ofRuleValue, LocationFragment.ofPredicate_mk]
    simp only [sourceLoc, RuleReduction.arguments]
    rw [ofTypeExprArguments_some_eq_ofNonempty]
    change LocationFragment.located witness.span
      [LocationFragment.ofTypeExpr main,
        LocationFragment.ofQualifiedName className, parameterCore] =
        LocationFragment.located witness.span [core]
    exact (LocationFragment.located_merge _ _).symm
  · apply LocationFragment.IsSubfragmentOf.merge
    intro fragment member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · apply
        EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.rule .typeAtom main
    · apply
        EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.rule .qualifiedName className
    · unfold parameterCore LocationFragment.ofNonempty
      apply LocationFragment.IsSubfragmentOf.merge_pair
      · apply
          EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
        apply EbnfValue.ContainsLocationFragment.transport (by rfl)
        apply EbnfValue.ContainsLocationFragment.sequence
        apply EbnfValues.ContainsLocationFragment.tail
        apply EbnfValues.ContainsLocationFragment.tail
        apply EbnfValues.ContainsLocationFragment.tail
        apply EbnfValues.ContainsLocationFragment.head
        apply EbnfValue.ContainsLocationFragment.optional
        apply EbnfValue.ContainsLocationFragment.sequence
        apply EbnfValues.ContainsLocationFragment.tail
        apply EbnfValues.ContainsLocationFragment.head
        apply EbnfValue.ContainsLocationFragment.list1Head
        exact EbnfValue.ContainsLocationFragment.rule .type parameters.head
      · unfold LocationFragment.ofList
        apply LocationFragment.IsSubfragmentOf.merge_map
        intro parameter parameterMember
        apply
          EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
        apply EbnfValue.ContainsLocationFragment.transport (by rfl)
        apply EbnfValue.ContainsLocationFragment.sequence
        apply EbnfValues.ContainsLocationFragment.tail
        apply EbnfValues.ContainsLocationFragment.tail
        apply EbnfValues.ContainsLocationFragment.tail
        apply EbnfValues.ContainsLocationFragment.head
        apply EbnfValue.ContainsLocationFragment.optional
        apply EbnfValue.ContainsLocationFragment.sequence
        apply EbnfValues.ContainsLocationFragment.tail
        apply EbnfValues.ContainsLocationFragment.head
        apply EbnfValue.ContainsLocationFragment.list1Tail
        · exact List.mem_map_of_mem parameterMember
        · exact EbnfValue.ContainsLocationFragment.rule .type parameter
  · apply input_roots_ne_nil_of_inside
    · apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.rule .typeAtom main
    · simp [RuleLocationView.ofRuleValue]

theorem genericPrefixContext_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens) (forallClause : ForallClause)
    (predicates : NonemptyList Predicate)
    (fatArrow : MatchedTerminal file tokens (.symbol .fatArrow))
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.genericPrefixContext origin finish forallClause
        predicates fatArrow witness) := by
  let predicateCore := LocationFragment.ofNonempty
    LocationFragment.ofPredicate predicates
  let core := LocationFragment.merge
    [LocationFragment.ofForallClause forallClause, predicateCore]
  apply WrappedLocation.projectedInput witness core
  · rw [RuleLocationView.ofRuleValue,
      LocationFragment.ofGenericPrefix_mk]
    change LocationFragment.located witness.span
      [LocationFragment.ofForallClause forallClause, predicateCore] =
        LocationFragment.located witness.span [core]
    exact (LocationFragment.located_merge _ _).symm
  · apply LocationFragment.IsSubfragmentOf.merge_pair
    · apply
        EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.rule .forallClause forallClause
    · change (LocationFragment.ofNonempty LocationFragment.ofPredicate
          predicates).IsSubfragmentOf _
      rw [← RuleLocationView.ofPredicateList_eq_ofNonempty]
      apply
        EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      apply EbnfValue.ContainsLocationFragment.optional
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.rule .predicateList predicates
  · apply input_roots_ne_nil_of_inside
    · apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.rule .forallClause forallClause
    · simp [RuleLocationView.ofRuleValue]

theorem forallClause_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (forallKw : MatchedTerminal file tokens (.hardKeyword .forallKw))
    (first : ForallBinder)
    (rest : List (OptionalCommaValue × ForallBinder))
    (dot : MatchedTerminal file tokens (.symbol .dot))
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.forallClause origin finish forallKw first rest dot
        witness) := by
  let binders : NonemptyList ForallBinder :=
    { head := first, tail := rest.map Prod.snd }
  let core := LocationFragment.ofNonempty
    LocationFragment.ofForallBinder binders
  apply WrappedLocation.projectedInput witness core
  · change LocationFragment.located witness.span
      [LocationFragment.ofNonempty LocationFragment.ofForallBinder binders] =
        LocationFragment.located witness.span [core]
    rfl
  · unfold core LocationFragment.ofNonempty
    apply LocationFragment.IsSubfragmentOf.merge_pair
    · apply
        EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.rule .forallBinder first
    · unfold LocationFragment.ofList
      apply LocationFragment.IsSubfragmentOf.merge_map
      intro binder binderMember
      change binder ∈ rest.map Prod.snd at binderMember
      rw [List.mem_map] at binderMember
      rcases binderMember with ⟨entry, entryMember, rfl⟩
      apply
        EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      apply EbnfValue.ContainsLocationFragment.star
      · exact List.mem_map_of_mem entryMember
      · apply EbnfValue.ContainsLocationFragment.group
        apply EbnfValue.ContainsLocationFragment.sequence
        apply EbnfValues.ContainsLocationFragment.tail
        apply EbnfValues.ContainsLocationFragment.head
        exact EbnfValue.ContainsLocationFragment.rule .forallBinder entry.2
  · apply input_roots_ne_nil_of_inside
    · apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.rule .forallBinder first
    · simp [RuleLocationView.ofRuleValue]

theorem functionSignature_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (genericPrefix : Option GenericPrefix)
    (publicToken : Option (MatchedTerminal file tokens (.hardKeyword .publicKw)))
    (payableToken : Option (MatchedTerminal file tokens (.hardKeyword .payableKw)))
    (functionKw : MatchedTerminal file tokens (.hardKeyword .functionKw))
    (name : RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier)
    (openParen : MatchedTerminal file tokens (.symbol .leftParen))
    (parameters : List Parameter)
    (closeParen : MatchedTerminal file tokens (.symbol .rightParen))
    (returnValue : Option
      (MatchedTerminal file tokens (.symbol .arrow) × (TypeExpr × Unit)))
    (publicProjects : ∀ terminal, publicToken = some terminal →
      RuleReduction.MarkerProjects file tokens terminal .publicModifier)
    (payableProjects : ∀ terminal, payableToken = some terminal →
      RuleReduction.MarkerProjects file tokens terminal .payableModifier)
    (nameProjects : IdentifierProjects name.matched name.spelling name.parsed)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.functionSignature origin finish genericPrefix publicToken
        payableToken functionKw name openParen parameters closeParen
        returnValue publicProjects payableProjects nameProjects witness) := by
  let genericCore := LocationFragment.ofOption
    LocationFragment.ofGenericPrefix genericPrefix
  let publicCore := match publicToken with
    | none => LocationFragment.empty
    | some terminal => terminal.locationFragment
  let payableCore := match payableToken with
    | none => LocationFragment.empty
    | some terminal => terminal.locationFragment
  let retainedName := RuleReduction.terminalLoc name.matched name.parsed
  let parameterCore := LocationFragment.ofList
    LocationFragment.ofParameter parameters
  let returnCore := match returnValue with
    | none => LocationFragment.empty
    | some value => LocationFragment.ofTypeExpr value.2.1
  let core := LocationFragment.merge [genericCore, publicCore, payableCore,
    LocationFragment.ofIdentifier retainedName, parameterCore, returnCore]
  apply WrappedLocation.projectedInput witness core
  · rw [RuleLocationView.ofRuleValue,
      LocationFragment.ofFunctionSignature_mk]
    cases publicToken <;> cases payableToken <;> cases returnValue <;>
      apply LocationFragment.eq_of_fields <;>
        simp [core, genericCore, publicCore, payableCore, retainedName,
          parameterCore, returnCore, sourceLoc, LocationFragment.ofOption,
          LocationFragment.leaf, MatchedTerminal.locationFragment,
          RuleReduction.marker, RuleReduction.terminalLoc]
  · apply LocationFragment.IsSubfragmentOf.merge
    intro fragment member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    · cases genericPrefix with
      | none => exact LocationFragment.IsSubfragmentOf.empty _
      | some value =>
          apply
            EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
          apply EbnfValue.ContainsLocationFragment.transport (by rfl)
          apply EbnfValue.ContainsLocationFragment.sequence
          apply EbnfValues.ContainsLocationFragment.head
          apply EbnfValue.ContainsLocationFragment.optional
          exact EbnfValue.ContainsLocationFragment.rule .genericPrefix value
    · cases publicToken with
      | none => exact LocationFragment.IsSubfragmentOf.empty _
      | some terminal =>
          apply
            EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
          apply EbnfValue.ContainsLocationFragment.transport (by rfl)
          apply EbnfValue.ContainsLocationFragment.sequence
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.head
          apply EbnfValue.ContainsLocationFragment.optional
          exact EbnfValue.ContainsLocationFragment.terminal _ _
    · cases payableToken with
      | none => exact LocationFragment.IsSubfragmentOf.empty _
      | some terminal =>
          apply
            EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
          apply EbnfValue.ContainsLocationFragment.transport (by rfl)
          apply EbnfValue.ContainsLocationFragment.sequence
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.head
          apply EbnfValue.ContainsLocationFragment.optional
          exact EbnfValue.ContainsLocationFragment.terminal _ _
    · rw [ofIdentifier_terminal_eq]
      apply
        EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.terminal _ _
    · unfold parameterCore LocationFragment.ofList
      apply LocationFragment.IsSubfragmentOf.merge_map
      intro parameter parameterMember
      apply
        EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      apply EbnfValue.ContainsLocationFragment.list0
      · exact List.mem_map_of_mem parameterMember
      · exact EbnfValue.ContainsLocationFragment.rule .parameter parameter
    · cases returnValue with
      | none => exact LocationFragment.IsSubfragmentOf.empty _
      | some value =>
          apply
            EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
          apply EbnfValue.ContainsLocationFragment.transport (by rfl)
          apply EbnfValue.ContainsLocationFragment.sequence
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.head
          apply EbnfValue.ContainsLocationFragment.optional
          apply EbnfValue.ContainsLocationFragment.sequence
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.head
          exact EbnfValue.ContainsLocationFragment.rule .type value.2.1
  · apply input_roots_ne_nil_of_inside
    · apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.terminal _ _
    · simp [MatchedTerminal.locationFragment]

theorem dataConstructorWithArguments_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (name : RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier)
    (openParen : MatchedTerminal file tokens (.symbol .leftParen))
    (fields : NonemptyList TypeExpr)
    (closeParen : MatchedTerminal file tokens (.symbol .rightParen))
    (nameProjects : IdentifierProjects name.matched name.spelling name.parsed)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.dataConstructorWithArguments origin finish name openParen
        fields closeParen nameProjects witness) := by
  let retainedName := RuleReduction.terminalLoc name.matched name.parsed
  let fieldCore := LocationFragment.ofNonempty
    LocationFragment.ofTypeExpr fields
  let core := LocationFragment.merge
    [LocationFragment.ofIdentifier retainedName, fieldCore]
  apply WrappedLocation.projectedInput witness core
  · rw [RuleLocationView.ofRuleValue,
      LocationFragment.ofDataConstructor_mk]
    simp only [sourceLoc, RuleReduction.arguments]
    simp only [LocationFragment.ofOption]
    change LocationFragment.located witness.span
      [LocationFragment.ofIdentifier retainedName, fieldCore] =
        LocationFragment.located witness.span [core]
    exact (LocationFragment.located_merge _ _).symm
  · apply LocationFragment.IsSubfragmentOf.merge_pair
    · rw [ofIdentifier_terminal_eq]
      apply
        EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.terminal _ _
    · unfold fieldCore LocationFragment.ofNonempty
      apply LocationFragment.IsSubfragmentOf.merge_pair
      · apply
          EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
        apply EbnfValue.ContainsLocationFragment.transport (by rfl)
        apply EbnfValue.ContainsLocationFragment.sequence
        apply EbnfValues.ContainsLocationFragment.tail
        apply EbnfValues.ContainsLocationFragment.head
        apply EbnfValue.ContainsLocationFragment.optional
        apply EbnfValue.ContainsLocationFragment.sequence
        apply EbnfValues.ContainsLocationFragment.tail
        apply EbnfValues.ContainsLocationFragment.head
        apply EbnfValue.ContainsLocationFragment.list1Head
        exact EbnfValue.ContainsLocationFragment.rule .type fields.head
      · unfold LocationFragment.ofList
        apply LocationFragment.IsSubfragmentOf.merge_map
        intro field fieldMember
        apply
          EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
        apply EbnfValue.ContainsLocationFragment.transport (by rfl)
        apply EbnfValue.ContainsLocationFragment.sequence
        apply EbnfValues.ContainsLocationFragment.tail
        apply EbnfValues.ContainsLocationFragment.head
        apply EbnfValue.ContainsLocationFragment.optional
        apply EbnfValue.ContainsLocationFragment.sequence
        apply EbnfValues.ContainsLocationFragment.tail
        apply EbnfValues.ContainsLocationFragment.head
        apply EbnfValue.ContainsLocationFragment.list1Tail
        · exact List.mem_map_of_mem fieldMember
        · exact EbnfValue.ContainsLocationFragment.rule .type field
  · apply input_roots_ne_nil_of_inside
    · apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.terminal _ _
    · simp [MatchedTerminal.locationFragment]

theorem dataDecl_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (dataKw : MatchedTerminal file tokens (.hardKeyword .dataKw))
    (name : RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier)
    (parameters : Option
      (MatchedTerminal file tokens (.symbol .leftParen) ×
        (NonemptyList (RuleReduction.SpelledTerminalData file tokens
          (.category .identifier) Identifier) ×
          (MatchedTerminal file tokens (.symbol .rightParen) × Unit))))
    (constructors : Option
      (MatchedTerminal file tokens (.symbol .equal) ×
        (DataConstructor ×
          (List (MatchedTerminal file tokens (.symbol .pipe) ×
            DataConstructor) × Unit))))
    (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
    (nameProjects : IdentifierProjects name.matched name.spelling name.parsed)
    (parameterProjects : ∀ value, parameters = some value →
      IdentifierProjects value.2.1.head.matched
        value.2.1.head.spelling value.2.1.head.parsed ∧
      ∀ parameter, parameter ∈ value.2.1.tail →
        IdentifierProjects parameter.matched
          parameter.spelling parameter.parsed)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.dataDecl origin finish dataKw name parameters
        constructors semicolon nameProjects parameterProjects witness) := by
  let retainedName := RuleReduction.terminalLoc name.matched name.parsed
  let parameterCore := match parameters with
    | none => LocationFragment.empty
    | some value => LocationFragment.ofNonempty LocationFragment.ofIdentifier
        (value.2.1.map fun
          (parameter : RuleReduction.SpelledTerminalData file tokens
            (.category .identifier) Identifier) =>
          RuleReduction.terminalLoc parameter.matched parameter.parsed)
  let constructorCore := match constructors with
    | none => LocationFragment.empty
    | some value => LocationFragment.ofNonempty
        LocationFragment.ofDataConstructor {
          head := value.2.1
          tail := value.2.2.1.map Prod.snd
        }
  let core := LocationFragment.merge
    [LocationFragment.ofIdentifier retainedName, parameterCore,
      constructorCore]
  apply WrappedLocation.projectedInput witness core
  · rw [RuleLocationView.ofRuleValue, LocationFragment.ofDataDecl_mk]
    cases parameters <;> cases constructors <;>
      apply LocationFragment.eq_of_fields <;>
        simp [core, retainedName, parameterCore, constructorCore, sourceLoc,
          LocationFragment.ofOption, RuleReduction.terminalLoc]
  · apply LocationFragment.IsSubfragmentOf.merge
    intro fragment member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · rw [ofIdentifier_terminal_eq]
      apply
        EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.terminal _ _
    · cases parameters with
      | none => exact LocationFragment.IsSubfragmentOf.empty _
      | some value =>
          apply identifier_nonempty_core_inside value.2.1
          · apply EbnfValue.ContainsLocationFragment.transport (by rfl)
            apply EbnfValue.ContainsLocationFragment.sequence
            apply EbnfValues.ContainsLocationFragment.tail
            apply EbnfValues.ContainsLocationFragment.tail
            apply EbnfValues.ContainsLocationFragment.head
            apply EbnfValue.ContainsLocationFragment.optional
            apply EbnfValue.ContainsLocationFragment.sequence
            apply EbnfValues.ContainsLocationFragment.tail
            apply EbnfValues.ContainsLocationFragment.head
            apply EbnfValue.ContainsLocationFragment.list1Head
            exact EbnfValue.ContainsLocationFragment.terminal _ _
          · intro parameter parameterMember
            apply EbnfValue.ContainsLocationFragment.transport (by rfl)
            apply EbnfValue.ContainsLocationFragment.sequence
            apply EbnfValues.ContainsLocationFragment.tail
            apply EbnfValues.ContainsLocationFragment.tail
            apply EbnfValues.ContainsLocationFragment.head
            apply EbnfValue.ContainsLocationFragment.optional
            apply EbnfValue.ContainsLocationFragment.sequence
            apply EbnfValues.ContainsLocationFragment.tail
            apply EbnfValues.ContainsLocationFragment.head
            apply EbnfValue.ContainsLocationFragment.list1Tail
            · exact List.mem_map_of_mem parameterMember
            · exact EbnfValue.ContainsLocationFragment.terminal _ _
    · cases constructors with
      | none => exact LocationFragment.IsSubfragmentOf.empty _
      | some value =>
          unfold constructorCore LocationFragment.ofNonempty
          apply LocationFragment.IsSubfragmentOf.merge_pair
          · apply
              EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
            apply EbnfValue.ContainsLocationFragment.transport (by rfl)
            apply EbnfValue.ContainsLocationFragment.sequence
            apply EbnfValues.ContainsLocationFragment.tail
            apply EbnfValues.ContainsLocationFragment.tail
            apply EbnfValues.ContainsLocationFragment.tail
            apply EbnfValues.ContainsLocationFragment.head
            apply EbnfValue.ContainsLocationFragment.optional
            apply EbnfValue.ContainsLocationFragment.sequence
            apply EbnfValues.ContainsLocationFragment.tail
            apply EbnfValues.ContainsLocationFragment.head
            exact EbnfValue.ContainsLocationFragment.rule .dataConstructor
              value.2.1
          · unfold LocationFragment.ofList
            apply LocationFragment.IsSubfragmentOf.merge_map
            intro constructor constructorMember
            change constructor ∈ value.2.2.1.map Prod.snd at constructorMember
            rw [List.mem_map] at constructorMember
            rcases constructorMember with ⟨entry, entryMember, rfl⟩
            apply
              EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
            apply EbnfValue.ContainsLocationFragment.transport (by rfl)
            apply EbnfValue.ContainsLocationFragment.sequence
            apply EbnfValues.ContainsLocationFragment.tail
            apply EbnfValues.ContainsLocationFragment.tail
            apply EbnfValues.ContainsLocationFragment.tail
            apply EbnfValues.ContainsLocationFragment.head
            apply EbnfValue.ContainsLocationFragment.optional
            apply EbnfValue.ContainsLocationFragment.sequence
            apply EbnfValues.ContainsLocationFragment.tail
            apply EbnfValues.ContainsLocationFragment.tail
            apply EbnfValues.ContainsLocationFragment.head
            apply EbnfValue.ContainsLocationFragment.star
            · exact List.mem_map_of_mem entryMember
            · apply EbnfValue.ContainsLocationFragment.group
              apply EbnfValue.ContainsLocationFragment.sequence
              apply EbnfValues.ContainsLocationFragment.tail
              apply EbnfValues.ContainsLocationFragment.head
              exact EbnfValue.ContainsLocationFragment.rule .dataConstructor
                entry.2
  · apply input_roots_ne_nil_of_inside
    · apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.terminal _ _
    · simp [MatchedTerminal.locationFragment]

theorem fieldDecl_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (name : RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier)
    (colon : MatchedTerminal file tokens (.symbol .colon))
    (typeValue : TypeExpr)
    (initializer : Option
      (MatchedTerminal file tokens (.symbol .equal) × (Expression × Unit)))
    (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
    (nameProjects : IdentifierProjects name.matched name.spelling name.parsed)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.fieldDecl origin finish name colon typeValue initializer
        semicolon nameProjects witness) := by
  let retainedName := RuleReduction.terminalLoc name.matched name.parsed
  let initializerCore := match initializer with
    | none => LocationFragment.empty
    | some value => LocationFragment.ofExpression value.2.1
  let core := LocationFragment.merge
    [LocationFragment.ofIdentifier retainedName,
      LocationFragment.ofTypeExpr typeValue, initializerCore]
  apply WrappedLocation.projectedInput witness core
  · rw [RuleLocationView.ofRuleValue, LocationFragment.ofFieldDecl_mk]
    cases initializer <;>
      apply LocationFragment.eq_of_fields <;>
        simp [core, retainedName, initializerCore, sourceLoc,
          LocationFragment.ofOption, RuleReduction.terminalLoc]
  · apply LocationFragment.IsSubfragmentOf.merge
    intro fragment member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · rw [ofIdentifier_terminal_eq]
      apply
        EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.terminal _ _
    · apply
        EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.rule .type typeValue
    · cases initializer with
      | none => exact LocationFragment.IsSubfragmentOf.empty _
      | some value =>
          apply
            EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
          apply EbnfValue.ContainsLocationFragment.transport (by rfl)
          apply EbnfValue.ContainsLocationFragment.sequence
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.head
          apply EbnfValue.ContainsLocationFragment.optional
          apply EbnfValue.ContainsLocationFragment.sequence
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.head
          exact EbnfValue.ContainsLocationFragment.rule .expression value.2.1
  · apply input_roots_ne_nil_of_inside
    · apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.terminal _ _
    · simp [MatchedTerminal.locationFragment]

theorem typeAliasDecl_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (typeKw : MatchedTerminal file tokens (.hardKeyword .typeKw))
    (name : RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier)
    (parameters : Option
      (MatchedTerminal file tokens (.symbol .leftParen) ×
        (NonemptyList (RuleReduction.SpelledTerminalData file tokens
          (.category .identifier) Identifier) ×
          (MatchedTerminal file tokens (.symbol .rightParen) × Unit))))
    (equal : MatchedTerminal file tokens (.symbol .equal))
    (body : TypeExpr)
    (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
    (nameProjects : IdentifierProjects name.matched name.spelling name.parsed)
    (parameterProjects : ∀ value, parameters = some value →
      IdentifierProjects value.2.1.head.matched
        value.2.1.head.spelling value.2.1.head.parsed ∧
      ∀ parameter, parameter ∈ value.2.1.tail →
        IdentifierProjects parameter.matched
          parameter.spelling parameter.parsed)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.typeAliasDecl origin finish typeKw name parameters equal
        body semicolon nameProjects parameterProjects witness) := by
  let retainedName := RuleReduction.terminalLoc name.matched name.parsed
  let parameterCore := match parameters with
    | none => LocationFragment.empty
    | some value => LocationFragment.ofNonempty LocationFragment.ofIdentifier
        (value.2.1.map fun
          (parameter : RuleReduction.SpelledTerminalData file tokens
            (.category .identifier) Identifier) =>
          RuleReduction.terminalLoc parameter.matched parameter.parsed)
  let core := LocationFragment.merge
    [LocationFragment.ofIdentifier retainedName, parameterCore,
      LocationFragment.ofTypeExpr body]
  apply WrappedLocation.projectedInput witness core
  · rw [RuleLocationView.ofRuleValue,
      LocationFragment.ofTypeAliasDecl_mk]
    cases parameters <;>
      apply LocationFragment.eq_of_fields <;>
        simp [core, retainedName, parameterCore, sourceLoc,
          LocationFragment.ofOption, RuleReduction.terminalLoc]
  · apply LocationFragment.IsSubfragmentOf.merge
    intro fragment member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · rw [ofIdentifier_terminal_eq]
      apply
        EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.terminal _ _
    · cases parameters with
      | none => exact LocationFragment.IsSubfragmentOf.empty _
      | some value =>
          apply identifier_nonempty_core_inside value.2.1
          · apply EbnfValue.ContainsLocationFragment.transport (by rfl)
            apply EbnfValue.ContainsLocationFragment.sequence
            apply EbnfValues.ContainsLocationFragment.tail
            apply EbnfValues.ContainsLocationFragment.tail
            apply EbnfValues.ContainsLocationFragment.head
            apply EbnfValue.ContainsLocationFragment.optional
            apply EbnfValue.ContainsLocationFragment.sequence
            apply EbnfValues.ContainsLocationFragment.tail
            apply EbnfValues.ContainsLocationFragment.head
            apply EbnfValue.ContainsLocationFragment.list1Head
            exact EbnfValue.ContainsLocationFragment.terminal _ _
          · intro parameter parameterMember
            apply EbnfValue.ContainsLocationFragment.transport (by rfl)
            apply EbnfValue.ContainsLocationFragment.sequence
            apply EbnfValues.ContainsLocationFragment.tail
            apply EbnfValues.ContainsLocationFragment.tail
            apply EbnfValues.ContainsLocationFragment.head
            apply EbnfValue.ContainsLocationFragment.optional
            apply EbnfValue.ContainsLocationFragment.sequence
            apply EbnfValues.ContainsLocationFragment.tail
            apply EbnfValues.ContainsLocationFragment.head
            apply EbnfValue.ContainsLocationFragment.list1Tail
            · exact List.mem_map_of_mem parameterMember
            · exact EbnfValue.ContainsLocationFragment.terminal _ _
    · apply
        EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.rule .type body
  · apply input_roots_ne_nil_of_inside
    · apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.terminal _ _
    · simp [MatchedTerminal.locationFragment]

theorem contractDecl_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (contractKw : MatchedTerminal file tokens (.hardKeyword .contractKw))
    (name : RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier)
    (parameters : Option
      (MatchedTerminal file tokens (.symbol .leftParen) ×
        (NonemptyList (RuleReduction.SpelledTerminalData file tokens
          (.category .identifier) Identifier) ×
          (MatchedTerminal file tokens (.symbol .rightParen) × Unit))))
    (openBrace : MatchedTerminal file tokens (.symbol .leftBrace))
    (members : List ContractMember)
    (closeBrace : MatchedTerminal file tokens (.symbol .rightBrace))
    (nameProjects : IdentifierProjects name.matched name.spelling name.parsed)
    (parameterProjects : ∀ value, parameters = some value →
      IdentifierProjects value.2.1.head.matched
        value.2.1.head.spelling value.2.1.head.parsed ∧
      ∀ parameter, parameter ∈ value.2.1.tail →
        IdentifierProjects parameter.matched
          parameter.spelling parameter.parsed)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.contractDecl origin finish contractKw name parameters
        openBrace members closeBrace nameProjects parameterProjects
        witness) := by
  let retainedName := RuleReduction.terminalLoc name.matched name.parsed
  let parameterCore := match parameters with
    | none => LocationFragment.empty
    | some value => LocationFragment.ofNonempty LocationFragment.ofIdentifier
        (value.2.1.map fun
          (parameter : RuleReduction.SpelledTerminalData file tokens
            (.category .identifier) Identifier) =>
          RuleReduction.terminalLoc parameter.matched parameter.parsed)
  let memberCore := LocationFragment.ofList
    LocationFragment.ofContractMember members
  let core := LocationFragment.merge
    [LocationFragment.ofIdentifier retainedName, parameterCore, memberCore]
  apply WrappedLocation.projectedInput witness core
  · rw [RuleLocationView.ofRuleValue, LocationFragment.ofContractDecl_mk]
    cases parameters <;>
      apply LocationFragment.eq_of_fields <;>
        simp [core, retainedName, parameterCore, memberCore, sourceLoc,
          LocationFragment.ofOption, RuleReduction.terminalLoc]
  · apply LocationFragment.IsSubfragmentOf.merge
    intro fragment member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · rw [ofIdentifier_terminal_eq]
      apply
        EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.terminal _ _
    · cases parameters with
      | none => exact LocationFragment.IsSubfragmentOf.empty _
      | some value =>
          apply identifier_nonempty_core_inside value.2.1
          · apply EbnfValue.ContainsLocationFragment.transport (by rfl)
            apply EbnfValue.ContainsLocationFragment.sequence
            apply EbnfValues.ContainsLocationFragment.tail
            apply EbnfValues.ContainsLocationFragment.tail
            apply EbnfValues.ContainsLocationFragment.head
            apply EbnfValue.ContainsLocationFragment.optional
            apply EbnfValue.ContainsLocationFragment.sequence
            apply EbnfValues.ContainsLocationFragment.tail
            apply EbnfValues.ContainsLocationFragment.head
            apply EbnfValue.ContainsLocationFragment.list1Head
            exact EbnfValue.ContainsLocationFragment.terminal _ _
          · intro parameter parameterMember
            apply EbnfValue.ContainsLocationFragment.transport (by rfl)
            apply EbnfValue.ContainsLocationFragment.sequence
            apply EbnfValues.ContainsLocationFragment.tail
            apply EbnfValues.ContainsLocationFragment.tail
            apply EbnfValues.ContainsLocationFragment.head
            apply EbnfValue.ContainsLocationFragment.optional
            apply EbnfValue.ContainsLocationFragment.sequence
            apply EbnfValues.ContainsLocationFragment.tail
            apply EbnfValues.ContainsLocationFragment.head
            apply EbnfValue.ContainsLocationFragment.list1Tail
            · exact List.mem_map_of_mem parameterMember
            · exact EbnfValue.ContainsLocationFragment.terminal _ _
    · unfold memberCore LocationFragment.ofList
      apply LocationFragment.IsSubfragmentOf.merge_map
      intro contractMember memberMember
      apply
        EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      apply EbnfValue.ContainsLocationFragment.star
      · exact List.mem_map_of_mem memberMember
      · exact EbnfValue.ContainsLocationFragment.rule .contractMember
          contractMember
  · apply input_roots_ne_nil_of_inside
    · apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.terminal _ _
    · simp [MatchedTerminal.locationFragment]

theorem parameter_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (comptimeToken : Option (MatchedTerminal file tokens
      (.contextualKeyword .comptimeKw)))
    (name : RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier)
    (typeValue : Option
      (MatchedTerminal file tokens (.symbol .colon) × (TypeExpr × Unit)))
    (comptimeProjects : ∀ terminal, comptimeToken = some terminal →
      RuleReduction.MarkerProjects file tokens terminal .comptimeModifier)
    (nameProjects : IdentifierProjects name.matched name.spelling name.parsed)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.parameter origin finish comptimeToken name typeValue
        comptimeProjects nameProjects witness) := by
  let retainedName := RuleReduction.terminalLoc name.matched name.parsed
  let comptimeCore := match comptimeToken with
    | none => LocationFragment.empty
    | some terminal => terminal.locationFragment
  let typeCore := match typeValue with
    | none => LocationFragment.empty
    | some value => LocationFragment.ofTypeExpr value.2.1
  let core := LocationFragment.merge
    [comptimeCore, LocationFragment.ofIdentifier retainedName, typeCore]
  apply WrappedLocation.projectedInput witness core
  · rw [RuleLocationView.ofRuleValue, LocationFragment.ofParameter_mk]
    cases comptimeToken <;> cases typeValue <;>
      apply LocationFragment.eq_of_fields <;>
        simp [core, comptimeCore, typeCore, retainedName, sourceLoc,
          LocationFragment.ofOption, LocationFragment.leaf,
          MatchedTerminal.locationFragment, RuleReduction.marker,
          RuleReduction.terminalLoc]
  · apply LocationFragment.IsSubfragmentOf.merge
    intro fragment member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · cases comptimeToken with
      | none => exact LocationFragment.IsSubfragmentOf.empty _
      | some terminal =>
          apply
            EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
          apply EbnfValue.ContainsLocationFragment.transport (by rfl)
          apply EbnfValue.ContainsLocationFragment.sequence
          apply EbnfValues.ContainsLocationFragment.head
          apply EbnfValue.ContainsLocationFragment.optional
          exact EbnfValue.ContainsLocationFragment.terminal _ _
    · rw [ofIdentifier_terminal_eq]
      apply
        EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.terminal _ _
    · cases typeValue with
      | none => exact LocationFragment.IsSubfragmentOf.empty _
      | some value =>
          apply
            EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
          apply EbnfValue.ContainsLocationFragment.transport (by rfl)
          apply EbnfValue.ContainsLocationFragment.sequence
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.head
          apply EbnfValue.ContainsLocationFragment.optional
          apply EbnfValue.ContainsLocationFragment.sequence
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.head
          exact EbnfValue.ContainsLocationFragment.rule .type value.2.1
  · apply input_roots_ne_nil_of_inside
    · apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.terminal _ _
    · simp [MatchedTerminal.locationFragment]

theorem body_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (openBrace : MatchedTerminal file tokens (.symbol .leftBrace))
    (statements : List Statement)
    (closeBrace : MatchedTerminal file tokens (.symbol .rightBrace))
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.body origin finish openBrace statements closeBrace
        witness) := by
  let core := LocationFragment.merge
    [LocationFragment.raw openBrace.span,
      LocationFragment.raw closeBrace.span,
      LocationFragment.ofStatementList statements]
  apply WrappedLocation.projectedInput witness core
  · rw [RuleLocationView.ofRuleValue]
    simp only [sourceLoc]
    rw [LocationFragment.ofBody_braced]
  · apply LocationFragment.IsSubfragmentOf.merge
    intro fragment member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · apply
        EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.terminal _ _
    · apply
        EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.terminal _ _
    · rw [ofStatementList_eq_ofList]
      unfold LocationFragment.ofList
      apply LocationFragment.IsSubfragmentOf.merge_map
      intro statement statementMember
      apply
        EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      apply EbnfValue.ContainsLocationFragment.star
      · exact List.mem_map_of_mem statementMember
      · exact EbnfValue.ContainsLocationFragment.rule .statement statement
  · apply input_roots_ne_nil_of_inside
    · apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.terminal _ _
    · simp [MatchedTerminal.locationFragment]

theorem typeFunction_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens) (domain : TypeExpr)
    (arrow : MatchedTerminal file tokens (.symbol .arrow))
    (codomain : TypeExpr)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.typeFunction origin finish domain arrow codomain
        witness) := by
  let core := LocationFragment.merge
    [LocationFragment.ofTypeExpr domain,
      LocationFragment.ofTypeExpr codomain]
  apply WrappedLocation.projectedInput witness core
  · simp [core, RuleLocationView.ofRuleValue, sourceLoc,
      LocationFragment.ofTypeExprPayload]
  · apply LocationFragment.IsSubfragmentOf.merge_pair
    · apply
        EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.choice ⟨1, by decide⟩
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.rule .typeAtom domain
    · apply
        EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.choice ⟨1, by decide⟩
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      apply EbnfValue.ContainsLocationFragment.optional
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.rule .type codomain
  · apply input_roots_ne_nil_of_inside
    · apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.choice ⟨1, by decide⟩
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.rule .typeAtom domain
    · simp [RuleLocationView.ofRuleValue]

theorem typeAtomGroup_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (openParen : MatchedTerminal file tokens (.symbol .leftParen))
    (inner : TypeExpr)
    (closeParen : MatchedTerminal file tokens (.symbol .rightParen))
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.typeAtomGroup origin finish openParen inner closeParen
        witness) := by
  let core := LocationFragment.ofTypeExpr inner
  apply WrappedLocation.projectedInput witness core
  · simp [core, RuleLocationView.ofRuleValue, sourceLoc,
      LocationFragment.ofTypeExprPayload]
  · apply
      EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
    apply EbnfValue.ContainsLocationFragment.transport (by rfl)
    apply EbnfValue.ContainsLocationFragment.choice ⟨3, by decide⟩
    apply EbnfValue.ContainsLocationFragment.sequence
    apply EbnfValues.ContainsLocationFragment.tail
    apply EbnfValues.ContainsLocationFragment.head
    exact EbnfValue.ContainsLocationFragment.rule .type inner
  · apply input_roots_ne_nil_of_inside
    · apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.choice ⟨3, by decide⟩
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.rule .type inner
    · simp [RuleLocationView.ofRuleValue]

theorem typeAtomNamedWithArguments_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens) (name : QualifiedName)
    (openParen : MatchedTerminal file tokens (.symbol .leftParen))
    (arguments : NonemptyList TypeExpr)
    (closeParen : MatchedTerminal file tokens (.symbol .rightParen))
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.typeAtomNamedWithArguments origin finish name openParen
        arguments closeParen witness) := by
  let argumentCore := LocationFragment.ofNonempty
    LocationFragment.ofTypeExpr arguments
  let core := LocationFragment.merge
    [LocationFragment.ofQualifiedName name, argumentCore]
  apply WrappedLocation.projectedInput witness core
  · rw [RuleLocationView.ofRuleValue]
    simp only [sourceLoc, RuleReduction.arguments]
    rw [LocationFragment.ofTypeExpr_mk]
    simp [LocationFragment.ofTypeExprPayload, core, argumentCore,
      ofTypeExprArguments_some_eq_ofNonempty]
  · apply LocationFragment.IsSubfragmentOf.merge_pair
    · apply
        EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.choice ⟨1, by decide⟩
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.rule .qualifiedName name
    · unfold argumentCore LocationFragment.ofNonempty
      apply LocationFragment.IsSubfragmentOf.merge_pair
      · apply
          EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
        apply EbnfValue.ContainsLocationFragment.transport (by rfl)
        apply EbnfValue.ContainsLocationFragment.choice ⟨1, by decide⟩
        apply EbnfValue.ContainsLocationFragment.sequence
        apply EbnfValues.ContainsLocationFragment.tail
        apply EbnfValues.ContainsLocationFragment.head
        apply EbnfValue.ContainsLocationFragment.optional
        apply EbnfValue.ContainsLocationFragment.sequence
        apply EbnfValues.ContainsLocationFragment.tail
        apply EbnfValues.ContainsLocationFragment.head
        apply EbnfValue.ContainsLocationFragment.list1Head
        exact EbnfValue.ContainsLocationFragment.rule .type arguments.head
      · unfold LocationFragment.ofList
        apply LocationFragment.IsSubfragmentOf.merge_map
        intro argument argumentMember
        apply
          EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
        apply EbnfValue.ContainsLocationFragment.transport (by rfl)
        apply EbnfValue.ContainsLocationFragment.choice ⟨1, by decide⟩
        apply EbnfValue.ContainsLocationFragment.sequence
        apply EbnfValues.ContainsLocationFragment.tail
        apply EbnfValues.ContainsLocationFragment.head
        apply EbnfValue.ContainsLocationFragment.optional
        apply EbnfValue.ContainsLocationFragment.sequence
        apply EbnfValues.ContainsLocationFragment.tail
        apply EbnfValues.ContainsLocationFragment.head
        apply EbnfValue.ContainsLocationFragment.list1Tail
        · exact List.mem_map_of_mem argumentMember
        · exact EbnfValue.ContainsLocationFragment.rule .type argument
  · apply input_roots_ne_nil_of_inside
    · apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.choice ⟨1, by decide⟩
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.rule .qualifiedName name
    · simp [RuleLocationView.ofRuleValue]

theorem typeAtomTuple_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (openParen : MatchedTerminal file tokens (.symbol .leftParen))
    (first : TypeExpr)
    (comma : MatchedTerminal file tokens (.symbol .comma))
    (second : TypeExpr)
    (rest : List (MatchedTerminal file tokens (.symbol .comma) × TypeExpr))
    (closeParen : MatchedTerminal file tokens (.symbol .rightParen))
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.typeAtomTuple origin finish openParen first comma second
        rest closeParen witness) := by
  let elements := first :: second :: rest.map Prod.snd
  let core := LocationFragment.ofTypeExprList elements
  apply WrappedLocation.projectedInput witness core
  · simp [core, elements, RuleLocationView.ofRuleValue, sourceLoc,
      LocationFragment.ofTypeExprPayload]
  · change (LocationFragment.ofTypeExprList elements).IsSubfragmentOf _
    rw [ofTypeExprList_eq_ofList]
    unfold LocationFragment.ofList
    apply LocationFragment.IsSubfragmentOf.merge_map
    intro element member
    change element ∈ first :: second :: rest.map Prod.snd at member
    simp only [List.mem_cons] at member
    rcases member with rfl | rfl | restMember
    · apply
        EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.choice ⟨4, by decide⟩
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.rule .type _
    · apply
        EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.choice ⟨4, by decide⟩
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.rule .type _
    · rw [List.mem_map] at restMember
      rcases restMember with ⟨entry, entryMember, rfl⟩
      apply
        EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.choice ⟨4, by decide⟩
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      apply EbnfValue.ContainsLocationFragment.star
      · exact List.mem_map_of_mem entryMember
      · apply EbnfValue.ContainsLocationFragment.group
        apply EbnfValue.ContainsLocationFragment.sequence
        apply EbnfValues.ContainsLocationFragment.tail
        apply EbnfValues.ContainsLocationFragment.head
        exact EbnfValue.ContainsLocationFragment.rule .type entry.2
  · apply input_roots_ne_nil_of_inside
    · apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.choice ⟨4, by decide⟩
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.rule .type first
    · simp [RuleLocationView.ofRuleValue]

theorem qualifiedName_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (first : RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier)
    (rest : List
      (MatchedTerminal file tokens (.symbol .dot) ×
        RuleReduction.SpelledTerminalData file tokens
          (.category .identifier) Identifier))
    (firstProjects : IdentifierProjects first.matched
      first.spelling first.parsed)
    (restProjects : ∀ entry, entry ∈ rest →
      IdentifierProjects entry.2.matched entry.2.spelling entry.2.parsed)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.qualifiedName origin finish first rest firstProjects
        restProjects witness) := by
  let components : NonemptyList IdentifierOccurrence := {
    head := RuleReduction.terminalLoc first.matched first.parsed
    tail := rest.map fun entry =>
      RuleReduction.terminalLoc entry.2.matched entry.2.parsed
  }
  let core := LocationFragment.ofNonempty
    LocationFragment.ofIdentifier components
  apply WrappedLocation.projectedInput witness core
  · rw [RuleLocationView.ofRuleValue]
    change LocationFragment.located witness.span
      [LocationFragment.ofNonempty LocationFragment.ofIdentifier components] =
        LocationFragment.located witness.span [core]
    rfl
  · unfold core LocationFragment.ofNonempty
    apply LocationFragment.IsSubfragmentOf.merge_pair
    · change (LocationFragment.ofIdentifier
          (RuleReduction.terminalLoc first.matched first.parsed)).IsSubfragmentOf _
      rw [ofIdentifier_terminal_eq]
      apply
        EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.terminal _ _
    · unfold LocationFragment.ofList
      apply LocationFragment.IsSubfragmentOf.merge_map
      intro component componentMember
      change component ∈ (rest.map fun entry =>
        RuleReduction.terminalLoc entry.2.matched entry.2.parsed) at componentMember
      rw [List.mem_map] at componentMember
      rcases componentMember with ⟨entry, entryMember, rfl⟩
      rw [ofIdentifier_terminal_eq]
      apply
        EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      apply EbnfValue.ContainsLocationFragment.star
      · exact List.mem_map_of_mem entryMember
      · apply EbnfValue.ContainsLocationFragment.group
        apply EbnfValue.ContainsLocationFragment.sequence
        apply EbnfValues.ContainsLocationFragment.tail
        apply EbnfValues.ContainsLocationFragment.head
        exact EbnfValue.ContainsLocationFragment.terminal _ _
  · apply input_roots_ne_nil_of_inside
    · apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.terminal _ _
    · simp [MatchedTerminal.locationFragment]

theorem classDecl_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (genericPrefix : Option GenericPrefix)
    (classKw : MatchedTerminal file tokens (.hardKeyword .classKw))
    (main : TypeExpr)
    (colon : MatchedTerminal file tokens (.symbol .colon))
    (name : RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier)
    (parameters : Option
      (MatchedTerminal file tokens (.symbol .leftParen) ×
        (NonemptyList TypeExpr ×
          (MatchedTerminal file tokens (.symbol .rightParen) × Unit))))
    (openBrace : MatchedTerminal file tokens (.symbol .leftBrace))
    (methods : List ClassMethodDecl)
    (closeBrace : MatchedTerminal file tokens (.symbol .rightBrace))
    (nameProjects : IdentifierProjects name.matched name.spelling name.parsed)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.classDecl origin finish genericPrefix classKw main colon
        name parameters openBrace methods closeBrace nameProjects witness) := by
  let genericCore := LocationFragment.ofOption
    LocationFragment.ofGenericPrefix genericPrefix
  let retainedName := RuleReduction.terminalLoc name.matched name.parsed
  let parameterCore := match parameters with
    | none => LocationFragment.empty
    | some value => LocationFragment.ofNonempty
        LocationFragment.ofTypeExpr value.2.1
  let methodCore := LocationFragment.ofList
    LocationFragment.ofClassMethodDecl methods
  let core := LocationFragment.merge
    [genericCore, LocationFragment.ofTypeExpr main,
      LocationFragment.ofIdentifier retainedName, parameterCore, methodCore]
  apply WrappedLocation.projectedInput witness core
  · rw [RuleLocationView.ofRuleValue, LocationFragment.ofClassDecl_mk]
    simp only [sourceLoc, RuleReduction.arguments]
    cases parameters with
    | none =>
        change LocationFragment.located witness.span
          [genericCore, LocationFragment.ofTypeExpr main,
            LocationFragment.ofIdentifier retainedName,
            LocationFragment.ofTypeExprArguments none, methodCore] =
              LocationFragment.located witness.span [core]
        rw [show LocationFragment.ofTypeExprArguments none =
          LocationFragment.empty by rfl]
        exact (LocationFragment.located_merge _ _).symm
    | some value =>
        rw [ofTypeExprArguments_some_eq_ofNonempty]
        change LocationFragment.located witness.span
          [genericCore, LocationFragment.ofTypeExpr main,
            LocationFragment.ofIdentifier retainedName,
            LocationFragment.ofNonempty LocationFragment.ofTypeExpr
              value.2.1, methodCore] =
              LocationFragment.located witness.span [core]
        exact (LocationFragment.located_merge _ _).symm
  · apply LocationFragment.IsSubfragmentOf.merge
    intro fragment member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    · cases genericPrefix with
      | none => exact LocationFragment.IsSubfragmentOf.empty _
      | some value =>
          apply
            EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
          apply EbnfValue.ContainsLocationFragment.transport (by rfl)
          apply EbnfValue.ContainsLocationFragment.sequence
          apply EbnfValues.ContainsLocationFragment.head
          apply EbnfValue.ContainsLocationFragment.optional
          exact EbnfValue.ContainsLocationFragment.rule .genericPrefix value
    · apply
        EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.rule .typeAtom main
    · rw [ofIdentifier_terminal_eq]
      apply
        EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.terminal _ _
    · cases parameters with
      | none => exact LocationFragment.IsSubfragmentOf.empty _
      | some value =>
          apply type_nonempty_core_inside value.2.1
          · apply EbnfValue.ContainsLocationFragment.transport (by rfl)
            apply EbnfValue.ContainsLocationFragment.sequence
            apply EbnfValues.ContainsLocationFragment.tail
            apply EbnfValues.ContainsLocationFragment.tail
            apply EbnfValues.ContainsLocationFragment.tail
            apply EbnfValues.ContainsLocationFragment.tail
            apply EbnfValues.ContainsLocationFragment.tail
            apply EbnfValues.ContainsLocationFragment.head
            apply EbnfValue.ContainsLocationFragment.optional
            apply EbnfValue.ContainsLocationFragment.sequence
            apply EbnfValues.ContainsLocationFragment.tail
            apply EbnfValues.ContainsLocationFragment.head
            apply EbnfValue.ContainsLocationFragment.list1Head
            exact EbnfValue.ContainsLocationFragment.rule .type value.2.1.head
          · intro parameter parameterMember
            apply EbnfValue.ContainsLocationFragment.transport (by rfl)
            apply EbnfValue.ContainsLocationFragment.sequence
            apply EbnfValues.ContainsLocationFragment.tail
            apply EbnfValues.ContainsLocationFragment.tail
            apply EbnfValues.ContainsLocationFragment.tail
            apply EbnfValues.ContainsLocationFragment.tail
            apply EbnfValues.ContainsLocationFragment.tail
            apply EbnfValues.ContainsLocationFragment.head
            apply EbnfValue.ContainsLocationFragment.optional
            apply EbnfValue.ContainsLocationFragment.sequence
            apply EbnfValues.ContainsLocationFragment.tail
            apply EbnfValues.ContainsLocationFragment.head
            apply EbnfValue.ContainsLocationFragment.list1Tail
            · exact List.mem_map_of_mem parameterMember
            · exact EbnfValue.ContainsLocationFragment.rule .type parameter
    · unfold methodCore LocationFragment.ofList
      apply LocationFragment.IsSubfragmentOf.merge_map
      intro method methodMember
      apply
        EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      apply EbnfValue.ContainsLocationFragment.star
      · exact List.mem_map_of_mem methodMember
      · exact EbnfValue.ContainsLocationFragment.rule .classMethod method
  · apply input_roots_ne_nil_of_inside
    · apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.terminal _ _
    · simp [MatchedTerminal.locationFragment]

theorem instanceDecl_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (genericPrefix : Option GenericPrefix)
    (defaultToken : Option
      (MatchedTerminal file tokens (.hardKeyword .defaultKw)))
    (instanceKw : MatchedTerminal file tokens (.hardKeyword .instanceKw))
    (main : TypeExpr)
    (colon : MatchedTerminal file tokens (.symbol .colon))
    (className : QualifiedName)
    (parameters : Option
      (MatchedTerminal file tokens (.symbol .leftParen) ×
        (NonemptyList TypeExpr ×
          (MatchedTerminal file tokens (.symbol .rightParen) × Unit))))
    (openBrace : MatchedTerminal file tokens (.symbol .leftBrace))
    (methods : List FunctionDecl)
    (closeBrace : MatchedTerminal file tokens (.symbol .rightBrace))
    (defaultProjects : ∀ terminal, defaultToken = some terminal →
      RuleReduction.MarkerProjects file tokens terminal .defaultModifier)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.instanceDecl origin finish genericPrefix defaultToken
        instanceKw main colon className parameters openBrace methods
        closeBrace defaultProjects witness) := by
  let genericCore := LocationFragment.ofOption
    LocationFragment.ofGenericPrefix genericPrefix
  let defaultCore := match defaultToken with
    | none => LocationFragment.empty
    | some terminal => terminal.locationFragment
  let parameterCore := LocationFragment.ofTypeExprArguments
    (RuleReduction.arguments parameters)
  let methodCore := LocationFragment.ofList
    LocationFragment.ofFunctionDecl methods
  let core := LocationFragment.merge
    [genericCore, defaultCore, LocationFragment.ofTypeExpr main,
      LocationFragment.ofQualifiedName className, parameterCore, methodCore]
  apply WrappedLocation.projectedInput witness core
  · rw [RuleLocationView.ofRuleValue, LocationFragment.ofInstanceDecl_mk]
    simp only [sourceLoc]
    cases defaultToken <;>
      apply LocationFragment.eq_of_fields <;>
        simp [core, genericCore, defaultCore, parameterCore, methodCore,
          LocationFragment.ofOption, LocationFragment.leaf,
          MatchedTerminal.locationFragment, RuleReduction.marker,
          RuleReduction.terminalLoc]
  · apply LocationFragment.IsSubfragmentOf.merge
    intro fragment member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    · cases genericPrefix with
      | none => exact LocationFragment.IsSubfragmentOf.empty _
      | some value =>
          apply
            EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
          apply EbnfValue.ContainsLocationFragment.transport (by rfl)
          apply EbnfValue.ContainsLocationFragment.sequence
          apply EbnfValues.ContainsLocationFragment.head
          apply EbnfValue.ContainsLocationFragment.optional
          exact EbnfValue.ContainsLocationFragment.rule .genericPrefix value
    · cases defaultToken with
      | none => exact LocationFragment.IsSubfragmentOf.empty _
      | some terminal =>
          apply
            EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
          apply EbnfValue.ContainsLocationFragment.transport (by rfl)
          apply EbnfValue.ContainsLocationFragment.sequence
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.head
          apply EbnfValue.ContainsLocationFragment.optional
          exact EbnfValue.ContainsLocationFragment.terminal _ _
    · apply
        EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.rule .typeAtom main
    · apply
        EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.rule .qualifiedName className
    · cases parameters with
      | none =>
          change (LocationFragment.ofTypeExprArguments none).IsSubfragmentOf _
          exact LocationFragment.IsSubfragmentOf.empty _
      | some value =>
          change (LocationFragment.ofTypeExprArguments
            (some value.2.1)).IsSubfragmentOf _
          rw [ofTypeExprArguments_some_eq_ofNonempty]
          apply type_nonempty_core_inside value.2.1
          · apply EbnfValue.ContainsLocationFragment.transport (by rfl)
            apply EbnfValue.ContainsLocationFragment.sequence
            apply EbnfValues.ContainsLocationFragment.tail
            apply EbnfValues.ContainsLocationFragment.tail
            apply EbnfValues.ContainsLocationFragment.tail
            apply EbnfValues.ContainsLocationFragment.tail
            apply EbnfValues.ContainsLocationFragment.tail
            apply EbnfValues.ContainsLocationFragment.tail
            apply EbnfValues.ContainsLocationFragment.head
            apply EbnfValue.ContainsLocationFragment.optional
            apply EbnfValue.ContainsLocationFragment.sequence
            apply EbnfValues.ContainsLocationFragment.tail
            apply EbnfValues.ContainsLocationFragment.head
            apply EbnfValue.ContainsLocationFragment.list1Head
            exact EbnfValue.ContainsLocationFragment.rule .type value.2.1.head
          · intro parameter parameterMember
            apply EbnfValue.ContainsLocationFragment.transport (by rfl)
            apply EbnfValue.ContainsLocationFragment.sequence
            apply EbnfValues.ContainsLocationFragment.tail
            apply EbnfValues.ContainsLocationFragment.tail
            apply EbnfValues.ContainsLocationFragment.tail
            apply EbnfValues.ContainsLocationFragment.tail
            apply EbnfValues.ContainsLocationFragment.tail
            apply EbnfValues.ContainsLocationFragment.tail
            apply EbnfValues.ContainsLocationFragment.head
            apply EbnfValue.ContainsLocationFragment.optional
            apply EbnfValue.ContainsLocationFragment.sequence
            apply EbnfValues.ContainsLocationFragment.tail
            apply EbnfValues.ContainsLocationFragment.head
            apply EbnfValue.ContainsLocationFragment.list1Tail
            · exact List.mem_map_of_mem parameterMember
            · exact EbnfValue.ContainsLocationFragment.rule .type parameter
    · unfold methodCore LocationFragment.ofList
      apply LocationFragment.IsSubfragmentOf.merge_map
      intro method methodMember
      apply
        EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      apply EbnfValue.ContainsLocationFragment.star
      · exact List.mem_map_of_mem methodMember
      · exact EbnfValue.ContainsLocationFragment.rule .instanceMethod method
  · apply input_roots_ne_nil_of_inside
    · apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.terminal _ _
    · simp [MatchedTerminal.locationFragment]

theorem fallbackDecl_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (genericPrefix : Option GenericPrefix)
    (publicToken : Option
      (MatchedTerminal file tokens (.hardKeyword .publicKw)))
    (payableToken : Option
      (MatchedTerminal file tokens (.hardKeyword .payableKw)))
    (fallbackKw : MatchedTerminal file tokens (.hardKeyword .fallbackKw))
    (openParen : MatchedTerminal file tokens (.symbol .leftParen))
    (parameters : List Parameter)
    (closeParen : MatchedTerminal file tokens (.symbol .rightParen))
    (returnValue : Option
      (MatchedTerminal file tokens (.symbol .arrow) × (TypeExpr × Unit)))
    (body : Body)
    (publicProjects : ∀ terminal, publicToken = some terminal →
      RuleReduction.MarkerProjects file tokens terminal .publicModifier)
    (payableProjects : ∀ terminal, payableToken = some terminal →
      RuleReduction.MarkerProjects file tokens terminal .payableModifier)
    (fallbackProjects : RuleReduction.MarkerProjects file tokens
      fallbackKw .fallbackName)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.fallbackDecl origin finish genericPrefix publicToken
        payableToken fallbackKw openParen parameters closeParen returnValue
        body publicProjects payableProjects fallbackProjects witness) := by
  let genericCore := LocationFragment.ofOption
    LocationFragment.ofGenericPrefix genericPrefix
  let publicCore := match publicToken with
    | none => LocationFragment.empty
    | some terminal => terminal.locationFragment
  let payableCore := match payableToken with
    | none => LocationFragment.empty
    | some terminal => terminal.locationFragment
  let fallbackCore := fallbackKw.locationFragment
  let parameterCore := LocationFragment.ofList
    LocationFragment.ofParameter parameters
  let returnCore := match returnValue with
    | none => LocationFragment.empty
    | some value => LocationFragment.ofTypeExpr value.2.1
  let core := LocationFragment.merge
    [genericCore, publicCore, payableCore, fallbackCore, parameterCore,
      returnCore, LocationFragment.ofBody body]
  apply WrappedLocation.projectedInput witness core
  · rw [RuleLocationView.ofRuleValue, LocationFragment.ofFallbackDecl_mk]
    cases publicToken <;> cases payableToken <;> cases returnValue <;>
      apply LocationFragment.eq_of_fields <;>
        simp [core, genericCore, publicCore, payableCore, fallbackCore,
          parameterCore, returnCore, sourceLoc, LocationFragment.ofOption,
          LocationFragment.leaf, MatchedTerminal.locationFragment,
          RuleReduction.marker, RuleReduction.terminalLoc]
  · apply LocationFragment.IsSubfragmentOf.merge
    intro fragment member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · cases genericPrefix with
      | none => exact LocationFragment.IsSubfragmentOf.empty _
      | some value =>
          apply
            EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
          apply EbnfValue.ContainsLocationFragment.transport (by rfl)
          apply EbnfValue.ContainsLocationFragment.sequence
          apply EbnfValues.ContainsLocationFragment.head
          apply EbnfValue.ContainsLocationFragment.optional
          exact EbnfValue.ContainsLocationFragment.rule .genericPrefix value
    · cases publicToken with
      | none => exact LocationFragment.IsSubfragmentOf.empty _
      | some terminal =>
          apply
            EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
          apply EbnfValue.ContainsLocationFragment.transport (by rfl)
          apply EbnfValue.ContainsLocationFragment.sequence
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.head
          apply EbnfValue.ContainsLocationFragment.optional
          exact EbnfValue.ContainsLocationFragment.terminal _ _
    · cases payableToken with
      | none => exact LocationFragment.IsSubfragmentOf.empty _
      | some terminal =>
          apply
            EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
          apply EbnfValue.ContainsLocationFragment.transport (by rfl)
          apply EbnfValue.ContainsLocationFragment.sequence
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.head
          apply EbnfValue.ContainsLocationFragment.optional
          exact EbnfValue.ContainsLocationFragment.terminal _ _
    · apply
        EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.terminal _ _
    · unfold parameterCore LocationFragment.ofList
      apply LocationFragment.IsSubfragmentOf.merge_map
      intro parameter parameterMember
      apply
        EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      apply EbnfValue.ContainsLocationFragment.list0
      · exact List.mem_map_of_mem parameterMember
      · exact EbnfValue.ContainsLocationFragment.rule .parameter parameter
    · cases returnValue with
      | none => exact LocationFragment.IsSubfragmentOf.empty _
      | some value =>
          apply
            EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
          apply EbnfValue.ContainsLocationFragment.transport (by rfl)
          apply EbnfValue.ContainsLocationFragment.sequence
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.head
          apply EbnfValue.ContainsLocationFragment.optional
          apply EbnfValue.ContainsLocationFragment.sequence
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.head
          exact EbnfValue.ContainsLocationFragment.rule .type value.2.1
    · apply
        EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.rule .body body
  · apply input_roots_ne_nil_of_inside
    · apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.terminal _ _
    · simp [MatchedTerminal.locationFragment]

theorem contractConstructorDecl_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (publicToken : Option
      (MatchedTerminal file tokens (.hardKeyword .publicKw)))
    (payableToken : Option
      (MatchedTerminal file tokens (.hardKeyword .payableKw)))
    (constructorKw : MatchedTerminal file tokens
      (.hardKeyword .constructorKw))
    (openParen : MatchedTerminal file tokens (.symbol .leftParen))
    (parameters : List Parameter)
    (closeParen : MatchedTerminal file tokens (.symbol .rightParen))
    (body : Body)
    (publicProjects : ∀ terminal, publicToken = some terminal →
      RuleReduction.MarkerProjects file tokens terminal .publicModifier)
    (payableProjects : ∀ terminal, payableToken = some terminal →
      RuleReduction.MarkerProjects file tokens terminal .payableModifier)
    (constructorProjects : RuleReduction.MarkerProjects file tokens
      constructorKw .contractConstructorName)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.contractConstructorDecl origin finish publicToken
        payableToken constructorKw openParen parameters closeParen body
        publicProjects payableProjects constructorProjects witness) := by
  let publicCore := match publicToken with
    | none => LocationFragment.empty
    | some terminal => terminal.locationFragment
  let payableCore := match payableToken with
    | none => LocationFragment.empty
    | some terminal => terminal.locationFragment
  let constructorCore := constructorKw.locationFragment
  let parameterCore := LocationFragment.ofList
    LocationFragment.ofParameter parameters
  let core := LocationFragment.merge
    [publicCore, payableCore, constructorCore, parameterCore,
      LocationFragment.ofBody body]
  apply WrappedLocation.projectedInput witness core
  · rw [RuleLocationView.ofRuleValue,
      LocationFragment.ofContractConstructorDecl_mk]
    cases publicToken <;> cases payableToken <;>
      apply LocationFragment.eq_of_fields <;>
        simp [core, publicCore, payableCore, constructorCore,
          parameterCore, sourceLoc, LocationFragment.ofOption,
          LocationFragment.leaf, MatchedTerminal.locationFragment,
          RuleReduction.marker, RuleReduction.terminalLoc]
  · apply LocationFragment.IsSubfragmentOf.merge
    intro fragment member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    · cases publicToken with
      | none => exact LocationFragment.IsSubfragmentOf.empty _
      | some terminal =>
          apply
            EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
          apply EbnfValue.ContainsLocationFragment.transport (by rfl)
          apply EbnfValue.ContainsLocationFragment.sequence
          apply EbnfValues.ContainsLocationFragment.head
          apply EbnfValue.ContainsLocationFragment.optional
          exact EbnfValue.ContainsLocationFragment.terminal _ _
    · cases payableToken with
      | none => exact LocationFragment.IsSubfragmentOf.empty _
      | some terminal =>
          apply
            EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
          apply EbnfValue.ContainsLocationFragment.transport (by rfl)
          apply EbnfValue.ContainsLocationFragment.sequence
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.head
          apply EbnfValue.ContainsLocationFragment.optional
          exact EbnfValue.ContainsLocationFragment.terminal _ _
    · apply
        EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.terminal _ _
    · unfold parameterCore LocationFragment.ofList
      apply LocationFragment.IsSubfragmentOf.merge_map
      intro parameter parameterMember
      apply
        EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      apply EbnfValue.ContainsLocationFragment.list0
      · exact List.mem_map_of_mem parameterMember
      · exact EbnfValue.ContainsLocationFragment.rule .parameter parameter
    · apply
        EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.rule .body body
  · apply input_roots_ne_nil_of_inside
    · apply EbnfValue.ContainsLocationFragment.transport (by rfl)
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.terminal _ _
    · simp [MatchedTerminal.locationFragment]

end RuleReduction.WrappedLocation

end Solcore.Surface.Multi
