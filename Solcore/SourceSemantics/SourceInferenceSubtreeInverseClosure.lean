import Solcore.SourceSemantics.SourceInferenceSubtreeTransport

/-! A closed earlier subtree cannot acquire descendants when its complete
records are preserved in a later source with unique occurrence identities. -/
set_option autoImplicit false
set_option Elab.async false

namespace Solcore.SourceSemantics.SourceInferenceSoundness.RawSubtreePreserved
open Frontend.SourceInference

private theorem node_unique {source : TypedSource} (unique : NodeOccurrencesUnique source)
    {left right : Node} (leftMember : left ∈ source.nodes)
    (rightMember : right ∈ source.nodes) (same : left.id = right.id) :
    left = right := by
  have occurrence : left.occurrenceId = right.occurrenceId :=
    congrArg NodeId.occurrenceId same
  have leftLookup := lookupNode?_complete unique leftMember occurrence
  have rightLookup := lookupNode?_complete unique rightMember rfl
  exact Option.some.inj (leftLookup.symm.trans rightLookup)

private theorem direct_inverse {before after : TypedSource} {root child : NodeId}
    (preserved : RawSubtreePreserved before after root)
    (closed : ChildEdgesExist before) (present : root ∈ nodeIds before)
    (unique : NodeOccurrencesUnique after) (edge : DirectChild after root child) :
    DirectChild before root child ∧ child ∈ nodeIds before := by
  obtain ⟨original, member, id⟩ := List.mem_map.mp present
  obtain ⟨later, contains, reference⟩ := edge
  have retained := preserved.nodes original member (.inl id)
  have same : original = later :=
    node_unique unique retained contains.1 (id.trans contains.2.symm)
  subst later
  exact ⟨⟨original, ⟨member, id⟩, reference⟩, closed original member child reference⟩

/-- Every later path from the preserved root was already an earlier path. -/
theorem descends_inverse {before after : TypedSource} {root child : NodeId}
    (preserved : RawSubtreePreserved before after root)
    (closed : ChildEdgesExist before) (present : root ∈ nodeIds before)
    (unique : NodeOccurrencesUnique after) (path : Descends after root child) :
    Descends before root child ∧ child ∈ nodeIds before := by
  induction path with
  | direct edge =>
      have earlier := direct_inverse preserved closed present unique edge
      exact ⟨.direct earlier.1, earlier.2⟩
  | step edge tail ih =>
      have earlier := direct_inverse preserved closed present unique edge
      have rest := ih (preserved.child earlier.1) earlier.2
      exact ⟨.step earlier.1 rest.1, rest.2⟩

/-- The same inclusion holds for the root together with all its descendants. -/
theorem reflexive_inverse {before after : TypedSource} {root child : NodeId}
    (preserved : RawSubtreePreserved before after root)
    (closed : ChildEdgesExist before) (present : root ∈ nodeIds before)
    (unique : NodeOccurrencesUnique after)
    (path : child = root ∨ Descends after root child) :
    (child = root ∨ Descends before root child) ∧ child ∈ nodeIds before := by
  rcases path with same | path
  · exact ⟨.inl same, same ▸ present⟩
  · have earlier := preserved.descends_inverse closed present unique path
    exact ⟨.inr earlier.1, earlier.2⟩

/-- Recover the complete earlier record, including its local reference target. -/
theorem node_inverse {before after : TypedSource} {root : NodeId}
    (preserved : RawSubtreePreserved before after root)
    (closed : ChildEdgesExist before) (present : root ∈ nodeIds before)
    (unique : NodeOccurrencesUnique after) {node : Node} (member : node ∈ after.nodes)
    (path : node.id = root ∨ Descends after root node.id) :
    node ∈ before.nodes := by
  have earlier := preserved.reflexive_inverse closed present unique path
  obtain ⟨original, originalMember, id⟩ := List.mem_map.mp earlier.2
  have originalPath : original.id = root ∨ Descends before root original.id := by
    simpa only [id] using earlier.1
  have retained := preserved.nodes original originalMember originalPath
  have same := node_unique unique retained member id
  exact same ▸ originalMember

end Solcore.SourceSemantics.SourceInferenceSoundness.RawSubtreePreserved
