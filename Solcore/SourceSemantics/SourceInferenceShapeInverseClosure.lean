import Solcore.Frontend.SourceInference.NodeShapeProperties
import Solcore.SourceSemantics.SourceInferenceSubtreeTransport

/-! Shape preservation suffices to recover earlier paths and local targets.
Coercion metadata and final expression types need not be unchanged. -/
set_option autoImplicit false
set_option Elab.async false

namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend.SourceInference
namespace NodeShapesPreserved

private theorem node_unique {source : TypedSource} (unique : NodeOccurrencesUnique source)
    {left right : Node} (leftMember : left ∈ source.nodes)
    (rightMember : right ∈ source.nodes) (same : left.id = right.id) :
    left = right := by
  have occurrence := congrArg NodeId.occurrenceId same
  have leftLookup := lookupNode?_complete unique leftMember occurrence
  have rightLookup := lookupNode?_complete unique rightMember rfl
  exact Option.some.inj (leftLookup.symm.trans rightLookup)

private theorem direct_inverse {before after : TypedSource} {root child : NodeId}
    (preserved : NodeShapesPreserved before.nodes after.nodes)
    (closed : ChildEdgesExist before) (present : root ∈ nodeIds before)
    (unique : NodeOccurrencesUnique after) (edge : DirectChild after root child) :
    DirectChild before root child ∧ child ∈ nodeIds before := by
  obtain ⟨original, member, id⟩ := List.mem_map.mp present
  obtain ⟨later, contains, reference⟩ := edge
  obtain ⟨current, retained, shape⟩ := preserved original member
  have same : current = later :=
    node_unique unique retained contains.1 (shape.id.symm.trans (id.trans contains.2.symm))
  subst later
  have originalReference : child ∈ nodeChildIds original := by
    simpa only [nodeChildIds, shape.references] using reference
  exact ⟨⟨original, ⟨member, id⟩, originalReference⟩,
    closed original member child originalReference⟩

theorem descends_inverse {before after : TypedSource} {root child : NodeId}
    (preserved : NodeShapesPreserved before.nodes after.nodes)
    (closed : ChildEdgesExist before) (present : root ∈ nodeIds before)
    (unique : NodeOccurrencesUnique after) (path : Descends after root child) :
    Descends before root child ∧ child ∈ nodeIds before := by
  induction path with
  | direct edge =>
      have earlier := direct_inverse preserved closed present unique edge
      exact ⟨.direct earlier.1, earlier.2⟩
  | step edge tail ih =>
      have earlier := direct_inverse preserved closed present unique edge
      have rest := ih earlier.2
      exact ⟨.step earlier.1 rest.1, rest.2⟩

theorem node_inverse {before after : TypedSource} {root : NodeId}
    (preserved : NodeShapesPreserved before.nodes after.nodes)
    (closed : ChildEdgesExist before) (present : root ∈ nodeIds before)
    (unique : NodeOccurrencesUnique after) {node : Node} (member : node ∈ after.nodes)
    (path : node.id = root ∨ Descends after root node.id) :
    ∃ original ∈ before.nodes, SameNodeShape original node := by
  have earlier : node.id ∈ nodeIds before := by
    rcases path with same | path
    · exact same ▸ present
    · exact (descends_inverse preserved closed present unique path).2
  obtain ⟨original, originalMember, id⟩ := List.mem_map.mp earlier
  obtain ⟨current, retained, shape⟩ := preserved original originalMember
  have same := node_unique unique retained member (shape.id.symm.trans id)
  exact ⟨original, originalMember, same ▸ shape⟩

theorem local_read_inverse {before after : TypedSource} {root : NodeId}
    (preserved : NodeShapesPreserved before.nodes after.nodes)
    (closed : ChildEdgesExist before) (present : root ∈ nodeIds before)
    (unique : NodeOccurrencesUnique after)
    {read : ExpressionNode} (member : Node.expression read ∈ after.nodes)
    (path : NodeId.expression read.id = root ∨ Descends after root (.expression read.id))
    {name : String} {binder : Resolved.LocalId}
    (form : read.form = .reference name (.local binder)) :
    ∃ original : ExpressionNode, Node.expression original ∈ before.nodes ∧
      original.id = read.id ∧ original.form = .reference name (.local binder) := by
  obtain ⟨original, originalMember, shape⟩ :=
    node_inverse preserved closed present unique member path
  cases original with
  | statement _ => cases shape
  | expression original =>
      exact ⟨original, originalMember, shape.1, shape.2.trans form⟩

end NodeShapesPreserved
end Solcore.SourceSemantics.SourceInferenceSoundness
