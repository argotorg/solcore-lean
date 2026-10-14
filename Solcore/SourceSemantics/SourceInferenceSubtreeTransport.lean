import Solcore.SourceSemantics.SourceInferenceRootedTyping

/-! Only the returned occurrence subtree must retain its complete records.
Unrelated earlier roots may change during enclosing coercion attachment. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend.SourceInference TypeSystem

structure SubtreePreserved (substitution : Substitution)
    (before after : TypedSource) (root : NodeId) : Prop where
  owner_eq : after.owner = before.owner
  nodes : ∀ node, node ∈ before.nodes →
    (node.id = root ∨ Descends before root node.id) →
    node.applySubstitution substitution ∈ after.nodes

namespace SubtreePreserved
variable {substitution : Substitution} {before middle after : TypedSource}
  {root childId : NodeId}

theorem ofTypingSourceExtends
    (extension : TypingSourceExtends (before.applySubstitution substitution) after) :
    SubtreePreserved substitution before after root := by
  refine ⟨extension.owner_eq, ?_⟩
  intro node member _
  exact extension.nodes_prefix.subset (List.mem_map.mpr ⟨node, member, rfl⟩)

theorem proper (preserved : SubtreePreserved substitution before after root) :
    ProperDescendantsPreserved substitution before after root :=
  ⟨preserved.owner_eq, fun node member path => preserved.nodes node member (.inr path)⟩

theorem child (preserved : SubtreePreserved substitution before after root)
    (edge : DirectChild before root childId) :
    SubtreePreserved substitution before after childId := by
  refine ⟨preserved.owner_eq, ?_⟩
  intro node member path
  apply preserved.nodes node member
  rcases path with same | path
  · exact .inr (same ▸ Descends.direct edge)
  · exact .inr (.step edge path)

theorem transExtension (preserved : SubtreePreserved substitution before middle root)
    (extension : TypingSourceExtends middle after) :
    SubtreePreserved substitution before after root :=
  ⟨extension.owner_eq.trans preserved.owner_eq,
    fun node member path => extension.nodes_prefix.subset (preserved.nodes node member path)⟩

private theorem path_prefix (extension : TypingSourceExtends before middle)
    (path : Descends before root childId) : Descends middle root childId := by
  induction path with
  | direct edge =>
      rcases edge with ⟨node, contains, member⟩
      exact .direct ⟨node, ⟨extension.nodes_prefix.subset contains.1, contains.2⟩, member⟩
  | step edge _ next =>
      rcases edge with ⟨node, contains, member⟩
      exact .step ⟨node, ⟨extension.nodes_prefix.subset contains.1, contains.2⟩, member⟩ next

theorem monoBefore (preserved : SubtreePreserved substitution middle after root)
    (extension : TypingSourceExtends before middle) :
    SubtreePreserved substitution before after root := by
  refine ⟨preserved.owner_eq.trans extension.owner_eq, ?_⟩
  intro node member path
  apply preserved.nodes node (extension.nodes_prefix.subset member)
  exact path.elim Or.inl (fun path => .inr (path_prefix extension path))

theorem subgraph (preserved : SubtreePreserved substitution before after root) :
    SourceSubgraphTransport (before.applySubstitution substitution) after
      (fun id => id = root ∨ Descends before root id) := by
  refine ⟨preserved.owner_eq, ?_, ?_⟩
  · intro node member path
    change node ∈ before.nodes.map (Node.applySubstitution substitution) at member
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    exact preserved.nodes original originalMember (by simpa using path)
  · intro node member path child edge
    have found : ContainsNode (before.applySubstitution substitution) node.id node := ⟨member, rfl⟩
    obtain ⟨original, contains, same⟩ :=
      FlexibleSubstitution.containsNode_of_applySubstitution found
    have originalEdge : DirectChild before node.id child :=
      ⟨original, contains, by simpa [nodeChildIds, ← same] using edge⟩
    exact .inr (path.elim (fun same => same ▸ Descends.direct originalEdge)
      (fun path => path.trans (.direct originalEdge)))

end SubtreePreserved
/-- The exact unmodified records used by the actual finalization state. -/
structure RawSubtreePreserved (before after : TypedSource) (root : NodeId) : Prop where
  owner_eq : after.owner = before.owner
  nodes : ∀ node, node ∈ before.nodes →
    (node.id = root ∨ Descends before root node.id) → node ∈ after.nodes

theorem RawProperDescendantsPreserved.childSubtree
    {before after : TypedSource} {root child : NodeId}
    (preserved : RawProperDescendantsPreserved before after root)
    (edge : DirectChild before root child) : RawSubtreePreserved before after child := by
  refine ⟨preserved.owner_eq, ?_⟩
  intro node member path
  exact preserved.nodes node member
    (path.elim (fun same => same ▸ Descends.direct edge) (fun path => .step edge path))

namespace RawSubtreePreserved
variable {before middle after : TypedSource} {root childId : NodeId}

theorem proper (preserved : RawSubtreePreserved before after root) :
    RawProperDescendantsPreserved before after root :=
  ⟨preserved.owner_eq, fun node member path => preserved.nodes node member (.inr path)⟩

theorem ofTypingSourceExtends (extension : TypingSourceExtends before after) :
    RawSubtreePreserved before after root :=
  ⟨extension.owner_eq, fun _ member _ => extension.nodes_prefix.subset member⟩

theorem monoBefore (preserved : RawSubtreePreserved middle after root)
    (extension : TypingSourceExtends before middle) :
    RawSubtreePreserved before after root := by
  refine ⟨preserved.owner_eq.trans extension.owner_eq, ?_⟩
  intro node member path
  apply preserved.nodes node (extension.nodes_prefix.subset member)
  exact path.elim Or.inl (fun path => .inr (SubtreePreserved.path_prefix extension path))

theorem child (preserved : RawSubtreePreserved before after root)
    (edge : DirectChild before root childId) : RawSubtreePreserved before after childId := by
  refine ⟨preserved.owner_eq, ?_⟩
  intro node member path
  apply preserved.nodes node member
  exact .inr (path.elim (fun same => same ▸ Descends.direct edge) (fun path => .step edge path))

theorem substituted (preserved : RawSubtreePreserved before after root)
    (substitution : Substitution) :
    SubtreePreserved substitution before (after.applySubstitution substitution) root := by
  refine ⟨preserved.owner_eq, ?_⟩
  intro node member path
  exact List.mem_map.mpr ⟨node, preserved.nodes node member path, rfl⟩

end RawSubtreePreserved
end Solcore.SourceSemantics.SourceInferenceSoundness
