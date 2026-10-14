import Solcore.SourceSemantics.Graph
import Solcore.SourceSemantics.Static

set_option autoImplicit false
set_option Elab.async false

namespace Solcore.SourceSemantics.SourceInferenceSoundness

open Frontend.SourceInference TypeSystem

/-- Every proper child occurrence keeps its complete substituted record.
The root may receive an output coercion while its children remain unchanged. -/
structure ProperDescendantsPreserved (substitution : Substitution)
    (before after : TypedSource) (root : NodeId) : Prop where
  owner_eq : after.owner = before.owner
  nodes : ∀ node, node ∈ before.nodes → Descends before root node.id →
    node.applySubstitution substitution ∈ after.nodes

/-- Actual proper descendants retain their original records before final
substitution. A later attachment may still replace the enclosing root. -/
structure RawProperDescendantsPreserved (before after : TypedSource) (root : NodeId) : Prop where
  owner_eq : after.owner = before.owner
  nodes : ∀ node, node ∈ before.nodes → Descends before root node.id → node ∈ after.nodes

namespace RawProperDescendantsPreserved

theorem ofTypingSourceExtends {before after : TypedSource} {root : NodeId}
    (extension : TypingSourceExtends before after) : RawProperDescendantsPreserved before after root :=
  ⟨extension.owner_eq, fun _ member _ => extension.nodes_prefix.subset member⟩

private theorem path_prefix {before after : TypedSource} {root child : NodeId}
    (extension : TypingSourceExtends before after) (path : Descends before root child) :
    Descends after root child := by
  induction path with
  | direct edge =>
    obtain ⟨parent, contains, edge⟩ := edge
    exact .direct ⟨parent, ⟨extension.nodes_prefix.subset contains.1, contains.2⟩, edge⟩
  | step edge _ next =>
    obtain ⟨parent, contains, edge⟩ := edge
    exact .step ⟨parent, ⟨extension.nodes_prefix.subset contains.1, contains.2⟩, edge⟩ next

theorem monoBefore {before middle after : TypedSource} {root : NodeId}
    (preserved : RawProperDescendantsPreserved middle after root)
    (extension : TypingSourceExtends before middle) : RawProperDescendantsPreserved before after root := by
  refine ⟨preserved.owner_eq.trans extension.owner_eq, ?_⟩
  intro node member path
  exact preserved.nodes node (extension.nodes_prefix.subset member) (path_prefix extension path)

end RawProperDescendantsPreserved

namespace ProperDescendantsPreserved

theorem ofTypingSourceExtends
    {substitution : Substitution} {before after : TypedSource} {root : NodeId}
    (extension : TypingSourceExtends
      (before.applySubstitution substitution) after) :
    ProperDescendantsPreserved substitution before after root := by
  refine ⟨extension.owner_eq, ?_⟩
  intro node member _
  exact extension.nodes_prefix.subset (List.mem_map.mpr ⟨node, member, rfl⟩)

theorem child
    {substitution : Substitution} {before after : TypedSource}
    {root child : NodeId}
    (preserved : ProperDescendantsPreserved substitution before after root)
    (edge : DirectChild before root child) :
    ProperDescendantsPreserved substitution before after child := by
  refine ⟨preserved.owner_eq, ?_⟩
  intro node member path
  exact preserved.nodes node member (.step edge path)

theorem containsNode
    {substitution : Substitution} {before after : TypedSource}
    {root child : NodeId} {node : Node}
    (preserved : ProperDescendantsPreserved substitution before after root)
    (path : Descends before root child)
    (contains : ContainsNode before child node) :
    ContainsNode after child (node.applySubstitution substitution) := by
  refine ⟨preserved.nodes node contains.1 ?_, ?_⟩
  · simpa [contains.2] using path
  · simpa using contains.2

theorem transExtension
    {substitution : Substitution} {before middle after : TypedSource}
    {root : NodeId}
    (preserved : ProperDescendantsPreserved substitution before middle root)
    (extension : TypingSourceExtends middle after) :
    ProperDescendantsPreserved substitution before after root := by
  exact ⟨extension.owner_eq.trans preserved.owner_eq,
    fun node member path => extension.nodes_prefix.subset
      (preserved.nodes node member path)⟩

end ProperDescendantsPreserved

/-- A source transport is restricted to a set closed under actual source
edges. It contains no declarative typing assumption. -/
structure SourceSubgraphTransport (before after : TypedSource)
    (reached : NodeId → Prop) : Prop where
  owner_eq : after.owner = before.owner
  nodes : ∀ node, node ∈ before.nodes → reached node.id → node ∈ after.nodes
  children : ∀ node, node ∈ before.nodes → reached node.id →
    ∀ child, child ∈ node.references → reached child

namespace SourceSubgraphTransport

theorem containsExpression
    {before after : TypedSource} {reached : NodeId → Prop}
    {id : ExpressionId} {node : ExpressionNode}
    (transport : SourceSubgraphTransport before after reached)
    (contains : ContainsExpression before id node)
    (selected : reached (.expression id)) : ContainsExpression after id node := by
  exact ⟨transport.nodes (.expression node) contains.1
    (by simpa [Node.id, contains.2] using selected), contains.2⟩

theorem containsStatement
    {before after : TypedSource} {reached : NodeId → Prop}
    {id : StatementId} {node : StatementNode}
    (transport : SourceSubgraphTransport before after reached)
    (contains : ContainsStatement before id node)
    (selected : reached (.statement id)) : ContainsStatement after id node := by
  exact ⟨transport.nodes (.statement node) contains.1
    (by simpa [Node.id, contains.2] using selected), contains.2⟩

theorem expression_children
    {before after : TypedSource} {reached : NodeId → Prop}
    {id : ExpressionId} {node : ExpressionNode}
    (transport : SourceSubgraphTransport before after reached)
    (contains : ContainsExpression before id node)
    (selected : reached (.expression id)) :
    ∀ child ∈ node.form.references, reached child := by
  exact transport.children (.expression node) contains.1
    (by simpa [Node.id, contains.2] using selected)

theorem statement_children
    {before after : TypedSource} {reached : NodeId → Prop}
    {id : StatementId} {node : StatementNode}
    (transport : SourceSubgraphTransport before after reached)
    (contains : ContainsStatement before id node)
    (selected : reached (.statement id)) :
    ∀ child ∈ node.form.references, reached child := by
  exact transport.children (.statement node) contains.1
    (by simpa [Node.id, contains.2] using selected)

end SourceSubgraphTransport

theorem ProperDescendantsPreserved.subgraph
    {substitution : Substitution} {before after : TypedSource} {root : NodeId}
    (preserved : ProperDescendantsPreserved substitution before after root) :
    SourceSubgraphTransport (before.applySubstitution substitution) after
      (Descends before root) := by
  refine ⟨preserved.owner_eq, ?_, ?_⟩
  · intro node member path
    change node ∈ before.nodes.map (Node.applySubstitution substitution) at member
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    exact preserved.nodes original originalMember (by simpa using path)
  · intro node member path child edge
    have found : ContainsNode (before.applySubstitution substitution)
        node.id node := ⟨member, rfl⟩
    obtain ⟨original, contains, same⟩ :=
      FlexibleSubstitution.containsNode_of_applySubstitution found
    have originalEdge : DirectChild before node.id child :=
      ⟨original, contains, by simpa [nodeChildIds, ← same] using edge⟩
    exact path.trans (.direct originalEdge)

end Solcore.SourceSemantics.SourceInferenceSoundness
