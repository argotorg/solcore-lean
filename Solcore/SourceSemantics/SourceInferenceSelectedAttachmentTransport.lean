import Solcore.SourceSemantics.SourceInferenceSubtreeTransport
import Solcore.SourceSemantics.SourceInferenceSoundness

set_option autoImplicit false
set_option Elab.async false

namespace Solcore.SourceSemantics.SourceInferenceSoundness

open Frontend.SourceInference TypeSystem

/-- Coercion attachment preserves the actual occurrence edges even at the
expression roots whose type and coercion records it updates. -/
theorem attachExpressionCoercions_nodeReferences
    (state : State) (entries : List Detail.ExpressionCoercions)
    {node : Node} (member : node ∈ state.nodes) :
    ∃ attached ∈ (Detail.attachExpressionCoercions state entries).nodes,
      attached.id = node.id ∧ nodeChildIds attached = nodeChildIds node := by
  induction entries generalizing state node with
  | nil => exact ⟨node, member, rfl, rfl⟩
  | cons entry entries induction =>
    let changed := state.modifyExpressionNode entry.expression fun node =>
      Detail.appendExpressionCoercions node entry.coercions
    have one : ∃ next ∈ changed.nodes,
        next.id = node.id ∧ nodeChildIds next = nodeChildIds node := by
      cases node with
      | statement node =>
        refine ⟨.statement node, ?_, rfl, rfl⟩
        exact List.mem_map.mpr ⟨.statement node, member, rfl⟩
      | expression node =>
        by_cases same : node.id = entry.expression
        · refine ⟨.expression { Detail.appendExpressionCoercions node
            entry.coercions with id := entry.expression }, ?_, ?_, rfl⟩
          · exact List.mem_map.mpr ⟨.expression node, member,
              by simp [same]⟩
          · exact congrArg NodeId.expression same.symm
        · refine ⟨.expression node, ?_, rfl, rfl⟩
          exact List.mem_map.mpr ⟨.expression node, member,
            by simp [same]⟩
    obtain ⟨next, nextMember, sameId, sameChildren⟩ := one
    obtain ⟨attached, attachedMember, attachedId, attachedChildren⟩ :=
      induction changed nextMember
    exact ⟨attached, attachedMember, attachedId.trans sameId,
      attachedChildren.trans sameChildren⟩

theorem attachExpressionCoercions_directChild
    (state : State) (entries : List Detail.ExpressionCoercions)
    (roots : List NodeId) {parent child : NodeId}
    (edge : DirectChild (state.toTypedSource roots) parent child) :
    DirectChild ((Detail.attachExpressionCoercions state entries).toTypedSource roots)
      parent child := by
  obtain ⟨node, contains, childMember⟩ := edge
  obtain ⟨attached, member, same, children⟩ :=
    attachExpressionCoercions_nodeReferences state entries contains.1
  exact ⟨attached, ⟨member, same.trans contains.2⟩, children ▸ childMember⟩

theorem attachExpressionCoercions_descends
    (state : State) (entries : List Detail.ExpressionCoercions)
    (roots : List NodeId) {parent child : NodeId}
    (path : Descends (state.toTypedSource roots) parent child) :
    Descends ((Detail.attachExpressionCoercions state entries).toTypedSource roots)
      parent child := by
  induction path with
  | direct edge => exact .direct (attachExpressionCoercions_directChild state entries roots edge)
  | step edge _ next =>
    exact .step (attachExpressionCoercions_directChild state entries roots edge) next

theorem SubtreePreserved.directChild
    {substitution : Substitution} {before after : TypedSource}
    {root child : NodeId}
    (preserved : SubtreePreserved substitution before after root)
    (edge : DirectChild before root child) : DirectChild after root child := by
  obtain ⟨node, contains, member⟩ := edge
  refine ⟨node.applySubstitution substitution, ⟨?_, ?_⟩, ?_⟩
  · exact preserved.nodes node contains.1 (.inl contains.2)
  · simpa using contains.2
  · simpa [nodeChildIds] using member

theorem SubtreePreserved.descends
    {substitution : Substitution} {before after : TypedSource}
    {root child : NodeId} (path : Descends before root child) :
    SubtreePreserved substitution before after root → Descends after root child := by
  induction path with
  | direct edge => intro preserved; exact .direct (preserved.directChild edge)
  | step edge _ next =>
      intro preserved
      exact .step (preserved.directChild edge) (next (preserved.child edge))

/-- Distinct operand positions in a closed occurrence tree cannot occur
inside each other. This also excludes a position from its own descendants. -/
theorem sibling_not_descends
    {source : TypedSource} {parent left right : NodeId}
    (closed : OccurrenceGraphClosed source)
    (leftEdge : DirectChild source parent left)
    (rightEdge : DirectChild source parent right) :
    ¬ Descends source left right := by
  intro path
  obtain ⟨lastParent, lastEdge, priorPath⟩ := path.final_edge
  have same : lastParent = parent :=
    closed.childHasUniqueParent lastEdge rightEdge
  subst lastParent
  rcases priorPath with same | priorPath
  · subst left
    exact closed.acyclic parent (.direct leftEdge)
  · exact closed.acyclic parent (.step leftEdge priorPath)

private theorem attach_containsStatement
    (state : State) (entries : List Detail.ExpressionCoercions)
    {id : StatementId} {node : StatementNode} (roots : List NodeId)
    (contains : ContainsStatement (state.toTypedSource roots) id node) :
    ContainsStatement
      ((Detail.attachExpressionCoercions state entries).toTypedSource roots)
      id node := by
  induction entries generalizing state with
  | nil => simpa [Detail.attachExpressionCoercions] using contains
  | cons entry entries induction =>
    apply induction
    refine ⟨?_, contains.2⟩
    change Node.statement node ∈ state.nodes.map _
    exact List.mem_map.mpr ⟨.statement node, contains.1, rfl⟩

private theorem attach_owner
    (state : State) (entries : List Detail.ExpressionCoercions) :
    (Detail.attachExpressionCoercions state entries).owner = state.owner := by
  induction entries generalizing state with
  | nil => rfl
  | cons entry entries induction =>
    exact induction (state.modifyExpressionNode entry.expression fun node =>
      Detail.appendExpressionCoercions node entry.coercions)

theorem rawProperDescendantsPreserved_attachExpressionCoercions
    (state : State) (entries : List Detail.ExpressionCoercions)
    (roots : List NodeId) (root : NodeId)
    (disjoint : ∀ entry ∈ entries,
      ¬ Descends (state.toTypedSource roots) root (.expression entry.expression)) :
    RawProperDescendantsPreserved (state.toTypedSource roots)
      ((Detail.attachExpressionCoercions state entries).toTypedSource roots) root := by
  refine ⟨attach_owner state entries, ?_⟩
  intro node member path
  cases node with
  | expression node =>
    have absent : node.id ∉ entries.map (·.expression) := by
      intro present
      obtain ⟨entry, entryMember, same⟩ := List.mem_map.mp present
      exact disjoint entry entryMember (by simpa [same, Node.id] using path)
    exact (attachExpressionCoercions_containsExpression_of_not_mem state
      entries node.id node roots absent ⟨member, rfl⟩).1
  | statement node =>
    exact (attach_containsStatement state entries roots ⟨member, rfl⟩).1

/-- Actual coercion attachment changes only its named expression roots.
Every proper descendant outside that exact row retains its full record. -/
theorem properDescendantsPreserved_attachExpressionCoercions
    (state : State) (entries : List Detail.ExpressionCoercions)
    (roots : List NodeId) (root : NodeId) (substitution : Substitution)
    (disjoint : ∀ entry ∈ entries,
      ¬ Descends (state.toTypedSource roots) root (.expression entry.expression)) :
    ProperDescendantsPreserved substitution (state.toTypedSource roots)
      (((Detail.attachExpressionCoercions state entries).toTypedSource roots
        ).applySubstitution substitution) root := by
  refine ⟨attach_owner state entries, ?_⟩
  intro node member path
  apply List.mem_map.mpr
  refine ⟨node, ?_, rfl⟩
  cases node with
  | expression node =>
    have absent : node.id ∉ entries.map (·.expression) := by
      intro present
      obtain ⟨entry, entryMember, same⟩ := List.mem_map.mp present
      exact disjoint entry entryMember (by simpa [same, Node.id] using path)
    exact (attachExpressionCoercions_containsExpression_of_not_mem state
      entries node.id node roots absent ⟨member, rfl⟩).1
  | statement node =>
    exact (attach_containsStatement state entries roots ⟨member, rfl⟩).1

/-- A real operand edge and the final occurrence tree discharge disjointness
for an ordered row of sibling coercion targets. -/
theorem properDescendantsPreserved_attach_siblings
    (state : State) (entries : List Detail.ExpressionCoercions)
    (roots : List NodeId) (root parent : NodeId) (substitution : Substitution)
    (evidenceSource : TypedSource)
    (closed : OccurrenceGraphClosed evidenceSource)
    (rootEdge : DirectChild evidenceSource parent root)
    (entryEdges : ∀ entry ∈ entries,
      DirectChild evidenceSource parent (.expression entry.expression))
    (paths : ∀ child, Descends (state.toTypedSource roots) root child →
      Descends evidenceSource root child) :
    ProperDescendantsPreserved substitution (state.toTypedSource roots)
      (((Detail.attachExpressionCoercions state entries).toTypedSource roots
        ).applySubstitution substitution) root := by
  apply properDescendantsPreserved_attachExpressionCoercions
  intro entry member path
  exact sibling_not_descends closed rootEdge (entryEdges entry member)
    (paths _ path)

/-- The actual final tree discharges attachment disjointness. The path
transport is derived from the attachment action and its retained subtree. -/
theorem rawProperDescendantsPreserved_attach_final
    (state : State) (entries : List Detail.ExpressionCoercions)
    (roots : List NodeId) (root parent : NodeId) (substitution : Substitution)
    (finalSource : TypedSource)
    (closed : OccurrenceGraphClosed finalSource)
    (rootEdge : DirectChild finalSource parent root)
    (entryEdges : ∀ entry ∈ entries,
      DirectChild finalSource parent (.expression entry.expression))
    (retained : SubtreePreserved substitution
      ((Detail.attachExpressionCoercions state entries).toTypedSource roots)
      finalSource root) :
    RawProperDescendantsPreserved (state.toTypedSource roots)
      ((Detail.attachExpressionCoercions state entries).toTypedSource roots) root := by
  apply rawProperDescendantsPreserved_attachExpressionCoercions
  intro entry member path
  exact sibling_not_descends closed rootEdge (entryEdges entry member)
    (SubtreePreserved.descends
      (attachExpressionCoercions_descends state entries roots path) retained)

theorem SubtreePreserved.before_attachment
    (state : State) (entries : List Detail.ExpressionCoercions)
    (roots : List NodeId) (root : NodeId)
    {substitution : Substitution} {after : TypedSource}
    (preserved : SubtreePreserved substitution
      ((Detail.attachExpressionCoercions state entries).toTypedSource roots) after root)
    (unchanged : RawProperDescendantsPreserved (state.toTypedSource roots)
      ((Detail.attachExpressionCoercions state entries).toTypedSource roots) root) :
    ProperDescendantsPreserved substitution (state.toTypedSource roots) after root := by
  refine ⟨preserved.owner_eq.trans unchanged.owner_eq, ?_⟩
  intro node member path
  exact preserved.nodes node (unchanged.nodes node member path)
    (.inr (attachExpressionCoercions_descends state entries roots path))

theorem RawSubtreePreserved.before_attachment
    (state : State) (entries : List Detail.ExpressionCoercions)
    (roots : List NodeId) (root : NodeId) {after : TypedSource}
    (preserved : RawSubtreePreserved
      ((Detail.attachExpressionCoercions state entries).toTypedSource roots) after root)
    (unchanged : RawProperDescendantsPreserved (state.toTypedSource roots)
      ((Detail.attachExpressionCoercions state entries).toTypedSource roots) root) :
    RawProperDescendantsPreserved (state.toTypedSource roots) after root := by
  refine ⟨preserved.owner_eq.trans unchanged.owner_eq, ?_⟩
  intro node member path
  exact preserved.nodes node (unchanged.nodes node member path)
    (.inr (attachExpressionCoercions_descends state entries roots path))

/-- The raw form is typed using exactly the retained proper descendants;
the original root record continues to supply its own requirements. -/
theorem ExpressionTypingBase.transportSemanticChildren
    {before after : TypedSource} {context : Context}
    {substitution : Substitution} {inferred : InferredExpression}
    (base : ExpressionTypingBase before (before.applySubstitution substitution)
      context substitution inferred)
    (preserved : ProperDescendantsPreserved substitution before after
      (.expression inferred.id)) :
    ExpressionTypingBase before after context substitution inferred := by
  cases base with
  | intro contains typeEq formType rawAdmissible requirements =>
    refine .intro contains typeEq (preserved.subgraph.form formType ?_)
      rawAdmissible requirements
    intro child member
    apply Descends.direct
    refine ⟨_, ⟨contains.1, ?_⟩, ?_⟩
    · exact congrArg NodeId.expression contains.2
    · simpa [nodeChildIds, Node.references] using member

end Solcore.SourceSemantics.SourceInferenceSoundness
