import Solcore.SourceSemantics.WellFormed
import Solcore.SourceSemantics.Ownership
import Solcore.SourceSemantics.Substitution

/-!
Reachability and acyclicity of resolved source occurrence graphs.

The base closure judgment proves that every retained edge names a node.  This
module additionally excludes unreachable table entries and cyclic occurrence
spines, independently of the executable lookup functions.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics

open Frontend.SourceInference

/-- One direct, category-preserving occurrence edge. -/
def DirectChild (source : TypedSource) (parent child : NodeId) : Prop :=
  ∃ node, ContainsNode source parent node ∧ child ∈ nodeChildIds node

/-- A nonempty path through direct occurrence edges. -/
inductive Descends (source : TypedSource) : NodeId → NodeId → Prop where
  | direct {parent child : NodeId}
      (edge : DirectChild source parent child) :
      Descends source parent child
  | step {parent middle child : NodeId}
      (edge : DirectChild source parent middle)
      (tail : Descends source middle child) :
      Descends source parent child

/-- An occurrence is reachable from one of the declaration roots. -/
inductive Reachable (source : TypedSource) : NodeId → Prop where
  | root {id : NodeId} (member : id ∈ source.roots) : Reachable source id
  | child {parent child : NodeId}
      (parent_reachable : Reachable source parent)
      (edge : DirectChild source parent child) :
      Reachable source child

/-- Every retained table node contributes to the represented declaration. -/
def AllNodesReachable (source : TypedSource) : Prop :=
  ∀ node, node ∈ source.nodes → Reachable source node.id

/-- No occurrence can be its own proper descendant. -/
def OccurrenceGraphAcyclic (source : TypedSource) : Prop :=
  ∀ id, ¬ Descends source id id

/-- Declaration roots are occurrence positions, rather than a bag of entry
points.  Repeating a root would execute the same occurrence more than once. -/
def RootsUnique (source : TypedSource) : Prop :=
  source.roots.Nodup

/-- A parent may not retain the same child occurrence in two operand slots.
Together with `ChildHasUniqueParent`, this gives every non-root occurrence
exactly one incoming edge once reachability is known. -/
def ChildSlotsUnique (source : TypedSource) : Prop :=
  ∀ node, node ∈ source.nodes → (nodeChildIds node).Nodup

/-- One occurrence cannot be shared by two distinct parents. -/
def ChildHasUniqueParent (source : TypedSource) : Prop :=
  ∀ {left right child},
    DirectChild source left child →
    DirectChild source right child →
    left = right

/-- A declaration root has no incoming edge.  Thus roots and proper children
are disjoint occurrence classes. -/
def RootsHaveNoParent (source : TypedSource) : Prop :=
  ∀ {root parent}, root ∈ source.roots →
    ¬ DirectChild source parent root

/-- Full structural closure required by recursive source judgments. -/
structure OccurrenceGraphClosed (source : TypedSource) : Prop where
  wellFormed : OccurrenceGraphWellFormed source
  rootsUnique : RootsUnique source
  childSlotsUnique : ChildSlotsUnique source
  childHasUniqueParent : ChildHasUniqueParent source
  rootsHaveNoParent : RootsHaveNoParent source
  allNodesReachable : AllNodesReachable source
  acyclic : OccurrenceGraphAcyclic source

namespace Descends

theorem trans
    {source : TypedSource} {first middle last : NodeId}
    (left : Descends source first middle)
    (right : Descends source middle last) :
    Descends source first last := by
  induction left with
  | direct edge => exact .step edge right
  | step edge _ induction => exact .step edge (induction right)

end Descends

namespace Reachable

theorem descendant
    {source : TypedSource} {parent child : NodeId}
    (reachable : Reachable source parent)
    (descends : Descends source parent child) :
    Reachable source child := by
  induction descends with
  | direct edge => exact .child reachable edge
  | step edge _ induction => exact induction (.child reachable edge)

end Reachable

namespace OccurrenceGraphClosed

/-- Every reachable non-root occurrence has exactly one parent.  Existence
comes from reachability; uniqueness is the no-sharing invariant above. -/
theorem unique_parent
    {source : TypedSource} (closed : OccurrenceGraphClosed source)
    {child : NodeId} (reachable : Reachable source child)
    (notRoot : child ∉ source.roots) :
    ∃ parent, DirectChild source parent child ∧
      ∀ candidate, DirectChild source candidate child → candidate = parent := by
  induction reachable with
  | root member => exact False.elim (notRoot member)
  | @child parent child _ edge =>
      refine ⟨parent, edge, ?_⟩
      intro candidate candidateEdge
      exact closed.childHasUniqueParent candidateEdge edge

/-- Every retained non-root node has exactly one parent occurrence. -/
theorem retained_unique_parent
    {source : TypedSource} (closed : OccurrenceGraphClosed source)
    {node : Node} (member : node ∈ source.nodes)
    (notRoot : node.id ∉ source.roots) :
    ∃ parent, DirectChild source parent node.id ∧
      ∀ candidate, DirectChild source candidate node.id →
        candidate = parent :=
  closed.unique_parent (closed.allNodesReachable node member) notRoot

end OccurrenceGraphClosed

end Solcore.SourceSemantics

/-!
## Consolidated module: `Solcore.SourceSemantics.GraphSubstitutionProperties`
-/

/-!
Structural rigid substitution changes only retained type and evidence data.
This module records the complementary graph facts: occurrence identities,
child edges, and roots are unchanged.  These are the structural premises
needed when a generic semantic body is instantiated before source evaluation;
the corresponding local and requirement ownership facts live with the static
substitution theorems in `SubstitutionProperties`.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.StructuralSubstitution

open Frontend.SourceInference
open TypeSystem

@[simp] theorem applyBinder_id
    (substitution : ParameterSubstitution) (binder : TypedBinder) :
    (applyBinder substitution binder).id = binder.id := by
  rfl

@[simp] theorem applyPlaceResolution_projections
    (substitution : ParameterSubstitution) (place : PlaceResolution) :
    (applyPlaceResolution substitution place).projections = place.projections := by
  rfl

@[simp] theorem applyAssignmentResolution_requirements
    (substitution : ParameterSubstitution) (assignment : AssignmentResolution) :
    (applyAssignmentResolution substitution assignment).requirements =
      assignment.requirements := by
  rfl

@[simp] theorem applyAssignmentResolution_placeChildIds
    (substitution : ParameterSubstitution) (assignment : AssignmentResolution) :
    assignmentChildIds (applyAssignmentResolution substitution assignment) =
      assignmentChildIds assignment := by
  rfl

@[simp] theorem applyMatchPatternInstruction_binderIds
    (substitution : ParameterSubstitution)
    (instruction : MatchPatternInstruction) :
    patternInstructionBinderIds [applyMatchPatternInstruction substitution
      instruction] = patternInstructionBinderIds [instruction] := by
  cases instruction <;>
    simp [applyMatchPatternInstruction, patternInstructionBinderIds]

@[simp] theorem applyMatchPatternInstructions_binderIds
    (substitution : ParameterSubstitution)
    (instructions : List MatchPatternInstruction) :
    patternInstructionBinderIds
        (instructions.map (applyMatchPatternInstruction substitution)) =
      patternInstructionBinderIds instructions := by
  unfold patternInstructionBinderIds
  rw [List.filterMap_map]
  apply congrArg (fun select => List.filterMap select instructions)
  funext instruction
  cases instruction <;> rfl

@[simp] theorem applyTypedMatchPattern_binderIds
    (substitution : ParameterSubstitution) (pattern : TypedMatchPattern) :
    patternBinderIds (applyTypedMatchPattern substitution pattern) =
      patternBinderIds pattern := by
  cases pattern with
  | mk _ _ resolution =>
      cases resolution <;>
        simp [applyTypedMatchPattern, applyMatchPatternResolution,
          patternBinderIds]

@[simp] theorem applyTypedMatchCase_childIds
    (substitution : ParameterSubstitution) (matchCase : TypedMatchCase) :
    matchCaseChildIds (applyTypedMatchCase substitution matchCase) =
      matchCaseChildIds matchCase := by
  rfl

@[simp] theorem applyTypedMatchCases_childIds
    (substitution : ParameterSubstitution) (cases : List TypedMatchCase) :
    (cases.map (applyTypedMatchCase substitution)).flatMap matchCaseChildIds =
      cases.flatMap matchCaseChildIds := by
  induction cases with
  | nil => rfl
  | cons matchCase cases induction => simp [induction]

@[simp] theorem applyForItemForm_childIds
    (substitution : ParameterSubstitution) (item : ForItemForm) :
    forItemChildIds (applyForItemForm substitution item) =
      forItemChildIds item := by
  cases item <;> simp [applyForItemForm, forItemChildIds]

@[simp] theorem applyForItemForms_childIds
    (substitution : ParameterSubstitution) (items : List ForItemForm) :
    (items.map (applyForItemForm substitution)).flatMap forItemChildIds =
      items.flatMap forItemChildIds := by
  induction items with
  | nil => rfl
  | cons item items induction => simp [induction]

@[simp] theorem applyExpressionForm_childIds
    (substitution : ParameterSubstitution) (form : ExpressionForm) :
    expressionChildIds (applyExpressionForm substitution form) =
      expressionChildIds form := by
  cases form <;> rfl

@[simp] theorem applyStatementForm_childIds
    (substitution : ParameterSubstitution) (form : StatementForm) :
    statementChildIds (applyStatementForm substitution form) =
      statementChildIds form := by
  cases form <;>
    simp [applyStatementForm, statementChildIds, matchChildIds,
      applyMatchResolution]

@[simp] theorem applyNode_id
    (substitution : ParameterSubstitution) (node : Node) :
    (applyNode substitution node).id = node.id := by
  cases node <;> rfl

@[simp] theorem applyNode_occurrenceId
    (substitution : ParameterSubstitution) (node : Node) :
    (applyNode substitution node).occurrenceId = node.occurrenceId := by
  cases node <;> rfl

@[simp] theorem applyNode_childIds
    (substitution : ParameterSubstitution) (node : Node) :
    nodeChildIds (applyNode substitution node) = nodeChildIds node := by
  cases node <;>
    simp [applyNode, applyExpressionNode, applyStatementNode, nodeChildIds]

@[simp] theorem applyTypedSource_owner
    (substitution : ParameterSubstitution) (source : TypedSource) :
    (applyTypedSource substitution source).owner = source.owner := by
  rfl

@[simp] theorem applyTypedSource_roots
    (substitution : ParameterSubstitution) (source : TypedSource) :
    (applyTypedSource substitution source).roots = source.roots := by
  rfl

@[simp] theorem applyTypedSource_nodeIds
    (substitution : ParameterSubstitution) (source : TypedSource) :
    nodeIds (applyTypedSource substitution source) = nodeIds source := by
  simp [nodeIds, applyTypedSource, List.map_map, Function.comp_def]

@[simp] theorem applyTypedSource_nodeOccurrenceIds
    (substitution : ParameterSubstitution) (source : TypedSource) :
    nodeOccurrenceIds (applyTypedSource substitution source) =
      nodeOccurrenceIds source := by
  simp [nodeOccurrenceIds, applyTypedSource, List.map_map, Function.comp_def]

/-- Structural substitution transports one retained node membership forward. -/
theorem containsNode_applyParameters
    {source : TypedSource} {id : NodeId} {node : Node}
    (substitution : ParameterSubstitution)
    (contains : ContainsNode source id node) :
    ContainsNode (applyTypedSource substitution source) id
      (applyNode substitution node) := by
  exact ⟨List.mem_map.mpr ⟨node, contains.1, rfl⟩, by
    simpa using contains.2⟩

/-- Structural substitution reflects retained node membership because it
preserves every node identity and maps the table pointwise. -/
theorem containsNode_of_applyParameters
    {source : TypedSource} {id : NodeId} {node : Node}
    {substitution : ParameterSubstitution}
    (contains : ContainsNode (applyTypedSource substitution source) id node) :
    ∃ original, ContainsNode source id original ∧
      applyNode substitution original = node := by
  rcases List.mem_map.mp contains.1 with ⟨original, originalMem, rfl⟩
  exact ⟨original, ⟨originalMem, by simpa using contains.2⟩, rfl⟩

theorem directChild_applyParameters
    {source : TypedSource} {parent child : NodeId}
    (substitution : ParameterSubstitution)
    (edge : DirectChild source parent child) :
    DirectChild (applyTypedSource substitution source) parent child := by
  rcases edge with ⟨node, contains, childMem⟩
  exact ⟨applyNode substitution node,
    containsNode_applyParameters substitution contains,
    by simpa using childMem⟩

theorem directChild_of_applyParameters
    {source : TypedSource} {parent child : NodeId}
    {substitution : ParameterSubstitution}
    (edge : DirectChild (applyTypedSource substitution source) parent child) :
    DirectChild source parent child := by
  rcases edge with ⟨node, contains, childMem⟩
  rcases containsNode_of_applyParameters contains with
    ⟨original, originalContains, rfl⟩
  exact ⟨original, originalContains, by simpa using childMem⟩

theorem descends_applyParameters
    {source : TypedSource} {parent child : NodeId}
    (substitution : ParameterSubstitution)
    (path : Descends source parent child) :
    Descends (applyTypedSource substitution source) parent child := by
  induction path with
  | direct edge => exact .direct (directChild_applyParameters substitution edge)
  | step edge _ induction =>
      exact .step (directChild_applyParameters substitution edge) induction

theorem descends_of_applyParameters
    {source : TypedSource} {parent child : NodeId}
    {substitution : ParameterSubstitution}
    (path : Descends (applyTypedSource substitution source) parent child) :
    Descends source parent child := by
  induction path with
  | direct edge => exact .direct (directChild_of_applyParameters edge)
  | step edge _ induction =>
      exact .step (directChild_of_applyParameters edge) induction

theorem reachable_applyParameters
    {source : TypedSource} {id : NodeId}
    (substitution : ParameterSubstitution)
    (reachable : Reachable source id) :
    Reachable (applyTypedSource substitution source) id := by
  induction reachable with
  | root member => exact .root (by simpa using member)
  | child _ edge induction =>
      exact .child induction (directChild_applyParameters substitution edge)

/-- Occurrence-graph closure is invariant under rigid type substitution. -/
theorem OccurrenceGraphClosed.applyParameters
    {source : TypedSource} (substitution : ParameterSubstitution)
    (closed : OccurrenceGraphClosed source) :
    OccurrenceGraphClosed (applyTypedSource substitution source) := by
  refine {
    wellFormed := {
      nodeOccurrencesUnique := by
        simpa [NodeOccurrencesUnique] using
          closed.wellFormed.nodeOccurrencesUnique
      nodesOwned := ?_
      rootsOwned := by simpa [RootsOwned] using closed.wellFormed.rootsOwned
      rootsExist := by simpa [RootsExist] using closed.wellFormed.rootsExist
      childEdgesExist := ?_
    }
    rootsUnique := by simpa [RootsUnique] using closed.rootsUnique
    childSlotsUnique := ?_
    childHasUniqueParent := ?_
    rootsHaveNoParent := ?_
    allNodesReachable := ?_
    acyclic := ?_
  }
  · intro node member
    rcases List.mem_map.mp member with ⟨original, originalMem, rfl⟩
    simpa using closed.wellFormed.nodesOwned original originalMem
  · intro node member child childMem
    rcases List.mem_map.mp member with ⟨original, originalMem, rfl⟩
    simpa using closed.wellFormed.childEdgesExist original originalMem child
      (by simpa using childMem)
  · intro node member
    rcases List.mem_map.mp member with ⟨original, originalMem, rfl⟩
    simpa using closed.childSlotsUnique original originalMem
  · intro left right child leftEdge rightEdge
    exact closed.childHasUniqueParent
      (directChild_of_applyParameters leftEdge)
      (directChild_of_applyParameters rightEdge)
  · intro root parent rootMem edge
    exact closed.rootsHaveNoParent (by simpa using rootMem)
      (directChild_of_applyParameters edge)
  · intro node member
    rcases List.mem_map.mp member with ⟨original, originalMem, rfl⟩
    have reachable := reachable_applyParameters substitution
      (closed.allNodesReachable original originalMem)
    simpa using reachable
  · intro id path
    exact closed.acyclic id (descends_of_applyParameters path)

end Solcore.SourceSemantics.StructuralSubstitution
