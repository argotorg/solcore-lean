import Solcore.SourceSemantics.Graph
import Solcore.SourceSemantics.Ownership
import Solcore.SourceSemantics.Substitution

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
