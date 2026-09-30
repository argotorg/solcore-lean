import Solcore.SourceSemantics.SourceInferenceSoundness

/-!
Operational provenance for assignable-place and assignment inference.  The
lemmas in this file expose the exact recursive states used by a successful
assignment; they do not assume soundness of unrelated expressions.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.SourceInferenceSoundness

open Frontend Frontend.SourceInference TypeSystem

/-- Place inference only appends to a node table whose existing occurrences
were allocated before its input cutoff. -/
theorem inferPlaceFuel_success_typingSourceExtends_under_bound
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {target : Syntax.Expr} {initial final : Frontend.SourceInference.State}
    {place : PlaceResolution}
    (success : Detail.inferPlaceFuel fuel inferenceContext target initial =
      .ok (place, final))
    (below : initial.NodesBelowNextOccurrence)
    (roots : List NodeId := []) :
    TypingSourceExtends (initial.toTypedSource roots)
      (final.toTypedSource roots) := by
  constructor
  · exact Detail.inferPlaceFuel_preserves_owner success
  · exact Detail.inferPlaceFuel_preserves_nodesPrefix success
      List.prefix_rfl below (Nat.le_refl _)

/-- The compound assignment traversal likewise retains its anchored input
table; a selected call inside a new RHS cannot rewrite an older place node. -/
theorem inferAssignedValueFuel_success_typingSourceExtends_under_bound
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {target value : Syntax.Expr} {operator : Syntax.ValueAssignOp}
    {initial final : Frontend.SourceInference.State}
    {assignment : AssignmentResolution}
    {inferred : InferredExpression}
    (success : Detail.inferAssignedValueFuel fuel inferenceContext target
      operator value initial = .ok (assignment, inferred, final))
    (below : initial.NodesBelowNextOccurrence)
    (roots : List NodeId := []) :
    TypingSourceExtends (initial.toTypedSource roots)
      (final.toTypedSource roots) := by
  constructor
  · exact Detail.inferAssignedValueFuel_preserves_owner success
  · exact Detail.inferAssignedValueFuel_preserves_nodesPrefix success
      List.prefix_rfl below (Nat.le_refl _)

/-- A successful value-assignment statement records only one fresh statement
node after its actual delegated assignment traversal. -/
theorem inferStatementFuel_success_assignValue_child_provenance
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {targetExpression value : Syntax.Expr}
    {operator : Syntax.Located Syntax.ValueAssignOp}
    {expectedReturn : Ty}
    {initial allocated : Frontend.SourceInference.State}
    {id : StatementId} {result : Detail.StatementResult}
    {outer : Substitution}
    (statementEq : statement.value =
      .assignValue targetExpression operator value)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (initialBelow : initial.NodesBelowNextOccurrence)
    (roots : List NodeId := []) :
    ∃ assignment inferred assignmentState,
      Detail.inferAssignedValueFuel fuel inferenceContext targetExpression
        operator.value value allocated =
          .ok (assignment, inferred, assignmentState) ∧
      allocated.NodesBelowNextOccurrence ∧
      TypingSourceExtends
        ((assignmentState.toTypedSource roots).applySubstitution outer)
        ((result.state.toTypedSource roots).applySubstitution outer) ∧
      assignmentState.integerPatterns ⊆ result.state.integerPatterns ∧
      assignmentState.requirements ⊆ result.state.requirements := by
  obtain ⟨assignment, inferred, assignmentState, assignmentSuccess,
      resultEq, _⟩ :=
    inferStatementFuel_success_assignValue_facts statementEq allocationEq
      success roots
  have allocatedBelow : allocated.NodesBelowNextOccurrence :=
    by
      have nextBelow :=
        (Frontend.SourceInference.State.OccurrenceBoundExtends.allocateStatementId
          initial).nodesBelowNextOccurrence initialBelow
      simpa only [allocationEq] using nextBelow
  subst result
  refine ⟨assignment, inferred, assignmentState, assignmentSuccess,
    allocatedBelow, ?_, ?_, ?_⟩
  · apply TypingSourceExtends.applySubstitution outer
    constructor
    · rfl
    · exact Frontend.SourceInference.State.recordNode_nodesPrefix
        assignmentState _
  · intro pattern member
    exact member
  · intro requirement member
    exact member

/-- Bit-not assignment uses exactly one place traversal, one unification to
`Word`, and one fresh statement node.  All indexed key expressions therefore
remain in the parent source and both evidence ledgers are preserved. -/
theorem inferStatementFuel_success_assignBitNot_child_provenance
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {targetExpression : Syntax.Expr}
    {operatorSpan : Syntax.SourceSpan} {expectedReturn : Ty}
    {initial allocated : Frontend.SourceInference.State}
    {id : StatementId} {result : Detail.StatementResult}
    {outer : Substitution}
    (statementEq : statement.value =
      .assignBitNot targetExpression operatorSpan)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (initialBelow : initial.NodesBelowNextOccurrence)
    (roots : List NodeId := []) :
    ∃ place placeState unified,
      Detail.inferPlaceFuel fuel inferenceContext targetExpression allocated =
        .ok (place, placeState) ∧
      Detail.unify placeState place.type .word = .ok unified ∧
      allocated.NodesBelowNextOccurrence ∧
      TypingSourceExtends
        ((placeState.toTypedSource roots).applySubstitution outer)
        ((result.state.toTypedSource roots).applySubstitution outer) ∧
      placeState.integerPatterns ⊆ result.state.integerPatterns ∧
      placeState.requirements ⊆ result.state.requirements := by
  obtain ⟨place, placeState, unified, placeSuccess, unifiedSuccess, _,
      resultEq, _⟩ :=
    inferStatementFuel_success_assignBitNot_facts statementEq allocationEq
      success roots
  have allocatedBelow : allocated.NodesBelowNextOccurrence := by
    have nextBelow :=
      (Frontend.SourceInference.State.OccurrenceBoundExtends.allocateStatementId
        initial).nodesBelowNextOccurrence initialBelow
    simpa only [allocationEq] using nextBelow
  have placeToUnified : TypingSourceExtends
      (placeState.toTypedSource roots) (unified.toTypedSource roots) := by
    constructor
    · have headerEq := Detail.unify_state_header unifiedSuccess
      have ownerEq := congrArg Frontend.SourceInference.State.Header.owner
        headerEq
      simpa [Frontend.SourceInference.State.toTypedSource,
        Frontend.SourceInference.State.header] using ownerEq
    · have nodesEq := (Detail.unify_occurrenceState_eq unifiedSuccess).1
      change placeState.nodes <+: unified.nodes
      rw [nodesEq]
      exact List.prefix_rfl
  have unifiedToRecorded : TypingSourceExtends
      (unified.toTypedSource roots)
      ((unified.recordNode (.statement {
          id
          span := statement.span
          type := .unit
          form := .assignBitNot {
            target := { place with type := unified.resolve place.type }
          }
        })).toTypedSource roots) := by
    constructor
    · rfl
    · exact Frontend.SourceInference.State.recordNode_nodesPrefix unified _
  subst result
  refine ⟨place, placeState, unified, placeSuccess, unifiedSuccess,
    allocatedBelow, ?_, ?_, ?_⟩
  · exact (placeToUnified.trans unifiedToRecorded).applySubstitution outer
  · intro pattern member
    change pattern ∈ unified.integerPatterns
    rw [Detail.unify_integerPatterns unifiedSuccess]
    exact member
  · intro requirement member
    change requirement ∈ unified.requirements
    rw [Detail.unify_requirements_eq unifiedSuccess]
    exact member

end Solcore.SourceSemantics.SourceInferenceSoundness
