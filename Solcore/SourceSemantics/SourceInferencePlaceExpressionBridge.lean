import Solcore.SourceSemantics.SourceInferenceExpressionDispatchSoundness
import Solcore.SourceSemantics.SourceInferenceStatementAssignmentSoundness

/-!
Actual mapping keys and assignment RHS expressions as recursive-child
provenance.  These adapters feed the bounded expression induction with the
precise calls made by place and assignment inference.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.SourceInferenceSoundness

open Frontend Frontend.SourceInference TypeSystem

/-- The actual key traversal of an indexed place is a smaller-fuel expression
child, with its final node table and evidence ledgers connected to the parent
ambient source. -/
theorem inferPlaceFuel_success_index_key_childProvenance
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {targetExpression base key : Syntax.Expr}
    {brackets : Syntax.SourceSpan}
    {initial final evidenceState : Frontend.SourceInference.State}
    {place : PlaceResolution} {ambient : TypedSource}
    (targetEq : targetExpression.value = .index base brackets key)
    (success : Detail.inferPlaceFuel (fuel + 1) inferenceContext
      targetExpression initial = .ok (place, final))
    (below : initial.NodesBelowNextOccurrence)
    (roots : List NodeId := [])
    (sourceExtension : TypingSourceExtends (final.toTypedSource roots) ambient)
    (literalsSubset : final.integerLiterals ⊆ evidenceState.integerLiterals)
    (requirementsSubset : final.requirements ⊆ evidenceState.requirements) :
    ∃ child : ExpressionChildInferenceProvenance (fuel + 1)
        inferenceContext ambient evidenceState roots,
      child.expression = key ∧ child.final = final ∧
        .expression child.inferred.id ∈ place.references := by
  obtain ⟨expected, keyInitial, inferredKey, keySuccess, keyBelow,
      keyMember, _, _, _, _⟩ :=
    inferPlaceFuel_success_index_key_provenance targetEq success below roots
  refine ⟨{
    fuel := fuel
    expression := key
    expected := some expected
    initial := keyInitial
    final := final
    inferred := inferredKey
    fuel_lt := Nat.lt_succ_self fuel
    initialNodesBelow := keyBelow
    success := keySuccess
    sourceExtension := sourceExtension
    integerLiteralsSubset := literalsSubset
    requirementsSubset := requirementsSubset
  }, rfl, rfl, keyMember⟩

/-- The actual RHS traversal of a value assignment is likewise a smaller-
fuel expression child, independent of whether the operator first requires a
`Word` unification. -/
theorem inferAssignedValueFuel_success_value_childProvenance
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {targetExpression value : Syntax.Expr}
    {operator : Syntax.ValueAssignOp}
    {initial final evidenceState : Frontend.SourceInference.State}
    {assignment : AssignmentResolution}
    {inferredValue : InferredExpression} {ambient : TypedSource}
    (success : Detail.inferAssignedValueFuel fuel inferenceContext
      targetExpression operator value initial =
        .ok (assignment, inferredValue, final))
    (below : initial.NodesBelowNextOccurrence)
    (roots : List NodeId := [])
    (sourceExtension : TypingSourceExtends (final.toTypedSource roots) ambient)
    (literalsSubset : final.integerLiterals ⊆ evidenceState.integerLiterals)
    (requirementsSubset : final.requirements ⊆ evidenceState.requirements) :
    ∃ child : ExpressionChildInferenceProvenance (fuel + 1)
        inferenceContext ambient evidenceState roots,
      child.expression = value ∧ child.final = final ∧
        child.inferred = inferredValue := by
  obtain ⟨expected, valueInitial, valueSuccess, valueBelow, _, _, _, _⟩ :=
    inferAssignedValueFuel_success_value_provenance success below roots
  refine ⟨{
    fuel := fuel
    expression := value
    expected := some expected
    initial := valueInitial
    final := final
    inferred := inferredValue
    fuel_lt := Nat.lt_succ_self fuel
    initialNodesBelow := valueBelow
    success := valueSuccess
    sourceExtension := sourceExtension
    integerLiteralsSubset := literalsSubset
    requirementsSubset := requirementsSubset
  }, rfl, rfl, rfl⟩

end Solcore.SourceSemantics.SourceInferenceSoundness
