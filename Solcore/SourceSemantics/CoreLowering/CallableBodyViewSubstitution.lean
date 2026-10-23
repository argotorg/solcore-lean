import Solcore.SourceSemantics.CoreLowering.CallableBodyMetadataViews
import Solcore.Frontend.SourceInference.TypedIRProperties

/-! Substitution preserves actual occurrence paths. A reached-body relation
therefore transports without comparing unrelated source-table entries. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableBodyMetadataViews
open Frontend SourceInference TypeSystem CallableLambdaBodyReachability

private theorem lookupNode_apply (source : TypedSource) (substitution : Substitution)
    (id : OccurrenceId) :
    (source.applySubstitution substitution).lookupNode? id =
      (source.lookupNode? id).map (Node.applySubstitution substitution) := by
  simp only [TypedSource.lookupNode?, TypedSource.applySubstitution, List.find?_map]
  congr 2
  funext candidate
  simp only [Function.comp_apply, Node.occurrenceId_applySubstitution]

theorem lookupExpression_apply (source : TypedSource) (substitution : Substitution)
    (id : ExpressionId) :
    (source.applySubstitution substitution).lookupExpression? id =
      (source.lookupExpression? id).map (ExpressionNode.applySubstitution substitution) := by
  unfold TypedSource.lookupExpression?
  rw [lookupNode_apply]
  cases source.lookupNode? id.occurrence with
  | none => rfl
  | some node => cases node <;> rfl

theorem lookupStatement_apply (source : TypedSource) (substitution : Substitution)
    (id : StatementId) :
    (source.applySubstitution substitution).lookupStatement? id =
      (source.lookupStatement? id).map (StatementNode.applySubstitution substitution) := by
  unfold TypedSource.lookupStatement?
  rw [lookupNode_apply]
  cases source.lookupNode? id.occurrence with
  | none => rfl
  | some node => cases node <;> rfl

theorem reaches_substitution {source : TypedSource} {roots : List NodeId}
    (substitution : Substitution) {id : NodeId} :
    Reaches (source.applySubstitution substitution) roots id ↔ Reaches source roots id := by
  constructor
  · intro reached
    induction reached with
    | root member => exact .root member
    | expression parent found edge ih =>
      rw [lookupExpression_apply] at found
      obtain ⟨node, actual, rfl⟩ := Option.map_eq_some_iff.mp found
      exact .expression ih actual (by simpa only [ExpressionNode.applySubstitution,
        ExpressionForm.applySubstitution_references] using edge)
    | statement parent found edge ih =>
      rw [lookupStatement_apply] at found
      obtain ⟨node, actual, rfl⟩ := Option.map_eq_some_iff.mp found
      exact .statement ih actual (by simpa only [StatementNode.applySubstitution,
        StatementForm.applySubstitution_references] using edge)
  · intro reached
    induction reached with
    | root member => exact .root member
    | expression parent found edge ih =>
      exact .expression ih (by rw [lookupExpression_apply, found]; rfl)
        (by simpa only [ExpressionNode.applySubstitution, ExpressionForm.applySubstitution_references] using edge)
    | statement parent found edge ih =>
      exact .statement ih (by rw [lookupStatement_apply, found]; rfl)
        (by simpa only [StatementNode.applySubstitution, StatementForm.applySubstitution_references] using edge)

/-- The relation follows real paths on either side and preserves only the
metadata that the body readers consume. -/
theorem BodyView.applySubstitution {source view : TypedSource} {roots : List NodeId}
    (related : BodyView source view roots) (substitution : Substitution) :
    BodyView (source.applySubstitution substitution) (view.applySubstitution substitution) roots where
  owner := related.owner
  inputs := by simpa only [TypedSource.applySubstitution_inputIds] using related.inputs
  expression reached _ found := by
    have originalReached : Reaches source roots _ ∨ Reaches view roots _ :=
      reached.imp (reaches_substitution substitution).mp (reaches_substitution substitution).mp
    rw [lookupExpression_apply] at found
    obtain ⟨node, actual, rfl⟩ := Option.map_eq_some_iff.mp found
    obtain ⟨old, selected, sameId, sameForm⟩ := related.expression originalReached actual
    refine ⟨old.applySubstitution substitution, ?_, sameId, ?_⟩
    · rw [lookupExpression_apply, selected]; rfl
    · exact congrArg (ExpressionForm.applySubstitution substitution) sameForm
  expression_back reached _ found := by
    have originalReached : Reaches source roots _ ∨ Reaches view roots _ :=
      reached.imp (reaches_substitution substitution).mp (reaches_substitution substitution).mp
    rw [lookupExpression_apply] at found
    obtain ⟨node, actual, rfl⟩ := Option.map_eq_some_iff.mp found
    obtain ⟨old, selected, sameId, sameForm⟩ := related.expression_back originalReached actual
    refine ⟨old.applySubstitution substitution, ?_, sameId, ?_⟩
    · rw [lookupExpression_apply, selected]; rfl
    · exact congrArg (ExpressionForm.applySubstitution substitution) sameForm
  statement reached := by
    rw [lookupStatement_apply, lookupStatement_apply]
    exact congrArg (Option.map (StatementNode.applySubstitution substitution))
      (related.statement (reached.imp (reaches_substitution substitution).mp (reaches_substitution substitution).mp))

end Solcore.SourceSemantics.CoreLowering.CallableBodyMetadataViews
