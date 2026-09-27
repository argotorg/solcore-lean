import Solcore.Frontend.SourceInference.TypedIR

/-! Identity-preservation laws for final substitution over typed source IR. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceInference

@[simp] theorem TypedBinder.applySubstitution_id
    (substitution : TypeSystem.Substitution) (binder : TypedBinder) :
    (binder.applySubstitution substitution).id = binder.id := by
  rfl

@[simp] theorem TypedBinder.applySubstitution_name
    (substitution : TypeSystem.Substitution) (binder : TypedBinder) :
    (binder.applySubstitution substitution).name = binder.name := by
  rfl

@[simp] theorem TypedBinder.applySubstitution_comptime
    (substitution : TypeSystem.Substitution) (binder : TypedBinder) :
    (binder.applySubstitution substitution).comptime = binder.comptime := by
  rfl

@[simp] theorem IntegerLiteralResolution.applySubstitution_rawValue
    (substitution : TypeSystem.Substitution)
    (resolution : IntegerLiteralResolution) :
    (resolution.applySubstitution substitution).rawValue =
      resolution.rawValue := by
  rfl

@[simp] theorem IntegerLiteralResolution.applySubstitution_targetType
    (substitution : TypeSystem.Substitution)
    (resolution : IntegerLiteralResolution) :
    (resolution.applySubstitution substitution).targetType =
      substitution.apply resolution.targetType := by
  rfl

@[simp] theorem IntegerLiteralResolution.applySubstitution_requirement
    (substitution : TypeSystem.Substitution)
    (resolution : IntegerLiteralResolution) :
    (resolution.applySubstitution substitution).requirement =
      resolution.requirement := by
  rfl

theorem IntegerLiteralResolution.applySubstitution_predicate
    (substitution : TypeSystem.Substitution)
    (resolution : IntegerLiteralResolution) :
    (resolution.applySubstitution substitution).predicate =
      TypedTraitResolution.applySubstitution substitution
        resolution.predicate := by
  rfl

@[simp] theorem CoercionStep.applySubstitution_requirement
    (substitution : TypeSystem.Substitution) (step : CoercionStep) :
    (step.applySubstitution substitution).requirement = step.requirement := by
  rfl

@[simp] theorem CoercionStep.applySubstitution_methodRequirements
    (substitution : TypeSystem.Substitution) (step : CoercionStep) :
    (step.applySubstitution substitution).methodRequirements =
      step.methodRequirements := by
  rfl

@[simp] theorem CoercionStep.applySubstitution_requirements
    (substitution : TypeSystem.Substitution) (step : CoercionStep) :
    (step.applySubstitution substitution).requirements = step.requirements := by
  rfl

namespace CoercionPath

/-- Closing flexible types preserves exact coercion endpoints and adjacency;
stable requirement identities are unchanged by `CoercionStep.applySubstitution`.
-/
theorem isValid_applySubstitution
    (substitution : TypeSystem.Substitution)
    {source target : TypeSystem.Ty} {steps : List CoercionStep}
    (valid : isValid source target steps = true) :
    isValid (substitution.apply source) (substitution.apply target)
      (steps.map (CoercionStep.applySubstitution substitution)) = true := by
  induction steps generalizing source with
  | nil =>
      exact beq_iff_eq.mpr
        (congrArg substitution.apply (beq_iff_eq.mp valid))
  | cons step rest induction =>
      cases rest with
      | nil =>
          change (step.source == source && step.target == target) = true
            at valid
          change
            (substitution.apply step.source == substitution.apply source &&
              substitution.apply step.target == substitution.apply target) =
                true
          rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at valid ⊢
          exact ⟨congrArg substitution.apply valid.1,
            congrArg substitution.apply valid.2⟩
      | cons next tail =>
          change
            (step.source == source &&
              isValid step.target target (next :: tail)) = true at valid
          change
            (substitution.apply step.source == substitution.apply source &&
              isValid (substitution.apply step.target)
                (substitution.apply target)
                ((next :: tail).map
                  (CoercionStep.applySubstitution substitution))) = true
          rw [Bool.and_eq_true, beq_iff_eq] at valid ⊢
          exact ⟨congrArg substitution.apply valid.1,
            induction valid.2⟩

end CoercionPath

@[simp] theorem ExpressionNode.applySubstitution_id
    (substitution : TypeSystem.Substitution) (node : ExpressionNode) :
    (node.applySubstitution substitution).id = node.id := by
  rfl

@[simp] theorem ExpressionNode.applySubstitution_requirements
    (substitution : TypeSystem.Substitution) (node : ExpressionNode) :
    (node.applySubstitution substitution).requirements = node.requirements := by
  rfl

@[simp] theorem ExpressionNode.applySubstitution_rawType
    (substitution : TypeSystem.Substitution) (node : ExpressionNode) :
    (node.applySubstitution substitution).rawType =
      substitution.apply node.rawType := by
  cases coercions : node.coercions with
  | nil =>
      simp [ExpressionNode.applySubstitution, ExpressionNode.rawType,
        coercions]
  | cons first rest =>
      simp [ExpressionNode.applySubstitution, ExpressionNode.rawType,
        coercions, CoercionStep.applySubstitution]

@[simp] theorem StatementNode.applySubstitution_id
    (substitution : TypeSystem.Substitution) (node : StatementNode) :
    (node.applySubstitution substitution).id = node.id := by
  rfl

@[simp] theorem PlaceResolution.applySubstitution_projections
    (substitution : TypeSystem.Substitution) (place : PlaceResolution) :
    (place.applySubstitution substitution).projections = place.projections := by
  rfl

@[simp] theorem AssignmentResolution.applySubstitution_requirements
    (substitution : TypeSystem.Substitution)
    (assignment : AssignmentResolution) :
    (assignment.applySubstitution substitution).requirements =
      assignment.requirements := by
  rfl

@[simp] theorem Node.id_applySubstitution
    (substitution : TypeSystem.Substitution) (node : Node) :
    (node.applySubstitution substitution).id = node.id := by
  cases node <;> rfl

@[simp] theorem Node.occurrenceId_applySubstitution
    (substitution : TypeSystem.Substitution) (node : Node) :
    (node.applySubstitution substitution).occurrenceId = node.occurrenceId := by
  cases node <;> rfl

@[simp] theorem TypedSource.applySubstitution_owner
    (substitution : TypeSystem.Substitution) (source : TypedSource) :
    (source.applySubstitution substitution).owner = source.owner := by
  rfl

@[simp] theorem TypedSource.applySubstitution_roots
    (substitution : TypeSystem.Substitution) (source : TypedSource) :
    (source.applySubstitution substitution).roots = source.roots := by
  rfl

@[simp] theorem TypedSource.applySubstitution_inputIds
    (substitution : TypeSystem.Substitution) (source : TypedSource) :
    (source.applySubstitution substitution).inputs.map (fun binder => binder.id) =
      source.inputs.map (fun binder => binder.id) := by
  simp [TypedSource.applySubstitution]

@[simp] theorem TypedSource.applySubstitution_inputNames
    (substitution : TypeSystem.Substitution) (source : TypedSource) :
    (source.applySubstitution substitution).inputs.map
        (fun binder => binder.name) =
      source.inputs.map (fun binder => binder.name) := by
  simp [TypedSource.applySubstitution]

@[simp] theorem TypedSource.applySubstitution_inputComptime
    (substitution : TypeSystem.Substitution) (source : TypedSource) :
    (source.applySubstitution substitution).inputs.map
        (fun binder => binder.comptime) =
      source.inputs.map (fun binder => binder.comptime) := by
  simp [TypedSource.applySubstitution]

@[simp] theorem TypedSource.applySubstitution_nodeIds
    (substitution : TypeSystem.Substitution) (source : TypedSource) :
    (source.applySubstitution substitution).nodes.map Node.id =
      source.nodes.map Node.id := by
  simp [TypedSource.applySubstitution]

@[simp] theorem TypedSource.applySubstitution_nodeOccurrenceIds
    (substitution : TypeSystem.Substitution) (source : TypedSource) :
    (source.applySubstitution substitution).nodes.map Node.occurrenceId =
      source.nodes.map Node.occurrenceId := by
  simp [TypedSource.applySubstitution]

end Solcore.Frontend.SourceInference
