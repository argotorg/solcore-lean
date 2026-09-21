import Solcore.Frontend.SourceInference.TypedIR

/-! Identity-preservation laws for final substitution over typed source IR. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceInference

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

@[simp] theorem ExpressionNode.applySubstitution_id
    (substitution : TypeSystem.Substitution) (node : ExpressionNode) :
    (node.applySubstitution substitution).id = node.id := by
  rfl

@[simp] theorem ExpressionNode.applySubstitution_requirements
    (substitution : TypeSystem.Substitution) (node : ExpressionNode) :
    (node.applySubstitution substitution).requirements = node.requirements := by
  rfl

@[simp] theorem StatementNode.applySubstitution_id
    (substitution : TypeSystem.Substitution) (node : StatementNode) :
    (node.applySubstitution substitution).id = node.id := by
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

@[simp] theorem TypedSource.applySubstitution_nodeIds
    (substitution : TypeSystem.Substitution) (source : TypedSource) :
    (source.applySubstitution substitution).nodes.map Node.id =
      source.nodes.map Node.id := by
  simp [TypedSource.applySubstitution]

end Solcore.Frontend.SourceInference
