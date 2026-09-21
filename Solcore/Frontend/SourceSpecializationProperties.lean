import Solcore.Frontend.SourceSpecialization

/-! Identity-preservation laws for checked source specialization. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceSpecialization

open SourceInference TypeSystem

@[simp] theorem applyIntegerLiteralResolution_rawValue
    (substitution : ParameterSubstitution)
    (resolution : IntegerLiteralResolution) :
    (applyIntegerLiteralResolution substitution resolution).rawValue =
      resolution.rawValue := by
  rfl

@[simp] theorem applyIntegerLiteralResolution_targetType
    (substitution : ParameterSubstitution)
    (resolution : IntegerLiteralResolution) :
    (applyIntegerLiteralResolution substitution resolution).targetType =
      substitution.apply resolution.targetType := by
  rfl

@[simp] theorem applyIntegerLiteralResolution_requirement
    (substitution : ParameterSubstitution)
    (resolution : IntegerLiteralResolution) :
    (applyIntegerLiteralResolution substitution resolution).requirement =
      resolution.requirement := by
  rfl

theorem applyIntegerLiteralResolution_predicate
    (substitution : ParameterSubstitution)
    (resolution : IntegerLiteralResolution) :
    (applyIntegerLiteralResolution substitution resolution).predicate =
      ProgramPredicate.applyParameters substitution resolution.predicate := by
  rfl

@[simp] theorem applyScheme_quantified
    (substitution : ParameterSubstitution) (scheme : Scheme) :
    (applyScheme substitution scheme).quantified = scheme.quantified := by
  rfl

@[simp] theorem applyScheme_body
    (substitution : ParameterSubstitution) (scheme : Scheme) :
    (applyScheme substitution scheme).body = substitution.apply scheme.body := by
  rfl

@[simp] theorem applyInstantiation_declaration
    (substitution : ParameterSubstitution)
    (instantiation : DeclarationInstantiation) :
    (applyInstantiation substitution instantiation).declaration =
      instantiation.declaration := by
  rfl

@[simp] theorem applyInstantiation_parameterKeys
    (substitution : ParameterSubstitution)
    (instantiation : DeclarationInstantiation) :
    (applyInstantiation substitution instantiation).parameterSubstitution.map
        Prod.fst =
      instantiation.parameterSubstitution.map Prod.fst := by
  simp [applyInstantiation]

@[simp] theorem applyCoercionStep_requirement
    (substitution : ParameterSubstitution) (step : CoercionStep) :
    (applyCoercionStep substitution step).requirement = step.requirement := by
  rfl

@[simp] theorem applyCoercionStep_methodRequirements
    (substitution : ParameterSubstitution) (step : CoercionStep) :
    (applyCoercionStep substitution step).methodRequirements =
      step.methodRequirements := by
  rfl

@[simp] theorem applyCoercionStep_requirements
    (substitution : ParameterSubstitution) (step : CoercionStep) :
    (applyCoercionStep substitution step).requirements = step.requirements := by
  rfl

@[simp] theorem applyNode_id (substitution : ParameterSubstitution)
    (node : Node) :
    (applyNode substitution node).id = node.id := by
  cases node <;> rfl

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
    (applyTypedSource substitution source).nodes.map Node.id =
      source.nodes.map Node.id := by
  simp [applyTypedSource]

@[simp] theorem applySolvedRequirement_id
    (substitution : ParameterSubstitution)
    (requirement : SolvedRequirement) :
    (applySolvedRequirement substitution requirement).id = requirement.id := by
  rfl

theorem applyPredicateEvidence_goal (substitution : ParameterSubstitution)
    (evidence : PredicateEvidence) :
    (applyPredicateEvidence substitution evidence).goal =
      ProgramPredicate.applyParameters substitution evidence.goal := by
  cases evidence with
  | assumption predicate => rfl
  | implementation evidence =>
      cases evidence
      rfl

theorem applySolvedRequirement_goal_alignment
    (substitution : ParameterSubstitution)
    (requirement : SolvedRequirement)
    (aligned : requirement.evidence.goal = requirement.predicate) :
    (applySolvedRequirement substitution requirement).evidence.goal =
      (applySolvedRequirement substitution requirement).predicate := by
  change (applyPredicateEvidence substitution requirement.evidence).goal =
    ProgramPredicate.applyParameters substitution requirement.predicate
  rw [applyPredicateEvidence_goal, aligned]

@[simp] theorem applyCheckedFunction_declaration
    (substitution : ParameterSubstitution) (function : CheckedFunction) :
    (applyCheckedFunction substitution function).declaration =
      function.declaration := by
  rfl

@[simp] theorem applyCheckedFunction_bodyOwner
    (substitution : ParameterSubstitution) (function : CheckedFunction) :
    (applyCheckedFunction substitution function).typedBody.owner =
      function.typedBody.owner := by
  rfl

@[simp] theorem applyCheckedFunction_bodyRoots
    (substitution : ParameterSubstitution) (function : CheckedFunction) :
    (applyCheckedFunction substitution function).typedBody.roots =
      function.typedBody.roots := by
  rfl

@[simp] theorem applyCheckedFunction_requirementIds
    (substitution : ParameterSubstitution) (function : CheckedFunction) :
    (applyCheckedFunction substitution function).solvedRequirements.map
        (·.id) =
      function.solvedRequirements.map (·.id) := by
  simp [applyCheckedFunction]

@[simp] theorem applyCheckedFunction_nodeIds
    (substitution : ParameterSubstitution) (function : CheckedFunction) :
    (applyCheckedFunction substitution function).typedBody.nodes.map Node.id =
      function.typedBody.nodes.map Node.id := by
  simp [applyCheckedFunction]

end Solcore.Frontend.SourceSpecialization
