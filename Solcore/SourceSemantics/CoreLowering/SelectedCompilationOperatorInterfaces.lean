import Solcore.SourceSemantics.SourceExecutableCoercionInterfaces
import Solcore.SourceSemantics.CoreLowering.CallableCoercionPreparation

/-! Actual operator preparation verifies convention names at selected source
sites. The original node and primary requirement identity survive complete
rigid specialization, including expressions inside lambda bodies. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationOperatorInterfaces
open Frontend SourceInference TypeSystem
open ExecutableCoercionInterfaces
open CallableCoercionPreparationSteps (bind_ok OperatorForm operatorOwnedNode)

private theorem require_ok {α ε : Type} {condition : Prop} [Decidable condition]
    {action : Except ε α} {error : ε} {value : α}
    (accepted : (if condition then action else .error error) = .ok value) :
    condition ∧ action = .ok value := by
  split at accepted
  · exact ⟨‹condition›, accepted⟩
  · cases accepted

theorem ordinary_of_layout {node : ExpressionNode} {requirements : List RequirementId}
    (layout : node.requirements = requirements ++ node.coercions.flatMap CoercionStep.requirements) :
    SourceCompilationPlan.ordinaryOwnedRequirements? node = some requirements := by
  unfold SourceCompilationPlan.ordinaryOwnedRequirements?
  change (if node.requirements.length < (node.coercions.flatMap CoercionStep.requirements).length
    then none else
    let owned := node.requirements.take
      (node.requirements.length - (node.coercions.flatMap CoercionStep.requirements).length)
    if node.requirements = owned ++ node.coercions.flatMap CoercionStep.requirements
    then some owned else none) = some requirements
  rw [layout]
  simp

theorem unary_interface
    {program : CheckedProgram} {caller : SourceSpecialization.SpecializedFunction}
    {node : ExpressionNode} {available : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    {operator : Syntax.UnaryOp} {selection : SourceCompilationPlan.CheckedRuntimeOperatorMethod}
    {primary : RequirementId} {companions : List RequirementId} {name methodName : String}
    (owned : SourceCompilationPlan.ordinaryOwnedRequirements? node = some (primary :: companions))
    (dispatch : Detail.unaryOperatorDispatch operator = .traitMethod name methodName)
    (accepted : SourceCompilationPlan.checkedUnaryOperatorMethod program caller node available operator = .ok selection) :
    ∃ solved trait,
      caller.function.solvedRequirements.filter (fun row => decide (row.id = primary)) = [solved] ∧
      solved.predicate.trait = .declaration trait ∧
      (program.signatures.trait? trait).map (·.name) = some name := by
  simp only [SourceCompilationPlan.checkedUnaryOperatorMethod, bind, Except.bind, pure, Except.pure,
    throw, throwThe, MonadExceptOf.throw] at accepted
  split at accepted <;> try contradiction
  rename_i profile profileFound
  rcases profile with ⟨traitName, actualMethod⟩
  have profileDispatch : Detail.unaryOperatorDispatch operator = .traitMethod traitName actualMethod := by
    cases operator <;> cases profileFound <;> rfl
  have sameName : traitName = name := by
    have same := profileDispatch.symm.trans dispatch
    cases same
    rfl
  rw [owned] at accepted
  dsimp only at accepted
  split at accepted <;> try contradiction
  obtain ⟨solved, picked, accepted⟩ := bind_ok accepted
  have selected : caller.function.solvedRequirements.filter
      (fun row => decide (row.id = primary)) = [solved] := by
    change (match caller.function.solvedRequirements.filter (fun row => decide (row.id = primary)) with
      | [] => .error (.missingSolvedRequirement caller.key node.id primary)
      | [row] => .ok row
      | rows => .error (.duplicateSolvedRequirements caller.key node.id primary rows.length) :
      Except SourceTypedRuntime.RuntimeError SolvedRequirement) = .ok solved at picked
    cases filtered : caller.function.solvedRequirements.filter (fun row => decide (row.id = primary)) with
    | nil => simp [filtered] at picked
    | cons row rest =>
      cases rest with
      | nil => simp only [filtered, Except.ok.injEq] at picked; subst solved; rfl
      | cons other rest => simp [filtered] at picked
  obtain ⟨_, _, accepted⟩ := bind_ok accepted
  split at accepted <;> try contradiction
  rename_i traitId goalTrait
  split at accepted <;> try contradiction
  rename_i trait found
  obtain ⟨guard, _⟩ := require_ok accepted
  exact ⟨solved, traitId, selected, goalTrait, by
    simp only [found, Option.map_some]
    exact congrArg some (guard.trans sameName)⟩

theorem binary_interface
    {program : CheckedProgram} {caller : SourceSpecialization.SpecializedFunction}
    {node : ExpressionNode} {available : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    {operator : Syntax.BinaryOp} {selection : SourceCompilationPlan.CheckedRuntimeOperatorMethod}
    {primary : RequirementId} {companions : List RequirementId} {name methodName : String}
    (owned : SourceCompilationPlan.ordinaryOwnedRequirements? node = some (primary :: companions))
    (dispatch : Detail.binaryOperatorDispatch operator = .traitMethod name methodName)
    (accepted : SourceCompilationPlan.checkedBinaryOperatorMethod program caller node available operator = .ok selection) :
    ∃ solved trait,
      caller.function.solvedRequirements.filter (fun row => decide (row.id = primary)) = [solved] ∧
      solved.predicate.trait = .declaration trait ∧
      (program.signatures.trait? trait).map (·.name) = some name := by
  simp only [SourceCompilationPlan.checkedBinaryOperatorMethod, bind, Except.bind, pure, Except.pure,
    throw, throwThe, MonadExceptOf.throw] at accepted
  split at accepted <;> try contradiction
  rename_i profile profileFound
  rcases profile with ⟨traitName, actualMethod⟩
  have profileDispatch : Detail.binaryOperatorDispatch operator = .traitMethod traitName actualMethod := by
    cases operator <;> cases profileFound <;> rfl
  have sameName : traitName = name := by
    have same := profileDispatch.symm.trans dispatch
    cases same
    rfl
  rw [owned] at accepted
  dsimp only at accepted
  split at accepted <;> try contradiction
  obtain ⟨solved, picked, accepted⟩ := bind_ok accepted
  have selected : caller.function.solvedRequirements.filter
      (fun row => decide (row.id = primary)) = [solved] := by
    change (match caller.function.solvedRequirements.filter (fun row => decide (row.id = primary)) with
      | [] => .error (.missingSolvedRequirement caller.key node.id primary)
      | [row] => .ok row
      | rows => .error (.duplicateSolvedRequirements caller.key node.id primary rows.length) :
      Except SourceTypedRuntime.RuntimeError SolvedRequirement) = .ok solved at picked
    cases filtered : caller.function.solvedRequirements.filter (fun row => decide (row.id = primary)) with
    | nil => simp [filtered] at picked
    | cons row rest =>
      cases rest with
      | nil => simp only [filtered, Except.ok.injEq] at picked; subst solved; rfl
      | cons other rest => simp [filtered] at picked
  obtain ⟨_, _, accepted⟩ := bind_ok accepted
  split at accepted <;> try contradiction
  rename_i traitId goalTrait
  split at accepted <;> try contradiction
  rename_i trait found
  obtain ⟨guard, _⟩ := require_ok accepted
  exact ⟨solved, traitId, selected, goalTrait, by
    simp only [found, Option.map_some]
    exact congrArg some (guard.trans sameName)⟩

theorem of_covered {program : CheckedProgram}
    {caller : SourceSpecialization.SpecializedFunction} {plan : SourceSpecializationWorklist.Plan}
    (covered : CallableCoercionPreparation.CoveredWith program caller plan) :
    OperatorInterfaces program.signatures caller.function.solvedRequirements caller.function.typedBody := by
  obtain ⟨available, _, covered⟩ := covered
  intro node member primary companions name layout dispatch
  have ordinary := ordinary_of_layout layout
  have form : OperatorForm node := by
    cases nodeForm : node.form <;> simp only [operatorDispatch, nodeForm] at dispatch
    all_goals first | contradiction | simp only [OperatorForm, nodeForm]
  obtain ⟨visit⟩ := (covered node member).2 (primary :: companions) ordinary (by simp) form
  have sameRequirements : visit.requirements = primary :: companions :=
    Option.some.inj (visit.owned.symm.trans ordinary)
  have owned : SourceCompilationPlan.ordinaryOwnedRequirements?
      (operatorOwnedNode node visit.requirements) = some (primary :: companions) := by
    apply ordinary_of_layout
    simp only [operatorOwnedNode, List.flatMap_nil, List.append_nil, sameRequirements]
  have accepted := visit.selected
  cases nodeForm : node.form <;>
    simp only [operatorDispatch, nodeForm] at dispatch
  all_goals try contradiction
  case unary operator operand =>
    obtain ⟨method, dispatch⟩ := dispatch
    change (match node.form with
      | .unary operator _ => SourceCompilationPlan.checkedUnaryOperatorMethod program caller
          (operatorOwnedNode node visit.requirements) available operator
      | .binary _ operator _ => SourceCompilationPlan.checkedBinaryOperatorMethod program caller
          (operatorOwnedNode node visit.requirements) available operator
      | _ => .error (.unsupportedRequirements visit.requirements)) = .ok visit.selection at accepted
    rw [nodeForm] at accepted
    exact unary_interface (program := program) (caller := caller)
      (node := operatorOwnedNode node visit.requirements) (available := available)
      (operator := operator) (selection := visit.selection) owned dispatch accepted
  case binary left operator right =>
    obtain ⟨method, dispatch⟩ := dispatch
    change (match node.form with
      | .unary operator _ => SourceCompilationPlan.checkedUnaryOperatorMethod program caller
          (operatorOwnedNode node visit.requirements) available operator
      | .binary _ operator _ => SourceCompilationPlan.checkedBinaryOperatorMethod program caller
          (operatorOwnedNode node visit.requirements) available operator
      | _ => .error (.unsupportedRequirements visit.requirements)) = .ok visit.selection at accepted
    rw [nodeForm] at accepted
    exact binary_interface (program := program) (caller := caller)
      (node := operatorOwnedNode node visit.requirements) (available := available)
      (operator := operator) (selection := visit.selection) owned dispatch accepted

private theorem filter_applied (substitution : ParameterSubstitution)
    (requirements : List SolvedRequirement) (id : RequirementId) :
    (requirements.map (SourceSpecialization.applySolvedRequirement substitution)).filter
        (fun row => decide (row.id = id)) =
      (requirements.filter (fun row => decide (row.id = id))).map
        (SourceSpecialization.applySolvedRequirement substitution) := by
  induction requirements with
  | nil => rfl
  | cons first rest ih =>
    by_cases same : first.id = id <;>
      simp [same, SourceSpecialization.applySolvedRequirement, ih]

private theorem map_singleton {α β : Type} {f : α → β} {items : List α} {value : β}
    (same : items.map f = [value]) : ∃ item, items = [item] ∧ f item = value := by
  cases items with
  | nil => cases same
  | cons item rest =>
    cases rest with
    | nil => exact ⟨item, rfl, (List.cons.inj same).1⟩
    | cons next tail => cases same

private theorem dispatch_applied (substitution : ParameterSubstitution)
    (node : ExpressionNode) (name : String) :
    operatorDispatch (SourceSpecialization.applyExpressionNode substitution node) name =
      operatorDispatch node name := by
  cases form : node.form <;>
    simp [operatorDispatch, SourceSpecialization.applyExpressionNode,
      SourceSpecialization.applyExpressionForm, form]

private theorem coercion_ids_applied (substitution : ParameterSubstitution)
    (steps : List CoercionStep) :
    (steps.map (SourceSpecialization.applyCoercionStep substitution)).flatMap CoercionStep.requirements =
      steps.flatMap CoercionStep.requirements := by
  induction steps with
  | nil => rfl
  | cons step rest ih => simp [ih]

/-- Rigid specialization leaves operator syntax and every requirement identity
unchanged. No inverse type substitution is needed to recover the original site. -/
theorem of_applied {signatures : ProgramSignatures} {function : CheckedFunction}
    {substitution : ParameterSubstitution}
    (supported : OperatorInterfaces signatures
      (SourceSpecialization.applyCheckedFunction substitution function).solvedRequirements
      (SourceSpecialization.applyCheckedFunction substitution function).typedBody) :
    OperatorInterfaces signatures function.solvedRequirements function.typedBody := by
  intro node member primary companions name layout dispatch
  have nodeMember : .expression (SourceSpecialization.applyExpressionNode substitution node) ∈
      (SourceSpecialization.applyCheckedFunction substitution function).typedBody.nodes :=
    List.mem_map.mpr ⟨.expression node, member, rfl⟩
  have appliedLayout : (SourceSpecialization.applyExpressionNode substitution node).requirements =
      (primary :: companions) ++
        (SourceSpecialization.applyExpressionNode substitution node).coercions.flatMap CoercionStep.requirements := by
    simpa only [SourceSpecialization.applyExpressionNode, coercion_ids_applied] using layout
  obtain ⟨actual, trait, selected, traitEq, nameEq⟩ := supported _ nodeMember
    primary companions name appliedLayout (by simpa only [dispatch_applied] using dispatch)
  change (function.solvedRequirements.map (SourceSpecialization.applySolvedRequirement substitution)).filter
    (fun row => decide (row.id = primary)) = [actual] at selected
  rw [filter_applied] at selected
  obtain ⟨original, singleton, applied⟩ := map_singleton selected
  refine ⟨original, trait, singleton, ?_, nameEq⟩
  rw [← applied] at traitEq
  exact traitEq

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationOperatorInterfaces
