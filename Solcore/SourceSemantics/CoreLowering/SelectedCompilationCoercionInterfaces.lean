import Solcore.SourceSemantics.CoreLowering.SelectedCompilationOperatorInterfaces
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedFinalPlanOrigins
import Solcore.SourceSemantics.CoreLowering.CallablePreparedFinalCatalogOrigins

/-! Executable preparation authenticates the named Coerce interface at every
retained coercion site in each selected original source body. The source table
and complete rigid substitution remain explicit throughout the connection. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationCoercionInterfaces
open Frontend SourceInference TypeSystem
open ExecutableCoercionInterfaces
open CallableCoercionPreparation (argumentSteps Covered CoveredWith)
open CallableCoercionPreparationSteps (bind_ok)

private theorem require_ok {α ε : Type} {condition : Prop} [Decidable condition]
    {action : Except ε α} {error : ε} {value : α}
    (accepted : (if condition then action else .error error) = .ok value) :
    condition ∧ action = .ok value := by
  split at accepted
  · exact ⟨‹condition›, accepted⟩
  · cases accepted

theorem checkedCoercionMethod_interface
    {program : CheckedProgram} {caller : SourceSpecialization.SpecializedFunction}
    {node : ExpressionNode} {available : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    {step : CoercionStep} {method : ExecutableImplMethods.CheckedMethod}
    (accepted : SourceCompilationPlan.checkedCoercionMethod program caller node available step = .ok method) :
    ∃ solved,
      caller.function.solvedRequirements.filter (fun row => decide (row.id = step.requirement)) = [solved] ∧
      HasInterface program.signatures solved.predicate.trait := by
  simp only [SourceCompilationPlan.checkedCoercionMethod, bind, Except.bind, pure, Except.pure,
    throw, throwThe, MonadExceptOf.throw] at accepted
  split at accepted <;> try contradiction
  obtain ⟨solved, picked, accepted⟩ := bind_ok accepted
  have selected : caller.function.solvedRequirements.filter
      (fun row => decide (row.id = step.requirement)) = [solved] := by
    change (match caller.function.solvedRequirements.filter (fun row => decide (row.id = step.requirement)) with
      | [] => .error (.missingSolvedRequirement caller.key node.id step.requirement)
      | [row] => .ok row
      | rows => .error (.duplicateSolvedRequirements caller.key node.id step.requirement rows.length) :
      Except SourceTypedRuntime.RuntimeError SolvedRequirement) = .ok solved at picked
    cases filtered : caller.function.solvedRequirements.filter (fun row => decide (row.id = step.requirement)) with
    | nil => simp [filtered] at picked
    | cons row rest =>
      cases rest with
      | nil => simp only [filtered, Except.ok.injEq] at picked; subst solved; rfl
      | cons other rest => simp [filtered] at picked
  obtain ⟨_, accepted⟩ := require_ok accepted
  split at accepted <;> try contradiction
  rename_i traitId goalTrait
  split at accepted <;> try contradiction
  rename_i trait found
  obtain ⟨guard, accepted⟩ := require_ok accepted
  have guards : trait.name = "Coerce" ∧ trait.parameters.length = 2 := by
    simpa only [Bool.and_eq_true, decide_eq_true_eq] using guard
  split at accepted <;> try contradiction
  rename_i traitMethod single
  exact ⟨solved, selected, traitId, trait, traitMethod, goalTrait, found,
    guards.1, guards.2, single⟩

theorem coercions_of_covered {program : CheckedProgram}
    {caller : SourceSpecialization.SpecializedFunction} {plan : SourceSpecializationWorklist.Plan}
    (covered : Covered program caller plan) :
    CoercionInterfaces program.signatures caller.function.solvedRequirements caller.function.typedBody := by
  obtain ⟨available, resolved, covered⟩ := covered
  intro node member step site
  obtain ⟨visit⟩ := covered node member step site
  exact checkedCoercionMethod_interface visit.selected

theorem of_covered {program : CheckedProgram}
    {caller : SourceSpecialization.SpecializedFunction} {plan : SourceSpecializationWorklist.Plan}
    (covered : CoveredWith program caller plan) : BodyInterfaces program.signatures caller.function :=
  ⟨coercions_of_covered covered.coercions, SelectedCompilationOperatorInterfaces.of_covered covered⟩

theorem argumentSteps_apply (substitution : ParameterSubstitution) (node : ExpressionNode) :
    argumentSteps (SourceSpecialization.applyExpressionNode substitution node) =
      (argumentSteps node).map (SourceSpecialization.applyCoercionStep substitution) := by
  cases form : node.form <;>
    simp only [SourceSpecialization.applyExpressionNode, SourceSpecialization.applyExpressionForm,
      form, argumentSteps, List.map_nil]
  case call callee arguments resolution =>
    cases resolution <;> rfl

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

/-- Interface presence transfers to the complete original body without
inverting any rigid type substitution. Every original requirement identity
and both ordered coercion lists are retained by specialization. -/
theorem of_applied {signatures : ProgramSignatures} {function : CheckedFunction}
    {substitution : ParameterSubstitution}
    (supported : BodyInterfaces signatures (SourceSpecialization.applyCheckedFunction substitution function)) :
    BodyInterfaces signatures function := by
  constructor
  · intro node member step site
    have nodeMember : .expression (SourceSpecialization.applyExpressionNode substitution node) ∈
        (SourceSpecialization.applyCheckedFunction substitution function).typedBody.nodes :=
      List.mem_map.mpr ⟨.expression node, member, rfl⟩
    have stepMember : SourceSpecialization.applyCoercionStep substitution step ∈
        (SourceSpecialization.applyExpressionNode substitution node).coercions ++
          argumentSteps (SourceSpecialization.applyExpressionNode substitution node) := by
      rw [argumentSteps_apply]
      change SourceSpecialization.applyCoercionStep substitution step ∈
        node.coercions.map (SourceSpecialization.applyCoercionStep substitution) ++ _
      rw [← List.map_append]
      exact List.mem_map.mpr ⟨step, site, rfl⟩
    obtain ⟨actual, selected, supported⟩ := supported.coercions _ nodeMember _ stepMember
    change (function.solvedRequirements.map (SourceSpecialization.applySolvedRequirement substitution)).filter
      (fun row => decide (row.id = step.requirement)) = [actual] at selected
    rw [filter_applied] at selected
    obtain ⟨original, singleton, applied⟩ := map_singleton selected
    refine ⟨original, singleton, ?_⟩
    rw [← applied] at supported
    exact supported
  · exact SelectedCompilationOperatorInterfaces.of_applied supported.operators

theorem of_specialization {program : CheckedProgram}
    {caller : SourceSpecialization.SpecializedFunction} {plan : SourceSpecializationWorklist.Plan}
    {signature : ProgramFunctionSignature} {original : CheckedFunction} {supplied : ParameterSubstitution}
    (accepted : SourceSpecialization.specializeFunction signature original supplied = .ok caller)
    (covered : CoveredWith program caller plan) : BodyInterfaces program.signatures original := by
  apply of_applied (substitution := caller.parameterSubstitution)
  rw [← (CallableCoercionBodyProvenance.specialization_fields accepted).1]
  exact of_covered covered

/-- Original bodies are ordinary declarations or retained implementation
methods. Methods keep their own checker carrier and are never recategorized
as ordinary functions by a matching owner or specialization key. -/
def OriginalMember (program : CheckedProgram) (function : CheckedFunction) : Prop :=
  function ∈ program.functions ∨ ∃ method ∈ program.methods, function = method.checked

theorem original_of_catalogOrigin {program : CheckedProgram}
    {caller : SourceSpecialization.SpecializedFunction} {plan : SourceSpecializationWorklist.Plan}
    (checked : CallableMethodBodyCoherence.Checked program)
    (origin : CallablePreparedFinalCatalogOrigins.CatalogOrigin program caller)
    (covered : CoveredWith program caller plan) :
    ∃ original, OriginalMember program original ∧
      caller.function = SourceSpecialization.applyCheckedFunction caller.parameterSubstitution original ∧
      BodyInterfaces program.signatures original := by
  cases origin with
  | ordinary origin =>
    obtain ⟨request, signature, original, _, member, _, specialized⟩ := origin
    exact ⟨original, Or.inl member,
      (CallableCoercionBodyProvenance.specialization_fields specialized).1,
      of_specialization specialized covered⟩
  | method selected =>
    obtain ⟨retained, member, _, identical⟩ := selected.retained checked
    exact ⟨selected.generic, Or.inr ⟨retained, member, identical⟩,
      (CallableCoercionBodyProvenance.specialization_fields selected.specialized).1,
      of_specialization selected.specialized covered⟩

/-- Every actual cached function belongs to the completed executable plan,
including ordinary helpers and methods discovered during its traversal. -/
theorem cached (compiled : SourceCoreUnifiedCompilation.Compiled)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : compiled.indexed.base.functions[index]? = some named) :
    BodyInterfaces compiled.sourceProgram.signatures named.specialized.function := by
  have prepared := SourceCoreUnifiedPreparationCertificates.compiled_planPrepared compiled
  have member := RecursiveNamedPreparedFinalPlanOrigins.final_member compiled selected rfl
  exact of_covered ((CallableCoercionPreparation.of_accepted_with prepared).2 named.specialized member)

/-- The actual cache position and preparation receipt supply the complete
original checker carrier and all executable coercion interfaces. Nested
lambda bodies are included because preparation visits the full node table. -/
theorem cached_original (compiled : SourceCoreUnifiedCompilation.Compiled)
    (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : compiled.indexed.base.functions[index]? = some named) :
    ∃ original, OriginalMember compiled.sourceProgram original ∧
      named.specialized.function =
        SourceSpecialization.applyCheckedFunction named.specialized.parameterSubstitution original ∧
      BodyInterfaces compiled.sourceProgram.signatures original := by
  have prepared := SourceCoreUnifiedPreparationCertificates.compiled_planPrepared compiled
  have member := RecursiveNamedPreparedFinalPlanOrigins.final_member compiled selected rfl
  exact original_of_catalogOrigin checked
    (CallablePreparedFinalCatalogOrigins.of_default_preparation prepared named.specialized member)
    ((CallableCoercionPreparation.of_accepted_with prepared).2 named.specialized member)

theorem checked_cached_original {raw : Workspace.RawWorkspace} {checkingFuel : Nat}
    (compiled : SourceCoreUnifiedCompilation.Compiled)
    (checked : Frontend.checkProgram raw checkingFuel = .ok compiled.sourceProgram)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : compiled.indexed.base.functions[index]? = some named) :
    ∃ original, OriginalMember compiled.sourceProgram original ∧
      named.specialized.function =
        SourceSpecialization.applyCheckedFunction named.specialized.parameterSubstitution original ∧
      BodyInterfaces compiled.sourceProgram.signatures original :=
  cached_original compiled (CallableMethodBodyCoherence.of_checked checked) selected

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationCoercionInterfaces
