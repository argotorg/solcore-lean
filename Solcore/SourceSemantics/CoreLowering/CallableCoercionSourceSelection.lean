import Solcore.SourceSemantics.CoreLowering.CallableCoercionMethodInstantiation
import Solcore.SourceSemantics.CoreLowering.CallableCoercionEvidenceOrigins
import Solcore.SourceSemantics.CoreLowering.CallableCoercionPreparation

/-! Successful coercion preparation selects an independent source method and
the actual ordered dictionary. Caller-covered headers use the same resolver32;
uncovered origins, cross-fuel coherence and dictionary uniqueness are not
asserted. Runtime body execution and installed closure history remain separate. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000
namespace Solcore.SourceSemantics.CoreLowering.CallableCoercionSourceSelection
open Frontend SourceInference TypeSystem Solcore.SourceSemantics.Dynamic
open CallableNamedMetadata (evidence environment)
open CallableEvidenceEnvironment
open CallableCoercionMethodInstantiation (Selection Formation bodyInstance)

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {value : β}
    (accepted : action >>= next = .ok value) : ∃ item, action = .ok item ∧ next item = .ok value := by
  cases action with
  | error error => cases accepted
  | ok item => exact ⟨item, rfl, accepted⟩

private theorem mapError_ok {α ε δ : Type} {action : Except ε α} {f : ε → δ} {value : α}
    (accepted : action.mapError f = .ok value) : action = .ok value := by
  cases action <;> cases accepted <;> rfl

private theorem require_ok {α ε : Type} {condition : Prop} [Decidable condition]
    {action : Except ε α} {error : ε} {value : α}
    (accepted : (if condition then action else .error error) = .ok value) :
    condition ∧ action = .ok value := by
  split at accepted
  · exact ⟨‹condition›, accepted⟩
  · cases accepted

/-- The exact runtime selector's returned tree is also the singleton result of
the real materializer. Both actions keep the same first-match raw row. -/
theorem requirement_materialized {program : CheckedProgram} {caller : SourceSpecialization.SpecializedFunction}
    {node : ExpressionNode} {available : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    {id : RequirementId} {goal : ProgramPredicate} {raw : TypedTraitResolution.Evidence}
    (accepted : SourceCompilationPlan.exactRuntimeRequirementEvidence program caller node available id goal = .ok raw) :
    SourceCompilationPlan.materializeCallEvidence caller node.id available [id] [goal] = .ok [raw] := by
  simp only [SourceCompilationPlan.exactRuntimeRequirementEvidence, bind, Except.bind, pure, Except.pure,
    throw, throwThe, MonadExceptOf.throw] at accepted
  obtain ⟨row, selected, accepted⟩ := bind_ok accepted
  rcases row with ⟨rowId, predicate, retained⟩
  split at accepted <;> try contradiction
  rename_i predicateEq
  have matchedPredicate : predicate = goal := by simpa using predicateEq
  split at accepted <;> try contradiction
  rename_i retainedEq
  have matchedRetained : retained.goal = goal := by simpa using retainedEq
  cases retained with
  | implementation stored =>
    obtain ⟨_, _, accepted⟩ := bind_ok accepted
    cases accepted
    simp [SourceCompilationPlan.materializeCallEvidence, selected, matchedPredicate, matchedRetained, bind, Except.bind, pure, Except.pure]
  | assumption assumed =>
    dsimp only at accepted
    split at accepted <;> try contradiction
    rename_i stored found
    obtain ⟨_, _, accepted⟩ := bind_ok accepted
    cases accepted
    simp [SourceCompilationPlan.materializeCallEvidence, selected, matchedPredicate, matchedRetained, bind, Except.bind, pure, Except.pure]
    change (match available.find? (fun item => decide (SourceCompilationPlan.runtimeEvidenceGoal item = assumed)) with
      | some item => Except.ok [item]
      | none => Except.error (SourceTypedRuntime.RuntimeError.missingRuntimeAssumptionEvidence caller.key node.id id assumed)) = .ok [raw]
    change available.find? (fun item => decide (SourceCompilationPlan.runtimeEvidenceGoal item = assumed)) = some raw at found
    rw [found]

/-- Reached-row validity comes from the authenticated returned tree; unrelated
ledger entries are not required to be valid here. -/
theorem requirement_produces {program : CheckedProgram} {caller : SourceSpecialization.SpecializedFunction}
    {node : ExpressionNode} {available : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    {id : RequirementId} {goal : ProgramPredicate} {raw : TypedTraitResolution.Evidence} {context : Context}
    (signatures : context.signatures = program.signatures)
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (assumptions : ∀ goal, goal ∈ caller.assumptions → goal ∈ context.assumptions)
    (resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions = .ok available)
    (accepted : SourceCompilationPlan.exactRuntimeRequirementEvidence program caller node available id goal = .ok raw)
    (valid : EvidenceValid [] program.signatures.resolutionRules goal (evidence raw)) :
    RequirementProducesEvidence context (environment available) id goal (evidence raw) := by
  have keys : ∀ goal, goal ∈ (environment available).map Prod.fst → goal ∈ context.assumptions := by
    intro goal member
    exact assumptions goal ((resolved_valid resolved).2 ▸ member)
  have produced := CallableAuthenticatedCallEvidence.produces_of_authenticated ledger keys
    (by simpa only [signatures] using (resolved_valid resolved).1)
    (requirement_materialized accepted) (Forall₂.cons (by simpa only [signatures] using valid) Forall₂.nil)
  cases produced with
  | cons head tail => exact head

theorem requirements_produce {program : CheckedProgram} {caller : SourceSpecialization.SpecializedFunction}
    {node : ExpressionNode} {available returned : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    {ids : List RequirementId} {goals : List ProgramPredicate} {context : Context}
    (signatures : context.signatures = program.signatures)
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (assumptions : ∀ goal, goal ∈ caller.assumptions → goal ∈ context.assumptions)
    (resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions = .ok available)
    (accepted : SourceCompilationPlan.exactRuntimeRequirementEvidenceList program caller node available ids goals = .ok returned)
    (valid : Forall₂ (fun goal raw => EvidenceValid [] program.signatures.resolutionRules goal (evidence raw)) goals returned) :
    RequirementsProduceEnvironment context (environment available) ids goals (environment returned) := by
  induction ids generalizing goals returned with
  | nil => cases goals <;> cases accepted; exact .nil
  | cons id rest ih =>
    cases goals with
    | nil => cases accepted
    | cons goal goals =>
      unfold SourceCompilationPlan.exactRuntimeRequirementEvidenceList at accepted
      obtain ⟨raw, headAccepted, accepted⟩ := bind_ok accepted
      obtain ⟨tail, tailAccepted, accepted⟩ := bind_ok accepted
      cases accepted
      cases valid with
      | cons head tailValid =>
        have goalEq := SourceCompilationPlan.exactRuntimeRequirementEvidence_success_goal _ _ _ _ _ _ _ headAccepted
        simpa only [environment, List.map_cons, goalEq] using
          (RequirementsProduceEnvironment.cons (requirement_produces signatures ledger assumptions resolved headAccepted head)
            (ih tailAccepted tailValid))

private theorem trait_lookup {program : CheckedProgram} {primary : TypedTraitResolution.Evidence}
    {name : String} {method : ExecutableImplMethods.CheckedMethod}
    (selected : Selection program primary name method) :
    program.signatures.trait? method.traitMethod.id.trait = some selected.trait := by
  rw [← selected.association]
  exact selected.traitLookup

/-- The outer coercion guard fixes the selected trait's name, not just its
arity or numeric identity. The inner and outer singleton selectors agree. -/
theorem trait_name {program : CheckedProgram} {caller : SourceSpecialization.SpecializedFunction}
    {node : ExpressionNode} {available : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    {step : CoercionStep} {method : ExecutableImplMethods.CheckedMethod}
    (accepted : SourceCompilationPlan.checkedCoercionMethod program caller node available step = .ok method)
    {primary : TypedTraitResolution.Evidence} (selected : Selection program primary "coerce" method) :
    selected.trait.name = "Coerce" := by
  simp only [SourceCompilationPlan.checkedCoercionMethod, bind, Except.bind, pure, Except.pure,
    throw, throwThe, MonadExceptOf.throw] at accepted
  split at accepted <;> try contradiction
  obtain ⟨row, _, accepted⟩ := bind_ok accepted
  obtain ⟨_, accepted⟩ := require_ok accepted
  split at accepted <;> try contradiction
  rename_i traitId goalTrait
  split at accepted <;> try contradiction
  rename_i trait found
  obtain ⟨traitGuard, accepted⟩ := require_ok accepted
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  obtain ⟨raw, rawAccepted, accepted⟩ := bind_ok accepted
  obtain ⟨methods, _, accepted⟩ := bind_ok accepted
  obtain ⟨actual⟩ := CallableCoercionMethodInstantiation.selection (mapError_ok accepted)
  have goalEq : actual.goal = row.predicate := by
    have matched := SourceCompilationPlan.exactRuntimeRequirementEvidence_success_goal _ _ _ _ _ _ _ rawAccepted
    rw [actual.primaryShape] at matched
    exact matched
  have traitIdEq : actual.trait.id = traitId := by
    have eq := actual.goalTrait
    rw [goalEq, goalTrait] at eq
    exact (ProgramTraitId.declaration.inj eq).symm
  have actualLookup := actual.traitLookup
  have owner : actual.declaration.traitMethod.trait = actual.trait.id := by
    unfold ProgramSignatures.trait? at actualLookup
    have eq := List.find?_some (p := fun trait : ProgramTraitSignature =>
      decide (trait.id = actual.declaration.traitMethod.trait)) actualLookup
    exact (of_decide_eq_true eq).symm
  rw [owner, traitIdEq] at actualLookup
  have same := Option.some.inj (actualLookup.symm.trans found)
  have selectedSame := Option.some.inj ((trait_lookup selected).symm.trans (trait_lookup actual))
  rw [selectedSame, same]
  have guards : trait.name = "Coerce" ∧ trait.parameters.length = 2 := by
    simpa only [Bool.and_eq_true, decide_eq_true_eq] using traitGuard
  exact guards.1


/-- Static source selection keeps the full implementation, declaration, trait,
head match and checked body. It contains no source execution or closure law. -/
structure Certificate (program : CheckedProgram) (caller : SourceSpecialization.SpecializedFunction)
    (node : ExpressionNode) (available : SourceTypedRuntime.RuntimeEvidenceEnvironment)
    (step : CoercionStep) (method : ExecutableImplMethods.CheckedMethod) where
  roots : CallableCoercionMethodCertificates.Certificate program caller node available step method
  selected : Selection program roots.primary "coerce" method
  traitName : selected.trait.name = "Coerce"

theorem of_accepted {program : CheckedProgram} {caller : SourceSpecialization.SpecializedFunction}
    {node : ExpressionNode} {available : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    {step : CoercionStep} {method : ExecutableImplMethods.CheckedMethod}
    (accepted : SourceCompilationPlan.checkedCoercionMethod program caller node available step = .ok method) :
    Nonempty (Certificate program caller node available step method) := by
  obtain ⟨roots⟩ := CallableCoercionMethodCertificates.of_accepted accepted
  obtain ⟨selected⟩ := CallableCoercionMethodInstantiation.selection roots.checked
  exact ⟨⟨roots, selected, trait_name accepted selected⟩⟩

/-- Actual selector, same-fuel retained body and returned dictionary determine
an independent source selection. Range formation and caller coverage remain
explicit; neither is inferred from a ground specialization key. -/
theorem Certificate.selects {loaded : LoadedProgram} {program : CheckedProgram}
    (loadedAccepted : Frontend.checkLoadedProgram loaded 1024 = .ok program)
    {caller : SourceSpecialization.SpecializedFunction} {node : ExpressionNode}
    {available dictionary : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    {step : CoercionStep} {method : ExecutableImplMethods.CheckedMethod} {context : Context}
    (receipt : Certificate program caller node available step method)
    (formed : Formation receipt.selected.implementation receipt.selected.declaration)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures program.signatures) method.specialized.parameterSubstitution)
    (signatures : context.signatures = program.signatures)
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (assumptions : ∀ goal, goal ∈ caller.assumptions → goal ∈ context.assumptions)
    (resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions = .ok available)
    (covered : CallableCoercionEvidenceOrigins.CallerCovered caller method)
    (materialized : SourceCompilationPlan.coercionMethodRuntimeEvidence program caller node step method = .ok dictionary) :
    OperatorMethodSelected (Program.ofChecked program) context (environment available) "Coerce" "coerce"
      (step.requirement :: step.methodRequirements) (bodyInstance program method) (environment dictionary) := by
  obtain ⟨definition, definitionMember, definitionId, instantiated⟩ :=
    receipt.selected.instantiates loadedAccepted formed.parameters range
  have determined := receipt.selected.determines formed
  have headTrait : receipt.selected.goal.trait = receipt.selected.implementation.head.trait := by
    exact (congrArg (fun goal : ProgramPredicate => goal.trait) determined.2.2).symm
  have produced := requirement_produces signatures ledger assumptions resolved
    receipt.roots.primarySelected receipt.roots.primaryValid
  have sourceSelected : EvidenceSelectsMethod (Program.ofChecked program)
      (evidence receipt.roots.primary) "coerce" definition := by
    simpa only [receipt.selected.primaryShape, evidence] using
      (EvidenceSelectsMethod.source (premises := method.implementationPremises.map evidence)
        receipt.selected.implementationMember headTrait receipt.selected.methodMember
        receipt.selected.declarationName definitionMember definitionId)
  have primaryGoal : SourceCompilationPlan.runtimeEvidenceGoal receipt.roots.primary = receipt.selected.goal := by
    exact congrArg SourceCompilationPlan.runtimeEvidenceGoal receipt.selected.primaryShape
  rw [primaryGoal] at produced
  have methodsProduced := requirements_produce signatures ledger assumptions resolved
    receipt.roots.methodsSelected receipt.roots.methodsValid
  have methodsGoals : receipt.roots.methodEvidence.map SourceCompilationPlan.runtimeEvidenceGoal =
      receipt.selected.declaration.wherePredicates.map
        (ProgramPredicate.applyParameters method.specialized.parameterSubstitution) := by
    rw [← receipt.roots.methods, receipt.selected.methodsGoals, receipt.selected.method_predicates formed]
  rw [methodsGoals] at methodsProduced
  have assembled := (CallableCoercionEvidenceOrigins.Certificate.origins receipt.roots covered resolved materialized).1
  have methodAssumptions : method.specialized.assumptions =
      (SourceSemantics.methodAssumptions receipt.selected.trait receipt.selected.implementation receipt.selected.declaration).map
        (ProgramPredicate.applyParameters method.specialized.parameterSubstitution) :=
    (CallableCoercionBodyProvenance.specialization_fields receipt.selected.specialized).2
  rw [methodAssumptions] at assembled
  have traitOwner : receipt.selected.declaration.traitMethod.trait = receipt.selected.trait.id := by
    have found := receipt.selected.traitLookup
    unfold ProgramSignatures.trait? at found
    exact (of_decide_eq_true (List.find?_some
      (p := fun trait : ProgramTraitSignature => decide (trait.id = receipt.selected.declaration.traitMethod.trait)) found)).symm
  refine .intro (.intro produced sourceSelected) ?_ receipt.selected.implementationMember
    receipt.selected.traitMember receipt.traitName receipt.selected.goalTrait determined
    receipt.selected.methodMember receipt.selected.declarationName traitOwner methodsProduced instantiated ?_ ?_
  · exact ⟨method.implementationPremises.map evidence, by
      simpa only [evidence] using congrArg evidence receipt.selected.primaryShape⟩
  · simpa only [environment, List.map_map, Function.comp_def] using assembled
  · exact CallableCoercionEvidenceOrigins.Certificate.covers receipt.roots covered resolved materialized rfl rfl

/-- Public preparation fixes the emitted complete carrier, and the actual
spine step fixes the same source selection and dictionary. This is a static
connection; it does not assert invocation of an installed method closure. -/
theorem prepared_step {loaded : LoadedProgram} {program : CheckedProgram}
    (loadedAccepted : Frontend.checkLoadedProgram loaded 1024 = .ok program)
    {before : SourceSpecializationWorklist.Plan} {fuel budget : Nat}
    {project : CallableCoercionSpine.Projector} {compilation : CallableCoercionSpine.Context}
    (prepared : SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget program before fuel budget = .ok compilation.plan)
    {caller : SourceSpecialization.SpecializedFunction} (member : caller ∈ compilation.plan.specializations)
    {node : ExpressionNode} (nodeMember : .expression node ∈ caller.function.typedBody.nodes)
    {coercion : CoercionStep} (site : coercion ∈ node.coercions ++ CallableCoercionPreparation.argumentSteps node)
    {available : CallableCoercionSpine.RuntimeEvidence}
    (resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions = .ok available)
    {scope : CallableCoercionSpine.Scope} {policy : SourceCoreFunctions.CallablePolicy}
    {input output : CallableCoercionSpine.Lowered} {call : CallableCoercionSpine.Call}
    (step : CallableCoercionSpine.Step program project compilation caller available scope node policy input coercion output call)
    {context : Context}
    (signatures : context.signatures = program.signatures)
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (assumptions : ∀ goal, goal ∈ caller.assumptions → goal ∈ context.assumptions)
    (formed : ∀ receipt : Certificate program caller node available coercion step.method,
      Formation receipt.selected.implementation receipt.selected.declaration)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures program.signatures) step.method.specialized.parameterSubstitution)
    (covered : CallableCoercionEvidenceOrigins.CallerCovered caller step.method) :
    step.specialized = step.method.specialized ∧
      OperatorMethodSelected (Program.ofChecked program) context (environment available) "Coerce" "coerce"
        (coercion.requirement :: coercion.methodRequirements) (bodyInstance program step.method) (environment step.dictionary) := by
  obtain ⟨receipt⟩ := of_accepted step.selectedMethod
  exact ⟨CallableCoercionPreparation.step_specialized prepared member nodeMember site resolved step,
    receipt.selects loadedAccepted (formed receipt) range signatures ledger assumptions resolved covered step.materialized⟩

end Solcore.SourceSemantics.CoreLowering.CallableCoercionSourceSelection
