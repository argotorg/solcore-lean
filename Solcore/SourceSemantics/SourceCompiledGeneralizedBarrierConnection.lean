import Solcore.SourceSemantics.SourceSelectedTemplateInventory
import Solcore.SourceSemantics.SourceCompiledDirectCallPredicateOrigins

/-! Selected compilation constrains the same original finalized templates
which occur in the declarative generalization barrier. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedBarrierConnection
open Frontend SourceInference TypeSystem SourceSpecializationWorklist
open SourceCompiledLocalFinalization
open CoreLowering.CallableCoercionPreparationSteps (Specialized)

private theorem parameters_keep (parameters : ParameterSubstitution) (type : Ty) :
    type.freeVariables ⊆ (parameters.apply type).freeVariables := by
  intro metavariable occurs
  induction type with
  | «variable» value => exact occurs
  | parameter value | constructor value | error => cases occurs
  | proxy inner ih | comptime inner ih => exact ih occurs
  | application left right leftIH rightIH =>
      simp only [ParameterSubstitution.apply, Ty.mem_freeVariables_application_iff] at occurs ⊢
      exact occurs.elim (fun member => .inl (leftIH member)) (fun member => .inr (rightIH member))
  | function left right leftIH rightIH =>
      simp only [ParameterSubstitution.apply, Ty.mem_freeVariables_function_iff] at occurs ⊢
      exact occurs.elim (fun member => .inl (leftIH member)) (fun member => .inr (rightIH member))
  | product left right leftIH rightIH =>
      simp only [ParameterSubstitution.apply, Ty.mem_freeVariables_product_iff] at occurs ⊢
      exact occurs.elim (fun member => .inl (leftIH member)) (fun member => .inr (rightIH member))
  | mapping left right leftIH rightIH =>
      simp only [ParameterSubstitution.apply, Ty.mem_freeVariables_mapping_iff] at occurs ⊢
      exact occurs.elim (fun member => .inl (leftIH member)) (fun member => .inr (rightIH member))

private theorem predicate_parameters_keep (parameters : ParameterSubstitution) (predicate : ProgramPredicate) :
    TypedTraitResolution.predicateVariables predicate ⊆
      TypedTraitResolution.predicateVariables (ProgramPredicate.applyParameters parameters predicate) := by
  intro metavariable occurs
  apply TypedTraitResolution.mem_predicateVariables_iff.mpr
  rcases TypedTraitResolution.mem_predicateVariables_iff.mp occurs with subject | ⟨argument, present, occurs⟩
  · exact .inl (parameters_keep parameters _ subject)
  · exact .inr ⟨parameters.apply argument, List.mem_map.mpr ⟨argument, present, rfl⟩,
      parameters_keep parameters argument occurs⟩

private theorem closed_predicate_absent {instantiation : DeclarationInstantiation}
    (closed : SourcePreparedOpenCallEdges.InstantiationClosed instantiation = true)
    {predicate : ProgramPredicate} (present : predicate ∈ instantiation.predicates)
    {metavariable : TypeVarId}
    (occurs : metavariable ∈ TypedTraitResolution.predicateVariables predicate) : False := by
  simp only [SourcePreparedOpenCallEdges.InstantiationClosed, Bool.and_eq_true] at closed
  have checked := List.all_eq_true.mp closed.2 predicate present
  simp only [Bool.and_eq_true] at checked
  rcases TypedTraitResolution.mem_predicateVariables_iff.mp occurs with subject | ⟨argument, member, inside⟩
  · rw [List.isEmpty_iff.mp checked.1] at subject
    cases subject
  · rw [List.isEmpty_iff.mp (List.all_eq_true.mp checked.2 argument member)] at inside
    cases inside

/-- A successful selected compilation confines each original finalized
template predicate to its complete owner's quantified variables. The closed
call case uses the same issued ledger predicate; the open case uses the same
discovered instance and checked qualified-read metadata. -/
theorem original_template_scoped {raw : Workspace.RawWorkspace}
    {seeds : List SourceCoreCompiler.Seed} {options : SourceCoreCompiler.Options}
    {compiled : SourceCoreCompiler.Compiled}
    (accepted : SourceCoreCompiler.compile raw seeds options = .ok compiled)
    {row : Specialized} (member : row ∈ compiled.plan.specializations) {fuel : Nat}
    (selected : Selected compiled row fuel)
    {owner : LocalSchemeTemplateOwner}
    (contains : ContainsLocalSchemeTemplate selected.body.finalized.typedSource owner) :
    ∀ metavariable ∈ TypedTraitResolution.predicateVariables owner.requirement.predicate,
      metavariable ∈ owner.binder.scheme.quantified := by
  have template := sourceLocalSchemeTemplateIds_mem_iff.mpr ⟨owner, contains, rfl⟩
  obtain ⟨solved, solvedMember, same, emitter⟩ :=
    SourceCompiledDirectCallPredicateOrigins.BodyReceipt.finalized_template_emitter selected.body template
  have scopedRow := selected.body.resources.ledger.template_scoped solvedMember (same ▸ template)
  obtain ⟨actualOwner, occurrence, actualContains, actualId, predicateEq, _⟩ := scopedRow.exact_owner
  have ownerEq := selected.body.resources.ledger.templateOwnership.owner_unique
    contains actualContains (same.symm.trans actualId)
  subst actualOwner
  have specializedEmitter :=
    SourceCompiledDirectCallPredicateOrigins.specialized_call emitter row.parameterSubstitution
  rw [← selected.source] at specializedEmitter
  obtain ⟨node, present, callee, arguments, instantiation, form, issued, cataloged, paired⟩ := specializedEmitter
  let specialized := StructuralSubstitution.applyLocalSchemeTemplateOwner row.parameterSubstitution owner
  have specializedContains : ContainsLocalSchemeTemplate row.function.typedBody specialized := by
    rw [selected.source]
    exact StructuralSubstitution.ContainsLocalSchemeTemplate.applyParameters row.parameterSubstitution contains
  intro metavariable occurs
  have specializedOccurs := predicate_parameters_keep row.parameterSubstitution owner.requirement.predicate occurs
  cases closed : SourcePreparedOpenCallEdges.InstantiationClosed instantiation with
  | true =>
      apply False.elim
      apply closed_predicate_absent closed paired
      simpa only [predicateEq] using specializedOccurs
  | false =>
      obtain ⟨receipt⟩ := SourceCompiledTemplateCallOwner.open_call_owner accepted member present form cataloged closed
      exact SourceSelectedTemplateInventory.contextual_predicate_scoped
        accepted member form receipt specializedContains issued specializedOccurs

/-- The actual final ledger preserves the same owner and predicate. This
exposes precisely the quantified variables relevant to the generalization
barrier, without replacing the original ledger by the specialized one. -/
theorem original_solved_template_scoped {raw : Workspace.RawWorkspace}
    {seeds : List SourceCoreCompiler.Seed} {options : SourceCoreCompiler.Options}
    {compiled : SourceCoreCompiler.Compiled}
    (accepted : SourceCoreCompiler.compile raw seeds options = .ok compiled)
    {row : Specialized} (member : row ∈ compiled.plan.specializations) {fuel : Nat}
    (selected : Selected compiled row fuel)
    {solved : SolvedRequirement} (present : solved ∈ selected.body.finalized.solvedRequirements)
    (template : solved.id ∈ sourceLocalSchemeTemplateIds selected.body.finalized.typedSource) :
    ∃ owner, ContainsLocalSchemeTemplate selected.body.finalized.typedSource owner ∧
      solved.id = owner.requirement.templateRequirement ∧
      solved.predicate = owner.requirement.predicate ∧
      (∀ metavariable ∈ TypedTraitResolution.predicateVariables solved.predicate,
        metavariable ∈ owner.binder.scheme.quantified) := by
  obtain ⟨owner, occurrence, contains, same, predicateEq, _⟩ :=
    (selected.body.resources.ledger.template_scoped present template).exact_owner
  refine ⟨owner, contains, same, predicateEq, ?_⟩
  rw [predicateEq]
  exact original_template_scoped accepted member selected contains

end Solcore.SourceSemantics.SourceCompiledGeneralizedBarrierConnection
