import Solcore.SourceSemantics.SourceCachedTemplateReceipts

/-! The completed cache supplies template inventory, original qualified-read
metadata and the complete same-owner relation for ordinary prepared rows. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCachedTemplateScope
open Frontend SourceInference TypeSystem SourceSpecializationWorklist
open SourceCompiledLocalFinalization
open CoreLowering.CallableCoercionPreparationSteps (Specialized)

private theorem collector_initialized {source : TypedSource} {binding : LocalLambdaBinding}
    (member : binding ∈ localLambdaBindings source) :
    ({binder := binding.binder, initializer := .expression binding.initializer} : InitializedLetBinding) ∈ initializedLetBindings source := by
  obtain ⟨statement, present, form⟩ := localLambdaBindings_statement_origin member
  apply List.mem_flatMap.mpr
  refine ⟨.statement statement, present, ?_⟩
  change _ ∈ statementInitializedLetBindings statement.form
  rw [form]
  exact List.mem_singleton_self _

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


theorem specialized_inventory {compiled : SourceCoreCompiler.Compiled}
    {row : Specialized} {fuel : Nat} (selected : Selected compiled row fuel)
    {signature : ProgramFunctionSignature} {generic : CheckedFunction} {supplied : ParameterSubstitution}
    (specialized : SourceSpecialization.specializeFunction signature generic supplied = .ok row)
    {id : RequirementId} (template : id ∈ sourceLocalSchemeTemplateIds row.function.typedBody) :
    id ∈ (localLambdaBindings row.function.typedBody).flatMap fun binding =>
      binding.binder.schemeRequirements.map (·.templateRequirement) := by
  obtain ⟨owner, contains, same⟩ := sourceLocalSchemeTemplateIds_mem_iff.mp template
  have requirement := LocalSchemeTemplateOwner.requirement_mem contains
  have nonempty : owner.binder.schemeRequirements ≠ [] := by
    intro empty
    rw [empty] at requirement
    cases requirement
  obtain ⟨binding, present, binder⟩ := SourceSelectedTemplateInventory.specialized_binding
    specialized (SourceSelectedTemplateInventory.selected_ownership selected).1
    (LocalSchemeTemplateOwner.binding_mem contains) nonempty
  apply List.mem_flatMap.mpr
  refine ⟨binding, present, ?_⟩
  rw [binder]
  exact List.mem_map.mpr ⟨owner.requirement, requirement, same⟩

theorem cached_instance_template_scoped (cached : SourceCoreUnifiedCompilation.Compiled)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (position : cached.indexed.base.functions[index]? = some named)
    {contextFuel : Option Nat} {instances : List LocalLambdaInstance}
    (discovered : localLambdaInstances named.specialized.function.typedBody contextFuel = .ok instances)
    {localInstance : LocalLambdaInstance} (member : localInstance ∈ instances)
    {template : LocalSchemeRequirement} (owned : template ∈ localInstance.binding.binder.schemeRequirements)
    {metavariable : TypeVarId}
    (occurs : metavariable ∈ TypedTraitResolution.predicateVariables template.predicate) :
    metavariable ∈ localInstance.binding.binder.scheme.quantified := by
  have qualified : localInstance.binding.binder.schemeRequirements ≠ [] := by
    intro empty
    rw [empty] at owned
    cases owned
  have owner := SourcePreparedQualifiedLocalReadOwner.discovered_owner discovered member
  have origin := localLambdaInstances_read_origin discovered localInstance member
  cases origin with
  | root node present name form matched =>
      obtain ⟨_owned, _substitution, _bindings, _spine, receipt⟩ :=
        SourcePreparedQualifiedLocalReadBindings.metadata_bindings
          (SourceCachedTemplateReceipts.cached_metadata cached position) present form owner qualified
      exact receipt.template_scoped owned occurs
  | contextual parentOrigin node present name form child matched cumulative =>
      obtain ⟨_owned, _substitution, _bindings, _spine, receipt⟩ :=
        SourcePreparedQualifiedLocalReadBindings.metadata_bindings
          (SourceCachedTemplateReceipts.cached_metadata cached position) present form owner qualified
      exact receipt.template_scoped owned occurs

theorem contextual_owner {compiled : SourceCoreCompiler.Compiled}
    {row : Specialized} {fuel : Nat} (selected : Selected compiled row fuel)
    {signature : ProgramFunctionSignature} {generic : CheckedFunction} {supplied : ParameterSubstitution}
    (specialized : SourceSpecialization.specializeFunction signature generic supplied = .ok row)
    {node : ExpressionNode} {callee : ExpressionId} {arguments : List ExpressionId}
    {instantiation : DeclarationInstantiation}
    (form : node.form = .call callee arguments (.declaration instantiation))
    (receipt : SourceCompiledTemplateCallOwner.PreparedContextual compiled row node instantiation)
    {owner : LocalSchemeTemplateOwner} (contains : ContainsLocalSchemeTemplate row.function.typedBody owner)
    (issued : owner.requirement.templateRequirement ∈ node.requirements) :
    owner.binder = receipt.contextual.localInstance.binding.binder ∧
      owner.requirement ∈ receipt.contextual.localInstance.binding.binder.schemeRequirements := by
  have template := sourceLocalSchemeTemplateIds_mem_iff.mpr ⟨owner, contains, rfl⟩
  have used : node ∈ localDeclarationUses receipt.bodyNodes := by
    apply List.mem_filterMap.mpr
    refine ⟨.expression node, receipt.nodeInBody, ?_⟩
    change (match (match node.form with
      | .call _ _ (.declaration value) | .reference _ (.declaration value) => some value
      | _ => none) with | some _ => some node | none => none) = some node
    rw [form]
  have belongs := receipt.templates.foreign_mem used issued (specialized_inventory selected specialized template)
  obtain ⟨requirement, requirementMember, same⟩ := List.mem_map.mp belongs
  have bindingMember := localLambdaInstances_bindings receipt.contextual.discovered
    receipt.contextual.localInstance receipt.contextual.member
  have initialized := collector_initialized bindingMember
  let owned : LocalSchemeTemplateOwner := {
    binder := receipt.contextual.localInstance.binding.binder
    initializer := .expression receipt.contextual.localInstance.binding.initializer
    requirement }
  have ownedContains : ContainsLocalSchemeTemplate row.function.typedBody owned :=
    List.mem_flatMap.mpr ⟨_, initialized, List.mem_map.mpr ⟨requirement, requirementMember, rfl⟩⟩
  have ownerEq := (SourceSelectedTemplateInventory.selected_ownership selected).2.owner_unique
    contains ownedContains same.symm
  exact ⟨congrArg (fun owner : LocalSchemeTemplateOwner => owner.binder) ownerEq,
    (congrArg (fun owner : LocalSchemeTemplateOwner => owner.requirement) ownerEq).symm ▸ requirementMember⟩

/-- Same-owner predicate scope for every cached ordinary row. All premises
are actual cache, checker and specialization receipts; no initial plan
membership or whole-program body-typing premise is present. -/
theorem original_template_scoped {raw : Workspace.RawWorkspace} {fuel : Nat}
    {compiled : SourceCoreCompiler.Compiled} {cached : SourceCoreUnifiedCompilation.Compiled}
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (position : cached.indexed.base.functions[index]? = some named)
    (selected : Selected compiled named.specialized fuel)
    {signature : ProgramFunctionSignature} {generic : CheckedFunction} {supplied : ParameterSubstitution}
    (specialized : SourceSpecialization.specializeFunction signature generic supplied = .ok named.specialized)
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
    SourceCompiledDirectCallPredicateOrigins.specialized_call emitter named.specialized.parameterSubstitution
  rw [← selected.source] at specializedEmitter
  obtain ⟨node, present, callee, arguments, instantiation, form, issued, cataloged, paired⟩ := specializedEmitter
  let specializedOwner := StructuralSubstitution.applyLocalSchemeTemplateOwner named.specialized.parameterSubstitution owner
  have specializedContains : ContainsLocalSchemeTemplate named.specialized.function.typedBody specializedOwner := by
    rw [selected.source]
    exact StructuralSubstitution.ContainsLocalSchemeTemplate.applyParameters named.specialized.parameterSubstitution contains
  intro metavariable occurs
  have specializedOccurs := predicate_parameters_keep named.specialized.parameterSubstitution owner.requirement.predicate occurs
  cases closed : SourcePreparedOpenCallEdges.InstantiationClosed instantiation with
  | true =>
      apply False.elim
      apply closed_predicate_absent closed paired
      simpa only [predicateEq] using specializedOccurs
  | false =>
      obtain ⟨receipt⟩ := SourceCachedTemplateReceipts.cached_open_call_owner
        artifact checked position selected present form cataloged closed
      obtain ⟨binderEq, requirement⟩ := contextual_owner selected specialized form receipt specializedContains issued
      change metavariable ∈ specializedOwner.binder.scheme.quantified
      rw [binderEq]
      exact cached_instance_template_scoped cached position receipt.contextual.discovered
        receipt.contextual.member requirement specializedOccurs

/-- The actual ordinary catalog origin supplies specialization and the
original checker receipt at this completed cache position. -/
theorem cached_origin_scope {raw : Workspace.RawWorkspace} {fuel : Nat}
    {compiled : SourceCoreCompiler.Compiled} {cached : SourceCoreUnifiedCompilation.Compiled}
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (position : cached.indexed.base.functions[index]? = some named)
    (origin : CoreLowering.RecursiveNamedPublicSpecializationMeaning.Origin cached.sourceProgram named.specialized) :
    ∃ original ∈ compiled.program.functions,
      named.specialized.function = SourceSpecialization.applyCheckedFunction named.specialized.parameterSubstitution original ∧
      (∀ owner, ContainsLocalSchemeTemplate original.typedBody owner →
        ∀ metavariable ∈ TypedTraitResolution.predicateVariables owner.requirement.predicate,
          metavariable ∈ owner.binder.scheme.quantified) := by
  obtain ⟨request, signature, original, _signatureMember, originalMember, _resolved, specialized⟩ := origin
  rw [(compiled.artifact_fields artifact).1] at originalMember
  obtain ⟨bodySignature, signatureMember, bodyChecked⟩ :=
    checkProgram_success_function_body checked originalMember
  obtain ⟨body⟩ := BodyReceipt.of_check bodyChecked
  have same := (CoreLowering.CallableCoercionBodyProvenance.specialization_fields specialized).1
  let selected : Selected compiled named.specialized fuel :=
    ⟨original, originalMember, bodySignature, signatureMember, body, same⟩
  refine ⟨original, originalMember, same, ?_⟩
  intro owner contains
  rw [body.source] at contains
  exact original_template_scoped artifact checked position selected specialized contains

end Solcore.SourceSemantics.SourceCachedTemplateScope
