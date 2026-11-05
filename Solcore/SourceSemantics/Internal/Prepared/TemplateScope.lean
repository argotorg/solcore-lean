import Solcore.SourceSemantics.Internal.Compiled.LoopHeaders
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.HeadersAndPrograms
import Solcore.SourceSemantics.Internal.Compiled.BodySelection
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.PreparedOrigins
import Solcore.SourceSemantics.Internal.Compiled.InitializerOccurrences

/-!
# Template scope of cached bodies

The completed cache supplies template inventory, qualified-read metadata and same-owner scope.
Generalization receipts keep the private variables of retained binders through it.
-/

section
-- leanmerge: from Solcore.SourceSemantics.SourceCachedTemplateReceipts
/-! Successful cache construction validates and scans its complete prepared
plan, including ordinary helpers discovered after the initial worklist. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.SourceCachedTemplateReceipts
open Frontend SourceInference TypeSystem SourceSpecializationWorklist
open SourceCompiledLocalFinalization SourcePreparedPlanGrowth SourcePreparedCallEdgeOrigins
open CoreLowering
open CoreLowering.CallableCoercionPreparationSteps (Specialized bind_ok)

private theorem mapError_ok {α ε δ : Type} {action : Except ε α} {f : ε → δ} {value : α}
    (accepted : action.mapError f = .ok value) : action = .ok value := by
  cases action <;> cases accepted <;> rfl

private theorem checked_none {duplicate : Option (SourceSpecialization.SpecializationKey × Nat)}
    (accepted : (match duplicate with
      | none => Except.ok ()
      | some (key, count) => Except.error (Error.duplicatePlanSpecializations key count)) = .ok ()) :
    duplicate = none := by
  cases duplicate with
  | none => rfl
  | some value => rcases value with ⟨key, count⟩; cases accepted

private theorem unique_keys {plan : Plan} (accepted : validatePlanSpecializationsUnique plan = .ok ()) :
    (plan.specializations.map (·.key)).Nodup := by
  rcases plan with ⟨seeds, entries, calls, references⟩
  induction entries with
  | nil => exact .nil
  | cons head rest ih =>
    unfold validatePlanSpecializationsUnique at accepted
    have noDuplicate := checked_none accepted
    change (if (rest.filter (fun entry => decide (entry.key = head.key))).isEmpty then _
      else some (head.key, (rest.filter (fun entry => decide (entry.key = head.key))).length + 1)) = none at noDuplicate
    split at noDuplicate
    · have absent : head.key ∉ rest.map (·.key) := by
        have empty : rest.filter (fun entry => decide (entry.key = head.key)) = [] := List.isEmpty_iff.mp ‹_ = true›
        intro member
        obtain ⟨entry, member, same⟩ := List.mem_map.mp member
        have : entry ∈ rest.filter (fun entry => decide (entry.key = head.key)) := List.mem_filter.mpr ⟨member, by simpa only [decide_eq_true_eq] using same⟩
        rw [empty] at this
        cases this
      have tailAccepted : validatePlanSpecializationsUnique ⟨seeds, rest, calls, references⟩ = .ok () := by
        unfold validatePlanSpecializationsUnique
        rw [noDuplicate]
        rfl
      exact List.nodup_cons.mpr ⟨absent, ih tailAccepted⟩
    · cases noDuplicate

private theorem member_filter {entries : List Specialized} {row : Specialized}
    (unique : (entries.map (·.key)).Nodup) (member : row ∈ entries) :
    entries.filter (fun other => decide (other.key = row.key)) = [row] := by
  induction entries with
  | nil => cases member
  | cons first rest ih =>
      obtain ⟨absent, unique⟩ := List.nodup_cons.mp unique
      rcases List.mem_cons.mp member with rfl | member
      · have empty : rest.filter (fun other => decide (other.key = row.key)) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro other present matched
          exact absent (List.mem_map.mpr ⟨other, present, of_decide_eq_true matched⟩)
        simp only [List.filter_cons, decide_true, if_true, empty]
      · have different : first.key ≠ row.key := by
          intro same
          exact absent (List.mem_map.mpr ⟨row, member, same.symm⟩)
        simpa only [List.filter_cons, decide_eq_false different, Bool.false_eq_true, if_false] using ih unique member

private theorem metadata_aux {program : CheckedProgram} {budget fuel next : Nat}
    {before after : Plan}
    (accepted : SourceCompilationPlan.prepareExecutablePlanEvidenceAux program budget fuel next before = .ok after) :
    ∀ index caller, next ≤ index → after.specializations[index]? = some caller →
      SourceCompilationPlan.validateSpecializationMetadataWith true caller = .ok () := by
  induction fuel generalizing next before after with
  | zero =>
    unfold SourceCompilationPlan.prepareExecutablePlanEvidenceAux at accepted
    split at accepted
    · rename_i ended
      cases accepted
      intro index caller bound found
      have length := List.getElem?_eq_none_iff.mp ended
      have present := (List.getElem?_eq_some_iff.mp found).1
      omega
    · cases accepted
  | succ fuel ih =>
    have growth := (SourcePreparedOpenCallEdges.aux accepted).1
    unfold SourceCompilationPlan.prepareExecutablePlanEvidenceAux at accepted
    split at accepted
    · rename_i ended
      cases accepted
      intro index caller bound found
      have length := List.getElem?_eq_none_iff.mp ended
      have present := (List.getElem?_eq_some_iff.mp found).1
      omega
    · rename_i caller found
      obtain ⟨checked, metadata, accepted⟩ := bind_ok accepted
      cases checked
      obtain ⟨extended, _scan, remaining⟩ := bind_ok accepted
      intro index actual bound selected
      by_cases current : index = next
      · subst index
        have same := Option.some.inj (selected.symm.trans (growth.at found))
        subst actual
        exact metadata
      · exact ih remaining index actual (by omega) selected

/-- The actual automatic catalog pass checks uniqueness of the same final
plan retained by the completed cache. -/
theorem cached_unique (cached : SourceCoreUnifiedCompilation.Compiled) :
    (cached.indexed.base.plan.specializations.map (·.key)).Nodup := by
  have accepted := cached.compatiblePrepared
  unfold SourceCoreCompatibleFunctions.prepare at accepted
  obtain ⟨executable, executed, accepted⟩ := bind_ok accepted
  obtain ⟨locals, discovered, _accepted⟩ := bind_ok accepted
  have executed := mapError_ok executed
  have same := Except.ok.inj (executed.symm.trans
    (SourceCoreUnifiedPreparationCertificates.compiled_planPrepared cached))
  subst executable
  have discovered := mapError_ok discovered
  unfold SourceCompilationPlan.localLambdaCatalog at discovered
  obtain ⟨checked, checkedEq, _⟩ := bind_ok discovered
  cases checked
  exact unique_keys checkedEq

/-- A real cache position selects the complete source row uniquely in its
final plan, without initial-worklist membership. -/
theorem cached_exact (cached : SourceCoreUnifiedCompilation.Compiled)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (position : cached.indexed.base.functions[index]? = some named) :
    SourceCompilationPlan.exactSpecialization cached.indexed.base.plan named.specialized.key =
      .ok named.specialized := by
  have member := CoreLowering.RecursiveNamedPreparedFinalPlanOrigins.final_member cached position rfl
  have filtered := member_filter (cached_unique cached) member
  simp only [SourceCompilationPlan.exactSpecialization, filtered]

/-- Metadata validation covers every completed cache row. -/
theorem cached_metadata (cached : SourceCoreUnifiedCompilation.Compiled)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (position : cached.indexed.base.functions[index]? = some named) :
    SourceCompilationPlan.validateSpecializationMetadataWith true named.specialized = .ok () := by
  have accepted := SourceCoreUnifiedPreparationCertificates.compiled_planPrepared cached
  unfold SourceCompilationPlan.prepareExecutablePlanEvidence
    SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget at accepted
  obtain ⟨scanned, inspected, accepted⟩ := bind_ok accepted
  obtain ⟨checked, _canonical, returned⟩ := bind_ok accepted
  cases checked
  cases returned
  obtain ⟨slot, found⟩ := List.mem_iff_getElem?.mp
    (CoreLowering.RecursiveNamedPreparedFinalPlanOrigins.final_member cached position rfl)
  exact metadata_aux inspected slot named.specialized (Nat.zero_le _) found

private theorem exact_member_eq {plan : Plan} {key : SourceSpecialization.SpecializationKey}
    {selected other : Specialized}
    (accepted : SourceCompilationPlan.exactSpecialization plan key = .ok selected)
    (member : other ∈ plan.specializations) (same : other.key = key) : other = selected := by
  unfold SourceCompilationPlan.exactSpecialization at accepted
  split at accepted <;> try contradiction
  cases accepted
  rename_i found
  have present : other ∈ plan.specializations.filter (fun row => decide (row.key = key)) :=
    List.mem_filter.mpr ⟨member, by simpa only [decide_eq_true_eq] using same⟩
  rw [found] at present
  exact List.mem_singleton.mp present

private theorem exact_member {plan : Plan} {key : SourceSpecialization.SpecializationKey}
    {selected : Specialized}
    (accepted : SourceCompilationPlan.exactSpecialization plan key = .ok selected) :
    selected ∈ plan.specializations := by
  unfold SourceCompilationPlan.exactSpecialization at accepted
  split at accepted <;> try contradiction
  cases accepted
  rename_i found
  have present : selected ∈ plan.specializations.filter (fun row => decide (row.key = key)) := by
    rw [found]
    exact List.mem_cons_self
  exact (List.mem_filter.mp present).1

/-- Every real ancestry branch for a cataloged call is source-emitted by the
same complete selected row. Synthetic outer edges are eliminated by the
actual method/ordinary catalog separation. -/
theorem final_source_origin {program : CheckedProgram} {input final : Plan}
    (catalog : SignatureCatalogWellFormed program.signatures)
    (growth : Growth input final) {caller : Specialized}
    (selected : SourceCompilationPlan.exactSpecialization final caller.key = .ok caller)
    {edge : CallEdge} (origin : Origin program input final edge)
    (sameCaller : edge.caller = caller.key)
    (cataloged : edge.callee.declaration ∈ program.signatures.functions.map (·.id)) :
    CallEdge.SourceOrigin program caller.key caller.function.typedBody edge := by
  have finalSelected := selected
  cases origin with
  | input _ _ row member source =>
      have same := exact_member_eq finalSelected (growth.rows.entries.subset member)
        (source.caller_eq.symm.trans sameCaller)
      subst row
      exact source
  | outer event _ same =>
      have target : event.root.key.declaration ∈ program.signatures.functions.map (·.id) := by
        simpa only [same, Event.outer] using cataloged
      exact False.elim (SourcePreparedCatalogedCallOrigin.selection_key_not_catalog catalog event.selection target)
  | suppliedRoot event later source =>
      have root := CallableCoercionPlanProvenance.complete_root event.extended
      have member := exact_member root
      have same := exact_member_eq finalSelected (later.rows.entries.subset member)
        (source.caller_eq.symm.trans sameCaller)
      rw [same] at source
      exact source
  | ordinary event later row member source =>
      have same := exact_member_eq finalSelected (later.rows.entries.subset member)
        (source.caller_eq.symm.trans sameCaller)
      subst row
      exact source


/-- Open cataloged calls in real cached rows retain their complete original
owner, including rows discovered after the input worklist. -/
theorem cached_open_call_owner {raw : Workspace.RawWorkspace} {fuel : Nat}
    {compiled : SourceCoreCompiler.Compiled} {cached : SourceCoreUnifiedCompilation.Compiled}
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (position : cached.indexed.base.functions[index]? = some named)
    (selected : Selected compiled named.specialized fuel)
    {node : ExpressionNode} (present : .expression node ∈ named.specialized.function.typedBody.nodes)
    {callee : ExpressionId} {arguments : List ExpressionId} {instantiation : DeclarationInstantiation}
    (form : node.form = .call callee arguments (.declaration instantiation))
    (cataloged : instantiation.declaration ∈ compiled.program.signatures.functions.map (·.id))
    (opened : SourcePreparedOpenCallEdges.InstantiationClosed instantiation = false) :
    Nonempty (SourceCompiledTemplateCallOwner.PreparedContextual compiled named.specialized node instantiation) := by
  obtain ⟨programEq, planEq, _⟩ := compiled.artifact_fields artifact
  have prepared := SourceCoreUnifiedPreparationCertificates.compiled_planPrepared cached
  rw [programEq, planEq] at prepared
  obtain ⟨growth, covered⟩ := SourcePreparedOpenCallEdges.of_default_preparation prepared
  have member := RecursiveNamedPreparedFinalPlanOrigins.final_member cached position rfl
  obtain ⟨edge⟩ := covered named.specialized member node present callee arguments instantiation form opened
  have origin := SourcePreparedFinalCallEdgeOrigins.of_default_preparation prepared
    edge.edge (edge.retained edge.present)
  have source := final_source_origin (SignatureCatalogWellFormed.ofCheckProgram checked) growth
    (cached_exact cached position) origin edge.callerEq (edge.declarationEq.symm ▸ cataloged)
  obtain ⟨contextual⟩ := SourcePreparedOpenCallOwner.contextual_of_open
    (SourceCompiledTemplateCallOwner.selected_unique selected) present form opened source edge.occurrenceEq
  obtain ⟨bodyNodes, bodyAccepted, nodeInBody, templates⟩ :=
    contextual.body (SourceCompiledTemplateCallOwner.selected_unique selected) present
  exact ⟨⟨cached.indexed.base.plan, prepared, edge, contextual,
    bodyNodes, bodyAccepted, nodeInBody, templates⟩⟩

end Solcore.SourceSemantics.SourceCachedTemplateReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCachedTemplateScope
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
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceBodyTemplateOrigins
/-! The same finalizer and preparation receipts identify local template owners
inside ordinary functions and implementation methods. Catalog separation is
used for each emitted callee; it does not constrain the caller's body origin. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceBodyTemplateOrigins
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceSpecializationWorklist SourceCompiledLocalFinalization
open CoreLowering SourceCachedTemplateReceipts

theorem selected_unique {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (receipt : BodySelection compiled row fuel) : NodeOccurrencesUnique row.function.typedBody := by
  have unique := receipt.body.resources.graph_closed.wellFormed.nodeOccurrencesUnique
  rw [receipt.source]
  change (nodeOccurrenceIds (SourceSpecialization.applyTypedSource row.parameterSubstitution receipt.body.finalized.typedSource)).Nodup
  have occurrences : nodeOccurrenceIds (SourceSpecialization.applyTypedSource row.parameterSubstitution receipt.body.finalized.typedSource) =
      nodeOccurrenceIds receipt.body.finalized.typedSource := by
    simp only [nodeOccurrenceIds, SourceSpecialization.applyTypedSource, List.map_map]
    congr 1
    funext node
    cases node <;> rfl
  rw [occurrences]
  exact unique

theorem selected_ownership {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : BodySelection compiled row fuel) :
    LocalIdentityOwnership row.function.typedBody ∧ LocalSchemeTemplateOwnership row.function.typedBody := by
  rw [selected.source]
  exact ⟨StructuralSubstitution.LocalIdentityOwnership.applyParameters _
      selected.body.resources.local_identity_ownership,
    StructuralSubstitution.LocalSchemeTemplateOwnership.applyParameters _
      selected.body.resources.ledger.templateOwnership⟩

theorem cached_open_call_owner {raw : Workspace.RawWorkspace} {fuel : Nat}
    {compiled : SourceCoreCompiler.Compiled} {cached : SourceCoreUnifiedCompilation.Compiled}
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (position : cached.indexed.base.functions[index]? = some named)
    (selected : BodySelection compiled named.specialized fuel)
    {node : ExpressionNode} (present : .expression node ∈ named.specialized.function.typedBody.nodes)
    {callee : ExpressionId} {arguments : List ExpressionId} {instantiation : DeclarationInstantiation}
    (form : node.form = .call callee arguments (.declaration instantiation))
    (cataloged : instantiation.declaration ∈ compiled.program.signatures.functions.map (·.id))
    (opened : SourcePreparedOpenCallEdges.InstantiationClosed instantiation = false) :
    Nonempty (SourceCompiledTemplateCallOwner.PreparedContextual compiled named.specialized node instantiation) := by
  obtain ⟨programEq, planEq, _⟩ := compiled.artifact_fields artifact
  have prepared := SourceCoreUnifiedPreparationCertificates.compiled_planPrepared cached
  rw [programEq, planEq] at prepared
  obtain ⟨growth, covered⟩ := SourcePreparedOpenCallEdges.of_default_preparation prepared
  have member := RecursiveNamedPreparedFinalPlanOrigins.final_member cached position rfl
  obtain ⟨edge⟩ := covered named.specialized member node present callee arguments instantiation form opened
  have origin := SourcePreparedFinalCallEdgeOrigins.of_default_preparation prepared
    edge.edge (edge.retained edge.present)
  have source := final_source_origin (SignatureCatalogWellFormed.ofCheckProgram checked) growth
    (cached_exact cached position) origin edge.callerEq (edge.declarationEq.symm ▸ cataloged)
  obtain ⟨contextual⟩ := SourcePreparedOpenCallOwner.contextual_of_open
    (selected_unique selected) present form opened source edge.occurrenceEq
  obtain ⟨bodyNodes, bodyAccepted, nodeInBody, templates⟩ :=
    contextual.body (selected_unique selected) present
  exact ⟨⟨cached.indexed.base.plan, prepared, edge, contextual,
    bodyNodes, bodyAccepted, nodeInBody, templates⟩⟩

end Solcore.SourceSemantics.SourceBodyTemplateOrigins
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceBodyTemplateScope
/-! The completed cache supplies template inventory, original qualified-read
metadata and the complete same-owner relation for ordinary and method bodies. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceBodyTemplateScope
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
    {row : Specialized} {fuel : Nat} (selected : BodySelection compiled row fuel)
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
    specialized (SourceBodyTemplateOrigins.selected_ownership selected).1
    (LocalSchemeTemplateOwner.binding_mem contains) nonempty
  apply List.mem_flatMap.mpr
  refine ⟨binding, present, ?_⟩
  rw [binder]
  exact List.mem_map.mpr ⟨owner.requirement, requirement, same⟩

theorem contextual_owner {compiled : SourceCoreCompiler.Compiled}
    {row : Specialized} {fuel : Nat} (selected : BodySelection compiled row fuel)
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
  have ownerEq := (SourceBodyTemplateOrigins.selected_ownership selected).2.owner_unique
    contains ownedContains same.symm
  exact ⟨congrArg (fun owner : LocalSchemeTemplateOwner => owner.binder) ownerEq,
    (congrArg (fun owner : LocalSchemeTemplateOwner => owner.requirement) ownerEq).symm ▸ requirementMember⟩

/-- Same-owner predicate scope for every actual checked cached body. All premises
are actual cache, checker and specialization receipts; no initial plan
membership or whole-program body-typing premise is present. -/
theorem original_template_scoped {raw : Workspace.RawWorkspace} {fuel : Nat}
    {compiled : SourceCoreCompiler.Compiled} {cached : SourceCoreUnifiedCompilation.Compiled}
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (position : cached.indexed.base.functions[index]? = some named)
    (selected : BodySelection compiled named.specialized fuel)
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
      obtain ⟨receipt⟩ := SourceBodyTemplateOrigins.cached_open_call_owner
        artifact checked position selected present form cataloged closed
      obtain ⟨binderEq, requirement⟩ := contextual_owner selected specialized form receipt specializedContains issued
      change metavariable ∈ specializedOwner.binder.scheme.quantified
      rw [binderEq]
      exact SourceCachedTemplateScope.cached_instance_template_scoped cached position receipt.contextual.discovered
        receipt.contextual.member requirement specializedOccurs

/-- Complete preparation supplies a real specialization for every cache row,
including implementation methods and ordinary helpers discovered later. -/
theorem cached_template_scoped {raw : Workspace.RawWorkspace} {fuel : Nat}
    {compiled : SourceCoreCompiler.Compiled} {cached : SourceCoreUnifiedCompilation.Compiled}
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (position : cached.indexed.base.functions[index]? = some named)
    (selected : BodySelection compiled named.specialized fuel)
    {owner : LocalSchemeTemplateOwner}
    (contains : ContainsLocalSchemeTemplate selected.body.finalized.typedSource owner) :
    ∀ metavariable ∈ TypedTraitResolution.predicateVariables owner.requirement.predicate,
      metavariable ∈ owner.binder.scheme.quantified := by
  have prepared := SourceCoreUnifiedPreparationCertificates.compiled_planPrepared cached
  have member := CoreLowering.RecursiveNamedPreparedFinalPlanOrigins.final_member cached position rfl
  obtain ⟨signature, original, supplied, specialized⟩ :=
    CoreLowering.CallablePreparedFinalSpecializationOrigins.of_default_preparation prepared _ member
  exact original_template_scoped artifact checked position selected specialized contains

/-- Both catalog origins construct their own actual checker body. In the
method branch the executable recheck is identified with the retained method. -/
theorem catalog_selection {raw : Workspace.RawWorkspace} {fuel : Nat}
    {compiled : SourceCoreCompiler.Compiled}
    (checked : checkProgram raw fuel = .ok compiled.program)
    {row : Specialized}
    (origin : CoreLowering.CallablePreparedFinalCatalogOrigins.CatalogOrigin compiled.program row) :
    Nonempty (BodySelection compiled row fuel) := by
  cases origin with
  | ordinary origin =>
      obtain ⟨request, signature, original, _signatureMember, originalMember, _resolved, specialized⟩ := origin
      obtain ⟨bodySignature, signatureMember, bodyChecked⟩ :=
        checkProgram_success_function_body checked originalMember
      obtain ⟨body⟩ := BodyReceipt.of_check bodyChecked
      exact ⟨{
        original := original
        signature := bodySignature
        body := body
        origin := .ordinary originalMember signatureMember
        specialized := (CoreLowering.CallableCoercionBodyProvenance.specialization_fields specialized).1 }⟩
  | method selection =>
      obtain ⟨retained, member, _identity, same⟩ := selection.retained
        (CoreLowering.CallableMethodBodyCoherence.of_checked checked)
      obtain ⟨body⟩ := SourceCompiledMethodFinalization.MethodBodyReceipt.of_checked checked member
      have specialized := selection.specialized
      rw [same] at specialized
      exact ⟨body.toBodySelection member
        (CoreLowering.CallableCoercionBodyProvenance.specialization_fields specialized).1⟩

/-- A completed cache position and raw checking provenance suffice to obtain
this same original body and its template scope, for either catalog origin. -/
theorem cached_selection_scope {raw : Workspace.RawWorkspace} {fuel : Nat}
    {compiled : SourceCoreCompiler.Compiled} {cached : SourceCoreUnifiedCompilation.Compiled}
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (position : cached.indexed.base.functions[index]? = some named) :
    ∃ selected : BodySelection compiled named.specialized fuel,
      ∀ owner, ContainsLocalSchemeTemplate selected.body.finalized.typedSource owner →
        ∀ metavariable ∈ TypedTraitResolution.predicateVariables owner.requirement.predicate,
          metavariable ∈ owner.binder.scheme.quantified := by
  have member := CoreLowering.RecursiveNamedPreparedFinalPlanOrigins.final_member cached position rfl
  have origin := CoreLowering.CallablePreparedFinalCatalogOrigins.of_default_preparation
    (SourceCoreUnifiedPreparationCertificates.compiled_planPrepared cached) _ member
  rw [(compiled.artifact_fields artifact).1] at origin
  obtain ⟨selected⟩ := catalog_selection checked origin
  exact ⟨selected, fun _ contains => cached_template_scoped artifact checked position selected contains⟩

end Solcore.SourceSemantics.SourceBodyTemplateScope
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceBodyGeneralizationLedger
/-! Actual completed-cache receipts classify every remaining flexible ledger
variable by its exact initialized source owner. This includes method bodies
and ordinary bodies discovered after the initial worklist. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceBodyGeneralizationLedger
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization

/-- A flexible variable in the final solved ledger must come from a literal
retained template owner. Non-template rows are closed by actual specialization. -/
theorem variable_owner {raw : Workspace.RawWorkspace} {fuel : Nat}
    {compiled : SourceCoreCompiler.Compiled} {cached : SourceCoreUnifiedCompilation.Compiled}
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (position : cached.indexed.base.functions[index]? = some named)
    (selected : BodySelection compiled named.specialized fuel)
    {requirement : SolvedRequirement}
    (member : requirement ∈ selected.body.finalized.solvedRequirements)
    {q : TypeVarId}
    (occurs : q ∈ TypedTraitResolution.predicateVariables requirement.predicate) :
    ∃ owner : LocalSchemeTemplateOwner,
      ContainsLocalSchemeTemplate selected.body.finalized.typedSource owner ∧
      requirement.id = owner.requirement.templateRequirement ∧
      requirement.predicate = owner.requirement.predicate ∧
      q ∈ owner.binder.scheme.quantified := by
  by_cases template : requirement.id ∈
      sourceLocalSchemeTemplateIds selected.body.finalized.typedSource
  · obtain ⟨owner, _occurrence, contains, sameId, samePredicate, _⟩ :=
      (selected.body.resources.ledger.template_scoped member template).exact_owner
    refine ⟨owner, contains, sameId, samePredicate, ?_⟩
    apply SourceBodyTemplateScope.cached_template_scoped artifact checked position selected contains
    simpa only [samePredicate] using occurs
  · have closed := SourceCompiledNonTemplateLedger.finalized_closed selected.body
      selected.specialized (SourceCompiledNonTemplateLedger.cached_closed cached position)
      member template
    rw [closed] at occurs
    exact False.elim (List.not_mem_nil occurs)

/-- Removing the current binder's template IDs leaves only different actual
owners; neither a row identity nor a predicate-to-owner pairing is assumed. -/
theorem other_owner {raw : Workspace.RawWorkspace} {fuel : Nat}
    {compiled : SourceCoreCompiler.Compiled} {cached : SourceCoreUnifiedCompilation.Compiled}
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (position : cached.indexed.base.functions[index]? = some named)
    (selected : BodySelection compiled named.specialized fuel)
    {binder : TypedBinder} {requirement : SolvedRequirement}
    (member : requirement ∈ selected.body.finalized.solvedRequirements)
    (notOwn : requirement.id ∉ localSchemeTemplateIds binder)
    {q : TypeVarId}
    (occurs : q ∈ TypedTraitResolution.predicateVariables requirement.predicate) :
    ∃ owner : LocalSchemeTemplateOwner,
      ContainsLocalSchemeTemplate selected.body.finalized.typedSource owner ∧
      requirement.id = owner.requirement.templateRequirement ∧
      requirement.predicate = owner.requirement.predicate ∧
      owner.binder ≠ binder ∧ q ∈ owner.binder.scheme.quantified := by
  obtain ⟨owner, contains, sameId, samePredicate, quantified⟩ :=
    variable_owner artifact checked position selected member occurs
  refine ⟨owner, contains, sameId, samePredicate, ?_, quantified⟩
  intro sameBinder
  apply notOwn
  rw [sameId, ← sameBinder]
  exact List.mem_map.mpr
    ⟨owner.requirement, LocalSchemeTemplateOwner.requirement_mem contains, rfl⟩

/-- The same offending row identifies a different binder in the actual
inference source, before final substitution, as used by generalization traces. -/
theorem raw_other_owner {raw : Workspace.RawWorkspace} {fuel : Nat}
    {compiled : SourceCoreCompiler.Compiled} {cached : SourceCoreUnifiedCompilation.Compiled}
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (position : cached.indexed.base.functions[index]? = some named)
    (selected : BodySelection compiled named.specialized fuel)
    {binder : TypedBinder} {requirement : SolvedRequirement}
    (member : requirement ∈ selected.body.finalized.solvedRequirements)
    (notOwn : requirement.id ∉
      localSchemeTemplateIds (binder.applySubstitution selected.body.finalized.substitution))
    {q : TypeVarId}
    (occurs : q ∈ TypedTraitResolution.predicateVariables requirement.predicate) :
    ∃ owner : LocalSchemeTemplateOwner,
      ContainsLocalSchemeTemplate (SourceCompiledGeneralizedSoundness.evidenceSource selected) owner ∧
      requirement.id = owner.requirement.templateRequirement ∧
      requirement.predicate =
        (FlexibleSubstitution.applyLocalSchemeTemplateOwner
          selected.body.finalized.substitution owner).requirement.predicate ∧
      owner.binder ≠ binder ∧ q ∈ owner.binder.scheme.quantified := by
  obtain ⟨finalOwner, contains, sameId, samePredicate, distinct, quantified⟩ :=
    other_owner artifact checked position selected member notOwn occurs
  rw [selected.body.resources.source_eq] at contains
  unfold ContainsLocalSchemeTemplate at contains
  rw [FlexibleSubstitution.localSchemeTemplateOwners_applySubstitution] at contains
  obtain ⟨owner, rawContains, transformed⟩ := List.mem_map.mp contains
  subst finalOwner
  refine ⟨owner, rawContains, sameId, samePredicate, ?_, quantified⟩
  intro same
  apply distinct
  exact congrArg (TypedBinder.applySubstitution selected.body.finalized.substitution) same

end Solcore.SourceSemantics.SourceBodyGeneralizationLedger
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceBodyRetainedTemplatePrivacy
/-! Actual generalization receipts preserve an already retained binder's
private variables in newly allocated statement and for-header binders. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceBodyRetainedTemplatePrivacy
open Frontend SourceInference TypeSystem SourceInferenceSoundness ProtectedVariables
open SourceCompiledLocalFinalization

private theorem predicate_image {substitution : Substitution} {predicate : ProgramPredicate}
    {type : Ty} (member : type ∈ predicate.subject :: predicate.arguments)
    {v q : TypeVarId} (occurs : v ∈ type.freeVariables)
    (image : q ∈ (substitution.apply (.variable v)).freeVariables) :
    q ∈ TypedTraitResolution.predicateVariables
      (TypedTraitResolution.applySubstitution substitution predicate) := by
  have inside := MonomorphicGeneralization.replacement_occurs substitution type occurs image
  rcases List.mem_cons.mp member with rfl | member
  · exact TypedTraitResolution.mem_predicateVariables_iff.mpr (.inl inside)
  · exact TypedTraitResolution.mem_predicateVariables_iff.mpr
      (.inr ⟨substitution.apply type, List.mem_map.mpr ⟨type, member, rfl⟩, inside⟩)


private theorem item_binders (item : ForItemForm) :
    item.initializedLetBinders = (forItemInitializedLetBindings item).map (·.binder) := by
  cases item <;> try rfl
  rename_i binder initializer
  cases initializer <;> rfl

private theorem statement_binders (form : StatementForm) :
    form.initializedLetBinders = (statementInitializedLetBindings form).map (·.binder) := by
  cases form <;> try rfl
  · rename_i binder initializer
    cases initializer <;> rfl
  · simp only [StatementForm.initializedLetBinders, statementInitializedLetBindings,
      List.map_append, List.map_flatMap]
    simp only [← item_binders]

private theorem source_binders (source : TypedSource) :
    source.initializedLetBinders = (initializedLetBindings source).map (·.binder) := by
  simp only [TypedSource.initializedLetBinders, initializedLetBindings, List.map_flatMap]
  apply congrArg (fun f : Node → List TypedBinder => source.nodes.flatMap f)
  funext node
  cases node with
  | expression expression => rfl
  | statement statement => exact statement_binders statement.form

private theorem template_origin {source : TypedSource} {binder : TypedBinder}
    (retained : binder ∈ source.initializedLetBinders) {requirement : LocalSchemeRequirement}
    (owned : requirement ∈ binder.schemeRequirements) :
    ∃ initializer, ContainsLocalSchemeTemplate source ⟨binder, initializer, requirement⟩ := by
  rw [source_binders] at retained
  obtain ⟨binding, present, same⟩ := List.mem_map.mp retained
  refine ⟨binding.initializer, List.mem_flatMap.mpr ⟨binding, present, ?_⟩⟩
  exact List.mem_map.mpr ⟨requirement, same ▸ owned, by cases binding; simp_all⟩

private theorem allocated_safe
    {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction}
    {fuel : Nat} (selected : BodySelection compiled row fuel)
    (templateScoped : ∀ owner, ContainsLocalSchemeTemplate selected.body.finalized.typedSource owner →
      ∀ v ∈ TypedTraitResolution.predicateVariables owner.requirement.predicate,
        v ∈ owner.binder.scheme.quantified)
    {ready result : State} {valueType : Ty} {binder inner : TypedBinder}
    (readyWF : ready.InferenceReady)
    (extension : selected.body.finalized.substitution.SemanticallyExtends ready.inference.substitution)
    (retained : binder ∈ (SourceCompiledGeneralizedSoundness.evidenceSource selected).initializedLetBinders)
    (innerRetained : inner ∈ (SourceCompiledGeneralizedSoundness.evidenceSource selected).initializedLetBinders)
    (resultSub : result.inference.substitution = ready.inference.substitution)
    (bodyEq : binder.scheme.body = ready.resolve valueType)
    (quantifiedSubset : binder.scheme.quantified ⊆ (ready.resolve valueType).freeVariables)
    (bodySafe : Safe inner.scheme.quantified ready valueType) :
    BinderSafe inner.scheme.quantified result binder := by
  have innerCapture := selected.body.resources.local_no_capture _ innerRetained
  have outerCapture := selected.body.resources.local_no_capture _ retained
  have fixed : ∀ q ∈ inner.scheme.quantified,
      selected.body.finalized.substitution.apply (.variable q) = .variable q := by
    intro q quantified
    simp only [Substitution.apply,
      (Substitution.lookup?_eq_none_iff_not_mem_domain _ _).mpr
        (innerCapture.quantified_fresh q quantified), Option.getD_none]
  have resultResolve : ∀ type, result.resolve type = ready.resolve type := by
    intro type
    simp only [State.resolve, InferState.resolve, resultSub]
  constructor
  · intro v occurs q image privateMember
    rw [resultResolve] at image
    have inBody := (List.mem_filter.mp occurs).1
    have inResolved := MonomorphicGeneralization.replacement_occurs
      ready.inference.substitution binder.scheme.body inBody image
    rw [bodyEq] at inResolved
    exact safe_resolved readyWF bodySafe q inResolved privateMember
  · intro requirement owned type typeMember v occurs _unbound q image privateMember
    rw [resultResolve] at image
    have finalImage := fixed_variable_occurs_at_final extension (fixed q privateMember) image
    have predicateOccurs := predicate_image typeMember occurs finalImage
    obtain ⟨initializer, contains⟩ := template_origin retained owned
    let owner : LocalSchemeTemplateOwner := ⟨binder, initializer, requirement⟩
    have finalizedContains := FlexibleSubstitution.ContainsLocalSchemeTemplate.applySubstitution
      selected.body.finalized.substitution contains
    rw [← selected.body.resources.source_eq] at finalizedContains
    have restricted : selected.body.finalized.substitution.without binder.scheme.quantified =
        selected.body.finalized.substitution :=
      FlexibleSubstitution.Substitution.without_eq_self_of_disjoint_domain _ _ outerCapture.quantified_fresh
    have finalizedOccurs : q ∈ TypedTraitResolution.predicateVariables
        (FlexibleSubstitution.applyLocalSchemeTemplateOwner selected.body.finalized.substitution owner).requirement.predicate := by
      change q ∈ TypedTraitResolution.predicateVariables
        (TypedTraitResolution.applySubstitution
          (selected.body.finalized.substitution.without binder.scheme.quantified) requirement.predicate)
      rw [restricted]
      exact predicateOccurs
    have quantified := templateScoped _ finalizedContains q finalizedOccurs
    exact bodySafe q (quantifiedSubset quantified) privateMember

/-- The actual statement receipt needs only its ready state, final extension
and retained binder to preserve an earlier event's private variables. -/
theorem cached_statement_receipt {raw : Workspace.RawWorkspace} {fuel : Nat}
    {compiled : SourceCoreCompiler.Compiled} {cached : SourceCoreUnifiedCompilation.Compiled}
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (position : cached.indexed.base.functions[index]? = some named)
    {selected : BodySelection compiled named.specialized fuel}
    {childFuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {entry : State} {result : Detail.StatementResult}
    (outer : LocalLetRequirementTiming.Receipt childFuel context source entry result)
    (ready : outer.ready.InferenceReady)
    (extension : selected.body.finalized.substitution.SemanticallyExtends outer.ready.inference.substitution)
    (retained : outer.binding.1 ∈ (SourceCompiledGeneralizedSoundness.evidenceSource selected).initializedLetBinders)
    (inner : TypedBinder)
    (innerRetained : inner ∈ (SourceCompiledGeneralizedSoundness.evidenceSource selected).initializedLetBinders)
    (bodySafe : Safe inner.scheme.quantified outer.ready outer.value.type) :
    BinderSafe inner.scheme.quantified result.state outer.binding.1 := by
  apply allocated_safe selected (fun _ contains =>
    SourceBodyTemplateScope.cached_template_scoped artifact checked position selected contains)
    ready extension retained innerRetained
    (congrArg InferState.substitution outer.inference_eq)
    (Detail.generalizeValue_scheme_body _ _ _ _) ?_ bodySafe
  exact fun _ quantified => (List.mem_filter.mp quantified).1

/-- Completed-cache preparation supplies the same statement producer for
ordinary functions and implementation methods at their actual cache position. -/
theorem cached_statement {raw : Workspace.RawWorkspace} {fuel : Nat}
    {compiled : SourceCoreCompiler.Compiled} {cached : SourceCoreUnifiedCompilation.Compiled}
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (position : cached.indexed.base.functions[index]? = some named)
    {selected : BodySelection compiled named.specialized fuel} {source : Syntax.Statement}
    (outer : BodyInitializerOccurrence selected source) (inner : TypedBinder)
    (innerRetained : inner ∈ (SourceCompiledGeneralizedSoundness.evidenceSource selected).initializedLetBinders)
    (bodySafe : Safe inner.scheme.quantified outer.receipt.ready outer.receipt.value.type) :
    BinderSafe inner.scheme.quantified outer.result.state outer.receipt.binding.1 :=
  cached_statement_receipt artifact checked position outer.receipt outer.ready
    outer.extension outer.retained inner innerRetained bodySafe

/-- Actual cache preparation also supplies method template scope for headers. -/
theorem cached_header {raw : Workspace.RawWorkspace} {fuel : Nat}
    {compiled : SourceCoreCompiler.Compiled} {cached : SourceCoreUnifiedCompilation.Compiled}
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (position : cached.indexed.base.functions[index]? = some named)
    {selected : BodySelection compiled named.specialized fuel}
    {childFuel : Nat} {context : Frontend.SourceInference.Context} {source : Syntax.ForItem}
    {entry : State} {result : ForItemForm × State}
    (outer : LocalHeaderRequirementTiming.Receipt childFuel context source entry result)
    (readyWF : outer.ready.InferenceReady)
    (extension : selected.body.finalized.substitution.SemanticallyExtends outer.ready.inference.substitution)
    (retained : outer.binding.1 ∈ (SourceCompiledGeneralizedSoundness.evidenceSource selected).initializedLetBinders)
    (inner : TypedBinder)
    (innerRetained : inner ∈ (SourceCompiledGeneralizedSoundness.evidenceSource selected).initializedLetBinders)
    (bodySafe : Safe inner.scheme.quantified outer.ready outer.value.type) :
    BinderSafe inner.scheme.quantified result.2 outer.binding.1 := by
  apply allocated_safe selected (fun _ contains =>
    SourceBodyTemplateScope.cached_template_scoped artifact checked position selected contains)
    readyWF extension retained innerRetained ?_
    (Detail.generalizeValue_scheme_body _ _ _ _) ?_ bodySafe
  · exact congrArg (fun output : ForItemForm × State => output.2.inference.substitution) outer.completed
  · exact fun _ quantified => (List.mem_filter.mp quantified).1

end Solcore.SourceSemantics.SourceBodyRetainedTemplatePrivacy
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCachedNestedTemplatePrivacy
/-! Actual completed-cache template scope closes the requirements of a new outer
binder while preserving an inner binder's private quantified variables, including
ordinary helpers added by executable preparation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCachedNestedTemplatePrivacy
open Frontend SourceInference TypeSystem SourceInferenceSoundness ProtectedVariables
open SourceCompiledLocalFinalization

private theorem predicate_image {substitution : Substitution} {predicate : ProgramPredicate}
    {type : Ty} (member : type ∈ predicate.subject :: predicate.arguments)
    {v q : TypeVarId} (occurs : v ∈ type.freeVariables)
    (image : q ∈ (substitution.apply (.variable v)).freeVariables) :
    q ∈ TypedTraitResolution.predicateVariables
      (TypedTraitResolution.applySubstitution substitution predicate) := by
  have inside := MonomorphicGeneralization.replacement_occurs substitution type occurs image
  rcases List.mem_cons.mp member with rfl | member
  · exact TypedTraitResolution.mem_predicateVariables_iff.mpr (.inl inside)
  · exact TypedTraitResolution.mem_predicateVariables_iff.mpr
      (.inr ⟨substitution.apply type, List.mem_map.mpr ⟨type, member, rfl⟩, inside⟩)

/-- The inner binder's real finalizer check keeps each protected variable
fixed. The actual outer template then excludes those variables from every
live requirement, using the same source owner after finalization. -/
theorem outer_binder_safe {raw : Workspace.RawWorkspace} {fuel : Nat}
    {compiled : SourceCoreCompiler.Compiled} {cached : SourceCoreUnifiedCompilation.Compiled}
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (position : cached.indexed.base.functions[index]? = some named)
    (origin : CoreLowering.RecursiveNamedPublicSpecializationMeaning.Origin cached.sourceProgram named.specialized)
    {selected : Selected compiled named.specialized fuel} {outerSource innerSource : Syntax.Statement}
    (outer : InitializerOccurrence selected outerSource)
    (inner : InitializerOccurrence selected innerSource)
    (bodySafe : Safe inner.receipt.binding.1.scheme.quantified
      outer.receipt.ready outer.receipt.value.type) :
    BinderSafe inner.receipt.binding.1.scheme.quantified outer.result.state
      outer.receipt.binding.1 := by
  obtain ⟨_, _, _, _, _, _, specialized⟩ := origin
  have bodyEq : outer.receipt.binding.1.scheme.body =
      outer.receipt.ready.resolve outer.receipt.value.type := by
    exact Detail.generalizeValue_scheme_body _ _ _ _
  have innerCapture := selected.body.resources.local_no_capture _ (BodyInitializerOccurrence.retained inner)
  have outerCapture := selected.body.resources.local_no_capture _ (BodyInitializerOccurrence.retained outer)
  have fixed : ∀ q ∈ inner.receipt.binding.1.scheme.quantified,
      selected.body.finalized.substitution.apply (.variable q) = .variable q := by
    intro q quantified
    simp only [Substitution.apply,
      (Substitution.lookup?_eq_none_iff_not_mem_domain _ _).mpr
        (innerCapture.quantified_fresh q quantified), Option.getD_none]
  have resultResolve : ∀ type, outer.result.state.resolve type = outer.receipt.ready.resolve type := by
    intro type
    simp only [State.resolve, InferState.resolve, outer.receipt.inference_eq]
  constructor
  · intro v occurs q image privateMember
    rw [resultResolve] at image
    have inBody := (List.mem_filter.mp occurs).1
    have inResolved := MonomorphicGeneralization.replacement_occurs
      outer.receipt.ready.inference.substitution outer.receipt.binding.1.scheme.body inBody image
    rw [bodyEq] at inResolved
    exact safe_resolved outer.ready bodySafe q inResolved privateMember
  · intro requirement owned type typeMember v occurs _unbound q image privateMember
    rw [resultResolve] at image
    have finalImage := fixed_variable_occurs_at_final outer.extension (fixed q privateMember) image
    have predicateOccurs := predicate_image typeMember occurs finalImage
    let owner : LocalSchemeTemplateOwner :=
      ⟨outer.receipt.binding.1, .expression outer.receipt.value.id, requirement⟩
    have initialized : ({binder := outer.receipt.binding.1, initializer := .expression outer.receipt.value.id} :
        InitializedLetBinding) ∈ initializedLetBindings (SourceCompiledGeneralizedSoundness.evidenceSource selected.toBodySelection) :=
      List.mem_flatMap.mpr ⟨_, outer.recorded, List.mem_singleton_self _⟩
    have contains : ContainsLocalSchemeTemplate (SourceCompiledGeneralizedSoundness.evidenceSource selected.toBodySelection) owner :=
      List.mem_flatMap.mpr ⟨_, initialized, List.mem_map.mpr ⟨requirement, owned, rfl⟩⟩
    have finalizedContains := FlexibleSubstitution.ContainsLocalSchemeTemplate.applySubstitution
      selected.body.finalized.substitution contains
    simp only [SourceCompiledGeneralizedSoundness.evidenceSource,
      SourceCompiledGeneralizedSoundness.bodyRoots, Selected.toBodySelection] at finalizedContains
    rw [← selected.body.resources.source_eq] at finalizedContains
    have restricted : selected.body.finalized.substitution.without outer.receipt.binding.1.scheme.quantified =
        selected.body.finalized.substitution :=
      FlexibleSubstitution.Substitution.without_eq_self_of_disjoint_domain _ _ outerCapture.quantified_fresh
    have finalizedOccurs : q ∈ TypedTraitResolution.predicateVariables
        (FlexibleSubstitution.applyLocalSchemeTemplateOwner selected.body.finalized.substitution owner).requirement.predicate := by
      change q ∈ TypedTraitResolution.predicateVariables
        (TypedTraitResolution.applySubstitution
          (selected.body.finalized.substitution.without outer.receipt.binding.1.scheme.quantified) requirement.predicate)
      rw [restricted]
      exact predicateOccurs
    have quantified := SourceCachedTemplateScope.original_template_scoped
      artifact checked position selected specialized finalizedContains q finalizedOccurs
    have outerOccurs : q ∈ (outer.receipt.ready.resolve outer.receipt.value.type).freeVariables :=
      (List.mem_filter.mp quantified).1
    exact bodySafe q outerOccurs privateMember

end Solcore.SourceSemantics.SourceCachedNestedTemplatePrivacy
end
