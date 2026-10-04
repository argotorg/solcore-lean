import Solcore.SourceSemantics.CoreLowering.CallableAncestryPairedValidation
import Solcore.SourceSemantics.CoreLowering.CallEntryCertificates
import Solcore.SourceSemantics.CoreLowering.EmptySourceSubstitution

/-! Exact read and application recipes retain both parent histories. Their
semantic substitution and native compilation context stay separate. The
complete rewritten source, ordered witnesses and lexical header are preserved;
no body execution or source-table alignment is inferred from a native type. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableAppliedViewProvenance
open Frontend SourceInference TypeSystem
open SourceCoreCallableAncestryReadRecipes

abbrev MetadataState := SourceCoreCallableAncestryReadRecipes.State

abbrev Frame := SourceCoreCallablePairedFrames.Frame

/-- Two authenticated parent states and the actual metadata factories. -/
structure Recipe {checked : Checked} {base : Base checked} (inputs : Inputs base)
    (callerFrame lexicalFrame : Frame) (caller lexical : MetadataState) (id target : Core.Word) where
  callerHistory : CallableAncestryPairedLookup.Authenticates inputs callerFrame (some caller)
  lexicalHistory : CallableAncestryPairedLookup.Authenticates inputs lexicalFrame (some lexical)
  read : Read inputs caller id target
  readAccepted : prepareRead inputs caller id target = .ok read
  applied : Applied read lexical
  appliedAccepted : applyRead read lexical = .ok applied

namespace Recipe
variable {checked : Checked} {base : Base checked} {inputs : Inputs base}
  {callerFrame lexicalFrame : Frame} {caller lexical : MetadataState} {id target : Core.Word}

/-- A real completed view lookup supplies both factory receipts. -/
theorem of_view
    (callerHistory : CallableAncestryPairedLookup.Authenticates inputs callerFrame (some caller))
    (lexicalHistory : CallableAncestryPairedLookup.Authenticates inputs lexicalFrame (some lexical))
    {result : MetadataState}
    (accepted : SourceCoreCallableAncestryPairedPreparation.view? inputs caller lexical id target = some result) :
    ∃ recipe : Recipe inputs callerFrame lexicalFrame caller lexical id target,
      result = recipe.read.after lexical := by
  obtain ⟨read, applied, readAccepted, appliedAccepted, same⟩ :=
    CallableAncestryPairedValidation.view_receipts accepted
  exact ⟨⟨callerHistory, lexicalHistory, read, readAccepted, applied, appliedAccepted⟩, same⟩

variable (recipe : Recipe inputs callerFrame lexicalFrame caller lexical id target)

theorem view_accepted :
    SourceCoreCallableAncestryPairedPreparation.view? inputs caller lexical id target =
      some (recipe.read.after lexical) := by
  simp [SourceCoreCallableAncestryPairedPreparation.view?, recipe.readAccepted,
    recipe.appliedAccepted, Except.toOption]

theorem authenticated : CallableAncestryPairedLookup.Authenticates inputs
    (.appliedView id target callerFrame lexicalFrame) (some (recipe.read.after lexical)) :=
  .appliedView recipe.callerHistory recipe.lexicalHistory recipe.view_accepted

theorem full_source : (recipe.read.after lexical).metadata.source =
    SourceTypedRuntime.rewriteLocalRequirements recipe.read.witnesses
      (lexical.metadata.source.applySubstitution recipe.read.substitution) := rfl

theorem semantic_active : (recipe.read.after lexical).metadata.active =
    recipe.read.substitution.compose lexical.metadata.active := rfl

theorem native_active : (recipe.read.after lexical).nativeActive =
    recipe.read.entry.view.cumulative := rfl

theorem header : ExpressionForm.lambda
    (recipe.applied.parameters.map (TypedBinder.applySubstitution recipe.read.substitution))
    (recipe.read.substitution.apply recipe.applied.resultType) recipe.applied.body =
    recipe.read.template.node.form := recipe.applied.nativeHeader

theorem source_value (captured : SourceTypedRuntime.Environment)
    (evidence : SourceCompilationPlan.EvidenceEnvironment) :
    recipe.applied.sourceValue captured evidence =
      .instantiated recipe.read.substitution recipe.read.witnesses
        (.closure recipe.applied.parameters recipe.applied.resultType recipe.applied.body
          lexical.metadata.source lexical.metadata.owner captured evidence) := rfl

end Recipe

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β}
    {output : β} (accepted : (action >>= next) = .ok output) :
    ∃ input, action = .ok input ∧ next input = .ok output := by
  cases action with
  | error error => cases accepted
  | ok input => exact ⟨input, rfl, accepted⟩

private theorem mapError_ok {α ε δ : Type} {action : Except ε α} {f : ε → δ} {output : α}
    (accepted : action.mapError f = .ok output) : action = .ok output := by
  cases action <;> cases accepted <;> rfl

private theorem map_ok {α β ε : Type} {action : Except ε α} {f : α → β} {output : β}
    (accepted : action.map f = .ok output) : ∃ input, action = .ok input ∧ f input = output := by
  cases action with
  | error error => cases accepted
  | ok input => exact ⟨input, rfl, Except.ok.inj accepted⟩

private theorem exact_key {plan : SourceCompilationPlan.Plan} {key : SourceCompilationPlan.Key}
    {original : SourceSpecialization.SpecializedFunction}
    (accepted : SourceCompilationPlan.exactSpecialization plan key = .ok original) : original.key = key := by
  unfold SourceCompilationPlan.exactSpecialization at accepted
  split at accepted
  · cases accepted
  · next selected found =>
    cases accepted
    have member : original ∈ [original] := by simp
    rw [← found] at member
    exact of_decide_eq_true (List.mem_filter.mp member).2
  · cases accepted

private theorem exact_member {plan : SourceCompilationPlan.Plan} {key : SourceCompilationPlan.Key}
    {original candidate : SourceSpecialization.SpecializedFunction}
    (accepted : SourceCompilationPlan.exactSpecialization plan key = .ok original)
    (member : candidate ∈ plan.specializations) (same : candidate.key = key) : candidate = original := by
  unfold SourceCompilationPlan.exactSpecialization at accepted
  split at accepted
  · cases accepted
  · next selected found =>
    cases accepted
    have retained : candidate ∈ plan.specializations.filter (fun item => decide (item.key = key)) :=
      List.mem_filter.mpr ⟨member, by simpa using same⟩
    rw [found] at retained
    exact List.mem_singleton.mp retained
  · cases accepted

private theorem exactCaller_source {plan : SourceCompilationPlan.Plan}
    {binding : SourceCoreLocalPolymorphism.Binding} {original : SourceSpecialization.SpecializedFunction}
    (accepted : SourceCoreLocalEvidence.exactCaller plan binding = .ok original) :
    SourceCompilationPlan.exactSpecialization plan binding.caller = .ok original := by
  unfold SourceCoreLocalEvidence.exactCaller at accepted
  cases selected : SourceCompilationPlan.exactSpecialization plan binding.caller with
  | error error => simp [selected, Except.mapError, bind, Except.bind] at accepted
  | ok caller =>
    simp only [selected, Except.mapError, bind, Except.bind] at accepted
    split at accepted
    · cases accepted
    · split at accepted
      · cases accepted; rfl
      · cases accepted

private theorem prepared_canonical {program : CheckedProgram} {plan : SourceCompilationPlan.Plan}
    {candidate : SourceCoreLocalPolymorphism.Instance} {parent : Option SourceCoreLocalEvidence.Prepared}
    {prepared : SourceCoreLocalEvidence.Prepared}
    (accepted : SourceCoreLocalEvidence.prepare program plan candidate parent = .ok prepared) :
    ∃ original, SourceCompilationPlan.exactSpecialization plan prepared.caller.key = .ok original ∧
      prepared.source = original.function.typedBody.applySubstitution prepared.substitution := by
  unfold SourceCoreLocalEvidence.prepare at accepted
  obtain ⟨original, selected, accepted⟩ := bind_ok accepted
  have originalSelected := exactCaller_source selected
  have key := exact_key originalSelected
  simp only [bind, Except.bind, pure, Except.pure, Except.mapError] at accepted
  repeat' first | split at accepted | cases accepted
  all_goals exact ⟨original, by simpa only [SourceCoreLocalEvidence.contextualCaller, key] using originalSelected, rfl⟩

private theorem certified_source {program : CheckedProgram} {plan : SourceCompilationPlan.Plan}
    {candidates : List SourceCoreLocalPolymorphism.Instance} {parents : List SourceCoreLocalEvidence.Prepared}
    (accepted : SourceCoreStageCodebook.prepareContexts program plan candidates = .ok parents)
    (row : SourceCoreAllocationContexts.Certified plan parents)
    {original : SourceSpecialization.SpecializedFunction}
    (selected : SourceCompilationPlan.exactSpecialization plan row.context.owner = .ok original) :
    row.context.source = original.function.typedBody.applySubstitution row.context.active := by
  rw [row.sourceExact, row.activeExact]
  rw [row.ownerExact] at selected
  cases origin : row.origin with
  | root candidate member =>
    rw [origin] at selected
    have same := exact_member selected member rfl
    subst candidate
    simp only [SourceCoreAllocationContexts.Origin.source, SourceCoreAllocationContexts.Origin.active,
      EmptySourceSubstitution.source]
  | contextual prepared member =>
    rw [origin] at selected
    obtain ⟨candidate, parent, authentic⟩ := SourceCoreStageCodebook.prepareContexts_authentic accepted member
    obtain ⟨caller, found, source⟩ := prepared_canonical authentic
    cases Except.ok.inj (found.symm.trans selected)
    exact source


private theorem base_contexts {program : CheckedProgram} {plan : SourceCompilationPlan.Plan}
    {checked : Checked} {ownership : checked.signatures = program.signatures} {fuel : Nat}
    {base : Base checked}
    (accepted : SourceCoreCompatibleFunctions.prepareWithCatalog program plan checked ownership fuel = .ok base) :
    ∃ candidates, SourceCoreStageCodebook.prepareContexts base.sourceProgram base.plan candidates = .ok base.contexts := by
  unfold SourceCoreCompatibleFunctions.prepareWithCatalog at accepted
  obtain ⟨executable, _, accepted⟩ := bind_ok accepted
  obtain ⟨locals, _, accepted⟩ := bind_ok accepted
  obtain ⟨contexts, prepared, accepted⟩ := bind_ok accepted
  have prepared := mapError_ok prepared
  obtain ⟨functions, _, accepted⟩ := bind_ok accepted
  split at accepted
  · cases accepted
    exact ⟨_, prepared⟩
  · obtain ⟨diagnostics, _, accepted⟩ := bind_ok accepted
    split at accepted
    · obtain ⟨table, _, accepted⟩ := bind_ok accepted
      obtain ⟨callableDiagnostics, _, accepted⟩ := bind_ok accepted
      simp only [bind, Except.bind, pure, Except.pure] at accepted
      obtain ⟨locals, _, accepted⟩ := bind_ok accepted
      obtain ⟨closures, _, accepted⟩ := bind_ok accepted
      obtain ⟨sourceInputs, _, accepted⟩ := bind_ok accepted
      obtain ⟨entries, _, accepted⟩ := bind_ok accepted
      cases accepted
      exact ⟨_, prepared⟩
    · simp only [bind, Except.bind, pure, Except.pure] at accepted
      obtain ⟨closures, _, accepted⟩ := bind_ok accepted
      obtain ⟨sourceInputs, _, accepted⟩ := bind_ok accepted
      obtain ⟨entries, _, accepted⟩ := bind_ok accepted
      cases accepted
      exact ⟨_, prepared⟩

private theorem mapM_member {α β ε : Type} {f : α → Except ε β} {items : List α} {output : List β}
    (accepted : items.mapM f = .ok output) {value : β} (member : value ∈ output) :
    ∃ item, item ∈ items ∧ f item = .ok value := by
  induction items generalizing output with
  | nil => cases accepted; cases member
  | cons item items ih =>
    simp only [List.mapM_cons, bind, Except.bind, pure, Except.pure] at accepted
    cases first : f item with
    | error error => simp [first] at accepted
    | ok head =>
      simp only [first] at accepted
      cases rest : items.mapM f with
      | error error => simp [rest] at accepted
      | ok tail =>
        simp only [rest, Except.ok.injEq] at accepted
        subst output
        rcases List.mem_cons.mp member with rfl | member
        · exact ⟨item, List.mem_cons_self, first⟩
        · obtain ⟨child, member, selected⟩ := ih rest member
          exact ⟨child, List.mem_cons_of_mem item member, selected⟩

private theorem allocation_inventory {ambient : Core.DataEnvironment}
    {inventories : List SourceCoreAllocationCodebook.ContextInventory} {first : Nat}
    {prepared : SourceCoreAllocationCodebook.Prepared}
    (accepted : SourceCoreAllocationCodebook.prepare ambient inventories first = .ok prepared)
    {context : SourceCoreAllocationCodebook.IndexedContext} (member : context ∈ prepared.contexts) :
    context.inventory ∈ inventories := by
  unfold SourceCoreAllocationCodebook.prepare at accepted
  split at accepted
  · obtain ⟨_, _, accepted⟩ := bind_ok accepted
    split at accepted
    · obtain ⟨contexts, mapped, accepted⟩ := bind_ok accepted
      split at accepted
      · cases accepted
        obtain ⟨⟨inventory, index⟩, selected, compiled⟩ := mapM_member mapped member
        obtain ⟨key, _, compiled⟩ := bind_ok compiled
        obtain ⟨bindings, _, compiled⟩ := bind_ok compiled
        cases compiled
        exact List.fst_mem_of_mem_zipIdx selected
      · split at accepted
        · cases accepted
        · split at accepted <;> cases accepted
    · cases accepted
  · cases accepted

private theorem discovered_source {program : CheckedProgram} {plan : SourceCompilationPlan.Plan}
    {candidates : List SourceCoreLocalPolymorphism.Instance} {parents : List SourceCoreLocalEvidence.Prepared}
    (accepted : SourceCoreStageCodebook.prepareContexts program plan candidates = .ok parents)
    (rows : SourceCoreAllocationContexts.Inventory plan parents)
    {ambient : Core.DataEnvironment} {discovered : SourceCoreAllocationDiscovery.Prepared}
    (prepared : SourceCoreAllocationDiscovery.prepare ambient rows.contexts = .ok discovered)
    {owner : SourceCompilationPlan.Key} {active : TypeSystem.Substitution}
    {context : SourceCoreAllocationCodebook.IndexedContext}
    (found : discovered.metadata.contextAt? owner active = some context)
    {original : SourceSpecialization.SpecializedFunction}
    (selected : SourceCompilationPlan.exactSpecialization plan owner = .ok original) :
    context.inventory.source = original.function.typedBody.applySubstitution active := by
  obtain ⟨metadata, compiled, same⟩ := map_ok prepared
  cases same
  have member := allocation_inventory compiled (List.mem_of_find?_eq_some found)
  obtain ⟨row, rowMember, same⟩ := List.mem_map.mp member
  unfold SourceCoreAllocationCodebook.Prepared.contextAt? at found
  have fields := of_decide_eq_true (List.find?_some (p := fun candidate : SourceCoreAllocationCodebook.IndexedContext => decide (candidate.inventory.owner = owner ∧ candidate.inventory.active = active)) found)
  obtain ⟨certified, _, rfl⟩ := List.mem_map.mp rowMember
  rw [← same] at fields ⊢
  have fields : certified.context.owner = owner ∧ certified.context.active = active := fields
  rw [← fields.2]
  exact certified_source accepted certified (by rw [fields.1]; exact selected)


private theorem forIn_invariant {α β ε : Type} {items : List α} {initial final : β}
    {step : α → β → Except ε (ForInStep β)} {invariant : β → Prop}
    (accepted : forIn items initial step = .ok final) (start : invariant initial)
    (each : ∀ item, item ∈ items → ∀ state outcome, invariant state → step item state = .ok outcome →
      ∃ updated, outcome = .yield updated ∧ invariant updated) : invariant final := by
  induction items generalizing initial with
  | nil =>
    simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] at accepted
    exact accepted ▸ start
  | cons item items ih =>
    rw [List.forIn_cons] at accepted
    obtain ⟨outcome, ran, accepted⟩ := bind_ok accepted
    obtain ⟨updated, rfl, preserved⟩ := each item List.mem_cons_self initial outcome start ran
    exact ih accepted preserved (fun next member => each next (List.mem_cons_of_mem item member))

private def TemplateSource {checked : Checked} (base : Base checked)
    (template : SourceCoreLambdaTemplates.Lambda) : Prop :=
  ∃ original, SourceCompilationPlan.exactSpecialization base.plan template.owner = .ok original ∧
    original.function.typedBody.lookupExpression? template.id = some template.original ∧
    template.node = template.original.applySubstitution template.active

private theorem template_source {checked : Checked} {base : Base checked}
    {candidates : List SourceCoreLocalPolymorphism.Instance}
    (contexts : SourceCoreStageCodebook.prepareContexts base.sourceProgram base.plan candidates = .ok base.contexts)
    {inventory : SourceCoreLambdaTemplates.Inventory checked}
    (accepted : SourceCoreLambdaTemplates.prepare base = .ok inventory)
    {template : SourceCoreLambdaTemplates.Lambda} (member : template ∈ inventory.lambdas) :
    TemplateSource base template := by
  unfold SourceCoreLambdaTemplates.prepare at accepted
  obtain ⟨receipts, _, accepted⟩ := bind_ok accepted
  obtain ⟨metadata, compiled, accepted⟩ := bind_ok accepted
  have compiled := mapError_ok compiled
  split at accepted
  · next callable callableFound =>
    simp only [bind, Except.bind, pure, Except.pure] at accepted
    obtain ⟨lambdas, loop, accepted⟩ := bind_ok accepted
    cases accepted
    have invariant : ∀ value ∈ lambdas, TemplateSource base value := by
      apply forIn_invariant (invariant := fun values => ∀ value ∈ values, TemplateSource base value) loop
      · intro value member; cases member
      · intro entry _ state outcome previous iteration
        cases origin : entry.origin with
        | named key =>
          simp only [origin] at iteration
          cases iteration
          exact ⟨state, rfl, previous⟩
        | builtin function =>
          simp only [origin] at iteration
          cases iteration
          exact ⟨state, rfl, previous⟩
        | lambda owner id active =>
          simp only [origin] at iteration
          split at iteration
          · next context found =>
            try simp only [bind, Except.bind, pure, Except.pure] at iteration
            obtain ⟨original, selected, iteration⟩ := bind_ok iteration
            have selected := mapError_ok selected
            split at iteration
            · next originalNode originalFound =>
              try simp only [bind, Except.bind, pure, Except.pure] at iteration
              split at iteration
              · next node nodeFound =>
                try simp only [bind, Except.bind, pure, Except.pure] at iteration
                split at iteration
                · obtain ⟨parameterType, _, iteration⟩ := bind_ok iteration
                  obtain ⟨resultType, _, iteration⟩ := bind_ok iteration
                  cases iteration
                  refine ⟨_, rfl, ?_⟩
                  intro value member
                  rcases List.mem_append.mp member with old | fresh
                  · exact previous value old
                  · cases List.mem_singleton.mp fresh
                    refine ⟨original, selected, originalFound, ?_⟩
                    have source := discovered_source contexts receipts compiled found selected
                    have substituted := Frontend.SourceTypedRuntime.TypedSource.lookupExpression?_applySubstitution
                      original.function.typedBody active id originalNode originalFound
                    rw [source] at nodeFound
                    exact Option.some.inj (nodeFound.symm.trans substituted)
                · cases iteration
              · cases iteration
            · cases iteration
          · cases iteration
    exact invariant template member
  · cases accepted


private theorem sidecar_lookup {plan : SourceCompilationPlan.Plan} {key : SourceCompilationPlan.Key}
    {sidecar : SourceCoreStageContracts.Sidecar}
    (accepted : SourceCoreStageContracts.prepareSidecar plan key = .ok sidecar) :
    SourceCompilationPlan.exactSpecialization plan key = .ok sidecar.caller := by
  unfold SourceCoreStageContracts.prepareSidecar at accepted
  cases selected : SourceCompilationPlan.exactSpecialization plan key with
  | error error => simp [selected, Except.mapError, bind, Except.bind] at accepted
  | ok caller =>
    simp only [selected, Except.mapError, bind, Except.bind] at accepted
    cases valid : SourceCompilationPlan.validateSpecializationMetadataWith true caller with
    | error error => simp [valid, Functor.discard, Functor.mapConst, Except.map] at accepted
    | ok value =>
      simp only [valid] at accepted
      dsimp [Functor.discard, Functor.mapConst, Except.map] at accepted
      split at accepted
      · cases accepted
      · split at accepted
        · cases accepted; rfl
        · cases accepted

private def HeaderShape (node : ExpressionNode) (contract : SourceCoreStageContracts.Contract) : Prop :=
  ∃ parameters result body, node.form = .lambda parameters result body ∧
    contract.parameters = parameters ∧ contract.stagedResult = SourceCompilationPlan.sourceTypeIsComptimeOnly result

private theorem contract_header {plan : SourceCompilationPlan.Plan} {owner : SourceCompilationPlan.Key}
    {id : ExpressionId} {active : TypeSystem.Substitution} {arity : Nat}
    {attached : Option SourceCoreStageContracts.Contract}
    (authenticated : CallEntryCertificates.OriginContract plan (.lambda owner id active) arity attached)
    {original : SourceSpecialization.SpecializedFunction} {node : ExpressionNode}
    (selected : SourceCompilationPlan.exactSpecialization plan owner = .ok original)
    (found : original.function.typedBody.lookupExpression? id = some node) :
    ∃ contract, attached = some contract ∧ HeaderShape (node.applySubstitution active) contract := by
  cases authenticated with
  | originalLambda prepared accepted =>
    obtain ⟨receipt⟩ := CallContractCertificates.lambda_of_accepted accepted
    have same := Except.ok.inj (selected.symm.trans (sidecar_lookup prepared))
    subst original
    have nodeEq := CallContractCertificates.expression_unique receipt.selected (lookupExpression?_sound found)
    subst node
    exact ⟨_, rfl, receipt.parameters, receipt.result, receipt.body,
      by simpa only [EmptySourceSubstitution.expression] using receipt.form,
      receipt.parameters_eq, receipt.stagedResult⟩
  | contextualLambda prepared accepted =>
    obtain ⟨receipt⟩ := CallContractCertificates.contextualLambda_of_accepted accepted
    have same := Except.ok.inj (selected.symm.trans (sidecar_lookup prepared))
    subst original
    have nodeEq := CallContractCertificates.expression_unique receipt.selected (lookupExpression?_sound found)
    subst node
    refine ⟨_, rfl, _, _, receipt.body, ?_, receipt.parameters_eq, receipt.stagedResult⟩
    simp only [ExpressionNode.applySubstitution, receipt.form, ExpressionForm.applySubstitution]

/-- The source header is authenticated by both actual preparations. Its form
comes from the same selected template, while the contract comes from the full
original codebook factory. -/
structure CanonicalHeader {checked : Checked} {base : Base checked} (inputs : Inputs base)
    (template : SourceCoreLambdaTemplates.Lambda) (contract : SourceCoreStageContracts.Contract) : Prop where
  basePrepared : ∃ (program : CheckedProgram) (plan : SourceCompilationPlan.Plan)
    (ownership : checked.signatures = program.signatures) (fuel : Nat),
    SourceCoreCompatibleFunctions.prepareWithCatalog program plan checked ownership fuel = .ok base
  tablePrepared : ∃ (project : TypeSystem.Ty → Except SourceCoreLocalPolymorphism.Error Core.Ty)
    (limits : SourceCoreStageCodebook.Limits) (firstId : Nat),
    SourceCoreStageCodebook.prepareWithProjection base.sourceProgram base.plan project limits firstId = .ok inputs.callable.table
  shape : ∃ parameters result body, template.node.form = .lambda parameters result body ∧
    contract.parameters = parameters ∧ contract.stagedResult = SourceCompilationPlan.sourceTypeIsComptimeOnly result

/-- Factory success connects an actual read target to its canonical contract.
No private template constructor or native header check establishes provenance. -/
theorem header_of_prepared {program : CheckedProgram} {plan : SourceCompilationPlan.Plan}
    {checked : Checked} {ownership : checked.signatures = program.signatures} {fuel : Nat}
    {base : Base checked} {inputs : Inputs base}
    (accepted : SourceCoreCompatibleFunctions.prepareWithCatalog program plan checked ownership fuel = .ok base)
    {project : TypeSystem.Ty → Except SourceCoreLocalPolymorphism.Error Core.Ty}
    {limits : SourceCoreStageCodebook.Limits} {firstId : Nat}
    (table : SourceCoreStageCodebook.prepareWithProjection base.sourceProgram base.plan project limits firstId = .ok inputs.callable.table)
    {caller : MetadataState} {id target : Core.Word} (read : Read inputs caller id target) :
    ∃ contract, read.descriptor.contract = some contract ∧ CanonicalHeader inputs read.template contract := by
  obtain ⟨candidates, contexts⟩ := base_contexts accepted
  obtain ⟨original, selected, found, nodeEq⟩ := template_source contexts inputs.templatesPrepared
    (List.mem_of_find?_eq_some read.targetSelected)
  have authenticated := CallEntryCertificates.prepareWithProjection_authenticates table
    read.descriptor (List.mem_of_find?_eq_some read.descriptorSelected)
  unfold CallEntryCertificates.Authenticated at authenticated
  rw [read.templateOrigin] at authenticated
  obtain ⟨contract, attached, shape⟩ := contract_header authenticated selected found
  rw [← nodeEq] at shape
  exact ⟨contract, attached, ⟨⟨program, plan, ownership, fuel, accepted⟩,
    ⟨project, limits, firstId, table⟩, shape⟩⟩


namespace Recipe
variable {checked : Checked} {base : Base checked} {inputs : Inputs base}
  {callerFrame lexicalFrame : Frame} {caller lexical : MetadataState} {id target : Core.Word}
  (recipe : Recipe inputs callerFrame lexicalFrame caller lexical id target)
  {contract : SourceCoreStageContracts.Contract} (canonical : CanonicalHeader inputs recipe.read.template contract)

include canonical in
theorem contract_parameters : contract.parameters =
    recipe.applied.parameters.map (TypedBinder.applySubstitution recipe.read.substitution) := by
  obtain ⟨parameters, result, body, form, same, _⟩ := canonical.shape
  exact same.trans (ExpressionForm.lambda.inj (recipe.header.trans form)).1.symm

include canonical in
theorem contract_result : contract.stagedResult =
    SourceCompilationPlan.sourceTypeIsComptimeOnly (recipe.read.substitution.apply recipe.applied.resultType) := by
  obtain ⟨parameters, result, body, form, _, same⟩ := canonical.shape
  rw [(ExpressionForm.lambda.inj (recipe.header.trans form)).2.1]
  exact same


/-- The real recipe selects the pointwise rewritten original node, including
all of its requirement rows; the lambda header itself is not rewritten. -/
theorem source_node :
    (recipe.read.after lexical).metadata.source.lookupExpression? recipe.read.entry.view.principal.initializer =
      some (SourceTypedRuntime.rewriteExpressionLocalRequirements recipe.read.witnesses
        (recipe.applied.node.applySubstitution recipe.read.substitution)) :=
  SourceTypedRuntime.TypedSource.lookupExpression?_rewriteLocalRequirements _ _ _ _
    (SourceTypedRuntime.TypedSource.lookupExpression?_applySubstitution _ _ _ _ recipe.applied.found)

theorem source_node_form :
    (SourceTypedRuntime.rewriteExpressionLocalRequirements recipe.read.witnesses
      (recipe.applied.node.applySubstitution recipe.read.substitution)).form =
      .lambda (recipe.applied.parameters.map (TypedBinder.applySubstitution recipe.read.substitution))
        (recipe.read.substitution.apply recipe.applied.resultType) recipe.applied.body := by
  simp only [SourceTypedRuntime.rewriteExpressionLocalRequirements,
    ExpressionNode.applySubstitution, recipe.applied.shape, ExpressionForm.applySubstitution]

end Recipe

end Solcore.SourceSemantics.CoreLowering.CallableAppliedViewProvenance
