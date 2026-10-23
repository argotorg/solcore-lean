import Solcore.Frontend.SourceCoreLocalPolymorphism

/-! Every native catalog binding retains its exact source declaration, even when
its instance bundle is empty. The witness comes from the actual preparation fold. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.PreparedLocalBindingOrigins
open Frontend SourceInference TypeSystem SourceCoreLocalPolymorphism

private theorem bind_ok {α β ε : Type} {action : Except ε α}
    {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) :
    ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem forIn_invariant {α β ε : Type} {items : List α} {initial final : β}
    {step : α → β → Except ε (ForInStep β)} {invariant : β → Prop}
    (accepted : forIn items initial step = .ok final) (start : invariant initial)
    (each : ∀ item ∈ items, ∀ state outcome, invariant state →
      step item state = .ok outcome → ∃ updated, outcome = .yield updated ∧ invariant updated) :
    invariant final := by
  induction items generalizing initial with
  | nil =>
    simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] at accepted
    exact accepted ▸ start
  | cons item rest ih =>
    rw [List.forIn_cons] at accepted
    obtain ⟨outcome, ran, accepted⟩ := bind_ok accepted
    obtain ⟨updated, rfl, preserved⟩ := each item List.mem_cons_self initial outcome start ran
    exact ih accepted preserved (fun next member => each next (List.mem_cons_of_mem item member))

private theorem mapM_property {α β ε : Type} {items : List α} {values : List β}
    {action : α → Except ε β} {property : β → Prop}
    (accepted : items.mapM action = .ok values)
    (each : ∀ item ∈ items, ∀ value, action item = .ok value → property value) :
    ∀ value ∈ values, property value := by
  induction items generalizing values with
  | nil =>
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at accepted
    subst values
    simp
  | cons item rest ih =>
    rw [List.mapM_cons] at accepted
    obtain ⟨head, first, accepted⟩ := bind_ok accepted
    obtain ⟨tail, later, accepted⟩ := bind_ok accepted
    cases accepted
    intro value member
    rcases List.mem_cons.mp member with rfl | member
    · exact each item List.mem_cons_self _ first
    · exact ih later (fun next present => each next (List.mem_cons_of_mem item present)) value member

private theorem binding_mem {source : TypedSource} {statement : StatementNode}
    {binder : TypedBinder} {initializer : ExpressionId}
    (member : Node.statement statement ∈ source.nodes)
    (form : statement.form = .letDecl binder (some initializer))
    (quantified : binder.scheme.quantified.isEmpty = false)
    (direct : SourceSpecialization.isDirectLambdaInitializer source initializer = true) :
    ({ binder, initializer } : SourceSpecializationWorklist.LocalLambdaBinding) ∈
      SourceSpecializationWorklist.localLambdaBindings source := by
  change _ ∈ source.nodes.filterMap _
  apply List.mem_filterMap.mpr
  refine ⟨.statement statement, member, ?_⟩
  cases statement
  simp_all

def BindingOrigin (plan : SourceSpecializationWorklist.Plan) (binding : Binding) : Prop :=
  ∃ row ∈ plan.specializations,
    binding.caller = row.key ∧ binding.source = row.function.typedBody ∧
      ({ binder := binding.binder, initializer := binding.initializer } :
        SourceSpecializationWorklist.LocalLambdaBinding) ∈
          SourceSpecializationWorklist.localLambdaBindings binding.source

def CatalogOrigins (plan : SourceSpecializationWorklist.Plan) (catalog : Catalog) : Prop :=
  ∀ binding ∈ catalog.bindings, BindingOrigin plan binding

theorem of_preparation {project : Ty → Except SourceCoreLocalPolymorphism.Error Core.Ty}
    {plan : SourceSpecializationWorklist.Plan} {contextFuel : Option Nat} {catalog : Catalog}
    (accepted : prepareWithProjection project plan contextFuel = .ok catalog) :
    CatalogOrigins plan catalog := by
  unfold prepareWithProjection at accepted
  obtain ⟨entries, _, accepted⟩ := bind_ok accepted
  obtain ⟨instances, _, accepted⟩ := bind_ok accepted
  obtain ⟨bindings, assembled, accepted⟩ := bind_ok accepted
  cases accepted
  change ∀ binding ∈ bindings, BindingOrigin plan binding
  apply forIn_invariant assembled (by simp)
  intro row rowMember before outcome previous iteration
  try dsimp only at iteration
  split at iteration
  · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at iteration
  · obtain ⟨after, nodes, iteration⟩ := bind_ok iteration
    cases iteration
    refine ⟨after, rfl, ?_⟩
    apply forIn_invariant nodes previous
    intro node nodeMember current outcome previous step
    try dsimp only at step
    split at step
    · split at step
      · cases step
        exact ⟨current, rfl, previous⟩
      · split at step
        · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at step
        · split at step
          · cases step
            refine ⟨_, rfl, ?_⟩
            intro binding member
            rcases List.mem_append.mp member with old | added
            · exact previous binding old
            · cases List.mem_singleton.mp added
              have collected := binding_mem nodeMember (by rfl) (by simp_all) (by assumption)
              exact ⟨row, rowMember, rfl, rfl, collected⟩
          · cases step
            exact ⟨current, rfl, previous⟩
    · cases step
      exact ⟨current, rfl, previous⟩

theorem with_contracts {plan : SourceSpecializationWorklist.Plan} {catalog assigned : Catalog}
    {idAt : Key → ExpressionId → Substitution → Option Core.Word}
    (origins : CatalogOrigins plan catalog)
    (accepted : catalog.withCallableContracts idAt = .ok assigned) :
    CatalogOrigins plan assigned := by
  unfold Catalog.withCallableContracts at accepted
  obtain ⟨bindings, prepared, accepted⟩ := bind_ok accepted
  cases accepted
  refine mapM_property (property := BindingOrigin plan) prepared ?_
  intro binding member updated actual
  obtain ⟨instances, _, actual⟩ := bind_ok actual
  cases actual
  exact origins binding member

theorem at_binding {plan : SourceSpecializationWorklist.Plan} {catalog : Catalog}
    {caller : Key} {binder : Resolved.LocalId} {binding : Binding}
    (origins : CatalogOrigins plan catalog)
    (located : catalog.binding caller binder = .ok binding) :
    BindingOrigin plan binding ∧ binding.caller = caller ∧ binding.binder.id = binder := by
  unfold Catalog.binding at located
  generalize filtered : catalog.bindings.filter
    (fun entry => decide (entry.caller = caller ∧ entry.binder.id = binder)) = entries at located
  cases entries with
  | nil => cases located
  | cons entry rest =>
    cases rest with
    | cons next tail => cases located
    | nil =>
      cases located
      have selected := List.mem_filter.mp (show binding ∈ catalog.bindings.filter
        (fun entry => decide (entry.caller = caller ∧ entry.binder.id = binder)) from by
          rw [filtered]
          simp)
      exact ⟨origins binding selected.1, of_decide_eq_true selected.2⟩

theorem BindingOrigin.statement {plan : SourceSpecializationWorklist.Plan} {binding : Binding}
    (origin : BindingOrigin plan binding) :
    ∃ statement, Node.statement statement ∈ binding.source.nodes ∧
      statement.form = .letDecl binding.binder (some binding.initializer) := by
  obtain ⟨_, _, _, _, member⟩ := origin
  exact SourceSpecializationWorklist.localLambdaBindings_statement_origin member

end Solcore.SourceSemantics.CoreLowering.PreparedLocalBindingOrigins
