import Lean
import Solcore.SourceSemantics.CoreLowering.CallableAncestryComposition
import Solcore.Frontend.SourceCoreLocalPolymorphism

/-! Actual local-read discovery gives closed replacement ranges for every
prepared candidate. Preparation and callable decoration preserve this fact. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.PreparedLocalInstanceClosure
open Frontend SourceInference TypeSystem SourceCoreLocalPolymorphism
open CallableAncestryProfiles.SourceComposition

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

private def unfoldAction (hypothesis : Lean.Name) : Lean.Elab.Tactic.TacticM Unit :=
  Lean.Elab.Tactic.withMainContext do
    let some declaration := (← Lean.getLCtx).findFromUserName? hypothesis
      | throwError "missing accepted action"
    let type ← Lean.instantiateMVars (← Lean.Meta.inferType declaration.toExpr)
    let some (_, left, _) := type.eq? | throwError "expected equality"
    let .const action _ := left.getAppFn | throwError "expected compiler action"
    let goal ← Lean.Elab.Tactic.getMainGoal
    let updated ← Lean.Meta.unfoldLocalDecl goal declaration.fvarId action
    Lean.Elab.Tactic.replaceMainGoal [updated]

theorem read_origin_closed {source : TypedSource}
    {localInstance : SourceSpecializationWorklist.LocalLambdaInstance}
    (origin : SourceSpecializationWorklist.LocalLambdaInstance.ReadOrigin source localInstance) :
    RangesClosed localInstance.substitution := by
  induction origin with
  | root expression present name form matched => exact matchClosed_ranges matched
  | contextual previous expression present name form child matched cumulative ih =>
      rw [cumulative]
      exact RangesClosed.compose ih (matchClosed_ranges matched)

theorem catalog_entries_closed {plan : SourceSpecializationWorklist.Plan}
    {contextFuel : Option Nat} {entries : List SourceCompilationPlan.LocalLambdaCatalogEntry}
    (accepted : SourceCompilationPlan.localLambdaCatalog plan contextFuel = .ok entries) :
    ∀ entry ∈ entries, RangesClosed entry.substitution := by
  unfold SourceCompilationPlan.localLambdaCatalog at accepted
  obtain ⟨done, _, accepted⟩ := bind_ok accepted
  cases done
  obtain ⟨result, assembled, accepted⟩ := bind_ok accepted
  cases accepted
  apply forIn_invariant assembled (by simp)
  intro row _ before outcome previous iteration
  obtain ⟨instances, discovered, iteration⟩ := bind_ok iteration
  obtain ⟨after, appended, iteration⟩ := bind_ok iteration
  cases iteration
  refine ⟨after, rfl, ?_⟩
  apply forIn_invariant appended previous
  intro localInstance present current outcome previous step
  obtain ⟨nodes, _, step⟩ := bind_ok step
  cases step
  refine ⟨_, rfl, ?_⟩
  intro entry occurs
  rcases List.mem_append.mp occurs with old | new
  · exact previous entry old
  · cases List.mem_singleton.mp new
    exact read_origin_closed
      (SourceSpecializationWorklist.localLambdaInstances_read_origin discovered localInstance present)

def CatalogClosed (catalog : Catalog) : Prop :=
  ∀ binding ∈ catalog.bindings, ∀ candidate ∈ binding.instances,
    RangesClosed candidate.origin.substitution

theorem of_preparation {project : Ty → Except SourceCoreLocalPolymorphism.Error Core.Ty}
    {plan : SourceSpecializationWorklist.Plan} {contextFuel : Option Nat} {catalog : Catalog}
    (accepted : prepareWithProjection project plan contextFuel = .ok catalog) :
    CatalogClosed catalog := by
  unfold prepareWithProjection at accepted
  obtain ⟨entries, discovered, accepted⟩ := bind_ok accepted
  have closedEntries : ∀ entry ∈ entries, RangesClosed entry.substitution := by
    apply catalog_entries_closed
    cases actual : SourceCompilationPlan.localLambdaCatalog plan contextFuel with
    | error error => simp [actual, Except.mapError] at discovered
    | ok values =>
        have same : values = entries := by simpa only [actual, Except.mapError, Except.ok.injEq] using discovered
        exact congrArg Except.ok same
  obtain ⟨instances, instantiated, accepted⟩ := bind_ok accepted
  have valid : ∀ candidate ∈ instances, RangesClosed candidate.origin.substitution := by
    refine mapM_property (property := fun candidate => RangesClosed candidate.origin.substitution) instantiated ?_
    intro entry member candidate actual
    run_tac unfoldAction `actual
    simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at actual
    iterate 8 split at actual <;> try contradiction
    obtain ⟨parameterType, _, actual⟩ := bind_ok actual
    obtain ⟨resultType, _, actual⟩ := bind_ok actual
    cases actual
    exact closedEntries entry member
  obtain ⟨bindings, assembled, accepted⟩ := bind_ok accepted
  cases accepted
  change ∀ binding ∈ bindings, ∀ candidate ∈ binding.instances, RangesClosed candidate.origin.substitution
  apply forIn_invariant assembled (by simp)
  intro specialized _ before outcome previous iteration
  try dsimp only at iteration
  split at iteration
  · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at iteration
  · obtain ⟨after, nodes, iteration⟩ := bind_ok iteration
    cases iteration
    refine ⟨after, rfl, ?_⟩
    apply forIn_invariant nodes previous
    intro node _ current outcome previous step
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
            intro binding member candidate memberCandidate
            rcases List.mem_append.mp member with old | new
            · exact previous binding old candidate memberCandidate
            · cases List.mem_singleton.mp new
              exact valid candidate (List.mem_filter.mp memberCandidate).1
          · cases step
            exact ⟨current, rfl, previous⟩
    · cases step
      exact ⟨current, rfl, previous⟩

theorem with_contracts {catalog assigned : Catalog}
    {idAt : Key → ExpressionId → Substitution → Option Core.Word}
    (valid : CatalogClosed catalog)
    (accepted : catalog.withCallableContracts idAt = .ok assigned) :
    CatalogClosed assigned := by
  unfold Catalog.withCallableContracts at accepted
  obtain ⟨bindings, prepared, accepted⟩ := bind_ok accepted
  cases accepted
  refine mapM_property (property := fun binding => ∀ candidate ∈ binding.instances,
    RangesClosed candidate.origin.substitution) prepared ?_
  intro binding member updated actual
  obtain ⟨instances, preparedInstances, actual⟩ := bind_ok actual
  cases actual
  refine mapM_property (property := fun candidate => RangesClosed candidate.origin.substitution) preparedInstances ?_
  intro candidate present decorated actual
  try dsimp only at actual
  split at actual <;> try contradiction
  cases actual
  exact valid binding member candidate present

theorem at_context {catalog : Catalog} {caller : Key} {binder : Resolved.LocalId}
    {binding : Binding} {active : Substitution} {candidate : Instance}
    (closed : CatalogClosed catalog)
    (located : catalog.binding caller binder = .ok binding)
    (member : candidate ∈ binding.atContext active) : RangesClosed candidate.origin.substitution := by
  have instanceMember := (List.mem_filter.mp member).1
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
      exact closed binding selected.1 candidate instanceMember

end Solcore.SourceSemantics.CoreLowering.PreparedLocalInstanceClosure
