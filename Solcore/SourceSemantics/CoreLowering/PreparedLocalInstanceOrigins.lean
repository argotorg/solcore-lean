import Lean
import Solcore.Frontend.SourceCoreLocalPolymorphism

/-! Actual catalog generation identifies a contextual candidate with the
complete source binding that owns its bundle. Matching a local ID alone is
insufficient; the worklist's unique binding selection supplies the other fields. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.PreparedLocalInstanceOrigins
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

private theorem checked_none {duplicate : Option (Key × Nat)}
    (accepted : (match duplicate with
      | none => Except.ok ()
      | some (key, count) => Except.error
        (SourceSpecializationWorklist.Error.duplicatePlanSpecializations key count)) = .ok ()) :
    duplicate = none := by
  cases duplicate with
  | none => rfl
  | some value => rcases value with ⟨key, count⟩; cases accepted

private theorem unique_keys {plan : SourceSpecializationWorklist.Plan}
    (accepted : SourceSpecializationWorklist.validatePlanSpecializationsUnique plan = .ok ()) :
    (plan.specializations.map (·.key)).Nodup := by
  rcases plan with ⟨seeds, entries, calls, references⟩
  induction entries with
  | nil => exact .nil
  | cons head rest ih =>
    unfold SourceSpecializationWorklist.validatePlanSpecializationsUnique at accepted
    have noDuplicate := checked_none accepted
    change (if (rest.filter (fun entry => decide (entry.key = head.key))).isEmpty then _
      else some (head.key, (rest.filter (fun entry => decide (entry.key = head.key))).length + 1)) = none at noDuplicate
    split at noDuplicate
    · have absent : head.key ∉ rest.map (·.key) := by
        have empty : rest.filter (fun entry => decide (entry.key = head.key)) = [] :=
          List.isEmpty_iff.mp ‹_ = true›
        intro member
        obtain ⟨entry, member, same⟩ := List.mem_map.mp member
        have : entry ∈ rest.filter (fun entry => decide (entry.key = head.key)) :=
          List.mem_filter.mpr ⟨member, by simpa only [decide_eq_true_eq] using same⟩
        rw [empty] at this
        cases this
      have tailAccepted : SourceSpecializationWorklist.validatePlanSpecializationsUnique
          ⟨seeds, rest, calls, references⟩ = .ok () := by
        unfold SourceSpecializationWorklist.validatePlanSpecializationsUnique
        rw [noDuplicate]
        rfl
      exact List.nodup_cons.mpr ⟨absent, ih tailAccepted⟩
    · cases noDuplicate

private theorem same_key {rows : List SourceSpecialization.SpecializedFunction}
    (unique : (rows.map (·.key)).Nodup)
    {left right : SourceSpecialization.SpecializedFunction}
    (leftMember : left ∈ rows) (rightMember : right ∈ rows) (same : left.key = right.key) :
    left = right := by
  induction rows with
  | nil => cases leftMember
  | cons head tail ih =>
    obtain ⟨absent, unique⟩ := List.nodup_cons.mp unique
    rcases List.mem_cons.mp leftMember with rfl | leftTail
    · rcases List.mem_cons.mp rightMember with rfl | rightTail
      · rfl
      · exact False.elim (absent (List.mem_map.mpr ⟨right, rightTail, same.symm⟩))
    · rcases List.mem_cons.mp rightMember with rfl | rightTail
      · exact False.elim (absent (List.mem_map.mpr ⟨left, leftTail, same⟩))
      · exact ih unique leftTail rightTail

def CatalogEntryOrigin (plan : SourceSpecializationWorklist.Plan)
    (entry : SourceCompilationPlan.LocalLambdaCatalogEntry) : Prop :=
  ∃ row ∈ plan.specializations,
    entry.caller = row.key ∧ entry.source = row.function.typedBody ∧
    SourceSpecializationWorklist.LocalLambdaBinding.Selected
      (SourceSpecializationWorklist.localLambdaBindings entry.source) entry.localInstance.binding

theorem catalog_entry_origins {plan : SourceSpecializationWorklist.Plan}
    {contextFuel : Option Nat} {entries : List SourceCompilationPlan.LocalLambdaCatalogEntry}
    (accepted : SourceCompilationPlan.localLambdaCatalog plan contextFuel = .ok entries) :
    (plan.specializations.map (·.key)).Nodup ∧
      ∀ entry ∈ entries, CatalogEntryOrigin plan entry := by
  unfold SourceCompilationPlan.localLambdaCatalog at accepted
  obtain ⟨done, validated, accepted⟩ := bind_ok accepted
  cases done
  obtain ⟨result, assembled, accepted⟩ := bind_ok accepted
  cases accepted
  refine ⟨unique_keys validated, ?_⟩
  apply forIn_invariant assembled (by simp)
  intro row rowMember before outcome previous iteration
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
    exact ⟨row, rowMember, rfl, rfl,
      SourceSpecializationWorklist.localLambdaInstances_selected discovered localInstance present⟩

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

def BindingOrigins (binding : Binding) : Prop :=
  ∀ candidate ∈ binding.instances,
    candidate.origin.caller = binding.caller ∧
    candidate.origin.source = binding.source ∧
    candidate.origin.binder = binding.binder ∧
    candidate.origin.initializer = binding.initializer

def CatalogOrigins (catalog : Catalog) : Prop :=
  ∀ binding ∈ catalog.bindings, BindingOrigins binding

private theorem candidate_binding {plan : SourceSpecializationWorklist.Plan}
    (unique : (plan.specializations.map (·.key)).Nodup)
    {candidate : Instance} (origin : CatalogEntryOrigin plan candidate.origin)
    {row : SourceSpecialization.SpecializedFunction} (member : row ∈ plan.specializations)
    {binder : TypedBinder} {initializer : ExpressionId}
    (binding : ({ binder, initializer } : SourceSpecializationWorklist.LocalLambdaBinding) ∈
      SourceSpecializationWorklist.localLambdaBindings row.function.typedBody)
    (caller : candidate.origin.caller = row.key)
    (id : candidate.origin.binder.id = binder.id) :
    candidate.origin.source = row.function.typedBody ∧
      candidate.origin.binder = binder ∧ candidate.origin.initializer = initializer := by
  obtain ⟨actual, present, actualCaller, actualSource, selected⟩ := origin
  have same := same_key unique present member (actualCaller.symm.trans caller)
  subst actual
  have picked : ({ binder, initializer } : SourceSpecializationWorklist.LocalLambdaBinding) ∈
      (SourceSpecializationWorklist.localLambdaBindings candidate.origin.source).filter
        (fun entry => entry.binder.id == candidate.origin.binder.id) := by
    apply List.mem_filter.mpr
    exact ⟨actualSource.symm ▸ binding, by simp [id]⟩
  change _ = [candidate.origin.localInstance.binding] at selected
  simp only [SourceCompilationPlan.LocalLambdaCatalogEntry.binder] at picked
  rw [selected] at picked
  have sameBinding := List.mem_singleton.mp picked
  exact ⟨actualSource, (congrArg SourceSpecializationWorklist.LocalLambdaBinding.binder sameBinding).symm,
    (congrArg SourceSpecializationWorklist.LocalLambdaBinding.initializer sameBinding).symm⟩

theorem of_preparation {project : Ty → Except SourceCoreLocalPolymorphism.Error Core.Ty}
    {plan : SourceSpecializationWorklist.Plan} {contextFuel : Option Nat} {catalog : Catalog}
    (accepted : prepareWithProjection project plan contextFuel = .ok catalog) :
    CatalogOrigins catalog := by
  unfold prepareWithProjection at accepted
  obtain ⟨entries, discovered, accepted⟩ := bind_ok accepted
  have discovered : SourceCompilationPlan.localLambdaCatalog plan contextFuel = .ok entries := by
    cases actual : SourceCompilationPlan.localLambdaCatalog plan contextFuel <;> simp_all [Except.mapError]
  obtain ⟨unique, origins⟩ := catalog_entry_origins discovered
  obtain ⟨instances, prepared, accepted⟩ := bind_ok accepted
  have instancesOrigin : ∀ candidate ∈ instances, CatalogEntryOrigin plan candidate.origin := by
    refine mapM_property (property := fun candidate => CatalogEntryOrigin plan candidate.origin) prepared ?_
    intro entry member candidate actual
    have same : candidate.origin = entry := by
      run_tac unfoldAction `actual
      simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at actual
      split at actual <;> try contradiction
      split at actual <;> try contradiction
      split at actual <;> try contradiction
      split at actual <;> try contradiction
      split at actual <;> try contradiction
      split at actual <;> try contradiction
      split at actual <;> try contradiction
      split at actual <;> try contradiction
      obtain ⟨_, _, actual⟩ := bind_ok actual
      obtain ⟨_, _, actual⟩ := bind_ok actual
      cases actual
      rfl
    rw [same]
    exact origins entry member
  obtain ⟨bindings, assembled, accepted⟩ := bind_ok accepted
  cases accepted
  change ∀ binding ∈ bindings, BindingOrigins binding
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
            intro binding member candidate candidateMember
            rcases List.mem_append.mp member with old | added
            · exact previous binding old candidate candidateMember
            · cases List.mem_singleton.mp added
              obtain ⟨present, picked⟩ := List.mem_filter.mp candidateMember
              have picked := of_decide_eq_true picked
              have collected := binding_mem nodeMember (by rfl) (by simp_all) (by assumption)
              exact ⟨picked.1, candidate_binding unique (instancesOrigin candidate present)
                rowMember collected picked.1 picked.2⟩
          · cases step
            exact ⟨current, rfl, previous⟩
    · cases step
      exact ⟨current, rfl, previous⟩

theorem with_contracts {catalog assigned : Catalog}
    {idAt : Key → ExpressionId → Substitution → Option Core.Word}
    (origins : CatalogOrigins catalog)
    (accepted : catalog.withCallableContracts idAt = .ok assigned) :
    CatalogOrigins assigned := by
  unfold Catalog.withCallableContracts at accepted
  obtain ⟨bindings, prepared, accepted⟩ := bind_ok accepted
  cases accepted
  refine mapM_property (property := BindingOrigins) prepared ?_
  intro binding member updated actual
  obtain ⟨instances, preparedInstances, actual⟩ := bind_ok actual
  cases actual
  refine mapM_property (property := fun candidate =>
    candidate.origin.caller = binding.caller ∧ candidate.origin.source = binding.source ∧
      candidate.origin.binder = binding.binder ∧ candidate.origin.initializer = binding.initializer)
    preparedInstances ?_
  intro candidate present decorated actual
  try dsimp only at actual
  split at actual <;> try contradiction
  cases actual
  exact origins binding member candidate present

theorem at_context {catalog : Catalog} {caller : Key} {binder : Resolved.LocalId}
    {binding : Binding} {active : Substitution} {candidate : Instance}
    (origins : CatalogOrigins catalog)
    (located : catalog.binding caller binder = .ok binding)
    (member : candidate ∈ binding.atContext active) :
    candidate.origin.caller = caller ∧ candidate.origin.source = binding.source ∧
      candidate.origin.binder = binding.binder ∧ candidate.origin.initializer = binding.initializer := by
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
      have identity := of_decide_eq_true selected.2
      have origin := origins binding selected.1 candidate instanceMember
      exact ⟨origin.1.trans identity.1, origin.2⟩

end Solcore.SourceSemantics.CoreLowering.PreparedLocalInstanceOrigins
