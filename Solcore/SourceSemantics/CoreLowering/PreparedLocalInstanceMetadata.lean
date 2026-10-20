import Lean
import Solcore.Frontend.SourceCoreLocalPolymorphism

/-! Successful local-instance preparation supplies the actual contextual lambda
and its checked native parameter and result types. Contract attachment changes
only the descriptor and keeps these facts. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.PreparedLocalInstanceMetadata
open Frontend SourceInference TypeSystem SourceCoreLocalPolymorphism

def Metadata (project : Ty → Except SourceCoreLocalPolymorphism.Error Core.Ty) (candidate : Instance) : Prop :=
  candidate.source.owner = candidate.origin.caller.declaration ∧
  candidate.origin.binder.id.owner = candidate.source.owner ∧
  candidate.origin.initializer.occurrence.owner = candidate.source.owner ∧
  ∃ node parameters result body,
    candidate.source.lookupExpression? candidate.origin.initializer = some node ∧
    node.form = .lambda parameters result body ∧
    node.type = candidate.origin.substitution.apply candidate.origin.binder.scheme.body ∧
    node.type = .function (Ty.productMany (parameters.map (·.scheme.body))) result ∧
    node.type.freeVariables = [] ∧
    project (Ty.productMany (parameters.map (·.scheme.body))) = .ok candidate.parameterType ∧
    project result = .ok candidate.resultType

def BindingMetadata (project : Ty → Except SourceCoreLocalPolymorphism.Error Core.Ty)
    (binding : Binding) : Prop :=
  ∀ candidate ∈ binding.instances,
    candidate.origin.caller = binding.caller ∧
    candidate.origin.binder.id = binding.binder.id ∧ Metadata project candidate

def CatalogMetadata (project : Ty → Except SourceCoreLocalPolymorphism.Error Core.Ty) (catalog : Catalog) : Prop :=
  ∀ binding ∈ catalog.bindings, BindingMetadata project binding

/-- Inspect the actual private compiler action and ask Lean to unfold it. No
generated private identifier or replacement implementation is used. -/
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

private theorem bind_ok {α β ε : Type} {action : Except ε α}
    {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) :
    ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

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

/-- The same preparation action authenticates every retained contextual lambda.
The final catalog loop only selects from that checked instance list. -/
theorem of_preparation {project : Ty → Except SourceCoreLocalPolymorphism.Error Core.Ty}
    {plan : SourceSpecializationWorklist.Plan} {contextFuel : Option Nat} {catalog : Catalog}
    (accepted : prepareWithProjection project plan contextFuel = .ok catalog) :
    CatalogMetadata project catalog := by
  unfold prepareWithProjection at accepted
  obtain ⟨entries, _, accepted⟩ := bind_ok accepted
  obtain ⟨instances, instantiated, accepted⟩ := bind_ok accepted
  have valid : ∀ candidate ∈ instances, Metadata project candidate := by
    refine mapM_property (property := Metadata project) instantiated ?_
    intro entry _ candidate actual
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
    obtain ⟨parameterType, projectedParameter, actual⟩ := bind_ok actual
    obtain ⟨resultType, projectedResult, actual⟩ := bind_ok actual
    cases actual
    simp_all [Metadata, Instance.source, Bool.or_eq_true, List.isEmpty_iff]
    refine ⟨_, _, ⟨rfl, rfl⟩, ?_⟩
    simp_all
  obtain ⟨bindings, assembled, accepted⟩ := bind_ok accepted
  cases accepted
  change ∀ binding ∈ bindings, BindingMetadata project binding
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
              obtain ⟨present, selected⟩ := List.mem_filter.mp memberCandidate
              have selected := of_decide_eq_true selected
              exact ⟨selected.1, selected.2, valid candidate present⟩
          · cases step
            exact ⟨current, rfl, previous⟩
    · cases step
      exact ⟨current, rfl, previous⟩

theorem with_contracts {project : Ty → Except SourceCoreLocalPolymorphism.Error Core.Ty}
    {catalog assigned : Catalog} {idAt : Key → ExpressionId → Substitution → Option Core.Word}
    (valid : CatalogMetadata project catalog)
    (accepted : catalog.withCallableContracts idAt = .ok assigned) :
    CatalogMetadata project assigned := by
  unfold Catalog.withCallableContracts at accepted
  obtain ⟨bindings, prepared, accepted⟩ := bind_ok accepted
  cases accepted
  refine mapM_property (property := BindingMetadata project) prepared ?_
  intro binding member updated actual
  obtain ⟨instances, preparedInstances, actual⟩ := bind_ok actual
  cases actual
  refine mapM_property (property := fun candidate =>
    candidate.origin.caller = binding.caller ∧
    candidate.origin.binder.id = binding.binder.id ∧ Metadata project candidate) preparedInstances ?_
  intro candidate present decorated actual
  try dsimp only at actual
  split at actual <;> try contradiction
  cases actual
  exact valid binding member candidate present

/-- A real binding lookup and lexical filter retain the authenticated instance;
the selection never substitutes a candidate from another caller or binder. -/
theorem at_context {project : Ty → Except SourceCoreLocalPolymorphism.Error Core.Ty}
    {catalog : Catalog} {caller : Key} {binder : Resolved.LocalId}
    {binding : Binding} {active : Substitution} {candidate : Instance}
    (valid : CatalogMetadata project catalog)
    (located : catalog.binding caller binder = .ok binding)
    (member : candidate ∈ binding.atContext active) :
    candidate.origin.caller = caller ∧ candidate.origin.binder.id = binder ∧
      Metadata project candidate := by
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
      have metadata := valid binding selected.1 candidate instanceMember
      exact ⟨metadata.1.trans identity.1, metadata.2.1.trans identity.2, metadata.2.2⟩

end Solcore.SourceSemantics.CoreLowering.PreparedLocalInstanceMetadata
