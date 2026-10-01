import Solcore.SourceSemantics.CoreLowering.CallableAncestryCardinality

/-! Invariants of actual reachable-worklist preparation. No source evaluator
or recursively supplied whole-frame list appears in the traversal. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableAncestryWorklist
open Frontend SourceInference CallableAncestryMetadata CallableAncestryCache CallableAncestryTransitions CallableAncestryCardinality
abbrev Inputs := @SourceCoreCallableAncestryPreparation.Inputs
abbrev NativeState := SourceCoreCallableAncestryCache.State
abbrev Table := SourceCoreCallableAncestryCache.Table

structure StatesValid {checked : Checked} {base : Base checked} (owned : Owned base) (states : List NativeState) : Prop where
  unique : (states.map (·.key)).Nodup
  authentic : ∀ state ∈ states, ∃ frame, Authenticates owned frame (some (sourceState state))

private theorem intern_total {checked : Checked} {base : Base checked} {owned : Owned base}
    {states : List NativeState} (valid : StatesValid owned states) {state : NativeState}
    (authentic : ∃ frame, Authenticates owned frame (some (sourceState state))) :
    ∃ position output, SourceCoreCallableAncestryPreparation.intern states state = .ok (position, output) ∧
      StatesValid owned output ∧ states ⊆ output ∧ state ∈ output := by
  unfold SourceCoreCallableAncestryPreparation.intern
  cases selected : states.zipIdx.find? (fun row => decide (row.1.key = state.key)) with
  | none =>
    have fresh : state.key ∉ states.map (·.key) := by
      intro member
      obtain ⟨previous, included, same⟩ := List.mem_map.mp member
      obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp included
      have zipped := List.mk_mem_zipIdx_iff_getElem?.mpr found
      have excluded := List.find?_eq_none.mp selected (previous, index) zipped
      exact excluded (by simpa only [decide_eq_true_eq] using same)
    refine ⟨states.length, states ++ [state], rfl, ?_, ?_, by simp⟩
    · constructor
      · simp only [List.map_append, List.map_cons, List.map_nil, List.nodup_append]
        refine ⟨valid.unique, by simp, ?_⟩
        intro before member after singleton equal
        have same : after = state.key := by simpa using singleton
        exact fresh (by simpa [← same, ← equal] using member)
      · intro value member
        rcases List.mem_append.mp member with previous | added
        · exact valid.authentic value previous
        · have same : value = state := by simpa using added
          simpa only [same] using authentic
    · intro value member; exact List.mem_append_left _ member
  | some row =>
    obtain ⟨previous, index⟩ := row
    have member := List.mem_of_find?_eq_some selected
    have lookup := List.mk_mem_zipIdx_iff_getElem?.mp member
    have included := List.mem_of_getElem? lookup
    have keySame : previous.key = state.key := by simpa using List.find?_some selected
    obtain ⟨previousFrame, previousAuth⟩ := valid.authentic previous included
    obtain ⟨frame, stateAuth⟩ := authentic
    have same := native_key_injective previousAuth stateAuth keySame
    dsimp only
    rw [if_pos same]
    exact ⟨index, states, rfl, valid, fun _ member => member, same ▸ included⟩

private theorem bind_ok {α β ε : Type} {computation : Except ε α} {next : α → Except ε β} {result : β}
    (accepted : computation >>= next = .ok result) : ∃ value, computation = .ok value ∧ next value = .ok result := by
  cases computation with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem forIn_total {α β ε : Type} (items : List α) (step : α → β → Except ε (ForInStep β))
    (invariant : β → Prop) (initial : β) (valid : invariant initial)
    (next : ∀ item ∈ items, ∀ state, invariant state →
      ∃ result, step item state = .ok (.yield result) ∧ invariant result) :
    ∃ final, forIn items initial step = .ok final ∧ invariant final := by
  induction items generalizing initial with
  | nil => exact ⟨initial, rfl, valid⟩
  | cons head tail ih =>
    obtain ⟨after, executed, maintained⟩ := next head (by simp) initial valid
    obtain ⟨final, finished, preserved⟩ := ih after maintained (fun item member => next item (by simp [member]))
    refine ⟨final, ?_, preserved⟩
    simpa only [List.forIn_cons, executed, bind, Except.bind] using finished

private theorem forIn_preserves {α β ε : Type} {items : List α} {initial final : β}
    {step : α → β → Except ε (ForInStep β)} (accepted : forIn items initial step = .ok final)
    (invariant : List α → β → Prop) (start : invariant [] initial)
    (next : ∀ seen item remaining state outcome,
      items = seen ++ item :: remaining → invariant seen state → step item state = .ok outcome →
      ∃ updated, outcome = .yield updated ∧ invariant (seen ++ [item]) updated) : invariant items final := by
  have loop : ∀ remaining seen state,
      items = seen ++ remaining → invariant seen state → forIn remaining state step = .ok final → invariant items final := by
    intro remaining
    induction remaining with
    | nil =>
      intro seen state split valid finished
      simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] at finished
      subst final
      simpa [split] using valid
    | cons item remaining ih =>
      intro seen state split valid finished
      rw [List.forIn_cons] at finished
      obtain ⟨outcome, ran, finished⟩ := bind_ok finished
      obtain ⟨updated, rfl, preserved⟩ := next seen item remaining state outcome split valid ran
      exact ih (seen ++ [item]) updated (by simpa [List.append_assoc] using split) preserved finished
  exact loop items [] initial rfl start accepted



theorem expand_total {checked : Checked} {base : Base checked} (owned : Owned base)
    (inputs : Inputs base) (position : Nat) (state : NativeState) (initial : Table)
    (authentic : ∃ frame, Authenticates owned frame (some (sourceState state)))
    (valid : StatesValid owned initial.states) :
    ∃ final, SourceCoreCallableAncestryPreparation.expand inputs position state initial = .ok final ∧
      StatesValid owned final.states := by
  let lambdaStep : Lambda → Table → Except SourceCoreCallableAncestryPreparation.Error (ForInStep Table) := fun (template : Lambda) (table : Table) =>
    if SourceCoreCallableAncestryPreparation.lambdaAllowed inputs state template.descriptor then
      Except.ok (ForInStep.yield {table with lambdas := table.lambdas ++ [⟨position, template.descriptor⟩]})
    else Except.ok (ForInStep.yield table)
  have first := forIn_total (ε := SourceCoreCallableAncestryPreparation.Error)
    inputs.templates.lambdas lambdaStep (fun table => StatesValid owned table.states) initial valid
  obtain ⟨middle, firstEval, firstValid⟩ := first (by
    intro template _ table valid
    dsimp only [lambdaStep]
    split <;> exact ⟨_, rfl, valid⟩)
  let innerStep : SourceCoreCallableViews.Entry base.sourceProgram base.plan → Lambda → Table →
      Except SourceCoreCallableAncestryPreparation.Error (ForInStep Table) := fun (entry : SourceCoreCallableViews.Entry base.sourceProgram base.plan) (template : Lambda) (table : Table) =>
    match SourceCoreCallableAncestryPreparation.view? inputs state entry.id template.descriptor with
    | none => Except.ok (ForInStep.yield table)
    | some next => do
      let (destination, states) ← SourceCoreCallableAncestryPreparation.intern table.states next
      pure (ForInStep.yield {table with states, views := table.views ++ [⟨position, entry.id, template.descriptor, destination⟩]})
  have innerTotal : ∀ entry (table : Table), StatesValid owned table.states →
      ∃ final, forIn inputs.templates.lambdas table (innerStep entry) = .ok final ∧ StatesValid owned final.states := by
    intro entry table valid
    apply forIn_total _ _ (fun table => StatesValid owned table.states) table valid
    intro template _ table valid
    dsimp only [innerStep]
    cases generated : SourceCoreCallableAncestryPreparation.view? inputs state entry.id template.descriptor with
    | none => exact ⟨_, rfl, valid⟩
    | some next =>
      obtain ⟨frame, ancestry⟩ := authentic
      obtain ⟨receipt, step, same⟩ := view_sound owned inputs (state := sourceState state) (by simpa only [native_source] using generated)
      have nextAuth : ∃ frame, Authenticates owned frame (some (sourceState next)) :=
        ⟨.view entry.id template.descriptor frame, by rw [same, source_native]; exact .view ancestry receipt step⟩
      obtain ⟨destination, states, accepted, maintained, _, _⟩ := intern_total valid nextAuth
      exact ⟨{table with states, views := table.views ++ [⟨position, entry.id, template.descriptor, destination⟩]},
        by simp only [accepted, bind, Except.bind, pure, Except.pure], maintained⟩
  let outerStep := fun (entry : SourceCoreCallableViews.Entry base.sourceProgram base.plan) (table : Table) => do
    let after ← forIn inputs.templates.lambdas table (innerStep entry)
    pure (ForInStep.yield after)
  have second := forIn_total inputs.views.entries outerStep (fun table => StatesValid owned table.states) middle firstValid
  obtain ⟨final, secondEval, finalValid⟩ := second (by
    intro entry _ table valid
    obtain ⟨after, ran, valid⟩ := innerTotal entry table valid
    exact ⟨after, by simp only [outerStep, ran, bind, Except.bind, pure, Except.pure], valid⟩)
  refine ⟨final, ?_, finalValid⟩
  change (forIn inputs.templates.lambdas initial lambdaStep >>= fun middle =>
    forIn inputs.views.entries middle outerStep >>= fun result => Except.ok result) = .ok final
  simp only [firstEval, secondEval, bind, Except.bind]

/-- Successful seeding retains every owned named starting state and gives
only authenticated states with distinct keys. -/
theorem seed_spec {checked : Checked} {base : Base checked} (owned : Owned base)
    (inputs : Inputs base) {initial : Table}
    (seeded : SourceCoreCallableAncestryPreparation.seed inputs = .ok initial) :
    StatesValid owned initial.states ∧ CoversRoots owned initial.states := by
  unfold SourceCoreCallableAncestryPreparation.seed at seeded
  obtain ⟨final, executed, result⟩ := bind_ok seeded
  cases result
  let invariant := fun (seen : List SourceCoreStageCodebook.Entry) (table : Table) =>
    StatesValid owned table.states ∧ ∀ {id} (receipt : Named owned id), receipt.entry ∈ seen → nativeState receipt.state ∈ table.states
  have valid : invariant inputs.callable.table.entries initial := by
    apply forIn_preserves executed invariant
    · exact ⟨⟨by simp, by simp⟩, by simp⟩
    · intro seen entry remaining table outcome _ previous rowAccepted
      cases origin : entry.origin with
      | named owner =>
        simp only [origin] at rowAccepted
        cases generated : SourceCoreCallableAncestryPreparation.named? inputs entry.id with
        | none => simp [generated, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at rowAccepted
        | some state =>
          simp only [generated, pure, Except.pure, bind, Except.bind] at rowAccepted
          obtain ⟨receipt, same⟩ := named_sound owned inputs generated
          have stateAuth : ∃ frame, Authenticates owned frame (some (sourceState state)) :=
            ⟨.named entry.id, by rw [same, source_native]; exact .named receipt⟩
          obtain ⟨position, states, accepted, maintained, includes, added⟩ := intern_total previous.1 stateAuth
          simp only [accepted, Except.ok.injEq] at rowAccepted
          subst outcome
          refine ⟨_, rfl, maintained, ?_⟩
          intro id named member
          rcases List.mem_append.mp member with before | here
          · exact includes (previous.2 named before)
          · have entryEq : named.entry = entry := by simpa using here
            have identifier : named.entry.id = id := by simpa using List.find?_some named.selected
            have identifier : entry.id = id := by simpa only [entryEq] using identifier
            have exactState := Option.some.inj ((identifier ▸ generated).symm.trans (named_complete inputs named))
            exact exactState ▸ added
      | lambda owner id active =>
        simp only [origin, pure, Except.pure, Except.ok.injEq] at rowAccepted
        subst outcome
        refine ⟨_, rfl, previous.1, ?_⟩
        intro id named member
        rcases List.mem_append.mp member with before | here
        · exact previous.2 named before
        · have entryEq : named.entry = entry := by simpa using here
          have impossible := named.origin
          rw [entryEq, origin] at impossible
          cases impossible
      | builtin function =>
        simp only [origin, pure, Except.pure, Except.ok.injEq] at rowAccepted
        subst outcome
        refine ⟨_, rfl, previous.1, ?_⟩
        intro id named member
        rcases List.mem_append.mp member with before | here
        · exact previous.2 named before
        · have entryEq : named.entry = entry := by simpa using here
          have impossible := named.origin
          rw [entryEq, origin] at impossible
          cases impossible
  refine ⟨valid.1, ?_⟩
  intro id receipt
  apply valid.2 receipt
  rw [callable_eq owned inputs]
  exact List.mem_of_find?_eq_some receipt.selected

/-- A reached-state traversal cannot exhaust the structural capacity. The
initial seed equation remains explicit; no arbitrary runtime fuel appears. -/
theorem saturate_total {checked : Checked} {base : Base checked} (owned : Owned base)
    (inputs : Inputs base) (initial : Table) (covered : CoversRoots owned initial.states)
    (fuel position : Nat) (table : Table) (valid : StatesValid owned table.states)
    (budget : SourceCoreCallableAncestryPreparation.capacity inputs initial ≤ position + fuel) :
    ∃ final, SourceCoreCallableAncestryPreparation.saturate inputs fuel position table = .ok final ∧
      StatesValid owned final.states := by
  induction fuel generalizing position table with
  | zero =>
    have bounded := states_bounded inputs initial covered table.states valid.unique valid.authentic
    have absent : table.stateAt? position = none := List.getElem?_eq_none (by omega)
    exact ⟨table, by simp only [SourceCoreCallableAncestryPreparation.saturate, absent], valid⟩
  | succ fuel ih =>
    cases selected : table.stateAt? position with
    | none => exact ⟨table, by simp only [SourceCoreCallableAncestryPreparation.saturate, selected], valid⟩
    | some state =>
      have authentic := valid.authentic state (List.mem_of_getElem? selected)
      obtain ⟨next, expanded, maintained⟩ := expand_total owned inputs position state table authentic valid
      obtain ⟨final, completed, finalValid⟩ := ih (position + 1) next maintained (by omega)
      refine ⟨final, ?_, finalValid⟩
      rw [SourceCoreCallableAncestryPreparation.saturate, selected]
      simpa only [expanded, bind, Except.bind] using completed

theorem seeded_saturation_total {checked : Checked} {base : Base checked} (owned : Owned base)
    (inputs : Inputs base) {initial : Table}
    (seeded : SourceCoreCallableAncestryPreparation.seed inputs = .ok initial) :
    ∃ final, SourceCoreCallableAncestryPreparation.saturate inputs
      (SourceCoreCallableAncestryPreparation.capacity inputs initial) 0 initial = .ok final ∧
      StatesValid owned final.states := by
  obtain ⟨valid, covered⟩ := seed_spec owned inputs seeded
  exact saturate_total owned inputs initial covered _ 0 initial valid (by omega)

end Solcore.SourceSemantics.CoreLowering.CallableAncestryWorklist
