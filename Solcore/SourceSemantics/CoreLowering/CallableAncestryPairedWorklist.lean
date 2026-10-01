import Solcore.SourceSemantics.CoreLowering.CallableAncestryPairedValidation

/-! State invariants for the actual paired reachable worklist. The finite
named root set below is extracted from owned table lookups; it is not a list
of runtime frames. All source metadata remains separate from native active
compilation contexts. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableAncestryPairedWorklist
open Frontend SourceInference TypeSystem CallableAncestryPairedLookup
abbrev State := SourceCoreCallableAncestryReadRecipes.State

def namedRoots {checked : Checked} {base : Base checked} (inputs : Inputs base) : List State :=
  inputs.callable.table.entries.filterMap (fun entry => SourceCoreCallableAncestryPairedPreparation.named? inputs entry.id)

private theorem named_fields {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {id : Core.Word} {state : State}
    (accepted : SourceCoreCallableAncestryPairedPreparation.named? inputs id = some state) :
    ∃ specialized : SourceSpecialization.SpecializedFunction,
      SourceCompilationPlan.exactSpecialization base.plan state.metadata.owner = .ok specialized ∧
        state.metadata.source = specialized.function.typedBody ∧ state.metadata.active = [] ∧ state.nativeActive = [] := by
  cases selected : SourceCoreCallableAncestryPreparation.named? inputs id with
  | none => simp [SourceCoreCallableAncestryPairedPreparation.named?, selected] at accepted
  | some metadata =>
    have same : (⟨metadata, []⟩ : State) = state := by
      simpa [SourceCoreCallableAncestryPairedPreparation.named?, selected] using accepted
    subst state
    obtain ⟨specialized, found, source, active⟩ := CallableAncestryPairedProfiles.named_source inputs selected
    exact ⟨specialized, found, source, active, rfl⟩

theorem named_roots_seeded {checked : Checked} {base : Base checked} (inputs : Inputs base) :
    CallableAncestryPairedProfiles.Seeded base (namedRoots inputs) := by
  intro root member
  obtain ⟨entry, _, accepted⟩ := List.mem_filterMap.mp member
  exact named_fields accepted

theorem named_roots_cover {checked : Checked} {base : Base checked} (inputs : Inputs base)
    {id : Core.Word} {state : State}
    (accepted : SourceCoreCallableAncestryPairedPreparation.named? inputs id = some state) : state ∈ namedRoots inputs := by
  cases selected : inputs.callable.table.entryAt? id with
  | none => simp [SourceCoreCallableAncestryPairedPreparation.named?, SourceCoreCallableAncestryPreparation.named?, selected] at accepted
  | some entry =>
    have identifier : entry.id = id := by simpa using List.find?_some selected
    exact List.mem_filterMap.mpr ⟨entry, List.mem_of_find?_eq_some selected, identifier ▸ accepted⟩

theorem authenticated_key_injective {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {left right : State} {leftFrame rightFrame : Frame}
    (leftAuth : Authenticates inputs leftFrame (some left)) (rightAuth : Authenticates inputs rightFrame (some right))
    (same : SourceCoreCallableAncestryPairedCache.stateKey left = SourceCoreCallableAncestryPairedCache.stateKey right) :
    left = right := by
  have seeded := named_roots_seeded inputs
  exact CallableAncestryPairedProfiles.key_injective (CallableAncestryPairedProfiles.seeded_coherent seeded)
    (CallableAncestryPairedValidation.authenticated_valid seeded (named_roots_cover inputs) leftAuth)
    (CallableAncestryPairedValidation.authenticated_valid seeded (named_roots_cover inputs) rightAuth) same

structure StatesValid {checked : Checked} {base : Base checked} (inputs : Inputs base) (states : List State) : Prop where
  unique : (states.map SourceCoreCallableAncestryPairedCache.stateKey).Nodup
  authentic : ∀ state ∈ states, ∃ frame, Authenticates inputs frame (some state)

theorem intern_total {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {states : List State} (valid : StatesValid inputs states) {state : State}
    (authentic : ∃ frame, Authenticates inputs frame (some state)) :
    ∃ position output, SourceCoreCallableAncestryPairedPreparation.intern states state = .ok (position, output) ∧
      StatesValid inputs output ∧ states ⊆ output ∧ state ∈ output := by
  unfold SourceCoreCallableAncestryPairedPreparation.intern
  cases selected : states.zipIdx.find? (fun row => decide
      (SourceCoreCallableAncestryPairedCache.stateKey row.1 = SourceCoreCallableAncestryPairedCache.stateKey state)) with
  | none =>
    have fresh : SourceCoreCallableAncestryPairedCache.stateKey state ∉ states.map SourceCoreCallableAncestryPairedCache.stateKey := by
      intro member
      obtain ⟨previous, included, same⟩ := List.mem_map.mp member
      obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp included
      have excluded := List.find?_eq_none.mp selected (previous, index) (List.mk_mem_zipIdx_iff_getElem?.mpr found)
      exact excluded (by simpa only [decide_eq_true_eq] using same)
    refine ⟨states.length, states ++ [state], rfl, ?_, ?_, by simp⟩
    · constructor
      · simp only [List.map_append, List.map_cons, List.map_nil, List.nodup_append]
        refine ⟨valid.unique, by simp, ?_⟩
        intro before member after singleton equal
        have same : after = SourceCoreCallableAncestryPairedCache.stateKey state := by simpa using singleton
        exact fresh (by simpa [← same, ← equal] using member)
      · intro value member
        rcases List.mem_append.mp member with previous | added
        · exact valid.authentic value previous
        · have same : value = state := by simpa using added
          simpa only [same] using authentic
    · intro value member; exact List.mem_append_left _ member
  | some row =>
    obtain ⟨previous, index⟩ := row
    have included := List.mem_of_getElem? (List.mk_mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some selected))
    have keySame : SourceCoreCallableAncestryPairedCache.stateKey previous = SourceCoreCallableAncestryPairedCache.stateKey state := by
      simpa using List.find?_some selected
    obtain ⟨previousFrame, previousAuth⟩ := valid.authentic previous included
    obtain ⟨frame, stateAuth⟩ := authentic
    have same := authenticated_key_injective previousAuth stateAuth keySame
    dsimp only
    rw [if_pos same]
    exact ⟨index, states, rfl, valid, fun _ member => member, same ▸ included⟩

theorem intern_members {states output : List State} {state : State} {position : Nat}
    (accepted : SourceCoreCallableAncestryPairedPreparation.intern states state = .ok (position, output)) :
    output ⊆ states ++ [state] := by
  unfold SourceCoreCallableAncestryPairedPreparation.intern at accepted
  split at accepted
  · cases accepted; exact fun _ member => member
  · split at accepted
    · cases accepted; exact fun _ member => List.mem_append_left _ member
    · cases accepted

private theorem bind_ok {α β ε : Type} {computation : Except ε α} {next : α → Except ε β} {result : β}
    (accepted : computation >>= next = .ok result) : ∃ value, computation = .ok value ∧ next value = .ok result := by
  cases computation with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

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

/-- Successful seeding provides distinct authenticated states, exact named
source provenance, and coverage of every accepted owned named descriptor. -/
theorem seed_spec {checked : Checked} {base : Base checked} (inputs : Inputs base) {initial : Table}
    (seeded : SourceCoreCallableAncestryPairedPreparation.seed inputs = .ok initial) :
    StatesValid inputs initial.states ∧ CallableAncestryPairedProfiles.Seeded base initial.states ∧
      ∀ {id state}, SourceCoreCallableAncestryPairedPreparation.named? inputs id = some state → state ∈ initial.states := by
  unfold SourceCoreCallableAncestryPairedPreparation.seed at seeded
  obtain ⟨final, executed, result⟩ := bind_ok seeded
  cases result
  let invariant := fun (seen : List SourceCoreStageCodebook.Entry) (table : Table) =>
    StatesValid inputs table.states ∧
      (∀ state ∈ table.states, ∃ id, SourceCoreCallableAncestryPairedPreparation.named? inputs id = some state) ∧
      ∀ entry ∈ seen, ∀ state, SourceCoreCallableAncestryPairedPreparation.named? inputs entry.id = some state → state ∈ table.states
  have valid : invariant inputs.callable.table.entries initial := by
    apply forIn_preserves executed invariant
    · exact ⟨⟨by simp, by simp⟩, by simp, by simp⟩
    · intro seen entry remaining table outcome decomposition previous rowAccepted
      have entryMember : entry ∈ inputs.callable.table.entries := by rw [decomposition]; simp
      cases origin : entry.origin with
      | named owner =>
        simp only [origin] at rowAccepted
        cases generated : SourceCoreCallableAncestryPairedPreparation.named? inputs entry.id with
        | none => simp [generated, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at rowAccepted
        | some state =>
          simp only [generated, pure, Except.pure, bind, Except.bind] at rowAccepted
          obtain ⟨position, states, accepted, maintained, includes, added⟩ := intern_total previous.1 ⟨.named entry.id, .named generated⟩
          simp only [accepted, Except.ok.injEq] at rowAccepted
          subst outcome
          refine ⟨_, rfl, maintained, ?_, ?_⟩
          · intro value member
            rcases List.mem_append.mp (intern_members accepted member) with old | new
            · exact previous.2.1 value old
            · have same : value = state := by simpa using new
              exact ⟨entry.id, same ▸ generated⟩
          · intro earlier member value found
            rcases List.mem_append.mp member with old | new
            · exact includes (previous.2.2 earlier old value found)
            · have same : earlier = entry := by simpa using new
              subst earlier
              have sameValue := Option.some.inj (found.symm.trans generated)
              exact sameValue ▸ added
      | lambda owner id active =>
        simp only [origin, pure, Except.pure, Except.ok.injEq] at rowAccepted
        subst outcome
        refine ⟨_, rfl, previous.1, previous.2.1, ?_⟩
        intro earlier member value found
        rcases List.mem_append.mp member with old | new
        · exact previous.2.2 earlier old value found
        · have same : earlier = entry := by simpa using new
          subst earlier
          simp [SourceCoreCallableAncestryPairedPreparation.named?, SourceCoreCallableAncestryPreparation.named?,
            CallableAncestryPairedValidation.stage_entry_self inputs.callable.table entryMember, origin] at found
      | builtin builtin =>
        simp only [origin, pure, Except.pure, Except.ok.injEq] at rowAccepted
        subst outcome
        refine ⟨_, rfl, previous.1, previous.2.1, ?_⟩
        intro earlier member value found
        rcases List.mem_append.mp member with old | new
        · exact previous.2.2 earlier old value found
        · have same : earlier = entry := by simpa using new
          subst earlier
          simp [SourceCoreCallableAncestryPairedPreparation.named?, SourceCoreCallableAncestryPreparation.named?,
            CallableAncestryPairedValidation.stage_entry_self inputs.callable.table entryMember, origin] at found
  refine ⟨valid.1, ?_, ?_⟩
  · intro state member
    obtain ⟨id, selected⟩ := valid.2.1 state member
    exact named_fields selected
  · intro id state selected
    have member := named_roots_cover inputs selected
    obtain ⟨entry, entryMember, accepted⟩ := List.mem_filterMap.mp member
    exact valid.2.2 entry entryMember state accepted

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

theorem addView_total {checked : Checked} {base : Base checked} (inputs : Inputs base)
    (table : Table) (callerIndex lexicalIndex : Nat) (caller lexical : State) (id target : Core.Word)
    (callerAuth : ∃ frame, Authenticates inputs frame (some caller))
    (lexicalAuth : ∃ frame, Authenticates inputs frame (some lexical)) (valid : StatesValid inputs table.states) :
    ∃ final, SourceCoreCallableAncestryPairedPreparation.addView inputs table callerIndex lexicalIndex caller lexical id target = .ok final ∧
      StatesValid inputs final.states := by
  unfold SourceCoreCallableAncestryPairedPreparation.addView
  cases generated : SourceCoreCallableAncestryPairedPreparation.view? inputs caller lexical id target with
  | none => exact ⟨table, rfl, valid⟩
  | some state =>
    obtain ⟨callerFrame, callerAuth⟩ := callerAuth
    obtain ⟨lexicalFrame, lexicalAuth⟩ := lexicalAuth
    have authentic : ∃ frame, Authenticates inputs frame (some state) :=
      ⟨.appliedView id target callerFrame lexicalFrame, .appliedView callerAuth lexicalAuth generated⟩
    obtain ⟨position, states, accepted, maintained, _, _⟩ := intern_total valid authentic
    simp only [accepted, bind, Except.bind]
    split <;> exact ⟨_, rfl, maintained⟩

theorem expand_total {checked : Checked} {base : Base checked} (inputs : Inputs base)
    (position : Nat) (state : State) (initial : Table)
    (authentic : ∃ frame, Authenticates inputs frame (some state)) (valid : StatesValid inputs initial.states) :
    ∃ final, SourceCoreCallableAncestryPairedPreparation.expand inputs position state initial = .ok final ∧
      StatesValid inputs final.states := by
  let lambdaStep : SourceCoreLambdaTemplates.Lambda → Table →
      Except SourceCoreCallableAncestryPairedPreparation.Error (ForInStep Table) := fun template table =>
    if SourceCoreCallableAncestryPairedPreparation.lambdaAllowed inputs state template.descriptor then
      let edge : SourceCoreCallableAncestryPairedCache.LambdaEdge := ⟨position, template.descriptor⟩
      if !table.lambdas.contains edge then .ok (.yield {table with lambdas := table.lambdas ++ [edge]})
      else .ok (.yield table)
    else .ok (.yield table)
  obtain ⟨middle, firstEval, firstValid⟩ := forIn_total inputs.templates.lambdas lambdaStep
    (fun table => StatesValid inputs table.states) initial valid (by
      intro template _ table valid
      dsimp only [lambdaStep]
      split
      · split <;> exact ⟨_, rfl, valid⟩
      · exact ⟨_, rfl, valid⟩)
  let innerStep := fun (entry : SourceCoreCallableViews.Entry base.sourceProgram base.plan) (target : Core.Word)
      (row : State × Nat) (table : Table) => do
    let after ← SourceCoreCallableAncestryPairedPreparation.addView inputs table position row.2 state row.1 entry.id target
    let final ← SourceCoreCallableAncestryPairedPreparation.addView inputs after row.2 position row.1 state entry.id target
    pure (ForInStep.yield final)
  have innerTotal : ∀ entry target (table : Table), StatesValid inputs table.states →
      ∃ final, forIn initial.states.zipIdx table (innerStep entry target) = .ok final ∧ StatesValid inputs final.states := by
    intro entry target table maintained
    apply forIn_total _ _ (fun table => StatesValid inputs table.states) table maintained
    intro row member table maintained
    have rowAuth := valid.authentic row.1 (List.mem_of_getElem? (List.mk_mem_zipIdx_iff_getElem?.mp member))
    obtain ⟨after, first, afterValid⟩ := addView_total inputs table position row.2 state row.1 entry.id target authentic rowAuth maintained
    obtain ⟨final, second, finalValid⟩ := addView_total inputs after row.2 position row.1 state entry.id target rowAuth authentic afterValid
    exact ⟨final, by simp only [innerStep, first, second, bind, Except.bind, pure, Except.pure], finalValid⟩
  let outerStep := fun (entry : SourceCoreCallableViews.Entry base.sourceProgram base.plan) (table : Table) =>
    match inputs.callable.table.idAt? (.lambda entry.view.owner entry.view.principal.initializer entry.view.cumulative) with
    | none => Except.ok (ForInStep.yield table)
    | some target => do
      let after ← forIn initial.states.zipIdx table (innerStep entry target)
      pure (ForInStep.yield after)
  obtain ⟨final, secondEval, finalValid⟩ := forIn_total inputs.views.entries outerStep
    (fun table => StatesValid inputs table.states) middle firstValid (by
      intro entry _ table maintained
      dsimp only [outerStep]
      split
      · exact ⟨_, rfl, maintained⟩
      · next target selected =>
        obtain ⟨after, ran, preserved⟩ := innerTotal entry target table maintained
        exact ⟨after, by simp only [ran, bind, Except.bind, pure, Except.pure], preserved⟩)
  refine ⟨final, ?_, finalValid⟩
  change (forIn inputs.templates.lambdas initial lambdaStep >>= fun middle =>
    forIn inputs.views.entries middle outerStep >>= fun result => Except.ok result) = .ok final
  simp only [firstEval, secondEval, bind, Except.bind]

/-- Once the actual named seed succeeds, the production structural capacity
is enough for every reached paired-state expansion. This says nothing yet
about final edge-validation success or native runtime-frame provenance. -/
theorem saturate_total {checked : Checked} {base : Base checked} (inputs : Inputs base) (initial : Table)
    (seeded : SourceCoreCallableAncestryPairedPreparation.seed inputs = .ok initial)
    (fuel position : Nat) (table : Table) (valid : StatesValid inputs table.states)
    (budget : SourceCoreCallableAncestryPairedPreparation.capacity inputs initial ≤ position + fuel) :
    ∃ final, SourceCoreCallableAncestryPairedPreparation.saturate inputs fuel position table = .ok final ∧
      StatesValid inputs final.states := by
  obtain ⟨_, rootSources, covered⟩ := seed_spec inputs seeded
  induction fuel generalizing position table with
  | zero =>
    have bounded := CallableAncestryPairedProfiles.prepared_capacity_bound inputs initial table.states valid.unique (by
      intro state member
      obtain ⟨frame, authenticated⟩ := valid.authentic state member
      exact CallableAncestryPairedValidation.authenticated_valid rootSources covered authenticated)
    have absent : table.stateAt? position = none := List.getElem?_eq_none (by omega)
    exact ⟨table, by simp only [SourceCoreCallableAncestryPairedPreparation.saturate, absent], valid⟩
  | succ fuel ih =>
    cases selected : table.stateAt? position with
    | none => exact ⟨table, by simp only [SourceCoreCallableAncestryPairedPreparation.saturate, selected], valid⟩
    | some state =>
      have authentic := valid.authentic state (List.mem_of_getElem? selected)
      obtain ⟨next, expanded, maintained⟩ := expand_total inputs position state table authentic valid
      obtain ⟨final, completed, finalValid⟩ := ih (position + 1) next maintained (by omega)
      refine ⟨final, ?_, finalValid⟩
      rw [SourceCoreCallableAncestryPairedPreparation.saturate, selected]
      simpa only [expanded, bind, Except.bind] using completed

theorem seeded_saturation_total {checked : Checked} {base : Base checked} (inputs : Inputs base) {initial : Table}
    (seeded : SourceCoreCallableAncestryPairedPreparation.seed inputs = .ok initial) :
    ∃ final, SourceCoreCallableAncestryPairedPreparation.saturate inputs
      (SourceCoreCallableAncestryPairedPreparation.capacity inputs initial) 0 initial = .ok final ∧ StatesValid inputs final.states := by
  have initialValid := (seed_spec inputs seeded).1
  exact saturate_total inputs initial seeded _ 0 initial initialValid (by omega)

end Solcore.SourceSemantics.CoreLowering.CallableAncestryPairedWorklist
