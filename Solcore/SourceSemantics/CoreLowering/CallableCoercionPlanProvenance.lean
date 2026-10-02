import Solcore.SourceSemantics.CoreLowering.CallableSpecializationEquality

/-! Public worklist extension retains the complete supplied root and every
previously selected carrier. These static facts do not reconstruct a source
method or closure history from a key. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableCoercionPlanProvenance
open Frontend SourceInference SourceSpecializationWorklist
abbrev Specialized := SourceSpecialization.SpecializedFunction
abbrev Key := SourceSpecialization.SpecializationKey

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {value : β}
    (accepted : action >>= next = .ok value) : ∃ item, action = .ok item ∧ next item = .ok value := by
  cases action with
  | error error => cases accepted
  | ok item => exact ⟨item, rfl, accepted⟩

private theorem next_fresh {program : CheckedProgram} {seen : List Key}
    {queue rest : List Request} {request : Request} {selected : Specialized}
    (accepted : nextUnseen program seen queue = .ok (some (request, selected, rest))) : selected.key ∉ seen := by
  induction queue generalizing request selected with
  | nil => cases accepted
  | cons current tail ih =>
    unfold nextUnseen at accepted
    obtain ⟨value, _, accepted⟩ := bind_ok accepted
    split at accepted
    · exact ih accepted
    · rename_i skipped
      have fresh : value.key ∉ seen := by
        intro member
        exact skipped (by simpa only [List.any_eq_true, decide_eq_true_eq, exists_eq_right] using member)
      cases accepted
      exact fresh

/-- Once a key is in the actual worklist's seen vector, its complete ordered
filter is unchanged by every finite continuation, including budget exhaustion. -/
theorem runAux_filter {program : CheckedProgram} {seeds seen : List Key} {queue : List Request}
    {entries : List Specialized} {calls : List CallEdge} {references : List ReferenceEdge}
    {budget : Nat} {outcome : Outcome} {key : Key}
    (known : key ∈ seen)
    (accepted : runAux program seeds queue seen entries calls references budget = .ok outcome) :
    outcome.plan.specializations.filter (fun entry => decide (entry.key = key)) =
      entries.filter (fun entry => decide (entry.key = key)) := by
  induction budget generalizing queue seen entries calls references outcome with
  | zero =>
    unfold runAux at accepted
    obtain ⟨next, _, accepted⟩ := bind_ok accepted
    cases next with
    | none => cases accepted; rfl
    | some value => rcases value with ⟨request, selected, rest⟩; cases accepted; rfl
  | succ budget ih =>
    unfold runAux at accepted
    obtain ⟨next, selected, accepted⟩ := bind_ok accepted
    cases next with
    | none => cases accepted; rfl
    | some value =>
      rcases value with ⟨request, value, rest⟩
      have different : value.key ≠ key := fun same => next_fresh selected (same ▸ known)
      obtain ⟨⟨requests, newCalls, newReferences⟩, _, accepted⟩ := bind_ok accepted
      have continued := ih (List.mem_cons_of_mem _ known) accepted
      simpa only [List.filter_append, List.filter_cons, List.filter_nil, decide_eq_false different, Bool.false_eq_true,
        if_false, List.append_nil] using continued

private theorem checked_none {duplicate : Option (Key × Nat)}
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

private theorem find_filter {entries : List Specialized} {key : Key} {selected : Specialized}
    (unique : (entries.map (·.key)).Nodup)
    (found : entries.find? (fun entry => decide (entry.key = key)) = some selected) :
    entries.filter (fun entry => decide (entry.key = key)) = [selected] := by
  induction entries with
  | nil => cases found
  | cons head rest ih =>
    obtain ⟨absent, unique⟩ := List.nodup_cons.mp unique
    by_cases same : head.key = key
    · simp only [List.find?_cons, same, decide_true] at found
      cases found
      have empty : rest.filter (fun entry => decide (entry.key = key)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro entry member
        intro picked
        have selected : entry.key = key := of_decide_eq_true picked
        exact absent (List.mem_map.mpr ⟨entry, member, selected.trans same.symm⟩)
      simp only [List.filter_cons, same, decide_true, if_true, empty]
    · simp only [List.find?_cons, decide_eq_false same] at found
      simpa only [List.filter_cons, decide_eq_false same, Bool.false_eq_true, if_false] using ih unique found

private theorem exact_filter {plan : Plan} {key : Key} {selected : Specialized}
    (accepted : SourceCompilationPlan.exactSpecialization plan key = .ok selected) :
    plan.specializations.filter (fun entry => decide (entry.key = key)) = [selected] := by
  unfold SourceCompilationPlan.exactSpecialization at accepted
  split at accepted <;> try contradiction
  cases accepted
  assumption

private theorem exact_of_filter {plan : Plan} {key : Key} {selected : Specialized}
    (found : plan.specializations.filter (fun entry => decide (entry.key = key)) = [selected]) :
    SourceCompilationPlan.exactSpecialization plan key = .ok selected := by
  simp only [SourceCompilationPlan.exactSpecialization, found]

private theorem none_filter {entries : List Specialized} {key : Key}
    (missing : entries.find? (fun entry => decide (entry.key = key)) = none) :
    entries.filter (fun entry => decide (entry.key = key)) = [] := by
  exact List.filter_eq_nil_iff.mpr (List.find?_eq_none.mp missing)

private theorem key_mem {entries : List Specialized} {key : Key} {selected : Specialized}
    (found : entries.filter (fun entry => decide (entry.key = key)) = [selected]) : key ∈ entries.map (·.key) := by
  have member : selected ∈ entries.filter (fun entry => decide (entry.key = key)) := by rw [found]; simp
  obtain ⟨member, same⟩ := List.mem_filter.mp member
  exact List.mem_map.mpr ⟨selected, member, of_decide_eq_true same⟩

/-- Both root insertion and existing-root acceptance preserve exact carriers.
The public action itself supplies uniqueness and full-record comparison; no
additional validity or uniqueness premise is needed. -/
theorem extend {program : CheckedProgram} {plan : Plan} {root : Specialized} {edge : CallEdge}
    {budget : Nat} {outcome : Outcome}
    (accepted : extendCompletePlan program plan root edge budget = .ok outcome) :
    SourceCompilationPlan.exactSpecialization outcome.plan root.key = .ok root ∧
    ∀ key selected, SourceCompilationPlan.exactSpecialization plan key = .ok selected →
      SourceCompilationPlan.exactSpecialization outcome.plan key = .ok selected := by
  unfold extendCompletePlan at accepted
  obtain ⟨checked, unique, accepted⟩ := bind_ok accepted
  cases checked
  have unique := unique_keys unique
  split at accepted <;> try contradiction
  have finish : ∀ (entries : List Specialized) (requests : List Request) (calls : List CallEdge) (references : List ReferenceEdge),
      entries.filter (fun entry => decide (entry.key = root.key)) = [root] →
      (∀ key selected, SourceCompilationPlan.exactSpecialization plan key = .ok selected →
        entries.filter (fun entry => decide (entry.key = key)) = [selected]) →
      runAux program plan.seedKeys requests (entries.map (·.key)) entries calls references budget = .ok outcome →
      SourceCompilationPlan.exactSpecialization outcome.plan root.key = .ok root ∧
        ∀ key selected, SourceCompilationPlan.exactSpecialization plan key = .ok selected →
          SourceCompilationPlan.exactSpecialization outcome.plan key = .ok selected := by
    intro entries requests calls references rootFilter oldFilters completed
    constructor
    · exact exact_of_filter ((runAux_filter (key_mem rootFilter) completed).trans rootFilter)
    · intro key selected given
      have found := oldFilters key selected given
      exact exact_of_filter ((runAux_filter (key_mem found) completed).trans found)
  dsimp only at accepted
  split at accepted
  · rename_i missing
    simp only [pure, Except.pure, bind, Except.bind] at accepted
    obtain ⟨⟨requests, calls, references⟩, _, accepted⟩ := bind_ok accepted
    apply finish _ _ _ _ ?_ ?_ accepted
    · have empty := none_filter missing
      simp only [List.filter_append, empty, List.filter_cons, decide_true, if_true, List.filter_nil, List.nil_append]
    · intro key selected given
      have empty := none_filter missing
      have selectedFilter := exact_filter given
      have different : root.key ≠ key := by
        intro same
        rw [same, selectedFilter] at empty
        cases empty
      simpa only [List.filter_append, List.filter_cons, decide_eq_false different, Bool.false_eq_true, if_false,
        List.filter_nil, List.append_nil] using selectedFilter
  · rename_i previous found
    split at accepted <;> try contradiction
    rename_i same
    have equal := CallableSpecializationEquality.eq_of_beq same
    subst previous
    simp only [pure, Except.pure, bind, Except.bind] at accepted
    obtain ⟨⟨requests, calls, references⟩, _, accepted⟩ := bind_ok accepted
    exact finish _ _ _ _ (find_filter unique found) (fun _ _ given => exact_filter given) accepted

/-- Completion exposes the supplied root through the emitter's exact lookup. -/
theorem complete_root {program : CheckedProgram} {plan completed : Plan} {root : Specialized} {edge : CallEdge}
    {budget : Nat}
    (accepted : extendCompletePlan program plan root edge budget = .ok (.complete completed)) :
    SourceCompilationPlan.exactSpecialization completed root.key = .ok root := (extend accepted).1

/-- Existing exact selections survive the real public extension action. -/
theorem selected_after {program : CheckedProgram} {plan : Plan} {root : Specialized} {edge : CallEdge}
    {budget : Nat} {outcome : Outcome} {key : Key} {selected : Specialized}
    (accepted : extendCompletePlan program plan root edge budget = .ok outcome)
    (before : SourceCompilationPlan.exactSpecialization plan key = .ok selected) :
    SourceCompilationPlan.exactSpecialization outcome.plan key = .ok selected := (extend accepted).2 _ _ before

private theorem call_key {plan : Plan} {caller target selected : Key} {id : ExpressionId}
    (accepted : SourceCompilationPlan.exactCallKey plan caller id target = .ok selected) : selected = target := by
  unfold SourceCompilationPlan.exactCallKey at accepted
  split at accepted <;> try contradiction
  rename_i edge edges
  cases accepted
  have member : edge ∈ plan.callEdges.filter (fun edge => decide (edge.caller = caller) && decide (edge.occurrence = id) && decide (edge.callee = target)) := by rw [edges]; simp
  have same := (List.mem_filter.mp member).2
  simp only [Bool.and_eq_true, decide_eq_true_eq] at same
  exact same.2

/-- The emitted step's selected carrier is the complete checked method root,
when its actual plan is the returned extension. No identity-only cast occurs. -/
theorem step_specialized {program : CheckedProgram} {project : CallableCoercionSpine.Projector}
    {context : CallableCoercionSpine.Context} {caller : Specialized}
    {available : CallableCoercionSpine.RuntimeEvidence} {scope : CallableCoercionSpine.Scope}
    {node : ExpressionNode} {policy : SourceCoreFunctions.CallablePolicy}
    {input output : CallableCoercionSpine.Lowered} {coercion : CoercionStep} {call : CallableCoercionSpine.Call}
    (step : CallableCoercionSpine.Step program project context caller available scope node policy input coercion output call)
    {before : Plan} {edge : CallEdge} {budget : Nat}
    (extended : extendCompletePlan program before step.method.specialized edge budget = .ok (.complete context.plan)) :
    step.specialized = step.method.specialized := by
  have selected := complete_root extended
  have sameKey := call_key step.edge
  have emitted := step.selected
  rw [sameKey] at emitted
  exact Except.ok.inj (emitted.symm.trans selected)

end Solcore.SourceSemantics.CoreLowering.CallableCoercionPlanProvenance
