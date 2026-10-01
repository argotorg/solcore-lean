import Solcore.SourceSemantics.CoreLowering.CallableAncestryTransitions

/-! A mathematical finite key universe bounds reachable ancestry states.
The production worklist computes its cardinality arithmetically and never
enumerates this universe. This file keeps the cardinality argument separate
from successful preparation's already-proved all-frame lookup guarantee. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableAncestryCardinality
open Frontend SourceInference TypeSystem CallableAncestryMetadata CallableAncestryCache CallableAncestryProfiles
abbrev Inputs := @SourceCoreCallableAncestryPreparation.Inputs
abbrev NativeState := SourceCoreCallableAncestryCache.State
abbrev NativeKey := SourceCoreCallableAncestryCache.Key

def contexts {checked : Checked} {base : Base checked} (inputs : Inputs base) : List Substitution :=
  [] :: inputs.views.entries.map (·.view.cumulative)

def keysFor (actives : List Substitution) (root : NativeState) : List NativeKey :=
  actives.flatMap fun active =>
    (FiniteProfiles.profiles root.key.requirements.flatten (root.key.requirements.map List.length)).map
      (fun profile => ⟨root.owner, active, profile⟩)

/-- Used in proofs only. Actual preparation visits just reached states. -/
def keySpace {checked : Checked} {base : Base checked} (inputs : Inputs base) (roots : List NativeState) : List NativeKey :=
  roots.flatMap (keysFor (contexts inputs))

private theorem length_flatMap_const {α β : Type} (items : List α) (f : α → List β) (count : Nat)
    (constant : ∀ item ∈ items, (f item).length = count) : (items.flatMap f).length = items.length * count := by
  induction items with
  | nil => simp
  | cons head tail ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons,
      constant head (by simp), ih (fun item member => constant item (by simp [member]))]
    simp [Nat.add_mul, Nat.add_comm]

theorem spines_length (alphabet : List RequirementId) (count : Nat) :
    (FiniteProfiles.spines alphabet count).length = alphabet.length ^ count := by
  induction count with
  | zero => simp [FiniteProfiles.spines]
  | succ count ih =>
    rw [FiniteProfiles.spines, length_flatMap_const _ _ (alphabet.length ^ count)]
    · simp [Nat.pow_succ, Nat.mul_comm]
    · intro item _; simpa using ih

theorem profiles_length (alphabet : List RequirementId) (lengths : List Nat) :
    (FiniteProfiles.profiles alphabet lengths).length = alphabet.length ^ lengths.sum := by
  induction lengths with
  | nil => simp [FiniteProfiles.profiles]
  | cons first rest ih =>
    rw [FiniteProfiles.profiles, length_flatMap_const _ _ (alphabet.length ^ rest.sum)]
    · simp [spines_length, Nat.pow_add]
    · intro item _; simpa using ih

theorem keysFor_length (actives : List Substitution) (root : NativeState) :
    (keysFor actives root).length = actives.length * root.key.requirements.flatten.length ^ root.key.requirements.flatten.length := by
  unfold keysFor
  rw [length_flatMap_const _ _ (root.key.requirements.flatten.length ^ root.key.requirements.flatten.length)]
  intro active _
  simp [profiles_length, List.length_flatten]

private theorem fold_sum {α : Type} (items : List α) (f : α → Nat) (initial : Nat) :
    items.foldl (fun acc item => acc + f item) initial = initial + (items.map f).sum := by
  induction items generalizing initial with
  | nil => simp
  | cons head tail ih => simp [ih, Nat.add_assoc]

/-- The implementation's arithmetic capacity is exactly the length of the
finite overapproximation. Duplicate roots/contexts/IDs only enlarge it. -/
theorem universe_length {checked : Checked} {base : Base checked} (inputs : Inputs base)
    (initial : SourceCoreCallableAncestryCache.Table) :
    (keySpace inputs initial.states).length = SourceCoreCallableAncestryPreparation.capacity inputs initial := by
  simp only [keySpace, List.length_flatMap, keysFor_length, contexts, List.length_cons, List.length_map,
    SourceCoreCallableAncestryPreparation.capacity, fold_sum, Nat.zero_add]

theorem active_member {checked : Checked} {base : Base checked} {owned : Owned base}
    (inputs : Inputs base) {frame : ContextFrame} {state : CallableAncestryMetadata.State}
    (authenticated : Authenticates owned frame (some state)) : state.active ∈ contexts inputs := by
  generalize resultEq : some state = result at authenticated
  induction authenticated generalizing state with
  | empty => cases resultEq
  | named receipt => cases resultEq; simp [contexts, Named.state]
  | lambda _ _ _ ih => exact ih resultEq
  | view _ receipt step _ =>
    cases resultEq
    have member : receipt.entry ∈ owned.views.entries := List.mem_of_find?_eq_some receipt.selected
    rw [step.cumulative]
    simp only [contexts, CallableAncestryTransitions.views_eq owned inputs, List.mem_cons]
    exact .inr (List.mem_map.mpr ⟨receipt.entry, member, rfl⟩)

def CoversRoots {checked : Checked} {base : Base checked} (owned : Owned base) (roots : List NativeState) : Prop :=
  ∀ {id} (receipt : Named owned id), nativeState receipt.state ∈ roots

theorem key_member {checked : Checked} {base : Base checked} {owned : Owned base}
    (inputs : Inputs base) {roots : List NativeState} (covered : CoversRoots owned roots)
    {frame : ContextFrame} {state : CallableAncestryMetadata.State}
    (authenticated : Authenticates owned frame (some state)) : (nativeState state).key ∈ keySpace inputs roots := by
  obtain ⟨id, named, owner, bounded, lengths⟩ := Authenticates.original_bound authenticated
  apply List.mem_flatMap.mpr
  refine ⟨nativeState named.state, covered named, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨state.active, active_member inputs authenticated, ?_⟩
  have profile := FiniteProfiles.profile_member (requirementProfile state.source) bounded
  rw [lengths] at profile
  apply List.mem_map.mpr
  refine ⟨requirementProfile state.source, profile, ?_⟩
  simp only [nativeState, SourceCoreCallableAncestryCache.State.key, ← owner]
  rfl

/-- Any distinct reached-state keys fit the computed capacity. Every source
state must have an actual owned recipe; mere native typing is insufficient. -/
theorem states_bounded {checked : Checked} {base : Base checked} {owned : Owned base}
    (inputs : Inputs base) (initial : SourceCoreCallableAncestryCache.Table)
    (covered : CoversRoots owned initial.states) (states : List NativeState)
    (unique : (states.map (·.key)).Nodup)
    (authentic : ∀ state ∈ states, ∃ frame, Authenticates owned frame (some (sourceState state))) :
    states.length ≤ SourceCoreCallableAncestryPreparation.capacity inputs initial := by
  rw [← universe_length]
  have subset : states.map (·.key) ⊆ keySpace inputs initial.states := by
    intro key member
    obtain ⟨state, included, rfl⟩ := List.mem_map.mp member
    obtain ⟨frame, authenticated⟩ := authentic state included
    exact key_member inputs covered authenticated
  simpa only [List.length_map] using unique.length_le_of_subset subset

end Solcore.SourceSemantics.CoreLowering.CallableAncestryCardinality
