import Solcore.SourceSemantics.CoreLowering.CallableAncestryComposition

/-! Finite source substitutions under arbitrarily many owned read views.
These substitutions describe retained source metadata, separately from the
finite native codebook's compilation contexts. No restriction to an existing
`view.cumulative` is used. Ordered bindings are retained exactly.

The list-valued key space below is a mathematical overapproximation only. A
runtime/preparation worklist should deduplicate reached keys; it need not
enumerate the Cartesian key space. No runtime source evaluator or evidence
resolver participates in these facts. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableAncestrySourceActive
open Frontend SourceInference TypeSystem CallableAncestryMetadata
open CallableAncestryProfiles.SourceComposition

/-- Actual owned view factories are the only generators of new assignments. -/
def generators {program : CheckedProgram} {plan : SourceCoreCallableViews.Plan}
    (table : SourceCoreCallableViews.Table program plan) : List Substitution :=
  table.entries.map (·.view.ownSubstitution)

def alphabet (choices : List Substitution) : List (TypeVarId × Ty) := choices.flatten

def domainAlphabet (choices : List Substitution) : List TypeVarId :=
  ((alphabet choices).map Prod.fst).eraseDups

structure GeneratorsValid (choices : List Substitution) : Prop where
  closed : ∀ substitution ∈ choices, RangesClosed substitution
  unique : ∀ substitution ∈ choices, substitution.domain.Nodup

/-- Both closure and domain uniqueness are extracted from the actual matcher
called by the retained witness-factory receipt. -/
theorem generators_valid {program : CheckedProgram} {plan : SourceCoreCallableViews.Plan}
    (table : SourceCoreCallableViews.Table program plan) : GeneratorsValid (generators table) := by
  constructor
  · intro substitution member
    obtain ⟨entry, _, rfl⟩ := List.mem_map.mp member
    exact matchClosed_ranges (witnesses_matched entry.view.exactFactory)
  · intro substitution member
    obtain ⟨entry, _, rfl⟩ := List.mem_map.mp member
    have matched := SourceSpecialization.matchClosedSchemeInstance?_sound
      (witnesses_matched entry.view.exactFactory)
    rw [matched.2.2.1]
    exact matched.2.1

/-- The source substitution may combine views from distinct lexical contexts.
This unrestricted finite closure overapproximates any later paired-frame graph. -/
inductive Reachable (choices : List Substitution) : Substitution → Prop where
  | empty : Reachable choices []
  | step {before own : Substitution} (previous : Reachable choices before)
      (selected : own ∈ choices) : Reachable choices (own.compose before)

theorem Reachable.foldl {choices : List Substitution} {initial : Substitution}
    (initialReachable : Reachable choices initial) (steps : List Substitution)
    (selected : ∀ own ∈ steps, own ∈ choices) :
    Reachable choices (steps.foldl (fun active own => own.compose active) initial) := by
  induction steps generalizing initial with
  | nil => exact initialReachable
  | cons head tail ih =>
    exact ih (.step initialReachable (selected head (by simp))) (fun own member => selected own (by simp [member]))

/-- Closed older ranges do not change when a later substitution is applied.
Composition therefore appends only genuinely new variables. -/
theorem compose_closed {older newer : Substitution} (closed : RangesClosed older) :
    newer.compose older = older ++ newer.filter (fun entry => !(entry.1 ∈ older.domain)) := by
  unfold Substitution.compose
  have unchanged : older.map (fun entry => (entry.1, newer.apply entry.2)) = older := by
    calc
      _ = older.map id := by
        apply List.map_congr_left
        intro entry member
        rw [fixed (closed entry member) newer]
        rfl
      _ = older := List.map_id _
  rw [unchanged]
  rfl

theorem compose_entries {older newer : Substitution} (closed : RangesClosed older) :
    newer.compose older ⊆ older ++ newer := by
  rw [compose_closed closed]
  intro entry member
  rcases List.mem_append.mp member with old | added
  · exact List.mem_append_left _ old
  · exact List.mem_append_right _ (List.mem_filter.mp added).1

theorem Reachable.closed {choices : List Substitution} (valid : GeneratorsValid choices)
    {active : Substitution} (reachable : Reachable choices active) : RangesClosed active := by
  induction reachable with
  | empty => exact RangesClosed.empty
  | step _ selected ih => exact RangesClosed.compose ih (valid.closed _ selected)

theorem Reachable.domain_unique {choices : List Substitution} (valid : GeneratorsValid choices)
    {active : Substitution} (reachable : Reachable choices active) : active.domain.Nodup := by
  induction reachable with
  | empty => exact .nil
  | step _ selected ih => exact Substitution.domain_compose_nodup (valid.unique _ selected) ih

/-- Entry provenance is stronger than merely preserving possible range types:
every exact `(variable, closed type)` pair comes from one owned generator. -/
theorem Reachable.entries {choices : List Substitution} (valid : GeneratorsValid choices)
    {active : Substitution} (reachable : Reachable choices active) : active ⊆ alphabet choices := by
  induction reachable with
  | empty => simp
  | @step before own previous selected ih =>
    intro entry member
    rcases List.mem_append.mp (compose_entries (previous.closed valid) member) with old | added
    · exact ih old
    · exact List.mem_flatten.mpr ⟨own, selected, added⟩

theorem Reachable.range_alphabet {choices : List Substitution} (valid : GeneratorsValid choices)
    {active : Substitution} (reachable : Reachable choices active) :
    active.map Prod.snd ⊆ (alphabet choices).map Prod.snd := by
  intro type member
  obtain ⟨entry, included, rfl⟩ := List.mem_map.mp member
  exact List.mem_map.mpr ⟨entry, reachable.entries valid included, rfl⟩

theorem Reachable.domain_alphabet {choices : List Substitution} (valid : GeneratorsValid choices)
    {active : Substitution} (reachable : Reachable choices active) : active.domain ⊆ domainAlphabet choices := by
  intro metavariable member
  obtain ⟨entry, included, rfl⟩ := List.mem_map.mp member
  simp only [domainAlphabet, List.mem_eraseDups]
  exact List.mem_map.mpr ⟨entry, reachable.entries valid included, rfl⟩

theorem Reachable.length_bound {choices : List Substitution} (valid : GeneratorsValid choices)
    {active : Substitution} (reachable : Reachable choices active) :
    active.length ≤ (domainAlphabet choices).length := by
  have bounded := (reachable.domain_unique valid).length_le_of_subset (reachable.domain_alphabet valid)
  simpa only [Substitution.domain, List.length_map] using bounded

/-- Lists preserve exact substitution order. The finite mathematical space
also includes unreachable lists; no normalization of ordered keys is assumed. -/
def lists (entries : List (TypeVarId × Ty)) : Nat → List Substitution
  | 0 => [[]]
  | count + 1 => entries.flatMap fun entry => (lists entries count).map (entry :: ·)

def keySpace (choices : List Substitution) : List Substitution :=
  (List.range ((domainAlphabet choices).length + 1)).flatMap (lists (alphabet choices))

def capacity (choices : List Substitution) : Nat :=
  ((List.range ((domainAlphabet choices).length + 1)).map ((alphabet choices).length ^ ·)).sum

theorem lists_member {entries : List (TypeVarId × Ty)} (active : Substitution)
    (bounded : active ⊆ entries) : active ∈ lists entries active.length := by
  induction active with
  | nil => simp [lists]
  | cons head tail ih =>
    apply List.mem_flatMap.mpr
    refine ⟨head, bounded (by simp), ?_⟩
    apply List.mem_map.mpr
    exact ⟨tail, ih (fun _ member => bounded (by simp [member])), rfl⟩

private theorem length_flatMap_const {α β : Type} (items : List α) (f : α → List β) (count : Nat)
    (constant : ∀ item ∈ items, (f item).length = count) : (items.flatMap f).length = items.length * count := by
  induction items with
  | nil => simp
  | cons head tail ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons,
      constant head (by simp), ih (fun item member => constant item (by simp [member]))]
    simp [Nat.add_mul, Nat.add_comm]

theorem lists_length (entries : List (TypeVarId × Ty)) (count : Nat) :
    (lists entries count).length = entries.length ^ count := by
  induction count with
  | zero => simp [lists]
  | succ count ih =>
    rw [lists, length_flatMap_const _ _ (entries.length ^ count)]
    · simp [Nat.pow_succ, Nat.mul_comm]
    · intro entry _; simpa using ih

theorem keySpace_length (choices : List Substitution) : (keySpace choices).length = capacity choices := by
  simp only [keySpace, List.length_flatMap, lists_length, capacity]

theorem Reachable.keySpace_member {choices : List Substitution} (valid : GeneratorsValid choices)
    {active : Substitution} (reachable : Reachable choices active) : active ∈ keySpace choices := by
  apply List.mem_flatMap.mpr
  refine ⟨active.length, List.mem_range.mpr (by have bounded := reachable.length_bound valid; omega), ?_⟩
  exact lists_member active (reachable.entries valid)

theorem reached_count_bound {choices : List Substitution} (valid : GeneratorsValid choices)
    (reached : List Substitution) (unique : reached.Nodup)
    (authentic : ∀ active ∈ reached, Reachable choices active) : reached.length ≤ capacity choices := by
  rw [← keySpace_length]
  exact unique.length_le_of_subset (fun _ member => (authentic _ member).keySpace_member valid)

/-- The public bound specializes directly to the exact substitutions retained
by the actual owned local-read factories. -/
theorem owned_reached_count_bound {program : CheckedProgram} {plan : SourceCoreCallableViews.Plan}
    (table : SourceCoreCallableViews.Table program plan) (reached : List Substitution)
    (unique : reached.Nodup) (authentic : ∀ active ∈ reached, Reachable (generators table) active) :
    reached.length ≤ capacity (generators table) := reached_count_bound (generators_valid table) reached unique authentic

/-- A closed source context cannot be enlarged by a generator whose variables
are already present. Existing values and their order are unchanged. -/
theorem compose_of_domain_subset {older newer : Substitution} (closed : RangesClosed older)
    (included : newer.domain ⊆ older.domain) : newer.compose older = older := by
  rw [compose_closed closed]
  have empty : newer.filter (fun entry => !(entry.1 ∈ older.domain)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro entry member
    have present := included (List.mem_map.mpr ⟨entry, member, rfl⟩)
    simp [present]
  simp [empty]

theorem compose_idempotent {older newer : Substitution}
    (oldClosed : RangesClosed older) (newClosed : RangesClosed newer) :
    newer.compose (newer.compose older) = newer.compose older := by
  apply compose_of_domain_subset (RangesClosed.compose oldClosed newClosed)
  intro metavariable member
  exact (Substitution.mem_domain_compose_iff newer older metavariable).mpr (.inr member)

end Solcore.SourceSemantics.CoreLowering.CallableAncestrySourceActive
