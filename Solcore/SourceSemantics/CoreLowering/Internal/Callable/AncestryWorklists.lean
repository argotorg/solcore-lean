import Solcore.SourceSemantics.CoreLowering.Internal.Callable.Ancestry
import Solcore.Frontend.SourceCoreCallableAncestryReadRecipes
import Solcore.Frontend.SourceCoreCallableAncestryCache
import Solcore.Frontend.SourceCoreCallableAncestryPreparation
import Solcore.Frontend.SourceCoreCallableAncestryPairedPreparation

/-!
# Callable ancestry: active sources and worklists

Active sources, read recipes, caches, transitions, cardinality, paired profiles and worklists.

These are apart from `Callable/Ancestry` on purpose. The matcher of `lists` is alpha-equal to the one of `spines`, so in one file Lean would reuse that one, and the equations of `lists` would take their variable names from it.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableAncestrySourceActive
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableAncestryReadRecipes
/-! Paired read-caller and lexical-principal metadata laws. The witness factory
reads the caller's occurrence metadata; substitution and requirement rewriting
act on the lexical principal source. Only the substitution is determined by
matching types. The witnesses retain the caller's actual requirement IDs.

These are laws about sealed preparation receipts, not runtime-history or
capture-ownership proofs. Independent dynamic instantiation does not rewrite
requirement IDs, so the comparison with it erases those lists only. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableAncestryReadRecipes
open Frontend SourceInference TypeSystem
open CallableAncestryMetadata CallableAncestryProfiles
open CallableAncestryProfiles.SourceComposition

/-- Matching fixes the substitution without equating dictionaries or
occurrence IDs. Both callers and available evidence may differ. -/
theorem factory_substitution_eq
    {leftCaller rightCaller : SourceSpecialization.SpecializedFunction}
    {leftAvailable rightAvailable : SourceCompilationPlan.EvidenceEnvironment}
    {leftBinder rightBinder : TypedBinder} {leftNode rightNode : ExpressionNode}
    {leftSubstitution rightSubstitution : Substitution}
    {leftWitnesses rightWitnesses : List Witness}
    (left : SourceCompilationPlan.localRequirementWitnesses leftCaller leftAvailable leftBinder leftNode =
      .ok (leftSubstitution, leftWitnesses))
    (right : SourceCompilationPlan.localRequirementWitnesses rightCaller rightAvailable rightBinder rightNode =
      .ok (rightSubstitution, rightWitnesses))
    (scheme : leftBinder.scheme = rightBinder.scheme)
    (rawType : leftNode.rawType = rightNode.rawType) : leftSubstitution = rightSubstitution := by
  have matched := witnesses_matched left
  rw [scheme, rawType] at matched
  exact Option.some.inj (matched.symm.trans (witnesses_matched right))

/-- This derives equality from the actual factories and the two matching
inputs. It does not use the receipt's separate `substitutionExact` check. -/
theorem read_substitution_from_metadata
    {checked : SourceCoreCallableAncestryReadRecipes.Checked} {base : SourceCoreCallableAncestryReadRecipes.Base checked} {inputs : SourceCoreCallableAncestryReadRecipes.Inputs base}
    {caller : SourceCoreCallableAncestryReadRecipes.State} {id target : Core.Word} (read : SourceCoreCallableAncestryReadRecipes.Read inputs caller id target)
    (scheme : read.binder.scheme =
      (read.entry.view.principal.binder.applySubstitution read.entry.view.parentActive).scheme)
    (rawType : read.node.rawType = read.entry.view.rawRead.rawType) :
    read.substitution = read.entry.view.ownSubstitution :=
  factory_substitution_eq read.factory read.entry.view.exactFactory scheme rawType

section Read
variable {checked : SourceCoreCallableAncestryReadRecipes.Checked} {base : SourceCoreCallableAncestryReadRecipes.Base checked} {inputs : SourceCoreCallableAncestryReadRecipes.Inputs base}
  {caller : SourceCoreCallableAncestryReadRecipes.State} {id target : Core.Word} (read : SourceCoreCallableAncestryReadRecipes.Read inputs caller id target)

theorem read_member : read.entry ∈ inputs.views.entries :=
  List.mem_of_find?_eq_some read.selected

/-- The generator receipt can also be derived from the two matching inputs,
without using the read factory's explicit substitution equality check. -/
theorem read_generator_from_metadata
    (scheme : read.binder.scheme =
      (read.entry.view.principal.binder.applySubstitution read.entry.view.parentActive).scheme)
    (rawType : read.node.rawType = read.entry.view.rawRead.rawType) :
    read.substitution ∈ CallableAncestrySourceActive.generators inputs.views := by
  rw [read_substitution_from_metadata read scheme rawType]
  exact List.mem_map.mpr ⟨read.entry, read_member read, rfl⟩

/-- Successful read authentication selects a generator from the actual owned
table. The checked equality is sufficient even before metadata alignment has
been obtained from the native/source occurrence correspondence. -/
theorem read_generator : read.substitution ∈ CallableAncestrySourceActive.generators inputs.views := by
  rw [read.substitutionExact]
  exact List.mem_map.mpr ⟨read.entry, read_member read, rfl⟩

theorem after_reachable (lexical : SourceCoreCallableAncestryReadRecipes.State)
    (reachable : CallableAncestrySourceActive.Reachable (CallableAncestrySourceActive.generators inputs.views) lexical.metadata.active) :
    CallableAncestrySourceActive.Reachable (CallableAncestrySourceActive.generators inputs.views) (read.after lexical).metadata.active :=
  .step reachable (read_generator read)

theorem after_finite (lexical : SourceCoreCallableAncestryReadRecipes.State)
    (reachable : CallableAncestrySourceActive.Reachable (CallableAncestrySourceActive.generators inputs.views) lexical.metadata.active) :
    RangesClosed (read.after lexical).metadata.active ∧
      (read.after lexical).metadata.active.domain.Nodup ∧
      (read.after lexical).metadata.active.length ≤ (CallableAncestrySourceActive.domainAlphabet (CallableAncestrySourceActive.generators inputs.views)).length ∧
      (read.after lexical).metadata.active ∈ CallableAncestrySourceActive.keySpace (CallableAncestrySourceActive.generators inputs.views) := by
  have valid := CallableAncestrySourceActive.generators_valid inputs.views
  have reached := after_reachable read lexical reachable
  exact ⟨reached.closed valid, reached.domain_unique valid, reached.length_bound valid, reached.keySpace_member valid⟩

/-- The source-active field composes with lexical creation metadata. No
equality with the native compilation context is asserted. -/
theorem after_contexts (lexical : SourceCoreCallableAncestryReadRecipes.State) :
    (read.after lexical).metadata.owner = lexical.metadata.owner ∧
      (read.after lexical).metadata.active = read.substitution.compose lexical.metadata.active ∧
      (read.after lexical).nativeActive = read.entry.view.cumulative := ⟨rfl, rfl, rfl⟩

theorem actual_ids_from_caller {ids : List RequirementId} (bounded : Bounded ids caller.metadata.source) :
    ∀ witness ∈ read.witnesses, witness.actualRequirement ∈ ids := by
  intro witness member
  have selected := witnesses_actual_subset read.factory witness member
  have owned := ordinary_requirements_subset read.requirementsSelected witness.actualRequirement selected
  exact lookup_requirements_bounded bounded read.found _ owned

theorem after_bounded (lexical : SourceCoreCallableAncestryReadRecipes.State) {ids : List RequirementId}
    (callerBounded : Bounded ids caller.metadata.source) (lexicalBounded : Bounded ids lexical.metadata.source) :
    Bounded ids (read.after lexical).metadata.source :=
  bounded_rewrite (bounded_substitute lexicalBounded read.substitution) (actual_ids_from_caller read callerBounded)

/-- A common finite alphabet may be formed from separate caller and lexical
alphabets. No unproved same-owner alphabet identity is needed. -/
theorem after_bounded_union (lexical : SourceCoreCallableAncestryReadRecipes.State) {callerIds lexicalIds : List RequirementId}
    (callerBounded : Bounded callerIds caller.metadata.source)
    (lexicalBounded : Bounded lexicalIds lexical.metadata.source) :
    Bounded (callerIds ++ lexicalIds) (read.after lexical).metadata.source := by
  apply after_bounded read lexical
  · intro spine member requirement occurs
    exact List.mem_append_left _ (callerBounded spine member requirement occurs)
  · intro spine member requirement occurs
    exact List.mem_append_right _ (lexicalBounded spine member requirement occurs)

theorem after_spines (lexical : SourceCoreCallableAncestryReadRecipes.State) :
    (requirementProfile (read.after lexical).metadata.source).map List.length =
      (requirementProfile lexical.metadata.source).map List.length := by
  change (requirementProfile (SourceTypedRuntime.rewriteLocalRequirements _
    (TypedSource.applySubstitution _ _))).map List.length = _
  rw [lengths_rewrite, profile_substitute]

theorem after_canonical (lexical : SourceCoreCallableAncestryReadRecipes.State) (original : TypedSource)
    (closed : RangesClosed lexical.metadata.active)
    (canonical : eraseRequirements lexical.metadata.source =
      eraseRequirements (original.applySubstitution lexical.metadata.active)) :
    eraseRequirements (read.after lexical).metadata.source =
      eraseRequirements (original.applySubstitution (read.after lexical).metadata.active) := by
  change eraseRequirements (SourceTypedRuntime.rewriteLocalRequirements _
    (TypedSource.applySubstitution _ _)) = eraseRequirements (original.applySubstitution (read.substitution.compose _))
  rw [rewrite_erased, erase_substitute, canonical, ← erase_substitute, source read.substitution _ closed]

end Read

section Applied
variable {checked : SourceCoreCallableAncestryReadRecipes.Checked} {base : SourceCoreCallableAncestryReadRecipes.Base checked} {inputs : SourceCoreCallableAncestryReadRecipes.Inputs base}
  {caller : SourceCoreCallableAncestryReadRecipes.State} {id target : Core.Word} {read : SourceCoreCallableAncestryReadRecipes.Read inputs caller id target}
  {lexical : SourceCoreCallableAncestryReadRecipes.State} (applied : SourceCoreCallableAncestryReadRecipes.Applied read lexical)

/-- The independently defined principal carrier for comparison of metadata.
The caller supplies a definition context, original binder, and captured source
locations. This definition does not authenticate those inputs. -/
def principal (context : Context) (binder : TypedBinder) (captured : Dynamic.Environment) : Dynamic.GeneralizedClosure :=
  Dynamic.GeneralizedClosure.ofDirectLambda context lexical.metadata.source captured binder
    read.entry.view.principal.initializer applied.parameters applied.resultType applied.body

theorem instantiated_metadata (context : Context) (binder : TypedBinder) (captured : Dynamic.Environment)
    (evidence : Dynamic.EvidenceEnvironment) :
    let result := (principal applied context binder captured).instantiate read.substitution evidence
    eraseRequirements (read.after lexical).metadata.source = eraseRequirements result.source ∧
      ExpressionForm.lambda result.parameters result.resultType result.body = read.template.node.form ∧
      result.captured = captured ∧ result.evidence = evidence := by
  refine ⟨?_, applied.nativeHeader, rfl, rfl⟩
  exact rewrite_erased read.witnesses (lexical.metadata.source.applySubstitution read.substitution)

/-- The exported instance wraps the original lexical closure. Its raw header,
source, evidence, and complete ordered capture list remain unmodified. The
native target's closed header is used only when applying that instance. -/
theorem export_original (captured : SourceTypedRuntime.Environment)
    (evidence : SourceCompilationPlan.EvidenceEnvironment) :
    applied.sourceValue captured evidence = .instantiated read.substitution read.witnesses
      (.closure applied.parameters applied.resultType applied.body lexical.metadata.source lexical.metadata.owner
        captured evidence) := rfl

theorem export_captures_injective {left right : SourceTypedRuntime.Environment}
    {leftEvidence rightEvidence : SourceCompilationPlan.EvidenceEnvironment}
    (same : applied.sourceValue left leftEvidence = applied.sourceValue right rightEvidence) :
    left = right ∧ leftEvidence = rightEvidence := by
  simpa only [SourceCoreCallableAncestryReadRecipes.Applied.sourceValue, SourceTypedRuntime.Value.instantiated.injEq,
    SourceTypedRuntime.Value.closure.injEq, true_and] using same

end Applied
end Solcore.SourceSemantics.CoreLowering.CallableAncestryReadRecipes
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableAncestryCache
/-! A completed finite transition table covers every independently
authenticated metadata frame, including arbitrary repeated lambda ancestry.
The closure certificate is about named/lambda/view metadata transitions, not
source or Core execution. Constructing it from the actual reachable worklist
is a separate preparation obligation; no arbitrary traversal fuel or supplied
list of runtime frames appears in these theorems. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableAncestryCache
open Frontend SourceInference TypeSystem CallableAncestryMetadata
abbrev Table := SourceCoreCallableAncestryCache.Table
abbrev State := CallableAncestryMetadata.State

def nativeState (state : State) : SourceCoreCallableAncestryCache.State :=
  ⟨state.owner, state.active, state.source⟩

def sourceState (state : SourceCoreCallableAncestryCache.State) : State :=
  ⟨state.owner, state.active, state.source⟩

@[simp] theorem source_native (state : State) : sourceState (nativeState state) = state := rfl
@[simp] theorem native_source (state : SourceCoreCallableAncestryCache.State) : nativeState (sourceState state) = state := rfl

theorem native_injective {left right : State} (same : nativeState left = nativeState right) : left = right :=
  congrArg sourceState same

/-- Every selected row is an owned metadata transition. These are finite-row
obligations; they contain no premise that a source/Core program has executed. -/
structure Sound {checked : Checked} {base : Base checked} (owned : Owned base) (table : Table) : Prop where
  named : ∀ {id position}, table.namedAt? id = some position →
    ∃ receipt : Named owned id, table.stateAt? position = some (nativeState receipt.state)
  lambda : ∀ {position state id}, table.stateAt? position = some (nativeState state) →
    table.lambdaAllowed position id = true → ∃ receipt : LambdaAt owned id, Nonempty (LambdaSource receipt state)
  view : ∀ {position state id target destination}, table.stateAt? position = some (nativeState state) →
    table.viewAt? position id target = some destination →
      ∃ (receipt : ViewAt owned id target) (step : ViewStep receipt state),
        table.stateAt? destination = some (nativeState step.after)

/-- Closure of a completed worklist. Each matching view factory is represented
at every reached state. Lambda edges keep that exact state; named edges seed
every owned named source. No condition mentions whole recursive frames. -/
structure Closed {checked : Checked} {base : Base checked} (owned : Owned base) (table : Table) : Prop where
  named : ∀ {id} (receipt : Named owned id), ∃ position,
    table.namedAt? id = some position ∧ table.stateAt? position = some (nativeState receipt.state)
  lambda : ∀ {position state id}, table.stateAt? position = some (nativeState state) →
    ∀ (receipt : LambdaAt owned id), LambdaSource receipt state → table.lambdaAllowed position id = true
  view : ∀ {position state id target}, table.stateAt? position = some (nativeState state) →
    ∀ (receipt : ViewAt owned id target) (step : ViewStep receipt state), ∃ destination,
      table.viewAt? position id target = some destination ∧ table.stateAt? destination = some (nativeState step.after)

structure Prepared {checked : Checked} {base : Base checked} (owned : Owned base) where private mk ::
  table : Table
  sound : Sound owned table
  closed : Closed owned table

/-- Proof-facing completion boundary. Actual factory preparation must produce
both certificates before its table can use the all-frame theorem below. -/
def certify {checked : Checked} {base : Base checked} {owned : Owned base}
    (table : Table) (sound : Sound owned table) (closed : Closed owned table) : Prepared owned :=
  ⟨table, sound, closed⟩

def IndexMeaning {checked : Checked} {base : Base checked} (owned : Owned base) (table : Table)
    (frame : ContextFrame) : Option Nat → Prop
  | none => Authenticates owned frame none
  | some position => ∃ state, table.stateAt? position = some (nativeState state) ∧
      Authenticates owned frame (some state)

theorem lookupIndex_sound {checked : Checked} {base : Base checked} {owned : Owned base} {table : Table}
    (sound : Sound owned table) (frame : ContextFrame) {result : Option Nat}
    (found : table.lookupIndex? frame = some result) : IndexMeaning owned table frame result := by
  induction frame generalizing result with
  | empty => cases found; exact .empty
  | named id =>
    cases selected : table.namedAt? id with
    | none => simp [SourceCoreCallableAncestryCache.Table.lookupIndex?, selected] at found
    | some position =>
      simp only [SourceCoreCallableAncestryCache.Table.lookupIndex?, selected, Option.map_some, Option.some.injEq] at found
      subst result
      obtain ⟨receipt, stored⟩ := sound.named selected
      exact ⟨receipt.state, stored, .named receipt⟩
  | lambda id parent ih =>
    cases parentResult : table.lookupIndex? parent with
    | none => simp [SourceCoreCallableAncestryCache.Table.lookupIndex?, parentResult] at found
    | some parentIndex =>
      cases parentIndex with
      | none => simp [SourceCoreCallableAncestryCache.Table.lookupIndex?, parentResult] at found
      | some position =>
        simp only [SourceCoreCallableAncestryCache.Table.lookupIndex?, parentResult] at found
        split at found
        · next allowed =>
          cases found
          obtain ⟨state, stored, ancestry⟩ := ih parentResult
          obtain ⟨receipt, ⟨metadata⟩⟩ := sound.lambda stored allowed
          exact ⟨state, stored, .lambda ancestry receipt metadata⟩
        · cases found
  | view id target parent ih =>
    cases parentResult : table.lookupIndex? parent with
    | none => simp [SourceCoreCallableAncestryCache.Table.lookupIndex?, parentResult] at found
    | some parentIndex =>
      cases parentIndex with
      | none => simp [SourceCoreCallableAncestryCache.Table.lookupIndex?, parentResult] at found
      | some position =>
        cases selected : table.viewAt? position id target with
        | none => simp [SourceCoreCallableAncestryCache.Table.lookupIndex?, parentResult, selected] at found
        | some destination =>
          simp only [SourceCoreCallableAncestryCache.Table.lookupIndex?, parentResult, selected,
            Option.map_some, Option.some.injEq] at found
          subst result
          obtain ⟨state, stored, ancestry⟩ := ih parentResult
          obtain ⟨receipt, step, final⟩ := sound.view stored selected
          exact ⟨step.after, final, .view ancestry receipt step⟩

def Indexed (table : Table) (frame : ContextFrame) : Option State → Prop
  | none => table.lookupIndex? frame = some none
  | some state => ∃ position, table.lookupIndex? frame = some (some position) ∧
      table.stateAt? position = some (nativeState state)

theorem lookupIndex_complete {checked : Checked} {base : Base checked} {owned : Owned base} {table : Table}
    (closed : Closed owned table) {frame : ContextFrame} {state : Option State}
    (authenticated : Authenticates owned frame state) : Indexed table frame state := by
  induction authenticated with
  | empty => rfl
  | named receipt =>
    obtain ⟨position, selected, stored⟩ := closed.named receipt
    exact ⟨position, by simp [SourceCoreCallableAncestryCache.Table.lookupIndex?, selected], stored⟩
  | lambda ancestry receipt metadata ih =>
    obtain ⟨position, parent, stored⟩ := ih
    have allowed := closed.lambda stored receipt metadata
    exact ⟨position, by simp [SourceCoreCallableAncestryCache.Table.lookupIndex?, parent, allowed], stored⟩
  | view ancestry receipt step ih =>
    obtain ⟨position, parent, stored⟩ := ih
    obtain ⟨destination, selected, final⟩ := closed.view stored receipt step
    exact ⟨destination, by simp [SourceCoreCallableAncestryCache.Table.lookupIndex?, parent, selected], final⟩

theorem lookup_complete {checked : Checked} {base : Base checked} {owned : Owned base} {table : Table}
    (closed : Closed owned table) {frame : ContextFrame} {state : Option State}
    (authenticated : Authenticates owned frame state) : table.lookup? frame = some (state.map nativeState) := by
  have indexed := lookupIndex_complete closed authenticated
  cases state with
  | none =>
    change table.lookupIndex? frame = some none at indexed
    simp [SourceCoreCallableAncestryCache.Table.lookup?, indexed]
  | some state =>
    obtain ⟨position, selected, stored⟩ := indexed
    simp [SourceCoreCallableAncestryCache.Table.lookup?, selected, stored]

theorem lookup_sound {checked : Checked} {base : Base checked} {owned : Owned base} {table : Table}
    (sound : Sound owned table) {frame : ContextFrame} {state : Option SourceCoreCallableAncestryCache.State}
    (found : table.lookup? frame = some state) : Authenticates owned frame (state.map sourceState) := by
  cases indexed : table.lookupIndex? frame with
  | none => simp [SourceCoreCallableAncestryCache.Table.lookup?, indexed] at found
  | some result =>
    have meaning := lookupIndex_sound sound frame indexed
    cases result with
    | none =>
      simp only [SourceCoreCallableAncestryCache.Table.lookup?, indexed, Option.some.injEq] at found
      subst state
      exact meaning
    | some position =>
      obtain ⟨selected, stored, ancestry⟩ := meaning
      simp only [SourceCoreCallableAncestryCache.Table.lookup?, indexed, stored, Option.map_some,
        Option.some.injEq] at found
      subst state
      exact ancestry

theorem Prepared.lookup_iff {checked : Checked} {base : Base checked} {owned : Owned base}
    (prepared : Prepared owned) {frame : ContextFrame} {state : Option State} :
    prepared.table.lookup? frame = some (state.map nativeState) ↔ Authenticates owned frame state := by
  constructor
  · intro found
    have authenticated := lookup_sound prepared.sound found
    cases state <;> exact authenticated
  · exact lookup_complete prepared.closed

/-- Deduplicating reached states by the frontend key preserves the full
metadata state, provided the rows came from authenticated recipes. -/
theorem native_key_injective {checked : Checked} {base : Base checked} {owned : Owned base}
    {leftFrame rightFrame : ContextFrame} {left right : SourceCoreCallableAncestryCache.State}
    (leftAuthenticated : Authenticates owned leftFrame (some (sourceState left)))
    (rightAuthenticated : Authenticates owned rightFrame (some (sourceState right)))
    (same : left.key = right.key) : left = right := by
  have converted := congrArg (fun key : SourceCoreCallableAncestryCache.Key =>
    (⟨key.owner, key.active, key.requirements⟩ : CallableAncestryProfiles.SourceComposition.StateKey)) same
  have sourceEqual := CallableAncestryProfiles.SourceComposition.stateKey_injective leftAuthenticated rightAuthenticated converted
  exact congrArg nativeState sourceEqual

theorem Prepared.lookup_key_injective {checked : Checked} {base : Base checked} {owned : Owned base}
    (prepared : Prepared owned) {leftFrame rightFrame : ContextFrame}
    {left right : SourceCoreCallableAncestryCache.State}
    (leftFound : prepared.table.lookup? leftFrame = some (some left))
    (rightFound : prepared.table.lookup? rightFrame = some (some right))
    (same : left.key = right.key) : left = right :=
  native_key_injective (lookup_sound prepared.sound leftFound) (lookup_sound prepared.sound rightFound) same

end Solcore.SourceSemantics.CoreLowering.CallableAncestryCache
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableAncestryTransitions
/-! Actual preparation transition factories and independent owned metadata
receipts. These facts concern finite static metadata, not execution history. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableAncestryTransitions
open Frontend SourceInference TypeSystem CallableAncestryMetadata CallableAncestryCache
abbrev Inputs := @SourceCoreCallableAncestryPreparation.Inputs
abbrev State := CallableAncestryMetadata.State

theorem views_eq {checked : Checked} {base : Base checked} (owned : Owned base) (inputs : Inputs base) :
    inputs.views = owned.views := Except.ok.inj (inputs.viewsPrepared.symm.trans owned.viewsPrepared)
theorem templates_eq {checked : Checked} {base : Base checked} (owned : Owned base) (inputs : Inputs base) :
    inputs.templates = owned.templates := Except.ok.inj (inputs.templatesPrepared.symm.trans owned.templatesPrepared)
theorem callable_eq {checked : Checked} {base : Base checked} (owned : Owned base) (inputs : Inputs base) :
    inputs.callable = owned.callable := Option.some.inj (inputs.callableSelected.symm.trans owned.callableSelected)

theorem named_equation {checked : Checked} {base : Base checked} (owned : Owned base) (inputs : Inputs base)
    (id : Core.Word) : SourceCoreCallableAncestryPreparation.named? inputs id =
      (named owned id).toOption.map (fun receipt => nativeState receipt.state) := by
  unfold named
  split
  · next selected =>
    simp [SourceCoreCallableAncestryPreparation.named?, callable_eq owned inputs, selected, Except.toOption, throw, throwThe, MonadExceptOf.throw]
  · next entry selected =>
    split
    · next owner origin =>
      split <;> rename_i caller found <;>
        simp [SourceCoreCallableAncestryPreparation.named?, callable_eq owned inputs, selected, origin, found,
          Except.toOption, throw, throwThe, MonadExceptOf.throw, pure, Except.pure, Named.state, nativeState]
    · next excluded =>
      cases shape : entry.origin <;>
        simp_all [SourceCoreCallableAncestryPreparation.named?, callable_eq owned inputs, Except.toOption, throw, throwThe, MonadExceptOf.throw]

theorem named_sound {checked : Checked} {base : Base checked} (owned : Owned base) (inputs : Inputs base)
    {id : Core.Word} {state : SourceCoreCallableAncestryCache.State}
    (accepted : SourceCoreCallableAncestryPreparation.named? inputs id = some state) :
    ∃ receipt : Named owned id, state = nativeState receipt.state := by
  rw [named_equation owned inputs] at accepted
  cases result : named owned id with
  | error error => simp [result, Except.toOption] at accepted
  | ok receipt => simpa only using (show ∃ receipt : Named owned id, state = nativeState receipt.state from
      ⟨receipt, by simpa [result, Except.toOption] using accepted.symm⟩)

theorem named_complete {checked : Checked} {base : Base checked} {owned : Owned base} (inputs : Inputs base)
    {id : Core.Word} (receipt : Named owned id) :
    SourceCoreCallableAncestryPreparation.named? inputs id = some (nativeState receipt.state) := by
  simp [SourceCoreCallableAncestryPreparation.named?, callable_eq owned inputs,
    receipt.selected, receipt.origin, receipt.found, Named.state, nativeState, Except.toOption]

theorem lambda_complete {checked : Checked} {base : Base checked} {owned : Owned base} (inputs : Inputs base)
    {id : Core.Word} {state : State} (receipt : LambdaAt owned id) (metadata : LambdaSource receipt state) :
    SourceCoreCallableAncestryPreparation.lambdaAllowed inputs (nativeState state) id = true := by
  simp only [SourceCoreCallableAncestryPreparation.lambdaAllowed, templates_eq owned inputs,
    callable_eq owned inputs, receipt.selected, receipt.descriptorSelected, receipt.origin,
    nativeState, metadata.owner, metadata.active, and_self, ↓reduceIte, metadata.found]
  rw [if_pos metadata.sameForm, metadata.shape]
  rfl

private theorem lambdaAt_exists {checked : Checked} {base : Base checked} {owned : Owned base}
    {id : Core.Word} {template : Lambda} {entry : SourceCoreStageCodebook.Entry}
    (selected : owned.templates.lambdaAt? id = some template)
    (descriptor : owned.callable.table.entryAt? id = some entry)
    (origin : entry.origin = .lambda template.owner template.id template.active) :
    ∃ receipt : LambdaAt owned id, lambdaAt owned id = .ok receipt ∧ receipt.template = template ∧ receipt.entry = entry := by
  unfold lambdaAt
  split
  · next missing => rw [selected] at missing; cases missing
  · next actual found =>
    have same := Option.some.inj (found.symm.trans selected)
    subst actual
    split
    · next missing => rw [descriptor] at missing; cases missing
    · next actual found =>
      have same := Option.some.inj (found.symm.trans descriptor)
      subst actual
      rw [dif_pos origin]
      exact ⟨_, rfl, rfl, rfl⟩

private theorem lambdaSource_exists {checked : Checked} {base : Base checked} {owned : Owned base}
    {id : Core.Word} {state : State} (receipt : LambdaAt owned id) {node : ExpressionNode}
    (owner : state.owner = receipt.template.owner) (active : state.active = receipt.template.active)
    (found : state.source.lookupExpression? receipt.template.id = some node)
    (sameForm : node.form = receipt.template.node.form)
    {parameters : List TypedBinder} {result : Ty} {body : List StatementId}
    (shape : node.form = .lambda parameters result body) : Nonempty (LambdaSource receipt state) := by
  have success : ∃ metadata, lambdaSource receipt state = .ok metadata := by
    unfold lambdaSource
    rw [dif_pos owner, dif_pos active]
    split
    · next missing => rw [found] at missing; cases missing
    · next actual selected =>
      have same := Option.some.inj (selected.symm.trans found)
      subst actual
      rw [dif_pos sameForm]
      split
      · exact ⟨_, rfl⟩
      · next impossible => exact (impossible _ _ _ shape).elim
  obtain ⟨metadata, _⟩ := success
  exact ⟨metadata⟩

theorem lambda_sound {checked : Checked} {base : Base checked} (owned : Owned base) (inputs : Inputs base)
    {id : Core.Word} {state : State}
    (accepted : SourceCoreCallableAncestryPreparation.lambdaAllowed inputs (nativeState state) id = true) :
    ∃ receipt : LambdaAt owned id, Nonempty (LambdaSource receipt state) := by
  unfold SourceCoreCallableAncestryPreparation.lambdaAllowed at accepted
  rw [templates_eq owned inputs, callable_eq owned inputs] at accepted
  simp only [nativeState, Id.run, pure] at accepted
  split at accepted <;> try cases accepted
  next template selected =>
    split at accepted <;> try cases accepted
    next entry descriptor =>
      split at accepted <;> try cases accepted
      next origin =>
        split at accepted <;> try cases accepted
        next context =>
          split at accepted <;> try cases accepted
          next node found =>
            split at accepted <;> try cases accepted
            next sameForm =>
              split at accepted <;> try cases accepted
              next parameters result body shape =>
                obtain ⟨receipt, _, same, _⟩ := lambdaAt_exists selected descriptor origin
                refine ⟨receipt, ?_⟩
                apply lambdaSource_exists receipt (node := node)
                · simpa only [same] using context.1
                · simpa only [same] using context.2
                · simpa only [same] using found
                · simpa only [same] using sameForm
                · exact shape

theorem view_complete {checked : Checked} {base : Base checked} {owned : Owned base} (inputs : Inputs base)
    {id target : Core.Word} {state : State} (receipt : ViewAt owned id target) (step : ViewStep receipt state) :
    SourceCoreCallableAncestryPreparation.view? inputs (nativeState state) id target = some (nativeState step.after) := by
  simp only [SourceCoreCallableAncestryPreparation.view?, views_eq owned inputs, templates_eq owned inputs,
    callable_eq owned inputs, receipt.selected, receipt.targetLambda.selected,
    receipt.targetLambda.descriptorSelected, bind, Option.bind, receipt.targetLambda.origin, ne_eq,
    not_true_eq_false, ↓reduceIte]
  have target := receipt.targetOrigin
  rw [receipt.targetLambda.origin] at target
  simp only [target, receipt.generalized, not_true_eq_false, ↓reduceIte,
    nativeState, step.owner, step.active, or_self]
  rw [← step.owner, ← step.active]
  simp only [step.callerFound, Except.toOption, step.found, step.reference, not_true_eq_false, ↓reduceIte,
    ← step.binderExact, step.declaration, step.requirementLayout]
  have factory := step.factory
  rw [step.reference] at factory
  rw [factory]
  simp only [step.substitutionExact, not_true_eq_false, ↓reduceIte, pure]
  simp only [ViewStep.after, step.substitutionExact]

private theorem viewAt_exists {checked : Checked} {base : Base checked} {owned : Owned base}
    {id target : Core.Word} {entry : SourceCoreCallableViews.Entry base.sourceProgram base.plan}
    (selected : owned.views.entryAt? id = some entry) (lambda : LambdaAt owned target)
    (generated : lambdaAt owned target = .ok lambda)
    (origin : lambda.entry.origin = .lambda entry.view.owner entry.view.principal.initializer entry.view.cumulative)
    (generalized : entry.view.wrapsPrincipal = true) :
    ∃ receipt : ViewAt owned id target, viewAt owned id target = .ok receipt ∧ receipt.entry = entry := by
  unfold viewAt
  split
  · next missing => rw [selected] at missing; cases missing
  · next actual found =>
    have same := Option.some.inj (found.symm.trans selected)
    subst actual
    simp only [generated, bind, Except.bind]
    rw [dif_pos origin, dif_pos generalized]
    exact ⟨_, rfl, rfl⟩

private theorem prepareStep_exists {checked : Checked} {base : Base checked} {owned : Owned base}
    {id target : Core.Word} (receipt : ViewAt owned id target) (state : State)
    (owner : state.owner = receipt.entry.view.owner) (active : state.active = receipt.entry.view.parentActive)
    {caller : SourceSpecialization.SpecializedFunction}
    (callerFound : SourceCompilationPlan.exactSpecialization base.plan state.owner = .ok caller)
    {node : ExpressionNode} (found : state.source.lookupExpression? receipt.entry.view.read = some node)
    {name : String} (reference : node.form = .reference name (.local receipt.entry.view.binding.binder.id))
    (declaration : (⟨receipt.entry.view.binding.binder.applySubstitution state.active,
      receipt.entry.view.principal.initializer⟩ : SourceCoreCallablePrincipals.Declaration) ∈
      SourceCoreCallablePrincipals.declarations state.source)
    {requirements : List RequirementId} (requirementLayout : SourceCompilationPlan.ordinaryOwnedRequirements? node = some requirements)
    {substitution : Substitution} {witnesses : List Witness}
    (factory : SourceCompilationPlan.localRequirementWitnesses caller receipt.entry.view.principal.evidence
      (receipt.entry.view.binding.binder.applySubstitution state.active)
      {node with type := node.rawType, requirements, coercions := []} = .ok (substitution, witnesses))
    (substitutionExact : substitution = receipt.entry.view.ownSubstitution) :
    ∃ step : ViewStep receipt state, step.after = ⟨state.owner, substitution.compose state.active,
      SourceTypedRuntime.rewriteLocalRequirements witnesses (state.source.applySubstitution substitution)⟩ := by
  have success : ∃ step, prepareStep receipt state = .ok step := by
    unfold prepareStep
    rw [dif_pos owner, dif_pos active]
    split
    · next error failed => rw [callerFound] at failed; cases failed
    · next actual selected =>
      have same := Except.ok.inj (selected.symm.trans callerFound)
      subst actual
      split
      · next missing => rw [found] at missing; cases missing
      · next actual selected =>
        have same := Option.some.inj (selected.symm.trans found)
        subst actual
        split
        · next readName binderId shape =>
          have same := ExpressionForm.reference.inj (shape.symm.trans reference)
          obtain ⟨rfl, same⟩ := same
          cases same
          rw [dif_pos rfl, dif_pos declaration]
          split
          · next missing => rw [requirementLayout] at missing; cases missing
          · next actual selected =>
            have same := Option.some.inj (selected.symm.trans requirementLayout)
            subst actual
            split
            · next error failed => rw [factory] at failed; cases failed
            · next result generated =>
              have same := Except.ok.inj (generated.symm.trans factory)
              cases same
              rw [dif_pos substitutionExact]
              exact ⟨_, rfl⟩
        · next excluded => exact (excluded _ _ reference).elim
  obtain ⟨step, _⟩ := success
  have sameCaller := Except.ok.inj (step.callerFound.symm.trans callerFound)
  have sameNode := Option.some.inj (step.found.symm.trans found)
  have sameRequirements := Option.some.inj ((sameNode ▸ step.requirementLayout).symm.trans requirementLayout)
  have sameFactory := step.factory
  rw [sameCaller, sameNode, step.binderExact, sameRequirements] at sameFactory
  have same := Except.ok.inj (sameFactory.symm.trans factory)
  exact ⟨step, by simp only [ViewStep.after, Prod.mk.injEq] at same ⊢; rw [same.1, same.2]⟩

theorem view_sound {checked : Checked} {base : Base checked} (owned : Owned base) (inputs : Inputs base)
    {id target : Core.Word} {state : State} {result : SourceCoreCallableAncestryCache.State}
    (accepted : SourceCoreCallableAncestryPreparation.view? inputs (nativeState state) id target = some result) :
    ∃ (receipt : ViewAt owned id target) (step : ViewStep receipt state), result = nativeState step.after := by
  unfold SourceCoreCallableAncestryPreparation.view? at accepted
  simp only [views_eq owned inputs, templates_eq owned inputs, callable_eq owned inputs,
    nativeState, bind, Option.bind, ne_eq, ite_not] at accepted
  split at accepted <;> try cases accepted
  next entry selected =>
    try dsimp only at accepted
    split at accepted <;> try cases accepted
    next template templateSelected =>
      try dsimp only at accepted
      split at accepted <;> try cases accepted
      next descriptor descriptorSelected =>
        try dsimp only at accepted
        split at accepted <;> try cases accepted
        next origin =>
          try dsimp only at accepted
          split at accepted <;> try cases accepted
          next targetOrigin =>
            try dsimp only at accepted
            split at accepted <;> try cases accepted
            next generalized =>
              try dsimp only at accepted
              split at accepted <;> try cases accepted
              next context =>
                try dsimp only at accepted
                have context : state.owner = entry.view.owner ∧ state.active = entry.view.parentActive := by
                  exact ⟨Classical.byContradiction (fun h => context (.inl h)),
                    Classical.byContradiction (fun h => context (.inr h))⟩
                cases callerFound : SourceCompilationPlan.exactSpecialization base.plan state.owner with
                | error error => simp [callerFound, Except.toOption] at accepted
                | ok caller =>
                  simp only [callerFound, Except.toOption] at accepted
                  split at accepted <;> try cases accepted
                  next node found =>
                    try dsimp only at accepted
                    split at accepted <;> try cases accepted
                    next name binderId reference =>
                      try dsimp only at accepted
                      split at accepted <;> try cases accepted
                      next sameBinder =>
                        try dsimp only at accepted
                        subst binderId
                        split at accepted <;> try cases accepted
                        next declaration =>
                          try dsimp only at accepted
                          split at accepted <;> try cases accepted
                          next requirements layout =>
                            try dsimp only at accepted
                            cases factory : SourceCompilationPlan.localRequirementWitnesses caller entry.view.principal.evidence
                                (entry.view.binding.binder.applySubstitution state.active)
                                {node with type := node.rawType, requirements, coercions := []} with
                            | error error => simp [factory] at accepted
                            | ok pair =>
                              obtain ⟨substitution, witnesses⟩ := pair
                              simp only [factory] at accepted
                              split at accepted <;> try cases accepted
                              next substitutionExact =>
                                try dsimp only at accepted
                                obtain ⟨lambda, generated, _, lambdaEntry⟩ := lambdaAt_exists templateSelected descriptorSelected origin
                                obtain ⟨receipt, _, sameEntry⟩ := viewAt_exists selected lambda generated
                                  (by simpa only [lambdaEntry] using targetOrigin) generalized
                                have completed := prepareStep_exists receipt state
                                  (node := node) (requirements := requirements)
                                  (substitution := substitution) (witnesses := witnesses)
                                  (by simpa only [sameEntry] using context.1)
                                  (by simpa only [sameEntry] using context.2) callerFound
                                  (by simpa only [sameEntry] using found)
                                  (by simpa only [sameEntry] using reference)
                                  (by rw [sameEntry]; exact declaration)
                                  layout (by rw [sameEntry]; exact factory)
                                  (by simpa only [sameEntry] using substitutionExact)
                                obtain ⟨step, after⟩ := completed
                                exact ⟨receipt, step, by rw [after]; rfl⟩



private theorem namedEdge {table : SourceCoreCallableAncestryCache.Table} {id : Core.Word} {position : Nat}
    (found : table.namedAt? id = some position) :
    ∃ edge ∈ table.named, edge.origin = id ∧ edge.destination = position := by
  unfold SourceCoreCallableAncestryCache.Table.namedAt? at found
  cases selected : table.named.find? (fun edge => decide (edge.origin = id)) with
  | none => simp [selected] at found
  | some edge =>
    have member := List.mem_of_find?_eq_some selected
    have origin : edge.origin = id := by simpa using List.find?_some selected
    exact ⟨edge, member, origin, by simpa [selected] using found⟩

private theorem lambdaEdge {table : SourceCoreCallableAncestryCache.Table} {id : Core.Word} {position : Nat}
    (found : table.lambdaAllowed position id = true) :
    ∃ edge ∈ table.lambdas, edge.state = position ∧ edge.origin = id := by
  simpa only [SourceCoreCallableAncestryCache.Table.lambdaAllowed, List.any_eq_true, decide_eq_true_eq] using found

private theorem viewEdge {table : SourceCoreCallableAncestryCache.Table} {id target : Core.Word} {position destination : Nat}
    (found : table.viewAt? position id target = some destination) :
    ∃ edge ∈ table.views, edge.state = position ∧ edge.view = id ∧ edge.target = target ∧ edge.destination = destination := by
  unfold SourceCoreCallableAncestryCache.Table.viewAt? at found
  cases selected : table.views.find? (fun edge => decide (edge.state = position ∧ edge.view = id ∧ edge.target = target)) with
  | none => rw [selected] at found; cases found
  | some edge =>
    have member := List.mem_of_find?_eq_some selected
    have shape : edge.state = position ∧ edge.view = id ∧ edge.target = target := by simpa using List.find?_some selected
    exact ⟨edge, member, shape.1, shape.2.1, shape.2.2, by simpa only [selected, Option.map_some, Option.some.injEq] using found⟩

/-- Actual finite-row validation implies independent owned transition
soundness. No runtime evaluation or preselected list of frames is assumed. -/
theorem valid_sound {checked : Checked} {base : Base checked} (owned : Owned base) (inputs : Inputs base)
    {table : SourceCoreCallableAncestryCache.Table}
    (validated : SourceCoreCallableAncestryPreparation.valid inputs table = true) : Sound owned table := by
  simp only [SourceCoreCallableAncestryPreparation.valid, Bool.and_eq_true] at validated
  obtain ⟨⟨⟨⟨namedRows, lambdaRows⟩, viewRows⟩, _⟩, _⟩ := validated
  constructor
  · intro id position found
    obtain ⟨edge, member, origin, destination⟩ := namedEdge found
    have row := List.all_eq_true.mp namedRows edge member
    rw [origin, destination] at row
    cases generated : SourceCoreCallableAncestryPreparation.named? inputs id with
    | none => simp [generated] at row
    | some state =>
      have stored : table.stateAt? position = some state := by simpa only [generated, decide_eq_true_eq] using row
      obtain ⟨receipt, same⟩ := named_sound owned inputs generated
      exact ⟨receipt, by simpa only [same] using stored⟩
  · intro position state id stored allowed
    obtain ⟨edge, member, index, origin⟩ := lambdaEdge allowed
    have row := List.all_eq_true.mp lambdaRows edge member
    simp only [index, origin, stored] at row
    exact lambda_sound owned inputs row
  · intro position state id target destination stored found
    obtain ⟨edge, member, index, viewId, targetId, next⟩ := viewEdge found
    have row := List.all_eq_true.mp viewRows edge member
    simp only [index, viewId, targetId, next, stored] at row
    cases generated : SourceCoreCallableAncestryPreparation.view? inputs (nativeState state) id target with
    | none => simp [generated] at row
    | some result =>
      have final : table.stateAt? destination = some result := by simpa only [generated, decide_eq_true_eq] using row
      obtain ⟨receipt, step, same⟩ := view_sound owned inputs generated
      exact ⟨receipt, step, by simpa only [same] using final⟩

/-- Every independently valid named/lambda/view transition is included by
actual validation of the completed table. -/
theorem valid_closed {checked : Checked} {base : Base checked} (owned : Owned base) (inputs : Inputs base)
    {table : SourceCoreCallableAncestryCache.Table}
    (validated : SourceCoreCallableAncestryPreparation.valid inputs table = true) : Closed owned table := by
  simp only [SourceCoreCallableAncestryPreparation.valid, Bool.and_eq_true] at validated
  obtain ⟨⟨_, namedRows⟩, transitions⟩ := validated
  rw [callable_eq owned inputs] at namedRows
  rw [templates_eq owned inputs, views_eq owned inputs] at transitions
  constructor
  · intro id receipt
    have member : receipt.entry ∈ owned.callable.table.entries := List.mem_of_find?_eq_some receipt.selected
    have identifier : receipt.entry.id = id := by simpa using List.find?_some receipt.selected
    have row := List.all_eq_true.mp namedRows receipt.entry member
    simp only [identifier, named_complete inputs receipt] at row
    cases selected : table.namedAt? id with
    | none => simp [selected] at row
    | some position => exact ⟨position, rfl, by simpa only [selected, decide_eq_true_eq] using row⟩
  · intro position state id stored receipt metadata
    have member : (nativeState state, position) ∈ table.states.zipIdx :=
      List.mk_mem_zipIdx_iff_getElem?.mpr stored
    have both := List.all_eq_true.mp transitions (nativeState state, position) member
    simp only [Bool.and_eq_true] at both
    have rows := both.1
    have templateMember : receipt.template ∈ owned.templates.lambdas := List.mem_of_find?_eq_some receipt.selected
    have identifier : receipt.template.descriptor = id := by simpa using List.find?_some receipt.selected
    have row := List.all_eq_true.mp rows receipt.template templateMember
    simpa only [identifier, lambda_complete inputs receipt metadata, Bool.not_true, Bool.false_or] using row
  · intro position state id target stored receipt step
    have member : (nativeState state, position) ∈ table.states.zipIdx :=
      List.mk_mem_zipIdx_iff_getElem?.mpr stored
    have both := List.all_eq_true.mp transitions (nativeState state, position) member
    simp only [Bool.and_eq_true] at both
    have rows := both.2
    have viewMember : receipt.entry ∈ owned.views.entries := List.mem_of_find?_eq_some receipt.selected
    have identifier : receipt.entry.id = id := by simpa using List.find?_some receipt.selected
    have row := List.all_eq_true.mp rows receipt.entry viewMember
    have templateMember : receipt.targetLambda.template ∈ owned.templates.lambdas := List.mem_of_find?_eq_some receipt.targetLambda.selected
    have targetId : receipt.targetLambda.template.descriptor = target := by simpa using List.find?_some receipt.targetLambda.selected
    have row := List.all_eq_true.mp row receipt.targetLambda.template templateMember
    simp only [identifier, targetId, view_complete inputs receipt step] at row
    cases selected : table.viewAt? position id target with
    | none => simp [selected] at row
    | some destination => exact ⟨destination, rfl, by simpa only [selected, decide_eq_true_eq] using row⟩

/-- Successful actual preparation provides the static completed-worklist
certificate. Proving that preparation cannot exhaust its computed cardinality
is a distinct totality obligation, not a premise hidden in this theorem. -/
def certified {checked : Checked} {base : Base checked} (owned : Owned base)
    (prepared : SourceCoreCallableAncestryPreparation.Prepared base) : CallableAncestryCache.Prepared owned :=
  certify prepared.table (valid_sound owned prepared.inputs prepared.validated)
    (valid_closed owned prepared.inputs prepared.validated)

theorem prepared_lookup_iff {checked : Checked} {base : Base checked} (owned : Owned base)
    (prepared : SourceCoreCallableAncestryPreparation.Prepared base) {frame : ContextFrame} {state : Option State} :
    prepared.table.lookup? frame = some (state.map nativeState) ↔ Authenticates owned frame state :=
  (certified owned prepared).lookup_iff

end Solcore.SourceSemantics.CoreLowering.CallableAncestryTransitions
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableAncestryCardinality
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableAncestryPairedProfiles
/-! Finite metadata profiles for paired read and lexical ancestry. Source
substitutions and native compilation contexts have separate finite bounds.
The mathematical key space is an overapproximation; preparation need only
visit reached states. None of these invariants assert runtime history. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableAncestryPairedProfiles
open Frontend SourceInference TypeSystem CallableAncestryMetadata CallableAncestryProfiles
open CallableAncestryProfiles.SourceComposition
abbrev PairedState := SourceCoreCallableAncestryReadRecipes.State
abbrev Inputs := @SourceCoreCallableAncestryPreparation.Inputs

abbrev Key := SourceCoreCallableAncestryPairedCache.Key
abbrev key := SourceCoreCallableAncestryPairedCache.stateKey
abbrev nativeContexts := @SourceCoreCallableAncestryPairedPreparation.nativeContexts

/-- Several named seed descriptors may share an owner. Their canonical source
must agree; equal native representations alone cannot establish this law. -/
def RootsCoherent (roots : List PairedState) : Prop :=
  ∀ left ∈ roots, ∀ right ∈ roots, left.metadata.owner = right.metadata.owner →
    left.metadata.source = right.metadata.source

/-- Exact specialization selection is the static provenance needed for named
seeds. It does not require a source execution or a caller-provided source
canonicality theorem. -/
def Seeded {checked : Checked} (base : Base checked) (roots : List PairedState) : Prop :=
  ∀ root ∈ roots, ∃ specialized : SourceSpecialization.SpecializedFunction,
    SourceCompilationPlan.exactSpecialization base.plan root.metadata.owner = .ok specialized ∧
      root.metadata.source = specialized.function.typedBody ∧
      root.metadata.active = [] ∧ root.nativeActive = []

theorem seeded_coherent {checked : Checked} {base : Base checked} {roots : List PairedState}
    (seeded : Seeded base roots) : RootsCoherent roots := by
  intro left leftMember right rightMember sameOwner
  obtain ⟨leftCaller, leftFound, leftSource, _⟩ := seeded left leftMember
  obtain ⟨rightCaller, rightFound, rightSource, _⟩ := seeded right rightMember
  rw [sameOwner] at leftFound
  have sameCaller := Except.ok.inj (leftFound.symm.trans rightFound)
  rw [leftSource, rightSource, sameCaller]

theorem named_source {checked : Checked} {base : Base checked} (inputs : Inputs base)
    {id : Core.Word} {metadata : SourceCoreCallableAncestryCache.State}
    (accepted : SourceCoreCallableAncestryPreparation.named? inputs id = some metadata) :
    ∃ specialized : SourceSpecialization.SpecializedFunction,
      SourceCompilationPlan.exactSpecialization base.plan metadata.owner = .ok specialized ∧
        metadata.source = specialized.function.typedBody ∧ metadata.active = [] := by
  cases selected : inputs.callable.table.entryAt? id with
  | none => simp [SourceCoreCallableAncestryPreparation.named?, selected] at accepted
  | some entry =>
    cases origin : entry.origin with
    | named owner =>
      cases found : SourceCompilationPlan.exactSpecialization base.plan owner with
      | error error => simp [SourceCoreCallableAncestryPreparation.named?, selected, origin, found, Except.toOption] at accepted
      | ok specialized =>
        have same : (⟨owner, [], specialized.function.typedBody⟩ : SourceCoreCallableAncestryCache.State) = metadata := by
          simpa [SourceCoreCallableAncestryPreparation.named?, selected, origin, found, Except.toOption] using accepted
        subst metadata
        exact ⟨specialized, found, rfl, rfl⟩
    | lambda owner id active => simp [SourceCoreCallableAncestryPreparation.named?, selected, origin] at accepted
    | builtin builtin => simp [SourceCoreCallableAncestryPreparation.named?, selected, origin] at accepted

theorem roots_seeded {checked : Checked} {base : Base checked} (inputs : Inputs base)
    (roots : List PairedState)
    (selected : ∀ root ∈ roots, ∃ id, SourceCoreCallableAncestryPreparation.named? inputs id = some root.metadata ∧
      root.nativeActive = []) : Seeded base roots := by
  intro root member
  obtain ⟨id, found, nativeEmpty⟩ := selected root member
  obtain ⟨specialized, found, source, active⟩ := named_source inputs found
  exact ⟨specialized, found, source, active, nativeEmpty⟩

structure ValidAt {checked : Checked} {base : Base checked} (inputs : Inputs base)
    (root state : PairedState) : Prop where
  owner : state.metadata.owner = root.metadata.owner
  canonical : eraseRequirements state.metadata.source =
    eraseRequirements (root.metadata.source.applySubstitution state.metadata.active)
  sourceReachable : CallableAncestrySourceActive.Reachable
    (CallableAncestrySourceActive.generators inputs.views) state.metadata.active
  nativeMember : state.nativeActive ∈ nativeContexts inputs
  bounded : Bounded (alphabet root.metadata.source) state.metadata.source
  lengths : (requirementProfile state.metadata.source).map List.length =
    (requirementProfile root.metadata.source).map List.length

def Valid {checked : Checked} {base : Base checked} (inputs : Inputs base)
    (roots : List PairedState) (state : PairedState) : Prop :=
  ∃ root ∈ roots, ValidAt inputs root state

theorem seed_validAt {checked : Checked} {base : Base checked} (inputs : Inputs base)
    (root : PairedState) (sourceEmpty : root.metadata.active = []) (nativeEmpty : root.nativeActive = []) :
    ValidAt inputs root root := by
  refine ⟨rfl, ?_, ?_, ?_, bounded_alphabet _, rfl⟩
  · rw [sourceEmpty, EmptySourceSubstitution.source]
  · rw [sourceEmpty]; exact .empty
  · simp [nativeEmpty, nativeContexts, SourceCoreCallableAncestryPairedPreparation.nativeContexts]

theorem seed_valid {checked : Checked} {base : Base checked} (inputs : Inputs base)
    {roots : List PairedState} {root : PairedState} (member : root ∈ roots)
    (sourceEmpty : root.metadata.active = []) (nativeEmpty : root.nativeActive = []) :
    Valid inputs roots root := ⟨root, member, seed_validAt inputs root sourceEmpty nativeEmpty⟩

theorem seeded_valid {checked : Checked} {base : Base checked} (inputs : Inputs base)
    {roots : List PairedState} (seeded : Seeded base roots) {root : PairedState} (member : root ∈ roots) :
    Valid inputs roots root := by
  obtain ⟨_, _, _, sourceEmpty, nativeEmpty⟩ := seeded root member
  exact seed_valid inputs member sourceEmpty nativeEmpty

/-- Classification remains valid when only the native component is replaced
by another owned context. This is a finite-set law, not a frame-transition
rule; a normal lambda frame may simply preserve its parent's state. -/
theorem ValidAt.native {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {root state : PairedState} (valid : ValidAt inputs root state) {active : Substitution}
    (selected : active ∈ nativeContexts inputs) : ValidAt inputs root {state with nativeActive := active} :=
  ⟨valid.owner, valid.canonical, valid.sourceReachable, selected, valid.bounded, valid.lengths⟩

theorem Valid.withNativeTemplate {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {roots : List PairedState} {state : PairedState} (valid : Valid inputs roots state)
    (template : SourceCoreLambdaTemplates.Lambda) (selected : template ∈ inputs.templates.lambdas) :
    Valid inputs roots {state with nativeActive := template.active} := by
  obtain ⟨root, member, valid⟩ := valid
  refine ⟨root, member, valid.native ?_⟩
  simp only [nativeContexts, SourceCoreCallableAncestryPairedPreparation.nativeContexts, List.mem_cons, List.mem_append]
  exact .inr (.inl (List.mem_map.mpr ⟨template, selected, rfl⟩))

theorem read_after_validAt {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {caller lexical root : PairedState} {id target : Core.Word}
    (read : SourceCoreCallableAncestryReadRecipes.Read inputs caller id target)
    (callerValid : ValidAt inputs root caller) (lexicalValid : ValidAt inputs root lexical) :
    ValidAt inputs root (read.after lexical) := by
  have closed := lexicalValid.sourceReachable.closed (CallableAncestrySourceActive.generators_valid inputs.views)
  refine ⟨lexicalValid.owner, CallableAncestryReadRecipes.after_canonical read lexical _ closed lexicalValid.canonical,
    CallableAncestryReadRecipes.after_reachable read lexical lexicalValid.sourceReachable, ?_,
    CallableAncestryReadRecipes.after_bounded read lexical callerValid.bounded lexicalValid.bounded, ?_⟩
  · change read.entry.view.cumulative ∈ _
    simp only [nativeContexts, SourceCoreCallableAncestryPairedPreparation.nativeContexts, List.mem_cons, List.mem_append]
    exact .inr (.inr (List.mem_map.mpr ⟨read.entry, CallableAncestryReadRecipes.read_member read, rfl⟩))
  · exact (CallableAncestryReadRecipes.after_spines read lexical).trans lexicalValid.lengths

/-- Caller and principal may have different source/native active contexts.
The actual read/application receipts identify their common owner. -/
theorem read_after_valid {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {roots : List PairedState} (coherent : RootsCoherent roots)
    {caller lexical : PairedState} {id target : Core.Word}
    (read : SourceCoreCallableAncestryReadRecipes.Read inputs caller id target)
    (applied : SourceCoreCallableAncestryReadRecipes.Applied read lexical)
    (callerValid : Valid inputs roots caller) (lexicalValid : Valid inputs roots lexical) :
    Valid inputs roots (read.after lexical) := by
  obtain ⟨callerRoot, callerMember, callerValid⟩ := callerValid
  obtain ⟨lexicalRoot, lexicalMember, lexicalValid⟩ := lexicalValid
  have owners : callerRoot.metadata.owner = lexicalRoot.metadata.owner :=
    callerValid.owner.symm.trans (read.owner.trans (applied.owner.symm.trans lexicalValid.owner))
  have sources := coherent callerRoot callerMember lexicalRoot lexicalMember owners
  have sameRoot : ValidAt inputs lexicalRoot caller := {
    owner := callerValid.owner.trans owners
    canonical := by simpa only [sources] using callerValid.canonical
    sourceReachable := callerValid.sourceReachable
    nativeMember := callerValid.nativeMember
    bounded := by simpa only [sources] using callerValid.bounded
    lengths := by simpa only [sources] using callerValid.lengths
  }
  exact ⟨lexicalRoot, lexicalMember, read_after_validAt read sameRoot lexicalValid⟩

/-- A canonical erased source plus its occurrence profile determines all
retained source metadata. Native active context is compared independently. -/
theorem key_injective {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {roots : List PairedState} (coherent : RootsCoherent roots) {left right : PairedState}
    (leftValid : Valid inputs roots left) (rightValid : Valid inputs roots right)
    (same : key left = key right) : left = right := by
  have owners : left.metadata.owner = right.metadata.owner := congrArg (fun value : Key => value.owner) same
  have active : left.metadata.active = right.metadata.active := congrArg (fun value : Key => value.sourceActive) same
  have native : left.nativeActive = right.nativeActive := congrArg (fun value : Key => value.nativeActive) same
  have profile : requirementProfile left.metadata.source = requirementProfile right.metadata.source := congrArg (fun value : Key => value.requirements) same
  obtain ⟨leftRoot, leftMember, leftValid⟩ := leftValid
  obtain ⟨rightRoot, rightMember, rightValid⟩ := rightValid
  have sources := coherent leftRoot leftMember rightRoot rightMember
    (leftValid.owner.symm.trans (owners.trans rightValid.owner))
  have erased : eraseRequirements left.metadata.source = eraseRequirements right.metadata.source := by
    rw [leftValid.canonical, rightValid.canonical, sources, active]
  have exactSource := FiniteProfiles.source_unique erased profile
  cases left with
  | mk leftMetadata leftNative =>
    cases right with
    | mk rightMetadata rightNative =>
      cases leftMetadata; cases rightMetadata
      cases owners; cases active; cases native; cases exactSource; rfl

def keysFor (choices : List Substitution) (contexts : List Substitution) (root : PairedState) : List Key :=
  (CallableAncestrySourceActive.keySpace choices).flatMap fun sourceActive =>
    contexts.flatMap fun nativeActive =>
      (FiniteProfiles.profiles (alphabet root.metadata.source)
        ((requirementProfile root.metadata.source).map List.length)).map fun profile =>
          ⟨root.metadata.owner, sourceActive, nativeActive, profile⟩

def keySpace {checked : Checked} {base : Base checked} (inputs : Inputs base) (roots : List PairedState) : List Key :=
  roots.flatMap (keysFor (CallableAncestrySourceActive.generators inputs.views) (nativeContexts inputs))

def capacity {checked : Checked} {base : Base checked} (inputs : Inputs base) (roots : List PairedState) : Nat :=
  (roots.map fun root => CallableAncestrySourceActive.capacity (CallableAncestrySourceActive.generators inputs.views) *
    (nativeContexts inputs).length * (alphabet root.metadata.source).length ^ (alphabet root.metadata.source).length).sum

private theorem length_flatMap_const {α β : Type} (items : List α) (f : α → List β) (count : Nat)
    (constant : ∀ item ∈ items, (f item).length = count) : (items.flatMap f).length = items.length * count := by
  induction items with
  | nil => simp
  | cons head tail ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons,
      constant head (by simp), ih (fun item member => constant item (by simp [member]))]
    simp [Nat.add_mul, Nat.add_comm]

theorem keysFor_length (choices : List Substitution) (contexts : List Substitution) (root : PairedState) :
    (keysFor choices contexts root).length = CallableAncestrySourceActive.capacity choices * contexts.length *
      (alphabet root.metadata.source).length ^ (alphabet root.metadata.source).length := by
  unfold keysFor
  rw [length_flatMap_const _ _ (contexts.length * (alphabet root.metadata.source).length ^ (alphabet root.metadata.source).length)]
  · rw [CallableAncestrySourceActive.keySpace_length, Nat.mul_assoc]
  · intro sourceActive _
    rw [length_flatMap_const _ _ ((alphabet root.metadata.source).length ^ (alphabet root.metadata.source).length)]
    intro nativeActive _
    simp only [List.length_map, CallableAncestryCardinality.profiles_length, alphabet, List.length_flatten]

theorem keySpace_length {checked : Checked} {base : Base checked} (inputs : Inputs base) (roots : List PairedState) :
    (keySpace inputs roots).length = capacity inputs roots := by
  simp only [keySpace, List.length_flatMap, keysFor_length, capacity]

theorem key_member {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {roots : List PairedState} {state : PairedState} (valid : Valid inputs roots state) :
    key state ∈ keySpace inputs roots := by
  obtain ⟨root, member, valid⟩ := valid
  apply List.mem_flatMap.mpr
  refine ⟨root, member, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨state.metadata.active, valid.sourceReachable.keySpace_member (CallableAncestrySourceActive.generators_valid inputs.views), ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨state.nativeActive, valid.nativeMember, ?_⟩
  have profiles := FiniteProfiles.profile_member (requirementProfile state.metadata.source) valid.bounded
  rw [valid.lengths] at profiles
  apply List.mem_map.mpr
  refine ⟨requirementProfile state.metadata.source, profiles, ?_⟩
  simp only [key, SourceCoreCallableAncestryPairedCache.stateKey, valid.owner, requirementProfile]
  rfl

theorem source_capacity_eq {checked : Checked} {base : Base checked} (inputs : Inputs base) :
    CallableAncestrySourceActive.capacity (CallableAncestrySourceActive.generators inputs.views) =
      SourceCoreCallableAncestryPairedPreparation.sourceActiveCapacity inputs := by
  simp only [CallableAncestrySourceActive.capacity, CallableAncestrySourceActive.domainAlphabet,
    CallableAncestrySourceActive.alphabet, CallableAncestrySourceActive.generators,
    SourceCoreCallableAncestryPairedPreparation.sourceActiveCapacity, List.flatMap]

private theorem fold_sum {α : Type} (items : List α) (f : α → Nat) (initial : Nat) :
    items.foldl (fun acc item => acc + f item) initial = initial + (items.map f).sum := by
  induction items generalizing initial with
  | nil => simp
  | cons head tail ih => simp [ih, Nat.add_assoc]

/-- The production arithmetic is exactly the mathematical overapproximation,
including ordered source substitutions and the separate native contexts. -/
theorem capacity_eq {checked : Checked} {base : Base checked} (inputs : Inputs base)
    (initial : SourceCoreCallableAncestryPairedCache.Table) :
    capacity inputs initial.states = SourceCoreCallableAncestryPairedPreparation.capacity inputs initial := by
  simp only [capacity, SourceCoreCallableAncestryPairedPreparation.capacity, fold_sum, Nat.zero_add,
    source_capacity_eq, SourceCoreCallableAncestryPairedCache.stateKey, alphabet, requirementProfile, nativeContexts]
  rfl

/-- Arithmetic capacity bounds all distinct valid keys, without enumerating
their unbounded frame histories or imposing an arbitrary preparation fuel. -/
theorem states_bounded {checked : Checked} {base : Base checked} (inputs : Inputs base)
    (roots states : List PairedState) (unique : (states.map key).Nodup)
    (valid : ∀ state ∈ states, Valid inputs roots state) : states.length ≤ capacity inputs roots := by
  rw [← keySpace_length]
  have subset : states.map key ⊆ keySpace inputs roots := by
    intro stateKey member
    obtain ⟨state, included, rfl⟩ := List.mem_map.mp member
    exact key_member (valid state included)
  simpa only [List.length_map] using unique.length_le_of_subset subset

theorem prepared_capacity_bound {checked : Checked} {base : Base checked} (inputs : Inputs base)
    (initial : SourceCoreCallableAncestryPairedCache.Table) (states : List PairedState)
    (unique : (states.map key).Nodup) (valid : ∀ state ∈ states, Valid inputs initial.states state) :
    states.length ≤ SourceCoreCallableAncestryPairedPreparation.capacity inputs initial := by
  rw [← capacity_eq]
  exact states_bounded inputs initial.states states unique valid

end Solcore.SourceSemantics.CoreLowering.CallableAncestryPairedProfiles
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableAncestryWorklist
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
end
