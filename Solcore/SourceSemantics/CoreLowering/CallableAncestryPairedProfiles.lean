import Solcore.SourceSemantics.CoreLowering.CallableAncestryReadRecipes
import Solcore.SourceSemantics.CoreLowering.CallableAncestryCardinality
import Solcore.Frontend.SourceCoreCallableAncestryPairedPreparation

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
