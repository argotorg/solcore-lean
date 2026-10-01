import Solcore.SourceSemantics.CoreLowering.CallableAncestryMetadata
import Solcore.SourceSemantics.CoreLowering.EmptySourceSubstitution
import Solcore.TypeSystem.SubstitutionProperties

/-! Invariants for occurrence-sensitive callable ancestry metadata. These
proofs concern retained metadata only: they do not evaluate source bodies or
resolve dictionaries during a runtime call. A requirement profile records the
actual IDs at every occurrence, rather than identifying equal types with equal
source metadata. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableAncestryProfiles
open Frontend SourceInference TypeSystem
open CallableAncestryMetadata

private theorem bind_ok {α β ε : Type} {computation : Except ε α} {next : α → Except ε β}
    {result : β} (accepted : computation >>= next = .ok result) :
    ∃ value, computation = .ok value ∧ next value = .ok result := by
  cases computation with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem forIn_invariant {α β ε : Type} {items : List α} {initial final : β}
    {step : α → β → Except ε (ForInStep β)} {invariant : β → Prop}
    (accepted : forIn items initial step = .ok final) (start : invariant initial)
    (each : ∀ item, item ∈ items → ∀ state outcome, invariant state → step item state = .ok outcome →
      ∃ updated, outcome = .yield updated ∧ invariant updated) : invariant final := by
  induction items generalizing initial with
  | nil =>
    simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] at accepted
    exact accepted ▸ start
  | cons item items ih =>
    rw [List.forIn_cons] at accepted
    obtain ⟨outcome, ran, accepted⟩ := bind_ok accepted
    obtain ⟨updated, rfl, preserved⟩ := each item List.mem_cons_self initial outcome start ran
    exact ih accepted preserved (fun next member => each next (List.mem_cons_of_mem item member))

def alphabet (source : TypedSource) : List RequirementId :=
  (requirementProfile source).flatten

def Bounded (ids : List RequirementId) (source : TypedSource) : Prop :=
  ∀ spine ∈ requirementProfile source, ∀ requirement ∈ spine, requirement ∈ ids

theorem bounded_alphabet (source : TypedSource) : Bounded (alphabet source) source := by
  intro spine member requirement occurs
  exact List.mem_flatten.mpr ⟨spine, member, occurs⟩

@[simp] theorem profile_substitute (source : TypedSource) (substitution : Substitution) :
    requirementProfile (source.applySubstitution substitution) = requirementProfile source := by
  simp only [requirementProfile, TypedSource.applySubstitution, List.map_map]
  apply List.map_congr_left
  intro node _
  cases node <;> rfl

@[simp] theorem profile_rewrite (source : TypedSource) (witnesses : List Witness) :
    requirementProfile (SourceTypedRuntime.rewriteLocalRequirements witnesses source) =
      (requirementProfile source).map (List.map (SourceTypedRuntime.rewriteLocalRequirement witnesses)) := by
  simp only [requirementProfile, SourceTypedRuntime.rewriteLocalRequirements, List.map_map]
  apply List.map_congr_left
  intro node _
  cases node <;> rfl

@[simp] theorem lengths_rewrite (source : TypedSource) (witnesses : List Witness) :
    (requirementProfile (SourceTypedRuntime.rewriteLocalRequirements witnesses source)).map List.length =
      (requirementProfile source).map List.length := by
  simp only [profile_rewrite, List.map_map, Function.comp_def, List.length_map]

theorem SourceRecipe.lengths {original source : TypedSource} (recipe : SourceRecipe original source) :
    (requirementProfile source).map List.length = (requirementProfile original).map List.length := by
  induction recipe with
  | unchanged => rfl
  | «instance» _ _ _ ih => rw [lengths_rewrite, profile_substitute]; exact ih

theorem ViewStep.lengths {checked : Checked} {base : Base checked} {owned : Owned base}
    {id target : Core.Word} {view : ViewAt owned id target} {before : CallableAncestryMetadata.State} (step : ViewStep view before) :
    (requirementProfile step.after.source).map List.length = (requirementProfile before.source).map List.length := by
  simp [ViewStep.after]

theorem rewrite_id_bounded {ids : List RequirementId} {witnesses : List Witness}
    (witnessesBounded : ∀ witness ∈ witnesses, witness.actualRequirement ∈ ids)
    {requirement : RequirementId} (member : requirement ∈ ids) :
    SourceTypedRuntime.rewriteLocalRequirement witnesses requirement ∈ ids := by
  unfold SourceTypedRuntime.rewriteLocalRequirement
  split
  · next witness found => exact witnessesBounded witness (List.mem_of_find?_eq_some found)
  · exact member

theorem bounded_rewrite {ids : List RequirementId} {source : TypedSource} {witnesses : List Witness}
    (sourceBounded : Bounded ids source)
    (witnessesBounded : ∀ witness ∈ witnesses, witness.actualRequirement ∈ ids) :
    Bounded ids (SourceTypedRuntime.rewriteLocalRequirements witnesses source) := by
  intro spine member requirement occurs
  rw [profile_rewrite] at member
  obtain ⟨oldSpine, oldMember, rfl⟩ := List.mem_map.mp member
  obtain ⟨oldRequirement, oldOccurs, rfl⟩ := List.mem_map.mp occurs
  exact rewrite_id_bounded witnessesBounded (sourceBounded oldSpine oldMember oldRequirement oldOccurs)

theorem bounded_substitute {ids : List RequirementId} {source : TypedSource}
    (bounded : Bounded ids source) (substitution : Substitution) :
    Bounded ids (source.applySubstitution substitution) := by
  simpa only [Bounded, profile_substitute] using bounded

theorem lookup_requirements_bounded {ids : List RequirementId} {source : TypedSource}
    {id : ExpressionId} {node : ExpressionNode} (bounded : Bounded ids source)
    (found : source.lookupExpression? id = some node) :
    ∀ requirement ∈ node.requirements, requirement ∈ ids := by
  have member : Node.expression node ∈ source.nodes := by
    unfold TypedSource.lookupExpression? TypedSource.lookupNode? at found
    split at found
    · next selected selectedEq =>
      cases found
      exact List.mem_of_find?_eq_some selectedEq
    · cases found
  exact bounded node.requirements (List.mem_map.mpr ⟨.expression node, member, rfl⟩)

theorem ordinary_requirements_subset {node : ExpressionNode} {requirements : List RequirementId}
    (accepted : SourceCompilationPlan.ordinaryOwnedRequirements? node = some requirements) :
    ∀ requirement ∈ requirements, requirement ∈ node.requirements := by
  unfold SourceCompilationPlan.ordinaryOwnedRequirements? at accepted
  dsimp only at accepted
  split at accepted
  · cases accepted
  · split at accepted
    · cases accepted
      intro requirement member
      exact List.mem_of_mem_take member
    · cases accepted

@[simp] theorem erase_substitute (source : TypedSource) (substitution : Substitution) :
    eraseRequirements (source.applySubstitution substitution) =
      (eraseRequirements source).applySubstitution substitution := by
  simp only [eraseRequirements, TypedSource.applySubstitution, List.map_map]
  congr 1
  apply List.map_congr_left
  intro node _
  cases node <;> rfl

theorem ViewStep.erase {checked : Checked} {base : Base checked} {owned : Owned base}
    {id target : Core.Word} {view : ViewAt owned id target} {before : CallableAncestryMetadata.State}
    (step : ViewStep view before) :
    eraseRequirements step.after.source =
      (eraseRequirements before.source).applySubstitution view.entry.view.ownSubstitution := by
  change eraseRequirements (SourceTypedRuntime.rewriteLocalRequirements step.witnesses
    (before.source.applySubstitution step.substitution)) = _
  rw [rewrite_erased, erase_substitute, step.substitutionExact]

/-- A canonical source is transported by the actual selected view's exact
substitution. This law does not assume arbitrary source substitutions commute
with quantified binders, nor erase the occurrence-specific requirement IDs. -/
theorem ViewStep.canonical {checked : Checked} {base : Base checked} {owned : Owned base}
    {id target : Core.Word} {view : ViewAt owned id target} {before : CallableAncestryMetadata.State}
    (step : ViewStep view before) {canonical : TypedSource}
    (beforeCanonical : eraseRequirements before.source = eraseRequirements canonical) :
    step.after.owner = view.entry.view.owner ∧ step.after.active = view.entry.view.cumulative ∧
      eraseRequirements step.after.source =
        eraseRequirements (canonical.applySubstitution view.entry.view.ownSubstitution) := by
  refine ⟨step.owner, step.cumulative, ?_⟩
  rw [ViewStep.erase step, beforeCanonical, erase_substitute]

/-- Every actual ID emitted by the real matching loop is taken from the
reference's requirement spine. Predicate and dictionary checks cannot invent
new occurrence identities. -/
theorem bindings_actual_subset {caller : SourceSpecialization.SpecializedFunction}
    {binder : TypedBinder} {node : ExpressionNode} {substitution : Substitution}
    {bindings : List SourceCompilationPlan.LocalRequirementBinding}
    (accepted : SourceCompilationPlan.localRequirementBindings caller binder node = .ok (substitution, bindings)) :
    ∀ binding ∈ bindings, binding.actualRequirement ∈ node.requirements := by
  unfold SourceCompilationPlan.localRequirementBindings at accepted
  simp (maxSteps := 1000000) only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at accepted
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  obtain ⟨final, loop, accepted⟩ := bind_ok accepted
  cases accepted
  apply forIn_invariant (invariant := fun current => ∀ binding ∈ current, binding.actualRequirement ∈ node.requirements) loop
  · simp
  · intro pair member current outcome prior iteration
    rcases pair with ⟨template, actual⟩
    have actualMember : actual ∈ node.requirements := List.of_mem_zip member |>.2
    try dsimp only at iteration
    obtain ⟨templateSolved, _, iteration⟩ := bind_ok iteration
    try dsimp only at iteration
    split at iteration <;> try contradiction
    split at iteration <;> try contradiction
    split at iteration <;> try contradiction
    split at iteration <;> try contradiction
    obtain ⟨actualSolved, _, iteration⟩ := bind_ok iteration
    try dsimp only at iteration
    split at iteration <;> try contradiction
    split at iteration <;> try contradiction
    cases iteration
    refine ⟨_, rfl, ?_⟩
    intro binding member
    rcases List.mem_append.mp member with old | fresh
    · exact prior binding old
    · cases List.mem_singleton.mp fresh
      exact actualMember

theorem witnesses_actual_subset {caller : SourceSpecialization.SpecializedFunction}
    {available : SourceCompilationPlan.EvidenceEnvironment} {binder : TypedBinder} {node : ExpressionNode}
    {substitution : Substitution} {witnesses : List Witness}
    (accepted : SourceCompilationPlan.localRequirementWitnesses caller available binder node = .ok (substitution, witnesses)) :
    ∀ witness ∈ witnesses, witness.actualRequirement ∈ node.requirements := by
  unfold SourceCompilationPlan.localRequirementWitnesses at accepted
  obtain ⟨⟨matched, bindings⟩, bound, accepted⟩ := bind_ok accepted
  obtain ⟨final, loop, accepted⟩ := bind_ok accepted
  cases accepted
  apply forIn_invariant (invariant := fun current => ∀ witness ∈ current, witness.actualRequirement ∈ node.requirements) loop
  · simp
  · intro binding member current outcome prior iteration
    have actualMember := bindings_actual_subset bound binding member
    dsimp only at iteration
    simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at iteration
    split at iteration
    · next evidence caseEq =>
      cases iteration
      refine ⟨_, rfl, ?_⟩
      intro witness member
      rcases List.mem_append.mp member with old | fresh
      · exact prior witness old
      · cases List.mem_singleton.mp fresh
        exact actualMember
    · split at iteration <;> try contradiction
      cases iteration
      refine ⟨_, rfl, ?_⟩
      intro witness member
      rcases List.mem_append.mp member with old | fresh
      · exact prior witness old
      · cases List.mem_singleton.mp fresh
        exact actualMember

theorem ViewStep.actual_ids_bounded {checked : Checked} {base : Base checked} {owned : Owned base}
    {id target : Core.Word} {view : ViewAt owned id target} {before : CallableAncestryMetadata.State}
    (step : ViewStep view before) {ids : List RequirementId} (bounded : Bounded ids before.source) :
    ∀ witness ∈ step.witnesses, witness.actualRequirement ∈ ids := by
  intro witness member
  have selected := witnesses_actual_subset step.factory witness member
  have owned := ordinary_requirements_subset step.requirementLayout witness.actualRequirement selected
  exact lookup_requirements_bounded bounded step.found _ owned

theorem ViewStep.bounded {checked : Checked} {base : Base checked} {owned : Owned base}
    {id target : Core.Word} {view : ViewAt owned id target} {before : CallableAncestryMetadata.State}
    (step : ViewStep view before) {ids : List RequirementId} (bounded : Bounded ids before.source) :
    Bounded ids step.after.source :=
  bounded_rewrite (bounded_substitute bounded step.substitution) (ViewStep.actual_ids_bounded step bounded)

/-- The actual factories keep every reachable expression requirement inside
the original named source's finite alphabet, for arbitrary finite ancestry
depth. No supplied witness-range or child evaluation premise is needed. -/
theorem Authenticates.original_bound {checked : Checked} {base : Base checked} {owned : Owned base}
    {frame : ContextFrame} {state : CallableAncestryMetadata.State}
    (authenticated : Authenticates owned frame (some state)) :
    ∃ (id : Core.Word) (named : Named owned id), state.owner = named.state.owner ∧
      Bounded (alphabet named.state.source) state.source ∧
      (requirementProfile state.source).map List.length = (requirementProfile named.state.source).map List.length := by
  generalize resultEq : some state = result at authenticated
  induction authenticated generalizing state with
  | empty => cases resultEq
  | named receipt => cases resultEq; exact ⟨_, receipt, rfl, bounded_alphabet _, rfl⟩
  | lambda parent receipt metadata ih => exact ih resultEq
  | view parent receipt step ih =>
    cases resultEq
    obtain ⟨id, named, owner, bounded, lengths⟩ := ih rfl
    exact ⟨id, named, owner, ViewStep.bounded step bounded, (ViewStep.lengths step).trans lengths⟩



end Solcore.SourceSemantics.CoreLowering.CallableAncestryProfiles
