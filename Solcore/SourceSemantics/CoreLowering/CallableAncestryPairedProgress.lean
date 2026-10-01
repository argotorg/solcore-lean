import Solcore.SourceSemantics.CoreLowering.CallableAncestryPairedExpansion
import Solcore.SourceSemantics.CoreLowering.CallableAncestryPairedRecipes

/-! Processing the actual queue preserves sound rows and covers its processed
prefix. At queue exhaustion this discharges the production closure validator;
recipe preparation then also succeeds. Native frame provenance is separate. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableAncestryPairedProgress
open Frontend SourceInference TypeSystem CallableAncestryPairedLookup CallableAncestryPairedEdges
open CallableAncestryPairedExpansion
abbrev State := SourceCoreCallableAncestryReadRecipes.State

structure Progress {checked : Checked} {base : Base checked} (inputs : Inputs base)
    (position : Nat) (table : Table) : Prop where
  within : position ≤ table.states.length
  sound : RowsSound inputs table
  named : ∀ {id state}, SourceCoreCallableAncestryPairedPreparation.named? inputs id = some state → HasNamed table id
  lambda : ∀ {index state id}, index < position → table.stateAt? index = some state →
    SourceCoreCallableAncestryPairedPreparation.lambdaAllowed inputs state id = true → HasLambda table index id
  view : ∀ {callerIndex lexicalIndex caller lexical id target result},
    callerIndex < position → lexicalIndex < position →
    table.stateAt? callerIndex = some caller → table.stateAt? lexicalIndex = some lexical →
    SourceCoreCallableAncestryPairedPreparation.view? inputs caller lexical id target = some result →
      HasView table callerIndex lexicalIndex id target

theorem seed_progress {checked : Checked} {base : Base checked} (inputs : Inputs base) {initial : Table}
    (seeded : SourceCoreCallableAncestryPairedPreparation.seed inputs = .ok initial) : Progress inputs 0 initial := by
  unfold SourceCoreCallableAncestryPairedPreparation.seed at seeded
  obtain ⟨final, executed, result⟩ := bind_ok seeded
  cases result
  have rows : Extends ⟨[], [], [], []⟩ initial ∧ RowsSound inputs initial ∧
      ∀ entry ∈ inputs.callable.table.entries, ∀ state,
        SourceCoreCallableAncestryPairedPreparation.named? inputs entry.id = some state → HasNamed initial entry.id := by
    apply forIn_coverage executed (invariant := RowsSound inputs)
      (done := fun entry table => ∀ state, SourceCoreCallableAncestryPairedPreparation.named? inputs entry.id = some state → HasNamed table entry.id)
      ⟨by simp, by simp, by simp⟩
    · intro entry before after growth covered state generated
      exact (covered state generated).extend growth
    · intro entry entryMember table outcome previous ran
      cases origin : entry.origin with
      | named owner =>
        simp only [origin] at ran
        cases generated : SourceCoreCallableAncestryPairedPreparation.named? inputs entry.id with
        | none => simp [generated, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at ran
        | some state =>
          simp only [generated, pure, Except.pure, bind, Except.bind] at ran
          cases interned : SourceCoreCallableAncestryPairedPreparation.intern table.states state with
          | error error => simp [interned] at ran
          | ok result =>
            obtain ⟨position, states⟩ := result
            simp only [interned, Except.ok.injEq] at ran
            subst outcome
            obtain ⟨statePrefix, stored⟩ := intern_spec interned
            have oldSound := previous.reindex statePrefix
            let edge : SourceCoreCallableAncestryPairedCache.NamedEdge := ⟨entry.id, position⟩
            refine ⟨_, rfl, ⟨statePrefix, fun _ h => List.mem_append_left _ h, fun _ h => h, fun _ h => h⟩, ?_, ?_⟩
            · refine ⟨?_, oldSound.lambda, oldSound.view⟩
              intro row member
              rcases List.mem_append.mp member with old | new
              · exact oldSound.named row old
              · have same : row = edge := by simpa using new
                subst row
                exact ⟨state, generated, stored⟩
            · intro _ _; exact ⟨edge, by simp [edge], rfl⟩
      | lambda owner id active =>
        simp only [origin, pure, Except.pure, Except.ok.injEq] at ran
        subst outcome
        refine ⟨table, rfl, .refl _, previous, ?_⟩
        intro state generated
        simp [SourceCoreCallableAncestryPairedPreparation.named?, SourceCoreCallableAncestryPreparation.named?,
          CallableAncestryPairedValidation.stage_entry_self inputs.callable.table entryMember, origin] at generated
      | builtin builtin =>
        simp only [origin, pure, Except.pure, Except.ok.injEq] at ran
        subst outcome
        refine ⟨table, rfl, .refl _, previous, ?_⟩
        intro state generated
        simp [SourceCoreCallableAncestryPairedPreparation.named?, SourceCoreCallableAncestryPreparation.named?,
          CallableAncestryPairedValidation.stage_entry_self inputs.callable.table entryMember, origin] at generated
  refine ⟨Nat.zero_le _, rows.2.1, ?_, by intro index _ _ impossible; omega, by intro callerIndex _ _ _ _ _ _ impossible; omega⟩
  intro id state generated
  cases selected : inputs.callable.table.entryAt? id with
  | none => simp [SourceCoreCallableAncestryPairedPreparation.named?, SourceCoreCallableAncestryPreparation.named?, selected] at generated
  | some entry =>
    have identifier : entry.id = id := by simpa using List.find?_some selected
    exact identifier ▸ rows.2.2 entry (List.mem_of_find?_eq_some selected) state (identifier ▸ generated)

theorem Progress.expand {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {position : Nat} {table next : Table} {state : State}
    (progress : Progress inputs position table) (stored : table.stateAt? position = some state)
    (expanded : SourceCoreCallableAncestryPairedPreparation.expand inputs position state table = .ok next) :
    Progress inputs (position + 1) next := by
  obtain ⟨growth, sound, lambdas, views⟩ := expand_spec expanded progress.sound stored
  have positionLt : position < table.states.length := (List.getElem?_eq_some_iff.mp stored).1
  have lengthLe := growth.states.length_le
  have oldLookup : ∀ {index value}, index ≤ position → next.stateAt? index = some value → table.stateAt? index = some value := by
    intro index value below found
    exact (prefix_lookup_below growth.states (by omega)).symm.trans found
  refine ⟨by omega, sound, ?_, ?_, ?_⟩
  · intro id value generated
    exact (progress.named generated).extend growth
  · intro index value id below found generated
    have previous := oldLookup (by omega) found
    by_cases already : index < position
    · exact (progress.lambda already previous generated).extend growth
    · have sameIndex : index = position := by omega
      subst index
      have sameValue := Option.some.inj (previous.symm.trans stored)
      subst value
      exact lambdas id generated
  · intro callerIndex lexicalIndex caller lexical id target result callerBelow lexicalBelow callerFound lexicalFound generated
    have callerOld := oldLookup (by omega) callerFound
    have lexicalOld := oldLookup (by omega) lexicalFound
    by_cases callerBefore : callerIndex < position
    · by_cases lexicalBefore : lexicalIndex < position
      · exact (progress.view callerBefore lexicalBefore callerOld lexicalOld generated).extend growth
      · have sameIndex : lexicalIndex = position := by omega
        subst lexicalIndex
        have sameValue := Option.some.inj (lexicalOld.symm.trans stored)
        subst lexical
        exact (views callerIndex caller callerOld id target result).2 generated
    · have sameIndex : callerIndex = position := by omega
      subst callerIndex
      have sameValue := Option.some.inj (callerOld.symm.trans stored)
      subst caller
      exact (views lexicalIndex lexical lexicalOld id target result).1 generated

theorem Progress.complete {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {position : Nat} {table : Table} (progress : Progress inputs position table)
    (finished : table.stateAt? position = none) : Complete inputs table := by
  have lengthLe : table.states.length ≤ position := List.getElem?_eq_none_iff.mp finished
  refine ⟨progress.named, ?_, ?_⟩
  · intro index state id stored generated
    have below := (List.getElem?_eq_some_iff.mp stored).1
    exact progress.lambda (by omega) stored generated
  · intro callerIndex lexicalIndex caller lexical id target result callerStored lexicalStored generated
    have callerBelow := (List.getElem?_eq_some_iff.mp callerStored).1
    have lexicalBelow := (List.getElem?_eq_some_iff.mp lexicalStored).1
    exact progress.view (by omega) (by omega) callerStored lexicalStored generated

/-- Any successful execution of the real worklist, from its processed-prefix
invariant, passes the final Boolean validator. No validator premise is used. -/
theorem saturate_valid {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {fuel position : Nat} {table final : Table} (progress : Progress inputs position table)
    (completed : SourceCoreCallableAncestryPairedPreparation.saturate inputs fuel position table = .ok final) :
    SourceCoreCallableAncestryPairedPreparation.valid inputs final = true := by
  induction fuel generalizing position table with
  | zero =>
    cases selected : table.stateAt? position with
    | none =>
      simp only [SourceCoreCallableAncestryPairedPreparation.saturate, selected, Except.ok.injEq] at completed
      subst final
      exact validated progress.sound (progress.complete selected)
    | some state => simp [SourceCoreCallableAncestryPairedPreparation.saturate, selected] at completed
  | succ fuel ih =>
    cases selected : table.stateAt? position with
    | none =>
      simp only [SourceCoreCallableAncestryPairedPreparation.saturate, selected, Except.ok.injEq] at completed
      subst final
      exact validated progress.sound (progress.complete selected)
    | some state =>
      rw [SourceCoreCallableAncestryPairedPreparation.saturate, selected] at completed
      obtain ⟨next, expanded, finished⟩ := bind_ok completed
      exact ih (progress.expand selected expanded) finished

theorem seeded_saturation_valid {checked : Checked} {base : Base checked} (inputs : Inputs base)
    {initial final : Table} (seeded : SourceCoreCallableAncestryPairedPreparation.seed inputs = .ok initial)
    (completed : SourceCoreCallableAncestryPairedPreparation.saturate inputs
      (SourceCoreCallableAncestryPairedPreparation.capacity inputs initial) 0 initial = .ok final) :
    SourceCoreCallableAncestryPairedPreparation.valid inputs final = true :=
  saturate_valid (seed_progress inputs seeded) completed

/-- From successful named seeding, every remaining production worklist phase
has an actual successful result, including exact per-edge recipe preparation. -/
theorem seeded_completion_total {checked : Checked} {base : Base checked} (inputs : Inputs base)
    {initial : Table} (seeded : SourceCoreCallableAncestryPairedPreparation.seed inputs = .ok initial) :
    ∃ final, SourceCoreCallableAncestryPairedPreparation.saturate inputs
      (SourceCoreCallableAncestryPairedPreparation.capacity inputs initial) 0 initial = .ok final ∧
      SourceCoreCallableAncestryPairedPreparation.valid inputs final = true ∧
      ∃ recipes, final.views.attach.mapM (fun edge =>
        SourceCoreCallableAncestryPairedPreparation.prepareRecipe inputs final edge.val edge.property) = .ok recipes := by
  obtain ⟨final, completed, _⟩ := CallableAncestryPairedWorklist.seeded_saturation_total inputs seeded
  have valid := seeded_saturation_valid inputs seeded completed
  exact ⟨final, completed, valid, CallableAncestryPairedRecipes.recipes_total valid⟩

end Solcore.SourceSemantics.CoreLowering.CallableAncestryPairedProgress
