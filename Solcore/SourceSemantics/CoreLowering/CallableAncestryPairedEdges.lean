import Solcore.SourceSemantics.CoreLowering.CallableAncestryPairedWorklist

/-! Append-only state indices and exact edge provenance for the actual paired
worklist. These properties are maintained independently of the final Boolean
validator, so they can be used to prove that validator succeeds. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableAncestryPairedEdges
open Frontend SourceInference TypeSystem CallableAncestryPairedLookup
abbrev State := SourceCoreCallableAncestryReadRecipes.State

structure Extends (before after : Table) : Prop where
  states : before.states <+: after.states
  named : before.named ⊆ after.named
  lambdas : before.lambdas ⊆ after.lambdas
  views : before.views ⊆ after.views

theorem Extends.refl (table : Table) : Extends table table :=
  ⟨⟨[], by simp⟩, fun _ h => h, fun _ h => h, fun _ h => h⟩

theorem Extends.trans {first middle last : Table} (left : Extends first middle) (right : Extends middle last) :
    Extends first last :=
  ⟨left.states.trans right.states, fun _ h => right.named (left.named h),
    fun _ h => right.lambdas (left.lambdas h), fun _ h => right.views (left.views h)⟩

theorem prefix_lookup {α : Type} {before after : List α} (growth : before <+: after)
    {position : Nat} {value : α} (found : before[position]? = some value) : after[position]? = some value := by
  obtain ⟨suffix, rfl⟩ := growth
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
  exact found

theorem prefix_lookup_below {α : Type} {before after : List α} (growth : before <+: after)
    {position : Nat} (below : position < before.length) : after[position]? = before[position]? := by
  obtain ⟨suffix, rfl⟩ := growth
  exact List.getElem?_append_left below

theorem Extends.lookup {before after : Table} (growth : Extends before after)
    {position : Nat} {state : State} (found : before.stateAt? position = some state) : after.stateAt? position = some state :=
  prefix_lookup growth.states found

theorem intern_spec {states output : List State} {state : State} {position : Nat}
    (accepted : SourceCoreCallableAncestryPairedPreparation.intern states state = .ok (position, output)) :
    states <+: output ∧ output[position]? = some state := by
  unfold SourceCoreCallableAncestryPairedPreparation.intern at accepted
  split at accepted
  · cases accepted
    exact ⟨⟨[state], rfl⟩, by simp⟩
  · next previous index selected =>
    split at accepted
    · next same =>
      cases accepted
      have lookup := List.mk_mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some selected)
      exact ⟨⟨[], by simp⟩, same ▸ lookup⟩
    · cases accepted

structure RowsSound {checked : Checked} {base : Base checked} (inputs : Inputs base) (table : Table) : Prop where
  named : ∀ edge ∈ table.named, ∃ state,
    SourceCoreCallableAncestryPairedPreparation.named? inputs edge.origin = some state ∧ table.stateAt? edge.destination = some state
  lambda : ∀ edge ∈ table.lambdas, ∃ state, table.stateAt? edge.state = some state ∧
    SourceCoreCallableAncestryPairedPreparation.lambdaAllowed inputs state edge.origin = true
  view : ∀ edge ∈ table.views, ∃ caller lexical result,
    table.stateAt? edge.caller = some caller ∧ table.stateAt? edge.lexical = some lexical ∧
      SourceCoreCallableAncestryPairedPreparation.view? inputs caller lexical edge.view edge.target = some result ∧
      table.stateAt? edge.destination = some result

theorem RowsSound.reindex {checked : Checked} {base : Base checked} {inputs : Inputs base} {table : Table}
    (sound : RowsSound inputs table) {states : List State} (growth : table.states <+: states) :
    RowsSound inputs {table with states} := by
  constructor
  · intro edge member
    obtain ⟨state, generated, stored⟩ := sound.named edge member
    exact ⟨state, generated, prefix_lookup growth stored⟩
  · intro edge member
    obtain ⟨state, stored, generated⟩ := sound.lambda edge member
    exact ⟨state, prefix_lookup growth stored, generated⟩
  · intro edge member
    obtain ⟨caller, lexical, result, callerStored, lexicalStored, generated, stored⟩ := sound.view edge member
    exact ⟨caller, lexical, result, prefix_lookup growth callerStored, prefix_lookup growth lexicalStored,
      generated, prefix_lookup growth stored⟩

def HasNamed (table : Table) (id : Core.Word) : Prop := ∃ edge ∈ table.named, edge.origin = id
def HasLambda (table : Table) (position : Nat) (id : Core.Word) : Prop :=
  ∃ edge ∈ table.lambdas, edge.state = position ∧ edge.origin = id
def HasView (table : Table) (caller lexical : Nat) (id target : Core.Word) : Prop :=
  ∃ edge ∈ table.views, edge.caller = caller ∧ edge.lexical = lexical ∧ edge.view = id ∧ edge.target = target

theorem HasNamed.extend {before after : Table} (growth : Extends before after) {id : Core.Word}
    (covered : HasNamed before id) : HasNamed after id := by
  obtain ⟨edge, member, selected⟩ := covered
  exact ⟨edge, growth.named member, selected⟩

theorem HasLambda.extend {before after : Table} (growth : Extends before after) {position : Nat} {id : Core.Word}
    (covered : HasLambda before position id) : HasLambda after position id := by
  obtain ⟨edge, member, selected⟩ := covered
  exact ⟨edge, growth.lambdas member, selected⟩

theorem HasView.extend {before after : Table} (growth : Extends before after)
    {caller lexical : Nat} {id target : Core.Word} (covered : HasView before caller lexical id target) :
    HasView after caller lexical id target := by
  obtain ⟨edge, member, selected⟩ := covered
  exact ⟨edge, growth.views member, selected⟩

theorem addView_spec {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {before after : Table} {callerIndex lexicalIndex : Nat} {caller lexical : State} {id target : Core.Word}
    (accepted : SourceCoreCallableAncestryPairedPreparation.addView inputs before callerIndex lexicalIndex caller lexical id target = .ok after)
    (sound : RowsSound inputs before) (callerStored : before.stateAt? callerIndex = some caller)
    (lexicalStored : before.stateAt? lexicalIndex = some lexical) :
    Extends before after ∧ RowsSound inputs after ∧
      (∀ result, SourceCoreCallableAncestryPairedPreparation.view? inputs caller lexical id target = some result →
        HasView after callerIndex lexicalIndex id target) := by
  unfold SourceCoreCallableAncestryPairedPreparation.addView at accepted
  cases generated : SourceCoreCallableAncestryPairedPreparation.view? inputs caller lexical id target with
  | none =>
    simp only [generated, pure, Except.pure, Except.ok.injEq] at accepted
    subst after
    exact ⟨.refl _, sound, by intro result impossible; cases impossible⟩
  | some state =>
    simp only [generated] at accepted
    cases interned : SourceCoreCallableAncestryPairedPreparation.intern before.states state with
    | error error => simp [interned, bind, Except.bind] at accepted
    | ok result =>
      obtain ⟨position, states⟩ := result
      simp only [interned, bind, Except.bind] at accepted
      obtain ⟨statePrefix, stored⟩ := intern_spec interned
      have oldSound := sound.reindex statePrefix
      let edge : SourceCoreCallableAncestryPairedCache.ViewEdge := ⟨callerIndex, lexicalIndex, id, target, position⟩
      split at accepted
      · next existsEdge =>
        cases accepted
        refine ⟨⟨statePrefix, fun _ h => h, fun _ h => h, fun _ h => h⟩, oldSound, ?_⟩
        intro result _
        obtain ⟨existing, member, same⟩ := List.any_eq_true.mp existsEdge
        have equal : existing = edge := by simpa only [decide_eq_true_eq] using same
        exact ⟨existing, member, by simp [equal, edge]⟩
      · cases accepted
        refine ⟨⟨statePrefix, fun _ h => h, fun _ h => h, fun _ h => List.mem_append_left _ h⟩, ?_, ?_⟩
        · refine ⟨oldSound.named, oldSound.lambda, ?_⟩
          intro existing member
          rcases List.mem_append.mp member with previous | new
          · exact oldSound.view existing previous
          · have equal : existing = edge := by simpa using new
            subst existing
            exact ⟨caller, lexical, state, prefix_lookup statePrefix callerStored, prefix_lookup statePrefix lexicalStored,
              generated, stored⟩
        · intro result _
          exact ⟨edge, by simp [edge], rfl, rfl, rfl, rfl⟩

private theorem find_exists {α : Type} {items : List α} {predicate : α → Bool}
    (existsItem : ∃ item ∈ items, predicate item = true) : ∃ item, items.find? predicate = some item := by
  cases selected : items.find? predicate with
  | some item => exact ⟨item, rfl⟩
  | none =>
    obtain ⟨item, member, accepted⟩ := existsItem
    exact False.elim (List.find?_eq_none.mp selected item member accepted)

theorem HasNamed.found {table : Table} {id : Core.Word} (covered : HasNamed table id) :
    ∃ position, table.namedAt? id = some position := by
  obtain ⟨edge, member, origin⟩ := covered
  obtain ⟨selected, found⟩ := find_exists (items := table.named) (predicate := fun row => decide (row.origin = id))
    ⟨edge, member, by simpa using origin⟩
  exact ⟨selected.destination, by simp only [SourceCoreCallableAncestryPairedCache.Table.namedAt?, found, Option.map_some]⟩

theorem HasLambda.allowed {table : Table} {position : Nat} {id : Core.Word} (covered : HasLambda table position id) :
    table.lambdaAllowed position id = true := by
  obtain ⟨edge, member, selected⟩ := covered
  exact List.any_eq_true.mpr ⟨edge, member, by simpa using selected⟩

theorem HasView.found {table : Table} {caller lexical : Nat} {id target : Core.Word}
    (covered : HasView table caller lexical id target) : ∃ position, table.viewAt? caller lexical id target = some position := by
  obtain ⟨edge, member, shape⟩ := covered
  obtain ⟨selected, found⟩ := find_exists (items := table.views) (predicate := fun row => decide
    (row.caller = caller ∧ row.lexical = lexical ∧ row.view = id ∧ row.target = target))
    ⟨edge, member, by simpa using shape⟩
  exact ⟨selected.destination, by simp only [SourceCoreCallableAncestryPairedCache.Table.viewAt?, found, Option.map_some]⟩

theorem RowsSound.sound {checked : Checked} {base : Base checked} {inputs : Inputs base} {table : Table}
    (sound : RowsSound inputs table) : Sound inputs table := by
  constructor
  · intro id position found
    unfold SourceCoreCallableAncestryPairedCache.Table.namedAt? at found
    cases selected : table.named.find? (fun edge => decide (edge.origin = id)) with
    | none => rw [selected] at found; cases found
    | some edge =>
      have origin : edge.origin = id := by simpa using List.find?_some selected
      have destination : edge.destination = position := by simpa only [selected, Option.map_some, Option.some.injEq] using found
      obtain ⟨state, generated, stored⟩ := sound.named edge (List.mem_of_find?_eq_some selected)
      exact ⟨state, origin ▸ generated, destination ▸ stored⟩
  · intro position state id stored allowed
    obtain ⟨edge, member, selected⟩ := List.any_eq_true.mp allowed
    have shape : edge.state = position ∧ edge.origin = id := by simpa using selected
    obtain ⟨actual, found, generated⟩ := sound.lambda edge member
    rw [shape.1] at found
    have same := Option.some.inj (found.symm.trans stored)
    simpa only [same, shape.2] using generated
  · intro callerIndex lexicalIndex caller lexical id target position callerStored lexicalStored found
    unfold SourceCoreCallableAncestryPairedCache.Table.viewAt? at found
    cases selected : table.views.find? (fun edge => decide
        (edge.caller = callerIndex ∧ edge.lexical = lexicalIndex ∧ edge.view = id ∧ edge.target = target)) with
    | none => rw [selected] at found; cases found
    | some edge =>
      have shape : edge.caller = callerIndex ∧ edge.lexical = lexicalIndex ∧ edge.view = id ∧ edge.target = target := by
        simpa using List.find?_some selected
      have destination : edge.destination = position := by simpa only [selected, Option.map_some, Option.some.injEq] using found
      obtain ⟨actualCaller, actualLexical, result, callerFound, lexicalFound, generated, stored⟩ :=
        sound.view edge (List.mem_of_find?_eq_some selected)
      rw [shape.1] at callerFound
      rw [shape.2.1] at lexicalFound
      have sameCaller := Option.some.inj (callerFound.symm.trans callerStored)
      have sameLexical := Option.some.inj (lexicalFound.symm.trans lexicalStored)
      exact ⟨result, by simpa only [sameCaller, sameLexical, shape.2.2.1, shape.2.2.2] using generated,
        destination ▸ stored⟩

structure Complete {checked : Checked} {base : Base checked} (inputs : Inputs base) (table : Table) : Prop where
  named : ∀ {id state}, SourceCoreCallableAncestryPairedPreparation.named? inputs id = some state → HasNamed table id
  lambda : ∀ {position state id}, table.stateAt? position = some state →
    SourceCoreCallableAncestryPairedPreparation.lambdaAllowed inputs state id = true → HasLambda table position id
  view : ∀ {callerIndex lexicalIndex caller lexical id target result},
    table.stateAt? callerIndex = some caller → table.stateAt? lexicalIndex = some lexical →
    SourceCoreCallableAncestryPairedPreparation.view? inputs caller lexical id target = some result →
      HasView table callerIndex lexicalIndex id target

theorem Complete.closed {checked : Checked} {base : Base checked} {inputs : Inputs base} {table : Table}
    (complete : Complete inputs table) (sound : RowsSound inputs table) : Closed inputs table := by
  constructor
  · intro id state generated
    obtain ⟨position, selected⟩ := (complete.named generated).found
    obtain ⟨actual, found, stored⟩ := sound.sound.named selected
    have same := Option.some.inj (found.symm.trans generated)
    exact ⟨position, selected, same ▸ stored⟩
  · intro position state id stored generated
    exact (complete.lambda stored generated).allowed
  · intro callerIndex lexicalIndex caller lexical id target result callerStored lexicalStored generated
    obtain ⟨position, selected⟩ := (complete.view callerStored lexicalStored generated).found
    obtain ⟨actual, found, stored⟩ := sound.sound.view callerStored lexicalStored selected
    have same := Option.some.inj (found.symm.trans generated)
    exact ⟨position, selected, same ▸ stored⟩

theorem validated {checked : Checked} {base : Base checked} {inputs : Inputs base} {table : Table}
    (sound : RowsSound inputs table) (complete : Complete inputs table) :
    SourceCoreCallableAncestryPairedPreparation.valid inputs table = true := by
  have closed := complete.closed sound
  simp only [SourceCoreCallableAncestryPairedPreparation.valid, Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · apply List.all_eq_true.mpr
    intro edge member
    obtain ⟨state, generated, stored⟩ := sound.named edge member
    simp [generated, stored]
  · apply List.all_eq_true.mpr
    intro edge member
    obtain ⟨state, stored, generated⟩ := sound.lambda edge member
    simp [stored, generated]
  · apply List.all_eq_true.mpr
    intro edge member
    obtain ⟨caller, lexical, result, callerStored, lexicalStored, generated, stored⟩ := sound.view edge member
    simp [callerStored, lexicalStored, generated, stored]
  · apply List.all_eq_true.mpr
    intro entry _
    cases generated : SourceCoreCallableAncestryPairedPreparation.named? inputs entry.id with
    | none => rfl
    | some state =>
      obtain ⟨position, selected, stored⟩ := closed.named generated
      simp [selected, stored]
  · apply List.all_eq_true.mpr
    intro caller callerMember
    have callerStored := List.mk_mem_zipIdx_iff_getElem?.mp callerMember
    simp only [Bool.and_eq_true]
    constructor
    · apply List.all_eq_true.mpr
      intro template _
      cases allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed inputs caller.1 template.descriptor with
      | false => rfl
      | true => simp [closed.lambda callerStored allowed]
    · apply List.all_eq_true.mpr
      intro lexical lexicalMember
      have lexicalStored := List.mk_mem_zipIdx_iff_getElem?.mp lexicalMember
      apply List.all_eq_true.mpr
      intro entry _
      cases targetSelected : inputs.callable.table.idAt? (.lambda entry.view.owner entry.view.principal.initializer entry.view.cumulative) with
      | none => rfl
      | some target =>
        cases generated : SourceCoreCallableAncestryPairedPreparation.view? inputs caller.1 lexical.1 entry.id target with
        | none => simp only [generated]
        | some result =>
          obtain ⟨position, selected, stored⟩ := closed.view callerStored lexicalStored generated
          simp [generated, selected, stored]

end Solcore.SourceSemantics.CoreLowering.CallableAncestryPairedEdges
