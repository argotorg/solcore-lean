import Solcore.SourceSemantics.CoreLowering.Internal.Callable.AncestryWorklists

/-!
# Callable ancestry: pairing

Lookup, validation, worklists, edges, expansion, recipes and progress of paired ancestry.

The seeds are in `Callable/MethodOrigins` on purpose. They open both `CallableAncestryPairedExpansion` and `CallableAncestryPairedWorklist`, and in this file the private `bind_ok` of the second would make their use of the first ambiguous.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableAncestryPairedLookup
/-! Completed paired-table lookup and the pure metadata-factory domain.
An applied view has two independent parent derivations: the read caller and
the lexical principal. Authentication here is metadata provenance, not runtime
execution history. Native snapshot/code/capture coverage is a separate layer. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableAncestryPairedLookup
open Frontend SourceInference TypeSystem
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev Base := SourceCoreCompatibleFunctions.Prepared
abbrev Inputs := @SourceCoreCallableAncestryPreparation.Inputs
abbrev State := SourceCoreCallableAncestryReadRecipes.State
abbrev Frame := SourceCoreCallablePairedFrames.Frame
abbrev Table := SourceCoreCallableAncestryPairedCache.Table

inductive Authenticates {checked : Checked} {base : Base checked} (inputs : Inputs base) :
    Frame → Option State → Prop where
  | empty : Authenticates inputs .empty none
  | named {id : Core.Word} {state : State}
      (selected : SourceCoreCallableAncestryPairedPreparation.named? inputs id = some state) :
      Authenticates inputs (.named id) (some state)
  | lambda {parent : Frame} {state : State} {id : Core.Word}
      (ancestry : Authenticates inputs parent (some state))
      (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed inputs state id = true) :
      Authenticates inputs (.lambda id parent) (some state)
  | appliedView {callerFrame lexicalFrame : Frame} {caller lexical result : State} {id target : Core.Word}
      (callerAncestry : Authenticates inputs callerFrame (some caller))
      (lexicalAncestry : Authenticates inputs lexicalFrame (some lexical))
      (selected : SourceCoreCallableAncestryPairedPreparation.view? inputs caller lexical id target = some result) :
      Authenticates inputs (.appliedView id target callerFrame lexicalFrame) (some result)

structure Sound {checked : Checked} {base : Base checked} (inputs : Inputs base) (table : Table) : Prop where
  named : ∀ {id position}, table.namedAt? id = some position → ∃ state,
    SourceCoreCallableAncestryPairedPreparation.named? inputs id = some state ∧ table.stateAt? position = some state
  lambda : ∀ {position state id}, table.stateAt? position = some state → table.lambdaAllowed position id = true →
    SourceCoreCallableAncestryPairedPreparation.lambdaAllowed inputs state id = true
  view : ∀ {callerIndex lexicalIndex caller lexical id target position},
    table.stateAt? callerIndex = some caller → table.stateAt? lexicalIndex = some lexical →
    table.viewAt? callerIndex lexicalIndex id target = some position → ∃ result,
      SourceCoreCallableAncestryPairedPreparation.view? inputs caller lexical id target = some result ∧
        table.stateAt? position = some result

structure Closed {checked : Checked} {base : Base checked} (inputs : Inputs base) (table : Table) : Prop where
  named : ∀ {id state}, SourceCoreCallableAncestryPairedPreparation.named? inputs id = some state →
    ∃ position, table.namedAt? id = some position ∧ table.stateAt? position = some state
  lambda : ∀ {position state id}, table.stateAt? position = some state →
    SourceCoreCallableAncestryPairedPreparation.lambdaAllowed inputs state id = true → table.lambdaAllowed position id = true
  view : ∀ {callerIndex lexicalIndex caller lexical id target result},
    table.stateAt? callerIndex = some caller → table.stateAt? lexicalIndex = some lexical →
    SourceCoreCallableAncestryPairedPreparation.view? inputs caller lexical id target = some result →
    ∃ position, table.viewAt? callerIndex lexicalIndex id target = some position ∧ table.stateAt? position = some result

def IndexMeaning {checked : Checked} {base : Base checked} (inputs : Inputs base) (table : Table)
    (frame : Frame) : Option Nat → Prop
  | none => Authenticates inputs frame none
  | some position => ∃ state, table.stateAt? position = some state ∧ Authenticates inputs frame (some state)

theorem lookupIndex_sound {checked : Checked} {base : Base checked} {inputs : Inputs base} {table : Table}
    (sound : Sound inputs table) (frame : Frame) {result : Option Nat}
    (found : table.lookupIndex? frame = some result) : IndexMeaning inputs table frame result := by
  induction frame generalizing result with
  | empty => cases found; exact .empty
  | named id =>
    cases selected : table.namedAt? id with
    | none => simp [SourceCoreCallableAncestryPairedCache.Table.lookupIndex?, selected] at found
    | some position =>
      simp only [SourceCoreCallableAncestryPairedCache.Table.lookupIndex?, selected, Option.map_some, Option.some.injEq] at found
      subst result
      obtain ⟨state, generated, stored⟩ := sound.named selected
      exact ⟨state, stored, .named generated⟩
  | lambda id parent ih =>
    cases parentResult : table.lookupIndex? parent with
    | none => simp [SourceCoreCallableAncestryPairedCache.Table.lookupIndex?, parentResult] at found
    | some parentIndex =>
      cases parentIndex with
      | none => simp [SourceCoreCallableAncestryPairedCache.Table.lookupIndex?, parentResult] at found
      | some position =>
        simp only [SourceCoreCallableAncestryPairedCache.Table.lookupIndex?, parentResult] at found
        split at found
        · next allowed =>
          cases found
          obtain ⟨state, stored, ancestry⟩ := ih parentResult
          exact ⟨state, stored, .lambda ancestry (sound.lambda stored allowed)⟩
        · cases found
  | view id target parent => cases found
  | appliedView id target caller lexical callerIH lexicalIH =>
    cases callerResult : table.lookupIndex? caller with
    | none => simp [SourceCoreCallableAncestryPairedCache.Table.lookupIndex?, callerResult] at found
    | some callerIndex =>
      cases callerIndex with
      | none => simp [SourceCoreCallableAncestryPairedCache.Table.lookupIndex?, callerResult] at found
      | some callerPosition =>
        cases lexicalResult : table.lookupIndex? lexical with
        | none => simp [SourceCoreCallableAncestryPairedCache.Table.lookupIndex?, callerResult, lexicalResult] at found
        | some lexicalIndex =>
          cases lexicalIndex with
          | none => simp [SourceCoreCallableAncestryPairedCache.Table.lookupIndex?, callerResult, lexicalResult] at found
          | some lexicalPosition =>
            cases selected : table.viewAt? callerPosition lexicalPosition id target with
            | none => simp [SourceCoreCallableAncestryPairedCache.Table.lookupIndex?, callerResult, lexicalResult, selected] at found
            | some position =>
              simp only [SourceCoreCallableAncestryPairedCache.Table.lookupIndex?, callerResult, lexicalResult,
                selected, Option.map_some, Option.some.injEq] at found
              subst result
              obtain ⟨callerState, callerStored, callerAncestry⟩ := callerIH callerResult
              obtain ⟨lexicalState, lexicalStored, lexicalAncestry⟩ := lexicalIH lexicalResult
              obtain ⟨state, generated, stored⟩ := sound.view callerStored lexicalStored selected
              exact ⟨state, stored, .appliedView callerAncestry lexicalAncestry generated⟩

def Indexed (table : Table) (frame : Frame) : Option State → Prop
  | none => table.lookupIndex? frame = some none
  | some state => ∃ position, table.lookupIndex? frame = some (some position) ∧ table.stateAt? position = some state

theorem lookupIndex_complete {checked : Checked} {base : Base checked} {inputs : Inputs base} {table : Table}
    (closed : Closed inputs table) {frame : Frame} {state : Option State}
    (authenticated : Authenticates inputs frame state) : Indexed table frame state := by
  induction authenticated with
  | empty => rfl
  | named generated =>
    obtain ⟨position, selected, stored⟩ := closed.named generated
    exact ⟨position, by simp [SourceCoreCallableAncestryPairedCache.Table.lookupIndex?, selected], stored⟩
  | lambda ancestry generated ih =>
    obtain ⟨position, parent, stored⟩ := ih
    have allowed := closed.lambda stored generated
    exact ⟨position, by simp [SourceCoreCallableAncestryPairedCache.Table.lookupIndex?, parent, allowed], stored⟩
  | appliedView callerAncestry lexicalAncestry generated callerIH lexicalIH =>
    obtain ⟨callerIndex, callerFound, callerStored⟩ := callerIH
    obtain ⟨lexicalIndex, lexicalFound, lexicalStored⟩ := lexicalIH
    obtain ⟨position, selected, stored⟩ := closed.view callerStored lexicalStored generated
    exact ⟨position, by simp [SourceCoreCallableAncestryPairedCache.Table.lookupIndex?, callerFound, lexicalFound, selected], stored⟩

theorem lookup_complete {checked : Checked} {base : Base checked} {inputs : Inputs base} {table : Table}
    (closed : Closed inputs table) {frame : Frame} {state : Option State}
    (authenticated : Authenticates inputs frame state) : table.lookup? frame = some state := by
  have indexed := lookupIndex_complete closed authenticated
  cases state with
  | none =>
    change table.lookupIndex? frame = some none at indexed
    simp [SourceCoreCallableAncestryPairedCache.Table.lookup?, indexed]
  | some state =>
    obtain ⟨position, selected, stored⟩ := indexed
    simp [SourceCoreCallableAncestryPairedCache.Table.lookup?, selected, stored]

theorem lookup_sound {checked : Checked} {base : Base checked} {inputs : Inputs base} {table : Table}
    (sound : Sound inputs table) {frame : Frame} {state : Option State}
    (found : table.lookup? frame = some state) : Authenticates inputs frame state := by
  cases indexed : table.lookupIndex? frame with
  | none => simp [SourceCoreCallableAncestryPairedCache.Table.lookup?, indexed] at found
  | some result =>
    have meaning := lookupIndex_sound sound frame indexed
    cases result with
    | none =>
      simp only [SourceCoreCallableAncestryPairedCache.Table.lookup?, indexed, Option.some.injEq] at found
      subst state
      exact meaning
    | some position =>
      obtain ⟨selected, stored, ancestry⟩ := meaning
      simp only [SourceCoreCallableAncestryPairedCache.Table.lookup?, indexed, stored, Option.map_some, Option.some.injEq] at found
      subst state
      exact ancestry

theorem lookup_iff {checked : Checked} {base : Base checked} {inputs : Inputs base} {table : Table}
    (sound : Sound inputs table) (closed : Closed inputs table) {frame : Frame} {state : Option State} :
    table.lookup? frame = some state ↔ Authenticates inputs frame state :=
  ⟨lookup_sound sound, lookup_complete closed⟩

end Solcore.SourceSemantics.CoreLowering.CallableAncestryPairedLookup
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableAncestryPairedValidation
/-! Actual finite-row validation supplies paired-table soundness and closure.
All factories in this module operate on static metadata during preparation.
No source/Core execution is an assumption or a result of authentication. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableAncestryPairedValidation
open Frontend SourceInference TypeSystem CallableAncestryPairedLookup
abbrev State := SourceCoreCallableAncestryReadRecipes.State

theorem view_receipts {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {caller lexical result : State} {id target : Core.Word}
    (accepted : SourceCoreCallableAncestryPairedPreparation.view? inputs caller lexical id target = some result) :
    ∃ (read : SourceCoreCallableAncestryReadRecipes.Read inputs caller id target)
      (applied : SourceCoreCallableAncestryReadRecipes.Applied read lexical),
      SourceCoreCallableAncestryReadRecipes.prepareRead inputs caller id target = .ok read ∧
      SourceCoreCallableAncestryReadRecipes.applyRead read lexical = .ok applied ∧ result = read.after lexical := by
  cases readResult : SourceCoreCallableAncestryReadRecipes.prepareRead inputs caller id target with
  | error error => simp [SourceCoreCallableAncestryPairedPreparation.view?, readResult, Except.toOption] at accepted
  | ok read =>
    cases appliedResult : SourceCoreCallableAncestryReadRecipes.applyRead read lexical with
    | error error => simp [SourceCoreCallableAncestryPairedPreparation.view?, readResult, appliedResult, Except.toOption] at accepted
    | ok applied =>
      exact ⟨read, applied, rfl, appliedResult, by
        simpa [SourceCoreCallableAncestryPairedPreparation.view?, readResult, appliedResult, Except.toOption] using accepted.symm⟩

private theorem named_entry {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {state : State} {id : Core.Word}
    (accepted : SourceCoreCallableAncestryPairedPreparation.named? inputs id = some state) :
    ∃ entry ∈ inputs.callable.table.entries, entry.id = id := by
  cases selected : inputs.callable.table.entryAt? id with
  | none => simp [SourceCoreCallableAncestryPairedPreparation.named?, SourceCoreCallableAncestryPreparation.named?, selected] at accepted
  | some entry => exact ⟨entry, List.mem_of_find?_eq_some selected, by simpa using List.find?_some selected⟩

private theorem lambda_template {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {state : State} {id : Core.Word}
    (accepted : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed inputs state id = true) :
    ∃ template ∈ inputs.templates.lambdas, template.descriptor = id := by
  cases selected : inputs.templates.lambdaAt? id with
  | none => simp [SourceCoreCallableAncestryPairedPreparation.lambdaAllowed, selected] at accepted
  | some template => exact ⟨template, List.mem_of_find?_eq_some selected, by simpa using List.find?_some selected⟩

private theorem find_unique_key {α β : Type} [DecidableEq β] (items : List α) (key : α → β)
    (unique : (items.map key).Nodup) {item : α} (member : item ∈ items) :
    items.find? (fun candidate => decide (key candidate = key item)) = some item := by
  induction items with
  | nil => cases member
  | cons head tail ih =>
    simp only [List.map_cons, List.nodup_cons] at unique
    rcases List.mem_cons.mp member with same | member
    · subst item; simp
    · have different : key head ≠ key item := by
        intro same
        exact unique.1 (List.mem_map.mpr ⟨item, member, same.symm⟩)
      simpa [List.find?_cons, different] using ih unique.2 member

theorem read_target {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {caller : State} {id target : Core.Word} (read : SourceCoreCallableAncestryReadRecipes.Read inputs caller id target) :
    inputs.callable.table.idAt? (.lambda read.entry.view.owner read.entry.view.principal.initializer read.entry.view.cumulative) = some target := by
  have member := List.mem_of_find?_eq_some read.descriptorSelected
  have identifier : read.descriptor.id = target := by simpa using List.find?_some read.descriptorSelected
  unfold SourceCoreStageCodebook.Table.idAt?
  rw [← read.viewOrigin, find_unique_key _ _ inputs.callable.table.originsUnique member]
  simp [identifier]

theorem stage_entry_self (table : SourceCoreStageCodebook.Table) {entry : SourceCoreStageCodebook.Entry}
    (member : entry ∈ table.entries) : table.entryAt? entry.id = some entry :=
  find_unique_key table.entries (·.id) table.idsUnique member

private theorem namedEdge {table : Table} {id : Core.Word} {position : Nat}
    (found : table.namedAt? id = some position) :
    ∃ edge ∈ table.named, edge.origin = id ∧ edge.destination = position := by
  unfold SourceCoreCallableAncestryPairedCache.Table.namedAt? at found
  cases selected : table.named.find? (fun edge => decide (edge.origin = id)) with
  | none => rw [selected] at found; cases found
  | some edge =>
    exact ⟨edge, List.mem_of_find?_eq_some selected, by simpa using List.find?_some selected,
      by simpa only [selected, Option.map_some, Option.some.injEq] using found⟩

private theorem lambdaEdge {table : Table} {position : Nat} {id : Core.Word}
    (allowed : table.lambdaAllowed position id = true) :
    ∃ edge ∈ table.lambdas, edge.state = position ∧ edge.origin = id := by
  obtain ⟨edge, member, selected⟩ := List.any_eq_true.mp allowed
  exact ⟨edge, member, by simpa using selected⟩

private theorem viewEdge {table : Table} {caller lexical position : Nat} {id target : Core.Word}
    (found : table.viewAt? caller lexical id target = some position) :
    ∃ edge ∈ table.views, edge.caller = caller ∧ edge.lexical = lexical ∧ edge.view = id ∧
      edge.target = target ∧ edge.destination = position := by
  unfold SourceCoreCallableAncestryPairedCache.Table.viewAt? at found
  cases selected : table.views.find? (fun edge => decide
      (edge.caller = caller ∧ edge.lexical = lexical ∧ edge.view = id ∧ edge.target = target)) with
  | none => rw [selected] at found; cases found
  | some edge =>
    have shape : edge.caller = caller ∧ edge.lexical = lexical ∧ edge.view = id ∧ edge.target = target := by
      simpa using List.find?_some selected
    exact ⟨edge, List.mem_of_find?_eq_some selected, shape.1, shape.2.1, shape.2.2.1, shape.2.2.2,
      by simpa only [selected, Option.map_some, Option.some.injEq] using found⟩

theorem valid_sound {checked : Checked} {base : Base checked} (inputs : Inputs base) {table : Table}
    (validated : SourceCoreCallableAncestryPairedPreparation.valid inputs table = true) : Sound inputs table := by
  simp only [SourceCoreCallableAncestryPairedPreparation.valid, Bool.and_eq_true] at validated
  obtain ⟨⟨⟨⟨namedRows, lambdaRows⟩, viewRows⟩, _⟩, _⟩ := validated
  constructor
  · intro id position found
    obtain ⟨edge, member, origin, destination⟩ := namedEdge found
    have row := List.all_eq_true.mp namedRows edge member
    rw [origin, destination] at row
    cases generated : SourceCoreCallableAncestryPairedPreparation.named? inputs id with
    | none => simp [generated] at row
    | some state => exact ⟨state, rfl, by simpa only [generated, decide_eq_true_eq] using row⟩
  · intro position state id stored allowed
    obtain ⟨edge, member, index, origin⟩ := lambdaEdge allowed
    have row := List.all_eq_true.mp lambdaRows edge member
    simpa only [index, origin, stored] using row
  · intro callerIndex lexicalIndex caller lexical id target position callerStored lexicalStored found
    obtain ⟨edge, member, callerEq, lexicalEq, viewId, targetId, destination⟩ := viewEdge found
    have row := List.all_eq_true.mp viewRows edge member
    simp only [callerEq, lexicalEq, viewId, targetId, destination, callerStored, lexicalStored] at row
    cases generated : SourceCoreCallableAncestryPairedPreparation.view? inputs caller lexical id target with
    | none => simp [generated] at row
    | some state => exact ⟨state, rfl, by simpa only [generated, decide_eq_true_eq] using row⟩

theorem valid_closed {checked : Checked} {base : Base checked} (inputs : Inputs base) {table : Table}
    (validated : SourceCoreCallableAncestryPairedPreparation.valid inputs table = true) : Closed inputs table := by
  simp only [SourceCoreCallableAncestryPairedPreparation.valid, Bool.and_eq_true] at validated
  obtain ⟨⟨_, namedRows⟩, transitions⟩ := validated
  constructor
  · intro id state generated
    obtain ⟨entry, member, identifier⟩ := named_entry generated
    have row := List.all_eq_true.mp namedRows entry member
    simp only [identifier, generated] at row
    cases selected : table.namedAt? id with
    | none => simp [selected] at row
    | some position => exact ⟨position, rfl, by simpa only [selected, decide_eq_true_eq] using row⟩
  · intro position state id stored generated
    have member : (state, position) ∈ table.states.zipIdx := List.mk_mem_zipIdx_iff_getElem?.mpr stored
    have both := List.all_eq_true.mp transitions (state, position) member
    simp only [Bool.and_eq_true] at both
    obtain ⟨template, templateMember, identifier⟩ := lambda_template generated
    have row := List.all_eq_true.mp both.1 template templateMember
    simpa only [identifier, generated, Bool.not_true, Bool.false_or] using row
  · intro callerIndex lexicalIndex caller lexical id target result callerStored lexicalStored generated
    have callerMember : (caller, callerIndex) ∈ table.states.zipIdx := List.mk_mem_zipIdx_iff_getElem?.mpr callerStored
    have lexicalMember : (lexical, lexicalIndex) ∈ table.states.zipIdx := List.mk_mem_zipIdx_iff_getElem?.mpr lexicalStored
    have both := List.all_eq_true.mp transitions (caller, callerIndex) callerMember
    simp only [Bool.and_eq_true] at both
    have rows := List.all_eq_true.mp both.2 (lexical, lexicalIndex) lexicalMember
    obtain ⟨read, _, _, _, _⟩ := view_receipts generated
    have viewMember : read.entry ∈ inputs.views.entries := List.mem_of_find?_eq_some read.selected
    have identifier : read.entry.id = id := by simpa using List.find?_some read.selected
    have row := List.all_eq_true.mp rows read.entry viewMember
    simp only [read_target read, identifier, generated] at row
    cases selected : table.viewAt? callerIndex lexicalIndex id target with
    | none => simp [selected] at row
    | some position => exact ⟨position, rfl, by simpa only [selected, decide_eq_true_eq] using row⟩

/-- Successful actual preparation certifies every finite pure-factory frame,
without a supplied list of frames or a bound on ancestry depth. Termination
and native-produced-frame coverage are independent obligations. -/
theorem prepared_lookup_iff {checked : Checked} {base : Base checked}
    (prepared : SourceCoreCallableAncestryPairedPreparation.Prepared base) {frame : Frame} {state : Option State} :
    prepared.table.lookup? frame = some state ↔ Authenticates prepared.inputs frame state :=
  lookup_iff (valid_sound prepared.inputs prepared.validated) (valid_closed prepared.inputs prepared.validated)

/-- Any collection of the actual named seeds covering all named roots also
bounds metadata at arbitrary paired-frame depth. This lemma is independent
of how the finite worklist orders or interns those seeds. -/
theorem authenticated_valid {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {roots : List State} (seeded : CallableAncestryPairedProfiles.Seeded base roots)
    (covered : ∀ {id state}, SourceCoreCallableAncestryPairedPreparation.named? inputs id = some state → state ∈ roots)
    {frame : Frame} {state : State} (authenticated : Authenticates inputs frame (some state)) :
    CallableAncestryPairedProfiles.Valid inputs roots state := by
  generalize resultEq : some state = result at authenticated
  induction authenticated generalizing state with
  | empty => cases resultEq
  | named selected =>
    cases resultEq
    exact CallableAncestryPairedProfiles.seeded_valid inputs seeded (covered selected)
  | lambda ancestry allowed ih => exact ih resultEq
  | appliedView callerAncestry lexicalAncestry selected callerIH lexicalIH =>
    cases resultEq
    obtain ⟨read, applied, _, _, same⟩ := view_receipts selected
    rw [same]
    exact CallableAncestryPairedProfiles.read_after_valid (CallableAncestryPairedProfiles.seeded_coherent seeded)
      read applied (callerIH rfl) (lexicalIH rfl)

end Solcore.SourceSemantics.CoreLowering.CallableAncestryPairedValidation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableAncestryPairedWorklist
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableAncestryPairedEdges
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableAncestryPairedExpansion
/-! Exact coverage of the actual paired worklist expansion. Both orientations
of each old-state pair are handled; new states remain queued for later turns. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableAncestryPairedExpansion
open Frontend SourceInference TypeSystem CallableAncestryPairedLookup CallableAncestryPairedEdges
abbrev State := SourceCoreCallableAncestryReadRecipes.State

 theorem bind_ok {α β ε : Type} {computation : Except ε α} {next : α → Except ε β} {result : β}
    (accepted : computation >>= next = .ok result) : ∃ value, computation = .ok value ∧ next value = .ok result := by
  cases computation with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

/-- A successful loop whose steps always yield accumulates one monotone
property for every traversed item, retaining exact table growth. -/
theorem forIn_coverage {α ε : Type} {items : List α} {initial final : Table}
    {step : α → Table → Except ε (ForInStep Table)}
    {invariant : Table → Prop} {done : α → Table → Prop}
    (accepted : forIn items initial step = .ok final) (start : invariant initial)
    (monotone : ∀ item before after, Extends before after → done item before → done item after)
    (next : ∀ item ∈ items, ∀ table outcome, invariant table →
      step item table = .ok outcome →
      ∃ updated, outcome = .yield updated ∧ Extends table updated ∧ invariant updated ∧ done item updated) :
    Extends initial final ∧ invariant final ∧ ∀ item ∈ items, done item final := by
  induction items generalizing initial with
  | nil =>
    simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] at accepted
    subst final
    exact ⟨.refl _, start, by simp⟩
  | cons item rest ih =>
    rw [List.forIn_cons] at accepted
    obtain ⟨outcome, executed, finished⟩ := bind_ok accepted
    obtain ⟨updated, rfl, firstGrowth, maintained, doneItem⟩ := next item (by simp) initial outcome start executed
    obtain ⟨restGrowth, finalValid, restDone⟩ := ih finished maintained (fun item member => next item (by simp [member]))
    refine ⟨firstGrowth.trans restGrowth, finalValid, ?_⟩
    intro value member
    rcases List.mem_cons.mp member with rfl | member
    · exact monotone value _ _ restGrowth doneItem
    · exact restDone value member

private theorem lambda_template {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {state : State} {id : Core.Word}
    (accepted : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed inputs state id = true) :
    ∃ template ∈ inputs.templates.lambdas, template.descriptor = id := by
  cases selected : inputs.templates.lambdaAt? id with
  | none => simp [SourceCoreCallableAncestryPairedPreparation.lambdaAllowed, selected] at accepted
  | some template => exact ⟨template, List.mem_of_find?_eq_some selected, by simpa using List.find?_some selected⟩

private theorem view_entry {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {caller lexical result : State} {id target : Core.Word}
    (accepted : SourceCoreCallableAncestryPairedPreparation.view? inputs caller lexical id target = some result) :
    ∃ entry ∈ inputs.views.entries, entry.id = id ∧
      inputs.callable.table.idAt? (.lambda entry.view.owner entry.view.principal.initializer entry.view.cumulative) = some target := by
  obtain ⟨read, _, _, _, _⟩ := CallableAncestryPairedValidation.view_receipts accepted
  exact ⟨read.entry, List.mem_of_find?_eq_some read.selected,
    by simpa using List.find?_some read.selected, CallableAncestryPairedValidation.read_target read⟩

/-- Actual expansion has covered every lambda of the selected state, and both
view orientations between that state and every state present before expansion. -/
theorem expand_spec {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {position : Nat} {state : State} {initial final : Table}
    (accepted : SourceCoreCallableAncestryPairedPreparation.expand inputs position state initial = .ok final)
    (sound : RowsSound inputs initial) (stored : initial.stateAt? position = some state) :
    Extends initial final ∧ RowsSound inputs final ∧
      (∀ id, SourceCoreCallableAncestryPairedPreparation.lambdaAllowed inputs state id = true → HasLambda final position id) ∧
      (∀ otherIndex other, initial.stateAt? otherIndex = some other → ∀ id target result,
        (SourceCoreCallableAncestryPairedPreparation.view? inputs state other id target = some result →
          HasView final position otherIndex id target) ∧
        (SourceCoreCallableAncestryPairedPreparation.view? inputs other state id target = some result →
          HasView final otherIndex position id target)) := by
  let lambdaStep : SourceCoreLambdaTemplates.Lambda → Table →
      Except SourceCoreCallableAncestryPairedPreparation.Error (ForInStep Table) := fun template table =>
    if SourceCoreCallableAncestryPairedPreparation.lambdaAllowed inputs state template.descriptor then
      let edge : SourceCoreCallableAncestryPairedCache.LambdaEdge := ⟨position, template.descriptor⟩
      if !table.lambdas.contains edge then .ok (.yield {table with lambdas := table.lambdas ++ [edge]})
      else .ok (.yield table)
    else .ok (.yield table)
  let innerStep := fun (entry : SourceCoreCallableViews.Entry base.sourceProgram base.plan) (target : Core.Word)
      (row : State × Nat) (table : Table) => do
    let after ← SourceCoreCallableAncestryPairedPreparation.addView inputs table position row.2 state row.1 entry.id target
    let final ← SourceCoreCallableAncestryPairedPreparation.addView inputs after row.2 position row.1 state entry.id target
    pure (ForInStep.yield final)
  let outerStep := fun (entry : SourceCoreCallableViews.Entry base.sourceProgram base.plan) (table : Table) =>
    match inputs.callable.table.idAt? (.lambda entry.view.owner entry.view.principal.initializer entry.view.cumulative) with
    | none => Except.ok (ForInStep.yield table)
    | some target => do
      let after ← forIn initial.states.zipIdx table (innerStep entry target)
      pure (ForInStep.yield after)
  change (forIn inputs.templates.lambdas initial lambdaStep >>= fun middle =>
    forIn inputs.views.entries middle outerStep >>= fun result => Except.ok result) = .ok final at accepted
  obtain ⟨middle, firstEval, rest⟩ := bind_ok accepted
  obtain ⟨last, secondEval, finished⟩ := bind_ok rest
  cases finished
  have firstSpec : Extends initial middle ∧ (Extends initial middle ∧ RowsSound inputs middle) ∧
      ∀ template ∈ inputs.templates.lambdas,
        SourceCoreCallableAncestryPairedPreparation.lambdaAllowed inputs state template.descriptor = true →
          HasLambda middle position template.descriptor := by
    apply forIn_coverage firstEval (invariant := fun table => Extends initial table ∧ RowsSound inputs table)
      (done := fun template table => SourceCoreCallableAncestryPairedPreparation.lambdaAllowed inputs state template.descriptor = true →
        HasLambda table position template.descriptor) ⟨.refl _, sound⟩
    · intro template before after growth covered allowed
      exact (covered allowed).extend growth
    · intro template _ table outcome previous ran
      dsimp only [lambdaStep] at ran
      split at ran
      · next allowed =>
        split at ran
        · cases ran
          let edge : SourceCoreCallableAncestryPairedCache.LambdaEdge := ⟨position, template.descriptor⟩
          have growth : Extends table {table with lambdas := table.lambdas ++ [edge]} :=
            ⟨⟨[], by simp⟩, fun _ h => h, fun _ h => List.mem_append_left _ h, fun _ h => h⟩
          refine ⟨_, rfl, growth, ⟨previous.1.trans growth, ?_⟩, ?_⟩
          · refine ⟨previous.2.named, ?_, previous.2.view⟩
            intro row member
            rcases List.mem_append.mp member with old | new
            · exact previous.2.lambda row old
            · have same : row = edge := by simpa using new
              subst row
              exact ⟨state, previous.1.lookup stored, allowed⟩
          · intro _; exact ⟨edge, by simp [edge], rfl, rfl⟩
        · next existsEdge =>
          cases ran
          refine ⟨table, rfl, .refl _, previous, ?_⟩
          intro _
          have member : (⟨position, template.descriptor⟩ : SourceCoreCallableAncestryPairedCache.LambdaEdge) ∈ table.lambdas := by
            simpa using existsEdge
          exact ⟨_, member, rfl, rfl⟩
      · next denied =>
        cases ran
        exact ⟨table, rfl, .refl _, previous, by intro impossible; exact False.elim (denied impossible)⟩
  let doneEntry := fun (entry : SourceCoreCallableViews.Entry base.sourceProgram base.plan) (table : Table) =>
    ∀ target, inputs.callable.table.idAt? (.lambda entry.view.owner entry.view.principal.initializer entry.view.cumulative) = some target →
      ∀ otherIndex other, initial.stateAt? otherIndex = some other → ∀ result,
        (SourceCoreCallableAncestryPairedPreparation.view? inputs state other entry.id target = some result →
          HasView table position otherIndex entry.id target) ∧
        (SourceCoreCallableAncestryPairedPreparation.view? inputs other state entry.id target = some result →
          HasView table otherIndex position entry.id target)
  have secondSpec : Extends middle final ∧ (Extends initial final ∧ RowsSound inputs final) ∧
      ∀ entry ∈ inputs.views.entries, doneEntry entry final := by
    apply forIn_coverage secondEval (invariant := fun table => Extends initial table ∧ RowsSound inputs table)
      (done := doneEntry) firstSpec.2.1
    · intro entry before after growth covered target selected otherIndex other otherStored result
      have both := covered target selected otherIndex other otherStored result
      exact ⟨fun h => (both.1 h).extend growth, fun h => (both.2 h).extend growth⟩
    · intro entry _ table outcome previous ran
      dsimp only [outerStep] at ran
      split at ran
      · next absent =>
        cases ran
        refine ⟨table, rfl, .refl _, previous, ?_⟩
        intro target selected
        rw [absent] at selected
        cases selected
      · next target selected =>
        obtain ⟨after, innerEval, finished⟩ := bind_ok ran
        cases finished
        have innerSpec : Extends table after ∧ (Extends initial after ∧ RowsSound inputs after) ∧
            ∀ row ∈ initial.states.zipIdx, ∀ result,
              (SourceCoreCallableAncestryPairedPreparation.view? inputs state row.1 entry.id target = some result →
                HasView after position row.2 entry.id target) ∧
              (SourceCoreCallableAncestryPairedPreparation.view? inputs row.1 state entry.id target = some result →
                HasView after row.2 position entry.id target) := by
          apply forIn_coverage innerEval (invariant := fun table => Extends initial table ∧ RowsSound inputs table)
            (done := fun row table => ∀ result,
              (SourceCoreCallableAncestryPairedPreparation.view? inputs state row.1 entry.id target = some result →
                HasView table position row.2 entry.id target) ∧
              (SourceCoreCallableAncestryPairedPreparation.view? inputs row.1 state entry.id target = some result →
                HasView table row.2 position entry.id target)) previous
          · intro row before after growth covered result
            exact ⟨fun h => ((covered result).1 h).extend growth, fun h => ((covered result).2 h).extend growth⟩
          · intro row member table outcome maintained ran
            dsimp only [innerStep] at ran
            obtain ⟨next, firstRun, secondRest⟩ := bind_ok ran
            obtain ⟨final, secondRun, finished⟩ := bind_ok secondRest
            cases finished
            have otherStored := List.mk_mem_zipIdx_iff_getElem?.mp member
            obtain ⟨growth, nextSound, leftDone⟩ := addView_spec firstRun maintained.2
              (maintained.1.lookup stored) (maintained.1.lookup otherStored)
            obtain ⟨lastGrowth, finalSound, rightDone⟩ := addView_spec secondRun nextSound
              (growth.lookup (maintained.1.lookup otherStored)) (growth.lookup (maintained.1.lookup stored))
            exact ⟨final, rfl, growth.trans lastGrowth, ⟨maintained.1.trans (growth.trans lastGrowth), finalSound⟩,
              fun result => ⟨fun h => (leftDone result h).extend lastGrowth, rightDone result⟩⟩
        refine ⟨after, rfl, innerSpec.1, innerSpec.2.1, ?_⟩
        intro actualTarget actualSelected otherIndex other otherStored result
        have same := Option.some.inj (actualSelected.symm.trans selected)
        subst actualTarget
        exact innerSpec.2.2 (other, otherIndex) (List.mk_mem_zipIdx_iff_getElem?.mpr otherStored) result
  refine ⟨firstSpec.1.trans secondSpec.1, secondSpec.2.1.2, ?_, ?_⟩
  · intro id allowed
    obtain ⟨template, member, same⟩ := lambda_template allowed
    exact (same ▸ firstSpec.2.2 template member (same ▸ allowed)).extend secondSpec.1
  · intro otherIndex other otherStored id target result
    constructor <;> intro generated
    · obtain ⟨entry, member, same, selected⟩ := view_entry generated
      exact same ▸ (secondSpec.2.2 entry member target selected otherIndex other otherStored result).1 (same ▸ generated)
    · obtain ⟨entry, member, same, selected⟩ := view_entry generated
      exact same ▸ (secondSpec.2.2 entry member target selected otherIndex other otherStored result).2 (same ▸ generated)

end Solcore.SourceSemantics.CoreLowering.CallableAncestryPairedExpansion
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableAncestryPairedRecipes
/-! Successful finite edge validation is enough to prepare every paired read
recipe. The actual read and application factories, their exact caller evidence,
and their lexical metadata are retained. Runtime selection only searches the
prepared list; these proofs do not authenticate native execution history. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableAncestryPairedRecipes
open Frontend SourceInference TypeSystem CallableAncestryPairedLookup
abbrev State := SourceCoreCallableAncestryReadRecipes.State

theorem prepareRecipe_total {checked : Checked} {base : Base checked} {inputs : Inputs base} {table : Table}
    (validated : SourceCoreCallableAncestryPairedPreparation.valid inputs table = true)
    (edge : SourceCoreCallableAncestryPairedCache.ViewEdge) (owned : edge ∈ table.views) :
    ∃ recipe, SourceCoreCallableAncestryPairedPreparation.prepareRecipe inputs table edge owned = .ok recipe := by
  simp only [SourceCoreCallableAncestryPairedPreparation.valid, Bool.and_eq_true] at validated
  obtain ⟨⟨⟨_, views⟩, _⟩, _⟩ := validated
  have row := List.all_eq_true.mp views edge owned
  cases callerFound : table.stateAt? edge.caller with
  | none => simp [callerFound] at row
  | some caller =>
    cases lexicalFound : table.stateAt? edge.lexical with
    | none => simp [callerFound, lexicalFound] at row
    | some lexical =>
      simp only [callerFound, lexicalFound] at row
      cases generated : SourceCoreCallableAncestryPairedPreparation.view? inputs caller lexical edge.view edge.target with
      | none => simp [generated] at row
      | some next =>
        have stored : table.stateAt? edge.destination = some next := by
          simpa only [generated, decide_eq_true_eq] using row
        obtain ⟨read, applied, readPrepared, appliedPrepared, same⟩ := CallableAncestryPairedValidation.view_receipts generated
        rw [same] at stored
        unfold SourceCoreCallableAncestryPairedPreparation.prepareRecipe
        split
        · next impossible => rw [callerFound] at impossible; cases impossible
        · next actual found =>
          have equal := Option.some.inj (found.symm.trans callerFound)
          subst actual
          split
          · next impossible => rw [lexicalFound] at impossible; cases impossible
          · next actual found =>
            have equal := Option.some.inj (found.symm.trans lexicalFound)
            subst actual
            split
            · next error impossible => rw [readPrepared] at impossible; cases impossible
            · next actual found =>
              have equal := Except.ok.inj (found.symm.trans readPrepared)
              subst actual
              split
              · next error impossible => rw [appliedPrepared] at impossible; cases impossible
              · next actual found =>
                have equal := Except.ok.inj (found.symm.trans appliedPrepared)
                subst actual
                rw [dif_pos stored]
                exact ⟨_, rfl⟩

private theorem mapM_total {α β ε : Type} (items : List α) (f : α → Except ε β)
    (each : ∀ item ∈ items, ∃ result, f item = .ok result) : ∃ result, items.mapM f = .ok result := by
  induction items with
  | nil => exact ⟨[], rfl⟩
  | cons head tail ih =>
    obtain ⟨value, first⟩ := each head (by simp)
    obtain ⟨values, rest⟩ := ih (fun item member => each item (by simp [member]))
    exact ⟨value :: values, by simp [List.mapM_cons, first, rest, bind, Except.bind]⟩

theorem recipes_total {checked : Checked} {base : Base checked} {inputs : Inputs base} {table : Table}
    (validated : SourceCoreCallableAncestryPairedPreparation.valid inputs table = true) :
    ∃ recipes, table.views.attach.mapM (fun edge =>
      SourceCoreCallableAncestryPairedPreparation.prepareRecipe inputs table edge.val edge.property) = .ok recipes := by
  apply mapM_total
  intro edge _
  exact prepareRecipe_total validated edge.val edge.property

theorem prepareRecipe_edge {checked : Checked} {base : Base checked} {inputs : Inputs base} {table : Table}
    {edge : SourceCoreCallableAncestryPairedCache.ViewEdge} {owned : edge ∈ table.views}
    {recipe : SourceCoreCallableAncestryPairedPreparation.Recipe inputs table}
    (accepted : SourceCoreCallableAncestryPairedPreparation.prepareRecipe inputs table edge owned = .ok recipe) :
    recipe.edge = edge := by
  unfold SourceCoreCallableAncestryPairedPreparation.prepareRecipe at accepted
  split at accepted <;> try cases accepted
  split at accepted <;> try cases accepted
  split at accepted <;> try cases accepted
  split at accepted <;> try cases accepted
  split at accepted <;> cases accepted
  rfl

private theorem mapM_member {α β ε : Type} {items : List α} {results : List β} {f : α → Except ε β}
    (accepted : items.mapM f = .ok results) {item : α} (member : item ∈ items) :
    ∃ result ∈ results, f item = .ok result := by
  induction items generalizing results with
  | nil => cases member
  | cons head tail ih =>
    simp only [List.mapM_cons] at accepted
    cases first : f head with
    | error error => simp [first, bind, Except.bind] at accepted
    | ok value =>
      cases rest : tail.mapM f with
      | error error => simp [first, rest, bind, Except.bind] at accepted
      | ok values =>
        have same : value :: values = results := by simpa [first, rest, bind, Except.bind] using accepted
        subst results
        rcases List.mem_cons.mp member with same | member
        · subst item; exact ⟨value, by simp, first⟩
        · obtain ⟨result, included, found⟩ := ih rest member
          exact ⟨result, by simp [included], found⟩

theorem prepared_recipe_member {checked : Checked} {base : Base checked}
    (prepared : SourceCoreCallableAncestryPairedPreparation.Prepared base)
    {edge : SourceCoreCallableAncestryPairedCache.ViewEdge} (member : edge ∈ prepared.table.views) :
    ∃ recipe ∈ prepared.recipes, recipe.edge = edge := by
  obtain ⟨recipe, included, accepted⟩ := mapM_member prepared.recipesPrepared
    (List.mem_attach prepared.table.views ⟨edge, member⟩)
  exact ⟨recipe, included, prepareRecipe_edge accepted⟩

/-- Every completed table edge has a cached recipe selectable without a
runtime witness factory, source traversal, or dictionary resolution. -/
theorem recipeAt_complete {checked : Checked} {base : Base checked}
    (prepared : SourceCoreCallableAncestryPairedPreparation.Prepared base)
    {caller lexical position : Nat} {id target : Core.Word}
    (found : prepared.table.viewAt? caller lexical id target = some position) :
    ∃ recipe, prepared.recipeAt? caller lexical id target = some recipe := by
  unfold SourceCoreCallableAncestryPairedCache.Table.viewAt? at found
  cases selected : prepared.table.views.find? (fun edge => decide
      (edge.caller = caller ∧ edge.lexical = lexical ∧ edge.view = id ∧ edge.target = target)) with
  | none => rw [selected] at found; cases found
  | some edge =>
    have shape : edge.caller = caller ∧ edge.lexical = lexical ∧ edge.view = id ∧ edge.target = target := by
      simpa using List.find?_some selected
    obtain ⟨recipe, included, same⟩ := prepared_recipe_member prepared (List.mem_of_find?_eq_some selected)
    cases cached : prepared.recipeAt? caller lexical id target with
    | some result => exact ⟨result, rfl⟩
    | none =>
      have excluded := List.find?_eq_none.mp cached recipe included
      exact False.elim (excluded (by simpa only [same, decide_eq_true_eq] using shape))

end Solcore.SourceSemantics.CoreLowering.CallableAncestryPairedRecipes
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableAncestryPairedProgress
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
end
