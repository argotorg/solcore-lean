import Solcore.SourceSemantics.CoreLowering.CallableAncestryPairedLookup

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
