import Solcore.SourceSemantics.CoreLowering.CallableAncestryPairedValidation

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
