import Solcore.SourceSemantics.CoreLowering.CallableAncestryPairedEdges

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
