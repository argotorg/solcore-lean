import Lean
import Solcore.Frontend.SourceCoreCallableIndexedAncestry
import Solcore.SourceSemantics.CoreLowering.CallableSpecializationEquality

/-! The static view's candidate is selected by the actual native catalog
filter, retaining the complete binding and cumulative substitution key. -/
set_option autoImplicit false
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.CallablePreparedViewSelection
open Frontend SourceInference TypeSystem SourceCoreCallableViews

open Lean Meta Elab Term in
private def actualDefinition (original : Name) : TermElabM Lean.Expr := do
  let mut found : Option Name := none
  for (name, _) in (← getEnv).constants.toList do
    if privateToUserName? name == some original then
      if found.isSome then throwError "ambiguous actual view definition: {original}"
      found := some name
  let some name := found | throwError "missing actual view definition: {original}"
  mkConstWithFreshMVarLevels name

elab "actual_view_select" : term => actualDefinition `Solcore.Frontend.SourceCoreCallableViews.selectInstance
elab "actual_view_insert" : term => actualDefinition `Solcore.Frontend.SourceCoreCallableViews.insert
elab "actual_view_collect" : term => actualDefinition `Solcore.Frontend.SourceCoreCallableViews.collect

open Lean Meta Elab Tactic in
private def unfoldActual (original : Name) (hypothesis : Name) : TacticM Unit := do
  let mut found : Option Name := none
  for (name, _) in (← getEnv).constants.toList do
    if privateToUserName? name == some original then
      if found.isSome then throwError "ambiguous actual view definition: {original}"
      found := some name
  let some name := found | throwError "missing actual view definition: {original}"
  let goal ← getMainGoal
  let declaration ← goal.withContext <| getLocalDeclFromUserName hypothesis
  replaceMainGoal [← unfoldLocalDecl goal declaration.fvarId name]

private theorem bind_ok {α β ε : Type} {action : Except ε α}
    {next : α → Except ε β} {output : β} (accepted : action >>= next = .ok output) :
    ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem forIn_invariant {α β ε : Type} {items : List α} {initial final : β}
    {step : α → β → Except ε (ForInStep β)} {invariant : β → Prop}
    (accepted : forIn items initial step = .ok final) (start : invariant initial)
    (each : ∀ item ∈ items, ∀ state outcome, invariant state →
      step item state = .ok outcome → ∃ updated, outcome = .yield updated ∧ invariant updated) :
    invariant final := by
  induction items generalizing initial with
  | nil =>
    simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] at accepted
    exact accepted ▸ start
  | cons item rest ih =>
    rw [List.forIn_cons] at accepted
    obtain ⟨outcome, ran, accepted⟩ := bind_ok accepted
    obtain ⟨updated, rfl, preserved⟩ := each item List.mem_cons_self initial outcome start ran
    exact ih accepted preserved (fun next member => each next (List.mem_cons_of_mem item member))

structure Selection {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    (catalog : SourceCoreLocalPolymorphism.Catalog) (view : View program plan) where
  binding : SourceCoreLocalPolymorphism.Binding
  located : catalog.binding view.owner view.binding.binder.id = .ok binding
  source : binding.source = view.binding.source
  binder : binding.binder = view.binding.binder
  initializer : binding.initializer = view.binding.initializer
  candidate : SourceCoreLocalPolymorphism.Instance
  selected : view.selectedInstance = some candidate
  rows : binding.instances.filter (fun candidate => decide (candidate.origin.substitution = view.cumulative)) = [candidate]
  owner : candidate.origin.caller = view.owner
  candidateSource : candidate.origin.source = view.binding.source
  candidateBinder : candidate.origin.binder = view.binding.binder
  candidateInitializer : candidate.origin.initializer = view.binding.initializer

private theorem select_correct {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {catalog : SourceCoreLocalPolymorphism.Catalog} {view result : View program plan}
    (accepted : actual_view_select catalog view = .ok result)
    (generalized : result.wrapsPrincipal = true) : Nonempty (Selection catalog result) := by
  run_tac unfoldActual `Solcore.Frontend.SourceCoreCallableViews.selectInstance `accepted
  split at accepted
  · cases accepted
    simp_all
  · split at accepted
    · simp only [throw, throwThe, MonadExceptOf.throw, bind, Except.bind, reduceCtorEq] at accepted
    · next binding filtered =>
      try dsimp only [bind, pure, Except.pure, Except.bind] at accepted
      split at accepted
      · simp only [throw, throwThe, MonadExceptOf.throw, reduceCtorEq] at accepted
      · next metadata =>
        split at accepted
        · simp only [throw, throwThe, MonadExceptOf.throw, bind, Except.bind, reduceCtorEq] at accepted
        · next candidate rows =>
          try dsimp only [bind, pure, Except.pure, Except.bind] at accepted
          split at accepted
          · simp only [throw, throwThe, MonadExceptOf.throw, reduceCtorEq] at accepted
          · next origin =>
            cases accepted
            have fields : binding.source = view.binding.source ∧ binding.binder = view.binding.binder ∧
                binding.initializer = view.binding.initializer := by simpa [bne, beq_iff_eq, and_assoc] using metadata
            have candidateFields : candidate.origin.caller = view.owner ∧
                candidate.origin.source = view.binding.source ∧ candidate.origin.binder = view.binding.binder ∧
                candidate.origin.initializer = view.binding.initializer := by simpa [bne, beq_iff_eq, and_assoc] using origin
            refine ⟨⟨binding, ?_, fields.1, fields.2.1, fields.2.2, candidate, rfl, rows,
              candidateFields.1, candidateFields.2.1, candidateFields.2.2.1, candidateFields.2.2.2⟩⟩
            change catalog.binding view.owner view.binding.binder.id = .ok binding
            simp only [SourceCoreLocalPolymorphism.Catalog.binding, filtered]
        · simp only [throw, throwThe, MonadExceptOf.throw, bind, Except.bind, reduceCtorEq] at accepted
    · simp only [throw, throwThe, MonadExceptOf.throw, bind, Except.bind, reduceCtorEq] at accepted

private def SelectedEntries {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    (catalog : SourceCoreLocalPolymorphism.Catalog) (entries : List (Entry program plan)) : Prop :=
  ∀ entry ∈ entries, entry.view.wrapsPrincipal = true → Nonempty (Selection catalog entry.view)

private theorem insert_preserves {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {catalog : SourceCoreLocalPolymorphism.Catalog} {limits : Limits} {firstId : Nat}
    {entries result : List (Entry program plan)} {view : View program plan}
    (accepted : actual_view_insert limits firstId entries view = .ok result)
    (previous : SelectedEntries catalog entries)
    (selected : view.wrapsPrincipal = true → Nonempty (Selection catalog view)) :
    SelectedEntries catalog result := by
  run_tac unfoldActual `Solcore.Frontend.SourceCoreCallableViews.insert `accepted
  dsimp only at accepted
  split at accepted
  · cases accepted
  · split at accepted
    · cases accepted
    · try dsimp only at accepted
      split at accepted
      · cases accepted
        intro entry member generalized
        rcases List.mem_append.mp member with old | added
        · exact previous entry old generalized
        · cases List.mem_singleton.mp added
          exact selected generalized
      · cases accepted

private theorem collect_preserves {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {catalog : SourceCoreLocalPolymorphism.Catalog} {limits : Limits} {firstId : Nat}
    {bindings : List SourceCoreLocalEvidence.Binding} {parent : Option Parent} {nodes : List Node}
    {entries result : List (Entry program plan)}
    (accepted : actual_view_collect limits firstId catalog bindings parent nodes entries = .ok result)
    (previous : SelectedEntries catalog entries) : SelectedEntries catalog result := by
  run_tac unfoldActual `Solcore.Frontend.SourceCoreCallableViews.collect `accepted
  obtain ⟨after, traversed, accepted⟩ := bind_ok accepted
  cases accepted
  apply forIn_invariant traversed previous
  intro node member before outcome beforeSelected step
  try dsimp only at step
  split at step
  · split at step
    · cases step
      exact ⟨before, rfl, beforeSelected⟩
    · obtain ⟨view, _, step⟩ := bind_ok step
      split at step
      · cases step
      · obtain ⟨selected, chosen, step⟩ := bind_ok step
        obtain ⟨updated, inserted, step⟩ := bind_ok step
        cases step
        exact ⟨updated, rfl, insert_preserves inserted beforeSelected (select_correct chosen)⟩
  · cases step
    exact ⟨before, rfl, beforeSelected⟩

/-- Actual root and contextual preparation retain the same native catalog
selection, including the complete source, binder, initializer and candidate. -/
theorem prepared {checked : Checked} {input : SourceCoreCompatibleFunctions.Prepared checked}
    {limits : Limits} {firstId : Nat} {table : Table input.sourceProgram input.plan}
    (accepted : prepare input limits firstId = .ok table)
    {entry : Entry input.sourceProgram input.plan} (member : entry ∈ table.entries)
    (generalized : entry.view.wrapsPrincipal = true) : Nonempty (Selection input.locals entry.view) := by
  unfold prepare at accepted
  dsimp only at accepted
  split at accepted
  · cases accepted
  · split at accepted
    · cases accepted
    · obtain ⟨roots, rootLoop, accepted⟩ := bind_ok accepted
      have rootSelected : SelectedEntries input.locals roots := by
        apply forIn_invariant rootLoop (by simp [SelectedEntries])
        intro caller callerMember before outcome previous step
        obtain ⟨_, _, step⟩ := bind_ok step
        obtain ⟨bindings, _, step⟩ := bind_ok step
        obtain ⟨nodes, _, step⟩ := bind_ok step
        obtain ⟨updated, collected, step⟩ := bind_ok step
        cases step
        exact ⟨updated, rfl, collect_preserves collected previous⟩
      obtain ⟨entries, contextLoop, accepted⟩ := bind_ok accepted
      have allSelected : SelectedEntries input.locals entries := by
        apply forIn_invariant contextLoop rootSelected
        intro parent parentMember before outcome previous step
        obtain ⟨_, _, step⟩ := bind_ok step
        obtain ⟨_, _, step⟩ := bind_ok step
        obtain ⟨bindings, _, step⟩ := bind_ok step
        obtain ⟨updated, collected, step⟩ := bind_ok step
        cases step
        exact ⟨updated, rfl, collect_preserves collected previous⟩
      try dsimp only at accepted
      split at accepted
      · split at accepted
        · cases accepted
          exact allSelected entry member generalized
        · split at accepted <;> cases accepted
      · cases accepted

/-- A read's selected static instance is an actual singleton member of the
binding catalog, with the cumulative substitution key checked by preparation. -/
theorem Selection.candidate_member {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {catalog : SourceCoreLocalPolymorphism.Catalog} {view : View program plan}
    (selection : Selection catalog view) :
    selection.candidate ∈ selection.binding.instances ∧
      selection.candidate.origin.substitution = view.cumulative := by
  have member : selection.candidate ∈ selection.binding.instances.filter
      (fun candidate => decide (candidate.origin.substitution = view.cumulative)) := by
    rw [selection.rows]
    simp
  exact ⟨(List.mem_filter.mp member).1, of_decide_eq_true (List.mem_filter.mp member).2⟩

/-- The same actual lowered-read receipt selects an entry whose complete native
binding and instance passed preparation. -/
theorem at_receipt {checked : Checked} {base : SourceCoreCompatibleFunctions.Prepared checked}
    (ancestry : SourceCoreCallableIndexedAncestry.Prepared base)
    {owner : Key} {active : Substitution} {read : ExpressionId}
    {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : SourceCoreCallableViewLowering.Viewed ancestry.views owner active read lowered)
    (generalized : receipt.entry.view.wrapsPrincipal = true) :
    Nonempty (Selection base.locals receipt.entry.view) := by
  have member : receipt.entry ∈ ancestry.views.entries :=
    List.mem_of_find?_eq_some receipt.found
  exact prepared ancestry.graph.inputs.viewsPrepared member generalized

/-- Any actual member with the checked cumulative key is the same complete
candidate selected for this static view. -/
theorem Selection.same_candidate {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {catalog : SourceCoreLocalPolymorphism.Catalog} {view : View program plan}
    (selection : Selection catalog view) {candidate : SourceCoreLocalPolymorphism.Instance}
    (member : candidate ∈ selection.binding.instances)
    (key : candidate.origin.substitution = view.cumulative) : candidate = selection.candidate := by
  have present : candidate ∈ selection.binding.instances.filter
      (fun candidate => decide (candidate.origin.substitution = view.cumulative)) :=
    List.mem_filter.mpr ⟨member, by simpa using key⟩
  rw [selection.rows] at present
  exact List.mem_singleton.mp present

end Solcore.SourceSemantics.CoreLowering.CallablePreparedViewSelection
