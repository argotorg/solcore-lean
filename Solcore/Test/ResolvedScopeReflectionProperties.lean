import Solcore.Resolved.Scope

/-! Fresh insertion reflects already-scoped evaluations, including references
under an existing binder with the inserted ID. Freshness alone is insufficient. -/

set_option autoImplicit false

namespace Tests.ResolvedScopeReflection

open Solcore Solcore.Resolved

private def modulePath : Workspace.ModulePath := ⟨[⟨"Reflect", by decide⟩], by decide⟩
private def owner : DeclarationId := ⟨⟨.main, modulePath⟩, 0⟩
private def oldId : LocalId := ⟨owner, 0⟩
private def environment : Environment := [(oldId, .bool false)]
private def fresh : LocalId := freshLocalId owner (LocalScope.ids environment)
private def nested : Expr :=
  .letE fresh (.bool true) (.letE oldId (.bool false) (.var fresh))

private theorem nested_scoped : WellScoped (LocalScope.ids environment) nested :=
  .letE .bool (.letE .bool (.var (by simp)))

theorem prefix_can_already_bind_the_inserted_id
    (keptValue addedValue value : Core.Value) (initialStore finalStore : Core.Store) :
    Evaluates ([(fresh, keptValue)] ++ (fresh, addedValue) :: environment)
      initialStore (.var fresh) value finalStore ↔
    Evaluates ([(fresh, keptValue)] ++ environment)
      initialStore (.var fresh) value finalStore := by
  have scopeValid : WellScoped
      (LocalScope.ids ([(fresh, keptValue)] ++ environment)) (.var fresh) :=
    .var (by simp [LocalScope.ids])
  exact scopeValid.evaluates_insert_fresh_iff
    (freshLocalId_not_mem owner (LocalScope.ids environment))

theorem nested_same_id_binder_has_exact_evaluation_iff
    (addedValue value : Core.Value) (initialStore finalStore : Core.Store) :
    Evaluates ((fresh, addedValue) :: environment) initialStore nested value finalStore ↔
      Evaluates environment initialStore nested value finalStore :=
  nested_scoped.evaluates_weaken_fresh_iff
    (freshLocalId_not_mem owner (LocalScope.ids environment))

theorem allocated_head_has_exact_evaluation_iff
    (addedValue value : Core.Value) (initialStore finalStore : Core.Store) :
    Evaluates ((freshLocalId owner (LocalScope.ids environment), addedValue) :: environment)
      initialStore (.var oldId) value finalStore ↔
    Evaluates environment initialStore (.var oldId) value finalStore := by
  have scopeValid : WellScoped (LocalScope.ids environment) (.var oldId) :=
    .var (by simp [LocalScope.ids, environment])
  exact scopeValid.evaluates_weaken_allocated_iff owner addedValue

/-- Reverse the independent extended evaluation; the inserted value is arbitrary
and the inner `fresh` binder continues to return true. -/
theorem nested_extended_evaluation_reflects (addedValue : Core.Value) (store : Core.Store) :
    Evaluates ((fresh, addedValue) :: environment) store nested (.bool true) store ∧
      Evaluates environment store nested (.bool true) store := by
  have extended : Evaluates ((fresh, addedValue) :: environment)
      store nested (.bool true) store :=
    .letE .bool (.letE .bool (.var (.tail (by decide) .head)))
  exact ⟨extended, extended.reflect_insert_fresh (leading := []) nested_scoped
    (freshLocalId_not_mem owner (LocalScope.ids environment))⟩

private def emptyFresh : LocalId := freshLocalId owner []

/-- The absent-ID premise holds, but the old expression is unscoped and has no
evaluation. Insertion creates a new evaluation, so reverse preservation fails. -/
theorem freshness_alone_does_not_reflect (addedValue : Core.Value) (store : Core.Store) :
    emptyFresh ∉ ([] : List LocalId) ∧ ¬ WellScoped [] (.var emptyFresh) ∧
    (∀ value finalStore, ¬ Evaluates [] store (.var emptyFresh) value finalStore) ∧
    Evaluates [(emptyFresh, addedValue)] store (.var emptyFresh) addedValue store := by
  refine ⟨freshLocalId_not_mem owner [], ?_, ?_, .var .head⟩
  · intro scopeValid
    cases scopeValid with
    | var member => cases member
  · intro value finalStore evaluation
    cases evaluation with
    | var found => cases found

end Tests.ResolvedScopeReflection
