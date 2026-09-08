import Solcore.Resolved.FreshIdentity
import Solcore.Resolved.ScopeExtensionProperties
import Solcore.Resolved.ScopeExtensionEvaluationProperties

/-! Fresh allocation is local to the caller's scope. Extension must preserve
both free outer references and existing inner binders, even when they share the new ID. -/

set_option autoImplicit false

namespace Tests.ResolvedFreshBinding

open Solcore Solcore.Resolved

private def modulePath : Workspace.ModulePath := ⟨[⟨"Fresh", by decide⟩], by decide⟩
private def owner : DeclarationId := ⟨⟨.main, modulePath⟩, 0⟩
private def oldId : LocalId := ⟨owner, 0⟩
private def innerId : LocalId := ⟨owner, 3⟩
private def otherOwnerId : LocalId := ⟨{ owner with declarationIndex := 1 }, 999⟩
private def outsideId : LocalId := ⟨owner, 4⟩
private def scope : List LocalId := [oldId, innerId, oldId]
private def allocated : LocalId := freshLocalId owner scope

theorem allocation_respects_owner_and_supplied_scope :
    allocated = outsideId ∧ allocated.owner = owner ∧ allocated ∉ scope :=
  ⟨by decide, freshLocalId_owner owner scope, freshLocalId_not_mem owner scope⟩

theorem other_owners_and_permutations_do_not_change_allocation :
    freshLocalId owner (otherOwnerId :: scope) = allocated ∧
    freshLocalId owner [innerId, oldId, oldId] = allocated := by
  constructor
  · exact freshLocalId_cons_of_ne_owner owner scope otherOwnerId (by decide)
  · exact freshLocalId_eq_of_perm owner (List.Perm.swap oldId innerId [oldId])

theorem second_allocation_advances :
    (freshLocalId owner (allocated :: scope)).binderIndex = allocated.binderIndex + 1 ∧
    freshLocalId owner (allocated :: scope) ≠ allocated :=
  ⟨freshLocalId_cons_fresh_binderIndex owner scope, freshLocalId_cons_fresh_ne owner scope⟩

theorem scope_freshness_is_not_global_freshness :
    allocated ∉ scope ∧ allocated ∈ [outsideId] :=
  ⟨freshLocalId_not_mem owner scope, by decide⟩

private def environment : Environment :=
  [(oldId, .bool true), (innerId, .bool false), (oldId, .bool false)]
private def nested : Expr :=
  .letE allocated (.bool true) (.letE innerId (.bool false)
    (.ifE (.var allocated) (.var oldId) (.var innerId)))
private def originalCore : Core.Expr :=
  .letE (.bool true) (.letE (.bool false) (.ifE (.var 1) (.var 2) (.var 0)))
private def insertedCore : Core.Expr :=
  .letE (.bool true) (.letE (.bool false) (.ifE (.var 1) (.var 3) (.var 0)))

private theorem nested_lowered : Lowers scope nested originalCore :=
  .letE .bool (.letE .bool (.ifE
    (.var (.tail (by decide) .head))
    (.var (.tail (by decide) (.tail (by decide) .head))) (.var .head)))

private theorem nested_evaluates (store : Core.Store) :
    Evaluates environment store nested (.bool true) store :=
  .letE .bool (.letE .bool (.ifTrue
    (.var (.tail (by decide) .head))
    (.var (.tail (by decide) (.tail (by decide) .head)))))

/-- An existing inner binder equal to the inserted ID still wins lookup. The
outer oldId reference also retains its value, and the store is arbitrary. -/
theorem nested_binder_equal_to_inserted_id_keeps_value (store : Core.Store) :
    Evaluates environment store nested (.bool true) store ∧
    Evaluates ((allocated, .bool false) :: environment) store nested (.bool true) store :=
  ⟨nested_evaluates store, (nested_evaluates store).weaken_allocated owner (.bool false)⟩

/-- The bound positions 1 and 0 stay fixed; only the free outer position 2 shifts. -/
theorem nested_lowering_shifts_only_the_free_reference :
    nested.lower? scope = some originalCore ∧
    nested.lower? (allocated :: scope) = some insertedCore ∧
    nested.lower? (allocated :: scope) =
      (nested.lower? scope).map (fun core => core.weakenAt 0) := by
  have extended := (nested_lowered.weaken_fresh (freshLocalId_not_mem owner scope)).complete
  refine ⟨nested_lowered.complete, ?_,
    Expr.lower?_weaken_fresh nested_lowered.wellScoped (freshLocalId_not_mem owner scope)⟩
  simpa [allocated, originalCore, insertedCore, Core.Expr.weakenAt] using extended

/-- Without the absent-ID premise, an added outer entry captures the old reference. -/
theorem nonfresh_insertion_captures_reference (store : Core.Store) :
    Evaluates environment store (.var oldId) (.bool true) store ∧
    Evaluates ((oldId, .bool false) :: environment) store (.var oldId) (.bool false) store ∧
    ¬ Evaluates ((oldId, .bool false) :: environment) store (.var oldId) (.bool true) store := by
  refine ⟨.var .head, .var .head, ?_⟩
  intro evaluation
  have opposite : Evaluates ((oldId, .bool false) :: environment) store
      (.var oldId) (.bool false) store := .var .head
  have impossible := (evaluation_deterministic evaluation opposite).1
  cases impossible

private def skippedMissing : Expr := .ifE (.bool true) (.var oldId) (.var allocated)

/-- Evaluation preservation does not require the old, unselected branch to be scoped. -/
theorem skipped_unscoped_branch_keeps_evaluation (store : Core.Store) :
    skippedMissing.lower? scope = none ∧
    skippedMissing.lower? (allocated :: scope) = some (.ifE (.bool true) (.var 1) (.var 0)) ∧
    Evaluates ((allocated, .bool false) :: environment) store skippedMissing (.bool true) store := by
  have evaluation : Evaluates environment store skippedMissing (.bool true) store :=
    .ifTrue .bool (.var .head)
  exact ⟨by decide, by decide, evaluation.weaken_allocated owner (.bool false)⟩

end Tests.ResolvedFreshBinding
