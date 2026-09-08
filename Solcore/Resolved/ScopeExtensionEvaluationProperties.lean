import Solcore.Resolved.EvaluationProperties
import Solcore.Resolved.FreshIdentity

set_option autoImplicit false

namespace Solcore.Resolved

/-- Inserting an absent identity behind a retained prefix preserves existing lookup.
The retained prefix may itself contain the inserted identity. -/
theorem LocalScope.Lookup.insert_fresh {α : Type} {leading suffix : LocalScope α}
    {id newId : LocalId} {value newValue : α}
    (found : LocalScope.Lookup (leading ++ suffix) id value)
    (fresh : newId ∉ LocalScope.ids suffix) :
    LocalScope.Lookup (leading ++ (newId, newValue) :: suffix) id value := by
  induction leading with
  | nil =>
      have different : newId ≠ id := by
        intro same
        apply fresh
        rw [same]
        exact List.mem_map.mpr ⟨_, found.mem, rfl⟩
      exact .tail different found
  | cons entry rest ih =>
      rcases entry with ⟨candidate, entryValue⟩
      cases found with
      | head => exact .head
      | tail different found => exact .tail different (ih found)

private theorem evaluation_insert_aux
    {environment : Environment} {initialStore finalStore : Core.Store}
    {expr : Expr} {value : Core.Value}
    (evaluation : Evaluates environment initialStore expr value finalStore) :
    ∀ (leading suffix : Environment), environment = leading ++ suffix →
      ∀ (newId : LocalId) (newValue : Core.Value), newId ∉ LocalScope.ids suffix →
        Evaluates (leading ++ (newId, newValue) :: suffix) initialStore expr value finalStore := by
  induction evaluation with
  | unit => intros; exact .unit
  | bool => intros; exact .bool
  | word => intros; exact .word
  | var found =>
      intro leading suffix split newId newValue fresh
      rw [split] at found
      exact .var (found.insert_fresh fresh)
  | unary _ applied ih =>
      intro leading suffix split newId newValue fresh
      exact .unary (ih leading suffix split newId newValue fresh) applied
  | binary _ _ applied leftIH rightIH =>
      intro leading suffix split newId newValue fresh
      exact .binary (leftIH leading suffix split newId newValue fresh)
        (rightIH leading suffix split newId newValue fresh) applied
  | @letE environment initialStore middleStore finalStore binder value body boundValue result
      _ _ valueIH bodyIH =>
      intro leading suffix split newId newValue fresh
      exact .letE (valueIH leading suffix split newId newValue fresh)
        (bodyIH ((binder, boundValue) :: leading) suffix
          (by simpa only [List.cons_append] using congrArg (List.cons (binder, boundValue)) split)
          newId newValue fresh)
  | ifTrue _ _ conditionIH branchIH =>
      intro leading suffix split newId newValue fresh
      exact .ifTrue (conditionIH leading suffix split newId newValue fresh)
        (branchIH leading suffix split newId newValue fresh)
  | ifFalse _ _ conditionIH branchIH =>
      intro leading suffix split newId newValue fresh
      exact .ifFalse (conditionIH leading suffix split newId newValue fresh)
        (branchIH leading suffix split newId newValue fresh)

/-- Existing evaluations survive fresh insertion, with exactly the same value
and store. Neither typing nor elaboration of skipped branches is required. -/
theorem Evaluates.insert_fresh {leading suffix : Environment}
    {initialStore finalStore : Core.Store} {expr : Expr} {value newValue : Core.Value}
    {newId : LocalId}
    (evaluation : Evaluates (leading ++ suffix) initialStore expr value finalStore)
    (fresh : newId ∉ LocalScope.ids suffix) :
    Evaluates (leading ++ (newId, newValue) :: suffix) initialStore expr value finalStore :=
  evaluation_insert_aux evaluation leading suffix rfl newId newValue fresh

theorem Evaluates.weaken_fresh {environment : Environment}
    {initialStore finalStore : Core.Store} {expr : Expr} {value newValue : Core.Value}
    {newId : LocalId} (evaluation : Evaluates environment initialStore expr value finalStore)
    (fresh : newId ∉ LocalScope.ids environment) :
    Evaluates ((newId, newValue) :: environment) initialStore expr value finalStore :=
  Evaluates.insert_fresh (leading := []) evaluation fresh

/-- The allocator supplies the precise local freshness premise needed by evaluation. -/
theorem Evaluates.weaken_allocated {environment : Environment}
    {initialStore finalStore : Core.Store} {expr : Expr} {value : Core.Value}
    (evaluation : Evaluates environment initialStore expr value finalStore)
    (owner : DeclarationId) (newValue : Core.Value) :
    Evaluates ((freshLocalId owner (LocalScope.ids environment), newValue) :: environment)
      initialStore expr value finalStore :=
  evaluation.weaken_fresh (freshLocalId_not_mem owner (LocalScope.ids environment))

end Solcore.Resolved
