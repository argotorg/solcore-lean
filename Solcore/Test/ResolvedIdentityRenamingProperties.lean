import Solcore.Resolved.Renaming

/-! Compile-time identity-renaming consumers. Injective index shifts preserve
meaning, while a constant map captures an outer reference under an inner let. -/

set_option autoImplicit false

namespace Tests.ResolvedIdentityRenaming

open Solcore Solcore.Resolved

private def modulePath : Workspace.ModulePath := ⟨[⟨"Rename", by decide⟩], by decide⟩
private def outerId : LocalId := ⟨⟨⟨.main, modulePath⟩, 0⟩, 0⟩
private def innerId : LocalId := { outerId with binderIndex := 1 }

private def shift (id : LocalId) : LocalId := { id with binderIndex := id.binderIndex + 1 }

private theorem shift_injective : Function.Injective shift := by
  intro first second same
  have owners := congrArg LocalId.owner same
  change first.owner = second.owner at owners
  have shifted := congrArg LocalId.binderIndex same
  change first.binderIndex + 1 = second.binderIndex + 1 at shifted
  have indices := Nat.add_right_cancel shifted
  cases first
  cases second
  cases owners
  cases indices
  rfl

private def expression : Expr :=
  .letE outerId (.bool false) (.letE innerId (.bool true) (.var outerId))

private def originalCore : Core.Expr := .letE (.bool false) (.letE (.bool true) (.var 1))
private def capturedCore : Core.Expr := .letE (.bool false) (.letE (.bool true) (.var 0))

private theorem original_lowered : Lowers [] expression originalCore :=
  .letE .bool (.letE .bool (.var (.tail (by decide) .head)))

private theorem original_typed : HasType [] expression .bool :=
  .letE .bool (.letE .bool (.var (.tail (by decide) .head)))

private theorem original_evaluates (store : Core.Store) :
    Evaluates [] store expression (.bool false) store :=
  .letE .bool (.letE .bool (.var (.tail (by decide) .head)))

theorem injective_shift_keeps_core :
    (expression.renameIds shift).lower? [] = some originalCore := by
  simpa only [List.map_nil] using
    (Expr.lower?_renameIds shift shift_injective expression []).trans original_lowered.complete

theorem injective_shift_keeps_type : HasType [] (expression.renameIds shift) .bool :=
  (typing_renameIds_iff shift shift_injective).mpr original_typed

theorem injective_shift_keeps_value_and_store (store : Core.Store) :
    Evaluates [] store (expression.renameIds shift) (.bool false) store :=
  (evaluates_renameIds_iff shift shift_injective).mpr (original_evaluates store)

private def collapse (_id : LocalId) : LocalId := outerId

private theorem collapsed_lowered : Lowers [] (expression.renameIds collapse) capturedCore :=
  .letE .bool (.letE .bool (.var .head))

theorem constant_map_changes_core :
    (expression.renameIds collapse).lower? [] ≠ expression.lower? [] := by
  rw [collapsed_lowered.complete, original_lowered.complete]
  intro same
  cases same

theorem constant_map_captures_outer_reference (store : Core.Store) :
    Evaluates [] store (expression.renameIds collapse) (.bool true) store :=
  .letE .bool (.letE .bool (.var .head))

theorem constant_map_does_not_preserve_result (store finalStore : Core.Store) :
    ¬ Evaluates [] store (expression.renameIds collapse) (.bool false) finalStore := by
  intro evaluation
  have impossible := (evaluation_deterministic evaluation (constant_map_captures_outer_reference store)).1
  cases impossible

theorem constant_map_not_injective : ¬ Function.Injective collapse := by
  intro injective
  have same : outerId = innerId := injective rfl
  have different : outerId ≠ innerId := by decide
  exact different same

end Tests.ResolvedIdentityRenaming
