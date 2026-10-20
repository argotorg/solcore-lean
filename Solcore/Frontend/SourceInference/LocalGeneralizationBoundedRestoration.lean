import Solcore.Frontend.SourceInference.LocalGeneralizationBoundedAuxiliaryHelpers

/-! Restoring a genuinely saved lexical scope preserves the traversal entry
cutoff. The suffix starts at the exact restored state. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.Frontend.SourceInference.LocalGeneralizationBoundaries
namespace Progress

/-- Restore the scope saved at this traversal's actual entry. -/
theorem restored_start {before middle : State} (initialStep : Progress before middle) :
    Progress before (middle.restoreLexicalScope before.lexicalScope) :=
  initialStep.restore before.lexicalScope (fun _ member => member)

/-- Continue from the exact state produced by restoring the entry scope. -/
theorem restored_then {before middle after : State}
    (initialStep : Progress before middle)
    (suffix : Progress (middle.restoreLexicalScope before.lexicalScope) after) :
    Progress before after :=
  initialStep.restored_start.trans suffix

/-- Restore a previously saved scope only with its actual binder membership. -/
theorem restored_saved_then {before middle after : State} {scope : LexicalScope}
    (initialStep : Progress before middle) (saved : scope.binders ⊆ before.localBinders)
    (suffix : Progress (middle.restoreLexicalScope scope) after) :
    Progress before after :=
  (initialStep.restore scope saved).trans suffix

/-- Actual pair-result equality exposes the restored state without changing
which traversal entry supplied the saved-scope evidence. -/
theorem restored_pair_result {alpha : Type} {value : alpha} {before middle : State}
    {scope : LexicalScope} {result : alpha × State}
    (initialStep : Progress before middle) (saved : scope.binders ⊆ before.localBinders)
    (completed : (value, middle.restoreLexicalScope scope) = result) :
    Progress before result.2 := by
  rw [← completed]
  exact initialStep.restore scope saved

/-- A successful pure return retains the exact restored pair-result state. -/
theorem restored_pure_result {epsilon alpha : Type} {value : alpha} {before middle : State}
    {scope : LexicalScope} {result : alpha × State}
    (initialStep : Progress before middle) (saved : scope.binders ⊆ before.localBinders)
    (completed : (pure (value, middle.restoreLexicalScope scope) : Except epsilon (alpha × State)) = .ok result) :
    Progress before result.2 := by
  change Except.ok (value, middle.restoreLexicalScope scope) = Except.ok result at completed
  exact initialStep.restored_pair_result saved (Except.ok.inj completed)

end Progress
end Solcore.Frontend.SourceInference.LocalGeneralizationBoundaries
