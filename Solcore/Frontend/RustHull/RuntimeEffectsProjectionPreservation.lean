import Solcore.Frontend.RustHull.EffectProjectionPreservation
import Solcore.Frontend.RustHull.RuntimeEffectsSemantics

/-! Immutable account observations of the independent memory/storage model.
The public runtime uses the entry address to complete a message; this theorem
identifies it with the address observed after an arbitrary source execution. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeEffectsProjectionPreservation

structure Context where
  address : Core.Word
  complete : Bool
  isStatic : Bool

def storageContext (state : StorageSemantics.State) : Context :=
  ⟨state.address, state.complete, state.isStatic⟩

def context (state : RuntimeEffectsSemantics.State) : Context := storageContext state.storage

theorem load_context (state : StorageSemantics.State) (key : Core.Word) (transient : Bool) :
    storageContext (StorageSemantics.load state key transient).2 = storageContext state := by
  unfold StorageSemantics.load
  split <;> rfl

theorem store_context (state : StorageSemantics.State) (key value : Core.Word) (transient : Bool) :
    storageContext (StorageSemantics.store state key value transient).2 = storageContext state := by
  unfold StorageSemantics.store
  split
  · rfl
  · split <;> rfl

theorem storage_builtin_context {name : String} {type : Ty} {arguments : List Semantics.Value}
    {initial final : StorageSemantics.State} {result : Semantics.Result Semantics.Value}
    (called : StorageSemantics.builtin name type arguments initial = some (result, final)) :
    storageContext final = storageContext initial := by
  unfold StorageSemantics.builtin at called
  split at called
  all_goals try contradiction
  all_goals have changed := congrArg (fun output => storageContext output.2) (Option.some.inj called)
  all_goals simp only [load_context, store_context] at changed
  all_goals exact changed.symm

theorem builtin_context {name : String} {type : Ty} {arguments : List Semantics.Value}
    {initial final : RuntimeEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (called : RuntimeEffectsSemantics.builtin name type arguments initial = some (result, final)) :
    context final = context initial := by
  unfold RuntimeEffectsSemantics.builtin at called
  split at called
  · cases Option.some.inj called
    rfl
  · rename_i memory
    cases storage : StorageSemantics.builtin name type arguments initial.storage with
    | none => simp [storage] at called
    | some output =>
      rcases output with ⟨storageResult, storageState⟩
      simp only [storage, Option.map_some, Option.some.injEq, Prod.mk.injEq] at called
      rcases called with ⟨rfl, rfl⟩
      exact storage_builtin_context storage

theorem preserves : EffectProjectionPreservation.Preserves RuntimeEffectsSemantics.effects context where
  builtin := builtin_context
  assembly := False.elim
  revert := False.elim

theorem function_context {functions : List Function} {function : Function}
    {arguments : List Semantics.Value}
    {initial final : Semantics.State RuntimeEffectsSemantics.State}
    {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction functions RuntimeEffectsSemantics.effects
      function arguments initial result final) :
    context final.external = context initial.external :=
  EffectProjectionPreservation.function_preserves preserves evaluated

theorem function_observations {functions : List Function} {function : Function}
    {arguments : List Semantics.Value}
    {initial final : Semantics.State RuntimeEffectsSemantics.State}
    {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction functions RuntimeEffectsSemantics.effects
      function arguments initial result final) :
    final.external.storage.address = initial.external.storage.address ∧
    final.external.storage.complete = initial.external.storage.complete ∧
    final.external.storage.isStatic = initial.external.storage.isStatic :=
  ⟨congrArg Context.address (function_context evaluated),
   congrArg Context.complete (function_context evaluated),
   congrArg Context.isStatic (function_context evaluated)⟩

end Solcore.Frontend.RustHull.RuntimeEffectsProjectionPreservation
