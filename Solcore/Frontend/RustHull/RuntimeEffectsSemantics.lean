import Solcore.Frontend.RustHull.MemorySemantics
import Solcore.Frontend.RustHull.StorageSemantics

/-! Independent memory and account-storage effects in one Hull state. The
source observations contain account data and mathematical memory words only. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeEffectsSemantics

structure State where
  memory : MemorySemantics.State := {}
  storage : StorageSemantics.State := {}
  deriving Repr

def builtin (name : String) (type : Ty) (arguments : List Semantics.Value)
    (state : State) : Option (Semantics.Result Semantics.Value × State) :=
  match MemorySemantics.builtin name type arguments state.memory with
  | some (result, memory) => some (result, {state with memory := memory})
  | none => (StorageSemantics.builtin name type arguments state.storage).map
      fun (result, storage) => (result, {state with storage := storage})

def effects : Semantics.ExternalSemantics State where
  builtin := fun name type arguments initial result final =>
    builtin name type arguments initial = some (result, final)
  assembly := fun _ _ _ _ _ _ => False
  revert := fun _ _ _ _ => False

end Solcore.Frontend.RustHull.RuntimeEffectsSemantics
