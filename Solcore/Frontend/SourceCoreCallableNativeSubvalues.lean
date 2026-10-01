import Solcore.Frontend.SourceCoreCallableNativeSlots

/-! Locate native values in public data without entering closure environments.
Each successful lookup retains its structural path, and runtime typing follows
from the enclosing typed result or source-cell payload. This pure operation
supplies no source-code, allocation or execution-history authority itself.
-/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCallableNativeSubvalues
open Core SourceCoreCallableNativeSlots

structure Path (value root : Value) : Type where
  related : Subvalue value root

/-- Saved closure environments remain outside public data paths. -/
def find (value : Value) : (root : Value) → Option (Path value root)
  | .pair left right =>
    if same : value = .pair left right then some ⟨same ▸ .root⟩
    else match find value left with
      | some inside => some ⟨.pairLeft inside.related⟩
      | none => (find value right).map fun inside => ⟨.pairRight inside.related⟩
  | .inLeft type payload =>
    if same : value = .inLeft type payload then some ⟨same ▸ .root⟩
    else (find value payload).map fun inside => ⟨.inLeft inside.related⟩
  | .inRight type payload =>
    if same : value = .inRight type payload then some ⟨same ▸ .root⟩
    else (find value payload).map fun inside => ⟨.inRight inside.related⟩
  | .constructed constructor payload =>
    if same : value = .constructed constructor payload then some ⟨same ▸ .root⟩
    else (find value payload).map fun inside => ⟨.constructed inside.related⟩
  | root => if same : value = root then some ⟨same ▸ .root⟩ else none

/-- A public data path inherits its actual finite-world native typing. -/
theorem runtime_typed {definitions : DataEnvironment} {world : StoreTyping}
    {value root : Value} {type : Ty} (inside : Subvalue value root)
    (typed : RuntimeValueHasType world root type definitions) :
    RuntimeValueHasType world value value.type definitions := by
  induction inside generalizing type with
  | root => simpa only [typed.type_eq] using typed
  | pairLeft inside ih => cases typed with | pair left right => exact ih left
  | pairRight inside ih => cases typed with | pair left right => exact ih right
  | inLeft inside ih => cases typed with | inLeft payload => exact ih payload
  | inRight inside ih => cases typed with | inRight payload => exact ih payload
  | constructed inside ih => cases typed with | constructed _ payload => exact ih payload

end Solcore.Frontend.SourceCoreCallableNativeSubvalues
