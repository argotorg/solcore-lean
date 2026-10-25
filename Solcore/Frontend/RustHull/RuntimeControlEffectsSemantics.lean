import Solcore.Frontend.RustHull.TerminationSemantics

/-! Independent memory, storage, and message termination share the same source
state. Termination changes the memory size and message exit registers together. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeControlEffectsSemantics

abbrev State := RuntimeEffectsSemantics.State

def builtin (name : String) (type : Ty) (arguments : List Semantics.Value)
    (state : State) : Option (Semantics.Result Semantics.Value × State) :=
  match RuntimeEffectsSemantics.builtin name type arguments state with
  | some output => some output
  | none => TerminationSemantics.builtin name type arguments state

def effects : Semantics.ExternalSemantics State where
  builtin := fun name type arguments initial result final =>
    builtin name type arguments initial = some (result, final)
  assembly := fun _ _ _ _ _ _ => False
  revert := fun _ _ _ _ => False

end Solcore.Frontend.RustHull.RuntimeControlEffectsSemantics
