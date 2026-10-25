import Solcore.Frontend.RustHull.RuntimeEffectsSemantics
import Solcore.Frontend.RustHull.EnvironmentSemantics

/-! Independent Hull effects with memory, account storage and immutable
message/block observations. An environment read leaves both state components
unchanged, including when optional information is unavailable. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeEnvironmentEffectsSemantics

structure State where
  runtime : RuntimeEffectsSemantics.State := {}
  environment : EnvironmentSemantics.State := {}

def builtin (name : String) (type : Ty) (arguments : List Semantics.Value)
    (state : State) : Option (Semantics.Result Semantics.Value × State) :=
  match RuntimeEffectsSemantics.builtin name type arguments state.runtime with
  | some (result, runtime) => some (result, {state with runtime := runtime})
  | none => (EnvironmentSemantics.builtin name type arguments state.environment).map
      fun (result, environment) => (result, {state with environment := environment})

def effects : Semantics.ExternalSemantics State where
  builtin := fun name type arguments initial result final =>
    builtin name type arguments initial = some (result, final)
  assembly := fun _ _ _ _ _ _ => False
  revert := fun _ _ _ _ => False

end Solcore.Frontend.RustHull.RuntimeEnvironmentEffectsSemantics
