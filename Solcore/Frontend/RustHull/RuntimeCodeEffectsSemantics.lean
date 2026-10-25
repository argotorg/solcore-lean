import Solcore.Frontend.RustHull.RuntimeAccountEffectsSemantics
import Solcore.Frontend.RustHull.CodeImageSemantics

/-! A linked code image is fixed during a frame. Copying it updates the same
memory used by account observations and the other runtime operations. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeCodeEffectsSemantics

abbrev State := RuntimeAccountEffectsSemantics.State

inductive Builtin (image : Option (List UInt8)) : String → Ty → List Semantics.Value →
    State → Semantics.Result Semantics.Value → State → Prop where
  | runtime {name : String} {type : Ty} {arguments : List Semantics.Value}
      {initial final : State} {result : Semantics.Result Semantics.Value}
      (computed : RuntimeAccountEffectsSemantics.Builtin name type arguments initial result final) :
      Builtin image name type arguments initial result final
  | copy {name : String} {type : Ty} {arguments : List Semantics.Value}
      {initial : State} {memory : MemorySemantics.State} {result : Semantics.Result Semantics.Value}
      (computed : CodeImageSemantics.Builtin image name type arguments
        initial.runtime.runtime.runtime.memory result memory) :
      Builtin image name type arguments initial result (RuntimeAccountEffectsSemantics.withMemory initial memory)

def effects (image : Option (List UInt8)) : Semantics.ExternalSemantics State where
  builtin := Builtin image
  assembly := fun _ _ _ _ _ _ => False
  revert := fun _ _ _ _ => False

end Solcore.Frontend.RustHull.RuntimeCodeEffectsSemantics
