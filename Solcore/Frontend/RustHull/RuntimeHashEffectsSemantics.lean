import Solcore.Frontend.RustHull.RuntimeCopyEffectsSemantics
import Solcore.Frontend.RustHull.KeccakSemantics

/-! Hashing observes source memory and updates its touched extent while the
surrounding world, event stream and message observations remain available. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeHashEffectsSemantics

abbrev State := RuntimeCopyEffectsSemantics.State
abbrev withMemory := RuntimeCopyEffectsSemantics.withMemory

inductive Builtin : String → Ty → List Semantics.Value → State → Semantics.Result Semantics.Value → State → Prop where
  | runtime {name type arguments state result final}
      (computed : RuntimeCopyEffectsSemantics.Builtin name type arguments state result final) :
      Builtin name type arguments state result final
  | hash {name type arguments state result final}
      (computed : KeccakSemantics.Builtin name type arguments state.runtime.runtime.memory result final) :
      Builtin name type arguments state result (withMemory state final)

def effects : Semantics.ExternalSemantics State where
  builtin := Builtin
  assembly := fun _ _ _ _ _ _ => False
  revert := fun _ _ _ _ => False

end Solcore.Frontend.RustHull.RuntimeHashEffectsSemantics
