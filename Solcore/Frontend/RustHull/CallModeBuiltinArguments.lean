import Solcore.Frontend.RustHull.CallBuiltinArguments
import Solcore.Frontend.RustHull.RuntimeCallModeSemantics

set_option autoImplicit false
namespace Solcore.Frontend.RustHull

def RuntimeCallModeSemantics.Operation.arity : RuntimeCallModeSemantics.Operation → Nat
  | .ordinary | .callCode => 7
  | .staticCall | .delegateCall => 6

namespace CallModeBuiltinCorrespondence
open Core Correspondence PureCallCorrespondence EffectBuiltinCorrespondence
open RuntimeCallModeSemantics (Operation)

theorem inner_arity (operation : Operation) {scope : Scope}
    {arguments : List Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope operation.name arguments = .ok lowered) :
    arguments.length = operation.arity := by
  cases operation with
  | ordinary | callCode =>
      rcases arguments with _ | ⟨first, _ | ⟨second, _ | ⟨third, _ | ⟨fourth, _ | ⟨fifth, _ | ⟨sixth, _ | ⟨seventh, _ | ⟨eighth, rest⟩⟩⟩⟩⟩⟩⟩⟩
      all_goals first
        | rfl
        | change Except.error _ = Except.ok lowered at compiled
          cases compiled
  | staticCall | delegateCall =>
      rcases arguments with _ | ⟨first, _ | ⟨second, _ | ⟨third, _ | ⟨fourth, _ | ⟨fifth, _ | ⟨sixth, _ | ⟨seventh, rest⟩⟩⟩⟩⟩⟩⟩
      all_goals first
        | rfl
        | change Except.error _ = Except.ok lowered at compiled
          cases compiled

end CallModeBuiltinCorrespondence
end Solcore.Frontend.RustHull
