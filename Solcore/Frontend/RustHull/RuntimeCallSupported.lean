import Solcore.Frontend.RustHull.RuntimeCallEffectsSemantics
import Solcore.Frontend.RustHull.RuntimeReturnDataSupported

/-! Call names extend the executable subset without changing the selection of
existing return-data and runtime builtins. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeCallEffectsCorrespondence
open Correspondence

def supported (slots : List EffectSlot) (withCode : Bool) (name : String) : Prop :=
  RuntimeReturnDataEffectsCorrespondence.supported slots withCode name ∨ name = "call" ∨ name = "staticcall"

theorem primitive_none {slots : List EffectSlot} {withCode : Bool} {name : String}
    (enabled : supported slots withCode name) (type : Ty) (arguments : List Semantics.Value) :
    Semantics.primitive? name type arguments = none := by
  rcases enabled with runtime | rfl | rfl
  · exact RuntimeReturnDataEffectsCorrespondence.primitive_none runtime type arguments
  · rfl
  · rfl

private theorem code_call_unsupported {image : Option (List UInt8)} {name : String} {type : Ty}
    {arguments : List Semantics.Value} {initial final : RuntimeCodeEffectsSemantics.State}
    {result : Semantics.Result Semantics.Value}
    (newName : name = "call" ∨ name = "staticcall")
    (computed : RuntimeCodeEffectsSemantics.Builtin image name type arguments initial result final) : False := by
  cases computed with
  | copy computed =>
      obtain ⟨operation, named⟩ := computed.named
      rcases newName with rfl | rfl <;> cases operation <;>
        simp [CodeImageSemantics.Operation.name] at named
  | runtime computed =>
      cases computed with
      | observation computed =>
          obtain ⟨operation, named⟩ := computed.named
          rcases newName with rfl | rfl <;> cases operation <;>
            simp [AccountObservationSemantics.Operation.name] at named
      | runtime computed =>
          cases computed with
          | hash computed =>
              cases computed
              simp at newName
          | runtime computed =>
              cases computed with
              | copy computed =>
                  cases computed <;> simp at newName
              | runtime computed =>
                  cases computed with
                  | termination computed =>
                      have missing : TerminationSemantics.builtin name type arguments initial.runtime.runtime.runtime = none := by
                        rcases newName with rfl | rfl <;> rfl
                      rw [missing] at computed
                      contradiction
                  | runtime computed =>
                      cases computed with
                      | logs computed =>
                          cases computed with
                          | log operation _ _ _ _ _ _ =>
                              rcases newName with named | named <;> cases operation <;>
                                simp [LogsSemantics.Operation.name] at named
                      | runtime computed =>
                          have missing : RuntimeEnvironmentEffectsSemantics.builtin name type arguments initial.runtime.runtime = none := by
                            rcases newName with rfl | rfl <;> rfl
                          rw [missing] at computed
                          contradiction


private theorem runtime_call_unsupported {image : Option (List UInt8)} {name : String} {type : Ty}
    {arguments : List Semantics.Value} {initial final : RuntimeReturnDataEffectsSemantics.State}
    {result : Semantics.Result Semantics.Value}
    (newName : name = "call" ∨ name = "staticcall")
    (computed : RuntimeReturnDataEffectsSemantics.Builtin image name type arguments initial result final) : False := by
  cases computed with
  | runtime computed => exact code_call_unsupported newName computed
  | copy computed => cases computed; simp at newName
  | guard computed => cases computed; simp at newName

theorem runtime_enabled {slots : List EffectSlot} {withCode : Bool} {image : Option (List UInt8)}
    {name : String} {type : Ty} {arguments : List Semantics.Value}
    {initial final : RuntimeReturnDataEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (enabled : supported slots withCode name)
    (computed : RuntimeReturnDataEffectsSemantics.Builtin image name type arguments initial result final) :
    RuntimeReturnDataEffectsCorrespondence.supported slots withCode name := by
  rcases enabled with runtime | called | staticCall
  · exact runtime
  · exact False.elim (runtime_call_unsupported (.inl called) computed)
  · exact False.elim (runtime_call_unsupported (.inr staticCall) computed)

end Solcore.Frontend.RustHull.RuntimeCallEffectsCorrespondence
