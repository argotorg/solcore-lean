import Solcore.Frontend.RustHull.ContractReturnDataCorrespondence
import Solcore.Frontend.RustHull.RuntimeCallModeSupported
import Solcore.Frontend.RustHull.RuntimeExtendedInitializedEffects

/-! The public effect subset includes all four message-call operations. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ContractCallModeCorrespondence
open Correspondence

def supported (withCode : Bool) (name : String) : Prop :=
  ContractReturnDataCorrespondence.supported withCode name ∨ name = "call" ∨ name = "staticcall" ∨ name = "callcode" ∨ name = "delegatecall"

theorem supported_actual {slots : List EffectSlot} {withCode : Bool}
    (signature : RuntimeEffectsFrameCorrespondence.slotTypes slots = RuntimeExtendedInitializedEffects.slots withCode) :
    RuntimeCallModeEffectsCorrespondence.supported slots withCode = supported withCode := by
  funext name
  apply propext
  simp only [RuntimeCallModeEffectsCorrespondence.supported, supported,
    ContractReturnDataCorrespondence.supported_actual signature]

end Solcore.Frontend.RustHull.ContractCallModeCorrespondence
