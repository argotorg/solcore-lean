import Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedOutput
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedTerminalBody

/-! The original lexical return envelope preserves the concrete Source/native
materialized payload. The function footer removes only that envelope. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedFlowOutput
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CellAwareMaterializedOutput

def FlowAt (compiled : SourceCoreUnifiedCompilation.Compiled)
    (mapping : LocationMap) (world : StoreTyping) (location : Core.Location)
    (outcome : Staging.Recursive.BodyOutcome) (native : Core.Value) : Prop :=
  ∀ source, outcome = .returned source →
    ∃ payload, native = LocalLoop.returnedValue payload ∧ ValueAt compiled mapping world location source payload

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {mapping : LocationMap}
  {world : StoreTyping} {location : Core.Location} {native : Value}

theorem FlowAt.returned {source : Dynamic.Value}
    (value : ValueAt compiled mapping world location source native) :
    FlowAt compiled mapping world location (.returned source) (LocalLoop.returnedValue native) := by
  intro other same
  cases same
  exact ⟨native, rfl, value⟩

theorem FlowAt.fault {failure : Staging.Recursive.Failure} :
    FlowAt compiled mapping world location (.fault failure) native := by
  intro source impossible
  cases impossible

end Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedFlowOutput
