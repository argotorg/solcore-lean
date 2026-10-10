import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCanonicalFlowBounds

/-! Both authentic caller protocols already retain their actual canonical
Globals observations. This carrier projects those literal fields and restores
the same reached pool. Forgetting its slot observations is definitionally the
original Origin bridge; no base-state packet or Source authority is inferred. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOriginGlobalsCarriers
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedPreparedCanonicalFlowBounds (Origin)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  (origin : Origin compiled) (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)

/-- The original complete packet supplies its own slots at the same pool. -/
def carrier : CallableIndexedOwnedNamedCallerProtocol.Carrier
    (headers := headers)
    (fun index => CallableIndexedOwnedExpressionHeads.Globals (headers := headers) owner 1 index.scope index.canonical)
    (Origin.protocol (headers := headers) origin owner) :=
  match origin with
  | .ordinary caller => CallableIndexedOwnedNestedCallerProtocol.carrier owner caller
  | .principal named => CallableIndexedOwnedOriginCanonicalState.carrier owner named

/-- The semantic bridge, actual returned pool and record lists are unchanged. -/
theorem forget_slots :
    CallableIndexedOwnedIndirectCallerProtocol.forget_slots (carrier (headers := headers) origin owner) =
      Origin.bridge (headers := headers) origin owner := by
  cases origin <;> rfl

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOriginGlobalsCarriers
