import Solcore.SourceSemantics.CoreLowering.SelectedCompilationMixedRootSupport
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCoercionPathBounds
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageMethodBodyLifting
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageCoercionPathLifting

/-! The shared numerical induction supplies every conversion body from the
actual terminal packet, preserving the exact SourceAt and reached caller. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStagePhysicalCoercionMethods
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open SelectedCompilationMixedRootBounds
open SelectedCompilationStageLiftBounds (LiftsRootsAt)
open SelectedCompilationMixedRootSupport (CoercionMethods)
open CallableIndexedOwnedPreparedStagedCoercionChain (Chain)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {project : SourceCoreEvidence.Projector} {compilation : SourceCoreFunctions.Context}
  {caller : SourceSpecialization.SpecializedFunction}
  {available : SourceTypedRuntime.RuntimeEvidenceEnvironment}
  {scope : SourceCoreBasic.Scope} {node : ExpressionNode}
  {policy : SourceCoreFunctions.CallablePolicy}
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {stages : Staging.Recursive.Registry}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {semanticFaults : FunctionCalls.FaultRep}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (keyPhysical : CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry}
  {source target : TypeSystem.Ty} {input output : SourceCoreBasic.LoweredExpr}
  {steps : List CoercionStep} {calls : List CallableCoercionSpine.Call}
  (chain : Chain compiled project compilation caller available scope node policy context invocation stages
    source target input steps output calls)
  (support : CoercionMethods headers semanticFaults chain)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions

include keyPhysical support in
theorem lift_bodies (budget : Nat)
    (children : ∀ size, size < budget → LiftsRootsAt (headers := headers) (keys := keys)
      model stages semanticFaults size) :
    SelectedCompilationStageCoercionPathLifting.LiftBodies
      (headers := headers) (receiving := receiving) owner functions chain budget := by
  induction chain with
  | nil => trivial
  | cons step port valid tail ih =>
      obtain ⟨⟨packet, sourceAt, certified, static⟩, remaining⟩ := support
      refine ⟨?_, ih remaining⟩
      intro mapping world heap store callerScope canonical administrative arguments payloads caller installed
        _parameters heapTyped argumentsTyped stable child selected
      have packetArguments : Dynamic.ValuesHaveTypes port.principal.sourceFunction.context heap
          arguments packet.sourceAt.types := by
        simpa only [sourceAt] using argumentsTyped
      simpa only [SelectedCompilationMethodBodies.Packet.sourceAt, sourceAt] using
        SelectedCompilationStageMethodTerminalLifting.source_continuation
          port.principal packet static certified functions selected installed
          owner keyPhysical caller heapTyped packetArguments stable budget children


end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStagePhysicalCoercionMethods
