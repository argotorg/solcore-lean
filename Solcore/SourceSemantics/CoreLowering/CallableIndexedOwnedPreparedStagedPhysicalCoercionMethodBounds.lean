import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalMixedRootStaticSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCoercionPathBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodBodyBounds

/-! The shared numerical induction supplies every conversion body from the
actual terminal packet, preserving the exact SourceAt and reached caller. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalCoercionMethodBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedPreparedStagedPhysicalMixedRootBounds
open CallableIndexedOwnedPreparedStagedPhysicalMixedRootStaticSupport (CoercionMethods)
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
  {receiving : SourceCoreRawMetadata.Registry} (faults : RecursiveStageMeaning.FaultRep)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry receiving)
  {source target : TypeSystem.Ty} {input output : SourceCoreBasic.LoweredExpr}
  {steps : List CoercionStep} {calls : List CallableCoercionSpine.Call}
  (chain : Chain compiled project compilation caller available scope node policy context invocation stages
    source target input steps output calls)
  (support : CoercionMethods headers semanticFaults chain)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions

variable (semantic : ∀ reason token, semanticFaults reason token → faults (.semantic reason) token)

include keyPhysical wellFormed support in
theorem source_bodies (budget : Nat)
    (children : ∀ size, size < budget → PreservesRootsAt (headers := headers) (keys := keys)
      model stages semanticFaults faults size) :
    CallableIndexedOwnedPreparedStagedCoercionPathBounds.SourceBodies
      (headers := headers) (receiving := receiving) owner functions faults chain budget := by
  induction chain with
  | nil => trivial
  | cons step port valid tail ih =>
      obtain ⟨⟨packet, sourceAt, static⟩, remaining⟩ := support
      refine ⟨?_, ih remaining⟩
      intro mapping world heap store callerScope canonical administrative arguments payloads caller installed
        _parameters heapTyped argumentsTyped stable child selected
      have packetArguments : Dynamic.ValuesHaveTypes port.principal.sourceFunction.context heap
          arguments packet.sourceAt.types := by
        simpa only [sourceAt] using argumentsTyped
      simpa only [CallableIndexedOwnedPreparedStagedMethodBodies.Packet.sourceAt, sourceAt] using
        CallableIndexedOwnedPreparedStagedMethodTerminalBounds.source_continuation
          port.principal packet static wellFormed functions selected installed
          owner keyPhysical caller heapTyped packetArguments stable budget
          (fun size smaller _context _invocation _scope _expression _lowered root owner physical =>
            children size smaller
              (CallableIndexedOwnedPreparedStagedPhysicalMixedRootStaticSupport.RootAt.ofMethod root) owner physical)

include keyPhysical wellFormed support in
theorem native_bodies (budget : Nat)
    (children : ∀ size, size < budget → ReflectsRootsAt (headers := headers) (keys := keys)
      model stages semanticFaults faults size) :
    CallableIndexedOwnedPreparedStagedCoercionPathBounds.NativeBodies
      (headers := headers) (receiving := receiving) owner functions faults chain budget := by
  induction chain with
  | nil => trivial
  | cons step port valid tail ih =>
      obtain ⟨⟨packet, sourceAt, static⟩, remaining⟩ := support
      refine ⟨?_, ih remaining⟩
      intro mapping world heap store callerScope canonical administrative arguments payloads caller installed
        _parameters heapTyped argumentsTyped stable child selected
      have packetArguments : Dynamic.ValuesHaveTypes port.principal.sourceFunction.context heap
          arguments packet.sourceAt.types := by
        simpa only [sourceAt] using argumentsTyped
      simpa only [CallableIndexedOwnedPreparedStagedMethodBodies.Packet.sourceAt, sourceAt] using
        CallableIndexedOwnedPreparedStagedMethodTerminalBounds.native_continuation
          port.principal packet static wellFormed functions selected installed
          owner keyPhysical caller heapTyped packetArguments stable budget
          (fun size smaller _context _invocation _scope _expression _lowered root owner physical =>
            children size smaller
              (CallableIndexedOwnedPreparedStagedPhysicalMixedRootStaticSupport.RootAt.ofMethod root) owner physical)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalCoercionMethodBounds
