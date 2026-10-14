import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageMethodLifting
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageLiftConstructors
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageMethodBodyLifting
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageCallerHeadHandlers

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageMethodHeadHandlers
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open SelectedCompilationPhysicalProgramSupport
open SelectedCompilationStageLiftBounds (LiftsRootsAt preserves_roots)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {initial receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (support : Support compiled headers keys initial)
  (issued : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed receiving.entry
    receiving.result.context.registry receiving.result.extension receiving.result.diagnostics)
  (extension : SourceCoreRawMetadata.Extends initial.result.context.registry receiving.result.context.registry)
  {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
  {compilation : SourceCoreFunctions.Context} {readFuel : Nat}
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope}
  {expression : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {rawType : TypeSystem.Ty}
  (root : SelectedCompilationMixedRootSupport.Root compiled headers (stages compiled) policy lowerBody compilation readFuel
    context invocation reasonAt scope expression lowered rawType
    (CallableIndexedOwnedPublicDecodedCallFaults.faults initial.result.diagnostics))
  (owner : OwnedKey keys)
  (keyPhysical : CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving.result.context.registry (functions support)
local notation "faults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics
local notation "semanticFaults" => CallableIndexedOwnedPublicDecodedCallFaults.faults initial.result.diagnostics
local notation "callerBridge" => CallableIndexedOwnedPhysicalCanonicalState.ordinaryCaller owner compilation.administrativePrefix keyPhysical.locations

include issued extension in
theorem method {budget : Nat}
    (children : ∀ size, size < budget → LiftsRootsAt (headers := headers) (keys := keys) model (stages compiled) semanticFaults size) :
    SelectedCompilationStageCallerHeadHandlers.Method (callerBridge).forgetSlots model (stages compiled) faults budget root.certificate := by
  intro fuel current id code types compiler path sequence
  obtain ⟨⟨port, selection⟩⟩ := root.methodReady compiler path
  obtain ⟨packet, sourceAtEq, static⟩ := support.methods compiler port selection
  have certified := SelectedCompilationMethodBodySupport.Certified.of_typed port.principal packet.sourceAt selection
  constructor
  · intro size childMeaning
    have bodies : SelectedCompilationMethodHeadBounds.SourceBodies
        (headers := headers) (receiving := receiving.result.context.registry) owner compiler port (functions support) faults size := by
      intro mapping world heap store callerScope canonical administrative arguments payloads caller installed _parameters
        heapTyped argumentsTyped stable child selected
      have packetArguments : Dynamic.ValuesHaveTypes port.principal.sourceFunction.context heap arguments packet.sourceAt.types := by
        simpa only [sourceAtEq] using argumentsTyped
      simpa only [sourceAtEq] using
        SelectedCompilationMethodBodyBounds.source_continuation
          port.principal packet static certified (functions support) selected installed owner keyPhysical caller
          heapTyped packetArguments stable (static_extension support extension) size
          (fun smaller _ => preserves_roots support issued extension smaller)
    intro actualScope actualId actualCode point actual found typed
    obtain ⟨rfl, rfl, rfl⟩ := point
    cases Option.some.inj (found.symm.trans compiler.metadata.found)
    have rows := SelectedCompilationMethodArgumentRows.raw_types compiler port
      root.catalog selection root.runtime root.unique typed
    have ordered := SelectedCompilationStageLiftConstructors.tree_types sequence root.unique rows.1 ▸ sequence
    intro mapping world administrativeContext environment canonical actualEnvironment actualContext before store ξ outcome after
    exact SelectedCompilationMethodHeadBounds.preserves
      owner compiler port callerBridge keyPhysical.frame (fun state => state.physical)
      (fun state => state.base.property) (functions support) faults root.unique root.catalog selection
      root.runtime size ordered childMeaning bodies ⟨rfl, rfl, rfl⟩ found typed
  · intro size within childLift preservation
    have bodies : SelectedCompilationStageMethodLifting.BodyLifts
        (headers := headers) (receiving := receiving.result.context.registry) owner compiler port (functions support) size := by
      intro mapping world heap store callerScope canonical administrative arguments payloads caller installed _parameters
        heapTyped argumentsTyped stable child selected
      have packetArguments : Dynamic.ValuesHaveTypes port.principal.sourceFunction.context heap arguments packet.sourceAt.types := by
        simpa only [sourceAtEq] using argumentsTyped
      simpa only [sourceAtEq] using
        SelectedCompilationStageMethodBodyLifting.source_continuation
          port.principal packet static certified (functions support) selected installed owner keyPhysical caller
          heapTyped packetArguments stable (static_extension support extension) size
          (fun smaller strict => children smaller (Nat.lt_of_lt_of_le strict within))
          (fun grade => preserves_roots support issued extension grade)
    intro actualScope actualId actualCode point actual found typed
    obtain ⟨rfl, rfl, rfl⟩ := point
    cases Option.some.inj (found.symm.trans compiler.metadata.found)
    have rows := SelectedCompilationMethodArgumentRows.raw_types compiler port
      root.catalog selection root.runtime root.unique typed
    have ordered := SelectedCompilationStageLiftConstructors.tree_types sequence root.unique rows.1 ▸ sequence
    intro mapping world administrativeContext environment canonical actualEnvironment actualContext before store ξ outcome after
    exact SelectedCompilationStageMethodLifting.method
      owner compiler port callerBridge keyPhysical.frame (fun state => state.physical)
      (fun state => state.base.property) (functions support) faults root.unique root.catalog selection
      root.runtime size ordered childLift preservation bodies ⟨rfl, rfl, rfl⟩ found typed

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageMethodHeadHandlers
