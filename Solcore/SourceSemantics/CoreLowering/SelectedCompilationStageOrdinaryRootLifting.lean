import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageCallHandlers
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageMethodHeadHandlers
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageSharedCallerLifting

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageOrdinaryRootLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open SelectedCompilationPhysicalProgramSupport
open SelectedCompilationStageLiftBounds (LiftsAt LiftsRootsAt)

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
local notation "semanticFaults" => CallableIndexedOwnedPublicDecodedCallFaults.faults initial.result.diagnostics

include support issued extension root owner keyPhysical in
theorem lifts (budget : Nat)
    (children : ∀ size, size < budget → LiftsRootsAt (headers := headers) (keys := keys) model (stages compiled) semanticFaults size) :
    LiftsAt (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys)
      compilation.administrativePrefix).forgetSlots context model (stages compiled) invocation
      (CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.Point scope expression lowered) budget := by
  let callerBridge := CallableIndexedOwnedPhysicalCanonicalState.ordinaryCaller owner compilation.administrativePrefix keyPhysical.locations
  intro current id code point
  exact SelectedCompilationStageSharedCallerLifting.lifts_reached_with_functions
    callerBridge.forgetSlots issued (functions support) root.runtime root.unique
    (observations support) (static_extension support extension) (semantic_extension support issued extension)
    root.sameLedger root.runtimeLedger root.uninitialized budget root.certificate (.root (by simp))
    (SelectedCompilationStageCallHandlers.direct support issued extension root owner keyPhysical children)
    (SelectedCompilationStageMethodHeadHandlers.method support issued extension root owner keyPhysical children)
    root.indexReady
    (SelectedCompilationStageCallHandlers.indirect support issued extension root owner keyPhysical children)
    budget (Nat.le_refl _) point

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageOrdinaryRootLifting
