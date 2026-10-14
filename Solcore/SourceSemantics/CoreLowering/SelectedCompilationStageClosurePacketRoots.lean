import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosurePacketLifting
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosureScopedLifting

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosurePacketRoots
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open SelectedCompilationPhysicalClosureStaticSupport (Packet PacketFor SupportFor)
open SelectedCompilationStageClosurePacketLifting (PacketBelow BelowFor)
open SelectedCompilationStageLiftBounds (LiftsRootsAt)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (code : Code compiled.indexed function scope administrative)
  (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry} {stages : Staging.Recursive.Registry}
  {semanticFaults : FunctionCalls.FaultRep} {faults : RecursiveStageMeaning.FaultRep}
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions

 theorem packet_of_roots (packet : Packet code stages)
    (support : SelectedCompilationPhysicalClosureStaticSupport.Support (headers := headers) code inputs stages packet semanticFaults)
    (owner : OwnedKey keys)
    (ownerPhysical : CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)
    (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry receiving)
    {budget : Nat}
    (children : ∀ size, size < budget → LiftsRootsAt (headers := headers) (keys := keys) model stages semanticFaults size)
    (preservation : ∀ size, SelectedCompilationMixedRootBounds.PreservesRootsAt
      (headers := headers) (keys := keys) model stages semanticFaults faults size) :
    PacketBelow (headers := headers) (keys := keys) code inputs model stages packet budget := by
  cases packet with
  | terminal terminal =>
    exact SelectedCompilationStageClosureEntryLifting.of_general code inputs model stages terminal.child
      (SelectedCompilationStageClosureBodyLifting.terminal code inputs model stages terminal.child
        support terminal.selected owner ownerPhysical children)
  | branching branching =>
    exact SelectedCompilationStageClosureScopedLifting.lifts code inputs functions support
      branching.selected owner ownerPhysical extension children preservation

section Association
variable {bodyRegistry : SourceCoreRawMetadata.Registry}
  {mapping : LocationMap} {world : StoreTyping} {native : Value}
  {bindings : List CallableIndexedParameterCertificates.Binding} {parameter result : Ty}

 theorem association_of_roots
    (association : CallableIndexedOwnedContextualTypedClosureReceipts.Association headers keys
      bodyRegistry semanticFaults mapping world function native bindings parameter result)
    (packet : PacketFor association stages)
    (support : SupportFor association stages packet)
    (owners : ∀ owner : OwnedKey keys, CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)
    (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry receiving)
    {budget : Nat}
    (children : ∀ size, size < budget → LiftsRootsAt (headers := headers) (keys := keys) model stages semanticFaults size)
    (preservation : ∀ size, SelectedCompilationMixedRootBounds.PreservesRootsAt
      (headers := headers) (keys := keys) model stages semanticFaults faults size) :
    BelowFor model stages association packet budget := by
  cases association with
  | ordinary owner captured code history body origin prefixContext globals referenceIndex typed provenance =>
    exact packet_of_roots code body.body.toContext functions packet support owner (owners owner)
      extension children preservation
  | principal owner captured code history body origin globals leading referenceIndex typed provenance =>
    exact packet_of_roots code body.body.toContext functions packet support owner (owners owner)
      extension children preservation
end Association
end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosurePacketRoots
