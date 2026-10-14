import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosureEntryLifting
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageImperativeLifting
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalBranchingLambdaBodyBounds

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosureScopedLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open SelectedCompilationStageBodyLiftBounds SelectedCompilationStageClosureEntryLifting
open SelectedCompilationStageLiftBounds (LiftsAt LiftsRootsAt)
open CallableIndexedOwnedAdmittedStagedExpressionBounds (PreservesAt)
open CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport (Branching parameterScope)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (code : Code compiled.indexed function scope administrative)
  (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry}
  {stages : Staging.Recursive.Registry} {child : Staging.Recursive.Scope}
  {semanticFaults : FunctionCalls.FaultRep} {faults : RecursiveStageMeaning.FaultRep}
  {packet : Branching code stages}
  (support : SelectedCompilationPhysicalBranchingClosureStaticSupport.SelectedBody headers code inputs stages packet semanticFaults)
  (selected : stages.Closure function child) (owner : OwnedKey keys)
  (ownerPhysical : CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions
local notation "physicalBridge" => CallableIndexedOwnedNamedCallerProtocol.Carrier.forgetSlots
  (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys) code.compilation.administrativePrefix)

variable (semantic : ∀ reason token, semanticFaults reason token → faults (.semantic reason) token)

include support selected ownerPhysical semantic in
theorem lifts
    (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry receiving)
    {budget : Nat}
    (children : ∀ size, size < budget → LiftsRootsAt (headers := headers) (keys := keys) model stages semanticFaults size)
    (preservation : ∀ size, SelectedCompilationMixedRootBounds.PreservesRootsAt
      (headers := headers) (keys := keys) model stages semanticFaults faults size) :
    EntryLiftsBelow (headers := headers) (keys := keys) code inputs model stages child budget := by
  intro mapping world environment canonical actual actualContext before store ξ contextLocation native
    environments heaps locals agrees actualTyped reference read unmapped conditioned initial admitted valid
    size finalContext outcome after trace within
  obtain ⟨sourceFinal, sourceFacts, sourceTyped, _sourceComplete⟩ :=
    CallableIndexedOwnedLambdaSourceAdmission.body_typed_at_parameters valid inputs.extended
  rw [← stages.source selected] at sourceTyped
  have originalTyping : ProtectedStateImperativeTypedSourceSites.Statements child.source inputs.context function.body :=
    ⟨_, _, _, sourceTyped⟩
  have tree := support.tree child selected
  have shape : CallableIndexedOwnedPreparedStagedBranchingTree.Shape child.source true function.body := by
    rw [stages.source selected]
    exact packet.shape
  have unique : NodeOccurrencesUnique child.source := by
    rw [stages.source selected]
    exact support.frame.code.graph.nodeOccurrencesUnique
  exact SelectedCompilationStageImperativeLifting.lifts_at
    physicalBridge
    (CallableIndexedOwnedPhysicalCanonicalState.bindings code.compilation.administrativePrefix)
    (CallableIndexedOwnedPhysicalCanonicalState.administrativeTransport code.compilation.administrativePrefix)
    functions extension rfl (CallableIndexedAmbient.frame_registered compiled.indexed)
    (CallableIndexedOwnedPhysicalCanonicalState.markedProducer model code.compilation.administrativePrefix)
    (CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (fun _ _ stable => CallableIndexedOwnedPhysicalCanonicalState.readyAt_of_stableOwner
      (headers := headers) model code.compilation.administrativePrefix stable)
    (fun context size smaller scope id lowered certified => by
      obtain ⟨rawType, root⟩ := certified
      exact children size smaller (SelectedCompilationMixedRootSupport.RootAt.ofRoot root) owner ownerPhysical ⟨rfl, rfl, rfl⟩)
    (fun context size scope id lowered certified => by
      obtain ⟨rawType, root⟩ := certified
      exact preservation size (SelectedCompilationMixedRootSupport.RootAt.ofRoot root) owner ownerPhysical ⟨rfl, rfl, rfl⟩)
    unique tree (support.sites child selected receiving) semantic rfl shape originalTyping support.projection within
    environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted trace

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosureScopedLifting
