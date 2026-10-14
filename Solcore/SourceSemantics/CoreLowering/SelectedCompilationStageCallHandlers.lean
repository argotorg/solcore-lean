import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageCallerHeadHandlers
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageDirectLifting
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageIndirectLifting
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageNamedBodyLifting
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosurePacketRoots

/-! Actual static program support closes both ordinary call-head ports. The
only recursive input is lifting at strictly smaller ordinary trace grades;
staged preservation is supplied by the already closed physical family. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageCallHandlers
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedPublicFaultReceiverTables (IssuedAt)
open SelectedCompilationPhysicalProgramSupport (Support functions stages stagePrepared)
open SelectedCompilationStageLiftBounds (LiftsRootsAt preserves_roots)
open SelectedCompilationStageBodyLiftBounds (NamedLiftsBelow)
open CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds (Point)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {initial receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (support : Support compiled headers keys initial)
  (issued : IssuedAt compiled.indexed receiving.entry receiving.result.context.registry
    receiving.result.extension receiving.result.diagnostics)
  (extension : SourceCoreRawMetadata.Extends initial.result.context.registry receiving.result.context.registry)
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving.result.context.registry (functions support)
local notation "semanticFaults" => CallableIndexedOwnedPublicDecodedCallFaults.faults initial.result.diagnostics
local notation "faults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics

include support issued extension in
theorem named_bodies {budget : Nat}
    (children : ∀ size, size < budget → LiftsRootsAt (headers := headers) (keys := keys)
      model (stages compiled) semanticFaults size)
    (header : Header compiled (Program.ofChecked compiled.sourceProgram)) (member : header ∈ headers)
    {child : Staging.Recursive.Scope} (selected : (stages compiled).Closure header.function child) :
    NamedLiftsBelow (headers := headers) (keys := keys) header model (stages compiled) child budget := by
  exact SelectedCompilationStageNamedBodyLifting.lifts (semantic := SelectedCompilationPhysicalProgramSupport.semantic_extension support issued extension) (support.bodySupport header member)
    support.profile (support.certificates header member)
    (SelectedCompilationPhysicalProgramSupport.static_extension support extension) selected children
    (preserves_roots support issued extension)

private theorem named_descriptor (header : Header compiled (Program.ofChecked compiled.sourceProgram)) :
    Nonempty (SourceCoreCallableContracts.Descriptor compiled.indexed.ancestry.graph.inputs.callable.table
      (.named header.named.signature.key)) := by
  obtain ⟨origin, index, metadata, found, _history, _emitted⟩ :=
    CallableIndexedFormation.namedBody_history compiled.indexed.ancestry header.hook
  cases h : SourceCoreCallableContracts.descriptor compiled.indexed.ancestry.graph.inputs.callable.table
      (.named header.named.signature.key) with
  | error _ =>
    unfold SourceCoreCallableContracts.descriptor at h
    split at h
    · rename_i missing
      rw [found] at missing
      contradiction
    · contradiction
  | ok descriptor => exact ⟨descriptor⟩

variable {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
  {compilation : SourceCoreFunctions.Context} {readFuel : Nat}
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope}
  {expression : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {rawType : TypeSystem.Ty}
  (root : SelectedCompilationMixedRootSupport.Root compiled headers (stages compiled)
    policy lowerBody compilation readFuel context invocation reasonAt scope expression lowered rawType
      (CallableIndexedOwnedPublicDecodedCallFaults.faults initial.result.diagnostics))
  (owner : OwnedKey keys)
  (keyPhysical : CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)
local notation "callerBridge" => CallableIndexedOwnedPhysicalCanonicalState.ordinaryCaller owner compilation.administrativePrefix keyPhysical.locations
local notation "bridge" => CallableIndexedOwnedNamedCallerProtocol.Carrier.forgetSlots (callerBridge)

include support issued extension root owner keyPhysical in
theorem direct {budget : Nat}
    (children : ∀ size, size < budget → LiftsRootsAt (headers := headers) (keys := keys)
      model (stages compiled) semanticFaults size) :
    SelectedCompilationStageCallerHeadHandlers.Direct bridge model (stages compiled) faults budget root.certificate := by
  intro fuel current id callee ids instantiation code types compiler path calleeTyped application sequence
  obtain ⟨⟨port, certified, shaped⟩⟩ := root.directReady compiler path
  have rows := SelectedCompilationDirectSourceTypes.source_types
    compiler port.toReady shaped root.runtime.signatures application
  have ordered := rows.1 ▸ sequence
  constructor
  · intro size childPreservation
    exact SelectedCompilationPhysicalDirectBounds.preserves
      owner compiler port.toPort port.evidence callerBridge keyPhysical (fun state => state.physical)
      (functions support) faults root.unique support.bodyTyping.function_ids certified shaped root.runtime
      size ordered childPreservation
      (fun selected => SelectedCompilationPhysicalProgramSupport.preserves_bodies
        support issued extension port.header port.member selected size)
  · intro size within childLift childPreservation
    obtain ⟨descriptor⟩ := named_descriptor port.header
    obtain ⟨sidecar, _prepared, _same, selected, _declaration, _local, _evidence, _marker, _analysis⟩ :=
      CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts.selected port.sourceAt port.prepared port.aligned
        (stagePrepared compiled) descriptor
    rw [CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts.global_view port.sourceAt] at selected
    exact SelectedCompilationStageDirectLifting.direct
      owner compiler port.toPort port.evidence callerBridge keyPhysical (fun state => state.physical)
      (functions support) faults root.runtime.requirements.idsUnique root.unique support.bodyTyping.function_ids
      certified root.runtime selected size ordered childLift childPreservation
      (named_bodies support issued extension
        (fun smaller strict => children smaller (Nat.lt_of_lt_of_le strict within)) port.header port.member selected)

include support issued extension root owner keyPhysical in
theorem indirect {budget : Nat}
    (children : ∀ size, size < budget → LiftsRootsAt (headers := headers) (keys := keys)
      model (stages compiled) semanticFaults size) :
    SelectedCompilationStageCallerHeadHandlers.Indirect bridge model (stages compiled) faults budget root.certificate := by
  intro fuel current id callee ids metadata code types compiler path sequence
  obtain ⟨port⟩ := root.callsReady compiler path
  have calleeCertified : RecursiveStageTupleMeaning.Entries current compiler.entries
      current callee compiler.calleeCode := ⟨rfl, by simp [CallableIndirectCallCertificates.Receipt.entries]⟩
  constructor
  · intro size childPreservation
    exact SelectedCompilationPhysicalIndirectHeadBounds.preserves (semantic := SelectedCompilationPhysicalProgramSupport.semantic_extension support issued extension)
      bridge (fun state => state.physical) support.owners issued (stagePrepared compiled) rfl
      support.profile support.bodyTyping support.certificates root.runtime root.unique root.actualFunctionType
      (SelectedCompilationPhysicalProgramSupport.observations support) support.closurePackets support.closureSupport
      support.bodies compiler port calleeCertified sequence size childPreservation size
      (fun child _smaller => preserves_roots support issued extension child)
      (fun header member {_} selected => SelectedCompilationPhysicalProgramSupport.preserves_bodies
        support issued extension header member selected size) (Nat.le_refl _)
  · intro size within childLift childPreservation
    exact SelectedCompilationStageIndirectLifting.indirect support bridge (fun state => state.physical)
      compiler port root.runtime root.actualFunctionType root.unique size calleeCertified sequence
      childLift childPreservation
      (fun header member child selected => named_bodies support issued extension
        (fun smaller strict => children smaller (Nat.lt_of_lt_of_le strict within)) header member selected)
      (fun association => SelectedCompilationStageClosurePacketRoots.association_of_roots (semantic := SelectedCompilationPhysicalProgramSupport.semantic_extension support issued extension)
        (functions support) association.original (support.closurePackets association)
        (support.closureSupport association) support.owners
        (SelectedCompilationPhysicalProgramSupport.static_extension support extension)
        (fun smaller strict => children smaller (Nat.lt_of_lt_of_le strict within))
        (preserves_roots support issued extension))

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageCallHandlers
