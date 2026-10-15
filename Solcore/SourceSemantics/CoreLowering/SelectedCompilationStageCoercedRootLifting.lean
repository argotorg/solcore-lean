import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageRawDirectLifting
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageCoercedExpressionLifting
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageNamedBodyLifting
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStagePhysicalCoercionMethods
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalCoercedDirectRawBounds

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageCoercedRootLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedPublicFaultReceiverTables (IssuedAt)
open SelectedCompilationPhysicalProgramSupport
open SelectedCompilationStageLiftBounds
open SelectedCompilationStageBodyLiftBounds (NamedLiftsBelow)

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
private theorem named_bodies {budget : Nat}
    (children : ∀ size, size < budget → LiftsRootsAt (headers := headers) (keys := keys)
      model (stages compiled) semanticFaults size)
    (header : Header compiled (Program.ofChecked compiled.sourceProgram)) (member : header ∈ headers)
    {child : Staging.Recursive.Scope} (selected : (stages compiled).Closure header.function child) :
    NamedLiftsBelow (headers := headers) (keys := keys) header model (stages compiled) child budget := by
  exact SelectedCompilationStageNamedBodyLifting.lifts (assignmentInterpretation := SelectedCompilationPhysicalProgramSupport.assignment_interpretation (compiled := compiled) issued) (semantic := SelectedCompilationPhysicalProgramSupport.semantic_extension support issued extension) (support.bodySupport header member)
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
  (root : SelectedCompilationMixedRootSupport.CoercedDirectRoot compiled headers (stages compiled)
    policy lowerBody compilation readFuel context invocation reasonAt scope expression lowered rawType
      (CallableIndexedOwnedPublicDecodedCallFaults.faults initial.result.diagnostics))
  (owner : OwnedKey keys)
  (keyPhysical : CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)
local notation "callerBridge" => CallableIndexedOwnedPhysicalCanonicalState.ordinaryCaller owner compilation.administrativePrefix keyPhysical.locations
local notation "bridge" => CallableIndexedOwnedNamedCallerProtocol.Carrier.forgetSlots callerBridge

include support issued extension root owner keyPhysical in
theorem lifts (budget : Nat)
    (children : ∀ size, size < budget → LiftsRootsAt (headers := headers) (keys := keys)
      model (stages compiled) semanticFaults size) :
    LiftsAt bridge context model (stages compiled) invocation
      (CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.Point scope expression lowered) budget := by
  intro current id code point actual found typed mapping world administrativeContext environment canonical actualEnvironment
    actualContext before store ξ outcome after environments heaps locals agrees actualTyped initialState admitted trace
  obtain ⟨rfl, rfl, rfl⟩ := point
  cases Option.some.inj (found.symm.trans root.actual.found)
  obtain ⟨types, _callee, application, argumentTyping⟩ :=
    CallableIndexedOwnedPreparedStagedRawDirectArguments.source_types root.actual root.unique typed
  have rows := SelectedCompilationRawDirectSourceTypes.source_types root.actual root.port.toReady root.shape root.runtime.signatures application
  have argumentTypes := (SelectedCompilationStageLiftConstructors.tree_types root.argumentTree root.unique argumentTyping).trans rows.1
  have ordered := argumentTypes ▸ root.argumentTree
  have preservation := preserves_roots support issued extension
  have rawPreservation := SelectedCompilationPhysicalCoercedDirectRawBounds.preserves
    (receiving := receiving.result.context.registry)
    root support.bodyTyping.function_ids owner keyPhysical (functions support) faults
  have rawAll (size : Nat) : SelectedCompilationPhysicalRawDirectBounds.RawPreservesAt
      (context := context) (receiving := receiving.result.context.registry) owner root.actual callerBridge
      (functions support) faults (stages compiled) size := by
    exact rawPreservation size (fun child _ => preservation child)
      (fun grade _ {_} selected => SelectedCompilationPhysicalProgramSupport.preserves_bodies
        support issued extension root.port.header root.port.member selected grade) size (Nat.le_refl _)
  have paths := SelectedCompilationStagePhysicalCoercionMethods.lift_bodies
    owner keyPhysical (functions support)
    root.chain root.methods budget children
  have pathsPreserved (size : Nat) := SelectedCompilationPhysicalCoercionMethodBounds.source_bodies
    owner keyPhysical (functions support) faults
    root.chain root.methods size (fun child _ => preservation child)
  apply SelectedCompilationStageCoercedExpressionLifting.lifts
    owner root.actual callerBridge (fun state => state.physical) (fun state => state.base.property)
    keyPhysical.frame (functions support) faults root.chain root.nonempty root.unique root.runtime root.ledger typed
    environments heaps locals agrees actualTyped initialState admitted budget
    ?_ rawAll paths pathsPreserved trace (Nat.le_refl _)
  intro size plain after raw within
  obtain ⟨descriptor⟩ := named_descriptor root.port.header
  obtain ⟨sidecar, _prepared, _same, selected, _declaration, _local, _evidence, _marker, _analysis⟩ :=
    CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts.selected root.port.sourceAt root.port.prepared root.port.aligned
      (stagePrepared compiled) descriptor
  rw [CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts.global_view root.port.sourceAt] at selected
  have childLifts : ∀ smaller, smaller < size → LiftsAt bridge context model (stages compiled) invocation root.argumentCertificate smaller := by
    intro smaller strict current id code member
    obtain ⟨type, ⟨supported⟩⟩ := root.argumentRoots member
    exact children smaller (Nat.lt_of_lt_of_le strict within)
      (SelectedCompilationMixedRootSupport.RootAt.ofRoot supported) owner keyPhysical ⟨rfl, rfl, rfl⟩
  have childPreservation : ∀ grade, CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesAt
      bridge context model (stages compiled) invocation root.argumentCertificate faults grade := by
    intro grade current id code member
    obtain ⟨type, ⟨supported⟩⟩ := root.argumentRoots member
    exact preservation grade (SelectedCompilationMixedRootSupport.RootAt.ofRoot supported) owner keyPhysical ⟨rfl, rfl, rfl⟩
  exact SelectedCompilationStageRawDirectLifting.raw_direct
    owner root.actual root.port.toPort root.port.evidence callerBridge keyPhysical (fun state => state.physical)
    (functions support) faults root.unique support.bodyTyping.function_ids root.certified root.shape root.runtime
    selected size ordered childLifts childPreservation
    (named_bodies support issued extension (fun smaller strict => children smaller (Nat.lt_of_lt_of_le strict within))
      root.port.header root.port.member selected)
    (fun _ fault => SelectedCompilationStageRawDirectSource.requirements_safe root.chain
      root.runtimeLedger.idsUnique root.port.evidence.produces fault)
    typed environments heaps locals agrees actualTyped initialState admitted raw

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageCoercedRootLifting
