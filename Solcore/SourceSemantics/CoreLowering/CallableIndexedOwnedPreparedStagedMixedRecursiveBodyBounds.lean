import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCanonicalRecursiveCallerBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodiesSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedRecursiveCallerBounds

/-! Simultaneous numeric recursion closes pool and canonical caller roots.
Actual named parameter packets supply canonical slots, while existing closure
packets retain their original pool support. Every called body consumes a
strictly smaller grade; structural children retain their independent bounds. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedRecursiveBodyBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedPublicFaultReceiverTables (IssuedAt)
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)
open CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport (PacketFor SupportFor)
open CallableIndexedOwnedPreparedStagedNamedBodies (Body)
open CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport (NamedSupport)
open CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds (PreservesRootsAt ReflectsRootsAt)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {stages : Staging.Recursive.Registry}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (closurePackets : ∀ {mapping world function native bindings parameterCore resultCore}
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore), PacketFor association stages)
  (closureSupport : ∀ {mapping world function native bindings parameterCore resultCore}
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore), SupportFor association stages (closurePackets association))
  (namedTerminals : ∀ header, header ∈ headers → Body header)
  (namedSupport : ∀ header (member : header ∈ headers),
    CallableIndexedOwnedPreparedStagedNamedBodiesSupport.Support headers keys bodyRegistry
      header stages (namedTerminals header member) semanticFaults)
  (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
    completion.result.extension completion.result.diagnostics)
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile) identities)
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry
    completion.result.context.registry)
  (semantic : ∀ reason token, semanticFaults reason token →
    CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token)

local notation "poolBridge" => CallableIndexedOwnedBodyRestorationAdmission.bridge
  (compiled := compiled) (program := Program.ofChecked compiled.sourceProgram) (headers := headers) (keys := keys)

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys
  bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked
  completion.result.context.registry functions
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
  completion.result.diagnostics

include closurePackets closureSupport namedTerminals namedSupport receiver stagePrepared observations extension semantic in
theorem preserves_both (size : Nat) :
    PreservesRootsAt (completion := completion) (stages := stages) (headers := headers) (keys := keys)
      (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile size ∧
    CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport.PreservesRootsAt
      (headers := headers) (keys := keys) model stages semanticFaults callFaults size := by
  induction size using Nat.strongRecOn with
  | ind size ih =>
    constructor
    · intro context invocation scope expression lowered root
      exact CallableIndexedOwnedPreparedStagedMixedRecursiveCallerBounds.preserves_reached
        poolBridge receiver stagePrepared profile root.support.wellFormed root.support.runtime
        root.support.covers root.support.unique root.support.actualFunctionType observations
        extension semantic closurePackets closureSupport namedTerminals root.support.sameLedger
        root.support.runtimeLedger root.support.uninitialized size
        (fun childSize smaller => (ih childSize smaller).1)
        (fun childSize smaller => (ih childSize smaller).2)
        (fun childSize within named member {_child} selected =>
          CallableIndexedOwnedPreparedStagedNamedBodiesSupport.Support.preserves (semantic := semantic)
            (namedSupport named member) profile root.support.wellFormed selected extension
            (fun smaller strict => (ih smaller (Nat.lt_of_lt_of_le strict within)).1)
            (fun smaller strict => (ih smaller (Nat.lt_of_lt_of_le strict within)).2))
        root.support.certificate (.root (by simp)) root.support.noMethods root.support.noDirect root.support.noIndexes
        root.support.callsReady size (Nat.le_refl _)
    · intro context invocation scope expression lowered root owner caller callerBridge
      exact CallableIndexedOwnedPreparedStagedCanonicalRecursiveCallerBounds.preserves_reached
        owner callerBridge receiver stagePrepared profile root.support.wellFormed root.support.runtime
        root.support.covers root.support.unique root.support.actualFunctionType observations
        extension semantic closurePackets closureSupport namedTerminals root.support.sameLedger
        root.support.runtimeLedger root.support.uninitialized size
        (fun childSize smaller => (ih childSize smaller).1)
        (fun childSize smaller => (ih childSize smaller).2)
        (fun childSize within named member {_child} selected =>
          CallableIndexedOwnedPreparedStagedNamedBodiesSupport.Support.preserves (semantic := semantic)
            (namedSupport named member) profile root.support.wellFormed selected extension
            (fun smaller strict => (ih smaller (Nat.lt_of_lt_of_le strict within)).1)
            (fun smaller strict => (ih smaller (Nat.lt_of_lt_of_le strict within)).2))
        root.support.certificate (.root (by simp)) root.support.noMethods root.support.directReady root.support.indexReady
        root.support.callsReady size (Nat.le_refl _)

include closurePackets closureSupport namedTerminals namedSupport receiver stagePrepared observations extension semantic in
theorem preserves (size : Nat) :
    PreservesRootsAt (completion := completion) (stages := stages) (headers := headers) (keys := keys)
      (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile size :=
  (preserves_both profile closurePackets closureSupport namedTerminals namedSupport receiver stagePrepared observations extension semantic size).1

include closurePackets closureSupport namedTerminals namedSupport receiver stagePrepared observations extension semantic in
theorem preserves_canonical (size : Nat) :
    CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport.PreservesRootsAt
      (headers := headers) (keys := keys) model stages semanticFaults callFaults size :=
  (preserves_both profile closurePackets closureSupport namedTerminals namedSupport receiver stagePrepared observations extension semantic size).2

include closurePackets closureSupport namedTerminals namedSupport receiver stagePrepared observations extension semantic in
theorem reflects_both (stageEq : stages = RecursiveNamedPreparedStageScopes.registry stagePrepared) (size : Nat) :
    ReflectsRootsAt (completion := completion) (stages := stages) (headers := headers) (keys := keys)
      (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile size ∧
    CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport.ReflectsRootsAt
      (headers := headers) (keys := keys) model stages semanticFaults callFaults size := by
  induction size using Nat.strongRecOn with
  | ind size ih =>
    constructor
    · intro context invocation scope expression lowered root
      exact CallableIndexedOwnedPreparedStagedMixedRecursiveCallerBounds.reflects_reached
        poolBridge receiver stagePrepared profile root.support.wellFormed root.support.runtime
        root.support.covers root.support.unique root.support.actualFunctionType observations
        extension semantic closurePackets closureSupport namedTerminals root.support.sameLedger
        root.support.runtimeLedger root.support.uninitialized stageEq size
        (fun childSize smaller => (ih childSize smaller).1)
        (fun childSize smaller => (ih childSize smaller).2)
        (fun childSize within named member {_child} selected =>
          CallableIndexedOwnedPreparedStagedNamedBodiesSupport.Support.reflects (semantic := semantic)
            (namedSupport named member) profile root.support.wellFormed selected extension
            (fun smaller strict => (ih smaller (Nat.lt_of_lt_of_le strict within)).1)
            (fun smaller strict => (ih smaller (Nat.lt_of_lt_of_le strict within)).2))
        root.support.certificate (.root (by simp)) root.support.noMethods root.support.noDirect root.support.noIndexes
        root.support.callsReady size (Nat.le_refl _)
    · intro context invocation scope expression lowered root owner caller callerBridge
      exact CallableIndexedOwnedPreparedStagedCanonicalRecursiveCallerBounds.reflects_reached
        owner callerBridge receiver stagePrepared profile root.support.wellFormed root.support.runtime
        root.support.covers root.support.unique root.support.actualFunctionType observations
        extension semantic closurePackets closureSupport namedTerminals root.support.sameLedger
        root.support.runtimeLedger root.support.uninitialized stageEq size
        (fun childSize smaller => (ih childSize smaller).1)
        (fun childSize smaller => (ih childSize smaller).2)
        (fun childSize within named member {_child} selected =>
          CallableIndexedOwnedPreparedStagedNamedBodiesSupport.Support.reflects (semantic := semantic)
            (namedSupport named member) profile root.support.wellFormed selected extension
            (fun smaller strict => (ih smaller (Nat.lt_of_lt_of_le strict within)).1)
            (fun smaller strict => (ih smaller (Nat.lt_of_lt_of_le strict within)).2))
        root.support.certificate (.root (by simp)) root.support.noMethods root.support.directReady root.support.indexReady
        root.support.callsReady size (Nat.le_refl _)

include closurePackets closureSupport namedTerminals namedSupport receiver stagePrepared observations extension semantic in
theorem reflects (stageEq : stages = RecursiveNamedPreparedStageScopes.registry stagePrepared) (size : Nat) :
    ReflectsRootsAt (completion := completion) (stages := stages) (headers := headers) (keys := keys)
      (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile size :=
  (reflects_both profile closurePackets closureSupport namedTerminals namedSupport receiver stagePrepared observations extension semantic stageEq size).1

include closurePackets closureSupport namedTerminals namedSupport receiver stagePrepared observations extension semantic in
theorem reflects_canonical (stageEq : stages = RecursiveNamedPreparedStageScopes.registry stagePrepared) (size : Nat) :
    CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport.ReflectsRootsAt
      (headers := headers) (keys := keys) model stages semanticFaults callFaults size :=
  (reflects_both profile closurePackets closureSupport namedTerminals namedSupport receiver stagePrepared observations extension semantic stageEq size).2

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedRecursiveBodyBounds
