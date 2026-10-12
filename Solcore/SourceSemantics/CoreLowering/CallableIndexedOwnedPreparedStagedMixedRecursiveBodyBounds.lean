import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodySupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedRecursiveCallerBounds

/-! Strong numeric recursion closes chosen mixed closure bodies. The same
pool-zero RootAt target and original call authority are reused. Static mixed
packets cover actual Associations; named bodies retain their terminal support.
Structural caller recursion handles equal native group and singleton grades. -/
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
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)
open CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport (NamedSupport)
open CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds (PreservesRootsAt ReflectsRootsAt)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : SourceCoreCallableIndexedPrograms.Completion compiled.indexed}
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
  (namedTerminals : ∀ header, header ∈ headers → Terminal header)
  (namedSupport : ∀ header (member : header ∈ headers),
    CallableIndexedOwnedPreparedStagedNamedBodySupport.Support headers keys bodyRegistry
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

include closurePackets closureSupport namedTerminals namedSupport receiver stagePrepared observations extension semantic in
/-- Each called first/tail expression consumes a genuinely smaller numeric Root.
The static packet retains all actual Source selections; no execution law enters. -/
theorem preserves (size : Nat) :
    PreservesRootsAt (completion := completion) (stages := stages) (headers := headers) (keys := keys)
      (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile size := by
  induction size using Nat.strongRecOn with
  | ind size ih =>
    intro context invocation scope expression lowered root
    exact CallableIndexedOwnedPreparedStagedMixedRecursiveCallerBounds.preserves
      poolBridge receiver stagePrepared profile root.support.wellFormed root.support.runtime
      root.support.covers root.support.unique root.support.actualFunctionType observations
      extension semantic closurePackets closureSupport namedTerminals root.support.sameLedger
      root.support.runtimeLedger root.support.uninitialized size ih
      (fun childSize within =>
        CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.named_preserves_below
          namedTerminals namedSupport ih within)
      root.support.certificate root.support.callsReady size (Nat.le_refl _)

include closurePackets closureSupport namedTerminals namedSupport receiver stagePrepared observations extension semantic in
/-- Only called-body evaluation decreases numerically. Structural group and
singleton tuple reflection retain their honest equal-grade child behavior. -/
theorem reflects (stageEq : stages = RecursiveNamedPreparedStageScopes.registry stagePrepared)
    (size : Nat) :
    ReflectsRootsAt (completion := completion) (stages := stages) (headers := headers) (keys := keys)
      (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile size := by
  induction size using Nat.strongRecOn with
  | ind size ih =>
    intro context invocation scope expression lowered root
    exact CallableIndexedOwnedPreparedStagedMixedRecursiveCallerBounds.reflects
      poolBridge receiver stagePrepared profile root.support.wellFormed root.support.runtime
      root.support.covers root.support.unique root.support.actualFunctionType observations
      extension semantic closurePackets closureSupport namedTerminals root.support.sameLedger
      root.support.runtimeLedger root.support.uninitialized stageEq size ih
      (fun childSize within =>
        CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.named_reflects_below
          namedTerminals namedSupport ih within)
      root.support.certificate root.support.callsReady size (Nat.le_refl _)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedRecursiveBodyBounds
