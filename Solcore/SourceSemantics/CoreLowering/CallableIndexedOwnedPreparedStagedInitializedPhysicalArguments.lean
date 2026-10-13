import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodiesSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedBootstrapRootState
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicBootstrapInitialization
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicNestedArgumentsReceiving
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPhysicalBootstrap

/-! Actual bootstrap and original public input encoding construct the semantic
caller and every installed cache cell, including selected method closures. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedInitializedPhysicalArguments
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedPreparedBootstrapRootState (keys owner)
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)
open CallableIndexedOwnedPreparedStagedNamedBodies (Body)
open CallableIndexedOwnedPreparedStagedNamedBodiesSupport (Support)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (inputs : List (Input compiled)) (rows : Inventory inputs)
  (distinct : (inputs.map (fun input => input.prepared.index)).Nodup)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  {recipe : SourceCoreIndexedSession.Recipe}
  (prepared : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
  {root : SourceCoreIndexedSession.Root compiled}
  {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  (selected : RecursiveNamedPublicRootMeaning.RootSelection
    (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (program := Program.ofChecked compiled.sourceProgram) (headers rows) root header)
  {publicCompiled : SourceCoreExecution.Compiled} {publicArtifact : SourceCoreExecution.Artifact}
  {publicBootstrap : SourceCoreExecution.Bootstrap publicArtifact}
  {bootstrapSession publicSession : SourceCoreExecution.Session publicArtifact}
  {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
  {nativeArtifact : SourceCoreIndexedSession.Artifact}
  {nativeSession : SourceCoreIndexedSession.Session nativeArtifact}
  {nativeCheckpoint : SourceCoreIndexedSession.Checkpoint nativeArtifact}
  {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
  {bootstrapFuel : Nat} {options : SourceCoreExecution.RunOptions}
  {world : StoreTyping} {store : Store} {payloads : Environment}
  {encodedValues : SourceCoreCompatibleValues.Context}
  (opened : publicArtifact.IndexedAt publicCompiled recipe nativeArtifact)
  (fresh : publicBootstrap.FreshAt)
  (ready : publicBootstrap.ReadyAt bootstrapFuel bootstrapSession)
  (sameRuntime : bootstrapSession.SameRuntime publicSession)
  (atSession : publicSession.IndexedAt nativeSession)
  (atCheckpoint : publicCheckpoint.IndexedAt nativeCheckpoint)
  (started : RecursiveNamedPublicStartMeaning.StartAt nativeSession key publicArguments
    options.inputValidationFuel nativeCheckpoint recipe
    ((SourceCoreIndexedSession.Recipe.prepare_compiled prepared).symm ▸ root)
    world store payloads encodedValues)
  {arguments : List Dynamic.Value}
  (inputReceipts : RecursiveNamedPublicNestedInputs.Inputs rows nativeSession
    header.function.context (header.bindings.map (fun binding => binding.1.scheme.body))
    publicArguments arguments)
  (metadata : SourceCoreRawMetadata.Extends encodedValues.registry completion.result.context.registry)

local notation "rootHeaders" => headers rows
local notation "rootKeys" => keys compiled
local notation "rootOwner" => owner compiled
local notation "rootFunctions" => CallableIndexedOwnedContextualCellOrigins.functions rootHeaders rootKeys bodyRegistry semanticFaults profile
local notation "rootModel" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry rootFunctions
local notation "rootFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include distinct wellFormed prepared selected opened fresh ready sameRuntime atSession started inputReceipts metadata in
/-- This proof is consumed immediately by the public endpoints below. The
runtime-preservation receipt fixes the initial store/world; the argument producer uses
the caller's receiving metadata without identifying two registries. -/
theorem initial_arguments :
    ∃ caller : (CallableIndexedOwnedPhysicalCanonicalState.protocol rootHeaders rootKeys 0).State
        ⟨[], [], world, ⟨[]⟩, store, SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed⟩,
      CallableIndexedOwnedIndirectExpressionHeads.StableRows caller.base.val ∧
      (SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)[header.slot]? =
        some (.cellRef (OptionalCell.cellType header.named.signature.functionType)
          ((rootOwner).key.locations header)) ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked completion.result.context.registry
        rootFunctions [] world ⟨[]⟩ store ∧
      Dynamic.HeapWellTyped header.function.context ⟨[]⟩ ∧
      CallableIndexedParameterMeaning.Arguments rootModel [] world header.bindings arguments payloads ∧
      Dynamic.ValuesHaveTypes header.function.context ⟨[]⟩ arguments header.types := by
  have sameCompiled := SourceCoreIndexedSession.Recipe.prepare_compiled prepared
  cases sameCompiled
  obtain ⟨value, booted, worldEq, storeEq, _nativeAt, _registryAt, _initializedStart⟩ :=
    CallableIndexedOwnedPublicBootstrapInitialization.at_started prepared opened fresh ready sameRuntime atSession started
  subst world
  subst store
  obtain ⟨_result, _storeEq, caller, stable, heaps, globals, heapTyped⟩ :=
    CallableIndexedOwnedPreparedPhysicalBootstrap.of_completed wellFormed inputs rows prepared distinct
      (CallableIndexedOwnedContextualCellOrigins.functions (headers rows) (keys recipe.compiled)
        bodyRegistry semanticFaults profile) completion.result.context.registry booted
  obtain ⟨represented, argumentsTyped⟩ :=
    RecursiveNamedPublicNestedArgumentsReceiving.StartAt.nested_arguments_receiving
      prepared inputs rows bodyRegistry completion.result.context.registry semanticFaults profile
      caller.base.val started selected inputReceipts metadata wellFormed
  exact ⟨caller, stable, globals header selected.member, heaps,
    heapTyped header.function.context, represented, argumentsTyped⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedInitializedPhysicalArguments
