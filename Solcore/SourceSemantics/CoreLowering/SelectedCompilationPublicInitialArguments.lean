import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalBootstrap
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicDataArgumentReceipts
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationHeaderCertificates
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodiesSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedBootstrapRootState
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicBootstrapInitialization
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDataArgumentReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalCellOrigins
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPhysicalBootstrap

/-! Actual bootstrap and original public data encoding construct the positive
closure model and every installed cache cell, including selected method closures. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicInitialArguments
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
  (bodyTyping : SelectedCompilationBodyTyping.Bodies compiled)
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
  (inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
    header.function.context publicArguments header.types)
  (inputMeanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments)
  (metadata : SourceCoreRawMetadata.Extends encodedValues.registry completion.result.context.registry)

local notation "rootHeaders" => headers rows
local notation "rootKeys" => keys compiled
local notation "rootOwner" => owner compiled
local notation "rootFunctions" => CallableIndexedOwnedPhysicalCellOrigins.functions rootHeaders rootKeys bodyRegistry semanticFaults profile
local notation "rootModel" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry rootFunctions
local notation "rootFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include distinct bodyTyping prepared selected opened fresh ready sameRuntime atSession started inputTypes inputMeanings metadata in
/-- This proof is consumed immediately by the public endpoints below. The
runtime-preservation receipt fixes the initial store/world; the argument producer uses
the caller's receiving metadata without identifying two registries. -/
theorem initial_data_arguments :
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
    SelectedCompilationPhysicalBootstrap.of_completed bodyTyping inputs rows prepared distinct
      (CallableIndexedOwnedPhysicalCellOrigins.functions (headers rows) (keys recipe.compiled)
        bodyRegistry semanticFaults profile) completion.result.context.registry booted
  obtain ⟨represented, argumentsTyped⟩ :=
    SelectedCompilationPublicDataArgumentReceipts.data_arguments_at_receiving
      (CallableIndexedOwnedPhysicalCellOrigins.functions (headers rows) (keys recipe.compiled)
        bodyRegistry semanticFaults profile) completion.result.context.registry [] ⟨[]⟩
      started selected rfl (SelectedCompilationHeaderCertificates.certified bodyTyping header) metadata inputTypes inputMeanings
  exact ⟨caller, stable, globals header selected.member, heaps,
    heapTyped header.function.context, represented, argumentsTyped⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicInitialArguments
