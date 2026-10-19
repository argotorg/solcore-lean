import Solcore.SourceSemantics.CoreLowering.CellAwarePublicInitialArguments
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionInitial

/-! The actual bootstrap and public input encoding produce the initial mixed
heap, caller, diagnostic receiver and parameter representation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicInitialStart
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys owner)
open CallableIndexedOwnedFunctionValues (Header)
open SelectedCompilationPublicSessionState (StartedCall)
open SelectedCompilationPublicSessionInitial (Started)

variable {recipe : SourceCoreIndexedSession.Recipe}
  {inputs : List (Input recipe.compiled)} {rows : Inventory inputs}
  {prepared : SourceCoreIndexedSession.Recipe.prepare recipe.compiled = .ok recipe}
  {header : Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
  {options : SourceCoreExecution.RunOptions} {call : StartedCall session key publicArguments options}

/-- Actual public compilation and startup recover the same recipe and selected
root before any Source execution premise is introduced. -/
theorem from_call
    {seeds : List SourceCompiler.Seed} {compileOptions : SourceCompiler.Options}
    {publicCompiled : SourceCoreExecution.Compiled}
    (compiled : SourceCoreExecution.compileChecked recipe.compiled.sourceProgram seeds compileOptions = .ok publicCompiled)
    (selected : RecursiveNamedPreparedStageContracts.PublicRecipe publicCompiled recipe)
    (opened : artifact.CompiledAt publicCompiled)
    (bootstrap : SourceCoreExecution.Bootstrap artifact) {bootstrapFuel : Nat}
    (fresh : bootstrap.FreshAt) (authority : bootstrap.ExportAuthorityAt)
    (ready : bootstrap.ReadyAt bootstrapFuel session)
    (selectRoot : ∀ root ∈ recipe.roots, RecursiveNamedPublicRootMeaning.RootSelection
      (values := .initial recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions recipe.compiled.indexed)
      (program := Program.ofChecked recipe.compiled.sourceProgram) (headers rows) root header) :
    Nonempty (Started rows prepared header call) := by
  obtain ⟨actualRecipe, nativeArtifact, nativeSession, checkpoint, root, world, store, native,
      encodedValues, atArtifact, _prepared, _source, atSession, atCheckpoint, started⟩ :=
    RecursiveNamedPublicExecutionMeaning.actual_start compiled opened call.started
  have same : actualRecipe = recipe := by
    have actual := atArtifact.compiled_recipe
    cases publicCompiled
    exact Option.some.inj (actual.symm.trans selected)
  cases same
  exact ⟨{
    publicCompiled := publicCompiled, artifact := nativeArtifact, nativeSession := nativeSession,
    checkpoint := checkpoint, root := root, world := world, store := store, native := native,
    encodedValues := encodedValues, opened := atArtifact, atSession := atSession,
    atCheckpoint := atCheckpoint, started := started,
    selected := selectRoot root (List.mem_of_find?_eq_some started.selected),
    bootstrap := bootstrap, bootstrapFuel := bootstrapFuel, fresh := fresh,
    authority := authority, ready := ready }⟩

/-- A selected factory row supplies the receiver entry; the actual encoder
supplies its metadata. No body meaning or pre-existing receiver is required. -/
theorem receiver (start : Started rows prepared header call) :
    ∃ receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver recipe.compiled.indexed,
      receiving.result.context = start.encodedValues ∧
      CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt recipe.compiled.indexed receiving.entry
        receiving.result.context.registry receiving.result.extension receiving.result.diagnostics ∧
      SourceCoreRawMetadata.Extends recipe.compiled.compatible.checked.staticRegistry
        receiving.result.context.registry := by
  obtain ⟨entry, _member, _shape, _found⟩ := start.selected.2
  obtain ⟨receiving, _entry, contextAt, issued⟩ :=
    CallableIndexedOwnedPublicFaultReceivers.Receiver.at_context recipe.compiled entry
      start.encodedValues start.started.owner
  exact ⟨receiving, contextAt, issued, receiving.result.extension⟩

structure Ready
    (profile : recipe.compiled.compatible.checked.catalog.callableContracts = true)
    (bodyRegistry : SourceCoreRawMetadata.Registry) (semanticFaults : FunctionCalls.FaultRep)
    (start : Started rows prepared header call) (arguments : List Dynamic.Value) where
  receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver recipe.compiled.indexed
  contextAt : receiving.result.context = start.encodedValues
  issued : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt recipe.compiled.indexed receiving.entry
    receiving.result.context.registry receiving.result.extension receiving.result.diagnostics
  extension : SourceCoreRawMetadata.Extends recipe.compiled.compatible.checked.staticRegistry
    receiving.result.context.registry
  exportsReady : start.nativeSession.ExportsReady
  caller : (CallableIndexedOwnedPhysicalCanonicalState.protocol (headers rows) (keys recipe.compiled) 0).State
    ⟨[], [], start.world, ⟨[]⟩, start.store,
      SourceCoreCallableIndexedTemplates.globalEnvironment recipe.compiled.indexed⟩
  stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows caller.base.val
  globalReference : (SourceCoreCallableIndexedTemplates.globalEnvironment recipe.compiled.indexed)[header.slot]? =
    some (.cellRef (OptionalCell.cellType header.named.signature.functionType)
      ((owner recipe.compiled).key.locations header))
  keyPhysical : CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical (owner recipe.compiled).key (headers rows)
  heaps : GenericHeap.CellHeapRepresents
    (CellAwarePublicCells.generalized
      (CellAwarePhysicalFunctionOrigins.functions (headers rows) (keys recipe.compiled) bodyRegistry semanticFaults profile)
      (GeneralizedLocalInstanceValues.model recipe.compiled.indexed) receiving.result.context.registry)
    [] start.world ⟨[]⟩ start.store
  heapTyped : Dynamic.HeapWellTyped header.function.context ⟨[]⟩
  represented : CallableIndexedParameterMeaning.Arguments
    (CompatibleAmbientHeap.payloadModel recipe.compiled.compatible.checked receiving.result.context.registry
      (CellAwarePhysicalFunctionOrigins.functions (headers rows) (keys recipe.compiled) bodyRegistry semanticFaults profile))
    [] start.world header.bindings arguments start.native
  argumentsTyped : Dynamic.ValuesHaveTypes header.function.context ⟨[]⟩ arguments header.types

/-- These are consequences of the public bootstrap/start receipts and independent
input meanings. The selected-body typing interface remains narrower than a whole
program execution theorem. -/
theorem of_started
    (distinct : (inputs.map (fun input => input.prepared.index)).Nodup)
    (profile : recipe.compiled.compatible.checked.catalog.callableContracts = true)
    (bodyRegistry : SourceCoreRawMetadata.Registry) (semanticFaults : FunctionCalls.FaultRep)
    (bodyTyping : SelectedCompilationBodyTyping.Bodies recipe.compiled)
    (start : Started rows prepared header call)
    {arguments : List Dynamic.Value}
    (inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      header.function.context publicArguments header.types)
    (inputMeanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments) :
    Nonempty (Ready profile bodyRegistry semanticFaults start arguments) := by
  obtain ⟨receiving, contextAt, issued, extension⟩ := receiver start
  have metadata : SourceCoreRawMetadata.Extends start.encodedValues.registry receiving.result.context.registry := by
    rw [contextAt]
    exact .refl _
  obtain ⟨caller, stable, globalReference, heaps, heapTyped, represented, argumentsTyped⟩ :=
    CellAwarePublicInitialArguments.initial_data_arguments
      (inputs := inputs) (rows := rows) (distinct := distinct) (completion := receiving)
      (profile := profile) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (bodyTyping := bodyTyping) (prepared := prepared) (selected := start.selected)
      (opened := start.opened) (fresh := start.fresh) (ready := start.ready)
      (sameRuntime := SourceCoreExecution.Session.SameRuntime.refl session)
      (atSession := start.atSession) (started := start.started)
      (inputTypes := inputTypes) (inputMeanings := inputMeanings) (metadata := metadata)
  exact ⟨⟨receiving, contextAt, issued, extension,
    start.atSession.exportsReady_iff.mp (start.ready.exportsReady start.authority),
    caller, stable, globalReference,
    CallableIndexedOwnedPreparedPhysicalBootstrap.key_physical recipe.compiled (headers rows),
    heaps, heapTyped, represented, argumentsTyped⟩⟩

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicInitialStart
