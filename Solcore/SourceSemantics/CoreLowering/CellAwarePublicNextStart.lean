import Solcore.SourceSemantics.CoreLowering.CellAwarePublicSessionRegistry
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicReturnedValues
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicDataArgumentReceipts
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalFrontdoor
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalSessionState

/-! A later real public start uses the heap and function history returned by
previous execution. Input encoding determines its new receiving registry. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicNextStart
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys owner)
open CallableIndexedOwnedFunctionValues (Header)
open RecursiveNamedPublicPhysicalSessionState (StartedCall)
open RecursiveNamedPublicFunctionHistory (Entry)

variable {recipe : SourceCoreIndexedSession.Recipe}
  {inputs : List (Input recipe.compiled)} {rows : Inventory inputs}
  {prepared : SourceCoreIndexedSession.Recipe.prepare recipe.compiled = .ok recipe}
  {anchor header : Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
  {initial : CallableIndexedOwnedPublicFaultReceivers.Receiver recipe.compiled.indexed}
  {functions : FunctionModel recipe.compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions recipe.compiled.indexed)}
  {cells : CellAwarePublicCells.Family (CallableIndexedAmbient.ambientDefinitions recipe.compiled.indexed).definitions}
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {entries : List Entry}
  (state : CellAwarePublicSessionState.State rows functions cells anchor initial recipe session entries)
  {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
  {options : SourceCoreExecution.RunOptions} (call : StartedCall session key publicArguments options)

structure Started where
  checkpoint : SourceCoreIndexedSession.Checkpoint state.artifact
  root : SourceCoreIndexedSession.Root recipe.compiled
  payloads : Environment
  encodedValues : SourceCoreCompatibleValues.Context
  atCheckpoint : call.checkpoint.IndexedAt checkpoint
  started : RecursiveNamedPublicStartMeaning.StartAt state.session key publicArguments
    options.inputValidationFuel checkpoint recipe root state.world state.store payloads encodedValues
  selected : RecursiveNamedPublicRootMeaning.RootSelection
    (values := .initial recipe.compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions recipe.compiled.indexed)
    (program := Program.ofChecked recipe.compiled.sourceProgram) (headers rows) root header

include prepared in
/-- The returned history fixes the actual world and store of this new start.
Selection only concerns the original root chosen by the requested key. -/
theorem from_call
    (selectRoot : ∀ root : SourceCoreIndexedSession.Root recipe.compiled,
      recipe.roots.find? (fun candidate => decide (candidate.key = key)) = some root →
      RecursiveNamedPublicRootMeaning.RootSelection
        (values := .initial recipe.compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions recipe.compiled.indexed)
        (program := Program.ofChecked recipe.compiled.sourceProgram) (headers rows) root header) :
    Nonempty (Started (header := header) state call) := by
  obtain ⟨request, headerEq⟩ := RecursiveNamedPublicPhysicalFrontdoor.recover_start_at_with
    prepared inputs rows state.atRecipe state.history.semantic.current.1 state.atSession
    (fun _ actual => actual = header)
    (fun root selected => ⟨header, selectRoot root selected, rfl⟩) call.started
  exact ⟨⟨request.checkpoint, request.root, request.payloads, request.encodedValues,
    request.atCheckpoint, request.started, headerEq ▸ request.selected⟩⟩

structure Ready (start : Started (header := header) state call) (arguments : List Dynamic.Value) where
  receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver recipe.compiled.indexed
  contextAt : receiving.result.context = start.encodedValues
  issued : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt recipe.compiled.indexed receiving.entry
    receiving.result.context.registry receiving.result.extension receiving.result.diagnostics
  extension : SourceCoreRawMetadata.Extends initial.result.context.registry receiving.result.context.registry
  history : CellAwarePublicPhysicalHistory.History (headers := headers rows) (keys := keys recipe.compiled)
    (functions := functions) (cells := cells receiving.result.context.registry)
    (receiving := receiving.result.context.registry) (anchor := anchor)
    state.session state.mapping state.world state.heap state.store state.caller entries
  stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows state.caller
  globalReference : (SourceCoreCallableIndexedTemplates.globalEnvironment recipe.compiled.indexed)[header.slot]? =
    some (.cellRef (OptionalCell.cellType header.named.signature.functionType)
      ((owner recipe.compiled).key.locations header))
  heapTyped : Dynamic.HeapWellTyped header.function.context state.heap
  represented : CallableIndexedParameterMeaning.Arguments
    (CompatibleAmbientHeap.payloadModel recipe.compiled.compatible.checked receiving.result.context.registry functions)
    state.mapping state.world header.bindings arguments start.payloads
  argumentsTyped : Dynamic.ValuesHaveTypes header.function.context state.heap arguments header.types

/-- Metadata transport, current heap typing and data argument representation
follow from the real input encoder and the previously established history. -/
theorem of_started
    (covariant : CellAwarePublicCells.ExtendsRegistry cells)
    (bodyTyping : SelectedCompilationBodyTyping.Bodies recipe.compiled)
    (start : Started (header := header) state call)
    {arguments : List Dynamic.Value}
    (inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      header.function.context publicArguments header.types)
    (inputMeanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments) :
    Nonempty (Ready state call start arguments) := by
  obtain ⟨receiving, _member, contextAt, issued, extended, retained, _diagnostic⟩ :=
    CellAwarePublicActualRegistryStart.named_start covariant state.history.semantic state.registry start.started
  have metadata : SourceCoreRawMetadata.Extends start.encodedValues.registry receiving.result.context.registry := by
    rw [contextAt]
    exact .refl _
  obtain ⟨represented, argumentsTyped⟩ :=
    SelectedCompilationPublicDataArgumentReceipts.data_arguments_at_receiving functions
      receiving.result.context.registry state.mapping state.heap start.started start.selected rfl
      (SelectedCompilationHeaderCertificates.certified bodyTyping header) metadata inputTypes inputMeanings
  have globals := CallableIndexedOwnedPhysicalCanonicalState.ordinary_slots
    (owner recipe.compiled) (by intro _ _; rfl)
    (CallableIndexedOwnedPhysicalGlobals.environment_slots recipe.compiled) header start.selected.member
  simp only [CallableIndexedOwnedPhysicalGlobals.environment, List.length_nil, Nat.zero_add] at globals
  exact ⟨⟨receiving, contextAt, issued, state.extension.trans extended,
    ⟨retained, state.history.physical⟩, retained.current.2.2.1, globals,
    retained.current.2.2.2.1.transportContext
      (SelectedCompilationPublicReturnedValues.header_context_supports anchor header bodyTyping).1,
    represented, argumentsTyped⟩⟩

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicNextStart
