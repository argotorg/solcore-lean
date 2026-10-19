import Solcore.SourceSemantics.CoreLowering.CellAwarePublicSessionRegistry
import Solcore.SourceSemantics.CoreLowering.CellAwarePhysicalFunctionOrigins
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalInstanceValues

/-! The selected session fixes its actual positive function model and authentic
compiler-instance descriptor cells. Registry transport is derived internally. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareSelectedPublicSessionState
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open CallableIndexedOwnedFunctionValues (Header)
open RecursiveNamedPublicFunctionHistory (Entry)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {inputs : List (Input compiled)}

def functions (rows : Inventory inputs)
    (initial : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :=
  CellAwarePhysicalFunctionOrigins.functions (headers rows) (keys compiled)
    initial.result.context.registry
    (CallableIndexedOwnedPublicDecodedCallFaults.faults initial.result.diagnostics) profile

def cells (rows : Inventory inputs)
    (initial : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :=
  CellAwarePublicCells.generalized (functions rows initial profile)
    (GeneralizedLocalInstanceValues.model compiled.indexed)

abbrev State (rows : Inventory inputs)
    (anchor : Header compiled (Program.ofChecked compiled.sourceProgram))
    (initial : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (recipe : SourceCoreIndexedSession.Recipe)
    {publicArtifact : SourceCoreExecution.Artifact}
    (publicSession : SourceCoreExecution.Session publicArtifact) (entries : List Entry) :=
  CellAwarePublicSessionState.State rows (functions rows initial profile)
    (cells rows initial profile) anchor initial recipe publicSession entries

variable {rows : Inventory inputs}
  {anchor : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {initial : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {profile : compiled.compatible.checked.catalog.callableContracts = true}
  {recipe : SourceCoreIndexedSession.Recipe}

/-- Actual named startup moves all retained entries to its real receiver. No
cell-transport law or call-body law is requested from the caller. -/
theorem State.at_named_request
    (prepared : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry} (state : State rows anchor initial profile recipe session entries)
    {checkpoint : SourceCoreExecution.Checkpoint artifact}
    {key : SourceCoreIndexedSession.Key} {arguments : List SourceCorePublicValues.Value} {inputFuel : Nat}
    (request : RecursiveNamedPublicHistoryFrontdoor.Started (headers rows) prepared
      checkpoint state.session key arguments inputFuel state.world state.store) :
    ∃ receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed,
      receiving.result.context = request.encodedValues ∧
      CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed receiving.entry
        receiving.result.context.registry receiving.result.extension receiving.result.diagnostics ∧
      SourceCoreRawMetadata.Extends initial.result.context.registry receiving.result.context.registry ∧
      CellAwarePublicPhysicalHistory.History (headers := headers rows) (keys := keys compiled)
        (functions := functions rows initial profile)
        (cells := cells rows initial profile receiving.result.context.registry)
        (receiving := receiving.result.context.registry) (anchor := anchor)
        state.session state.mapping state.world state.heap state.store state.caller entries :=
  CellAwarePublicSessionState.State.at_named_request
    (CellAwarePublicCells.generalized_extends_registry _ _) prepared state request

/-- Actual packed input encoding reuses all current handle meanings, including
nested or repeated references, and retains the exact physical heap authority. -/
theorem State.at_packed_input
    (prepared : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry} (state : State rows anchor initial profile recipe session entries)
    {entry : Entry} (member : entry ∈ entries)
    {sourceParameter sourceResult : TypeSystem.Ty}
    (entryType : entry.sourceType = .function sourceParameter sourceResult)
    {argument : SourceCorePublicValues.Value} {source : Dynamic.Value}
    (input : RecursiveNamedPublicFunctionHistoryInputs.Input entries anchor.function.context
      sourceParameter argument source)
    {inputFuel : Nat} {checkpoint : SourceCoreIndexedSession.Checkpoint state.artifact}
    {parameter result : TypeSystem.Ty} {nativeParameter nativeResult : Core.Ty}
    {callable packed : Core.Value} {encodedValues : SourceCoreCompatibleValues.Context}
    (started : RecursiveNamedPublicDirectPackedInputMeaning.StartAt state.session entry.handle
      argument inputFuel checkpoint recipe state.world state.store parameter result
      nativeParameter nativeResult callable packed encodedValues) :
    ∃ receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed,
      receiving.result.context = encodedValues ∧
      CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed receiving.entry
        receiving.result.context.registry receiving.result.extension receiving.result.diagnostics ∧
      SourceCoreRawMetadata.Extends initial.result.context.registry receiving.result.context.registry ∧
      CellAwarePublicPhysicalHistory.History (headers := headers rows) (keys := keys compiled)
        (functions := functions rows initial profile)
        (cells := cells rows initial profile receiving.result.context.registry)
        (receiving := receiving.result.context.registry) (anchor := anchor)
        state.session state.mapping state.world state.heap state.store state.caller entries ∧
      CompatiblePayload.ValueRep compiled.compatible.checked receiving.result.context.registry
        (functions rows initial profile) state.mapping state.world
        sourceParameter source packed nativeParameter ∧
      Dynamic.ValueHasType anchor.function.context state.heap source sourceParameter ∧
      ∀ token, checkpoint.diagnostic token = .ok (receiving.result.diagnostics.diagnostic? token) := by
  have sameCompiled := SourceCoreIndexedSession.Recipe.prepare_compiled prepared
  cases sameCompiled
  obtain ⟨receiving, _member, contextAt, issued, extended, retained, represented, typed, diagnostics⟩ :=
    CellAwarePublicActualRegistryStart.packed_input
      (CellAwarePublicCells.generalized_extends_registry _ _)
      state.history.semantic state.registry member entryType input started
  exact ⟨receiving, contextAt, issued, state.extension.trans extended,
    ⟨retained, state.history.physical⟩, represented, typed, diagnostics⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareSelectedPublicSessionState
