import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalSessionState
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryNamedStart

/-! The actual input encoder selects the receiving metadata table. Historical
Source results and physical cache authority move together to that table. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalSessionState
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open CallableIndexedOwnedFunctionValues (Header)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {inputs : List (Input compiled)} {rows : Inventory inputs}
  {anchor : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {initial : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {profile : compiled.compatible.checked.catalog.callableContracts = true}
  {recipe : SourceCoreIndexedSession.Recipe}

theorem State.at_named_request
    (prepared : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (state : State rows anchor initial profile recipe session entries)
    {checkpoint : SourceCoreExecution.Checkpoint artifact}
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    {inputFuel : Nat}
    (request : RecursiveNamedPublicHistoryFrontdoor.Started (headers rows) prepared
      checkpoint state.session key publicArguments inputFuel state.world state.store) :
    ∃ receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed,
      receiving.result.context = request.encodedValues ∧
      CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed receiving.entry
        receiving.result.context.registry receiving.result.extension receiving.result.diagnostics ∧
      SourceCoreRawMetadata.Extends initial.result.context.registry receiving.result.context.registry ∧
      RecursiveNamedPublicPhysicalHistory.History (headers := headers rows) (keys := keys compiled)
        (functions := functions rows initial profile) (receiving := receiving.result.context.registry)
        (anchor := anchor) state.session state.mapping state.world state.heap state.store state.caller entries := by
  have sameCompiled := SourceCoreIndexedSession.Recipe.prepare_compiled prepared
  cases sameCompiled
  obtain ⟨receiving, _member, contextAt, issued, extended, retained, _diagnostic⟩ :=
    RecursiveNamedPublicActualRegistryNamedStart.named_start state.history.semantic state.registry request.started
  exact ⟨receiving, contextAt, issued, state.extension.trans extended, retained, state.history.physical⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalSessionState
