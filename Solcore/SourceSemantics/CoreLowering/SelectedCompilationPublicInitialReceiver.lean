import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionInitial

/-! The initial public encoder can extend the static metadata registry. Its
actual returned context supplies the first diagnostic receiver, including for
mapping, constructor and proxy arguments. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicInitialReceiver
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open SelectedCompilationPublicSessionState (StartedCall)
open SelectedCompilationPublicSessionInitial (Started)
open SelectedCompilationPhysicalProgramSupport (Support)

variable {recipe : SourceCoreIndexedSession.Recipe}
  {inputs : List (Input recipe.compiled)} {rows : Inventory inputs}
  {prepared : SourceCoreIndexedSession.Recipe.prepare recipe.compiled = .ok recipe}
  {header : Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
  {initial : CallableIndexedOwnedPublicFaultReceivers.Receiver recipe.compiled.indexed}
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {key : SourceCoreIndexedSession.Key} {arguments : List SourceCorePublicValues.Value}
  {options : SourceCoreExecution.RunOptions} {call : StartedCall session key arguments options}

theorem of_started (support : Support recipe.compiled (headers rows) (keys recipe.compiled) initial)
    (start : Started rows prepared header call) :
    ∃ receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver recipe.compiled.indexed,
      receiving.result.context = start.encodedValues ∧
      CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt recipe.compiled.indexed receiving.entry
        receiving.result.context.registry receiving.result.extension receiving.result.diagnostics ∧
      SourceCoreRawMetadata.Extends initial.result.context.registry receiving.result.context.registry := by
  obtain ⟨receiving, _entry, contextAt, issued⟩ :=
    CallableIndexedOwnedPublicFaultReceivers.Receiver.at_context recipe.compiled initial.entry
      start.encodedValues start.started.owner
  refine ⟨receiving, contextAt, issued, ?_⟩
  rw [support.registry]
  exact receiving.result.extension

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicInitialReceiver
