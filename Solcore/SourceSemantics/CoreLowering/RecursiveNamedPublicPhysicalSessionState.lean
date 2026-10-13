import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalClosureHistory
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalFrontdoor
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedInitializedPhysicalClosureArguments
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicSimpleInputRegistry
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryReflection

/-! An actual public session carries its indexed runtime, Source heap and
positive physical history. Calls retain their own public options and receipts. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalSessionState
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open CallableIndexedOwnedFunctionValues (Header)
open RecursiveNamedPublicFunctionHistory (Entry)

structure StartedCall {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreIndexedSession.Key)
    (arguments : List SourceCorePublicValues.Value) (options : SourceCoreExecution.RunOptions) where
  checkpoint : SourceCoreExecution.Checkpoint artifact
  started : session.start key arguments options.inputValidationFuel = .ok checkpoint

structure Call {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreIndexedSession.Key)
    (arguments : List SourceCorePublicValues.Value) (options : SourceCoreExecution.RunOptions)
    extends StartedCall session key arguments options where
  completion : SourceCoreExecution.Completion artifact
  executed : session.RunAt key arguments options (.ok (.succeeded completion))

structure FunctionCall {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreIndexedSession.Key)
    (arguments : List SourceCorePublicValues.Value) (options : SourceCoreExecution.RunOptions)
    extends Call session key arguments options where
  handle : SourceCorePublicValues.Handle
  returned : completion.value = .function handle

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {inputs : List (Input compiled)}

def functions (rows : Inventory inputs)
    (initial : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :=
  CallableIndexedOwnedPhysicalCellOrigins.functions (headers rows) (keys compiled)
    initial.result.context.registry
    (CallableIndexedOwnedPublicDecodedCallFaults.faults initial.result.diagnostics) profile

structure State (rows : Inventory inputs)
    (anchor : Header compiled (Program.ofChecked compiled.sourceProgram))
    (initial : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (recipe : SourceCoreIndexedSession.Recipe)
    {publicArtifact : SourceCoreExecution.Artifact}
    (publicSession : SourceCoreExecution.Session publicArtifact) (entries : List Entry) where
  artifact : SourceCoreIndexedSession.Artifact
  session : SourceCoreIndexedSession.Session artifact
  mapping : GeneralHeap.LocationMap
  world : Core.StoreTyping
  heap : Dynamic.Heap
  store : Core.Store
  caller : RecursiveNamedPublicFunctionHistory.Caller (headers rows)
    (keys compiled) mapping world heap store
  atSession : publicSession.IndexedAt session
  atRecipe : RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact recipe
  receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed
  issued : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
    receiving.entry receiving.result.context.registry receiving.result.extension receiving.result.diagnostics
  extension : SourceCoreRawMetadata.Extends initial.result.context.registry receiving.result.context.registry
  registry : session.RegistryAt receiving.result.context.registry
  history : RecursiveNamedPublicPhysicalHistory.History (headers := headers rows)
    (keys := keys compiled) (functions := functions rows initial profile)
    (receiving := receiving.result.context.registry) (anchor := anchor)
    session mapping world heap store caller entries

def SourceCall (anchor header : Header compiled (Program.ofChecked compiled.sourceProgram))
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap) (arguments : List Dynamic.Value)
    (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap) : Prop :=
  ∃ rawD function size,
    CallableIndexedOwnedFunctionValues.NamedSourceAt header rawD function ∧
    Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram)
      (RecursiveNamedPreparedStageScopes.registry
        (RecursiveNamedPreparedStageContracts.of_compiled compiled compiled.indexed.ancestry.graph.inputs.callableSelected))
      size invocation anchor.function.context before (.global function) arguments outcome after

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalSessionState
