import Solcore.SourceSemantics.CoreLowering.CellAwarePublicPhysicalHistory

/-! An actual public session carries its indexed runtime, Source heap and
positive physical history. Calls retain their own public options and receipts. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicSessionState
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open CallableIndexedOwnedFunctionValues (Header)
open RecursiveNamedPublicFunctionHistory (Entry)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {inputs : List (Input compiled)}

structure State (rows : Inventory inputs)
    (functions : CompatiblePayload.FunctionModel compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
    (cells : SourceCoreRawMetadata.Registry →
      GenericHeap.CellModel (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (anchor : Header compiled (Program.ofChecked compiled.sourceProgram))
    (initial : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed)
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
  history : CellAwarePublicPhysicalHistory.History (headers := headers rows)
    (keys := keys compiled) (functions := functions)
    (cells := cells receiving.result.context.registry)
    (receiving := receiving.result.context.registry) (anchor := anchor)
    session mapping world heap store caller entries

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicSessionState
