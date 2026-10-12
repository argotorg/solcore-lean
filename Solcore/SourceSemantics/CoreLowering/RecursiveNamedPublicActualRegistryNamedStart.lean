import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryStart

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryNamedStart
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SourceCoreIndexedSession CallableIndexedOwnedFunctionState
open RecursiveNamedPublicFunctionHistory (History Entry Caller)
open CallableIndexedOwnedPublicFaultReceivers

variable {recipe : Recipe}
  {headers : List (CallableIndexedOwnedFunctionValues.Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))}
  {functions : FunctionModel recipe.compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions recipe.compiled.indexed)}
  {registry : SourceCoreRawMetadata.Registry}
  {anchor : CallableIndexedOwnedFunctionValues.Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
  {caller : Caller headers keys mapping world heap store}
  {artifact : Artifact} {session : Session artifact} {entries : List Entry}

/-- Named input encoding chooses the receiver and transports the entire
retained history along its actual forward metadata extension. -/
theorem named_start
    (history : History headers keys functions registry anchor session mapping world heap store caller entries)
    (atRegistry : session.RegistryAt registry)
    {root : Root recipe.compiled} {key : SourceCoreIndexedSession.Key}
    {arguments : List SourceCorePublicValues.Value} {inputFuel : Nat}
    {checkpoint : Checkpoint artifact} {native : Environment}
    {encodedValues : SourceCoreCompatibleValues.Context}
    (started : RecursiveNamedPublicStartMeaning.StartAt session key arguments inputFuel
      checkpoint recipe root world store native encodedValues) :
    ∃ receiver : Receiver recipe.compiled.indexed,
      receiver.entry ∈ recipe.compiled.indexed.entries ∧
      receiver.result.context = encodedValues ∧
      CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt recipe.compiled.indexed receiver.entry
        receiver.result.context.registry receiver.result.extension receiver.result.diagnostics ∧
      SourceCoreRawMetadata.Extends registry receiver.result.context.registry ∧
      History headers keys functions receiver.result.context.registry anchor
        session mapping world heap store caller entries ∧
      ∀ token, checkpoint.diagnostic token = .ok (receiver.result.diagnostics.diagnostic? token) := by
  obtain ⟨extended, retained⟩ :=
    RecursiveNamedPublicHistoryRegistryExtension.at_named_start history atRegistry started
  obtain ⟨indexed, indexedMember⟩ := RecursiveNamedPublicHistoryRegistryExtension.indexed_entry history
  obtain ⟨receiver, indexedAt, contextAt, issued⟩ :=
    Receiver.at_context recipe.compiled indexed encodedValues started.owner
  obtain ⟨program, present⟩ := RecursiveNamedPublicHistoryRegistryExtension.diagnostics_present history
  refine ⟨receiver, indexedAt ▸ indexedMember, contextAt, issued, ?_, ?_,
    fun token => RecursiveNamedPublicCheckpointReceiver.diagnostic_eq
      started.recipe_eq started.values contextAt issued present token⟩
  · rw [contextAt]; exact extended
  · rw [contextAt]; exact retained

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryNamedStart
