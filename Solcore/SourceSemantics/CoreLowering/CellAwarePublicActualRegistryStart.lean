import Solcore.SourceSemantics.CoreLowering.CellAwarePublicHistoryRegistryExtension
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicCheckpointReceiver

/-! The actual packed startup determines the receiving context. Current
history supplies both the retained callable and every nested input handle;
the encoder supplies the forward registry extension. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicActualRegistryStart
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SourceCoreIndexedSession CallableIndexedOwnedFunctionState
open CellAwarePublicFunctionHistory (History Caller)
open RecursiveNamedPublicFunctionHistory (Entry)
open CallableIndexedOwnedPublicFaultReceivers

variable {recipe : Recipe}
  {headers : List (CallableIndexedOwnedFunctionValues.Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))}
  {functions : FunctionModel recipe.compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions recipe.compiled.indexed)}
  {cells : CellAwarePublicCells.Family (CallableIndexedAmbient.ambientDefinitions recipe.compiled.indexed).definitions}
  {registry : SourceCoreRawMetadata.Registry}
  {anchor : CallableIndexedOwnedFunctionValues.Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
  {caller : Caller headers keys mapping world heap store}
  {artifact : Artifact} {session : Session artifact} {entries : List Entry}

/-- Construct the actual receiver and input meaning together. No completed
native execution, future registry or reverse extension is supplied. -/
theorem packed_input (covariant : CellAwarePublicCells.ExtendsRegistry cells)
    (history : History headers keys functions (cells registry) registry anchor session mapping world heap store caller entries)
    (atRegistry : session.RegistryAt registry)
    {entry : Entry} (member : entry ∈ entries)
    {sourceParameter sourceResult : TypeSystem.Ty}
    (entryType : entry.sourceType = .function sourceParameter sourceResult)
    {argument : SourceCorePublicValues.Value} {source : Dynamic.Value}
    (input : RecursiveNamedPublicFunctionHistoryInputs.Input entries anchor.function.context sourceParameter argument source)
    {inputFuel : Nat} {checkpoint : Checkpoint artifact}
    {parameter result : TypeSystem.Ty} {nativeParameter nativeResult : Core.Ty}
    {callable packed : Core.Value} {encodedValues : SourceCoreCompatibleValues.Context}
    (started : RecursiveNamedPublicDirectPackedInputMeaning.StartAt session entry.handle argument inputFuel
      checkpoint recipe world store parameter result nativeParameter nativeResult callable packed encodedValues) :
    ∃ receiver : Receiver recipe.compiled.indexed,
      receiver.entry ∈ recipe.compiled.indexed.entries ∧
      receiver.result.context = encodedValues ∧
      CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt recipe.compiled.indexed receiver.entry
        receiver.result.context.registry receiver.result.extension receiver.result.diagnostics ∧
      SourceCoreRawMetadata.Extends registry receiver.result.context.registry ∧
      History headers keys functions (cells receiver.result.context.registry) receiver.result.context.registry anchor
        session mapping world heap store caller entries ∧
      ValueRep recipe.compiled.compatible.checked receiver.result.context.registry functions mapping world
        sourceParameter source packed nativeParameter ∧
      Dynamic.ValueHasType anchor.function.context heap source sourceParameter ∧
      ∀ token, checkpoint.diagnostic token = .ok (receiver.result.diagnostics.diagnostic? token) := by
  obtain ⟨extended, retained, represented, typed⟩ :=
    CellAwarePublicHistoryRegistryExtension.at_packed_input covariant rfl member entryType input history atRegistry started
  obtain ⟨indexed, indexedMember⟩ := CellAwarePublicHistoryRegistryExtension.indexed_entry history
  obtain ⟨receiver, indexedAt, contextAt, issued⟩ :=
    Receiver.at_context recipe.compiled indexed encodedValues started.owner
  obtain ⟨program, present⟩ := CellAwarePublicHistoryRegistryExtension.diagnostics_present history
  refine ⟨receiver, indexedAt ▸ indexedMember, contextAt, issued, ?_, ?_, ?_, typed,
    fun token => RecursiveNamedPublicCheckpointReceiver.diagnostic_eq
      started.recipe_eq started.values contextAt issued present token⟩
  · rw [contextAt]; exact extended
  · rw [contextAt]; exact retained
  · rw [contextAt]; exact represented

/-- Named input encoding chooses the receiver and transports the entire
retained history along its actual forward metadata extension. -/
theorem named_start (covariant : CellAwarePublicCells.ExtendsRegistry cells)
    (history : History headers keys functions (cells registry) registry anchor session mapping world heap store caller entries)
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
      History headers keys functions (cells receiver.result.context.registry) receiver.result.context.registry anchor
        session mapping world heap store caller entries ∧
      ∀ token, checkpoint.diagnostic token = .ok (receiver.result.diagnostics.diagnostic? token) := by
  obtain ⟨extended, retained⟩ :=
    CellAwarePublicHistoryRegistryExtension.at_named_start covariant history atRegistry started
  obtain ⟨indexed, indexedMember⟩ := CellAwarePublicHistoryRegistryExtension.indexed_entry history
  obtain ⟨receiver, indexedAt, contextAt, issued⟩ :=
    Receiver.at_context recipe.compiled indexed encodedValues started.owner
  obtain ⟨program, present⟩ := CellAwarePublicHistoryRegistryExtension.diagnostics_present history
  refine ⟨receiver, indexedAt ▸ indexedMember, contextAt, issued, ?_, ?_,
    fun token => RecursiveNamedPublicCheckpointReceiver.diagnostic_eq
      started.recipe_eq started.values contextAt issued present token⟩
  · rw [contextAt]; exact extended
  · rw [contextAt]; exact retained

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicActualRegistryStart
