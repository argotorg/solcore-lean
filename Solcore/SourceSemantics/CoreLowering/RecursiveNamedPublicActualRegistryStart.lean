import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicHistoryRegistryExtension
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicCheckpointReceiver

/-! The actual packed startup determines the receiving context. Current
history supplies both the retained callable and every nested input handle;
the encoder supplies the forward registry extension. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryStart
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

/-- Construct the actual receiver and input meaning together. No completed
native execution, future registry or reverse extension is supplied. -/
theorem packed_input
    (history : History headers keys functions registry anchor session mapping world heap store caller entries)
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
      History headers keys functions receiver.result.context.registry anchor
        session mapping world heap store caller entries ∧
      ValueRep recipe.compiled.compatible.checked receiver.result.context.registry functions mapping world
        sourceParameter source packed nativeParameter ∧
      Dynamic.ValueHasType anchor.function.context heap source sourceParameter ∧
      ∀ token, checkpoint.diagnostic token = .ok (receiver.result.diagnostics.diagnostic? token) := by
  obtain ⟨extended, retained, represented, typed⟩ :=
    RecursiveNamedPublicHistoryRegistryExtension.at_packed_input rfl member entryType input history atRegistry started
  obtain ⟨indexed, indexedMember⟩ := RecursiveNamedPublicHistoryRegistryExtension.indexed_entry history
  obtain ⟨receiver, indexedAt, contextAt, issued⟩ :=
    Receiver.at_context recipe.compiled indexed encodedValues started.owner
  obtain ⟨program, present⟩ := RecursiveNamedPublicHistoryRegistryExtension.diagnostics_present history
  refine ⟨receiver, indexedAt ▸ indexedMember, contextAt, issued, ?_, ?_, ?_, typed,
    fun token => RecursiveNamedPublicCheckpointReceiver.diagnostic_eq
      started.recipe_eq started.values contextAt issued present token⟩
  · rw [contextAt]; exact extended
  · rw [contextAt]; exact retained
  · rw [contextAt]; exact represented

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryStart
