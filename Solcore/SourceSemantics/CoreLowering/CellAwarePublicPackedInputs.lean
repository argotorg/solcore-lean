import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectPackedInputMeaning
import Solcore.SourceSemantics.CoreLowering.CellAwarePublicFunctionHistory

/-! Actual packed input encoding derives every retained function leaf from
its current mixed-cell history, preserving ordered data and repeated handles. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicPackedInputs
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SourceCoreIndexedSession CallableIndexedOwnedFunctionState
open CallableIndexedOwnedFunctionValues (Header)
open RecursiveNamedPublicFunctionHistory (Entry)
open CellAwarePublicFunctionHistory (History Caller)
open RecursiveNamedPublicDirectPackedInputMeaning (StartAt)
section Inputs
variable {artifact : Artifact} {session : Session artifact} {recipe : Recipe}
  {handle : SourceCorePublicValues.Handle} {argument : SourceCorePublicValues.Value}
  {checkpoint : Checkpoint artifact} {fuel : Nat} {world : StoreTyping} {store : Store}
  {parameter result : TypeSystem.Ty} {nativeParameter nativeResult : Core.Ty}
  {callable packed : Core.Value} {encodedValues : SourceCoreCompatibleValues.Context}
  (started : StartAt session handle argument fuel checkpoint recipe world store
    parameter result nativeParameter nativeResult callable packed encodedValues)

include started

/-- Existing history supplies current meanings for every nested handle. The
actual encoder supplies the packed native payload and all registry changes. -/
theorem history_input_compatible
    {headers : List (Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))}
    {keys : List (CallableIndexedOwnedFunctionValues.Key recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))}
    {functions : FunctionModel recipe.compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions recipe.compiled.indexed)}
    {cells : GenericHeap.CellModel (CallableIndexedAmbient.ambientDefinitions recipe.compiled.indexed).definitions}
    {receiving : SourceCoreRawMetadata.Registry}
    {anchor : Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
    {mapping : LocationMap} {heap : Dynamic.Heap} {caller : Caller headers keys mapping world heap store}
    {entries : List Entry} {source : Dynamic.Value} {sourceParameter : TypeSystem.Ty}
    (history : History headers keys functions cells receiving anchor session mapping world heap store caller entries)
    (receipt : RecursiveNamedPublicFunctionHistoryInputs.Input entries anchor.function.context
      sourceParameter argument source)
    (compatible : SourceCoreRawMetadata.runtimeType parameter = SourceCoreRawMetadata.runtimeType sourceParameter)
    (metadata : SourceCoreRawMetadata.Extends encodedValues.registry receiving) :
    ValueRep recipe.compiled.compatible.checked receiving functions mapping world
      sourceParameter source packed nativeParameter ∧
    Dynamic.ValueHasType anchor.function.context heap source sourceParameter := by
  have current := history.current
  obtain ⟨meaning, sourceTyped⟩ := RecursiveNamedPublicFunctionHistoryEncoding.Input.meaning
    receipt started.recipe_eq
    (fun entry member => (current.2.2.2.2 entry member).1)
    (fun entry member => (current.2.2.2.2 entry member).2.1)
    (fun entry member => (current.2.2.2.2 entry member).2.2)
  obtain ⟨before, encoded, _registry, owner, accepted, valueEq, registryEq⟩ := started.raw
  have typed := started.packedTyped
  rw [← valueEq] at typed
  have extended : SourceCoreRawMetadata.Extends encoded.registry receiving := registryEq ▸ metadata
  have represented := meaning owner compatible accepted started.parameterProjection typed extended
  rw [valueEq] at represented
  exact ⟨represented, sourceTyped⟩

/-- Exact source signatures are the reflexive compatibility case. -/
theorem history_input
    {headers : List (Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))}
    {keys : List (CallableIndexedOwnedFunctionValues.Key recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))}
    {functions : FunctionModel recipe.compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions recipe.compiled.indexed)}
    {cells : GenericHeap.CellModel (CallableIndexedAmbient.ambientDefinitions recipe.compiled.indexed).definitions}
    {receiving : SourceCoreRawMetadata.Registry}
    {anchor : Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
    {mapping : LocationMap} {heap : Dynamic.Heap} {caller : Caller headers keys mapping world heap store}
    {entries : List Entry} {source : Dynamic.Value}
    (history : History headers keys functions cells receiving anchor session mapping world heap store caller entries)
    (receipt : RecursiveNamedPublicFunctionHistoryInputs.Input entries anchor.function.context parameter argument source)
    (metadata : SourceCoreRawMetadata.Extends encodedValues.registry receiving) :
    ValueRep recipe.compiled.compatible.checked receiving functions mapping world parameter source packed nativeParameter ∧
      Dynamic.ValueHasType anchor.function.context heap source parameter :=
  history_input_compatible started history receipt rfl metadata

end Inputs
end Solcore.SourceSemantics.CoreLowering.CellAwarePublicPackedInputs
