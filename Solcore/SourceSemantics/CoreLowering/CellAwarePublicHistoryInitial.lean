import Solcore.SourceSemantics.CoreLowering.CellAwarePublicFunctionHistory
import Solcore.SourceSemantics.CoreLowering.CellAwarePublicCells

/-! A real ordinary public history embeds into the mixed cell representation
without changing a call, capture, heap, session or ordered export. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicHistoryInitial
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SourceCoreIndexedSession CallableIndexedOwnedFunctionState
open CallableIndexedOwnedFunctionValues (Header NamedCapture OwnedKey)
open RecursiveNamedPublicFunctionHistory (Caller Entry)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
  (instances : GeneralizedLocalDescriptorHeap.InstanceModel (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
  {registry : SourceCoreRawMetadata.Registry}
  {anchor : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
  {caller : Caller headers keys mapping world heap store}

private theorem named_result
    {owner : OwnedKey keys} {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    {capture : NamedCapture headers owner.key header mapping world} {arguments : List Core.Value}
    {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap} {native : Core.Value}
    {finalStore : Store} {finalMap : LocationMap} {finalWorld : StoreTyping} {faults : RecursiveStageMeaning.FaultRep}
    (result : RecursiveNamedPublicFunctionHistory.Result (functions := functions) (receiving := registry) (anchor := anchor)
      owner caller header capture arguments outcome after native finalStore finalMap finalWorld faults) :
    CellAwarePublicFunctionHistory.Result (functions := functions) (receiving := registry) (anchor := anchor)
      (cells := CellAwarePublicCells.generalized functions instances registry)
      owner caller header capture arguments outcome after native finalStore finalMap finalWorld faults :=
  ⟨result.1, result.2.1, CellAwarePublicCells.generalized_initial instances result.2.2.1, result.2.2.2⟩

private theorem packed_result
    {sourceType : TypeSystem.Ty} {nativeType : Core.Ty}
    {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap} {native : Core.Value}
    {finalStore : Store} {finalMap : LocationMap} {finalWorld : StoreTyping} {faults : RecursiveStageMeaning.FaultRep}
    (result : RecursivePublicApplicationResult.ResultAt (registry := registry) functions caller
      anchor.function.context sourceType nativeType outcome after native finalStore finalMap finalWorld faults) :
    CellAwarePublicApplicationResult.ResultAt (registry := registry) functions
      (CellAwarePublicCells.generalized functions instances registry) caller
      anchor.function.context sourceType nativeType outcome after native finalStore finalMap finalWorld faults :=
  ⟨result.1, CellAwarePublicCells.generalized_initial instances result.2.1, result.2.2⟩

/-- Every transition still carries its original start and completion receipt.
Only ordinary cell representation is injected into the descriptor-aware model. -/
theorem of_ordinary {artifact : Artifact} {session : Session artifact} {entries : List Entry}
    (history : RecursiveNamedPublicFunctionHistory.History headers keys functions registry anchor
      session mapping world heap store caller entries) :
    CellAwarePublicFunctionHistory.History headers keys functions
      (CellAwarePublicCells.generalized functions instances registry) registry anchor
      session mapping world heap store caller entries := by
  induction history with
  | first sameCompiled started selected succeeded result reached post addition =>
      exact .first sameCompiled started selected succeeded (named_result instances result) reached post addition
  | next prior sameCompiled started selected succeeded result reached post addition ih =>
      exact .next ih sameCompiled started selected succeeded (named_result instances result) reached post addition
  | first_export_error sameCompiled started selected exported result reached post =>
      exact .first_export_error sameCompiled started selected exported (named_result instances result) reached post
  | next_export_error prior sameCompiled started selected exported result reached post ih =>
      exact .next_export_error ih sameCompiled started selected exported (named_result instances result) reached post
  | first_failed sameCompiled started selected failed result reached post heapTyped =>
      exact .first_failed sameCompiled started selected failed (named_result instances result) reached post heapTyped
  | failed prior sameCompiled started selected failed result reached post heapTyped ih =>
      exact .failed ih sameCompiled started selected failed (named_result instances result) reached post heapTyped
  | packed_next prior started succeeded result reached post addition ih =>
      exact .packed_next ih started succeeded (packed_result instances result) reached post addition
  | packed_failed prior started failed result reached post heapTyped ih =>
      exact .packed_failed ih started failed (packed_result instances result) reached post heapTyped
  | packed_export_error prior started exported result reached post ih =>
      exact .packed_export_error ih started exported (packed_result instances result) reached post
  | issued prior continued ih => exact .issued ih continued
  | remember_issued prior receipt ih => exact .remember_issued ih receipt
  | restored prior restored ih => exact .restored ih restored

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicHistoryInitial
