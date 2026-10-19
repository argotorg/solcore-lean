import Solcore.SourceSemantics.CoreLowering.CellAwarePublicApplicationResult

/-! Public continuation contexts are supported by actual Source typing. The
returned heap, native evaluation and owned state are kept exactly. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicApplicationResult
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedFunctionValues (Header NamedCapture OwnedKey)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
  {cells : GenericHeap.CellModel (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions}
  {registry : SourceCoreRawMetadata.Registry}
  {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {before : Dynamic.Heap} {store : Store} {canonical : Environment}
  {caller : State headers keys ⟨scope, mapping, world, before, store, canonical⟩}
  {first second : SourceSemantics.Context} {sourceType : TypeSystem.Ty} {nativeType : Ty}
  {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap} {value : Value} {finalStore : Store}
  {finalMap : LocationMap} {finalWorld : StoreTyping} {faults : RecursiveStageMeaning.FaultRep}

theorem ResultAt.context
    (supports : Dynamic.TypeContextSupports first second)
    (result : ResultAt (registry := registry) functions cells caller first sourceType nativeType
      outcome after value finalStore finalMap finalWorld faults) :
    ResultAt (registry := registry) functions cells caller second sourceType nativeType
      outcome after value finalStore finalMap finalWorld faults := by
  obtain ⟨represented, heaps, maps, worlds, administrative, metadata, returned, related, post⟩ := result
  refine ⟨represented, heaps, maps, worlds, administrative, metadata, returned, related, ?_⟩
  cases outcome with
  | value source =>
    refine ⟨post.rows, ?_⟩
    intro source same
    obtain ⟨typed, heapTyped⟩ := post.successful source same
    exact ⟨typed.transportContext supports, heapTyped.transportContext supports⟩
  | fault failure =>
    cases failure with
    | semantic reason => exact ⟨post.rows, by intro source same; cases same⟩
    | stage origin call reason => exact post

theorem NamedResultAt.context
    {owner : OwnedKey keys} {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    {capture : NamedCapture headers owner.key header mapping world} {arguments : List Value}
    (supports : Dynamic.TypeContextSupports first second)
    (result : NamedResultAt (registry := registry) functions cells owner caller header capture arguments
      first outcome after value finalStore finalMap finalWorld faults) :
    NamedResultAt (registry := registry) functions cells owner caller header capture arguments
      second outcome after value finalStore finalMap finalWorld faults :=
  ⟨result.1, result.2.context supports⟩

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicApplicationResult
