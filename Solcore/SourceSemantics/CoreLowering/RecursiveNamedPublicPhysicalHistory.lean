import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicFunctionHistory
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalCanonicalState

/-! Public histories retain the complete physical cache together with the same
ordinary Source exports and actual caller pool. Whole-call administrative
preservation transports this authority across every exact returned session. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalHistory
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SourceCoreIndexedSession CallableIndexedOwnedFunctionState
open CallableIndexedOwnedFunctionValues (Header NamedCapture OwnedKey)
open RecursiveNamedPublicFunctionHistory (Caller Entry Result)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
  {receiving : SourceCoreRawMetadata.Registry}
  {anchor : Header compiled (Program.ofChecked compiled.sourceProgram)}

structure History {artifact : Artifact} (session : Session artifact)
    (mapping : LocationMap) (world : StoreTyping) (heap : Dynamic.Heap) (store : Store)
    (caller : Caller headers keys mapping world heap store) (entries : List Entry) : Prop where
  semantic : RecursiveNamedPublicFunctionHistory.History headers keys functions receiving anchor
    session mapping world heap store caller entries
  physical : CallableIndexedOwnedPhysicalGlobals.Authority compiled mapping store

theorem physical_of_result
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    {owner : OwnedKey keys} {caller : Caller headers keys mapping world heap store}
    {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    {capture : NamedCapture headers owner.key header mapping world} {arguments : List Core.Value}
    {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap} {native : Core.Value} {finalStore : Store}
    {finalMap : LocationMap} {finalWorld : StoreTyping} {faults : RecursiveStageMeaning.FaultRep}
    (physical : CallableIndexedOwnedPhysicalGlobals.Authority compiled mapping store)
    (result : Result (functions := functions) (receiving := receiving) (anchor := anchor)
      owner caller header capture arguments outcome after native finalStore finalMap finalWorld faults) :
    CallableIndexedOwnedPhysicalGlobals.Authority compiled finalMap finalStore :=
  physical.extend result.2.2.2.2.2.1

/-- The supplied history is the original public history at the actual result;
only its physical cache proof is added from whole-call preservation. -/
theorem History.after_result
    {artifact : Artifact} {session : Session artifact}
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    {owner : OwnedKey keys} {caller : Caller headers keys mapping world heap store} {entries : List Entry}
    (prior : History (functions := functions) (receiving := receiving) (anchor := anchor)
      session mapping world heap store caller entries)
    {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    {capture : NamedCapture headers owner.key header mapping world} {arguments : List Core.Value}
    {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap} {native : Core.Value} {finalStore : Store}
    {finalMap : LocationMap} {finalWorld : StoreTyping} {faults : RecursiveStageMeaning.FaultRep}
    (result : Result (functions := functions) (receiving := receiving) (anchor := anchor)
      owner caller header capture arguments outcome after native finalStore finalMap finalWorld faults)
    {nextSession : Session artifact} {reached : Caller headers keys finalMap finalWorld after finalStore}
    {nextEntries : List Entry}
    (next : RecursiveNamedPublicFunctionHistory.History headers keys functions receiving anchor
      nextSession finalMap finalWorld after finalStore reached nextEntries) :
    History (functions := functions) (receiving := receiving) (anchor := anchor)
      nextSession finalMap finalWorld after finalStore reached nextEntries :=
  ⟨next, physical_of_result prior.physical result⟩

/-- The stronger public caller wraps the identical reached pool. -/
def History.caller {artifact : Artifact} {session : Session artifact}
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    {caller : Caller headers keys mapping world heap store} {entries : List Entry}
    (history : History (functions := functions) (receiving := receiving) (anchor := anchor)
      session mapping world heap store caller entries) :
    CallableIndexedOwnedPhysicalState.PoolState headers keys
      ⟨[], mapping, world, heap, store, SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed⟩ :=
  ⟨caller, history.physical⟩

/-- The public session's actual global environment supplies the full canonical
slot layout for the next call, paired with its reached physical cache. -/
def History.canonical_caller {artifact : Artifact} {session : Session artifact}
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    {caller : Caller headers keys mapping world heap store} {entries : List Entry}
    (history : History (functions := functions) (receiving := receiving) (anchor := anchor)
      session mapping world heap store caller entries) :
    (CallableIndexedOwnedPhysicalCanonicalState.protocol headers keys 0).State
      ⟨[], mapping, world, heap, store, SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed⟩ :=
  ⟨⟨caller, CallableIndexedOwnedPhysicalGlobals.environment_slots compiled⟩, history.physical⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalHistory
