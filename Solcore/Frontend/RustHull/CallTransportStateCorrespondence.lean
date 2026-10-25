import Solcore.Frontend.RustHull.CallTransportValues
import Solcore.Frontend.RustHull.LogsCorrespondence
import Solcore.Frontend.RustHull.MemoryCopyCorrespondence
import Solcore.Frontend.RustHull.ClosureFrameCorrespondence

/-! Caller-local memory and return data occupy four distinct cells. The same
four-cell frame rules used for event storage apply after renaming the two
mapping fields; no event behavior is involved in this representation. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.CallTransportCorrespondence
open Core Correspondence ScalarExecution CallTransportSemantics

structure Locations where
  memory : Nat
  memorySize : Nat
  returnData : Nat
  returnDataSize : Nat

def Locations.all (locations : Locations) : List Nat :=
  [locations.memory, locations.memorySize, locations.returnData, locations.returnDataSize]
def Locations.resources (locations : Locations) : LogsCorrespondence.Locations :=
  ⟨locations.memory, locations.memorySize, locations.returnData, locations.returnDataSize⟩
def resources (state : CallTransportSemantics.State) : LogsSemantics.State :=
  {memory := state.memory, words := state.returnData, cursor := state.returnDataSize}
abbrev StateRel (locations : Locations) (state : CallTransportSemantics.State) (store : Store) :=
  LogsCorrespondence.StateRel locations.resources (resources state) store
abbrev Frame (locations : Locations) (initial final : Store) :=
  LogsCorrespondence.Frame locations.resources initial final

theorem memory_related {locations : Locations} {state : CallTransportSemantics.State} {store : Store}
    (related : StateRel locations state store) :
    MemoryCorrespondence.StateRel locations.memory locations.memorySize state.memory store := by
  refine ⟨?_, related.memory, related.memorySize⟩
  have distinct := related.distinct
  simp [LogsCorrespondence.Locations.all, Locations.resources] at distinct
  exact distinct.1.1

theorem memory_updated {locations : Locations} {state : CallTransportSemantics.State} {memory : MemorySemantics.State} {initial final : Store}
    (related : StateRel locations state initial)
    (updated : MemoryCorrespondence.StateRel locations.memory locations.memorySize memory final)
    (frame : MemoryCorrespondence.Frame locations.memory locations.memorySize initial final) :
    StateRel locations {state with memory := memory} final := by
  have distinct := related.distinct
  simp [LogsCorrespondence.Locations.all, Locations.resources] at distinct
  refine ⟨related.distinct, updated.memory, updated.size, ?_, ?_⟩
  · exact frame.read locations.returnData _ (by intro same; simp_all) (by intro same; simp_all) related.logs
  · exact frame.read locations.returnDataSize _ (by intro same; simp_all) (by intro same; simp_all) related.logSize

theorem memory_frame {locations : Locations} {initial final : Store}
    (frame : MemoryCorrespondence.Frame locations.memory locations.memorySize initial final) :
    Frame locations initial final := by
  refine ⟨frame.length, ?_⟩
  intro location value outside found
  apply frame.read location value _ _ found
  · intro same
    exact outside (by simp [Locations.resources, LogsCorrespondence.Locations.all, same])
  · intro same
    exact outside (by simp [Locations.resources, LogsCorrespondence.Locations.all, same])

theorem frame_closures {locations : Locations} {state : CallTransportSemantics.State} {initial final : Store}
    (related : StateRel locations state initial) (frame : Frame locations initial final) :
    ClosuresPreserved initial final := by
  intro location parameter result body environment found
  apply frame.read location _ _ found
  intro member
  simp only [Locations.resources, LogsCorrespondence.Locations.all, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · have same := Option.some.inj (related.memory.symm.trans found)
    cases entries : state.memory.words <;> simp only [resources, entries, WordMapping.encode] at same <;> cases same
  · have same := Option.some.inj (related.memorySize.symm.trans found)
    cases same
  · have same := Option.some.inj (related.logs.symm.trans found)
    cases entries : state.returnData <;> simp only [resources, entries, WordMapping.encode] at same <;> cases same
  · have same := Option.some.inj (related.logSize.symm.trans found)
    cases same

def publishStore (locations : Locations) (store : Store) (data : MemorySemantics.Entries) (size : Word) : Store :=
  LogsCorrespondence.publishStore locations.resources store data size

theorem published {locations : Locations} {state : CallTransportSemantics.State} {store : Store}
    (related : StateRel locations state store) (data : MemorySemantics.Entries) (size : Word) :
    StateRel locations {state with returnData := data, returnDataSize := size} (publishStore locations store data size) :=
  related.publish data size

def argumentValues (locations : Locations) (callback : Nat) (arguments : Arguments) : List Core.Value :=
  [.cellRef WordMapping.type locations.memory, .cellRef .word locations.memorySize,
    .cellRef WordMapping.type locations.returnData, .cellRef .word locations.returnDataSize,
    .cellRef (OptionalCell.cellType Calls.callbackType) callback,
    .word arguments.caller, .word arguments.depth, .bool arguments.isStatic, .word arguments.gas,
    .word arguments.target, .word arguments.value, .word arguments.inputOffset, .word arguments.inputLength,
    .word arguments.outputOffset, .word arguments.outputLength]

abbrev Inputs (depth : Nat) (environment : Environment) (locations : Locations) (callback : Nat) (arguments : Arguments) :=
  CodeValue depth environment Calls.arg (bundleValues (argumentValues locations callback arguments))

theorem input_part {depth : Nat} {environment : Environment} {locations : Locations} {callback : Nat} {arguments : Arguments}
    (related : Inputs depth environment locations callback arguments) {index : Nat} {value : Core.Value}
    (found : (argumentValues locations callback arguments)[index]? = some value) :
    CodeValue depth environment (Calls.part index) value := related.part found

theorem input_initial (locations : Locations) (callback : Nat) (arguments : Arguments) (environment : Environment) :
    Inputs 0 (bundleValues (argumentValues locations callback arguments) :: environment) locations callback arguments := by
  intro extra store
  exact .var (by simp)

end Solcore.Frontend.RustHull.CallTransportCorrespondence
