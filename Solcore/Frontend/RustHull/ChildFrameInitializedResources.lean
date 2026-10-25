import Solcore.Frontend.RustHull.ChildFrameInitializationFacts

/-! Actual child cells provide the complete state relation for the compiled
frame. All locations and their separation come from allocation evidence. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ChildFrameCorrespondence
open Core Correspondence ScalarExecution

structure Ready (cells : List InitializedCell) (store : Store)
    (state : RuntimeReturnDataEffectsSemantics.State) (bytes : List UInt8) where
  layout : RuntimeReturnDataEffectsCorrespondence.Layout
  boundary : layout.boundary = store.length
  members : ∀ slot ∈ RuntimeCallInitializedEffects.baseSlots layout,
    slot ∈ cells.map InitializedCell.effectSlot
  codes : ∀ imageCells, layout.codeCells = some imageCells →
    ⟨"code", WordMapping.type, imageCells.code⟩ ∈ cells.map InitializedCell.effectSlot ∧
    ⟨"codeKnown", .bool, imageCells.known⟩ ∈ cells.map InitializedCell.effectSlot
  mode : layout.codeCells.isSome = true
  related : StateRel (RuntimeReturnDataEffectsCorrespondence.model layout (prefixRead layout.boundary store)
    (cells.map InitializedCell.effectSlot) (some bytes)) [] ⟨[], state⟩ store
  passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout (cells.map InitializedCell.effectSlot)

theorem initialized_ready {cells : List InitializedCell} {store : Store}
    (parent : RuntimeCallEffectsSemantics.State) (request : AccountCallSemantics.Request)
    (shared : AccountCallSemantics.Shared) (bytes : List UInt8)
    {accounts : StorageCorrespondence.Accounts}
    (world : accounts.map Prod.fst = shared.world)
    (signature : cells.map (fun cell => (cell.name, cell.type)) = RuntimeExtendedInitializedEffects.slots true)
    (stored : InitializedCells cells store) (separate : CellLocations cells)
    (observed : ∀ cell ∈ cells, Observed accounts (Initial parent request shared bytes) bytes cell) :
    Nonempty (Ready cells store (Initial parent request shared bytes) bytes) := by
  obtain ⟨runtime, logs, accountsReady⟩ := RuntimeExtendedInitializedEffects.ready signature stored separate
    (fun cell member => (observed cell member).runtime) world
    (fun cell member => (observed cell member).logs)
    (fun cell member => (observed cell member).logSize)
    (fun cell member => (observed cell member).balances)
  obtain ⟨accountsReady⟩ := accountsReady
  have environment := ContractEnvironmentCorrespondence.initialized_related stored
    (fun cell member => (observed cell member).environment)
  obtain ⟨ready⟩ := RuntimeReturnDataInitializedEffects.ready signature stored separate accountsReady
    (image := some bytes) (data := []) (size := Word.zero)
    (fun cell member => (observed cell member).data)
    (by
      intro cell member named typed
      apply (observed cell member).environment
      simp only [named, typed, EnvironmentBuiltinCorrespondence.observation, Initial, ChildFrameSemantics.initial])
    (fun _ cell member => (observed cell member).code)
    (fun _ cell member => (observed cell member).known)
  have memoryLocation : ready.layout.memory = runtime.memory := by
    change ready.layout.toAccountLayout.memory = runtime.memory
    rw [ready.base]
    exact (congrArg (fun layout : RuntimeLogEffectsCorrespondence.Layout => layout.memory) accountsReady.base).trans
      (congrArg RuntimeEffectsCorrespondence.Layout.memory logs.base)
  have storageLocations : ready.layout.storage = runtime.locations := by
    change ready.layout.toAccountLayout.storage = runtime.locations
    rw [ready.base]
    exact (congrArg (fun layout : RuntimeLogEffectsCorrespondence.Layout => layout.storage) accountsReady.base).trans
      (congrArg RuntimeEffectsCorrespondence.Layout.storage logs.base)
  have boundary : ready.layout.boundary = store.length := by
    change ready.layout.toAccountLayout.boundary = store.length
    rw [ready.base]
    exact (congrArg (fun layout : RuntimeLogEffectsCorrespondence.Layout => layout.boundary) accountsReady.base).trans
      (congrArg RuntimeEffectsCorrespondence.Layout.boundary logs.base)
  have related : StateRel (RuntimeReturnDataEffectsCorrespondence.model ready.layout
      (prefixRead ready.layout.boundary store) (cells.map InitializedCell.effectSlot) (some bytes)) []
      ⟨[], Initial parent request shared bytes⟩ store := by
    apply RuntimeReturnDataEffectsCorrespondence.initial_state
    · rw [ready.base]
      apply RuntimeAccountEffectsCorrespondence.initial_state
      · rw [accountsReady.base]
        apply RuntimeLogEffectsCorrespondence.initial_state
        · simpa only [logs.base, RuntimeEffectsCorrespondence.initialLayout] using
            RuntimeEnvironmentEffectsCorrespondence.initial_state runtime.memoryRelated runtime.storageRelated runtime.distinct environment
        · exact logs.logsRead
        · exact logs.logSizeRead
      · exact accountsReady.balancesRead
    · exact ready.readData
    · exact ready.readSize
    · exact ready.readCode
  refine ⟨ready.layout, boundary, RuntimeCallInitializedEffects.base_members ready,
    ready.codeMembers, ready.mode, related, ?_⟩
  apply RuntimeLogEffectsCorrespondence.Passive.of_names
    (memoryMember := by simpa only [memoryLocation] using runtime.memoryMember)
    (worldMember := by simpa only [storageLocations] using runtime.worldMember)
    (memorySizeMember := by simpa only [storageLocations] using runtime.sizeMember)
    (exitMember := by simpa only [storageLocations] using runtime.exitMember)
    (offsetMember := by simpa only [storageLocations] using runtime.offsetMember)
    (sizeMember := by simpa only [storageLocations] using runtime.returnSizeMember)
    (logsMember := by simpa only [ready.base, accountsReady.base] using logs.logsMember)
    (logSizeMember := by simpa only [ready.base, accountsReady.base] using logs.logSizeMember)
  intro first firstMember second secondMember same
  obtain ⟨left, leftMember, rfl⟩ := List.mem_map.mp firstMember
  obtain ⟨right, rightMember, rfl⟩ := List.mem_map.mp secondMember
  exact separate left leftMember right rightMember same

end Solcore.Frontend.RustHull.ChildFrameCorrespondence
