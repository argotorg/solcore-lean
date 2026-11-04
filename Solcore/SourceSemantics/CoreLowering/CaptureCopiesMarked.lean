import Solcore.SourceSemantics.CoreLowering.CaptureCopies
import Solcore.SourceSemantics.CoreLowering.CaptureCopiesMarkedSupport
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedAllocation
import Solcore.SourceSemantics.CoreLowering.CoreEvaluationSize

/-! The copies a closure makes of its captured cells through the indexed
marked allocator. Each copied slot reads its cell, then allocates a frame
snapshot, a marker over the scope's original slots and a payload cell holding
the read value, exactly as a marked `let` does. The source copies the same
bindings, so the copies of a represented scope pair up slot by slot; the frame
cell is read and never written. The prefix agreement is sized, so a completed
evaluation of the copies and their continuation unwraps to a continuation
completion no larger. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CaptureCopies
open Core Frontend Frontend.SourceInference GeneralHeap CoreProof ReadOnly

/-- A finite prefix around a continuation: wrapping is exact, and a sized
completion of the whole unwraps to a continuation completion no larger. -/
structure PrefixAgreement (environment : Environment) (store : Store) (whole : Expr)
    (nextEnvironment : Environment) (nextStore : Store) (next : Expr) : Prop where
  wrap : ∀ {result finalStore}, Evaluates nextEnvironment nextStore next result finalStore →
    Evaluates environment store whole result finalStore
  unwrap : ∀ {size result finalStore}, EvaluationSize size environment store whole result finalStore →
    ∃ smaller, smaller ≤ size ∧ EvaluationSize smaller nextEnvironment nextStore next result finalStore

namespace PrefixAgreement

theorem refl (environment : Environment) (store : Store) (code : Expr) :
    PrefixAgreement environment store code environment store code :=
  ⟨id, fun evaluation => ⟨_, Nat.le_refl _, evaluation⟩⟩

theorem trans {environment middleEnvironment nextEnvironment : Environment}
    {store middleStore nextStore : Store} {whole middle next : Expr}
    (first : PrefixAgreement environment store whole middleEnvironment middleStore middle)
    (second : PrefixAgreement middleEnvironment middleStore middle nextEnvironment nextStore next) :
    PrefixAgreement environment store whole nextEnvironment nextStore next := by
  refine ⟨fun evaluation => first.wrap (second.wrap evaluation), ?_⟩
  intro size result finalStore evaluation
  obtain ⟨middleSize, middleLe, middleEvaluation⟩ := first.unwrap evaluation
  obtain ⟨nextSize, nextLe, nextEvaluation⟩ := second.unwrap middleEvaluation
  exact ⟨nextSize, Nat.le_trans nextLe middleLe, nextEvaluation⟩

/-- Forgetting the sizes leaves the finite continuation agreement. -/
theorem continuation {environment nextEnvironment : Environment} {store nextStore : Store}
    {whole next : Expr} (agreement : PrefixAgreement environment store whole nextEnvironment nextStore next) :
    ContinuationAgreement environment store whole nextEnvironment nextStore next := by
  refine ⟨agreement.wrap, ?_⟩
  intro result finalStore evaluation
  obtain ⟨size, sized⟩ := evaluation_has_size evaluation
  obtain ⟨_, _, smaller⟩ := agreement.unwrap sized
  exact smaller.sound

/-- A `let` with a known initializer: its body's sized completion is
strictly smaller than the whole's. -/
theorem letE {environment : Environment} {before middle : Store} {initializer body : Expr} {value : Value}
    (evaluated : Evaluates environment before initializer value middle) :
    PrefixAgreement environment before (.letE initializer body) (value :: environment) middle body := by
  refine ⟨fun evaluation => .letE evaluated evaluation, ?_⟩
  intro size result finalStore evaluation
  obtain ⟨smaller, below, body⟩ := evaluation.let_body evaluated
  exact ⟨smaller, Nat.le_of_lt below, body⟩

end PrefixAgreement

open SourceSemantics.CaptureBinders (copiedBinder?)

/-- The marked copies of the scope suffix `rest`, at scope index `index`
after `ordinal` copies at the positions `done`. The copies made so far sit
below the original slots of the layout environment, the processed slots are
pending behind the copies still to be made, and the actual environment agrees
with the layout under `ρ`. -/
theorem marked_chain_prefix
    {catalog : SourceCoreDataCatalog.Catalog}
    {definitions : DataEnvironment} {cells : GenericHeap.CellModel definitions}
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {source : TypedSource} {administrativeContext preContext : Core.Context}
    {scope : SourceCoreLocalCell.Scope} {environment : Dynamic.Environment} {pre canonical : Environment}
    {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame}
    (sameDefinitions : layouts.definitions = definitions) (frameRegistered : layout.Registered definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef layout.type contextLocation))
    (preLength : preContext.length = pre.length) (rest : SourceCoreLocalCell.Scope) :
    ∀ {taken : SourceCoreLocalCell.Scope} {index ordinal : Nat} {done : List Nat}
      {mapping : LocationMap} {world : StoreTyping} {environmentRest : Dynamic.Environment}
      {canonicalRest copies processed current : Environment}
      {copyTypes processedContext currentContext : Core.Context}
      {heap : Dynamic.Heap} {store : Store} {ρ : Renaming} {inner emitted : Expr},
      scope = taken ++ rest → taken.length = index →
      (∀ i, canonicalRest[i]? = canonical[index + i]?) →
      done.length = ordinal → (∀ position ∈ done, position < index + pre.length) →
      copies.length = ordinal → copyTypes.length = ordinal →
      processed.length = index → processedContext.length = index →
      DataHeap.EnvRepresents catalog mapping world administrativeContext rest environmentRest canonicalRest
        definitions →
      DataHeap.EnvRepresents catalog mapping world [] scope environment (canonical.take scope.length) definitions →
      GenericHeap.CellHeapRepresents cells mapping world heap store →
      store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native) →
      Pending (chainRenaming source pre.length done rest index) (pendingCopies source rest index)
        (pre ++ processed) (copies ++ (pre ++ canonical)) →
      Pending (chainRenaming source pre.length done rest index) (pendingCopies source rest index)
        (preContext ++ processedContext)
        (copyTypes ++ (preContext ++ (SourceCoreLocalCell.coreContext scope ++ administrativeContext))) →
      EnvironmentsAgree ρ (copies ++ (pre ++ canonical)) current →
      Renaming.Respects ρ
        (copyTypes ++ (preContext ++ (SourceCoreLocalCell.coreContext scope ++ administrativeContext)))
        currentContext →
      RuntimeEnvironmentHasTypes world current currentContext definitions →
      SourceCoreSourceCells.copyChain
        (some (SourceCoreCallableIndexedAllocationFrames.allocator layout globals
          (layouts.allocatorAt owner active onError)))
        source scope (· + pre.length) rest index ordinal inner = .ok emitted →
      ∃ copiesRest finalHeap finalCanonicalRest finalActual finalActualContext finalStore finalMap finalWorld
        finalRho,
        Dynamic.EnvironmentCopies source environmentRest heap copiesRest finalHeap ∧
        DataHeap.EnvRepresents catalog finalMap finalWorld administrativeContext rest copiesRest
          finalCanonicalRest definitions ∧
        (∀ i, rest.length ≤ i → finalCanonicalRest[i]? = canonicalRest[i]?) ∧
        GenericHeap.CellHeapRepresents cells finalMap finalWorld finalHeap finalStore ∧
        LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
        AdministrativePreserved mapping store finalMap finalStore ∧ (∃ suffix, finalStore = store ++ suffix) ∧
        finalStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native) ∧
        EnvironmentsAgree (Renaming.comp finalRho (chainRenaming source pre.length done rest index))
          (pre ++ processed ++ finalCanonicalRest) finalActual ∧
        Renaming.Respects (Renaming.comp finalRho (chainRenaming source pre.length done rest index))
          (preContext ++ processedContext ++ (SourceCoreLocalCell.coreContext rest ++ administrativeContext))
          finalActualContext ∧
        RuntimeEnvironmentHasTypes finalWorld finalActual finalActualContext definitions ∧
        PrefixAgreement current store (emitted.rename ρ) finalActual finalStore (inner.rename finalRho) := by
  induction rest with
  | nil =>
    intro taken index ordinal done mapping world environmentRest canonicalRest copies processed current
      copyTypes processedContext currentContext heap store ρ inner emitted split takenLength dropped
      doneLength doneBelow copiesLength copyTypesLength processedLength processedContextLength
      environmentsRest environmentsScope heaps read pendingValues pendingTypes agrees respects
      currentTyped accepted
    obtain rfl := copyChain_nil _ _ _ _ _ _ accepted
    cases environmentsRest with
    | nil typed =>
      have scopeLength : scope.length = index := by
        rw [split, List.append_nil]
        exact takenLength
      have past : ∀ position, index + pre.length ≤ position →
          chainRenaming source pre.length done [] index position = position + ordinal := by
        intro position above
        rw [chainRenaming_not_mem (fun mem => by have := doneBelow position mem; omega)
          (fun slot mem => by simp [copiedSlotsFrom] at mem)]
        simp only [pendingCopies, copiedSlotsFrom_nil, List.length_nil, Nat.add_zero, doneLength]
      refine ⟨[], heap, _, current, currentContext, store, mapping, world, ρ, .nil heap, .nil typed,
        fun _ _ => rfl, heaps, LocationMap.Extends.refl _, WorldExtends.refl _,
        AdministrativePreserved.refl _ _, ⟨[], (List.append_nil store).symm⟩, read, ?_, ?_, currentTyped,
        PrefixAgreement.refl _ _ _⟩
      · intro position value found
        rcases Nat.lt_or_ge position (pre.length + index) with below | above
        · rw [List.getElem?_append_left (by simp [processedLength]; omega)] at found
          exact pendingValues.agree agrees found
        · rw [List.getElem?_append_right (by simp [processedLength]; omega)] at found
          show current[ρ (chainRenaming source pre.length done [] index position)]? = some value
          rw [past position (by omega)]
          apply agrees
          rw [getElem?_append_shift copiesLength, List.getElem?_append_right (by omega)]
          rw [dropped] at found
          rw [← found]
          congr 1
          simp only [List.length_append, processedLength]
          omega
      · intro position type found
        have found : (preContext ++ processedContext ++ administrativeContext)[position]? = some type := found
        rcases Nat.lt_or_ge position (pre.length + index) with below | above
        · rw [List.getElem?_append_left (by simp [processedContextLength, preLength]; omega)] at found
          exact pendingTypes.agree (fun found => respects found) found
        · rw [List.getElem?_append_right (by simp [processedContextLength, preLength]; omega)] at found
          show currentContext[ρ (chainRenaming source pre.length done [] index position)]? = some type
          rw [past position (by omega)]
          apply respects
          rw [getElem?_append_shift copyTypesLength, List.getElem?_append_right (by omega),
            List.getElem?_append_right (by simp [SourceCoreLocalCell.coreContext, scopeLength]; omega), ← found]
          congr 1
          simp only [List.length_append, processedContextLength, SourceCoreLocalCell.coreContext,
            List.length_map, scopeLength]
          omega
  | cons head rest ih =>
    obtain ⟨id, type⟩ := head
    intro taken index ordinal done mapping world environmentRest canonicalRest copies processed current
      copyTypes processedContext currentContext heap store ρ inner emitted split takenLength dropped
      doneLength doneBelow copiesLength copyTypesLength processedLength processedContextLength
      environmentsRest environmentsScope heaps read pendingValues pendingTypes agrees respects
      currentTyped accepted
    have slotFound : scope[index]? = some (id, type) := by
      rw [split, List.getElem?_append_right (by omega)]
      simp [takenLength]
    have splitNext : scope = (taken ++ [(id, type)]) ++ rest := by
      rw [split, List.append_assoc, List.singleton_append]
    have takenNextLength : (taken ++ [(id, type)]).length = index + 1 := by simp [takenLength]
    have canonicalAt : ∀ i, (pre ++ canonical)[i + pre.length]? = canonical[i]? := fun i => by
      rw [List.getElem?_append_right (by omega)]
      congr 1
      omega
    have contextAt : (preContext ++ (SourceCoreLocalCell.coreContext scope ++
        administrativeContext))[index + pre.length]? = some (.cell (OptionalCell.cellType type)) := by
      have bound : index < scope.length := by
        rw [split]
        simp only [List.length_append, List.length_cons]
        omega
      rw [List.getElem?_append_right (by omega),
        List.getElem?_append_left (by simp [SourceCoreLocalCell.coreContext]; omega)]
      have same : index + pre.length - preContext.length = index := by omega
      simp [SourceCoreLocalCell.coreContext, same, slotFound]
    have processedAt : (pre ++ processed).length = index + pre.length := by
      simp only [List.length_append, processedLength]
      omega
    have processedContextAt : (preContext ++ processedContext).length = index + pre.length := by
      simp only [List.length_append, processedContextLength, preLength]
      omega
    have bound : contextLocation < store.length :=
      (List.getElem?_eq_some_iff.mp (read : store[contextLocation]? = _)).1
    have frameAt : (copies ++ (pre ++ canonical))[(· + pre.length) (scope.length + 1 + globals) + ordinal]? =
        some (.cellRef layout.type contextLocation) := by
      show (copies ++ (pre ++ canonical))[scope.length + 1 + globals + pre.length + ordinal]? = _
      rw [getElem?_append_shift copiesLength, canonicalAt]
      exact reference
    have slotsAt : ∀ i, i < scope.length →
        (copies ++ (pre ++ canonical))[(· + pre.length) i + ordinal]? = canonical[i]? := by
      intro i _
      show (copies ++ (pre ++ canonical))[i + pre.length + ordinal]? = canonical[i]?
      rw [getElem?_append_shift copiesLength, canonicalAt]
    cases copied : copiedBinder? source id with
    | none =>
      rw [copyChain_shared _ _ _ _ _ _ _ copied] at accepted
      rw [chainRenaming_shared pre.length done rest index copied, pendingCopies_shared rest index copied]
        at pendingValues pendingTypes
      rw [chainRenaming_shared pre.length done rest index copied]
      have doneBelowNext : ∀ position ∈ done, position < index + 1 + pre.length := fun position mem => by
        have := doneBelow position mem
        omega
      have position : chainRenaming source pre.length done rest (index + 1) (index + pre.length) =
          index + pre.length + ordinal + pendingCopies source rest (index + 1) := by
        rw [chainRenaming_below (fun mem => by have := doneBelow _ mem; omega) (by omega), doneLength]
        omega
      cases environmentsRest with
      | @cons _ environmentTail canonicalTail _ sourceLocation target _ headReference tail =>
        have droppedNext : ∀ i, canonicalTail[i]? = canonical[index + 1 + i]? := fun i => by
          rw [show index + 1 + i = index + (i + 1) by omega]
          exact dropped (i + 1)
        have pendingValuesNext : Pending (chainRenaming source pre.length done rest (index + 1))
            (pendingCopies source rest (index + 1))
            (pre ++ (processed ++ [.cellRef (OptionalCell.cellType type) target])) (copies ++ (pre ++ canonical)) := by
          rw [← List.append_assoc]
          refine pendingValues.shared (by rw [processedAt]; exact position) ?_
          rw [getElem?_append_shift copiesLength, canonicalAt]
          exact (dropped 0).symm
        have pendingTypesNext : Pending (chainRenaming source pre.length done rest (index + 1))
            (pendingCopies source rest (index + 1))
            (preContext ++ (processedContext ++ [.cell (OptionalCell.cellType type)]))
            (copyTypes ++ (preContext ++ (SourceCoreLocalCell.coreContext scope ++ administrativeContext))) := by
          rw [← List.append_assoc]
          refine pendingTypes.shared (by rw [processedContextAt]; exact position) ?_
          rw [getElem?_append_shift copyTypesLength]
          exact contextAt
        obtain ⟨copiesRest, finalHeap, finalCanonicalRest, finalActual, finalActualContext, finalStore, finalMap,
            finalWorld, finalRho, copyTail, envTail, slotsTail, finalHeaps, maps, worlds, frame, storePrefix,
            finalRead, lookups, types, finalTyped, agreement⟩ :=
          ih splitNext takenNextLength droppedNext doneLength doneBelowNext copiesLength copyTypesLength
            (by simp [processedLength]) (by simp [processedContextLength]) tail environmentsScope heaps read
            pendingValuesNext pendingTypesNext agrees respects currentTyped accepted
        refine ⟨(id, sourceLocation) :: copiesRest, finalHeap,
          .cellRef (OptionalCell.cellType type) target :: finalCanonicalRest, finalActual, finalActualContext,
          finalStore, finalMap, finalWorld, finalRho, .shared copied copyTail,
          .cons (headReference.extend maps worlds) envTail, ?_, finalHeaps, maps, worlds, frame, storePrefix,
          finalRead,
          ?_, ?_, finalTyped, agreement⟩
        · intro i below
          cases i with
          | zero => simp at below
          | succ i => exact slotsTail i (Nat.le_of_succ_le_succ below)
        · exact agree_of_eq (by simp) lookups
        · exact respects_of_eq (by simp [SourceCoreLocalCell.coreContext]) types
      | @internal _ _ canonicalTail _ target _ typed absent tail =>
        have droppedNext : ∀ i, canonicalTail[i]? = canonical[index + 1 + i]? := fun i => by
          rw [show index + 1 + i = index + (i + 1) by omega]
          exact dropped (i + 1)
        have pendingValuesNext : Pending (chainRenaming source pre.length done rest (index + 1))
            (pendingCopies source rest (index + 1))
            (pre ++ (processed ++ [.cellRef (OptionalCell.cellType type) target])) (copies ++ (pre ++ canonical)) := by
          rw [← List.append_assoc]
          refine pendingValues.shared (by rw [processedAt]; exact position) ?_
          rw [getElem?_append_shift copiesLength, canonicalAt]
          exact (dropped 0).symm
        have pendingTypesNext : Pending (chainRenaming source pre.length done rest (index + 1))
            (pendingCopies source rest (index + 1))
            (preContext ++ (processedContext ++ [.cell (OptionalCell.cellType type)]))
            (copyTypes ++ (preContext ++ (SourceCoreLocalCell.coreContext scope ++ administrativeContext))) := by
          rw [← List.append_assoc]
          refine pendingTypes.shared (by rw [processedContextAt]; exact position) ?_
          rw [getElem?_append_shift copyTypesLength]
          exact contextAt
        obtain ⟨copiesRest, finalHeap, finalCanonicalRest, finalActual, finalActualContext, finalStore, finalMap,
            finalWorld, finalRho, copyTail, envTail, slotsTail, finalHeaps, maps, worlds, frame, storePrefix,
            finalRead, lookups, types, finalTyped, agreement⟩ :=
          ih splitNext takenNextLength droppedNext doneLength doneBelowNext copiesLength copyTypesLength
            (by simp [processedLength]) (by simp [processedContextLength]) tail environmentsScope heaps read
            pendingValuesNext pendingTypesNext agrees respects currentTyped accepted
        refine ⟨copiesRest, finalHeap,
          .cellRef (OptionalCell.cellType type) target :: finalCanonicalRest, finalActual, finalActualContext,
          finalStore, finalMap, finalWorld, finalRho, copyTail,
          .internal (worlds.lookup typed) (copies_absent copyTail absent) envTail, ?_, finalHeaps, maps, worlds,
          frame, storePrefix, finalRead, ?_, ?_, finalTyped, agreement⟩
        · intro i below
          cases i with
          | zero => simp at below
          | succ i => exact slotsTail i (Nat.le_of_succ_le_succ below)
        · exact agree_of_eq (by simp) lookups
        · exact respects_of_eq (by simp [SourceCoreLocalCell.coreContext]) types
    | some binder =>
      obtain ⟨copy, continuation, copyAccepted, continuationAccepted, rfl⟩ := copyChain_copied copied accepted
      rw [chainRenaming_copied pre.length done rest index copied, pendingCopies_copied rest index copied]
        at pendingValues pendingTypes
      rw [chainRenaming_copied pre.length done rest index copied]
      have doneBelowNext : ∀ position ∈ done ++ [index + pre.length], position < index + 1 + pre.length := by
        intro position mem
        rw [List.mem_append, List.mem_singleton] at mem
        rcases mem with mem | rfl
        · have := doneBelow position mem
          omega
        · omega
      have position : chainRenaming source pre.length (done ++ [index + pre.length]) rest (index + 1)
          (index + pre.length) = pendingCopies source rest (index + 1) :=
        chainRenaming_copy doneBelow
      have readNext : ∀ (snapshot marker payload : Value),
          (store ++ [snapshot, marker, payload]).read? contextLocation =
            some (SourceCoreCallableIndexedFrames.encode layout native) := by
        intro snapshot marker payload
        show (store ++ [snapshot, marker, payload])[contextLocation]? = _
        rw [List.getElem?_append_left bound]
        exact read
      have snapshotTyped := SourceCoreCallableIndexedFrames.encode_runtime_typed world frameRegistered native
      cases environmentsRest with
      | @cons _ environmentTail canonicalTail _ sourceLocation target _ headReference tail =>
        have droppedNext : ∀ i, canonicalTail[i]? = canonical[index + 1 + i]? := fun i => by
          rw [show index + 1 + i = index + (i + 1) by omega]
          exact dropped (i + 1)
        obtain ⟨cell, value, payloadType, sourceRead, worldTyped, storeRead, cellRel⟩ :=
          heaps.cells headReference.mapped
        have samePayload : payloadType = type := by
          have same := Option.some.inj (worldTyped.symm.trans headReference.typed)
          simpa [OptionalCell.cellType] using same
        subst payloadType
        obtain ⟨payload, rfl⟩ := optional_of_typed (cells.runtime_hasType cellRel)
        obtain ⟨marker, markerType, markerTyped, evaluated⟩ := copy_evaluates copyAccepted sameDefinitions
          environmentsScope slotsAt frameAt read
          (by rw [getElem?_append_shift copiesLength, canonicalAt]; exact (dropped 0).symm) storeRead agrees
        obtain ⟨heapsNext, referenceNext⟩ := heap_allocate_copy heaps
          snapshotTyped markerTyped cellRel (Dynamic.Heap.AllocatesCopy.append)
        have pendingValuesNext : Pending
            (chainRenaming source pre.length (done ++ [index + pre.length]) rest (index + 1))
            (pendingCopies source rest (index + 1))
            (pre ++ (processed ++ [.cellRef (OptionalCell.cellType type) (store.length + 2)]))
            ((.cellRef (OptionalCell.cellType type) (store.length + 2) :: copies) ++ (pre ++ canonical)) := by
          rw [← List.append_assoc]
          exact pendingValues.copied (by rw [processedAt]; exact position) _
        have pendingTypesNext : Pending
            (chainRenaming source pre.length (done ++ [index + pre.length]) rest (index + 1))
            (pendingCopies source rest (index + 1))
            (preContext ++ (processedContext ++ [.cell (OptionalCell.cellType type)]))
            ((.cell (OptionalCell.cellType type) :: copyTypes) ++
              (preContext ++ (SourceCoreLocalCell.coreContext scope ++ administrativeContext))) := by
          rw [← List.append_assoc]
          exact pendingTypes.copied (by rw [processedContextAt]; exact position) _
        obtain ⟨copiesRest, finalHeap, finalCanonicalRest, finalActual, finalActualContext, finalStore, finalMap,
            finalWorld, finalRho, copyTail, envTail, slotsTail, finalHeaps, maps, worlds, frame, storePrefix,
            finalRead, lookups, types, finalTyped, agreement⟩ :=
          ih (mapping := mapping ++ [store.length + 2])
            (world := world ++ [layout.type, markerType, OptionalCell.cellType type])
            splitNext takenNextLength droppedNext (by simp [doneLength]) doneBelowNext (by simp [copiesLength])
            (by simp [copyTypesLength]) (by simp [processedLength]) (by simp [processedContextLength])
            (tail.extend ⟨_, rfl⟩ ⟨_, rfl⟩) (environmentsScope.extend ⟨_, rfl⟩ ⟨_, rfl⟩) heapsNext
            (readNext _ _ _) pendingValuesNext pendingTypesNext (agrees.lift _) (respects.lift _)
            (.cons (.cellRef referenceNext.typed) (currentTyped.weaken ⟨_, rfl⟩)) continuationAccepted
        refine ⟨(id, ⟨heap.cells.length⟩) :: copiesRest, finalHeap,
          .cellRef (OptionalCell.cellType type) (store.length + 2) :: finalCanonicalRest, finalActual,
          finalActualContext, finalStore, finalMap, finalWorld, finalRho,
          .copied copied sourceRead .append copyTail, .cons (referenceNext.extend maps worlds) envTail, ?_,
          finalHeaps, LocationMap.Extends.trans ⟨_, rfl⟩ maps, WorldExtends.trans ⟨_, rfl⟩ worlds,
          AdministrativePreserved.trans
            (CallableIndexedAllocationCompletion.allocation_frame mapping store _ _ _) frame,
          (by obtain ⟨suffix, storeEq⟩ := storePrefix; exact ⟨_, storeEq.trans (List.append_assoc _ _ _)⟩),
          finalRead, ?_, ?_, finalTyped, (PrefixAgreement.letE evaluated).trans agreement⟩
        · intro i below
          cases i with
          | zero => simp at below
          | succ i => exact slotsTail i (Nat.le_of_succ_le_succ below)
        · exact agree_of_eq (by simp) lookups
        · exact respects_of_eq (by simp [SourceCoreLocalCell.coreContext]) types
      | @internal _ _ canonicalTail _ target _ typed absent tail =>
        have droppedNext : ∀ i, canonicalTail[i]? = canonical[index + 1 + i]? := fun i => by
          rw [show index + 1 + i = index + (i + 1) by omega]
          exact dropped (i + 1)
        obtain ⟨value, storeRead, valueTyped⟩ := heaps.runtime_hasTypes.lookup typed
        obtain ⟨payload, rfl⟩ := optional_of_typed valueTyped
        obtain ⟨marker, markerType, markerTyped, evaluated⟩ := copy_evaluates copyAccepted sameDefinitions
          environmentsScope slotsAt frameAt read
          (by rw [getElem?_append_shift copiesLength, canonicalAt]; exact (dropped 0).symm) storeRead agrees
        obtain ⟨heapsNext, typedNext⟩ := heap_allocate_administrative heaps snapshotTyped markerTyped valueTyped
        have pendingValuesNext : Pending
            (chainRenaming source pre.length (done ++ [index + pre.length]) rest (index + 1))
            (pendingCopies source rest (index + 1))
            (pre ++ (processed ++ [.cellRef (OptionalCell.cellType type) (store.length + 2)]))
            ((.cellRef (OptionalCell.cellType type) (store.length + 2) :: copies) ++ (pre ++ canonical)) := by
          rw [← List.append_assoc]
          exact pendingValues.copied (by rw [processedAt]; exact position) _
        have pendingTypesNext : Pending
            (chainRenaming source pre.length (done ++ [index + pre.length]) rest (index + 1))
            (pendingCopies source rest (index + 1))
            (preContext ++ (processedContext ++ [.cell (OptionalCell.cellType type)]))
            ((.cell (OptionalCell.cellType type) :: copyTypes) ++
              (preContext ++ (SourceCoreLocalCell.coreContext scope ++ administrativeContext))) := by
          rw [← List.append_assoc]
          exact pendingTypes.copied (by rw [processedContextAt]; exact position) _
        obtain ⟨copiesRest, finalHeap, finalCanonicalRest, finalActual, finalActualContext, finalStore, finalMap,
            finalWorld, finalRho, copyTail, envTail, slotsTail, finalHeaps, maps, worlds, frame, storePrefix,
            finalRead, lookups, types, finalTyped, agreement⟩ :=
          ih (mapping := mapping) (world := world ++ [layout.type, markerType, OptionalCell.cellType type])
            splitNext takenNextLength droppedNext (by simp [doneLength]) doneBelowNext (by simp [copiesLength])
            (by simp [copyTypesLength]) (by simp [processedLength]) (by simp [processedContextLength])
            (tail.extend (LocationMap.Extends.refl _) ⟨_, rfl⟩)
            (environmentsScope.extend (LocationMap.Extends.refl _) ⟨_, rfl⟩) heapsNext
            (readNext _ _ _) pendingValuesNext pendingTypesNext (agrees.lift _) (respects.lift _)
            (.cons (.cellRef typedNext) (currentTyped.weaken ⟨_, rfl⟩)) continuationAccepted
        refine ⟨copiesRest, finalHeap,
          .cellRef (OptionalCell.cellType type) (store.length + 2) :: finalCanonicalRest, finalActual,
          finalActualContext, finalStore, finalMap, finalWorld, finalRho, copyTail,
          .internal (worlds.lookup typedNext) (copies_absent copyTail absent) envTail, ?_,
          finalHeaps, maps, WorldExtends.trans ⟨_, rfl⟩ worlds,
          AdministrativePreserved.trans (administrative_append mapping store _ _ _) frame,
          (by obtain ⟨suffix, storeEq⟩ := storePrefix; exact ⟨_, storeEq.trans (List.append_assoc _ _ _)⟩),
          finalRead, ?_, ?_, finalTyped, (PrefixAgreement.letE evaluated).trans agreement⟩
        · intro i below
          cases i with
          | zero => simp at below
          | succ i => exact slotsTail i (Nat.le_of_succ_le_succ below)
        · exact agree_of_eq (by simp) lookups
        · exact respects_of_eq (by simp [SourceCoreLocalCell.coreContext]) types

/-- The marked copies of a scope in any cell model: the source copies the same
bindings, the heap and lexical relations extend to the copies, the frame cell
keeps its value, and the copies' continuation agrees with the whole in both
directions. Slots past the scope keep their canonical values. -/
theorem marked_copies_prefix_cells
    {catalog : SourceCoreDataCatalog.Catalog}
    {definitions : DataEnvironment} {cells : GenericHeap.CellModel definitions}
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {source : TypedSource} {mapping : LocationMap} {world : StoreTyping}
    {administrativeContext preContext actualContext : Core.Context} {scope : SourceCoreLocalCell.Scope}
    {environment : Dynamic.Environment} {pre canonical actual : Environment}
    {heap : Dynamic.Heap} {store : Store} {ξ : Renaming} {body emitted : Expr}
    {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame}
    (accepted : SourceCoreSourceCells.copyScope
      (some (SourceCoreCallableIndexedAllocationFrames.allocator layout globals
        (layouts.allocatorAt owner active onError)))
      source scope (· + pre.length) body = .ok emitted)
    (sameDefinitions : layouts.definitions = definitions) (frameRegistered : layout.Registered definitions)
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment
      canonical definitions)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world heap store)
    (actualLayout : EnvironmentsAgree ξ (pre ++ canonical) actual)
    (preLength : preContext.length = pre.length)
    (types : Renaming.Respects ξ
      (preContext ++ (SourceCoreLocalCell.coreContext scope ++ administrativeContext)) actualContext)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef layout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native)) :
    ∃ copies finalHeap finalCanonical finalActual finalActualContext finalStore finalMap finalWorld
      finalEmbedding,
      Dynamic.EnvironmentCopies source environment heap copies finalHeap ∧
      DataHeap.EnvRepresents catalog finalMap finalWorld administrativeContext scope copies
        finalCanonical definitions ∧
      (∀ index, scope.length ≤ index → finalCanonical[index]? = canonical[index]?) ∧
      GenericHeap.CellHeapRepresents cells finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ (∃ suffix, finalStore = store ++ suffix) ∧
      finalStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native) ∧
      EnvironmentsAgree finalEmbedding (pre ++ finalCanonical) finalActual ∧
      Renaming.Respects finalEmbedding
        (preContext ++ (SourceCoreLocalCell.coreContext scope ++ administrativeContext)) finalActualContext ∧
      RuntimeEnvironmentHasTypes finalWorld finalActual finalActualContext definitions ∧
      PrefixAgreement actual store (emitted.rename ξ) finalActual finalStore (body.rename finalEmbedding) := by
  have positions : ∀ position, position < pre.length →
      chainRenaming source pre.length [] scope 0 position = position + pendingCopies source scope 0 := by
    intro position below
    rw [chainRenaming_not_mem (List.not_mem_nil) (fun slot _ => by omega)]
    simp
  have pendingValues : Pending (chainRenaming source pre.length [] scope 0) (pendingCopies source scope 0)
      (pre ++ []) ([] ++ (pre ++ canonical)) := by
    intro position value found
    rw [List.append_nil] at found
    have below : position < pre.length := (List.getElem?_eq_some_iff.mp found).1
    exact ⟨position, positions position below, by rw [List.nil_append, List.getElem?_append_left below]; exact found⟩
  have pendingTypes : Pending (chainRenaming source pre.length [] scope 0) (pendingCopies source scope 0)
      (preContext ++ []) ([] ++ (preContext ++ (SourceCoreLocalCell.coreContext scope ++ administrativeContext))) := by
    intro position type found
    rw [List.append_nil] at found
    have below : position < preContext.length := (List.getElem?_eq_some_iff.mp found).1
    exact ⟨position, positions position (by omega),
      by rw [List.nil_append, List.getElem?_append_left below]; exact found⟩
  obtain ⟨copies, finalHeap, finalCanonical, finalActual, finalActualContext, finalStore, finalMap, finalWorld,
      finalRho, copy, finalEnvironments, slots, finalHeaps, maps, worlds, frame, storePrefix, finalRead, lookups,
      types, finalTyped, agreement⟩ :=
    marked_chain_prefix sameDefinitions frameRegistered reference preLength scope (taken := [])
      (done := []) (copies := []) (copyTypes := []) (processed := []) (processedContext := []) rfl rfl
      (fun i => by simp) rfl (fun _ mem => absurd mem List.not_mem_nil) rfl rfl rfl rfl environments
      (scope_environments environments) heaps read pendingValues pendingTypes actualLayout types actualTyped
      accepted
  refine ⟨copies, finalHeap, finalCanonical, finalActual, finalActualContext, finalStore, finalMap, finalWorld,
    Renaming.comp finalRho (chainRenaming source pre.length [] scope 0), copy, finalEnvironments, slots,
    finalHeaps, maps, worlds, frame, storePrefix, finalRead, agree_of_eq (by simp) lookups,
    respects_of_eq (by simp) types,
    finalTyped, ?_⟩
  rw [chainRenaming_scope, ← Expr.rename_comp]
  exact agreement

/-- The marked copies of a scope: the source copies the same bindings, the
heap and lexical relations extend to the copies, the frame cell keeps its
value, and the copies' continuation agrees with the whole in both directions.
Slots past the scope keep their canonical values. -/
theorem marked_copies_prefix
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {source : TypedSource} {mapping : LocationMap} {world : StoreTyping}
    {administrativeContext preContext actualContext : Core.Context} {scope : SourceCoreLocalCell.Scope}
    {environment : Dynamic.Environment} {pre canonical actual : Environment}
    {heap : Dynamic.Heap} {store : Store} {ξ : Renaming} {body emitted : Expr}
    {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame}
    (accepted : SourceCoreSourceCells.copyScope
      (some (SourceCoreCallableIndexedAllocationFrames.allocator layout globals
        (layouts.allocatorAt owner active onError)))
      source scope (· + pre.length) body = .ok emitted)
    (sameDefinitions : layouts.definitions = definitions) (frameRegistered : layout.Registered definitions)
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment
      canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (actualLayout : EnvironmentsAgree ξ (pre ++ canonical) actual)
    (preLength : preContext.length = pre.length)
    (types : Renaming.Respects ξ
      (preContext ++ (SourceCoreLocalCell.coreContext scope ++ administrativeContext)) actualContext)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef layout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native)) :
    ∃ copies finalHeap finalCanonical finalActual finalActualContext finalStore finalMap finalWorld
      finalEmbedding,
      Dynamic.EnvironmentCopies source environment heap copies finalHeap ∧
      DataHeap.EnvRepresents catalog finalMap finalWorld administrativeContext scope copies
        finalCanonical definitions ∧
      (∀ index, scope.length ≤ index → finalCanonical[index]? = canonical[index]?) ∧
      GenericHeap.HeapRepresents model finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      finalStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native) ∧
      EnvironmentsAgree finalEmbedding (pre ++ finalCanonical) finalActual ∧
      Renaming.Respects finalEmbedding
        (preContext ++ (SourceCoreLocalCell.coreContext scope ++ administrativeContext)) finalActualContext ∧
      RuntimeEnvironmentHasTypes finalWorld finalActual finalActualContext definitions ∧
      PrefixAgreement actual store (emitted.rename ξ) finalActual finalStore (body.rename finalEmbedding) := by
  obtain ⟨copies, finalHeap, finalCanonical, finalActual, finalActualContext, finalStore, finalMap, finalWorld,
      finalEmbedding, copy, finalEnvironments, slots, finalHeaps, maps, worlds, frame, _storePrefix, rest⟩ :=
    marked_copies_prefix_cells (cells := GenericHeap.CellModel.ordinary model) accepted sameDefinitions
      frameRegistered environments (GenericHeap.ordinaryHeap_iff.mpr heaps) actualLayout preLength types
      actualTyped reference read
  exact ⟨copies, finalHeap, finalCanonical, finalActual, finalActualContext, finalStore, finalMap, finalWorld,
    finalEmbedding, copy, finalEnvironments, slots, GenericHeap.ordinaryHeap_iff.mp finalHeaps, maps, worlds, frame,
    rest⟩

end Solcore.SourceSemantics.CoreLowering.CaptureCopies
