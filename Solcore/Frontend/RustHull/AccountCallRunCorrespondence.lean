import Solcore.Frontend.RustHull.AccountCallCheckpointCorrespondence

/-! An absent ordinary account uses the actual default record, whose code
identity is zero. An incomplete world instead produces the existing reason 7. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.AccountCallCorrespondence
open Core Correspondence ScalarExecution CodeBuilder CallTransportCorrespondence

theorem isPrecompile_evaluates {depth : Nat} {environment : Core.Environment} {store : Core.Store}
    {targetCode : Code} {target : Core.Word}
    (related : CodeValue depth environment targetCode (.word target)) :
    Core.Evaluates environment store (AccountRuntime.isPrecompile targetCode depth)
      (.bool (AccountCallSemantics.isPrecompile target)) store := by
  by_cases special : target == Word.ofNatModulo 256
  · simp only [AccountCallSemantics.isPrecompile, special, Bool.true_or]
    exact .ifTrue (.binary (related.evaluates store) .word (by
      change some (Core.Value.bool (target == Word.ofNatModulo 256)) = some (Core.Value.bool true)
      rw [special])) .bool
  have specialFalse : (target == Word.ofNatModulo 256) = false := Bool.eq_false_iff.mpr special
  by_cases positive : target > Word.zero
  · simp only [AccountCallSemantics.isPrecompile, specialFalse, Bool.false_or, positive, decide_true, Bool.true_and]
    exact .ifFalse (.binary (related.evaluates store) .word (by
      change some (Core.Value.bool (target == Word.ofNatModulo 256)) = some (Core.Value.bool false)
      rw [specialFalse]))
      (.ifTrue (.binary (related.evaluates store) .word (by change some (Core.Value.bool (decide (target > Word.zero))) = some (Core.Value.bool _); simp only [positive, decide_true]))
        (.binary .word (related.evaluates store) rfl))
  · simp only [AccountCallSemantics.isPrecompile, specialFalse, Bool.false_or, positive, decide_false, Bool.false_and]
    exact .ifFalse (.binary (related.evaluates store) .word (by
      change some (Core.Value.bool (target == Word.ofNatModulo 256)) = some (Core.Value.bool false)
      rw [specialFalse]))
      (.ifFalse (.binary (related.evaluates store) .word (by change some (Core.Value.bool (decide (target > Word.zero))) = some (Core.Value.bool _); simp only [positive, decide_false])) .bool)

def accountRun (shared : AccountRuntime.References) (target precompiled : Code) (child : Code → Code) : Code :=
  choose (AccountRuntime.isPrecompile target) precompiled <|
  bindResult Calls.responseType (AccountRuntime.worldGet shared target) fun record =>
    choose (binary .wordEq (part 3 9 record) (number 0))
      (choose (part 6 9 record)
        (choose (binary .wordEq (part 5 9 record) (number 0))
          (AccountRuntime.callResult (CodeBuilder.boolean true) empty (number 0))
          (failure Calls.responseType (number 16)))
        (failure Calls.responseType (number 15)))
      (child record)

def emptyRunResult (complete : Bool) : Core.Value :=
  if complete then .inRight .word (responseValue (AccountCallSemantics.emptyResponse true))
  else .inLeft Calls.responseType (.word (Word.ofNatModulo 7))

theorem accountRun_absent_evaluates {depth : Nat} {environment : Core.Environment} {initial : Core.Store}
    {shared : AccountRuntime.References} {targetCode precompiled : Code} {child : Code → Code}
    {locations : SharedLocations} {target : Core.Word} {accounts : StorageCorrespondence.Accounts} {complete : Bool}
    (references : SharedReferences depth environment shared locations)
    (argument : CodeValue depth environment targetCode (.word target))
    (worldRead : initial.read? locations.world = some (StorageCorrespondence.world accounts))
    (completeRead : initial.read? locations.complete = some (.bool complete))
    (ordinary : AccountCallSemantics.isPrecompile target = false)
    (absent : StorageCorrespondence.lookup target accounts = none) :
    Core.Evaluates environment initial (accountRun shared targetCode precompiled child depth)
      (emptyRunResult complete) (StorageCorrespondence.getStore accounts target complete environment initial) := by
  have fetched := StorageCorrespondence.get_evaluates accounts target complete
    (.loadCell (references.world.evaluates initial) worldRead) (argument.evaluates initial)
    (.loadCell (references.complete.evaluates initial) completeRead)
  apply Core.Evaluates.ifFalse (by simpa only [ordinary] using isPrecompile_evaluates argument)
  cases complete with
  | false =>
      simp only [StorageCorrespondence.get, absent, Bool.false_eq_true, ↓reduceIte,
        StorageCorrespondence.getValue] at fetched
      exact LanguageResult.bind_failure Calls.responseType fetched
  | true =>
      simp only [StorageCorrespondence.get, absent, ↓reduceIte, StorageCorrespondence.getValue] at fetched
      apply LanguageResult.bind_success Calls.responseType fetched
      have recordValue := CodeValue.bound depth environment (StorageCorrespondence.record {address := target} 0)
      apply Core.Evaluates.ifTrue (.binary ((recordValue.part (index := 3) rfl).evaluates _) .word rfl)
      apply Core.Evaluates.ifTrue ((recordValue.part (index := 6) rfl).evaluates _)
      apply Core.Evaluates.ifTrue (.binary ((recordValue.part (index := 5) rfl).evaluates _) .word rfl)
      exact .inRight (.pair .bool (.pair (.construct .unit) .word))

theorem accountRun_absent {depth : Nat} {environment : Core.Environment} {initial : Core.Store}
    {shared : AccountRuntime.References} {targetCode precompiled : Code} {child : Code → Code}
    {locations : SharedLocations} {target : Core.Word} {state : AccountCallSemantics.Shared}
    (references : SharedReferences depth environment shared locations)
    (argument : CodeValue depth environment targetCode (.word target))
    (related : SharedStateRel locations state initial)
    (ordinary : AccountCallSemantics.isPrecompile target = false)
    (absent : StorageSemantics.lookup target state.world = none) :
    ∃ final, Core.Evaluates environment initial (accountRun shared targetCode precompiled child depth)
      (emptyRunResult state.complete) final ∧ StoreRetains initial final := by
  obtain ⟨accounts, worldSame, worldRead⟩ := related.world
  have lookupAbsent : StorageCorrespondence.lookup target accounts = none := by
    have found := StorageCorrespondence.lookup_source accounts target
    rw [worldSame, absent] at found
    cases actual : StorageCorrespondence.lookup target accounts with
    | none => rfl
    | some value => simp only [actual, Option.map_some] at found; contradiction
  have fetched := StorageCorrespondence.get_evaluates accounts target state.complete
    (.loadCell (references.world.evaluates initial) worldRead) (argument.evaluates initial)
    (.loadCell (references.complete.evaluates initial) related.complete)
  refine ⟨StorageCorrespondence.getStore accounts target state.complete environment initial, ?_, StoreRetains.append _ _⟩
  apply Core.Evaluates.ifFalse (by simpa only [ordinary] using isPrecompile_evaluates argument)
  cases complete : state.complete with
  | false =>
      simp only [StorageCorrespondence.get, lookupAbsent, complete, Bool.false_eq_true, ↓reduceIte,
        StorageCorrespondence.getValue] at fetched
      exact LanguageResult.bind_failure Calls.responseType fetched
  | true =>
      simp only [StorageCorrespondence.get, lookupAbsent, complete, ↓reduceIte, StorageCorrespondence.getValue] at fetched
      apply LanguageResult.bind_success Calls.responseType fetched
      have recordValue := CodeValue.bound depth environment (StorageCorrespondence.record {address := target} 0)
      apply Core.Evaluates.ifTrue (.binary ((recordValue.part (index := 3) rfl).evaluates _) .word rfl)
      apply Core.Evaluates.ifTrue ((recordValue.part (index := 6) rfl).evaluates _)
      apply Core.Evaluates.ifTrue (.binary ((recordValue.part (index := 5) rfl).evaluates _) .word rfl)
      exact .inRight (.pair .bool (.pair (.construct .unit) .word))

end Solcore.Frontend.RustHull.AccountCallCorrespondence
