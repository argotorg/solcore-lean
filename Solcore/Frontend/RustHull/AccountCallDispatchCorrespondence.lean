import Solcore.Frontend.RustHull.AccountCallCheckpointCorrespondence
import Solcore.Frontend.RustHull.AccountCallTransferCorrespondence
import Solcore.Frontend.RustHull.AccountCallRunCorrespondence

/-! Independent account dispatch reaches the actual checkpoint, funds check,
and world lookup before a child closure would be selected. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.AccountCallCorrespondence
open Core Correspondence ScalarExecution CodeBuilder CallTransportCorrespondence

def extendedValue (source : Core.Word) (request : AccountCallSemantics.Request) : Core.Value :=
  bundleValues [requestValue request, .word Core.Word.zero, .word source]

theorem dispatch_insufficient {depth : Nat} {environment : Core.Environment} {initial : Core.Store}
    {shared : AccountRuntime.References} {runFrame : Code → Code → Code} {extended : Code}
    {locations : SharedLocations} {source : Core.Word} {request : AccountCallSemantics.Request}
    {state : AccountCallSemantics.Shared}
    (references : SharedReferences depth environment shared locations)
    (argument : CodeValue depth environment extended (extendedValue source request))
    (related : SharedStateRel locations state initial)
    (shortfall : request.value > StorageSemantics.readWord source state.balances) :
    ∃ final, Core.Evaluates environment initial (AccountRuntime.dispatch shared runFrame extended depth)
      (.inRight .word (responseValue (AccountCallSemantics.emptyResponse false))) final ∧
      StoreRetains initial final := by
  obtain ⟨accounts, worldSame, worldRead⟩ := related.world
  let saved : Core.Environment := [WordMapping.encode state.balances, .word state.logSize,
    WordMapping.encode state.logs, StorageCorrespondence.world accounts]
  have innerReferences := references.prepend saved
  have innerArgument := argument.prepend saved
  have sourceCode : CodeValue (depth + 4) (saved ++ environment) (part 2 3 extended) (.word source) :=
    innerArgument.part (index := 2) rfl
  obtain ⟨final, looked, retained⟩ := lookup_preserves
    (.loadCell (innerReferences.balances.evaluates initial) related.balances) (sourceCode.evaluates initial)
  refine ⟨final, ?_, retained⟩
  apply checkpoint_evaluates references worldRead related.logs related.logSize related.balances
  apply LanguageResult.bind_success Calls.responseType looked
  have afterArgument := innerArgument.prepend [.word (StorageSemantics.readWord source state.balances)]
  have modeCode := afterArgument.part (index := 1) rfl
  have requestCode := afterArgument.part (index := 0) rfl
  have valueCode := requestCode.part (index := 2) rfl
  apply Core.Evaluates.ifTrue
  · apply Core.Evaluates.ifFalse (.binary (modeCode.evaluates final) .word rfl)
    exact .binary (valueCode.evaluates final)
      ((CodeValue.bound (depth + 4) (saved ++ environment)
        (.word (StorageSemantics.readWord source state.balances))).evaluates final)
      (by simp [BinaryOp.apply, shortfall])
  · exact .inRight (.pair .bool (.pair (.construct .unit) .word))

theorem dispatch_transferFault {depth : Nat} {environment : Core.Environment} {initial : Core.Store}
    {shared : AccountRuntime.References} {runFrame : Code → Code → Code} {extended : Code}
    {locations : SharedLocations} {source : Core.Word} {request : AccountCallSemantics.Request}
    {state : AccountCallSemantics.Shared} {reason : Core.Word}
    (references : SharedReferences depth environment shared locations)
    (argument : CodeValue depth environment extended (extendedValue source request))
    (related : SharedStateRel locations state initial)
    (funds : ¬ request.value > StorageSemantics.readWord source state.balances)
    (failed : AccountCallSemantics.transfer source request.target request.value state.balances = .error reason) :
    ∃ final, Core.Evaluates environment initial (AccountRuntime.dispatch shared runFrame extended depth)
      (.inLeft Calls.responseType (.word reason)) final ∧
      SharedStateRel locations state final ∧ BalanceFrame locations.balances initial final := by
  obtain ⟨accounts, worldSame, worldRead⟩ := related.world
  let saved : Core.Environment := [WordMapping.encode state.balances, .word state.logSize,
    WordMapping.encode state.logs, StorageCorrespondence.world accounts]
  have innerReferences := references.prepend saved
  have innerArgument := argument.prepend saved
  obtain ⟨first, looked, retained⟩ := lookup_preserves
    (.loadCell (innerReferences.balances.evaluates initial) related.balances)
    ((innerArgument.part (index := 2) rfl).evaluates initial)
  let sourceBalance := StorageSemantics.readWord source state.balances
  let extra := .word sourceBalance :: saved
  have afterArgument := argument.prepend extra
  have requestCode := afterArgument.part (index := 0) rfl
  obtain ⟨final, moved, balanceFinal, frame⟩ := transfer_preserves ((references.balances.prepend extra))
    (afterArgument.part (index := 2) rfl) (requestCode.part (index := 0) rfl) (requestCode.part (index := 2) rfl)
    (retained_read retained related.balances)
  rw [failed] at moved balanceFinal
  have combined := (BalanceFrame.ofRetains retained).trans frame
  have finalRelated := related.balances_updated combined balanceFinal
  refine ⟨final, ?_, finalRelated, combined⟩
  apply checkpoint_evaluates references worldRead related.logs related.logSize related.balances
  apply LanguageResult.bind_success Calls.responseType looked
  apply Core.Evaluates.ifFalse
  · apply Core.Evaluates.ifFalse (.binary ((afterArgument.part (index := 1) rfl).evaluates first) .word rfl)
    exact .binary ((requestCode.part (index := 2) rfl).evaluates first)
      ((CodeValue.bound (depth + 4) (saved ++ environment) (.word sourceBalance)).evaluates first)
      (by simp [BinaryOp.apply, sourceBalance, funds])
  apply LanguageResult.bind_failure Calls.responseType
  exact .ifTrue (.binary ((afterArgument.part (index := 1) rfl).evaluates first) .word rfl) moved

theorem dispatch_empty {depth : Nat} {environment : Core.Environment} {initial : Core.Store}
    {shared : AccountRuntime.References} {runFrame : Code → Code → Code} {extended : Code}
    {locations : SharedLocations} {source : Core.Word} {request : AccountCallSemantics.Request}
    {state : AccountCallSemantics.Shared} {balances : StorageSemantics.Words}
    (references : SharedReferences depth environment shared locations)
    (argument : CodeValue depth environment extended (extendedValue source request))
    (related : SharedStateRel locations state initial)
    (funds : ¬ request.value > StorageSemantics.readWord source state.balances)
    (moved : AccountCallSemantics.transfer source request.target request.value state.balances = .ok balances)
    (ordinary : AccountCallSemantics.isPrecompile request.target = false)
    (absent : StorageSemantics.lookup request.target state.world = none)
    (complete : state.complete = true) :
    ∃ final, Core.Evaluates environment initial (AccountRuntime.dispatch shared runFrame extended depth)
      (.inRight .word (responseValue (AccountCallSemantics.emptyResponse true))) final ∧
      SharedStateRel locations {state with balances := balances} final ∧ BalanceFrame locations.balances initial final := by
  obtain ⟨accounts, worldSame, worldRead⟩ := related.world
  have lookupAbsent : StorageCorrespondence.lookup request.target accounts = none := by
    have found := StorageCorrespondence.lookup_source accounts request.target
    rw [worldSame, absent] at found
    cases actual : StorageCorrespondence.lookup request.target accounts with
    | none => rfl
    | some value => simp only [actual, Option.map_some] at found; contradiction
  let saved : Core.Environment := [WordMapping.encode state.balances, .word state.logSize,
    WordMapping.encode state.logs, StorageCorrespondence.world accounts]
  have innerReferences := references.prepend saved
  have innerArgument := argument.prepend saved
  obtain ⟨first, looked, retained⟩ := lookup_preserves
    (.loadCell (innerReferences.balances.evaluates initial) related.balances)
    ((innerArgument.part (index := 2) rfl).evaluates initial)
  let sourceBalance := StorageSemantics.readWord source state.balances
  let extra := .word sourceBalance :: saved
  have afterArgument := argument.prepend extra
  have requestCode := afterArgument.part (index := 0) rfl
  obtain ⟨transferred, transferEvaluated, balanceFinal, transferFrame⟩ := transfer_preserves (references.balances.prepend extra)
    (afterArgument.part (index := 2) rfl) (requestCode.part (index := 0) rfl) (requestCode.part (index := 2) rfl)
    (retained_read retained related.balances)
  rw [moved] at transferEvaluated balanceFinal
  have combined := (BalanceFrame.ofRetains retained).trans transferFrame
  have transferredRelated : SharedStateRel locations {state with balances := balances} transferred :=
    related.balances_updated combined balanceFinal
  have distinct := related.distinct
  simp only [SharedLocations.all, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at distinct
  have worldFinal : transferred.read? locations.world = some (StorageCorrespondence.world accounts) :=
    (combined.other locations.world distinct.1.2.2.1 (List.getElem?_eq_some_iff.mp worldRead).1).trans worldRead
  let runExtra := .unit :: extra
  let runEnv := runExtra ++ environment
  let final := StorageCorrespondence.getStore accounts request.target true runEnv transferred
  have runRetained : StoreRetains transferred final := StoreRetains.append _ _
  refine ⟨final, ?_, transferredRelated.retained runRetained, combined.trans (.ofRetains runRetained)⟩
  apply checkpoint_evaluates references worldRead related.logs related.logSize related.balances
  apply LanguageResult.bind_success Calls.responseType looked
  apply Core.Evaluates.ifFalse
  · apply Core.Evaluates.ifFalse (.binary ((afterArgument.part (index := 1) rfl).evaluates first) .word rfl)
    exact .binary ((requestCode.part (index := 2) rfl).evaluates first)
      ((CodeValue.bound (depth + 4) (saved ++ environment) (.word sourceBalance)).evaluates first)
      (by simp [BinaryOp.apply, sourceBalance, funds])
  apply LanguageResult.bind_success Calls.responseType
    (.ifTrue (.binary ((afterArgument.part (index := 1) rfl).evaluates first) .word rfl) transferEvaluated)
  apply Core.Evaluates.caseRight
  · exact accountRun_absent_evaluates (references.prepend runExtra)
      (((argument.prepend runExtra).part (index := 0) rfl).part (index := 0) rfl) worldFinal
      (by simpa only [complete] using transferredRelated.complete) ordinary lookupAbsent
  have response := CodeValue.bound (depth + 6) runEnv (responseValue (AccountCallSemantics.emptyResponse true))
  exact .ifTrue ((response.part (index := 0) rfl).evaluates final) (.inRight (response.evaluates final))

theorem dispatch_unavailable {depth : Nat} {environment : Core.Environment} {initial : Core.Store}
    {shared : AccountRuntime.References} {runFrame : Code → Code → Code} {extended : Code}
    {locations : SharedLocations} {source : Core.Word} {request : AccountCallSemantics.Request}
    {state : AccountCallSemantics.Shared} {balances : StorageSemantics.Words}
    (references : SharedReferences depth environment shared locations)
    (argument : CodeValue depth environment extended (extendedValue source request))
    (related : SharedStateRel locations state initial)
    (funds : ¬ request.value > StorageSemantics.readWord source state.balances)
    (moved : AccountCallSemantics.transfer source request.target request.value state.balances = .ok balances)
    (ordinary : AccountCallSemantics.isPrecompile request.target = false)
    (absent : StorageSemantics.lookup request.target state.world = none)
    (incomplete : state.complete = false) :
    ∃ final, Core.Evaluates environment initial (AccountRuntime.dispatch shared runFrame extended depth)
      (.inLeft Calls.responseType (.word (Core.Word.ofNatModulo 7))) final ∧
      SharedStateRel locations state final ∧ BalanceFrame locations.balances initial final := by
  obtain ⟨accounts, worldSame, worldRead⟩ := related.world
  have lookupAbsent : StorageCorrespondence.lookup request.target accounts = none := by
    have found := StorageCorrespondence.lookup_source accounts request.target
    rw [worldSame, absent] at found
    cases actual : StorageCorrespondence.lookup request.target accounts with
    | none => rfl
    | some value => simp only [actual, Option.map_some] at found; contradiction
  let saved : Core.Environment := [WordMapping.encode state.balances, .word state.logSize,
    WordMapping.encode state.logs, StorageCorrespondence.world accounts]
  have innerReferences := references.prepend saved
  have innerArgument := argument.prepend saved
  obtain ⟨first, looked, retained⟩ := lookup_preserves
    (.loadCell (innerReferences.balances.evaluates initial) related.balances)
    ((innerArgument.part (index := 2) rfl).evaluates initial)
  let sourceBalance := StorageSemantics.readWord source state.balances
  let extra := .word sourceBalance :: saved
  have afterArgument := argument.prepend extra
  have requestCode := afterArgument.part (index := 0) rfl
  obtain ⟨transferred, transferEvaluated, balanceFinal, transferFrame⟩ := transfer_preserves (references.balances.prepend extra)
    (afterArgument.part (index := 2) rfl) (requestCode.part (index := 0) rfl) (requestCode.part (index := 2) rfl)
    (retained_read retained related.balances)
  rw [moved] at transferEvaluated balanceFinal
  have combined := (BalanceFrame.ofRetains retained).trans transferFrame
  have transferredRelated : SharedStateRel locations {state with balances := balances} transferred :=
    related.balances_updated combined balanceFinal
  have distinct := related.distinct
  simp only [SharedLocations.all, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at distinct
  have worldFinal : transferred.read? locations.world = some (StorageCorrespondence.world accounts) :=
    (combined.other locations.world distinct.1.2.2.1 (List.getElem?_eq_some_iff.mp worldRead).1).trans worldRead
  let runExtra := .unit :: extra
  let runEnv := runExtra ++ environment
  let runStore := StorageCorrespondence.getStore accounts request.target false runEnv transferred
  have runRetained : StoreRetains transferred runStore := StoreRetains.append _ _
  have runRelated := transferredRelated.retained runRetained
  let final := runStore.set locations.balances (WordMapping.encode state.balances)
  have restoredFrame := BalanceFrame.write locations.balances runStore (WordMapping.encode state.balances)
  have totalFrame := (combined.trans (.ofRetains runRetained)).trans restoredFrame
  have finalBalance : Core.Store.read? final locations.balances = some (WordMapping.encode state.balances) := by
    exact List.getElem?_set_self (List.getElem?_eq_some_iff.mp runRelated.balances).1
  refine ⟨final, ?_, related.balances_updated totalFrame finalBalance, totalFrame⟩
  apply checkpoint_evaluates references worldRead related.logs related.logSize related.balances
  apply LanguageResult.bind_success Calls.responseType looked
  apply Core.Evaluates.ifFalse
  · apply Core.Evaluates.ifFalse (.binary ((afterArgument.part (index := 1) rfl).evaluates first) .word rfl)
    exact .binary ((requestCode.part (index := 2) rfl).evaluates first)
      ((CodeValue.bound (depth + 4) (saved ++ environment) (.word sourceBalance)).evaluates first)
      (by simp [BinaryOp.apply, sourceBalance, funds])
  apply LanguageResult.bind_success Calls.responseType
    (.ifTrue (.binary ((afterArgument.part (index := 1) rfl).evaluates first) .word rfl) transferEvaluated)
  apply Core.Evaluates.caseLeft
  · exact accountRun_absent_evaluates (references.prepend runExtra)
      (((argument.prepend runExtra).part (index := 0) rfl).part (index := 0) rfl) worldFinal
      (by simpa only [incomplete] using transferredRelated.complete) ordinary lookupAbsent
  have restored := checkpointRestore_evaluates (balances := WordMapping.encode state.balances) references
    [.word (Core.Word.ofNatModulo 7), .unit, .word sourceBalance]
    (retained_read runRetained worldFinal) runRelated.logs runRelated.logSize runRelated.balances related.distinct
  apply Core.Evaluates.letE restored
  exact .inLeft (((CodeValue.bound (depth + 6) runEnv (.word (Core.Word.ofNatModulo 7))).prepend [.unit]).evaluates final)

theorem transferFor_error {source : Core.Word} {request : AccountCallSemantics.Request}
    {state : AccountCallSemantics.Shared} {reason : Core.Word}
    (failed : AccountCallSemantics.transferFor .ordinary source request state = .error reason) :
    AccountCallSemantics.transfer source request.target request.value state.balances = .error reason := by
  simp only [AccountCallSemantics.transferFor,
    show (AccountCallSemantics.Mode.ordinary == .ordinary) = true from rfl, ↓reduceIte] at failed
  cases actual : AccountCallSemantics.transfer source request.target request.value state.balances with
  | error why =>
    simp [actual, Except.map] at failed
    exact congrArg Except.error failed
  | ok balances => simp [actual, Except.map] at failed

theorem transferFor_ok {source : Core.Word} {request : AccountCallSemantics.Request}
    {state transferred : AccountCallSemantics.Shared}
    (moved : AccountCallSemantics.transferFor .ordinary source request state = .ok transferred) :
    ∃ balances, AccountCallSemantics.transfer source request.target request.value state.balances = .ok balances ∧
      transferred = {state with balances := balances} := by
  simp only [AccountCallSemantics.transferFor,
    show (AccountCallSemantics.Mode.ordinary == .ordinary) = true from rfl, ↓reduceIte] at moved
  cases actual : AccountCallSemantics.transfer source request.target request.value state.balances with
  | error why => simp [actual, Except.map] at moved
  | ok balances =>
    simp [actual, Except.map] at moved
    exact ⟨balances, rfl, moved.symm⟩

/-- The independent dispatch derivation selects the real checkpoint, transfer,
world lookup and restoration branches. The retained helper allocations remain
part of the final store. -/
theorem dispatch_preserves {depth : Nat} {environment : Core.Environment} {initial : Core.Store}
    {shared : AccountRuntime.References} {runFrame : Code → Code → Code} {extended : Code}
    {locations : SharedLocations} {source : Core.Word} {request : AccountCallSemantics.Request}
    {state finalState : AccountCallSemantics.Shared} {result : Semantics.Result AccountCallSemantics.Response}
    (references : SharedReferences depth environment shared locations)
    (argument : CodeValue depth environment extended (extendedValue source request))
    (related : SharedStateRel locations state initial)
    (computed : AccountCallSemantics.Dispatch AccountCallSemantics.noChildren .ordinary source request state result finalState) :
    ∃ target final, Core.Evaluates environment initial (AccountRuntime.dispatch shared runFrame extended depth) target final ∧
      ResponseRel result target ∧ SharedStateRel locations finalState final ∧
      BalanceFrame locations.balances initial final := by
  cases computed with
  | insufficient checked shortfall =>
    obtain ⟨final, evaluated, retained⟩ := dispatch_insufficient references argument related shortfall
    exact ⟨_, final, evaluated, .returned _, related.retained retained, .ofRetains retained⟩
  | transferFault funds failed =>
    have funds' : ¬ request.value > StorageSemantics.readWord source state.balances := by simpa using funds
    obtain ⟨final, evaluated, finalRelated, frame⟩ :=
      dispatch_transferFault references argument related funds' (transferFor_error failed)
    exact ⟨_, final, evaluated, .language _, finalRelated, frame⟩
  | succeeded funds moved executed success =>
    have funds' : ¬ request.value > StorageSemantics.readWord source state.balances := by simpa using funds
    obtain ⟨balances, transferOk, rfl⟩ := transferFor_ok moved
    cases executed with
    | empty ordinary absent complete =>
      obtain ⟨final, evaluated, finalRelated, frame⟩ :=
        dispatch_empty references argument related funds' transferOk ordinary absent complete
      exact ⟨_, final, evaluated, .returned _, finalRelated, frame⟩
    | child impossible => exact False.elim impossible
  | refused funds moved executed failure =>
    cases executed with
    | empty ordinary absent complete => cases failure
    | child impossible => exact False.elim impossible
  | fault funds moved executed =>
    have funds' : ¬ request.value > StorageSemantics.readWord source state.balances := by simpa using funds
    obtain ⟨balances, transferOk, rfl⟩ := transferFor_ok moved
    cases executed with
    | unavailable ordinary absent incomplete =>
      obtain ⟨final, evaluated, finalRelated, frame⟩ :=
        dispatch_unavailable references argument related funds' transferOk ordinary absent incomplete
      exact ⟨_, final, evaluated, .language _, finalRelated, frame⟩
    | child impossible => exact False.elim impossible

end Solcore.Frontend.RustHull.AccountCallCorrespondence
