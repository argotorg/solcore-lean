import Solcore.Frontend.RustHull.Semantics.Accounts
import Solcore.Frontend.RustHull.Internal.RuntimeFrames
import Solcore.Frontend.RustHull.Internal.MemoryState
import Solcore.Frontend.RustHull.Internal.StorageState
import Solcore.Frontend.RustHull.Internal.CallTransport
import Solcore.Frontend.RustHull.Internal.LinkedWorld
import Solcore.Frontend.RustHull.Semantics.Frames
import Solcore.Frontend.RustHull.Internal.RuntimeObjects

/-!
# Account dispatch

Actual account dispatch against its independent rule: checkpoints, transfers, child selection, call
modes and account destruction.
-/

section
-- leanmerge: from Solcore.Frontend.RustHull.AccountCallHandlersCorrespondence
/-! Installed call handlers record the actual closures, their captured cell
references, and the optional cells from which the runtime reads them. No field
assumes that a callback preserves source execution. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.AccountCallCorrespondence
open Correspondence ScalarExecution CodeBuilder

structure SharedLocations where
  world : Nat
  logs : Nat
  logSize : Nat
  balances : Nat
  complete : Nat

def SharedLocations.all (locations : SharedLocations) : List Nat :=
  [locations.world, locations.logs, locations.logSize, locations.balances, locations.complete]

structure SharedReferences (depth : Nat) (environment : Core.Environment)
    (shared : AccountRuntime.References) (locations : SharedLocations) : Prop where
  world : CodeValue depth environment (AccountRuntime.reference shared "world") (.cellRef AccountState.type locations.world)
  logs : CodeValue depth environment (AccountRuntime.reference shared "logs") (.cellRef Core.WordMapping.type locations.logs)
  logSize : CodeValue depth environment (AccountRuntime.reference shared "logSize") (.cellRef .word locations.logSize)
  balances : CodeValue depth environment (AccountRuntime.reference shared "balances") (.cellRef Core.WordMapping.type locations.balances)
  complete : CodeValue depth environment (AccountRuntime.reference shared "worldComplete") (.cellRef .bool locations.complete)

theorem SharedReferences.prepend {depth : Nat} {environment : Core.Environment}
    {shared : AccountRuntime.References} {locations : SharedLocations}
    (references : SharedReferences depth environment shared locations) (extra : Core.Environment) :
    SharedReferences (depth + extra.length) (extra ++ environment) shared locations :=
  ⟨references.world.prepend extra, references.logs.prepend extra, references.logSize.prepend extra,
    references.balances.prepend extra, references.complete.prepend extra⟩

structure SharedStateRel (locations : SharedLocations) (state : AccountCallSemantics.Shared)
    (store : Core.Store) : Prop where
  world : ∃ accounts : StorageCorrespondence.Accounts,
    accounts.map Prod.fst = state.world ∧ store.read? locations.world = some (StorageCorrespondence.world accounts)
  logs : store.read? locations.logs = some (Core.WordMapping.encode state.logs)
  logSize : store.read? locations.logSize = some (.word state.logSize)
  balances : store.read? locations.balances = some (Core.WordMapping.encode state.balances)
  complete : store.read? locations.complete = some (.bool state.complete)
  distinct : locations.all.Nodup

structure DispatcherClosure (locations : SharedLocations) (value : Core.Value) where
  depth : Nat
  captured : Core.Environment
  shared : AccountRuntime.References
  runFrame : Code → Code → Code
  closure : CapturedClosure
    (lambda AccountRuntime.dispatchType (Core.LanguageResult.resultType Calls.responseType)
      (AccountRuntime.dispatch shared runFrame) depth) captured value
  references : SharedReferences depth captured shared locations

structure CallHandlerClosure (source : Core.Word) (dispatcherLocation : Nat) (value : Core.Value) where
  depth : Nat
  captured : Core.Environment
  frame : Code
  dispatcher : Code
  closure : CapturedClosure (AccountRuntime.frameCallHandler 0 frame dispatcher depth) captured value
  address : CodeValue depth captured (part 0 8 frame) (.word source)
  dispatcherReference : CodeValue depth captured dispatcher
    (.cellRef (Core.OptionalCell.cellType AccountRuntime.dispatchCallbackType) dispatcherLocation)

structure InstalledHandlers (locations : SharedLocations) (source : Core.Word)
    (handlerLocation dispatcherLocation : Nat) (store : Core.Store) where
  dispatchValue : Core.Value
  handlerValue : Core.Value
  dispatch : DispatcherClosure locations dispatchValue
  handler : CallHandlerClosure source dispatcherLocation handlerValue
  dispatchRead : store.read? dispatcherLocation = some (.inRight .unit dispatchValue)
  handlerRead : store.read? handlerLocation = some (.inRight .unit handlerValue)

end Solcore.Frontend.RustHull.AccountCallCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.AccountCallCheckpointCorrespondence
/-! Account dispatch captures the four actual shared cells before it checks
funds. The saved expressions retain their lexical bindings through the body. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.AccountCallCorrespondence
open Core Correspondence ScalarExecution CodeBuilder

def checkpointRestore (shared : AccountRuntime.References) (depth : Nat) : Code :=
  bind (store (AccountRuntime.reference shared "balances") (fun here => .var (here - (depth + 3) - 1))) fun _ =>
  bind (store (AccountRuntime.reference shared "logSize") (fun here => .var (here - (depth + 2) - 1))) fun _ =>
  bind (store (AccountRuntime.reference shared "logs") (fun here => .var (here - (depth + 1) - 1))) fun _ =>
  bind (store (AccountRuntime.reference shared "world") (fun here => .var (here - depth - 1))) fun _ => unit

theorem checkpoint_evaluates {depth : Nat} {environment : Core.Environment} {initial final : Core.Store}
    {shared : AccountRuntime.References} {locations : SharedLocations} {continuation : Code → Code}
    {world logs logSize balances result : Core.Value}
    (references : SharedReferences depth environment shared locations)
    (worldRead : initial.read? locations.world = some world)
    (logsRead : initial.read? locations.logs = some logs)
    (sizeRead : initial.read? locations.logSize = some logSize)
    (balancesRead : initial.read? locations.balances = some balances)
    (continued : Core.Evaluates ([balances, logSize, logs, world] ++ environment) initial
      (continuation (checkpointRestore shared depth) (depth + 4)) result final) :
    Core.Evaluates environment initial (AccountRuntime.checkpoint shared continuation depth) result final := by
  apply Core.Evaluates.letE (.loadCell (references.world.evaluates initial) worldRead)
  apply Core.Evaluates.letE (.loadCell ((references.logs.prepend [world]).evaluates initial) logsRead)
  apply Core.Evaluates.letE (.loadCell ((references.logSize.prepend [logs, world]).evaluates initial) sizeRead)
  apply Core.Evaluates.letE (.loadCell ((references.balances.prepend [logSize, logs, world]).evaluates initial) balancesRead)
  exact continued

theorem SharedStateRel.retained {locations : SharedLocations} {state : AccountCallSemantics.Shared}
    {initial final : Core.Store} (related : SharedStateRel locations state initial)
    (retained : StoreRetains initial final) : SharedStateRel locations state final := by
  have keep {location : Nat} {value : Core.Value} (found : initial.read? location = some value) :
      final.read? location = some value :=
    (retained.read location (List.getElem?_eq_some_iff.mp found).1).trans found
  obtain ⟨accounts, same, found⟩ := related.world
  exact ⟨⟨accounts, same, keep found⟩, keep related.logs, keep related.logSize, keep related.balances,
    keep related.complete, related.distinct⟩

theorem lookup_preserves {environment : Core.Environment} {initial : Core.Store}
    {mapping keyExpr : Core.Expr} {entries : StorageSemantics.Words} {key : Core.Word}
    (mappingEvaluated : Core.Evaluates environment initial mapping (Core.WordMapping.encode entries) initial)
    (keyEvaluated : Core.Evaluates environment initial keyExpr (.word key) initial) :
    ∃ final, Core.Evaluates environment initial (Core.WordMapping.lookup mapping keyExpr)
      (.inRight .word (.word (StorageSemantics.readWord key entries))) final ∧ StoreRetains initial final := by
  have evaluated := WordMapping.lookup_evaluates entries key mappingEvaluated keyEvaluated
  rw [← StorageCorrespondence.readWord_eq] at evaluated
  exact ⟨_, evaluated, StoreRetains.append _ _⟩

end Solcore.Frontend.RustHull.AccountCallCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.AccountCallRunCorrespondence
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

/-- A precompiled target runs the supplied precompile code; no world lookup
or account frame is reached. -/
theorem accountRun_precompile_evaluates {depth : Nat} {environment : Core.Environment} {initial final : Core.Store}
    {shared : AccountRuntime.References} {targetCode precompiled : Code} {child : Code → Code}
    {target : Core.Word} {result : Core.Value}
    (argument : CodeValue depth environment targetCode (.word target))
    (precompiledTarget : AccountCallSemantics.isPrecompile target = true)
    (evaluated : Core.Evaluates environment initial (precompiled depth) result final) :
    Core.Evaluates environment initial (accountRun shared targetCode precompiled child depth) result final :=
  .ifTrue (by simpa only [precompiledTarget] using isPrecompile_evaluates argument) evaluated

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
end

section
-- leanmerge: from Solcore.Frontend.RustHull.AccountCallTransferCorrespondence
/-! The dispatch transfer checks and updates the actual balance cell. Lookup
and insertion helper closures remain in the store and other cells are kept. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.AccountCallCorrespondence
open Core Correspondence ScalarExecution CodeBuilder

structure BalanceFrame (location : Nat) (initial final : Core.Store) : Prop where
  length_le : initial.length ≤ final.length
  other : ∀ index, index ≠ location → index < initial.length → final.read? index = initial.read? index

theorem BalanceFrame.ofRetains {location : Nat} {initial final : Core.Store}
    (retained : StoreRetains initial final) : BalanceFrame location initial final :=
  ⟨retained.length_le, fun index _ bound => retained.read index bound⟩

theorem BalanceFrame.trans {location : Nat} {initial middle final : Core.Store}
    (first : BalanceFrame location initial middle) (second : BalanceFrame location middle final) :
    BalanceFrame location initial final := by
  refine ⟨Nat.le_trans first.length_le second.length_le, ?_⟩
  intro index different bound
  rw [second.other index different (Nat.lt_of_lt_of_le bound first.length_le), first.other index different bound]

theorem BalanceFrame.write (location : Nat) (store : Core.Store) (value : Core.Value) :
    BalanceFrame location store (store.set location value) := by
  refine ⟨by simp, ?_⟩
  intro index different _
  exact List.getElem?_set_ne (Ne.symm different)

theorem retained_read {initial final : Core.Store} (retained : StoreRetains initial final)
    {location : Nat} {value : Core.Value} (found : initial.read? location = some value) :
    final.read? location = some value :=
  (retained.read location (List.getElem?_eq_some_iff.mp found).1).trans found

theorem SharedStateRel.balances_updated {locations : SharedLocations} {state : AccountCallSemantics.Shared}
    {initial final : Core.Store} {balances : StorageSemantics.Words}
    (related : SharedStateRel locations state initial) (frame : BalanceFrame locations.balances initial final)
    (read : final.read? locations.balances = some (WordMapping.encode balances)) :
    SharedStateRel locations {state with balances := balances} final := by
  have distinct := related.distinct
  simp only [SharedLocations.all, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at distinct
  have keep {location : Nat} {value : Core.Value} (different : location ≠ locations.balances)
      (found : initial.read? location = some value) : final.read? location = some value :=
    (frame.other location different (List.getElem?_eq_some_iff.mp found).1).trans found
  obtain ⟨accounts, same, world⟩ := related.world
  refine ⟨⟨accounts, same, keep distinct.1.2.2.1 world⟩, keep distinct.2.1.2.1 related.logs,
    keep distinct.2.2.1.1 related.logSize, read, keep (Ne.symm distinct.2.2.2.1) related.complete, related.distinct⟩

theorem write_same {store : Core.Store} {location : Nat} {value : Core.Value}
    (read : store.read? location = some value) : store.write? location value = some store := by
  obtain ⟨bound, same⟩ := List.getElem?_eq_some_iff.mp read
  apply Store.write?_eq_some_iff.mpr
  refine ⟨bound, ?_⟩
  rw [← same, List.set_getElem_self]

theorem checkpointRestore_evaluates {depth : Nat} {environment : Core.Environment} {initial : Core.Store}
    {shared : AccountRuntime.References} {locations : SharedLocations}
    {world logs logSize balances current : Core.Value}
    (references : SharedReferences depth environment shared locations) (extra : Core.Environment)
    (worldRead : initial.read? locations.world = some world)
    (logsRead : initial.read? locations.logs = some logs)
    (sizeRead : initial.read? locations.logSize = some logSize)
    (balancesRead : initial.read? locations.balances = some current)
    (distinct : locations.all.Nodup) :
    Core.Evaluates (extra ++ [balances, logSize, logs, world] ++ environment) initial
      (checkpointRestore shared depth (depth + 4 + extra.length)) .unit
      (initial.set locations.balances balances) := by
  have firstWrite : initial.write? locations.balances balances = some (initial.set locations.balances balances) :=
    Store.write?_eq_some_iff.mpr ⟨(List.getElem?_eq_some_iff.mp balancesRead).1, rfl⟩
  have distinct' := distinct
  simp only [SharedLocations.all, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at distinct'
  have sizeRead' : Core.Store.read? (initial.set locations.balances balances) locations.logSize = some logSize :=
    (Store.write?_preserves_other firstWrite distinct'.2.2.1.1).trans sizeRead
  have logsRead' : Core.Store.read? (initial.set locations.balances balances) locations.logs = some logs :=
    (Store.write?_preserves_other firstWrite distinct'.2.1.2.1).trans logsRead
  have worldRead' : Core.Store.read? (initial.set locations.balances balances) locations.world = some world :=
    (Store.write?_preserves_other firstWrite distinct'.1.2.2.1).trans worldRead
  have balanceValue := (CodeValue.bound (depth + 3) (logSize :: logs :: world :: environment) balances).prepend extra
  have sizeValue := ((CodeValue.bound (depth + 2) (logs :: world :: environment) logSize).prepend [balances]).prepend extra
  have logsValue := ((CodeValue.bound (depth + 1) (world :: environment) logs).prepend [balances, logSize]).prepend extra
  have worldValue := ((CodeValue.bound depth environment world).prepend [balances, logSize, logs]).prepend extra
  have refs := references.prepend (extra ++ [balances, logSize, logs, world])
  have refsDepth : depth + (extra ++ [balances, logSize, logs, world]).length = depth + 4 + extra.length := by simp; omega
  rw [refsDepth] at refs
  simp only [List.append_assoc, List.cons_append, List.nil_append] at refs ⊢
  apply Core.Evaluates.letE (.storeCell (refs.balances.evaluates initial) balancesRead (balanceValue.evaluates initial) firstWrite)
  apply Core.Evaluates.letE (.storeCell ((refs.logSize.prepend [.unit]).evaluates _)
    sizeRead' ((sizeValue.prepend [.unit]).evaluates _) (write_same sizeRead'))
  apply Core.Evaluates.letE (.storeCell ((refs.logs.prepend [.unit, .unit]).evaluates _)
    logsRead' ((logsValue.prepend [.unit, .unit]).evaluates _) (write_same logsRead'))
  apply Core.Evaluates.letE (.storeCell ((refs.world.prepend [.unit, .unit, .unit]).evaluates _)
    worldRead' ((worldValue.prepend [.unit, .unit, .unit]).evaluates _) (write_same worldRead'))
  exact .unit

theorem insert_preserves {environment : Core.Environment} {initial : Core.Store}
    {mapping keyExpr valueExpr : Core.Expr} {entries : StorageSemantics.Words} {key value : Core.Word}
    (mappingEvaluated : Core.Evaluates environment initial mapping (Core.WordMapping.encode entries) initial)
    (keyEvaluated : Core.Evaluates environment initial keyExpr (.word key) initial)
    (valueEvaluated : Core.Evaluates environment initial valueExpr (.word value) initial) :
    ∃ final, Core.Evaluates environment initial (Core.WordMapping.insert mapping keyExpr valueExpr)
      (.inRight .word (Core.WordMapping.encode (StorageSemantics.writeWord key value entries))) final ∧
      StoreRetains initial final := by
  have evaluated := WordMapping.insert_evaluates entries key value mappingEvaluated keyEvaluated valueEvaluated
  rw [← StorageCorrespondence.writeWord_eq] at evaluated
  exact ⟨_, evaluated, StoreRetains.append _ _⟩

def transferResult : Except Core.Word StorageSemantics.Words → Core.Value
  | .ok _ => .inRight .word .unit
  | .error reason => .inLeft .unit (.word reason)

def transferBalances (before : StorageSemantics.Words) : Except Core.Word StorageSemantics.Words → StorageSemantics.Words
  | .ok after => after
  | .error _ => before

theorem transfer_preserves {depth : Nat} {environment : Core.Environment} {initial : Core.Store}
    {shared : AccountRuntime.References} {sourceCode targetCode valueCode : Code}
    {location : Nat} {source target value : Core.Word} {balances : StorageSemantics.Words}
    (reference : CodeValue depth environment (AccountRuntime.reference shared "balances") (.cellRef WordMapping.type location))
    (sourceRelated : CodeValue depth environment sourceCode (.word source))
    (targetRelated : CodeValue depth environment targetCode (.word target))
    (valueRelated : CodeValue depth environment valueCode (.word value))
    (balancesRead : initial.read? location = some (WordMapping.encode balances)) :
    ∃ final, Core.Evaluates environment initial (AccountRuntime.transfer shared sourceCode targetCode valueCode depth)
      (transferResult (AccountCallSemantics.transfer source target value balances)) final ∧
      final.read? location = some (WordMapping.encode (transferBalances balances (AccountCallSemantics.transfer source target value balances))) ∧
      BalanceFrame location initial final := by
  by_cases zero : value == Word.zero
  · refine ⟨initial, ?_, ?_, .ofRetains (.refl _)⟩
    · simp only [AccountCallSemantics.transfer, zero, ↓reduceIte, transferResult]
      exact .ifTrue (.binary (valueRelated.evaluates initial) .word (by change some (Core.Value.bool (value == Word.zero)) = some (Core.Value.bool _); simp only [zero])) (.inRight .unit)
    · simpa only [AccountCallSemantics.transfer, zero, ↓reduceIte, transferBalances] using balancesRead
  have zeroFalse : (value == Word.zero) = false := Bool.eq_false_iff.mpr zero
  by_cases same : source == target
  · refine ⟨initial, ?_, ?_, .ofRetains (.refl _)⟩
    · simp only [AccountCallSemantics.transfer, zero, ↓reduceIte, same, transferResult]
      exact .ifFalse (.binary (valueRelated.evaluates initial) .word (by change some (Core.Value.bool (value == Word.zero)) = some (Core.Value.bool _); simp only [zero]))
        (.ifTrue (.binary (sourceRelated.evaluates initial) (targetRelated.evaluates initial) (by simp [BinaryOp.apply, same])) (.inRight .unit))
    · simpa only [AccountCallSemantics.transfer, zeroFalse, Bool.false_eq_true, ↓reduceIte, same, transferBalances] using balancesRead
  have sameFalse : (source == target) = false := Bool.eq_false_iff.mpr same
  obtain ⟨first, sourceLooked, firstRetained⟩ := lookup_preserves
    (.loadCell (reference.evaluates initial) balancesRead) (sourceRelated.evaluates initial)
  let sourceBalance := StorageSemantics.readWord source balances
  let targetBalance := StorageSemantics.readWord target balances
  let firstEnv : Core.Environment := [.word sourceBalance]
  have sourceBound := CodeValue.bound depth environment (.word sourceBalance)
  obtain ⟨second, targetLooked, secondRetained⟩ := lookup_preserves
    (.loadCell ((reference.prepend firstEnv).evaluates first) (retained_read firstRetained balancesRead))
    ((targetRelated.prepend firstEnv).evaluates first)
  have retained := firstRetained.trans secondRetained
  let secondEnv : Core.Environment := [.word targetBalance, .word sourceBalance]
  have targetBound := CodeValue.bound (depth + 1) (firstEnv ++ environment) (.word targetBalance)
  have overflowTest : Core.Evaluates (secondEnv ++ environment) second
      (binary .wordGt (fun here => .var (here - (depth + 1) - 1))
        (binary .wordSub (number (wordModulus - 1)) valueCode) (depth + 2))
      (.bool (decide (targetBalance > Word.maximum.sub value))) second :=
    .binary (targetBound.evaluates second)
      (.binary .word ((valueRelated.prepend secondEnv).evaluates second) rfl) rfl
  by_cases overflow : targetBalance > Word.maximum.sub value
  · refine ⟨second, ?_, ?_, .ofRetains retained⟩
    · simp only [AccountCallSemantics.transfer, zero, same, ↓reduceIte, transferResult,
        show StorageSemantics.readWord target balances > Word.maximum.sub value from overflow]
      apply Core.Evaluates.ifFalse (.binary (valueRelated.evaluates initial) .word (by change some (Core.Value.bool (value == Word.zero)) = some (Core.Value.bool _); simp only [zero]))
      apply Core.Evaluates.ifFalse (.binary (sourceRelated.evaluates initial) (targetRelated.evaluates initial) (by simp [BinaryOp.apply, same]))
      apply LanguageResult.bind_success .unit sourceLooked
      apply LanguageResult.bind_success .unit targetLooked
      exact .ifTrue (by simpa only [overflow, decide_true, secondEnv, firstEnv, List.cons_append, List.nil_append] using overflowTest) (.inLeft .word)
    · simpa only [AccountCallSemantics.transfer, zeroFalse, sameFalse, Bool.false_eq_true, ↓reduceIte, transferBalances,
        show StorageSemantics.readWord target balances > Word.maximum.sub value from overflow]
        using retained_read retained balancesRead
  let debited := StorageSemantics.writeWord source (sourceBalance.sub value) balances
  obtain ⟨third, debitEvaluated, thirdRetained⟩ := insert_preserves
    (entries := balances) (key := source) (value := sourceBalance.sub value)
    (.loadCell ((reference.prepend secondEnv).evaluates second) (retained_read retained balancesRead))
    ((sourceRelated.prepend secondEnv).evaluates second)
    (.binary (op := .wordSub) ((sourceBound.prepend [.word targetBalance]).evaluates second)
      ((valueRelated.prepend secondEnv).evaluates second) rfl)
  let thirdEnv : Core.Environment := WordMapping.encode debited :: secondEnv
  have debitBound := CodeValue.bound (depth + 2) (secondEnv ++ environment) (WordMapping.encode debited)
  obtain ⟨fourth, creditEvaluated, fourthRetained⟩ := insert_preserves
    (entries := debited) (key := target) (value := targetBalance.add value)
    (debitBound.evaluates third) ((targetRelated.prepend thirdEnv).evaluates third)
    (.binary (op := .wordAdd) ((targetBound.prepend [WordMapping.encode debited]).evaluates third)
      ((valueRelated.prepend thirdEnv).evaluates third) rfl)
  let credited := StorageSemantics.writeWord target (targetBalance.add value) debited
  let fourthEnv : Core.Environment := WordMapping.encode credited :: thirdEnv
  have creditBound := CodeValue.bound (depth + 3) (thirdEnv ++ environment) (WordMapping.encode credited)
  have retainedAll := (retained.trans thirdRetained).trans fourthRetained
  have readable := retained_read retainedAll balancesRead
  have written : fourth.write? location (WordMapping.encode credited) = some (fourth.set location (WordMapping.encode credited)) :=
    Store.write?_eq_some_iff.mpr ⟨(List.getElem?_eq_some_iff.mp readable).1, rfl⟩
  refine ⟨fourth.set location (WordMapping.encode credited), ?_, ?_, (BalanceFrame.ofRetains retainedAll).trans (.write ..)⟩
  · simp only [AccountCallSemantics.transfer, zero, same, ↓reduceIte, transferResult,
      show ¬ StorageSemantics.readWord target balances > Word.maximum.sub value from overflow]
    apply Core.Evaluates.ifFalse (.binary (valueRelated.evaluates initial) .word (by change some (Core.Value.bool (value == Word.zero)) = some (Core.Value.bool _); simp only [zero]))
    apply Core.Evaluates.ifFalse (.binary (sourceRelated.evaluates initial) (targetRelated.evaluates initial) (by simp [BinaryOp.apply, same]))
    apply LanguageResult.bind_success .unit sourceLooked
    apply LanguageResult.bind_success .unit targetLooked
    apply Core.Evaluates.ifFalse (by simpa only [overflow, decide_false, secondEnv, firstEnv, List.cons_append, List.nil_append] using overflowTest)
    apply LanguageResult.bind_success .unit debitEvaluated
    apply LanguageResult.bind_success .unit creditEvaluated
    exact .inRight (.storeCell ((reference.prepend fourthEnv).evaluates fourth) readable (creditBound.evaluates fourth) written)
  · simpa only [AccountCallSemantics.transfer, zeroFalse, sameFalse, Bool.false_eq_true, ↓reduceIte, transferBalances,
      show ¬ StorageSemantics.readWord target balances > Word.maximum.sub value from overflow]
      using Store.write?_reads_written written

end Solcore.Frontend.RustHull.AccountCallCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.AccountCallDispatchCorrespondence
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

/-- The shared state after a transferred precompile call: a successful response
keeps the transfer, while a false response or a fault restores the checkpoint. -/
def precompileAfter (state : AccountCallSemantics.Shared) (balances : StorageSemantics.Words) :
    Semantics.Result AccountCallSemantics.Response → AccountCallSemantics.Shared
  | .value response => if response.success then {state with balances := balances} else state
  | .fault _ => state

/-- After the transfer, a precompiled target answers through the actual
precompile call without a world lookup. The checkpoint restores the balances
after a false response or a language fault. -/
theorem dispatch_precompile {depth : Nat} {environment : Core.Environment} {initial : Core.Store}
    {shared : AccountRuntime.References} {runFrame : Code → Code → Code} {extended : Code}
    {locations : SharedLocations} {source : Core.Word} {request : AccountCallSemantics.Request}
    {state : AccountCallSemantics.Shared} {balances : StorageSemantics.Words}
    {result : Semantics.Result AccountCallSemantics.Response}
    (references : SharedReferences depth environment shared locations)
    (argument : CodeValue depth environment extended (extendedValue source request))
    (related : SharedStateRel locations state initial)
    (funds : ¬ request.value > StorageSemantics.readWord source state.balances)
    (moved : AccountCallSemantics.transfer source request.target request.value state.balances = .ok balances)
    (computed : AccountCallSemantics.Precompile request result) :
    ∃ target final, Core.Evaluates environment initial (AccountRuntime.dispatch shared runFrame extended depth) target final ∧
      ResponseRel result target ∧ SharedStateRel locations (precompileAfter state balances result) final ∧
      BalanceFrame locations.balances initial final := by
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
  have worldTransferred : transferred.read? locations.world = some (StorageCorrespondence.world accounts) :=
    (combined.other locations.world distinct.1.2.2.1 (List.getElem?_eq_some_iff.mp worldRead).1).trans worldRead
  let runExtra := .unit :: extra
  let runEnv := runExtra ++ environment
  have runRequest := (argument.prepend runExtra).part (index := 0) rfl
  obtain ⟨runTarget, ran, runEvaluated, runRelated, runRetained⟩ :=
    PrecompileCorrespondence.precompile_preserves (store := transferred) runRequest computed
  have ranRelated := transferredRelated.retained runRetained
  have ranFrame := combined.trans (.ofRetains runRetained)
  let restored := ran.set locations.balances (WordMapping.encode state.balances)
  have restoredFrame := ranFrame.trans (BalanceFrame.write locations.balances ran (WordMapping.encode state.balances))
  have restoredBalance : Core.Store.read? restored locations.balances = some (WordMapping.encode state.balances) :=
    List.getElem?_set_self (List.getElem?_eq_some_iff.mp ranRelated.balances).1
  have restoredRelated : SharedStateRel locations state restored :=
    related.balances_updated restoredFrame restoredBalance
  cases runRelated with
  | returned response =>
    have responseCode := CodeValue.bound (depth + 6) runEnv (responseValue response)
    cases success : response.success with
    | true =>
      refine ⟨_, ran, ?_, .returned _, by simpa only [precompileAfter, success, ↓reduceIte] using ranRelated, ranFrame⟩
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
        (accountRun_precompile_evaluates (runRequest.part (index := 0) rfl) computed.precompiled runEvaluated)
      exact .ifTrue (by simpa only [success, responseValues, List.length_cons, List.length_nil, Nat.add_assoc] using
        (responseCode.part (index := 0) rfl).evaluates ran) (.inRight (responseCode.evaluates ran))
    | false =>
      refine ⟨_, restored, ?_, .returned _, by simpa only [precompileAfter, success, Bool.false_eq_true, ↓reduceIte]
        using restoredRelated, restoredFrame⟩
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
        (accountRun_precompile_evaluates (runRequest.part (index := 0) rfl) computed.precompiled runEvaluated)
      apply Core.Evaluates.ifFalse (by simpa only [success, responseValues, List.length_cons, List.length_nil, Nat.add_assoc]
        using (responseCode.part (index := 0) rfl).evaluates ran)
      apply Core.Evaluates.letE (checkpointRestore_evaluates (balances := WordMapping.encode state.balances) references
        [responseValue response, .unit, .word sourceBalance] (retained_read runRetained worldTransferred)
        ranRelated.logs ranRelated.logSize ranRelated.balances related.distinct)
      exact .inRight ((responseCode.prepend [.unit]).evaluates restored)
  | language reason =>
    refine ⟨_, restored, ?_, .language _, by simpa only [precompileAfter] using restoredRelated, restoredFrame⟩
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
      (accountRun_precompile_evaluates (runRequest.part (index := 0) rfl) computed.precompiled runEvaluated)
    apply Core.Evaluates.letE (checkpointRestore_evaluates (balances := WordMapping.encode state.balances) references
      [.word reason, .unit, .word sourceBalance] (retained_read runRetained worldTransferred)
      ranRelated.logs ranRelated.logSize ranRelated.balances related.distinct)
    exact .inLeft (((CodeValue.bound (depth + 6) runEnv (.word reason)).prepend [.unit]).evaluates restored)

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
    | precompile executed =>
      obtain ⟨target, final, evaluated, responded, finalRelated, frame⟩ :=
        dispatch_precompile references argument related funds' transferOk executed
      exact ⟨target, final, evaluated, responded,
        by simpa only [precompileAfter, success, ↓reduceIte] using finalRelated, frame⟩
    | empty ordinary absent complete =>
      obtain ⟨final, evaluated, finalRelated, frame⟩ :=
        dispatch_empty references argument related funds' transferOk ordinary absent complete
      exact ⟨_, final, evaluated, .returned _, finalRelated, frame⟩
    | child impossible => exact False.elim impossible
  | refused funds moved executed failure =>
    cases executed with
    | precompile executed =>
      have funds' : ¬ request.value > StorageSemantics.readWord source state.balances := by simpa using funds
      obtain ⟨balances, transferOk, rfl⟩ := transferFor_ok moved
      obtain ⟨target, final, evaluated, responded, finalRelated, frame⟩ :=
        dispatch_precompile references argument related funds' transferOk executed
      exact ⟨target, final, evaluated, responded,
        by simpa only [precompileAfter, failure, Bool.false_eq_true, ↓reduceIte] using finalRelated, frame⟩
    | empty ordinary absent complete => cases failure
    | child impossible => exact False.elim impossible
  | fault funds moved executed =>
    have funds' : ¬ request.value > StorageSemantics.readWord source state.balances := by simpa using funds
    obtain ⟨balances, transferOk, rfl⟩ := transferFor_ok moved
    cases executed with
    | precompile executed =>
      obtain ⟨target, final, evaluated, responded, finalRelated, frame⟩ :=
        dispatch_precompile references argument related funds' transferOk executed
      exact ⟨target, final, evaluated, responded, by simpa only [precompileAfter] using finalRelated, frame⟩
    | unavailable ordinary absent incomplete =>
      obtain ⟨final, evaluated, finalRelated, frame⟩ :=
        dispatch_unavailable references argument related funds' transferOk ordinary absent incomplete
      exact ⟨_, final, evaluated, .language _, finalRelated, frame⟩
    | child impossible => exact False.elim impossible

end Solcore.Frontend.RustHull.AccountCallCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.AccountCallCallbackCorrespondence
/-! The concrete callback closures installed by object initialization execute
independent account dispatch in their captured environments. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.AccountCallCorrespondence
open Core Correspondence ScalarExecution CodeBuilder CallTransportCorrespondence

theorem DispatcherClosure.apply_preserves {locations : SharedLocations} {value : Core.Value}
    (closure : DispatcherClosure locations value)
    {source : Core.Word} {request : AccountCallSemantics.Request}
    {state finalState : AccountCallSemantics.Shared} {result : Semantics.Result AccountCallSemantics.Response}
    (computed : AccountCallSemantics.Dispatch AccountCallSemantics.noChildren .ordinary source request state result finalState)
    {environment : Core.Environment} {before middle initial : Core.Store} {function argument : Core.Expr}
    (related : SharedStateRel locations state initial)
    (resolved : Core.Evaluates environment before function value middle)
    (supplied : Core.Evaluates environment middle argument (extendedValue source request) initial) :
    ∃ target final, Core.Evaluates environment before (.apply function argument) target final ∧
      ResponseRel result target ∧ SharedStateRel locations finalState final ∧
      BalanceFrame locations.balances initial final := by
  rcases closure with ⟨depth, captured, shared, runFrame, capturedClosure, references⟩
  cases capturedClosure
  obtain ⟨target, final, evaluated, resultRelated, finalRelated, frame⟩ :=
    dispatch_preserves (references.prepend [extendedValue source request])
      (CodeValue.bound depth captured (extendedValue source request)) related computed
  exact ⟨target, final, .apply resolved supplied evaluated, resultRelated, finalRelated, frame⟩

theorem CallHandlerClosure.apply_preserves {locations : SharedLocations} {source : Core.Word}
    {dispatcherLocation : Nat} {handlerValue dispatchValue : Core.Value}
    (handler : CallHandlerClosure source dispatcherLocation handlerValue)
    (dispatcher : DispatcherClosure locations dispatchValue)
    {request : AccountCallSemantics.Request} {state finalState : AccountCallSemantics.Shared}
    {result : Semantics.Result AccountCallSemantics.Response}
    (computed : AccountCallSemantics.Dispatch AccountCallSemantics.noChildren .ordinary source request state result finalState)
    {environment : Core.Environment} {before middle initial : Core.Store} {function argument : Core.Expr}
    (related : SharedStateRel locations state initial)
    (dispatchRead : initial.read? dispatcherLocation = some (.inRight .unit dispatchValue))
    (resolved : Core.Evaluates environment before function handlerValue middle)
    (supplied : Core.Evaluates environment middle argument (requestValue request) initial) :
    ∃ target final, Core.Evaluates environment before (.apply function argument) target final ∧
      ResponseRel result target ∧ SharedStateRel locations finalState final ∧
      BalanceFrame locations.balances initial final := by
  rcases handler with ⟨depth, captured, frame, dispatchRef, capturedClosure, address, dispatcherReference⟩
  cases capturedClosure
  have read := OptionalCell.read_success (Word.ofNatModulo 7)
    ((dispatcherReference.prepend [requestValue request]).evaluates initial) dispatchRead
  have requestBound := CodeValue.bound depth captured (requestValue request)
  have dispatchBound := CodeValue.bound (depth + 1) (requestValue request :: captured) dispatchValue
  have suppliedExtended := Core.Evaluates.pair ((requestBound.prepend [dispatchValue]).evaluates initial)
    (.pair (.word (value := Word.zero)) ((address.prepend [dispatchValue, requestValue request]).evaluates initial))
  obtain ⟨target, final, evaluated, resultRelated, finalRelated, kept⟩ :=
    dispatcher.apply_preserves computed related (dispatchBound.evaluates initial) suppliedExtended
  refine ⟨target, final, .apply resolved supplied ?_, resultRelated, finalRelated, kept⟩
  exact LanguageResult.bind_success Calls.responseType read evaluated

/-- Handler-cell reads are the reads installed by the actual initializer;
callback correctness follows from the captured body, not a premise. -/
theorem InstalledHandlers.apply_preserves {locations : SharedLocations} {source : Core.Word}
    {handlerLocation dispatcherLocation : Nat} {initial : Core.Store}
    (installed : InstalledHandlers locations source handlerLocation dispatcherLocation initial)
    {request : AccountCallSemantics.Request} {state finalState : AccountCallSemantics.Shared}
    {result : Semantics.Result AccountCallSemantics.Response}
    (computed : AccountCallSemantics.Dispatch AccountCallSemantics.noChildren .ordinary source request state result finalState)
    {environment : Core.Environment} {function argument : Core.Expr}
    (related : SharedStateRel locations state initial)
    (resolved : Core.Evaluates environment initial function installed.handlerValue initial)
    (supplied : Core.Evaluates environment initial argument (requestValue request) initial) :
    ∃ target final, Core.Evaluates environment initial (.apply function argument) target final ∧
      ResponseRel result target ∧ SharedStateRel locations finalState final ∧
      BalanceFrame locations.balances initial final :=
  installed.handler.apply_preserves installed.dispatch computed related installed.dispatchRead resolved supplied

end Solcore.Frontend.RustHull.AccountCallCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.AccountCallSharedCorrespondence
/-! A child may change all four shared resources. The caller's other cells and
catalog identities survive dispatch, including restoration after a failed child. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.AccountCallCorrespondence
open Core Correspondence ScalarExecution CodeBuilder

def SharedLocations.mutable (locations : SharedLocations) : List Nat :=
  [locations.world, locations.logs, locations.logSize, locations.balances]

structure SharedFrame (locations : SharedLocations) (initial final : Core.Store) : Prop where
  length_le : initial.length ≤ final.length
  read : ∀ location value, location ∉ locations.mutable →
    initial.read? location = some value → final.read? location = some value

theorem SharedFrame.refl (locations : SharedLocations) (store : Core.Store) : SharedFrame locations store store :=
  ⟨Nat.le_refl _, fun _ _ _ found => found⟩

theorem SharedFrame.trans {locations : SharedLocations} {initial middle final : Core.Store}
    (first : SharedFrame locations initial middle) (second : SharedFrame locations middle final) :
    SharedFrame locations initial final :=
  ⟨Nat.le_trans first.length_le second.length_le,
    fun index value outside found => second.read index value outside (first.read index value outside found)⟩

theorem SharedFrame.ofRetains {locations : SharedLocations} {initial final : Core.Store}
    (retained : StoreRetains initial final) : SharedFrame locations initial final :=
  ⟨retained.length_le, fun _ _ _ found => retained_read retained found⟩

theorem SharedFrame.ofBalance {locations : SharedLocations} {initial final : Core.Store}
    (frame : BalanceFrame locations.balances initial final) : SharedFrame locations initial final := by
  refine ⟨frame.length_le, ?_⟩
  intro index value outside found
  exact (frame.other index (fun same => outside (by simp [SharedLocations.mutable, same]))
    (List.getElem?_eq_some_iff.mp found).1).trans found

theorem SharedFrame.write {locations : SharedLocations} {location : Nat}
    (member : location ∈ locations.mutable) (store : Core.Store) (value : Core.Value) :
    SharedFrame locations store (store.set location value) := by
  refine ⟨by simp, ?_⟩
  intro index old outside found
  have different : location ≠ index := fun same => outside (same ▸ member)
  exact (List.getElem?_set_ne different).trans found

structure LinkedSharedStateRel (anchors : List CatalogWorldCorrespondence.Anchor)
    (locations : SharedLocations) (state : AccountCallSemantics.Shared) (store : Core.Store) : Prop where
  shared : SharedStateRel locations state store
  linked : RuntimeLinkedWorldCorrespondence.StateRel anchors state.world locations.world store

theorem LinkedSharedStateRel.retained {anchors : List CatalogWorldCorrespondence.Anchor}
    {locations : SharedLocations} {state : AccountCallSemantics.Shared} {initial final : Core.Store}
    (related : LinkedSharedStateRel anchors locations state initial) (retained : StoreRetains initial final) :
    LinkedSharedStateRel anchors locations state final :=
  ⟨related.shared.retained retained, related.linked.retained retained⟩

theorem LinkedSharedStateRel.balances_updated {anchors : List CatalogWorldCorrespondence.Anchor}
    {locations : SharedLocations} {state : AccountCallSemantics.Shared} {initial final : Core.Store}
    {balances : StorageSemantics.Words} (related : LinkedSharedStateRel anchors locations state initial)
    (frame : BalanceFrame locations.balances initial final)
    (read : final.read? locations.balances = some (WordMapping.encode balances)) :
    LinkedSharedStateRel anchors locations {state with balances := balances} final := by
  refine ⟨related.shared.balances_updated frame read, related.linked.read_preserved ?_⟩
  intro value found
  have distinct := related.shared.distinct
  simp only [SharedLocations.all, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at distinct
  exact (frame.other locations.world distinct.1.2.2.1 (List.getElem?_eq_some_iff.mp found).1).trans found

def checkpointStore (locations : SharedLocations) (world logs logSize balances : Core.Value)
    (store : Core.Store) : Core.Store :=
  (((store.set locations.balances balances).set locations.logSize logSize).set locations.logs logs).set locations.world world

theorem checkpointStore_frame (locations : SharedLocations) (world logs logSize balances : Core.Value)
    (store : Core.Store) : SharedFrame locations store (checkpointStore locations world logs logSize balances store) :=
  (((SharedFrame.write (by simp [SharedLocations.mutable]) store balances).trans
    (.write (by simp [SharedLocations.mutable]) _ logSize)).trans
    (.write (by simp [SharedLocations.mutable]) _ logs)).trans
    (.write (by simp [SharedLocations.mutable]) _ world)

theorem checkpointRestore_all_evaluates {depth : Nat} {environment : Core.Environment} {initial : Core.Store}
    {shared : AccountRuntime.References} {locations : SharedLocations}
    (world logs logSize balances : Core.Value)
    (references : SharedReferences depth environment shared locations) (extra : Core.Environment)
    (bounded : ∀ location ∈ locations.mutable, location < initial.length) :
    Core.Evaluates (extra ++ [balances, logSize, logs, world] ++ environment) initial
      (checkpointRestore shared depth (depth + 4 + extra.length)) .unit
      (checkpointStore locations world logs logSize balances initial) := by
  have balanceValue := (CodeValue.bound (depth + 3) (logSize :: logs :: world :: environment) balances).prepend extra
  have sizeValue := ((CodeValue.bound (depth + 2) (logs :: world :: environment) logSize).prepend [balances]).prepend extra
  have logsValue := ((CodeValue.bound (depth + 1) (world :: environment) logs).prepend [balances, logSize]).prepend extra
  have worldValue := ((CodeValue.bound depth environment world).prepend [balances, logSize, logs]).prepend extra
  have refs := references.prepend (extra ++ [balances, logSize, logs, world])
  have refsDepth : depth + (extra ++ [balances, logSize, logs, world]).length = depth + 4 + extra.length := by simp; omega
  rw [refsDepth] at refs
  simp only [List.append_assoc, List.cons_append, List.nil_append] at refs ⊢
  have balanceBound := bounded locations.balances (by simp [SharedLocations.mutable])
  have sizeBound : locations.logSize < (initial.set locations.balances balances).length := by
    simpa only [List.length_set] using bounded locations.logSize (by simp [SharedLocations.mutable])
  have logsBound : locations.logs < ((initial.set locations.balances balances).set locations.logSize logSize).length := by
    simpa only [List.length_set] using bounded locations.logs (by simp [SharedLocations.mutable])
  have worldBound : locations.world < (((initial.set locations.balances balances).set locations.logSize logSize).set locations.logs logs).length := by
    simpa only [List.length_set] using bounded locations.world (by simp [SharedLocations.mutable])
  apply Core.Evaluates.letE (.storeCell (refs.balances.evaluates initial) (List.getElem?_eq_getElem balanceBound)
    (balanceValue.evaluates initial) (Store.write?_eq_some_iff.mpr ⟨balanceBound, rfl⟩))
  apply Core.Evaluates.letE (.storeCell ((refs.logSize.prepend [.unit]).evaluates _) (List.getElem?_eq_getElem sizeBound)
    ((sizeValue.prepend [.unit]).evaluates _) (Store.write?_eq_some_iff.mpr ⟨sizeBound, rfl⟩))
  apply Core.Evaluates.letE (.storeCell ((refs.logs.prepend [.unit, .unit]).evaluates _) (List.getElem?_eq_getElem logsBound)
    ((logsValue.prepend [.unit, .unit]).evaluates _) (Store.write?_eq_some_iff.mpr ⟨logsBound, rfl⟩))
  apply Core.Evaluates.letE (.storeCell ((refs.world.prepend [.unit, .unit, .unit]).evaluates _) (List.getElem?_eq_getElem worldBound)
    ((worldValue.prepend [.unit, .unit, .unit]).evaluates _) (Store.write?_eq_some_iff.mpr ⟨worldBound, rfl⟩))
  exact .unit

theorem SharedStateRel.mutable_bounded {locations : SharedLocations} {state : AccountCallSemantics.Shared}
    {store : Core.Store} (related : SharedStateRel locations state store) :
    ∀ location ∈ locations.mutable, location < store.length := by
  intro location member
  simp only [SharedLocations.mutable, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · obtain ⟨_, _, read⟩ := related.world; exact (List.getElem?_eq_some_iff.mp read).1
  · exact (List.getElem?_eq_some_iff.mp related.logs).1
  · exact (List.getElem?_eq_some_iff.mp related.logSize).1
  · exact (List.getElem?_eq_some_iff.mp related.balances).1

theorem checkpointStore_restores {anchors : List CatalogWorldCorrespondence.Anchor}
    {locations : SharedLocations} {state : AccountCallSemantics.Shared} {initial current : Core.Store}
    {accounts : StorageCorrespondence.Accounts}
    (related : SharedStateRel locations state initial)
    (same : accounts.map Prod.fst = state.world) (links : CatalogWorldCorrespondence.Links anchors accounts)
    (frame : SharedFrame locations initial current) :
    LinkedSharedStateRel anchors locations state
      (checkpointStore locations (StorageCorrespondence.world accounts) (WordMapping.encode state.logs)
        (.word state.logSize) (WordMapping.encode state.balances) current) := by
  have bounds : ∀ location ∈ locations.mutable, location < current.length :=
    fun location member => Nat.lt_of_lt_of_le (related.mutable_bounded location member) frame.length_le
  have distinct := related.distinct
  simp only [SharedLocations.all, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at distinct
  have readWorld : (checkpointStore locations (StorageCorrespondence.world accounts) (WordMapping.encode state.logs)
      (.word state.logSize) (WordMapping.encode state.balances) current).read? locations.world = some (StorageCorrespondence.world accounts) := by
    apply List.getElem?_set_self
    simpa only [List.length_set] using bounds locations.world (by simp [SharedLocations.mutable])
  have readLogs : (checkpointStore locations (StorageCorrespondence.world accounts) (WordMapping.encode state.logs)
      (.word state.logSize) (WordMapping.encode state.balances) current).read? locations.logs = some (WordMapping.encode state.logs) := by
    unfold checkpointStore Store.read?
    rw [List.getElem?_set_ne distinct.1.1]
    apply List.getElem?_set_self
    simpa only [List.length_set] using bounds locations.logs (by simp [SharedLocations.mutable])
  have readSize : (checkpointStore locations (StorageCorrespondence.world accounts) (WordMapping.encode state.logs)
      (.word state.logSize) (WordMapping.encode state.balances) current).read? locations.logSize = some (.word state.logSize) := by
    unfold checkpointStore Store.read?
    rw [List.getElem?_set_ne distinct.1.2.1, List.getElem?_set_ne distinct.2.1.1]
    apply List.getElem?_set_self
    simpa only [List.length_set] using bounds locations.logSize (by simp [SharedLocations.mutable])
  have readBalances : (checkpointStore locations (StorageCorrespondence.world accounts) (WordMapping.encode state.logs)
      (.word state.logSize) (WordMapping.encode state.balances) current).read? locations.balances = some (WordMapping.encode state.balances) := by
    unfold checkpointStore Store.read?
    rw [List.getElem?_set_ne distinct.1.2.2.1, List.getElem?_set_ne distinct.2.1.2.1,
      List.getElem?_set_ne distinct.2.2.1.1]
    exact List.getElem?_set_self (bounds locations.balances (by simp [SharedLocations.mutable]))
  have outside : locations.complete ∉ locations.mutable := by
    simp only [SharedLocations.mutable, List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨Ne.symm distinct.1.2.2.2, Ne.symm distinct.2.1.2.2,
      Ne.symm distinct.2.2.1.2, Ne.symm distinct.2.2.2.1⟩
  have complete := (frame.trans (checkpointStore_frame locations (StorageCorrespondence.world accounts) (WordMapping.encode state.logs) (.word state.logSize) (WordMapping.encode state.balances) current)).read
    locations.complete _ outside related.complete
  exact ⟨⟨⟨accounts, same, readWorld⟩, readLogs, readSize, readBalances, complete, related.distinct⟩,
    accounts, same, links, readWorld⟩

end Solcore.Frontend.RustHull.AccountCallCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.AccountCallChildRunCorrespondence
/-! The child interface describes the actual selected frame call under its
captured bindings. Public execution supplies it from compilation and fresh
frame initialization. Empty accounts continue to use the existing runtime path. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.AccountCallCorrespondence
open Core Correspondence ScalarExecution CodeBuilder CallTransportCorrespondence

def childRequest (extended : Code) : Code :=
  let request := part 0 3 extended
  packet [choose (binary .wordEq (part 1 3 extended) (number 0))
    (part 0 8 request) (part 2 3 extended),
    part 1 8 request, part 2 8 request, part 3 8 request, part 4 8 request,
    part 5 8 request, part 6 8 request, part 7 8 request]

def dispatchRun (shared : AccountRuntime.References) (runFrame : Code → Code → Code)
    (extended precompiled : Code) : Code :=
  accountRun shared (part 0 8 (part 0 3 extended)) precompiled
    (fun record => runFrame record (childRequest extended))

theorem childRequest_evaluates {depth : Nat} {environment : Core.Environment} {store : Core.Store}
    {extended : Code} {source : Core.Word} {request : AccountCallSemantics.Request}
    (argument : CodeValue depth environment extended (extendedValue source request)) :
    Core.Evaluates environment store (childRequest extended depth) (requestValue request) store := by
  have requestCode := argument.part (index := 0) rfl
  apply Core.Evaluates.pair
  · exact .ifTrue (.binary ((argument.part (index := 1) rfl).evaluates store) .word rfl)
      ((requestCode.part (index := 0) rfl).evaluates store)
  apply Core.Evaluates.pair ((requestCode.part (index := 1) rfl).evaluates store)
  apply Core.Evaluates.pair ((requestCode.part (index := 2) rfl).evaluates store)
  apply Core.Evaluates.pair ((requestCode.part (index := 3) rfl).evaluates store)
  apply Core.Evaluates.pair ((requestCode.part (index := 4) rfl).evaluates store)
  apply Core.Evaluates.pair ((requestCode.part (index := 5) rfl).evaluates store)
  exact .pair ((requestCode.part (index := 6) rfl).evaluates store)
    ((requestCode.part (index := 7) rfl).evaluates store)

theorem childRequest_value {depth : Nat} {environment : Core.Environment} {extended : Code}
    {source : Core.Word} {request : AccountCallSemantics.Request}
    (argument : CodeValue depth environment extended (extendedValue source request)) :
    CodeValue depth environment (childRequest extended) (requestValue request) := by
  intro extra store
  simpa only [List.length_append, Nat.add_assoc] using childRequest_evaluates (argument.prepend extra) (store := store)

def ChildRunPreservation (anchors : List CatalogWorldCorrespondence.Anchor) (locations : SharedLocations)
    (shared : AccountRuntime.References) (runFrame : Code → Code → Code)
    (children : AccountCallSemantics.Children) (valid : Core.Store → Prop)
    (baseDepth : Nat) (captured : Core.Environment) : Prop :=
  ∀ {source request state result finalState}, children .ordinary source request state result finalState →
  ∀ (extra : Core.Environment) {store : Core.Store} {extended precompiled : Code},
    SharedReferences (baseDepth + extra.length) (extra ++ captured) shared locations →
    CodeValue (baseDepth + extra.length) (extra ++ captured) extended (extendedValue source request) →
    LinkedSharedStateRel anchors locations state store → valid store →
    ∃ target final, Core.Evaluates (extra ++ captured) store
      (dispatchRun shared runFrame extended precompiled (baseDepth + extra.length)) target final ∧
      ResponseRel result target ∧ LinkedSharedStateRel anchors locations finalState final ∧
      SharedFrame locations store final

theorem ChildRunPreservation.prepend {anchors : List CatalogWorldCorrespondence.Anchor} {locations : SharedLocations}
    {shared : AccountRuntime.References} {runFrame : Code → Code → Code} {children : AccountCallSemantics.Children}
    {valid : Core.Store → Prop} {baseDepth : Nat} {captured : Core.Environment}
    (preserved : ChildRunPreservation anchors locations shared runFrame children valid baseDepth captured)
    (front : Core.Environment) :
    ChildRunPreservation anchors locations shared runFrame children valid (baseDepth + front.length) (front ++ captured) := by
  intro source request state result finalState computed extra store extended precompiled references argument related ready
  have references' : SharedReferences (baseDepth + (extra ++ front).length) ((extra ++ front) ++ captured) shared locations := by
    simpa only [List.length_append, List.append_assoc, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using references
  have argument' : CodeValue (baseDepth + (extra ++ front).length) ((extra ++ front) ++ captured) extended (extendedValue source request) := by
    simpa only [List.length_append, List.append_assoc, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using argument
  simpa only [List.length_append, List.append_assoc, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    preserved computed (extra ++ front) references' argument' related ready (precompiled := precompiled)

/-- The supplied precompile code produces every independent precompile result
for the request and retains the calling store. Dispatch supplies the actual
precompile call through `precompileCode_preservation`. -/
def PrecompiledPreservation (precompiled : Code) (request : AccountCallSemantics.Request)
    (baseDepth : Nat) (captured : Core.Environment) : Prop :=
  ∀ {result}, AccountCallSemantics.Precompile request result →
  ∀ (extra : Core.Environment) (store : Core.Store),
    ∃ target final, Core.Evaluates (extra ++ captured) store (precompiled (baseDepth + extra.length)) target final ∧
      ResponseRel result target ∧ StoreRetains store final

theorem PrecompiledPreservation.prepend {precompiled : Code} {request : AccountCallSemantics.Request}
    {baseDepth : Nat} {captured : Core.Environment}
    (preserved : PrecompiledPreservation precompiled request baseDepth captured) (front : Core.Environment) :
    PrecompiledPreservation precompiled request (baseDepth + front.length) (front ++ captured) := by
  intro result computed extra store
  simpa only [List.length_append, List.append_assoc, Nat.add_assoc, Nat.add_comm front.length extra.length] using
    preserved computed (extra ++ front) store

theorem precompileCode_preservation {depth : Nat} {environment : Core.Environment} {requestCode : Code}
    {request : AccountCallSemantics.Request}
    (requestRelated : CodeValue depth environment requestCode (requestValue request)) :
    PrecompiledPreservation (PrecompileCorrespondence.precompileCode requestCode) request depth environment :=
  fun computed extra _ => PrecompileCorrespondence.precompile_preserves (requestRelated.prepend extra) computed

/-- A selected nonzero identity reaches the actual frame continuation. The
lookup's helper allocation is retained and exposed to the continuation. -/
theorem accountRun_child_evaluates {depth : Nat} {environment : Core.Environment} {initial final : Core.Store}
    {shared : AccountRuntime.References} {targetCode precompiled : Code} {child : Code → Code}
    {locations : SharedLocations} {target : Core.Word} {accounts : StorageCorrespondence.Accounts}
    {account : AccountState.Account} {identity : Nat} {complete : Bool} {result : Core.Value}
    (references : SharedReferences depth environment shared locations)
    (argument : CodeValue depth environment targetCode (.word target))
    (worldRead : initial.read? locations.world = some (StorageCorrespondence.world accounts))
    (completeRead : initial.read? locations.complete = some (.bool complete))
    (ordinary : AccountCallSemantics.isPrecompile target = false)
    (selected : StorageCorrespondence.lookup target accounts = some (account, identity))
    (nonzero : Core.Word.ofNatModulo identity ≠ Core.Word.zero)
    (continued : Core.Evaluates (StorageCorrespondence.record account identity :: environment)
      (StorageCorrespondence.getStore accounts target complete environment initial)
      (child (fun here => .var (here - depth - 1)) (depth + 1)) result final) :
    Core.Evaluates environment initial (accountRun shared targetCode precompiled child depth) result final := by
  have fetched := StorageCorrespondence.get_evaluates accounts target complete
    (.loadCell (references.world.evaluates initial) worldRead) (argument.evaluates initial)
    (.loadCell (references.complete.evaluates initial) completeRead)
  simp only [StorageCorrespondence.get, selected, StorageCorrespondence.getValue] at fetched
  apply Core.Evaluates.ifFalse (by simpa only [ordinary] using isPrecompile_evaluates argument)
  apply LanguageResult.bind_success Calls.responseType fetched
  have recordValue := CodeValue.bound depth environment (StorageCorrespondence.record account identity)
  apply Core.Evaluates.ifFalse (.binary ((recordValue.part (index := 3) rfl).evaluates _) .word ?_) continued
  change some (Core.Value.bool (Word.ofNatModulo identity == Word.zero)) = some (Core.Value.bool false)
  simp only [beq_eq_false_iff_ne.mpr nonzero]

end Solcore.Frontend.RustHull.AccountCallCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.AccountCallChildDispatchCorrespondence
/-! Dispatch commits successful child effects and restores every captured shared
cell after revert or fault. The same frame rule retains the caller's local cells. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.AccountCallCorrespondence
open Core Correspondence ScalarExecution CodeBuilder CallTransportCorrespondence

theorem run_children_preserves {anchors : List CatalogWorldCorrespondence.Anchor} {locations : SharedLocations}
    {shared : AccountRuntime.References} {runFrame : Code → Code → Code} {children : AccountCallSemantics.Children}
    {valid : Core.Store → Prop} {depth : Nat} {environment : Core.Environment} {store : Core.Store}
    {extended precompiled : Code} {source : Core.Word} {request : AccountCallSemantics.Request}
    {state finalState : AccountCallSemantics.Shared} {result : Semantics.Result AccountCallSemantics.Response}
    (childrenPreserved : ChildRunPreservation anchors locations shared runFrame children valid depth environment)
    (precompiledPreserved : PrecompiledPreservation precompiled request depth environment)
    (references : SharedReferences depth environment shared locations)
    (argument : CodeValue depth environment extended (extendedValue source request))
    (related : LinkedSharedStateRel anchors locations state store) (ready : valid store)
    (computed : AccountCallSemantics.Run children .ordinary source request state result finalState) :
    ∃ target final, Core.Evaluates environment store (dispatchRun shared runFrame extended precompiled depth) target final ∧
      ResponseRel result target ∧ LinkedSharedStateRel anchors locations finalState final ∧
      SharedFrame locations store final := by
  cases computed with
  | precompile executed =>
    obtain ⟨target, final, evaluated, responded, retained⟩ := precompiledPreserved executed [] store
    refine ⟨target, final, ?_, responded, related.retained retained, .ofRetains retained⟩
    exact accountRun_precompile_evaluates ((argument.part (index := 0) rfl).part (index := 0) rfl)
      executed.precompiled (by simpa only [List.nil_append, List.length_nil, Nat.add_zero] using evaluated)
  | empty ordinary absent complete =>
    obtain ⟨final, evaluated, retained⟩ := accountRun_absent references
      ((argument.part (index := 0) rfl).part (index := 0) rfl) related.shared ordinary absent
      (precompiled := precompiled) (child := fun record => runFrame record (childRequest extended))
    refine ⟨_, final, ?_, .returned _, related.retained retained, .ofRetains retained⟩
    simpa only [emptyRunResult, complete, ↓reduceIte, dispatchRun, requestValues, List.length_cons, List.length_nil] using evaluated
  | unavailable ordinary absent incomplete =>
    obtain ⟨final, evaluated, retained⟩ := accountRun_absent references
      ((argument.part (index := 0) rfl).part (index := 0) rfl) related.shared ordinary absent
      (precompiled := precompiled) (child := fun record => runFrame record (childRequest extended))
    refine ⟨_, final, ?_, .language _, related.retained retained, .ofRetains retained⟩
    simpa only [emptyRunResult, incomplete, Bool.false_eq_true, ↓reduceIte, dispatchRun, requestValues, List.length_cons, List.length_nil] using evaluated
  | child computed =>
    simpa only [List.nil_append, List.length_nil, Nat.add_zero] using
      childrenPreserved computed [] references argument related ready (precompiled := precompiled)

def dispatchAfter (before : AccountCallSemantics.Shared)
    (result : Semantics.Result AccountCallSemantics.Response) (after : AccountCallSemantics.Shared) :
    AccountCallSemantics.Shared :=
  match result with
  | .value response => if response.success then after else before
  | .fault _ => before

def dispatchWith (shared : AccountRuntime.References) (runFrame : Code → Code → Code)
    (extended precompiled : Code) : Code :=
  let request := part 0 3 extended
  let mode := part 1 3 extended
  let source := part 2 3 extended
  AccountRuntime.checkpoint shared fun restore =>
  bindResult Calls.responseType (lookup (load (AccountRuntime.reference shared "balances")) source) fun sourceBalance =>
  choose (choose (binary .wordEq mode (number 2)) (CodeBuilder.boolean false)
    (binary .wordGt (part 2 8 request) sourceBalance))
    (AccountRuntime.callResult (CodeBuilder.boolean false) empty (number 0)) <|
  bindResult Calls.responseType
    (choose (binary .wordEq mode (number 0))
      (AccountRuntime.transfer shared source (part 0 8 request) (part 2 8 request)) (success unit)) fun _ =>
  fun depth => .caseE (dispatchRun shared runFrame extended precompiled depth)
    ((bind restore fun _ => failure Calls.responseType (fun here => .var (here - depth - 1))) (depth + 1))
    ((let response : Code := fun here => .var (here - depth - 1)
      choose (part 0 3 response) (success response)
        (bind restore fun _ => success response)) (depth + 1))

theorem dispatch_transferred_preserves {anchors : List CatalogWorldCorrespondence.Anchor} {locations : SharedLocations}
    {shared : AccountRuntime.References} {runFrame : Code → Code → Code} {children : AccountCallSemantics.Children}
    {valid : Core.Store → Prop} {depth : Nat} {environment : Core.Environment} {initial : Core.Store}
    {extended precompiled : Code} {source : Core.Word} {request : AccountCallSemantics.Request}
    {state attempted : AccountCallSemantics.Shared} {balances : StorageSemantics.Words}
    {result : Semantics.Result AccountCallSemantics.Response}
    (childrenPreserved : ChildRunPreservation anchors locations shared runFrame children valid depth environment)
    (precompiledPreserved : PrecompiledPreservation precompiled request depth environment)
    (stable : ∀ {first last}, SharedFrame locations first last → valid first → valid last)
    (references : SharedReferences depth environment shared locations)
    (argument : CodeValue depth environment extended (extendedValue source request))
    (related : LinkedSharedStateRel anchors locations state initial) (ready : valid initial)
    (funds : ¬ request.value > StorageSemantics.readWord source state.balances)
    (moved : AccountCallSemantics.transfer source request.target request.value state.balances = .ok balances)
    (computed : AccountCallSemantics.Run children .ordinary source request {state with balances := balances} result attempted) :
    ∃ target final, Core.Evaluates environment initial (dispatchWith shared runFrame extended precompiled depth) target final ∧
      ResponseRel result target ∧ LinkedSharedStateRel anchors locations (dispatchAfter state result attempted) final ∧
      SharedFrame locations initial final := by
  obtain ⟨accounts, worldSame, links, worldRead⟩ := related.linked
  let saved : Core.Environment := [WordMapping.encode state.balances, .word state.logSize,
    WordMapping.encode state.logs, StorageCorrespondence.world accounts]
  have innerReferences := references.prepend saved
  have innerArgument := argument.prepend saved
  obtain ⟨first, looked, retained⟩ := lookup_preserves
    (.loadCell (innerReferences.balances.evaluates initial) related.shared.balances)
    ((innerArgument.part (index := 2) rfl).evaluates initial)
  let sourceBalance := StorageSemantics.readWord source state.balances
  let extra := .word sourceBalance :: saved
  have afterArgument := argument.prepend extra
  have requestCode := afterArgument.part (index := 0) rfl
  obtain ⟨transferred, transferEvaluated, balanceFinal, transferFrame⟩ := transfer_preserves (references.balances.prepend extra)
    (afterArgument.part (index := 2) rfl) (requestCode.part (index := 0) rfl) (requestCode.part (index := 2) rfl)
    (retained_read retained related.shared.balances)
  rw [moved] at transferEvaluated balanceFinal
  have combined := (BalanceFrame.ofRetains retained).trans transferFrame
  have transferredRelated := related.balances_updated combined balanceFinal
  let runExtra := .unit :: extra
  let runEnv := runExtra ++ environment
  obtain ⟨output, afterRun, runEvaluated, resultRelated, afterRelated, runFrameProof⟩ :=
    run_children_preserves (childrenPreserved.prepend runExtra) (precompiledPreserved.prepend runExtra)
      (references.prepend runExtra) (argument.prepend runExtra) transferredRelated
      (stable (.ofBalance combined) ready) computed
  have throughRun : SharedFrame locations initial afterRun := (SharedFrame.ofBalance combined).trans runFrameProof
  have enter {target : Core.Value} {final : Core.Store}
      (continued : Core.Evaluates runEnv transferred
        (.caseE (dispatchRun shared runFrame extended precompiled (depth + 6))
          ((bind (checkpointRestore shared depth) fun _ => failure Calls.responseType (fun here => .var (here - (depth + 6) - 1))) (depth + 7))
          ((let response : Code := fun here => .var (here - (depth + 6) - 1)
            choose (part 0 3 response) (success response)
              (bind (checkpointRestore shared depth) fun _ => success response)) (depth + 7))) target final) :
      Core.Evaluates environment initial (dispatchWith shared runFrame extended precompiled depth) target final := by
    apply checkpoint_evaluates references worldRead related.shared.logs related.shared.logSize related.shared.balances
    apply LanguageResult.bind_success Calls.responseType looked
    apply Core.Evaluates.ifFalse
    · apply Core.Evaluates.ifFalse (.binary ((afterArgument.part (index := 1) rfl).evaluates first) .word rfl)
      exact .binary ((requestCode.part (index := 2) rfl).evaluates first)
        ((CodeValue.bound (depth + 4) (saved ++ environment) (.word sourceBalance)).evaluates first)
        (by simp [BinaryOp.apply, sourceBalance, funds])
    apply LanguageResult.bind_success Calls.responseType
      (.ifTrue (.binary ((afterArgument.part (index := 1) rfl).evaluates first) .word rfl) transferEvaluated)
    exact continued
  have restoreBound : ∀ location ∈ locations.mutable, location < afterRun.length :=
    fun location member => Nat.lt_of_lt_of_le (related.shared.mutable_bounded location member) throughRun.length_le
  let restored := checkpointStore locations (StorageCorrespondence.world accounts) (WordMapping.encode state.logs)
    (.word state.logSize) (WordMapping.encode state.balances) afterRun
  have restoredRelated : LinkedSharedStateRel anchors locations state restored :=
    checkpointStore_restores related.shared worldSame links throughRun
  have restoredFrame : SharedFrame locations initial restored := throughRun.trans (checkpointStore_frame ..)
  cases resultRelated with
  | returned response =>
    have responseCode := CodeValue.bound (depth + 6) runEnv (responseValue response)
    cases success : response.success with
    | true =>
      refine ⟨_, afterRun, enter (.caseRight runEvaluated ?_), .returned _, ?_, throughRun⟩
      · exact .ifTrue (by simpa only [success, responseValues, List.length_cons, List.length_nil, Nat.add_assoc] using (responseCode.part (index := 0) rfl).evaluates afterRun)
          (.inRight (responseCode.evaluates afterRun))
      · simpa only [dispatchAfter, success, ↓reduceIte] using afterRelated
    | false =>
      refine ⟨_, restored, enter (.caseRight runEvaluated ?_), .returned _, ?_, restoredFrame⟩
      · apply Core.Evaluates.ifFalse (by simpa only [success, responseValues, List.length_cons, List.length_nil, Nat.add_assoc] using (responseCode.part (index := 0) rfl).evaluates afterRun)
        apply Core.Evaluates.letE (checkpointRestore_all_evaluates _ _ _ _ references
          [responseValue response, .unit, .word sourceBalance] restoreBound)
        exact .inRight ((responseCode.prepend [.unit]).evaluates restored)
      · simpa only [dispatchAfter, success, Bool.false_eq_true, ↓reduceIte] using restoredRelated
  | language reason =>
    refine ⟨_, restored, enter (.caseLeft runEvaluated ?_), .language _, restoredRelated, restoredFrame⟩
    apply Core.Evaluates.letE (checkpointRestore_all_evaluates _ _ _ _ references
      [.word reason, .unit, .word sourceBalance] restoreBound)
    exact .inLeft (((CodeValue.bound (depth + 6) runEnv (.word reason)).prepend [.unit]).evaluates restored)

/-- The actual dispatcher is the composition above with the actual precompile
call, restated by `PrecompileCorrespondence.precompileCode`. -/
theorem dispatch_precompile_eq (shared : AccountRuntime.References) (runFrame : Code → Code → Code)
    (extended : Code) :
    AccountRuntime.dispatch shared runFrame extended =
      dispatchWith shared runFrame extended (PrecompileCorrespondence.precompileCode (part 0 3 extended)) := rfl

/-- Source dispatch selects the real funds, transfer and child branches. This
internal composition theorem is instantiated with compiled child execution. -/
theorem dispatch_children_preserves {anchors : List CatalogWorldCorrespondence.Anchor} {locations : SharedLocations}
    {shared : AccountRuntime.References} {runFrame : Code → Code → Code} {children : AccountCallSemantics.Children}
    {valid : Core.Store → Prop} {depth : Nat} {environment : Core.Environment} {initial : Core.Store}
    {extended : Code} {source : Core.Word} {request : AccountCallSemantics.Request}
    {state finalState : AccountCallSemantics.Shared} {result : Semantics.Result AccountCallSemantics.Response}
    (childrenPreserved : ChildRunPreservation anchors locations shared runFrame children valid depth environment)
    (stable : ∀ {first last}, SharedFrame locations first last → valid first → valid last)
    (references : SharedReferences depth environment shared locations)
    (argument : CodeValue depth environment extended (extendedValue source request))
    (related : LinkedSharedStateRel anchors locations state initial) (ready : valid initial)
    (computed : AccountCallSemantics.Dispatch children .ordinary source request state result finalState) :
    ∃ target final, Core.Evaluates environment initial (AccountRuntime.dispatch shared runFrame extended depth) target final ∧
      ResponseRel result target ∧ LinkedSharedStateRel anchors locations finalState final ∧
      SharedFrame locations initial final := by
  have requestCode : CodeValue depth environment (part 0 3 extended) (requestValue request) :=
    argument.part (index := 0) rfl
  cases computed with
  | insufficient checked shortfall =>
    obtain ⟨final, evaluated, retained⟩ := dispatch_insufficient references argument related.shared shortfall
    exact ⟨_, final, evaluated, .returned _, related.retained retained, .ofRetains retained⟩
  | transferFault funds failed =>
    have funds' : ¬ request.value > StorageSemantics.readWord source state.balances := by simpa using funds
    obtain ⟨final, evaluated, finalRelated, frame⟩ :=
      dispatch_transferFault references argument related.shared funds' (transferFor_error failed)
    exact ⟨_, final, evaluated, .language _, related.balances_updated frame finalRelated.balances, .ofBalance frame⟩
  | succeeded funds moved executed success =>
    have funds' : ¬ request.value > StorageSemantics.readWord source state.balances := by simpa using funds
    obtain ⟨balances, transferOk, rfl⟩ := transferFor_ok moved
    rw [dispatch_precompile_eq]
    simpa only [dispatchAfter, success, ↓reduceIte] using
      dispatch_transferred_preserves childrenPreserved (precompileCode_preservation requestCode)
        stable references argument related ready funds' transferOk executed
  | refused funds moved executed failure =>
    have funds' : ¬ request.value > StorageSemantics.readWord source state.balances := by simpa using funds
    obtain ⟨balances, transferOk, rfl⟩ := transferFor_ok moved
    rw [dispatch_precompile_eq]
    simpa only [dispatchAfter, failure, Bool.false_eq_true, ↓reduceIte] using
      dispatch_transferred_preserves childrenPreserved (precompileCode_preservation requestCode)
        stable references argument related ready funds' transferOk executed
  | fault funds moved executed =>
    have funds' : ¬ request.value > StorageSemantics.readWord source state.balances := by simpa using funds
    obtain ⟨balances, transferOk, rfl⟩ := transferFor_ok moved
    rw [dispatch_precompile_eq]
    exact dispatch_transferred_preserves childrenPreserved (precompileCode_preservation requestCode)
      stable references argument related ready funds' transferOk executed

end Solcore.Frontend.RustHull.AccountCallCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.AccountCallChildCallbackCorrespondence
/-! Captured runtime handlers execute child-capable dispatch. The internal
child interface is discharged by compiled frame execution before the public
contract theorem is exposed. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.AccountCallCorrespondence
open Core Correspondence ScalarExecution CodeBuilder CallTransportCorrespondence

theorem DispatcherClosure.apply_children_preserves {locations : SharedLocations} {value : Core.Value}
    (closure : DispatcherClosure locations value)
    {anchors : List CatalogWorldCorrespondence.Anchor} {children : AccountCallSemantics.Children} {valid : Core.Store → Prop}
    (childrenPreserved : ChildRunPreservation anchors locations closure.shared closure.runFrame children valid closure.depth closure.captured)
    (stable : ∀ {first last}, SharedFrame locations first last → valid first → valid last)
    {source : Core.Word} {request : AccountCallSemantics.Request}
    {state finalState : AccountCallSemantics.Shared} {result : Semantics.Result AccountCallSemantics.Response}
    (computed : AccountCallSemantics.Dispatch children .ordinary source request state result finalState)
    {environment : Core.Environment} {before middle initial : Core.Store} {function argument : Core.Expr}
    (related : LinkedSharedStateRel anchors locations state initial) (ready : valid initial)
    (resolved : Core.Evaluates environment before function value middle)
    (supplied : Core.Evaluates environment middle argument (extendedValue source request) initial) :
    ∃ target final, Core.Evaluates environment before (.apply function argument) target final ∧
      ResponseRel result target ∧ LinkedSharedStateRel anchors locations finalState final ∧
      SharedFrame locations initial final := by
  rcases closure with ⟨depth, captured, shared, runFrame, capturedClosure, references⟩
  cases capturedClosure
  obtain ⟨target, final, evaluated, resultRelated, finalRelated, frame⟩ :=
    dispatch_children_preserves (childrenPreserved.prepend [extendedValue source request]) stable
      (references.prepend [extendedValue source request])
      (CodeValue.bound depth captured (extendedValue source request)) related ready computed
  exact ⟨target, final, .apply resolved supplied evaluated, resultRelated, finalRelated, frame⟩

theorem CallHandlerClosure.apply_children_preserves {locations : SharedLocations} {source : Core.Word}
    {dispatcherLocation : Nat} {handlerValue dispatchValue : Core.Value}
    (handler : CallHandlerClosure source dispatcherLocation handlerValue)
    (dispatcher : DispatcherClosure locations dispatchValue)
    {anchors : List CatalogWorldCorrespondence.Anchor} {children : AccountCallSemantics.Children} {valid : Core.Store → Prop}
    (childrenPreserved : ChildRunPreservation anchors locations dispatcher.shared dispatcher.runFrame children valid dispatcher.depth dispatcher.captured)
    (stable : ∀ {first last}, SharedFrame locations first last → valid first → valid last)
    {request : AccountCallSemantics.Request} {state finalState : AccountCallSemantics.Shared}
    {result : Semantics.Result AccountCallSemantics.Response}
    (computed : AccountCallSemantics.Dispatch children .ordinary source request state result finalState)
    {environment : Core.Environment} {before middle initial : Core.Store} {function argument : Core.Expr}
    (related : LinkedSharedStateRel anchors locations state initial) (ready : valid initial)
    (dispatchRead : initial.read? dispatcherLocation = some (.inRight .unit dispatchValue))
    (resolved : Core.Evaluates environment before function handlerValue middle)
    (supplied : Core.Evaluates environment middle argument (requestValue request) initial) :
    ∃ target final, Core.Evaluates environment before (.apply function argument) target final ∧
      ResponseRel result target ∧ LinkedSharedStateRel anchors locations finalState final ∧
      SharedFrame locations initial final := by
  rcases handler with ⟨depth, captured, frame, dispatchRef, capturedClosure, address, dispatcherReference⟩
  cases capturedClosure
  have read := OptionalCell.read_success (Word.ofNatModulo 7)
    ((dispatcherReference.prepend [requestValue request]).evaluates initial) dispatchRead
  have requestBound := CodeValue.bound depth captured (requestValue request)
  have dispatchBound := CodeValue.bound (depth + 1) (requestValue request :: captured) dispatchValue
  have suppliedExtended := Core.Evaluates.pair ((requestBound.prepend [dispatchValue]).evaluates initial)
    (.pair (.word (value := Word.zero)) ((address.prepend [dispatchValue, requestValue request]).evaluates initial))
  obtain ⟨target, final, evaluated, resultRelated, finalRelated, kept⟩ :=
    dispatcher.apply_children_preserves childrenPreserved stable computed related ready (dispatchBound.evaluates initial) suppliedExtended
  refine ⟨target, final, .apply resolved supplied ?_, resultRelated, finalRelated, kept⟩
  exact LanguageResult.bind_success Calls.responseType read evaluated

/-- Handler-cell reads are the reads installed by the actual initializer;
callback correctness follows from the captured body, not a premise. -/
theorem InstalledHandlers.apply_children_preserves {locations : SharedLocations} {source : Core.Word}
    {handlerLocation dispatcherLocation : Nat} {initial : Core.Store}
    (installed : InstalledHandlers locations source handlerLocation dispatcherLocation initial)
    {anchors : List CatalogWorldCorrespondence.Anchor} {children : AccountCallSemantics.Children} {valid : Core.Store → Prop}
    (childrenPreserved : ChildRunPreservation anchors locations installed.dispatch.shared installed.dispatch.runFrame children valid
      installed.dispatch.depth installed.dispatch.captured)
    (stable : ∀ {first last}, SharedFrame locations first last → valid first → valid last)
    {request : AccountCallSemantics.Request} {state finalState : AccountCallSemantics.Shared}
    {result : Semantics.Result AccountCallSemantics.Response}
    (computed : AccountCallSemantics.Dispatch children .ordinary source request state result finalState)
    {environment : Core.Environment} {function argument : Core.Expr}
    (related : LinkedSharedStateRel anchors locations state initial) (ready : valid initial)
    (resolved : Core.Evaluates environment initial function installed.handlerValue initial)
    (supplied : Core.Evaluates environment initial argument (requestValue request) initial) :
    ∃ target final, Core.Evaluates environment initial (.apply function argument) target final ∧
      ResponseRel result target ∧ LinkedSharedStateRel anchors locations finalState final ∧
      SharedFrame locations initial final :=
  installed.handler.apply_children_preserves installed.dispatch childrenPreserved stable computed related ready installed.dispatchRead resolved supplied

end Solcore.Frontend.RustHull.AccountCallCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.AccountCallModeRunCorrespondence
/-! Calls select code by the original target and execute it at the address
chosen by their dispatch mode. Captured requests keep caller and value separate. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.AccountCallModeCorrespondence
open Core Correspondence ScalarExecution CodeBuilder CallTransportCorrespondence
open AccountCallCorrespondence hiding extendedValue ChildRunPreservation childRequest_evaluates childRequest_value

def extendedValue (mode : AccountCallSemantics.Mode) (source : Word)
    (request : AccountCallSemantics.Request) : Value :=
  bundleValues [requestValue request, .word (Word.ofNatModulo mode.number), .word source]

theorem childRequest_evaluates {depth : Nat} {environment : Core.Environment} {store : Core.Store}
    {extended : Code} {mode : AccountCallSemantics.Mode} {source : Core.Word} {request : AccountCallSemantics.Request}
    (argument : CodeValue depth environment extended (extendedValue mode source request)) :
    Core.Evaluates environment store (childRequest extended depth) (requestValue (ChildFrameModeSemantics.executionRequest mode source request)) store := by
  have requestCode := argument.part (index := 0) rfl
  apply Core.Evaluates.pair
  · cases mode with
    | ordinary =>
      exact .ifTrue (.binary ((argument.part (index := 1) rfl).evaluates store) .word rfl)
        ((requestCode.part (index := 0) rfl).evaluates store)
    | callCode =>
      exact .ifFalse (.binary ((argument.part (index := 1) rfl).evaluates store) .word rfl)
        ((argument.part (index := 2) rfl).evaluates store)
    | delegateCall =>
      exact .ifFalse (.binary ((argument.part (index := 1) rfl).evaluates store) .word rfl)
        ((argument.part (index := 2) rfl).evaluates store)
  apply Core.Evaluates.pair ((requestCode.part (index := 1) rfl).evaluates store)
  apply Core.Evaluates.pair ((requestCode.part (index := 2) rfl).evaluates store)
  apply Core.Evaluates.pair ((requestCode.part (index := 3) rfl).evaluates store)
  apply Core.Evaluates.pair ((requestCode.part (index := 4) rfl).evaluates store)
  apply Core.Evaluates.pair ((requestCode.part (index := 5) rfl).evaluates store)
  exact .pair ((requestCode.part (index := 6) rfl).evaluates store)
    ((requestCode.part (index := 7) rfl).evaluates store)

theorem childRequest_value {depth : Nat} {environment : Core.Environment} {extended : Code}
    {mode : AccountCallSemantics.Mode} {source : Core.Word} {request : AccountCallSemantics.Request}
    (argument : CodeValue depth environment extended (extendedValue mode source request)) :
    CodeValue depth environment (childRequest extended) (requestValue (ChildFrameModeSemantics.executionRequest mode source request)) := by
  intro extra store
  simpa only [List.length_append, Nat.add_assoc] using childRequest_evaluates (argument.prepend extra) (store := store)

def ChildRunPreservation (mode : AccountCallSemantics.Mode) (anchors : List CatalogWorldCorrespondence.Anchor) (locations : SharedLocations)
    (shared : AccountRuntime.References) (runFrame : Code → Code → Code)
    (children : AccountCallSemantics.Children) (valid : Core.Store → Prop)
    (baseDepth : Nat) (captured : Core.Environment) : Prop :=
  ∀ {source request state result finalState}, children mode source request state result finalState →
  ∀ (extra : Core.Environment) {store : Core.Store} {extended precompiled : Code},
    SharedReferences (baseDepth + extra.length) (extra ++ captured) shared locations →
    CodeValue (baseDepth + extra.length) (extra ++ captured) extended (extendedValue mode source request) →
    LinkedSharedStateRel anchors locations state store → valid store →
    ∃ target final, Core.Evaluates (extra ++ captured) store
      (dispatchRun shared runFrame extended precompiled (baseDepth + extra.length)) target final ∧
      ResponseRel result target ∧ LinkedSharedStateRel anchors locations finalState final ∧
      SharedFrame locations store final

theorem ChildRunPreservation.prepend {mode : AccountCallSemantics.Mode} {anchors : List CatalogWorldCorrespondence.Anchor} {locations : SharedLocations}
    {shared : AccountRuntime.References} {runFrame : Code → Code → Code} {children : AccountCallSemantics.Children}
    {valid : Core.Store → Prop} {baseDepth : Nat} {captured : Core.Environment}
    (preserved : ChildRunPreservation mode anchors locations shared runFrame children valid baseDepth captured)
    (front : Core.Environment) :
    ChildRunPreservation mode anchors locations shared runFrame children valid (baseDepth + front.length) (front ++ captured) := by
  intro source request state result finalState computed extra store extended precompiled references argument related ready
  have references' : SharedReferences (baseDepth + (extra ++ front).length) ((extra ++ front) ++ captured) shared locations := by
    simpa only [List.length_append, List.append_assoc, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using references
  have argument' : CodeValue (baseDepth + (extra ++ front).length) ((extra ++ front) ++ captured) extended (extendedValue mode source request) := by
    simpa only [List.length_append, List.append_assoc, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using argument
  simpa only [List.length_append, List.append_assoc, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    preserved computed (extra ++ front) references' argument' related ready (precompiled := precompiled)

theorem run_children_preserves {mode : AccountCallSemantics.Mode} {anchors : List CatalogWorldCorrespondence.Anchor} {locations : SharedLocations}
    {shared : AccountRuntime.References} {runFrame : Code → Code → Code} {children : AccountCallSemantics.Children}
    {valid : Core.Store → Prop} {depth : Nat} {environment : Core.Environment} {store : Core.Store}
    {extended precompiled : Code} {source : Core.Word} {request : AccountCallSemantics.Request}
    {state finalState : AccountCallSemantics.Shared} {result : Semantics.Result AccountCallSemantics.Response}
    (childrenPreserved : ChildRunPreservation mode anchors locations shared runFrame children valid depth environment)
    (precompiledPreserved : PrecompiledPreservation precompiled request depth environment)
    (references : SharedReferences depth environment shared locations)
    (argument : CodeValue depth environment extended (extendedValue mode source request))
    (related : LinkedSharedStateRel anchors locations state store) (ready : valid store)
    (computed : AccountCallSemantics.Run children mode source request state result finalState) :
    ∃ target final, Core.Evaluates environment store (dispatchRun shared runFrame extended precompiled depth) target final ∧
      ResponseRel result target ∧ LinkedSharedStateRel anchors locations finalState final ∧
      SharedFrame locations store final := by
  cases computed with
  | precompile executed =>
    obtain ⟨target, final, evaluated, responded, retained⟩ := precompiledPreserved executed [] store
    refine ⟨target, final, ?_, responded, related.retained retained, .ofRetains retained⟩
    exact accountRun_precompile_evaluates ((argument.part (index := 0) rfl).part (index := 0) rfl)
      executed.precompiled (by simpa only [List.nil_append, List.length_nil, Nat.add_zero] using evaluated)
  | empty ordinary absent complete =>
    obtain ⟨final, evaluated, retained⟩ := accountRun_absent references
      ((argument.part (index := 0) rfl).part (index := 0) rfl) related.shared ordinary absent
      (precompiled := precompiled) (child := fun record => runFrame record (childRequest extended))
    refine ⟨_, final, ?_, .returned _, related.retained retained, .ofRetains retained⟩
    simpa only [emptyRunResult, complete, ↓reduceIte, dispatchRun, requestValues, List.length_cons, List.length_nil] using evaluated
  | unavailable ordinary absent incomplete =>
    obtain ⟨final, evaluated, retained⟩ := accountRun_absent references
      ((argument.part (index := 0) rfl).part (index := 0) rfl) related.shared ordinary absent
      (precompiled := precompiled) (child := fun record => runFrame record (childRequest extended))
    refine ⟨_, final, ?_, .language _, related.retained retained, .ofRetains retained⟩
    simpa only [emptyRunResult, incomplete, Bool.false_eq_true, ↓reduceIte, dispatchRun, requestValues, List.length_cons, List.length_nil] using evaluated
  | child computed =>
    simpa only [List.nil_append, List.length_nil, Nat.add_zero] using
      childrenPreserved computed [] references argument related ready (precompiled := precompiled)

end Solcore.Frontend.RustHull.AccountCallModeCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.AccountCallModeDispatchCorrespondence
/-! CALLCODE and DELEGATECALL use the actual checkpoint and funds branch but
perform no transfer. All modes commit or roll back the same four shared cells. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.AccountCallModeCorrespondence
open Core Correspondence ScalarExecution CodeBuilder CallTransportCorrespondence
open AccountCallCorrespondence hiding extendedValue ChildRunPreservation run_children_preserves dispatch_insufficient

theorem dispatch_insufficient {mode : AccountCallSemantics.Mode} {depth : Nat} {environment : Core.Environment} {initial : Core.Store}
    {shared : AccountRuntime.References} {runFrame : Code → Code → Code} {extended : Code}
    {locations : SharedLocations} {source : Core.Word} {request : AccountCallSemantics.Request}
    {state : AccountCallSemantics.Shared}
    (references : SharedReferences depth environment shared locations)
    (argument : CodeValue depth environment extended (extendedValue mode source request))
    (related : SharedStateRel locations state initial)
    (checked : mode ≠ .delegateCall)
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
  · apply Core.Evaluates.ifFalse (.binary (modeCode.evaluates final) .word (by
      cases mode with
      | ordinary => rfl
      | callCode => rfl
      | delegateCall => exact False.elim (checked rfl)))
    exact .binary (valueCode.evaluates final)
      ((CodeValue.bound (depth + 4) (saved ++ environment)
        (.word (StorageSemantics.readWord source state.balances))).evaluates final)
      (by simp [BinaryOp.apply, shortfall])
  · exact .inRight (.pair .bool (.pair (.construct .unit) .word))

theorem dispatch_untransferred_preserves {mode : AccountCallSemantics.Mode} {anchors : List CatalogWorldCorrespondence.Anchor} {locations : SharedLocations}
    {shared : AccountRuntime.References} {runFrame : Code → Code → Code} {children : AccountCallSemantics.Children}
    {valid : Core.Store → Prop} {depth : Nat} {environment : Core.Environment} {initial : Core.Store}
    {extended precompiled : Code} {source : Core.Word} {request : AccountCallSemantics.Request}
    {state attempted : AccountCallSemantics.Shared}
    {result : Semantics.Result AccountCallSemantics.Response}
    (childrenPreserved : ChildRunPreservation mode anchors locations shared runFrame children valid depth environment)
    (precompiledPreserved : PrecompiledPreservation precompiled request depth environment)
    (stable : ∀ {first last}, SharedFrame locations first last → valid first → valid last)
    (references : SharedReferences depth environment shared locations)
    (argument : CodeValue depth environment extended (extendedValue mode source request))
    (related : LinkedSharedStateRel anchors locations state initial) (ready : valid initial)
    (other : mode ≠ .ordinary)
    (funds : mode = .delegateCall ∨ ¬ request.value > StorageSemantics.readWord source state.balances)
    (computed : AccountCallSemantics.Run children mode source request state result attempted) :
    ∃ target final, Core.Evaluates environment initial (dispatchWith shared runFrame extended precompiled depth) target final ∧
      ResponseRel result target ∧ LinkedSharedStateRel anchors locations (dispatchAfter state result attempted) final ∧
      SharedFrame locations initial final := by
  obtain ⟨accounts, worldSame, links, worldRead⟩ := related.linked
  let saved : Core.Environment := [WordMapping.encode state.balances, .word state.logSize,
    WordMapping.encode state.logs, StorageCorrespondence.world accounts]
  have innerReferences := references.prepend saved
  have innerArgument := argument.prepend saved
  obtain ⟨first, looked, retained⟩ := lookup_preserves
    (.loadCell (innerReferences.balances.evaluates initial) related.shared.balances)
    ((innerArgument.part (index := 2) rfl).evaluates initial)
  let sourceBalance := StorageSemantics.readWord source state.balances
  let extra := .word sourceBalance :: saved
  have afterArgument := argument.prepend extra
  have requestCode := afterArgument.part (index := 0) rfl
  let runExtra := .unit :: extra
  let runEnv := runExtra ++ environment
  obtain ⟨output, afterRun, runEvaluated, resultRelated, afterRelated, runFrameProof⟩ :=
    run_children_preserves (childrenPreserved.prepend runExtra) (precompiledPreserved.prepend runExtra)
      (references.prepend runExtra) (argument.prepend runExtra) (related.retained retained)
      (stable (.ofRetains retained) ready) computed
  have throughRun : SharedFrame locations initial afterRun := (SharedFrame.ofRetains retained).trans runFrameProof
  have enter {target : Core.Value} {final : Core.Store}
      (continued : Core.Evaluates runEnv first
        (.caseE (dispatchRun shared runFrame extended precompiled (depth + 6))
          ((bind (checkpointRestore shared depth) fun _ => failure Calls.responseType (fun here => .var (here - (depth + 6) - 1))) (depth + 7))
          ((let response : Code := fun here => .var (here - (depth + 6) - 1)
            choose (part 0 3 response) (success response)
              (bind (checkpointRestore shared depth) fun _ => success response)) (depth + 7))) target final) :
      Core.Evaluates environment initial (dispatchWith shared runFrame extended precompiled depth) target final := by
    apply checkpoint_evaluates references worldRead related.shared.logs related.shared.logSize related.shared.balances
    apply LanguageResult.bind_success Calls.responseType looked
    apply Core.Evaluates.ifFalse
    · cases mode with
      | ordinary => exact False.elim (other rfl)
      | callCode =>
        apply Core.Evaluates.ifFalse (.binary ((afterArgument.part (index := 1) rfl).evaluates first) .word rfl)
        exact .binary ((requestCode.part (index := 2) rfl).evaluates first)
          ((CodeValue.bound (depth + 4) (saved ++ environment) (.word sourceBalance)).evaluates first)
          (by
            have enough : ¬ request.value > StorageSemantics.readWord source state.balances :=
              funds.resolve_left (by decide)
            simp [BinaryOp.apply, sourceBalance, enough])
      | delegateCall =>
        exact .ifTrue (.binary ((afterArgument.part (index := 1) rfl).evaluates first) .word rfl) .bool
    apply LanguageResult.bind_success Calls.responseType
      (Core.Evaluates.ifFalse (.binary ((afterArgument.part (index := 1) rfl).evaluates first) .word (by
        cases mode with
        | ordinary => exact False.elim (other rfl)
        | callCode => rfl
        | delegateCall => rfl)) (.inRight .unit))
    exact continued
  have restoreBound : ∀ location ∈ locations.mutable, location < afterRun.length :=
    fun location member => Nat.lt_of_lt_of_le (related.shared.mutable_bounded location member) throughRun.length_le
  let restored := checkpointStore locations (StorageCorrespondence.world accounts) (WordMapping.encode state.logs)
    (.word state.logSize) (WordMapping.encode state.balances) afterRun
  have restoredRelated : LinkedSharedStateRel anchors locations state restored :=
    checkpointStore_restores related.shared worldSame links throughRun
  have restoredFrame : SharedFrame locations initial restored := throughRun.trans (checkpointStore_frame ..)
  cases resultRelated with
  | returned response =>
    have responseCode := CodeValue.bound (depth + 6) runEnv (responseValue response)
    cases success : response.success with
    | true =>
      refine ⟨_, afterRun, enter (.caseRight runEvaluated ?_), .returned _, ?_, throughRun⟩
      · exact .ifTrue (by simpa only [success, responseValues, List.length_cons, List.length_nil, Nat.add_assoc] using (responseCode.part (index := 0) rfl).evaluates afterRun)
          (.inRight (responseCode.evaluates afterRun))
      · simpa only [dispatchAfter, success, ↓reduceIte] using afterRelated
    | false =>
      refine ⟨_, restored, enter (.caseRight runEvaluated ?_), .returned _, ?_, restoredFrame⟩
      · apply Core.Evaluates.ifFalse (by simpa only [success, responseValues, List.length_cons, List.length_nil, Nat.add_assoc] using (responseCode.part (index := 0) rfl).evaluates afterRun)
        apply Core.Evaluates.letE (checkpointRestore_all_evaluates _ _ _ _ references
          [responseValue response, .unit, .word sourceBalance] restoreBound)
        exact .inRight ((responseCode.prepend [.unit]).evaluates restored)
      · simpa only [dispatchAfter, success, Bool.false_eq_true, ↓reduceIte] using restoredRelated
  | language reason =>
    refine ⟨_, restored, enter (.caseLeft runEvaluated ?_), .language _, restoredRelated, restoredFrame⟩
    apply Core.Evaluates.letE (checkpointRestore_all_evaluates _ _ _ _ references
      [.word reason, .unit, .word sourceBalance] restoreBound)
    exact .inLeft (((CodeValue.bound (depth + 6) runEnv (.word reason)).prepend [.unit]).evaluates restored)


private theorem transferFor_noTransfer {mode : AccountCallSemantics.Mode} {source : Word}
    {request : AccountCallSemantics.Request} {state final : AccountCallSemantics.Shared}
    (other : mode ≠ .ordinary) (moved : AccountCallSemantics.transferFor mode source request state = .ok final) :
    final = state := by
  have different : (mode == .ordinary) = false := by
      cases mode <;> first | rfl | contradiction
  simp only [AccountCallSemantics.transferFor, different, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at moved
  exact moved.symm

/-- Every source mode reaches the real dispatcher, including its checkpoint,
mode-specific funds check and child request transformation. -/
theorem dispatch_children_preserves {mode : AccountCallSemantics.Mode}
    {anchors : List CatalogWorldCorrespondence.Anchor} {locations : SharedLocations}
    {shared : AccountRuntime.References} {runFrame : Code → Code → Code} {children : AccountCallSemantics.Children}
    {valid : Store → Prop} {depth : Nat} {environment : Environment} {initial : Store}
    {extended : Code} {source : Word} {request : AccountCallSemantics.Request}
    {state finalState : AccountCallSemantics.Shared} {result : Semantics.Result AccountCallSemantics.Response}
    (childrenPreserved : ChildRunPreservation mode anchors locations shared runFrame children valid depth environment)
    (stable : ∀ {first last}, SharedFrame locations first last → valid first → valid last)
    (references : SharedReferences depth environment shared locations)
    (argument : CodeValue depth environment extended (extendedValue mode source request))
    (related : LinkedSharedStateRel anchors locations state initial) (ready : valid initial)
    (computed : AccountCallSemantics.Dispatch children mode source request state result finalState) :
    ∃ target final, Evaluates environment initial (AccountRuntime.dispatch shared runFrame extended depth) target final ∧
      ResponseRel result target ∧ LinkedSharedStateRel anchors locations finalState final ∧
      SharedFrame locations initial final := by
  by_cases ordinary : mode = .ordinary
  · subst mode
    exact AccountCallCorrespondence.dispatch_children_preserves childrenPreserved stable references argument related ready computed
  have requestCode : CodeValue depth environment (part 0 3 extended) (requestValue request) :=
    argument.part (index := 0) rfl
  cases computed with
  | insufficient checked shortfall =>
    obtain ⟨final, evaluated, retained⟩ := dispatch_insufficient references argument related.shared checked shortfall
    exact ⟨_, final, evaluated, .returned _, related.retained retained, .ofRetains retained⟩
  | transferFault funds failed =>
    have different : (mode == .ordinary) = false := by
      cases mode <;> first | rfl | contradiction
    simp only [AccountCallSemantics.transferFor, different, Bool.false_eq_true, ↓reduceIte] at failed
    contradiction
  | succeeded funds moved executed success =>
    cases transferFor_noTransfer ordinary moved
    rw [dispatch_precompile_eq]
    simpa only [dispatchAfter, success, ↓reduceIte] using
      dispatch_untransferred_preserves childrenPreserved (precompileCode_preservation requestCode) stable references
        argument related ready ordinary funds executed
  | refused funds moved executed failure =>
    cases transferFor_noTransfer ordinary moved
    rw [dispatch_precompile_eq]
    simpa only [dispatchAfter, failure, Bool.false_eq_true, ↓reduceIte] using
      dispatch_untransferred_preserves childrenPreserved (precompileCode_preservation requestCode) stable references
        argument related ready ordinary funds executed
  | fault funds moved executed =>
    cases transferFor_noTransfer ordinary moved
    rw [dispatch_precompile_eq]
    exact dispatch_untransferred_preserves childrenPreserved (precompileCode_preservation requestCode) stable references
      argument related ready ordinary funds executed

end Solcore.Frontend.RustHull.AccountCallModeCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.AccountCallModeHandlersCorrespondence
/-! The actual frame handler captures its execution address separately from
request caller and value. The selected mode is part of the captured Core body. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.AccountCallModeCorrespondence
open Core Correspondence ScalarExecution CodeBuilder
open AccountCallCorrespondence (SharedLocations DispatcherClosure)

structure CallHandlerClosure (mode : AccountCallSemantics.Mode) (source : Word)
    (dispatcherLocation : Nat) (value : Value) where
  depth : Nat
  captured : Environment
  frame : Code
  dispatcher : Code
  closure : CapturedClosure (AccountRuntime.frameCallHandler mode.number frame dispatcher depth) captured value
  address : CodeValue depth captured (part 0 8 frame) (.word source)
  dispatcherReference : CodeValue depth captured dispatcher
    (.cellRef (OptionalCell.cellType AccountRuntime.dispatchCallbackType) dispatcherLocation)

structure InstalledHandlers (mode : AccountCallSemantics.Mode) (locations : SharedLocations) (source : Word)
    (handlerLocation dispatcherLocation : Nat) (store : Store) where
  dispatchValue : Value
  handlerValue : Value
  dispatch : DispatcherClosure locations dispatchValue
  handler : CallHandlerClosure mode source dispatcherLocation handlerValue
  dispatchRead : store.read? dispatcherLocation = some (.inRight .unit dispatchValue)
  handlerRead : store.read? handlerLocation = some (.inRight .unit handlerValue)

/-- Existing ordinary closures carry the same concrete body and references. -/
def CallHandlerClosure.of_ordinary {source : Word} {dispatcher : Nat} {value : Value}
    (handler : AccountCallCorrespondence.CallHandlerClosure source dispatcher value) :
    CallHandlerClosure .ordinary source dispatcher value where
  depth := handler.depth
  captured := handler.captured
  frame := handler.frame
  dispatcher := handler.dispatcher
  closure := handler.closure
  address := handler.address
  dispatcherReference := handler.dispatcherReference

end Solcore.Frontend.RustHull.AccountCallModeCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.AccountCallModeCallbackCorrespondence
/-! Captured runtime handlers execute child-capable dispatch. The internal
child interface is discharged by compiled frame execution before the public
contract theorem is exposed. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.AccountCallModeCorrespondence
open Core Correspondence ScalarExecution CodeBuilder CallTransportCorrespondence
open AccountCallCorrespondence hiding extendedValue ChildRunPreservation CallHandlerClosure InstalledHandlers dispatch_children_preserves

theorem dispatcher_apply_children_preserves {mode : AccountCallSemantics.Mode} {locations : SharedLocations} {value : Core.Value}
    (closure : DispatcherClosure locations value)
    {anchors : List CatalogWorldCorrespondence.Anchor} {children : AccountCallSemantics.Children} {valid : Core.Store → Prop}
    (childrenPreserved : ChildRunPreservation mode anchors locations closure.shared closure.runFrame children valid closure.depth closure.captured)
    (stable : ∀ {first last}, SharedFrame locations first last → valid first → valid last)
    {source : Core.Word} {request : AccountCallSemantics.Request}
    {state finalState : AccountCallSemantics.Shared} {result : Semantics.Result AccountCallSemantics.Response}
    (computed : AccountCallSemantics.Dispatch children mode source request state result finalState)
    {environment : Core.Environment} {before middle initial : Core.Store} {function argument : Core.Expr}
    (related : LinkedSharedStateRel anchors locations state initial) (ready : valid initial)
    (resolved : Core.Evaluates environment before function value middle)
    (supplied : Core.Evaluates environment middle argument (extendedValue mode source request) initial) :
    ∃ target final, Core.Evaluates environment before (.apply function argument) target final ∧
      ResponseRel result target ∧ LinkedSharedStateRel anchors locations finalState final ∧
      SharedFrame locations initial final := by
  rcases closure with ⟨depth, captured, shared, runFrame, capturedClosure, references⟩
  cases capturedClosure
  obtain ⟨target, final, evaluated, resultRelated, finalRelated, frame⟩ :=
    dispatch_children_preserves (childrenPreserved.prepend [extendedValue mode source request]) stable
      (references.prepend [extendedValue mode source request])
      (CodeValue.bound depth captured (extendedValue mode source request)) related ready computed
  exact ⟨target, final, .apply resolved supplied evaluated, resultRelated, finalRelated, frame⟩

theorem CallHandlerClosure.apply_children_preserves {mode : AccountCallSemantics.Mode} {locations : SharedLocations} {source : Core.Word}
    {dispatcherLocation : Nat} {handlerValue dispatchValue : Core.Value}
    (handler : CallHandlerClosure mode source dispatcherLocation handlerValue)
    (dispatcher : DispatcherClosure locations dispatchValue)
    {anchors : List CatalogWorldCorrespondence.Anchor} {children : AccountCallSemantics.Children} {valid : Core.Store → Prop}
    (childrenPreserved : ChildRunPreservation mode anchors locations dispatcher.shared dispatcher.runFrame children valid dispatcher.depth dispatcher.captured)
    (stable : ∀ {first last}, SharedFrame locations first last → valid first → valid last)
    {request : AccountCallSemantics.Request} {state finalState : AccountCallSemantics.Shared}
    {result : Semantics.Result AccountCallSemantics.Response}
    (computed : AccountCallSemantics.Dispatch children mode source request state result finalState)
    {environment : Core.Environment} {before middle initial : Core.Store} {function argument : Core.Expr}
    (related : LinkedSharedStateRel anchors locations state initial) (ready : valid initial)
    (dispatchRead : initial.read? dispatcherLocation = some (.inRight .unit dispatchValue))
    (resolved : Core.Evaluates environment before function handlerValue middle)
    (supplied : Core.Evaluates environment middle argument (requestValue request) initial) :
    ∃ target final, Core.Evaluates environment before (.apply function argument) target final ∧
      ResponseRel result target ∧ LinkedSharedStateRel anchors locations finalState final ∧
      SharedFrame locations initial final := by
  rcases handler with ⟨depth, captured, frame, dispatchRef, capturedClosure, address, dispatcherReference⟩
  cases capturedClosure
  have read := OptionalCell.read_success (Word.ofNatModulo 7)
    ((dispatcherReference.prepend [requestValue request]).evaluates initial) dispatchRead
  have requestBound := CodeValue.bound depth captured (requestValue request)
  have dispatchBound := CodeValue.bound (depth + 1) (requestValue request :: captured) dispatchValue
  have suppliedExtended := Core.Evaluates.pair ((requestBound.prepend [dispatchValue]).evaluates initial)
    (.pair (.word (value := Word.ofNatModulo mode.number)) ((address.prepend [dispatchValue, requestValue request]).evaluates initial))
  obtain ⟨target, final, evaluated, resultRelated, finalRelated, kept⟩ :=
    dispatcher_apply_children_preserves dispatcher childrenPreserved stable computed related ready (dispatchBound.evaluates initial) suppliedExtended
  refine ⟨target, final, .apply resolved supplied ?_, resultRelated, finalRelated, kept⟩
  exact LanguageResult.bind_success Calls.responseType read evaluated

/-- Handler-cell reads are the reads installed by the actual initializer;
callback correctness follows from the captured body, not a premise. -/
theorem InstalledHandlers.apply_children_preserves {mode : AccountCallSemantics.Mode} {locations : SharedLocations} {source : Core.Word}
    {handlerLocation dispatcherLocation : Nat} {initial : Core.Store}
    (installed : InstalledHandlers mode locations source handlerLocation dispatcherLocation initial)
    {anchors : List CatalogWorldCorrespondence.Anchor} {children : AccountCallSemantics.Children} {valid : Core.Store → Prop}
    (childrenPreserved : ChildRunPreservation mode anchors locations installed.dispatch.shared installed.dispatch.runFrame children valid
      installed.dispatch.depth installed.dispatch.captured)
    (stable : ∀ {first last}, SharedFrame locations first last → valid first → valid last)
    {request : AccountCallSemantics.Request} {state finalState : AccountCallSemantics.Shared}
    {result : Semantics.Result AccountCallSemantics.Response}
    (computed : AccountCallSemantics.Dispatch children mode source request state result finalState)
    {environment : Core.Environment} {function argument : Core.Expr}
    (related : LinkedSharedStateRel anchors locations state initial) (ready : valid initial)
    (resolved : Core.Evaluates environment initial function installed.handlerValue initial)
    (supplied : Core.Evaluates environment initial argument (requestValue request) initial) :
    ∃ target final, Core.Evaluates environment initial (.apply function argument) target final ∧
      ResponseRel result target ∧ LinkedSharedStateRel anchors locations finalState final ∧
      SharedFrame locations initial final :=
  installed.handler.apply_children_preserves installed.dispatch childrenPreserved stable computed related ready installed.dispatchRead resolved supplied

end Solcore.Frontend.RustHull.AccountCallModeCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.AccountLifecycleCorrespondence
/-! The actual lifecycle code updates the current world and balance cells.
Helper allocations are retained, and all other existing cells are preserved. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.AccountLifecycleCorrespondence
open Core Correspondence ScalarExecution CodeBuilder
open AccountCallCorrespondence (retained_read lookup_preserves insert_preserves)
open StorageCorrespondence (Accounts)

abbrev Frame := StorageCorrespondence.FinalizeFrame

theorem frame_retained {worldLocation balancesLocation : Nat} {initial final : Core.Store}
    (retained : StoreRetains initial final) : Frame worldLocation balancesLocation initial final :=
  ⟨retained.length_le, fun _ _ _ _ found => retained_read retained found⟩

theorem frame_trans {worldLocation balancesLocation : Nat} {initial middle final : Core.Store}
    (first : Frame worldLocation balancesLocation initial middle)
    (second : Frame worldLocation balancesLocation middle final) : Frame worldLocation balancesLocation initial final :=
  ⟨Nat.le_trans first.length_le second.length_le,
    fun location value worldDifferent balancesDifferent found =>
      second.preserved location value worldDifferent balancesDifferent
        (first.preserved location value worldDifferent balancesDifferent found)⟩

theorem frame_write {worldLocation balancesLocation : Nat} (initial : Core.Store) (value : Core.Value)
    {location : Nat} (changed : location = worldLocation ∨ location = balancesLocation) :
    Frame worldLocation balancesLocation initial (initial.set location value) := by
  refine ⟨by simp, ?_⟩
  intro other old differentWorld differentBalances found
  have different : location ≠ other := by rcases changed with rfl | rfl <;> exact Ne.symm (by assumption)
  exact (List.getElem?_set_ne different).trans found

/-- This is the actual private publish helper, exposed only as a proof-local
builder so the runtime module needs no visibility or behavioral change. -/
def publishCode (world balances current record nextBalances : Code) : Code :=
  choose (part 7 9 record)
    (bindResult .unit (fun depth => AccountState.put (load world depth) (current depth)
      (AccountState.replace (record depth) 8 (.bool true))) fun nextWorld =>
      bind (store balances nextBalances) fun _ => success (store world nextWorld))
    (success (store balances nextBalances))

theorem replaceDestroyed_evaluates {environment : Core.Environment} {store : Core.Store}
    {recordExpr : Core.Expr} {account : AccountState.Account} {identity : Nat}
    (original : Core.Evaluates environment store recordExpr (StorageCorrespondence.record account identity) store) :
    Core.Evaluates environment store (AccountState.replace recordExpr 8 (.bool true))
      (StorageCorrespondence.record {account with destroyed := true} identity) store := by
  exact .pair (.first original)
    (.pair (.first (.second original))
      (.pair (.first (.second (.second original)))
        (.pair (.first (.second (.second (.second original))))
          (.pair (.first (.second (.second (.second (.second original)))))
            (.pair (.first (.second (.second (.second (.second (.second original))))))
              (.pair (.first (.second (.second (.second (.second (.second (.second original)))))))
                (.pair (.first (.second (.second (.second (.second (.second (.second (.second original)))))))) .bool)))))))

theorem publish_evaluates {depth : Nat} {environment : Core.Environment} {initial : Core.Store}
    {world balances current record nextBalances : Code} {accounts : Accounts}
    {initialBalances next : StorageSemantics.Words} {currentAddress : Word}
    {account : AccountState.Account} {identity worldLocation balancesLocation : Nat}
    (worldValue : CodeValue depth environment world (.cellRef AccountState.type worldLocation))
    (balancesValue : CodeValue depth environment balances (.cellRef WordMapping.type balancesLocation))
    (currentValue : CodeValue depth environment current (.word currentAddress))
    (recordValue : CodeValue depth environment record (StorageCorrespondence.record account identity))
    (nextValue : ∀ (extra : Core.Environment) (store : Core.Store), store.read? balancesLocation = some (WordMapping.encode initialBalances) →
      Core.Evaluates (extra ++ environment) store (nextBalances (depth + extra.length)) (WordMapping.encode next) store)
    (worldRead : initial.read? worldLocation = some (StorageCorrespondence.world accounts))
    (balancesRead : initial.read? balancesLocation = some (WordMapping.encode initialBalances))
    (separate : worldLocation ≠ balancesLocation) :
    ∃ final, Core.Evaluates environment initial (publishCode world balances current record nextBalances depth)
      (.inRight .word .unit) final ∧
      final.read? worldLocation = some (StorageCorrespondence.world (publishAccounts accounts currentAddress account identity)) ∧
      final.read? balancesLocation = some (WordMapping.encode next) ∧ Frame worldLocation balancesLocation initial final := by
  have createdValue : Core.Evaluates environment initial (part 7 9 record depth) (.bool account.created) initial :=
    (recordValue.part (index := 7) rfl).evaluates initial
  by_cases created : account.created = true
  · have inserted := StorageCorrespondence.put_evaluates accounts currentAddress {account with destroyed := true} identity
      (.loadCell (worldValue.evaluates initial) worldRead) (currentValue.evaluates initial)
      (replaceDestroyed_evaluates (recordValue.evaluates initial))
    let prepared := StorageCorrespondence.putStore accounts currentAddress {account with destroyed := true} identity environment initial
    let updated := StorageCorrespondence.world (publishAccounts accounts currentAddress account identity)
    have inserted' : Core.Evaluates environment initial
        (AccountState.put (load world depth) (current depth) (AccountState.replace (record depth) 8 (.bool true)))
        (.inRight .word updated) prepared := by simpa only [updated, prepared, publishAccounts, created, ↓reduceIte, CodeBuilder.load] using inserted
    have retained : StoreRetains initial prepared := StoreRetains.append _ _
    have worldPrepared := retained_read retained worldRead
    have balancesPrepared := retained_read retained balancesRead
    have balanceWrite : prepared.write? balancesLocation (WordMapping.encode next) =
        some (prepared.set balancesLocation (WordMapping.encode next)) :=
      Store.write?_eq_some_iff.mpr ⟨(List.getElem?_eq_some_iff.mp balancesPrepared).1, rfl⟩
    have worldMiddle := (Store.write?_preserves_other balanceWrite separate).trans worldPrepared
    have worldWrite : Core.Store.write? (prepared.set balancesLocation (WordMapping.encode next)) worldLocation updated =
        some ((prepared.set balancesLocation (WordMapping.encode next)).set worldLocation updated) :=
      Store.write?_eq_some_iff.mpr ⟨(List.getElem?_eq_some_iff.mp worldMiddle).1, rfl⟩
    refine ⟨_, ?_, Store.write?_reads_written worldWrite,
      (Store.write?_preserves_other worldWrite (Ne.symm separate)).trans (Store.write?_reads_written balanceWrite),
      frame_trans (frame_retained retained) (frame_trans (frame_write _ _ (.inr rfl)) (frame_write _ _ (.inl rfl)))⟩
    apply Core.Evaluates.ifTrue (by simpa only [created] using createdValue)
    apply LanguageResult.bind_success .unit inserted'
    apply Core.Evaluates.letE (.storeCell ((balancesValue.prepend [updated]).evaluates _) balancesPrepared
      (nextValue [updated] prepared balancesPrepared) balanceWrite)
    exact .inRight (.storeCell ((worldValue.prepend [.unit, updated]).evaluates _) worldMiddle
      (((CodeValue.bound depth environment updated).prepend [.unit]).evaluates _) worldWrite)
  · have notCreated : account.created = false := Bool.eq_false_iff.mpr created
    have written : initial.write? balancesLocation (WordMapping.encode next) =
        some (initial.set balancesLocation (WordMapping.encode next)) :=
      Store.write?_eq_some_iff.mpr ⟨(List.getElem?_eq_some_iff.mp balancesRead).1, rfl⟩
    refine ⟨_, .ifFalse (by simpa only [notCreated] using createdValue)
      (.inRight (.storeCell (balancesValue.evaluates _) balancesRead (nextValue [] initial balancesRead) written)), ?_,
      Store.write?_reads_written written, frame_write _ _ (.inr rfl)⟩
    simpa only [publishAccounts, notCreated, Bool.false_eq_true, ↓reduceIte] using
      (Store.write?_preserves_other written separate).trans worldRead


def recordOutcome (accounts : Accounts) (balances : StorageSemantics.Words) (current beneficiary : Word)
    (account : AccountState.Account) (identity : Nat) : Except Word (Accounts × StorageSemantics.Words) :=
  (AccountLifecycleSemantics.balances account.created current beneficiary balances).map fun next =>
    (publishAccounts accounts current account identity, next)

def destroyRecordCode (world balances current recipient record : Code) : Code :=
  let finish := publishCode world balances current record
  bindResult .unit (lookup (load balances) current) fun amount =>
  choose (binary .wordEq current recipient)
    (choose (part 7 9 record)
      (choose (binary .wordEq amount (number 0)) (finish (load balances))
        (bindResult .unit (insert (load balances) current (number 0)) finish))
      (success unit))
    (choose (binary .wordEq amount (number 0)) (finish (load balances))
      (bindResult .unit (lookup (load balances) recipient) fun recipientBalance =>
        choose (binary .wordGt recipientBalance (binary .wordSub (number (wordModulus - 1)) amount))
          (failure .unit (number 12))
          (bindResult .unit (insert (load balances) current (number 0)) fun debited =>
            bindResult .unit (insert debited recipient (binary .wordAdd recipientBalance amount)) finish)))

set_option linter.unusedSimpArgs false in
theorem destroyRecord_preserves {depth : Nat} {environment : Core.Environment} {initial : Core.Store}
    {world balances current recipient record : Code} {accounts : Accounts}
    {initialBalances : StorageSemantics.Words} {currentAddress recipientAddress : Word}
    {account : AccountState.Account} {identity worldLocation balancesLocation : Nat}
    (worldValue : CodeValue depth environment world (.cellRef AccountState.type worldLocation))
    (balancesValue : CodeValue depth environment balances (.cellRef WordMapping.type balancesLocation))
    (currentValue : CodeValue depth environment current (.word currentAddress))
    (recipientValue : CodeValue depth environment recipient (.word recipientAddress))
    (recordValue : CodeValue depth environment record (StorageCorrespondence.record account identity))
    (worldRead : initial.read? worldLocation = some (StorageCorrespondence.world accounts))
    (balancesRead : initial.read? balancesLocation = some (WordMapping.encode initialBalances))
    (separate : worldLocation ≠ balancesLocation) :
    ∃ final, Core.Evaluates environment initial (destroyRecordCode world balances current recipient record depth)
      (StorageCorrespondence.unitResult (recordOutcome accounts initialBalances currentAddress recipientAddress account identity)) final ∧
      final.read? worldLocation = some (StorageCorrespondence.world
        (nextAccounts accounts (recordOutcome accounts initialBalances currentAddress recipientAddress account identity))) ∧
      final.read? balancesLocation = some (WordMapping.encode
        (nextBalances initialBalances (recordOutcome accounts initialBalances currentAddress recipientAddress account identity))) ∧
      Frame worldLocation balancesLocation initial final := by
  obtain ⟨first, amountLooked, firstRetained⟩ := lookup_preserves
    (.loadCell (balancesValue.evaluates initial) balancesRead) (currentValue.evaluates initial)
  let amount := StorageSemantics.readWord currentAddress initialBalances
  let firstEnv : Core.Environment := [.word amount]
  have amountBound := CodeValue.bound depth environment (.word amount)
  have firstWorld := retained_read firstRetained worldRead
  have firstBalances := retained_read firstRetained balancesRead
  have sameValue : Core.Evaluates (firstEnv ++ environment) first
      (binary .wordEq current recipient (depth + 1)) (.bool (currentAddress == recipientAddress)) first :=
    .binary ((currentValue.prepend firstEnv).evaluates first) ((recipientValue.prepend firstEnv).evaluates first) rfl
  have createdValue : Core.Evaluates (firstEnv ++ environment) first
      (part 7 9 record (depth + 1)) (.bool account.created) first :=
    ((recordValue.prepend firstEnv).part (index := 7) rfl).evaluates first
  have zeroValue : Core.Evaluates (firstEnv ++ environment) first
      (binary .wordEq (fun here => .var (here - depth - 1)) (number 0) (depth + 1))
      (.bool (amount == Word.zero)) first := .binary (amountBound.evaluates first) .word rfl
  have zeroFinish : ∃ final, Core.Evaluates (firstEnv ++ environment) first
      (publishCode world balances current record (load balances) (depth + 1)) (.inRight .word .unit) final ∧
      final.read? worldLocation = some (StorageCorrespondence.world (publishAccounts accounts currentAddress account identity)) ∧
      final.read? balancesLocation = some (WordMapping.encode initialBalances) ∧
      Frame worldLocation balancesLocation first final := by
    apply publish_evaluates (worldValue.prepend firstEnv) (balancesValue.prepend firstEnv)
      (currentValue.prepend firstEnv) (recordValue.prepend firstEnv) ?_ firstWorld firstBalances separate
    intro extra store read
    exact .loadCell ((balancesValue.prepend firstEnv) extra store) read
  let debited := StorageSemantics.writeWord currentAddress Word.zero initialBalances
  have debitFinish : ∃ final, Core.Evaluates (firstEnv ++ environment) first
      (bindResult .unit (insert (load balances) current (number 0))
        (publishCode world balances current record) (depth + 1)) (.inRight .word .unit) final ∧
      final.read? worldLocation = some (StorageCorrespondence.world (publishAccounts accounts currentAddress account identity)) ∧
      final.read? balancesLocation = some (WordMapping.encode debited) ∧
      Frame worldLocation balancesLocation first final := by
    obtain ⟨middle, inserted, retained⟩ := insert_preserves
      (.loadCell ((balancesValue.prepend firstEnv).evaluates first) firstBalances)
      ((currentValue.prepend firstEnv).evaluates first) (.word (value := Word.zero))
    have bound := CodeValue.bound (depth + 1) (firstEnv ++ environment) (WordMapping.encode debited)
    obtain ⟨final, evaluated, worldFound, balancesFound, frame⟩ :=
      publish_evaluates (nextBalances := fun here => .var (here - (depth + 1) - 1)) (next := debited) ((worldValue.prepend firstEnv).prepend [WordMapping.encode debited])
        ((balancesValue.prepend firstEnv).prepend [WordMapping.encode debited])
        ((currentValue.prepend firstEnv).prepend [WordMapping.encode debited])
        ((recordValue.prepend firstEnv).prepend [WordMapping.encode debited])
        (fun extra store _ => by simpa only [firstEnv, List.cons_append, List.nil_append, List.length_cons, List.length_nil] using bound extra store)
        (retained_read retained firstWorld) (retained_read retained firstBalances) separate
    exact ⟨final, LanguageResult.bind_success .unit inserted evaluated, worldFound, balancesFound,
      frame_trans (frame_retained retained) frame⟩
  cases same : currentAddress == recipientAddress with
  | true =>
    cases created : account.created with
    | false =>
      have outcome : recordOutcome accounts initialBalances currentAddress recipientAddress account identity =
          .ok (accounts, initialBalances) := by
        simp only [recordOutcome, AccountLifecycleSemantics.balances, same, created, ↓reduceIte,
          Bool.false_eq_true, Except.map, publishAccounts]
      simp only [outcome, StorageCorrespondence.unitResult, nextAccounts, nextBalances]
      refine ⟨first, ?_, firstWorld, firstBalances, frame_retained firstRetained⟩
      apply LanguageResult.bind_success .unit amountLooked
      exact .ifTrue (by simpa only [same, firstEnv, amount, List.cons_append, List.nil_append] using sameValue)
        (.ifFalse (by simpa only [created, firstEnv, amount, List.cons_append, List.nil_append] using createdValue) (.inRight .unit))
    | true =>
      cases zero : StorageSemantics.readWord currentAddress initialBalances == Word.zero with
      | true =>
        have outcome : recordOutcome accounts initialBalances currentAddress recipientAddress account identity =
            .ok (publishAccounts accounts currentAddress account identity, initialBalances) := by
          simp only [recordOutcome, AccountLifecycleSemantics.balances, same, created, amount,
            zero, ↓reduceIte, Except.map]
        simp only [outcome, StorageCorrespondence.unitResult, nextAccounts, nextBalances]
        obtain ⟨final, evaluated, worldFound, balancesFound, frame⟩ := zeroFinish
        refine ⟨final, ?_, worldFound, balancesFound, frame_trans (frame_retained firstRetained) frame⟩
        apply LanguageResult.bind_success .unit amountLooked
        exact .ifTrue (by simpa only [same, firstEnv, amount, List.cons_append, List.nil_append] using sameValue)
          (.ifTrue (by simpa only [created, firstEnv, amount, List.cons_append, List.nil_append] using createdValue)
            (.ifTrue (by simpa only [zero, firstEnv, amount, List.cons_append, List.nil_append] using zeroValue) evaluated))
      | false =>
        have outcome : recordOutcome accounts initialBalances currentAddress recipientAddress account identity =
            .ok (publishAccounts accounts currentAddress account identity, debited) := by
          simp only [recordOutcome, AccountLifecycleSemantics.balances, same, created, amount,
            zero, Bool.false_eq_true, ↓reduceIte, Except.map, debited]
        simp only [outcome, StorageCorrespondence.unitResult, nextAccounts, nextBalances]
        obtain ⟨final, evaluated, worldFound, balancesFound, frame⟩ := debitFinish
        refine ⟨final, ?_, worldFound, balancesFound, frame_trans (frame_retained firstRetained) frame⟩
        apply LanguageResult.bind_success .unit amountLooked
        exact .ifTrue (by simpa only [same, firstEnv, amount, List.cons_append, List.nil_append] using sameValue)
          (.ifTrue (by simpa only [created, firstEnv, amount, List.cons_append, List.nil_append] using createdValue)
            (.ifFalse (by simpa only [zero, firstEnv, amount, List.cons_append, List.nil_append] using zeroValue) evaluated))
  | false =>
    cases zero : StorageSemantics.readWord currentAddress initialBalances == Word.zero with
    | true =>
      have outcome : recordOutcome accounts initialBalances currentAddress recipientAddress account identity =
          .ok (publishAccounts accounts currentAddress account identity, initialBalances) := by
        simp only [recordOutcome, AccountLifecycleSemantics.balances, same, Bool.false_eq_true, amount,
          zero, ↓reduceIte, Except.map]
      simp only [outcome, StorageCorrespondence.unitResult, nextAccounts, nextBalances]
      obtain ⟨final, evaluated, worldFound, balancesFound, frame⟩ := zeroFinish
      refine ⟨final, ?_, worldFound, balancesFound, frame_trans (frame_retained firstRetained) frame⟩
      apply LanguageResult.bind_success .unit amountLooked
      exact .ifFalse (by simpa only [same, firstEnv, amount, List.cons_append, List.nil_append] using sameValue)
        (.ifTrue (by simpa only [zero, firstEnv, amount, List.cons_append, List.nil_append] using zeroValue) evaluated)
    | false =>
      obtain ⟨second, recipientLooked, secondRetained⟩ := lookup_preserves
        (.loadCell ((balancesValue.prepend firstEnv).evaluates first) firstBalances)
        ((recipientValue.prepend firstEnv).evaluates first)
      let recipientBalance := StorageSemantics.readWord recipientAddress initialBalances
      let secondEnv : Core.Environment := [.word recipientBalance, .word amount]
      have recipientBound := CodeValue.bound (depth + 1) (firstEnv ++ environment) (.word recipientBalance)
      have secondWorld := retained_read secondRetained firstWorld
      have secondBalances := retained_read secondRetained firstBalances
      have overflowValue : Core.Evaluates (secondEnv ++ environment) second
          (binary .wordGt (fun here => .var (here - (depth + 1) - 1))
            (binary .wordSub (number (wordModulus - 1)) (fun here => .var (here - depth - 1))) (depth + 2))
          (.bool (decide (recipientBalance > Word.maximum.sub amount))) second :=
        .binary (recipientBound.evaluates second)
          (.binary .word ((amountBound.prepend [.word recipientBalance]).evaluates second) rfl) rfl
      by_cases overflow : StorageSemantics.readWord recipientAddress initialBalances > Word.maximum.sub (StorageSemantics.readWord currentAddress initialBalances)
      · have outcome : recordOutcome accounts initialBalances currentAddress recipientAddress account identity =
            .error (Word.ofNatModulo 12) := by
          simp only [recordOutcome, AccountLifecycleSemantics.balances, same, Bool.false_eq_true, amount,
            zero, recipientBalance, overflow, ↓reduceIte, Except.map]
        simp only [outcome, StorageCorrespondence.unitResult, nextAccounts, nextBalances]
        refine ⟨second, ?_, secondWorld, secondBalances, frame_retained (firstRetained.trans secondRetained)⟩
        apply LanguageResult.bind_success .unit amountLooked
        apply Core.Evaluates.ifFalse (by simpa only [same, firstEnv, amount, List.cons_append, List.nil_append] using sameValue)
        apply Core.Evaluates.ifFalse (by simpa only [zero, firstEnv, amount, List.cons_append, List.nil_append] using zeroValue)
        apply LanguageResult.bind_success .unit recipientLooked
        exact .ifTrue (by simpa only [overflow, decide_true, firstEnv, secondEnv, amount, recipientBalance, List.cons_append, List.nil_append] using overflowValue)
          (.inLeft .word)
      · let credited := StorageSemantics.writeWord recipientAddress (recipientBalance.add amount) debited
        obtain ⟨third, debitLooked, thirdRetained⟩ := insert_preserves
          (.loadCell ((balancesValue.prepend secondEnv).evaluates second) secondBalances)
          ((currentValue.prepend secondEnv).evaluates second) (.word (value := Word.zero))
        let thirdEnv : Core.Environment := WordMapping.encode debited :: secondEnv
        have debitBound := CodeValue.bound (depth + 2) (secondEnv ++ environment) (WordMapping.encode debited)
        obtain ⟨fourth, creditLooked, fourthRetained⟩ := insert_preserves
          (debitBound.evaluates third) ((recipientValue.prepend thirdEnv).evaluates third)
          (.binary (op := .wordAdd) ((recipientBound.prepend [WordMapping.encode debited]).evaluates third)
            ((amountBound.prepend [WordMapping.encode debited, .word recipientBalance]).evaluates third) rfl)
        let fourthEnv : Core.Environment := WordMapping.encode credited :: thirdEnv
        have creditBound := CodeValue.bound (depth + 3) (thirdEnv ++ environment) (WordMapping.encode credited)
        have retained := ((firstRetained.trans secondRetained).trans thirdRetained).trans fourthRetained
        obtain ⟨final, published, worldFound, balancesFound, frame⟩ :=
          publish_evaluates (nextBalances := fun here => .var (here - (depth + 3) - 1)) (next := credited) (worldValue.prepend fourthEnv) (balancesValue.prepend fourthEnv)
            (currentValue.prepend fourthEnv) (recordValue.prepend fourthEnv)
            (fun extra store _ => by simpa only [firstEnv, secondEnv, thirdEnv, fourthEnv, List.cons_append, List.nil_append, List.length_cons, List.length_nil] using creditBound extra store)
            (retained_read retained worldRead) (retained_read retained balancesRead) separate
        have outcome : recordOutcome accounts initialBalances currentAddress recipientAddress account identity =
            .ok (publishAccounts accounts currentAddress account identity, credited) := by
          simp only [recordOutcome, AccountLifecycleSemantics.balances, same, Bool.false_eq_true, amount,
            zero, recipientBalance, overflow, ↓reduceIte, Except.map, credited, debited]
        simp only [outcome, StorageCorrespondence.unitResult, nextAccounts, nextBalances]
        refine ⟨final, ?_, worldFound, balancesFound, frame_trans (frame_retained retained) frame⟩
        apply LanguageResult.bind_success .unit amountLooked
        apply Core.Evaluates.ifFalse (by simpa only [same, firstEnv, amount, List.cons_append, List.nil_append] using sameValue)
        apply Core.Evaluates.ifFalse (by simpa only [zero, firstEnv, amount, List.cons_append, List.nil_append] using zeroValue)
        apply LanguageResult.bind_success .unit recipientLooked
        apply Core.Evaluates.ifFalse (by simpa only [overflow, decide_false, firstEnv, secondEnv, amount, recipientBalance, List.cons_append, List.nil_append] using overflowValue)
        apply LanguageResult.bind_success .unit debitLooked
        apply LanguageResult.bind_success .unit creditLooked
        exact published

end Solcore.Frontend.RustHull.AccountLifecycleCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.AccountLifecycleDestroyCorrespondence
/-! The actual lifecycle entry evaluates its arguments once, normalizes both
addresses, obtains the current record, and reaches the independently specified
balance and pending-deletion result. Exact account identities are retained. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.AccountLifecycleCorrespondence
open Core Correspondence ScalarExecution CodeBuilder
open AccountCallCorrespondence (retained_read)
open StorageCorrespondence (Accounts)

def argumentsValue (worldLocation balancesLocation : Nat) (current beneficiary : Word) (complete : Bool) : Value :=
  bundleValues [.cellRef AccountState.type worldLocation, .cellRef WordMapping.type balancesLocation,
    .word current, .word beneficiary, .bool complete]

theorem destroy_preserves {environment : Core.Environment} {before store : Core.Store}
    {worldReference balancesReference currentExpr beneficiaryExpr completeExpr : Core.Expr}
    (accounts : Accounts) (balances : StorageSemantics.Words) (worldLocation balancesLocation : Nat)
    (current beneficiary : Word) (complete : Bool)
    (arguments : Core.Evaluates environment before
      (bundle [worldReference, balancesReference, currentExpr, beneficiaryExpr, completeExpr])
      (argumentsValue worldLocation balancesLocation current beneficiary complete) store)
    (worldRead : store.read? worldLocation = some (StorageCorrespondence.world accounts))
    (balancesRead : store.read? balancesLocation = some (WordMapping.encode balances))
    (separate : worldLocation ≠ balancesLocation) :
    ∃ final, Core.Evaluates environment before
      (AccountLifecycle.destroy worldReference balancesReference currentExpr beneficiaryExpr completeExpr)
      (StorageCorrespondence.unitResult (destroyAccounts accounts balances current beneficiary complete)) final ∧
      final.read? worldLocation = some (StorageCorrespondence.world
        (nextAccounts accounts (destroyAccounts accounts balances current beneficiary complete))) ∧
      final.read? balancesLocation = some (WordMapping.encode
        (nextBalances balances (destroyAccounts accounts balances current beneficiary complete))) ∧
      Frame worldLocation balancesLocation store final := by
  let packetValue := argumentsValue worldLocation balancesLocation current beneficiary complete
  let currentAddress := AccountLifecycleSemantics.address current
  let recipientAddress := AccountLifecycleSemantics.address beneficiary
  let args : Code := fun here => .var (here - 0 - 1)
  let currentCode : Code := fun here => .var (here - 1 - 1)
  let recipientCode : Code := fun here => .var (here - 2 - 1)
  let front : Core.Environment := [.word recipientAddress, .word currentAddress, packetValue]
  have argsBound : CodeValue 1 (packetValue :: environment) args packetValue := CodeValue.bound 0 environment packetValue
  have currentEvaluated : Core.Evaluates (packetValue :: environment) store
      (address (part 2 5 args) 1) (.word currentAddress) store :=
    .binary ((argsBound.part (index := 2) rfl).evaluates store) .word rfl
  have currentBound : CodeValue 2 (.word currentAddress :: packetValue :: environment) currentCode (.word currentAddress) :=
    CodeValue.bound 1 (packetValue :: environment) (.word currentAddress)
  have recipientEvaluated : Core.Evaluates (.word currentAddress :: packetValue :: environment) store
      (address (part 3 5 args) 2) (.word recipientAddress) store :=
    .binary (((argsBound.prepend [.word currentAddress]).part (index := 3) rfl).evaluates store) .word rfl
  have recipientBound : CodeValue 3 (front ++ environment) recipientCode (.word recipientAddress) :=
    CodeValue.bound 2 (.word currentAddress :: packetValue :: environment) (.word recipientAddress)
  have currentRelated : CodeValue 3 (front ++ environment) currentCode (.word currentAddress) :=
    currentBound.prepend [.word recipientAddress]
  have argsRelated : CodeValue 3 (front ++ environment) args packetValue :=
    argsBound.prepend [.word recipientAddress, .word currentAddress]
  have worldValue : CodeValue 3 (front ++ environment) (part 0 5 args) (.cellRef AccountState.type worldLocation) :=
    argsRelated.part (index := 0) rfl
  have balancesValue : CodeValue 3 (front ++ environment) (part 1 5 args) (.cellRef WordMapping.type balancesLocation) :=
    argsRelated.part (index := 1) rfl
  have fetched := StorageCorrespondence.get_evaluates accounts currentAddress complete
    (.loadCell (worldValue.evaluates store) worldRead) (currentRelated.evaluates store)
    ((argsRelated.part (index := 4) rfl).evaluates store)
  let fetchedStore := StorageCorrespondence.getStore accounts currentAddress complete (front ++ environment) store
  have retained : StoreRetains store fetchedStore := StoreRetains.append _ _
  cases found : StorageCorrespondence.get accounts currentAddress complete with
  | error reason =>
    have outcome : destroyAccounts accounts balances current beneficiary complete = .error reason := by
      unfold destroyAccounts
      dsimp only
      rw [found]
      rfl
    simp only [outcome, StorageCorrespondence.unitResult, nextAccounts, nextBalances]
    refine ⟨fetchedStore, ?_, retained_read retained worldRead, retained_read retained balancesRead, frame_retained retained⟩
    apply Core.Evaluates.letE arguments
    apply Core.Evaluates.letE currentEvaluated
    apply Core.Evaluates.letE recipientEvaluated
    apply LanguageResult.bind_failure .unit
    simpa only [found, StorageCorrespondence.getValue, front, fetchedStore, args, currentCode, CodeBuilder.load, List.length_cons, List.length_nil, List.cons_append, List.nil_append] using fetched
  | ok pair =>
    rcases pair with ⟨account, identity⟩
    let recordValue := StorageCorrespondence.record account identity
    have recordBound := CodeValue.bound 3 (front ++ environment) recordValue
    obtain ⟨final, evaluated, finalWorld, finalBalances, frame⟩ :=
      destroyRecord_preserves (worldValue.prepend [recordValue]) (balancesValue.prepend [recordValue])
        (currentRelated.prepend [recordValue]) (recipientBound.prepend [recordValue]) recordBound
        (retained_read retained worldRead) (retained_read retained balancesRead) separate
    have outcome : destroyAccounts accounts balances current beneficiary complete =
        recordOutcome accounts balances currentAddress recipientAddress account identity := by
      unfold destroyAccounts
      dsimp only
      rw [found]
      change (do let next ← AccountLifecycleSemantics.balances account.created currentAddress recipientAddress balances; pure (publishAccounts accounts currentAddress account identity, next)) = _
      unfold recordOutcome
      cases AccountLifecycleSemantics.balances account.created currentAddress recipientAddress balances <;> rfl
    simp only [outcome]
    refine ⟨final, ?_, finalWorld, finalBalances, frame_trans (frame_retained retained) frame⟩
    apply Core.Evaluates.letE arguments
    apply Core.Evaluates.letE currentEvaluated
    apply Core.Evaluates.letE recipientEvaluated
    apply LanguageResult.bind_success .unit (by simpa only [found, StorageCorrespondence.getValue, front, fetchedStore, args, currentCode, CodeBuilder.load, List.length_cons, List.length_nil, List.cons_append, List.nil_append] using fetched)
    exact evaluated

end Solcore.Frontend.RustHull.AccountLifecycleCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeCatalogDispatchCorrespondence
/-! The installed dispatcher selects a compiled frame by its actual runtime
identity. The selected branch retains the original frame allocator and child
completion wrapper. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeCatalogDispatchCorrespondence
open Core Correspondence ScalarExecution CodeBuilder

def invokeFrame (slots : List (String × Core.Ty)) (count index : Nat)
    (functions : Code) (shared : AccountRuntime.References) (dispatcher creator record frame : Code) : Code :=
  AccountRuntime.allocateFrame slots shared frame dispatcher creator (present (part 5 8 frame))
    (part 4 9 record) (part 5 9 record) (part 6 9 record) fun cells =>
      bind (apply (part index count functions) (packet cells)) AccountRuntime.childResult

def selectFrame (indices : List Nat) (record : Code) (invoke : Nat → Code) : Code :=
  indices.foldr (fun index fallback =>
    choose (binary .wordEq (part 3 9 record) (number (index + 1))) (invoke index) fallback)
    (failure Calls.responseType (number 16))

def runFrame (slots : List (String × Core.Ty)) (count : Nat)
    (functions : Code) (shared : AccountRuntime.References) (dispatcher creator record frame : Code) : Code :=
  selectFrame (List.range count) record
    (fun index => invokeFrame slots count index functions shared dispatcher creator record frame)

theorem objectHandlers_dispatch (slots : List (String × Core.Ty)) (count : Nat)
    (images : List (Nat × List UInt8)) (catalog : List AccountRuntime.CodeDefinition)
    (functions : Code) (shared : AccountRuntime.References) (dispatcher creator : Code) :
    (AccountRuntime.objectHandlers slots count images catalog functions shared dispatcher creator).1 =
      lambda AccountRuntime.dispatchType (LanguageResult.resultType Calls.responseType)
        (AccountRuntime.dispatch shared (runFrame slots count functions shared dispatcher creator)) := rfl

theorem selectFrame_evaluates {indices : List Nat} {index : Nat} {identity : Word}
    {depth : Nat} {environment : Environment} {initial final : Store}
    {record : Code} {invoke : Nat → Code} {result : Value}
    (selected : indices.find? (fun candidate => identity == Word.ofNatModulo (candidate + 1)) = some index)
    (represented : CodeValue depth environment (part 3 9 record) (.word identity))
    (executed : Core.Evaluates environment initial (invoke index depth) result final) :
    Core.Evaluates environment initial (selectFrame indices record invoke depth) result final := by
  induction indices with
  | nil => simp at selected
  | cons candidate rest ih =>
      by_cases matched : identity == Word.ofNatModulo (candidate + 1)
      · have same : candidate = index := by simpa [List.find?, matched] using selected
        subst candidate
        apply Core.Evaluates.ifTrue
        · exact .binary (represented.evaluates initial) .word (by
            change some (Core.Value.bool (identity == Word.ofNatModulo (index + 1))) = some (Core.Value.bool true)
            rw [matched])
        · exact executed
      · have rejected : (identity == Word.ofNatModulo (candidate + 1)) = false := Bool.eq_false_iff.mpr matched
        apply Core.Evaluates.ifFalse
        · exact .binary (represented.evaluates initial) .word (by
            change some (Core.Value.bool (identity == Word.ofNatModulo (candidate + 1))) = some (Core.Value.bool false)
            rw [rejected])
        · exact ih (by simpa [List.find?, rejected] using selected)

theorem runFrame_evaluates {slots : List (String × Core.Ty)} {count index : Nat}
    {functions : Code} {shared : AccountRuntime.References} {dispatcher creator record frame : Code}
    {depth : Nat} {environment : Environment} {initial final : Store}
    {account : AccountState.Account} {identity : Nat} {result : Value}
    (selected : (List.range count).find? (fun candidate => Word.ofNatModulo identity == Word.ofNatModulo (candidate + 1)) = some index)
    (represented : CodeValue depth environment record (StorageCorrespondence.record account identity))
    (executed : Core.Evaluates environment initial
      (invokeFrame slots count index functions shared dispatcher creator record frame depth) result final) :
    Core.Evaluates environment initial
      (runFrame slots count functions shared dispatcher creator record frame depth) result final :=
  selectFrame_evaluates selected (represented.part (index := 3) rfl) executed

end Solcore.Frontend.RustHull.RuntimeCatalogDispatchCorrespondence
end
