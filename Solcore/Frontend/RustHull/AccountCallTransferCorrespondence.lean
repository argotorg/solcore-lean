import Solcore.Frontend.RustHull.AccountCallCheckpointCorrespondence

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
