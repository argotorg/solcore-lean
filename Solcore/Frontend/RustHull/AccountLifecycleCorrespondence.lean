import Solcore.Frontend.RustHull.AccountLifecycleWorldCorrespondence
import Solcore.Frontend.RustHull.AccountCallTransferCorrespondence

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
