import Solcore.Frontend.RustHull.AccountObservationSemantics
import Solcore.Frontend.RustHull.AccountInspection
import Solcore.Frontend.RustHull.StorageCorrespondence
import Solcore.Frontend.RustHull.MemoryCopyCorrespondence
import Solcore.Frontend.RustHull.EffectStateCorrespondence
import Solcore.Frontend.RustHull.KeccakHashCorrespondence

/-! Account observations execute through the actual catalog lookup. Code hashes
use fresh scratch cells, preserving every pre-existing caller cell. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.AccountInspectionCorrespondence
open Core Correspondence
open StorageCorrespondence (Accounts record world get getValue getStore)

theorem get_error {accounts : Accounts} {target reason : Word} {complete : Bool}
    (found : StorageSemantics.get (accounts.map Prod.fst) target complete = .error reason) :
    get accounts target complete = .error reason := by
  have same := StorageCorrespondence.get_source accounts target complete
  rw [found] at same
  cases actual : get accounts target complete with
  | error actualReason => simpa [actual, Except.map] using same
  | ok account => simp [actual, Except.map] at same

theorem get_ok {accounts : Accounts} {target : Word} {complete : Bool} {account : AccountState.Account}
    (found : StorageSemantics.get (accounts.map Prod.fst) target complete = .ok account) :
    ∃ identity, get accounts target complete = .ok (account, identity) := by
  have same := StorageCorrespondence.get_source accounts target complete
  rw [found] at same
  cases actual : get accounts target complete with
  | error reason => simp [actual, Except.map] at same
  | ok entry =>
      rcases entry with ⟨actualAccount, identity⟩
      have equal : actualAccount = account := by simpa [actual, Except.map] using same
      cases equal
      exact ⟨identity, rfl⟩

theorem get_retains (accounts : Accounts) (target : Word) (complete : Bool)
    (environment : Environment) (store : Store) :
    StoreRetains store (getStore accounts target complete environment store) := by
  obtain ⟨suffix, _, extended⟩ := StorageCorrespondence.getStore_extension accounts target complete environment store
  rw [extended]
  exact StoreRetains.append _ _

theorem record_known {environment : Environment} {store : Store} {expression : Core.Expr}
    {account : AccountState.Account} {identity : Nat}
    (evaluated : Evaluates environment store expression (record account identity) store) :
    Evaluates environment store (projectArgument 6 9 expression) (.bool account.code.isSome) store :=
  .first (.second (.second (.second (.second (.second (.second evaluated))))))

theorem record_size {environment : Environment} {store : Store} {expression : Core.Expr}
    {account : AccountState.Account} {identity : Nat}
    (evaluated : Evaluates environment store expression (record account identity) store) :
    Evaluates environment store (projectArgument 5 9 expression)
      (.word (Word.ofNatModulo (account.code.getD []).length)) store :=
  .first (.second (.second (.second (.second (.second evaluated)))))

theorem record_code {environment : Environment} {store : Store} {expression : Core.Expr}
    {account : AccountState.Account} {identity : Nat}
    (evaluated : Evaluates environment store expression (record account identity) store) :
    Evaluates environment store (projectArgument 4 9 expression)
      (WordMapping.encode (Memory.packBytes (account.code.getD []))) store :=
  .first (.second (.second (.second (.second evaluated))))

theorem size_preserves
    {accounts : Accounts} {complete : Bool} {balances : StorageSemantics.Words} {current target : Word}
    {sourceType : Ty} {state finalState : MemorySemantics.State} {result : Semantics.Result Semantics.Value}
    (computed : AccountObservationSemantics.Builtin (accounts.map Prod.fst) complete balances current
      "extcodesize" sourceType [.word target] state result finalState)
    {environment : Environment} {store : Store} {worldLocation : Nat}
    {worldReference completeExpr targetExpr : Core.Expr}
    (worldFound : store.read? worldLocation = some (world accounts))
    (worldEvaluated : Evaluates environment store worldReference (.cellRef AccountState.type worldLocation) store)
    (completeEvaluated : Evaluates environment store completeExpr (.bool complete) store)
    (targetEvaluated : Evaluates environment store targetExpr (.word target) store) :
    ∃ value final, ResultRel .word result value ∧
      Evaluates environment store (AccountInspection.size worldReference completeExpr targetExpr) value final ∧
      StoreRetains store final := by
  let input := ScalarExecution.bundleValues [.cellRef AccountState.type worldLocation, .bool complete, .word target]
  have fetched := StorageCorrespondence.get_evaluates
    (environment := input :: environment) (initial := store)
    (worldExpr := .loadCell (.first (.var 0)))
    (addressExpr := .binary .wordAnd (.second (.second (.var 0))) (.word (Word.ofNatModulo (2 ^ 160 - 1))))
    (completeExpr := .first (.second (.var 0))) accounts (AccountObservationSemantics.address target) complete
    (.loadCell (.first (.var rfl)) worldFound)
    (.binary (.second (.second (.var rfl))) .word rfl) (.first (.second (.var rfl)))
  have retained := get_retains accounts (AccountObservationSemantics.address target) complete (input :: environment) store
  generalize nameEq : "extcodesize" = name at computed
  cases computed <;> simp only [String.reduceEq] at nameEq
  case sizeFailure reason found =>
      rw [get_error found] at fetched
      refine ⟨.inLeft .word (.word _), _, .language _, ?_, retained⟩
      exact .letE (.pair worldEvaluated (.pair completeEvaluated targetEvaluated))
        (LanguageResult.bind_failure .word fetched)
  case sizeUnknown account unknown found =>
      obtain ⟨identity, actual⟩ := get_ok found
      rw [actual] at fetched
      refine ⟨.inLeft .word (.word (Word.ofNatModulo 15)), _, .language _, ?_, retained⟩
      apply Evaluates.letE (.pair worldEvaluated (.pair completeEvaluated targetEvaluated))
      apply LanguageResult.bind_success .word fetched
      apply Evaluates.ifFalse
      · have observed := record_known (environment := record account identity :: input :: environment)
          (store := getStore accounts (AccountObservationSemantics.address target) complete (input :: environment) store)
          (expression := .var 0) (Evaluates.var rfl)
        simpa only [unknown, Option.isSome_none, CodeBuilder.part, Nat.reduceAdd, Nat.reduceSub] using observed
      · exact .inLeft .word
  case sizeKnown account bytes known found =>
      obtain ⟨identity, actual⟩ := get_ok found
      rw [actual] at fetched
      refine ⟨.inRight .word (.word (AccountObservationSemantics.codeSize bytes)), _, .value (.word _), ?_, retained⟩
      apply Evaluates.letE (.pair worldEvaluated (.pair completeEvaluated targetEvaluated))
      apply LanguageResult.bind_success .word fetched
      apply Evaluates.ifTrue
      · have observed := record_known (environment := record account identity :: input :: environment)
          (store := getStore accounts (AccountObservationSemantics.address target) complete (input :: environment) store)
          (expression := .var 0) (Evaluates.var rfl)
        simpa only [known, Option.isSome_some, CodeBuilder.part, Nat.reduceAdd, Nat.reduceSub] using observed
      · apply Evaluates.inRight
        have observed := record_size (environment := record account identity :: input :: environment)
          (store := getStore accounts (AccountObservationSemantics.address target) complete (input :: environment) store)
          (expression := .var 0) (Evaluates.var rfl)
        simpa only [known, Option.getD_some, AccountObservationSemantics.codeSize, CodeBuilder.part, Nat.reduceAdd, Nat.reduceSub] using observed


theorem copy_preserves
    {accounts : Accounts} {complete : Bool} {balances : StorageSemantics.Words} {current target destination source length : Word}
    {sourceType : Ty} {state finalState : MemorySemantics.State} {result : Semantics.Result Semantics.Value}
    (computed : AccountObservationSemantics.Builtin (accounts.map Prod.fst) complete balances current
      "extcodecopy" sourceType [.word target, .word destination, .word source, .word length] state result finalState)
    {environment : Environment} {store : Store} {worldLocation memoryLocation sizeLocation : Nat}
    {worldReference completeExpr memoryReference sizeReference targetExpr destinationExpr sourceExpr lengthExpr : Core.Expr}
    (worldFound : store.read? worldLocation = some (world accounts))
    (related : MemoryCorrespondence.StateRel memoryLocation sizeLocation state store)
    (worldEvaluated : Evaluates environment store worldReference (.cellRef AccountState.type worldLocation) store)
    (completeEvaluated : Evaluates environment store completeExpr (.bool complete) store)
    (memoryEvaluated : Evaluates environment store memoryReference (.cellRef WordMapping.type memoryLocation) store)
    (sizeEvaluated : Evaluates environment store sizeReference (.cellRef .word sizeLocation) store)
    (targetEvaluated : Evaluates environment store targetExpr (.word target) store)
    (destinationEvaluated : Evaluates environment store destinationExpr (.word destination) store)
    (sourceEvaluated : Evaluates environment store sourceExpr (.word source) store)
    (lengthEvaluated : Evaluates environment store lengthExpr (.word length) store) :
    ∃ value final, ResultRel .unit result value ∧
      Evaluates environment store (AccountInspection.copy worldReference completeExpr memoryReference sizeReference
        targetExpr destinationExpr sourceExpr lengthExpr) value final ∧
      MemoryCorrespondence.StateRel memoryLocation sizeLocation finalState final ∧
      MemoryCorrespondence.Frame memoryLocation sizeLocation store final := by
  let input := ScalarExecution.bundleValues [.cellRef AccountState.type worldLocation, .bool complete,
    .cellRef WordMapping.type memoryLocation, .cellRef .word sizeLocation, .word target,
    .word destination, .word source, .word length]
  have fetched := StorageCorrespondence.get_evaluates
    (environment := input :: environment) (initial := store)
    (worldExpr := .loadCell (projectArgument 0 8 (.var 0)))
    (addressExpr := .binary .wordAnd (projectArgument 4 8 (.var 0)) (.word (Word.ofNatModulo (2 ^ 160 - 1))))
    (completeExpr := projectArgument 1 8 (.var 0)) accounts (AccountObservationSemantics.address target) complete
    (.loadCell (.first (.var rfl)) worldFound)
    (.binary (.first (.second (.second (.second (.second (.var rfl)))))) .word rfl)
    (.first (.second (.var rfl)))
  obtain ⟨suffix, _, extended⟩ := StorageCorrespondence.getStore_extension accounts
    (AccountObservationSemantics.address target) complete (input :: environment) store
  rw [extended] at fetched
  have packed : Evaluates environment store
      (bundle [worldReference, completeExpr, memoryReference, sizeReference,
        targetExpr, destinationExpr, sourceExpr, lengthExpr]) input store :=
    .pair worldEvaluated (.pair completeEvaluated (.pair memoryEvaluated (.pair sizeEvaluated
      (.pair targetEvaluated (.pair destinationEvaluated (.pair sourceEvaluated lengthEvaluated))))))
  generalize nameEq : "extcodecopy" = name at computed
  cases computed <;> simp only at nameEq
  case copyFailure reason found =>
      rw [get_error found] at fetched
      exact ⟨.inLeft .unit (.word _), _, .language _,
        .letE packed (LanguageResult.bind_failure .unit fetched), related.append suffix,
        MemoryCorrespondence.Frame.append _ _ _ _⟩
  case copyUnknown account unknown found =>
      obtain ⟨identity, actual⟩ := get_ok found
      rw [actual] at fetched
      refine ⟨.inLeft .unit (.word (Word.ofNatModulo 15)), _, .language _, ?_, related.append suffix,
        MemoryCorrespondence.Frame.append _ _ _ _⟩
      apply Evaluates.letE packed
      apply LanguageResult.bind_success .unit fetched
      apply Evaluates.ifFalse
      · have observed := record_known (environment := record account identity :: input :: environment)
          (store := store ++ suffix) (expression := .var 0) (Evaluates.var rfl)
        simpa only [unknown, Option.isSome_none, CodeBuilder.part, Nat.reduceAdd, Nat.reduceSub] using observed
      · exact .inLeft .word
  case copyKnown account bytes known found copied =>
      obtain ⟨identity, actual⟩ := get_ok found
      rw [actual] at fetched
      have codeObserved := record_code (environment := record account identity :: input :: environment)
        (store := store ++ suffix) (expression := .var 0) (Evaluates.var rfl)
      simp only [known, Option.getD_some] at codeObserved
      obtain ⟨value, final, resultRelated, evaluated, finalRelated, frame⟩ :=
        MemoryCopyCorrespondence.copyPackedFrom_preserves copied
          (environment := record account identity :: input :: environment)
          (memoryRef := projectArgument 2 8 (.var 1))
          (sizeRef := projectArgument 3 8 (.var 1))
          (destinationExpr := projectArgument 5 8 (.var 1))
          (sourceMapping := projectArgument 4 9 (.var 0))
          (sourceExpr := projectArgument 6 8 (.var 1))
          (lengthExpr := projectArgument 7 8 (.var 1)) (related.append suffix)
          (.first (.second (.second (.var rfl))))
          (.first (.second (.second (.second (.var rfl)))))
          (.first (.second (.second (.second (.second (.second (.var rfl))))))) codeObserved
          (.first (.second (.second (.second (.second (.second (.second (.var rfl))))))))
          (.second (.second (.second (.second (.second (.second (.second (.var rfl))))))))
      refine ⟨value, final, resultRelated, ?_, finalRelated,
        (MemoryCorrespondence.Frame.append _ _ _ suffix).trans frame⟩
      apply Evaluates.letE packed
      apply LanguageResult.bind_success .unit fetched
      apply Evaluates.ifTrue
      · have observed := record_known (environment := record account identity :: input :: environment)
          (store := store ++ suffix) (expression := .var 0) (Evaluates.var rfl)
        simpa only [known, Option.isSome_some, CodeBuilder.part, Nat.reduceAdd, Nat.reduceSub] using observed
      · exact evaluated


theorem emptyAccount_evaluates {environment : Environment} {store : Store}
    {nonceExpr sizeExpr balanceExpr : Core.Expr} (account : AccountState.Account) (bytes : List UInt8) (balance : Word)
    (nonceEvaluated : Evaluates environment store nonceExpr (.word account.nonce) store)
    (sizeEvaluated : Evaluates environment store sizeExpr (.word (AccountObservationSemantics.codeSize bytes)) store)
    (balanceEvaluated : Evaluates environment store balanceExpr (.word balance) store) :
    Evaluates environment store
      (.ifE (.binary .wordEq nonceExpr (.word Word.zero))
        (.ifE (.binary .wordEq sizeExpr (.word Word.zero))
          (.binary .wordEq balanceExpr (.word Word.zero)) (.bool false)) (.bool false))
      (.bool (AccountObservationSemantics.emptyAccount account bytes balance)) store := by
  by_cases nonce : account.nonce == Word.zero
  · simp only [AccountObservationSemantics.emptyAccount, nonce, ↓reduceIte]
    apply Evaluates.ifTrue (.binary nonceEvaluated .word (by simp [BinaryOp.apply, nonce]))
    by_cases size : AccountObservationSemantics.codeSize bytes == Word.zero
    · simp only [size, ↓reduceIte]
      exact .ifTrue (.binary sizeEvaluated .word (by simp [BinaryOp.apply, size]))
        (.binary balanceEvaluated .word rfl)
    · simp only [size]
      exact .ifFalse (.binary sizeEvaluated .word (by simp [BinaryOp.apply, size])) .bool
  · simp only [AccountObservationSemantics.emptyAccount, nonce]
    exact .ifFalse (.binary nonceEvaluated .word (by simp [BinaryOp.apply, nonce])) .bool

/-- Writes through two newly allocated scratch cells cannot change a caller cell. -/
theorem scratch_retains {store final : Store} (words : MemorySemantics.Entries)
    (frame : MemoryCorrespondence.Frame store.length (store ++ [WordMapping.encode words]).length
      ((store ++ [WordMapping.encode words]) ++ [.word Word.zero]) final) : StoreRetains store final := by
  refine ⟨Nat.le_trans (by simp) frame.length, ?_⟩
  intro location bound
  have found : store.read? location = some store[location] := List.getElem?_eq_getElem bound
  rw [found]
  apply frame.read location store[location] (by omega) (by simp; omega)
  exact StorageCorrespondence.appended_read
    (StorageCorrespondence.appended_read found [WordMapping.encode words]) [.word Word.zero]

/-- The code image is hashed in its own cells, with its complete packed length. -/
theorem hash_scratch_preserves {account : AccountState.Account} {identity : Nat} {bytes : List UInt8}
    (known : account.code = some bytes) {result : Semantics.Result Semantics.Value}
    {scratchFinal : MemorySemantics.State}
    (hashed : KeccakSemantics.Hash Word.zero (AccountObservationSemantics.codeSize bytes)
      ⟨Memory.packBytes bytes, Word.zero⟩ result scratchFinal)
    (balance : Word) (rest : Environment) (store : Store) :
    ∃ target final, ResultRel .word result target ∧
      Evaluates (.word balance :: record account identity :: rest) store
        (.letE (.newCell WordMapping.type (projectArgument 4 9 (.var 1)))
          (.letE (.newCell .word (.word Word.zero))
            (Keccak.hash (.var 1) (.var 0) (.word Word.zero) (projectArgument 5 9 (.var 3)))))
        target final ∧ StoreRetains store final := by
  let words := Memory.packBytes bytes
  let withMemory := store ++ [WordMapping.encode words]
  let scratch := withMemory ++ [.word Word.zero]
  let environment := Value.cellRef .word withMemory.length ::
    .cellRef WordMapping.type store.length :: .word balance :: record account identity :: rest
  have related : MemoryCorrespondence.StateRel store.length withMemory.length ⟨words, Word.zero⟩ scratch := by
    refine ⟨by simp [withMemory], ?_, ?_⟩
    · apply StorageCorrespondence.appended_read (suffix := [.word Word.zero])
      exact List.getElem?_concat_length
    · exact List.getElem?_concat_length
  have sized := record_size (environment := environment) (store := scratch) (expression := .var 3) (Evaluates.var rfl)
  simp only [known, Option.getD_some] at sized
  obtain ⟨target, final, resultRelated, evaluated, _, frame⟩ := KeccakHashCorrespondence.hash_preserves
    hashed related (environment := environment) (memoryRef := .var 1) (sizeRef := .var 0)
      (offsetExpr := .word Word.zero) (lengthExpr := projectArgument 5 9 (.var 3))
      (.var rfl) (.var rfl) .word sized
  refine ⟨target, final, resultRelated, ?_, scratch_retains words frame⟩
  apply Evaluates.letE (boundValue := .cellRef WordMapping.type store.length)
    (bodyStore := withMemory)
  · apply Evaluates.newCell
    have code := record_code (environment := .word balance :: record account identity :: rest)
      (store := store) (expression := .var 1) (Evaluates.var rfl)
    simpa only [known, Option.getD_some] using code
  · exact .letE (.newCell .word) evaluated


def hashInput (worldLocation balanceLocation : Nat) (complete : Bool) (target : Word) : Value :=
  ScalarExecution.bundleValues [.cellRef AccountState.type worldLocation, .bool complete,
    .cellRef WordMapping.type balanceLocation, .word target]

/-- The continuation after a successful account read, including its ledger
lookup and the EIP-161 empty-account branch. -/
def hashKnownTail : Core.Expr :=
  LanguageResult.bind .word
    (WordMapping.lookup (.loadCell (projectArgument 2 4 (.var 2))) (.var 1))
    (.ifE
      (.ifE (.binary .wordEq (projectArgument 2 9 (.var 1)) (.word Word.zero))
        (.ifE (.binary .wordEq (projectArgument 5 9 (.var 1)) (.word Word.zero))
          (.binary .wordEq (.var 0) (.word Word.zero)) (.bool false)) (.bool false))
      (.inRight .word (.word Word.zero))
      (.letE (.newCell WordMapping.type (projectArgument 4 9 (.var 1)))
        (.letE (.newCell .word (.word Word.zero))
          (Keccak.hash (.var 1) (.var 0) (.word Word.zero) (projectArgument 5 9 (.var 3))))))

theorem hashKnownTail_preserves
    {account : AccountState.Account} {identity worldLocation balanceLocation : Nat} {complete : Bool}
    {bytes : List UInt8} {balances : StorageSemantics.Words} {target : Word}
    {environment : Environment} {store : Store} {result : Semantics.Result Semantics.Value}
    (known : account.code = some bytes)
    (balancesFound : store.read? balanceLocation = some (WordMapping.encode balances))
    (computed :
      (AccountObservationSemantics.emptyAccount account bytes
        (StorageSemantics.readWord (AccountObservationSemantics.address target) balances) = true ∧
        result = .value (.word Word.zero)) ∨
      (AccountObservationSemantics.emptyAccount account bytes
        (StorageSemantics.readWord (AccountObservationSemantics.address target) balances) = false ∧
        ∃ scratchFinal, KeccakSemantics.Hash Word.zero (AccountObservationSemantics.codeSize bytes)
          ⟨Memory.packBytes bytes, Word.zero⟩ result scratchFinal)) :
    ∃ value final, ResultRel .word result value ∧
      Evaluates (record account identity :: .word (AccountObservationSemantics.address target) ::
        hashInput worldLocation balanceLocation complete target :: environment) store hashKnownTail value final ∧
      StoreRetains store final := by
  let input := hashInput worldLocation balanceLocation complete target
  let rest := Value.word (AccountObservationSemantics.address target) :: input :: environment
  let balance := StorageSemantics.readWord (AccountObservationSemantics.address target) balances
  have looked := WordMapping.lookup_evaluates (environment := record account identity :: rest)
    (initialStore := store) (mapping := .loadCell (projectArgument 2 4 (.var 2))) (keyExpr := .var 1)
    balances (AccountObservationSemantics.address target)
    (.loadCell (.first (.second (.second (.var rfl)))) balancesFound) (.var rfl)
  rw [← StorageCorrespondence.readWord_eq] at looked
  let ledgerStore := WordMapping.installedStore store WordMapping.lookupParameter .word WordMapping.lookupBody
    (.pair (WordMapping.encode balances) (.word (AccountObservationSemantics.address target)))
    (record account identity :: rest)
  have retained : StoreRetains store ledgerStore := StoreRetains.append _ _
  have sized := record_size (environment := .word balance :: record account identity :: rest)
    (store := ledgerStore) (expression := .var 1) (Evaluates.var rfl)
  simp only [known, Option.getD_some] at sized
  have emptyEvaluated := emptyAccount_evaluates account bytes balance
    (nonceExpr := projectArgument 2 9 (.var 1))
    (sizeExpr := projectArgument 5 9 (.var 1)) (balanceExpr := .var 0)
    (.first (.second (.second (.var rfl)))) sized (.var rfl)
  rcases computed with ⟨empty, rfl⟩ | ⟨nonempty, scratchFinal, hashed⟩
  · rw [empty] at emptyEvaluated
    exact ⟨.inRight .word (.word Word.zero), ledgerStore, .value (.word _),
      LanguageResult.bind_success .word looked (.ifTrue emptyEvaluated (.inRight .word)), retained⟩
  · rw [nonempty] at emptyEvaluated
    obtain ⟨value, final, resultRelated, evaluated, finalRetained⟩ :=
      hash_scratch_preserves known hashed balance rest ledgerStore (identity := identity)
    exact ⟨value, final, resultRelated,
      LanguageResult.bind_success .word looked (.ifFalse emptyEvaluated evaluated), retained.trans finalRetained⟩


theorem hash_preserves
    {accounts : Accounts} {complete : Bool} {balances : StorageSemantics.Words} {current target : Word}
    {sourceType : Ty} {state finalState : MemorySemantics.State} {result : Semantics.Result Semantics.Value}
    (computed : AccountObservationSemantics.Builtin (accounts.map Prod.fst) complete balances current
      "extcodehash" sourceType [.word target] state result finalState)
    {environment : Environment} {store : Store} {worldLocation balanceLocation : Nat}
    {worldReference completeExpr balanceReference targetExpr : Core.Expr}
    (worldFound : store.read? worldLocation = some (world accounts))
    (balancesFound : store.read? balanceLocation = some (WordMapping.encode balances))
    (worldEvaluated : Evaluates environment store worldReference (.cellRef AccountState.type worldLocation) store)
    (completeEvaluated : Evaluates environment store completeExpr (.bool complete) store)
    (balanceEvaluated : Evaluates environment store balanceReference (.cellRef WordMapping.type balanceLocation) store)
    (targetEvaluated : Evaluates environment store targetExpr (.word target) store) :
    ∃ value final, ResultRel .word result value ∧
      Evaluates environment store (AccountInspection.hash worldReference completeExpr balanceReference targetExpr) value final ∧
      StoreRetains store final := by
  let input := hashInput worldLocation balanceLocation complete target
  let normalized := AccountObservationSemantics.address target
  let fetchedEnvironment := Value.word normalized :: input :: environment
  have packed : Evaluates environment store
      (bundle [worldReference, completeExpr, balanceReference, targetExpr]) input store :=
    .pair worldEvaluated (.pair completeEvaluated (.pair balanceEvaluated targetEvaluated))
  have fetched := StorageCorrespondence.get_evaluates
    (environment := fetchedEnvironment) (initial := store)
    (worldExpr := .loadCell (projectArgument 0 4 (.var 1))) (addressExpr := .var 0)
    (completeExpr := projectArgument 1 4 (.var 1)) accounts normalized complete
    (.loadCell (.first (.var rfl)) worldFound) (.var rfl) (.first (.second (.var rfl)))
  have retained := get_retains accounts normalized complete fetchedEnvironment store
  have balancesAfter : (getStore accounts normalized complete fetchedEnvironment store).read? balanceLocation =
      some (WordMapping.encode balances) :=
    (retained.read balanceLocation (List.getElem?_eq_some_iff.mp balancesFound).1).trans balancesFound
  generalize nameEq : "extcodehash" = name at computed
  cases computed <;> simp only [String.reduceEq] at nameEq
  case hashFailure reason found =>
    rw [get_error found] at fetched
    refine ⟨.inLeft .word (.word reason), _, .language _, ?_, retained⟩
    exact .letE packed (.letE (.binary (.second (.second (.second (.var rfl)))) .word rfl)
      (LanguageResult.bind_failure .word fetched))
  case hashUnknown account unknown found =>
    obtain ⟨identity, actual⟩ := get_ok found
    rw [actual] at fetched
    refine ⟨.inLeft .word (.word (Word.ofNatModulo 15)), _, .language _, ?_, retained⟩
    apply Evaluates.letE packed
    apply Evaluates.letE (.binary (.second (.second (.second (.var rfl)))) .word rfl)
    apply LanguageResult.bind_success .word fetched
    apply Evaluates.ifFalse
    · have observed := record_known (environment := record account identity :: fetchedEnvironment)
        (store := getStore accounts normalized complete fetchedEnvironment store)
        (expression := .var 0) (Evaluates.var rfl)
      simpa only [unknown, Option.isSome_none, CodeBuilder.part, Nat.reduceAdd, Nat.reduceSub] using observed
    · exact .inLeft .word
  case hashEmpty account bytes known found empty =>
    obtain ⟨identity, actual⟩ := get_ok found
    rw [actual] at fetched
    obtain ⟨value, final, resultRelated, evaluated, finalRetained⟩ :=
      hashKnownTail_preserves (identity := identity) (worldLocation := worldLocation)
        known balancesAfter (Or.inl ⟨empty, rfl⟩)
    refine ⟨value, final, resultRelated, ?_, retained.trans finalRetained⟩
    apply Evaluates.letE packed
    apply Evaluates.letE (.binary (.second (.second (.second (.var rfl)))) .word rfl)
    apply LanguageResult.bind_success .word fetched
    apply Evaluates.ifTrue
    · have observed := record_known (environment := record account identity :: fetchedEnvironment)
        (store := getStore accounts normalized complete fetchedEnvironment store)
        (expression := .var 0) (Evaluates.var rfl)
      simpa only [known, Option.isSome_some, CodeBuilder.part, Nat.reduceAdd, Nat.reduceSub] using observed
    · exact evaluated
  case hashKnown scratchFinal account bytes known found nonempty hashed =>
    obtain ⟨identity, actual⟩ := get_ok found
    rw [actual] at fetched
    obtain ⟨value, final, resultRelated, evaluated, finalRetained⟩ :=
      hashKnownTail_preserves (identity := identity) (worldLocation := worldLocation)
        known balancesAfter (Or.inr ⟨nonempty, scratchFinal, hashed⟩)
    refine ⟨value, final, resultRelated, ?_, retained.trans finalRetained⟩
    apply Evaluates.letE packed
    apply Evaluates.letE (.binary (.second (.second (.second (.var rfl)))) .word rfl)
    apply LanguageResult.bind_success .word fetched
    apply Evaluates.ifTrue
    · have observed := record_known (environment := record account identity :: fetchedEnvironment)
        (store := getStore accounts normalized complete fetchedEnvironment store)
        (expression := .var 0) (Evaluates.var rfl)
      simpa only [known, Option.isSome_some, CodeBuilder.part, Nat.reduceAdd, Nat.reduceSub] using observed
    · exact evaluated

end Solcore.Frontend.RustHull.AccountInspectionCorrespondence
