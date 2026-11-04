import Solcore.Frontend.RustHull.Semantics.World
import Solcore.Frontend.RustHull.Effects
import Solcore.Frontend.RustHull.Internal.StorageState
import Solcore.Frontend.RustHull.Internal.MemoryState
import Solcore.Frontend.RustHull.Internal.Digests
import Solcore.Frontend.RustHull.Internal.NamedFunctions
import Solcore.Frontend.RustHull.Semantics.Memory

/-!
# Effect builtins

Memory, storage, log, Keccak, environment and account observation builtins through the actual
builtin compiler.
-/

section
-- leanmerge: from Solcore.Frontend.RustHull.AccountInspectionCorrespondence
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
end

section
-- leanmerge: from Solcore.Frontend.RustHull.AccountInspectionRenamingCorrespondence
/-! Account inspection builders respect the renaming introduced by the actual
outer builtin compiler. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.AccountInspectionCorrespondence
open Core

set_option linter.unusedSimpArgs false in
theorem size_rename (world complete target : Core.Expr) (mapping : Renaming) :
    (AccountInspection.size world complete target).rename mapping =
      AccountInspection.size (world.rename mapping) (complete.rename mapping) (target.rename mapping) := by
  simp only [AccountInspection.size, CodeBuilder.bind, CodeBuilder.constant, bundle, Core.Expr.rename]
  congr 1
  simp [CodeBuilder.bind, AccountInspection.known, CodeBuilder.bindResult, CodeBuilder.part, CodeBuilder.load,
    CodeBuilder.address, CodeBuilder.binary, CodeBuilder.number, CodeBuilder.constant,
    CodeBuilder.choose, CodeBuilder.success, CodeBuilder.failure, projectArgument,
    AccountState.get, AccountState.lookup, AccountState.defaultRecord, bundle,
    LanguageResult.bind, LanguageResult.success, LanguageResult.failure,
    OrderedMapping.lookup, OrderedMapping.lookupBody, OrderedMapping.optionValue, OrderedMapping.invoke,
    OrderedMapping.runHelper, WordMapping.runHelper, WordMapping.invoke, WordMapping.empty, AccountState.equal, OptionalCell.allocate, OptionalCell.read,
    Core.Expr.rename, Core.Expr.renameList, Core.Renaming.lift, Core.Expr.weakenAt]
  all_goals rfl

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 10000 in
theorem copy_rename (world complete memory size target destination source length : Core.Expr) (mapping : Renaming) :
    (AccountInspection.copy world complete memory size target destination source length).rename mapping =
      AccountInspection.copy (world.rename mapping) (complete.rename mapping) (memory.rename mapping)
        (size.rename mapping) (target.rename mapping) (destination.rename mapping)
        (source.rename mapping) (length.rename mapping) := by
  simp only [AccountInspection.copy, CodeBuilder.bind, CodeBuilder.constant, bundle, Core.Expr.rename]
  congr 1
  simp [CodeBuilder.bind, AccountInspection.known, CodeBuilder.bindResult, CodeBuilder.part, CodeBuilder.load,
    CodeBuilder.address, CodeBuilder.binary, CodeBuilder.number, CodeBuilder.constant,
    CodeBuilder.choose, CodeBuilder.failure, projectArgument,
    AccountState.get, AccountState.lookup, AccountState.defaultRecord, bundle,
    MemoryCopyCorrespondence.copyPackedFrom_rename,
    LanguageResult.bind, LanguageResult.success, LanguageResult.failure,
    OrderedMapping.lookup, OrderedMapping.lookupBody, OrderedMapping.optionValue, OrderedMapping.invoke,
    OrderedMapping.runHelper, WordMapping.runHelper, WordMapping.invoke, WordMapping.empty, AccountState.equal, OptionalCell.allocate, OptionalCell.read,
    Core.Expr.rename, Core.Expr.renameList, Core.Renaming.lift, Core.Expr.weakenAt]
  all_goals rfl

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 10000 in
theorem hash_rename (world complete balances target : Core.Expr) (mapping : Renaming) :
    (AccountInspection.hash world complete balances target).rename mapping =
      AccountInspection.hash (world.rename mapping) (complete.rename mapping)
        (balances.rename mapping) (target.rename mapping) := by
  simp only [AccountInspection.hash, CodeBuilder.bind, CodeBuilder.constant, bundle, Core.Expr.rename]
  congr 1
  simp [CodeBuilder.bind, AccountInspection.known, CodeBuilder.bindResult, CodeBuilder.part, CodeBuilder.load,
    CodeBuilder.address, CodeBuilder.binary, CodeBuilder.number, CodeBuilder.constant,
    CodeBuilder.choose, CodeBuilder.success, CodeBuilder.failure, CodeBuilder.boolean,
    CodeBuilder.allocate, CodeBuilder.lookup, projectArgument,
    AccountState.get, AccountState.lookup, AccountState.defaultRecord, bundle,
    KeccakHashCorrespondence.hash_rename,
    LanguageResult.bind, LanguageResult.success, LanguageResult.failure,
    OrderedMapping.lookup, OrderedMapping.lookupBody, OrderedMapping.optionValue, OrderedMapping.invoke,
    OrderedMapping.runHelper, WordMapping.lookup, WordMapping.lookupBody, WordMapping.runHelper,
    WordMapping.invoke, WordMapping.empty, AccountState.equal, OptionalCell.allocate, OptionalCell.read,
    Core.Expr.rename, Core.Expr.renameList, Core.Renaming.lift, Core.Expr.weakenAt]
  all_goals rfl

end Solcore.Frontend.RustHull.AccountInspectionCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.MemoryCopyBuiltinCorrespondence
/-! The outer Hull builtin compiler determines word arguments and resolves
the memory and calldata references used by copying. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.MemoryCopyBuiltinCorrespondence
open Core Correspondence PureCallCorrespondence EffectBuiltinCorrespondence
open MemoryCopySemantics (Operation)

theorem three_words {arguments : List Lowered} {sources : List Semantics.Value}
    {targets : List Core.Value} (related : ArgumentsRel arguments sources targets)
    (words : ∀ argument ∈ arguments, argument.type = .word) (length : arguments.length = 3) :
    ∃ first second third left middle right,
      arguments = [⟨.word, first⟩, ⟨.word, second⟩, ⟨.word, third⟩] ∧
      sources = [.word left, .word middle, .word right] ∧
      targets = [.word left, .word middle, .word right] := by
  cases related with
  | nil => cases length
  | @cons first rest source sources target targets head tail =>
      obtain ⟨second, third, middle, right, rfl, rfl, rfl⟩ := two_words tail
        (fun argument member => words argument (.tail _ member)) (Nat.succ.inj length)
      have typed := words first (.head _)
      cases first with
      | mk type expression =>
          simp only at typed
          subst type
          cases head with
          | word left => exact ⟨expression, second, third, left, middle, right, rfl, rfl, rfl⟩

theorem inner_arity (operation : Operation) {scope : Scope}
    {arguments : List Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope operation.name arguments = .ok lowered) :
    arguments.length = 3 := by
  cases operation <;>
    rcases arguments with _ | ⟨first, _ | ⟨second, _ | ⟨third, _ | ⟨fourth, rest⟩⟩⟩⟩
  all_goals first
    | rfl
    | change Except.error _ = Except.ok lowered at compiled
      cases compiled

theorem move_components {scope : Scope} {destination source length : Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope "mcopy" [destination, source, length] = .ok lowered) :
    ∃ memory size, Effects.reference scope "memory" WordMapping.type = .ok memory ∧
      Effects.reference scope "memorySize" .word = .ok size ∧
      lowered = ⟨.unit, Memory.mcopy memory size destination source length⟩ := by
  change (do
    let raw ← (do
      let memory ← Effects.reference scope "memory" WordMapping.type
      let size ← Effects.reference scope "memorySize" .word
      pure (Lowered.mk .unit (Memory.mcopy memory size destination source length)) : LowerM Lowered)
    pure raw) = .ok lowered at compiled
  obtain ⟨memory, memoryCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨size, sizeCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
  exact ⟨memory, size, memoryCompiled, sizeCompiled, (Except.ok.inj returned).symm⟩

theorem calldata_components {scope : Scope} {destination source length : Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope "calldatacopy" [destination, source, length] = .ok lowered) :
    ∃ memory size calldata, Effects.reference scope "memory" WordMapping.type = .ok memory ∧
      Effects.reference scope "memorySize" .word = .ok size ∧
      Effects.reference scope "calldata" WordMapping.type = .ok calldata ∧
      lowered = ⟨.unit, Memory.copyPackedFrom memory size destination (.loadCell calldata) source length⟩ := by
  change (do
    let raw ← (do
      let memory ← Effects.reference scope "memory" WordMapping.type
      let size ← Effects.reference scope "memorySize" .word
      let calldata ← Effects.reference scope "calldata" WordMapping.type
      pure (Lowered.mk .unit (Memory.copyPackedFrom memory size destination (.loadCell calldata) source length)) : LowerM Lowered)
    pure raw) = .ok lowered at compiled
  obtain ⟨memory, memoryCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨size, sizeCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨calldata, calldataCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
  exact ⟨memory, size, calldata, memoryCompiled, sizeCompiled, calldataCompiled, (Except.ok.inj returned).symm⟩

theorem preserves (operation : Operation)
    {scope : Scope} {expected : Core.Ty} {arguments : List Lowered} {lowered : Lowered}
    (compiled : lowerBuiltin scope operation.name expected arguments = .ok lowered)
    {calldata : MemorySemantics.Entries} {sourceType : Ty} {sources : List Semantics.Value}
    {state finalState : MemorySemantics.State} {result : Semantics.Result Semantics.Value}
    (called : MemoryCopySemantics.Builtin calldata operation.name sourceType sources state result finalState)
    {targets : List Core.Value} (related : ArgumentsRel arguments sources targets)
    {slots : List EffectSlot} {mapping : Renaming} {environment : Environment}
    {initial store : Store} {memoryLocation sizeLocation : Nat}
    (runtime : EffectEnvironmentRel slots scope mapping environment)
    (memoryMember : ⟨"memory", WordMapping.type, memoryLocation⟩ ∈ slots)
    (sizeMember : ⟨"memorySize", .word, sizeLocation⟩ ∈ slots)
    (available : operation = .calldata → ∃ location, ⟨"calldata", WordMapping.type, location⟩ ∈ slots)
    (calldataRead : ∀ location, ⟨"calldata", WordMapping.type, location⟩ ∈ slots →
      store.read? location = some (WordMapping.encode calldata))
    (stateRelated : MemoryCorrespondence.StateRel memoryLocation sizeLocation state store)
    (packed : Evaluates environment initial ((packArguments arguments).expression.rename mapping)
      (.inRight .word (ScalarExecution.bundleValues targets)) store) :
    ∃ target finalStore,
      ResultRel lowered.type result target ∧
      Evaluates environment initial (lowered.expression.rename mapping) target finalStore ∧
      MemoryCorrespondence.StateRel memoryLocation sizeLocation finalState finalStore ∧
      MemoryCorrespondence.Frame memoryLocation sizeLocation store finalStore := by
  have supported : Effects.supports operation.name = true := by cases operation <;> rfl
  obtain ⟨words, raw, rawCompiled, typed, loweredEqual⟩ := outer_components supported compiled
  have arity : arguments.length = 3 := by
    simpa only [List.length_map, List.length_range] using inner_arity operation rawCompiled
  obtain ⟨destinationExpr, sourceExpr, lengthExpr, destination, source, length, rfl, rfl, rfl⟩ :=
    three_words related words arity
  let input := Value.pair (.word destination) (.pair (.word source) (.word length))
  let inputType := Core.Ty.product .word (.product .word .word)
  have runtime' := runtime.temporary inputType input
  cases operation with
  | move =>
      generalize named : Operation.move.name = actualName at called
      cases called with
      | move executed =>
          obtain ⟨memory, size, memoryCompiled, sizeCompiled, rfl⟩ := move_components rawCompiled
          cases typed
          cases loweredEqual
          obtain ⟨target, finalStore, resultRelated, evaluated, finalRelated, frame⟩ :=
            MemoryCopyCorrespondence.mcopy_preserves executed stateRelated
              (reference_evaluates runtime' memoryMember memoryCompiled store)
              (reference_evaluates runtime' sizeMember sizeCompiled store)
              (.first (.var (index := 0) rfl)) (.first (.second (.var (index := 0) rfl))) (by apply Evaluates.second; apply Evaluates.second; apply Evaluates.var (index := 0); rfl)
          refine ⟨target, finalStore, resultRelated, ?_, finalRelated, frame⟩
          apply LanguageResult.bind_success .unit packed
          rw [MemoryCopyCorrespondence.mcopy_rename]
          exact evaluated
      | calldata _ => exact False.elim ((by decide : ("mcopy" : String) ≠ "calldatacopy") named)
  | calldata =>
      generalize named : Operation.calldata.name = actualName at called
      cases called with
      | calldata executed =>
          obtain ⟨location, member⟩ := available rfl
          obtain ⟨memory, size, inputRef, memoryCompiled, sizeCompiled, inputCompiled, rfl⟩ :=
            calldata_components rawCompiled
          cases typed
          cases loweredEqual
          obtain ⟨target, finalStore, resultRelated, evaluated, finalRelated, frame⟩ :=
            MemoryCopyCorrespondence.copyPackedFrom_preserves executed stateRelated
              (reference_evaluates runtime' memoryMember memoryCompiled store)
              (reference_evaluates runtime' sizeMember sizeCompiled store)
              (.first (.var (index := 0) rfl))
              (.loadCell (reference_evaluates runtime' member inputCompiled store) (calldataRead location member))
              (.first (.second (.var (index := 0) rfl))) (by apply Evaluates.second; apply Evaluates.second; apply Evaluates.var (index := 0); rfl)
          refine ⟨target, finalStore, resultRelated, ?_, finalRelated, frame⟩
          apply LanguageResult.bind_success .unit packed
          rw [MemoryCopyCorrespondence.copyPackedFrom_rename]
          exact evaluated

      | move _ => exact False.elim ((by decide : ("calldatacopy" : String) ≠ "mcopy") named)

end Solcore.Frontend.RustHull.MemoryCopyBuiltinCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.AccountObservationBuiltinCompiler
/-! The actual account builtin compiler fixes the argument shapes and resolves
the runtime references used by account observations. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull

def AccountObservationSemantics.Operation.arity : AccountObservationSemantics.Operation → Nat
  | .selfbalance => 0
  | .copy => 4
  | _ => 1

namespace AccountObservationBuiltinCorrespondence
open Core Correspondence PureCallCorrespondence EffectBuiltinCorrespondence
open AccountObservationSemantics (Operation)

theorem four_words {arguments : List Lowered} {sources : List Semantics.Value}
    {targets : List Core.Value} (related : ArgumentsRel arguments sources targets)
    (words : ∀ argument ∈ arguments, argument.type = .word) (length : arguments.length = 4) :
    ∃ first second third fourth left middle right last,
      arguments = [⟨.word, first⟩, ⟨.word, second⟩, ⟨.word, third⟩, ⟨.word, fourth⟩] ∧
      sources = [.word left, .word middle, .word right, .word last] ∧
      targets = [.word left, .word middle, .word right, .word last] := by
  cases related with
  | nil => cases length
  | @cons first rest source sources target targets head tail =>
      obtain ⟨second, third, fourth, middle, right, last, rfl, rfl, rfl⟩ :=
        MemoryCopyBuiltinCorrespondence.three_words tail
          (fun argument member => words argument (.tail _ member)) (Nat.succ.inj length)
      have typed := words first (.head _)
      cases first with
      | mk type expression =>
          simp only at typed
          subst type
          cases head with
          | word left =>
              exact ⟨expression, second, third, fourth, left, middle, right, last, rfl, rfl, rfl⟩

theorem inner_arity (operation : Operation) {scope : Scope}
    {arguments : List Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope operation.name arguments = .ok lowered) :
    arguments.length = operation.arity := by
  cases operation with
  | balance =>
      rcases arguments with _ | ⟨first, _ | ⟨second, rest⟩⟩
      all_goals first
        | rfl
        | change Except.error _ = Except.ok lowered at compiled
          cases compiled
  | selfbalance =>
      rcases arguments with _ | ⟨first, rest⟩
      · rfl
      · change Except.error _ = Except.ok lowered at compiled
        cases compiled
  | size =>
      change AccountInspection.lowerBuiltin scope "extcodesize" arguments = .ok lowered at compiled
      unfold AccountInspection.lowerBuiltin at compiled
      obtain ⟨world, _, compiled⟩ := lower_bind_eq_ok.mp compiled
      obtain ⟨complete, _, compiled⟩ := lower_bind_eq_ok.mp compiled
      rcases arguments with _ | ⟨first, _ | ⟨second, rest⟩⟩
      all_goals first
        | rfl
        | change Except.error _ = Except.ok lowered at compiled
          cases compiled
  | copy =>
      change AccountInspection.lowerBuiltin scope "extcodecopy" arguments = .ok lowered at compiled
      unfold AccountInspection.lowerBuiltin at compiled
      obtain ⟨world, _, compiled⟩ := lower_bind_eq_ok.mp compiled
      obtain ⟨complete, _, compiled⟩ := lower_bind_eq_ok.mp compiled
      rcases arguments with _ | ⟨first, _ | ⟨second, _ | ⟨third, _ | ⟨fourth, _ | ⟨fifth, rest⟩⟩⟩⟩⟩
      all_goals first
        | rfl
        | change Except.error _ = Except.ok lowered at compiled
          cases compiled
  | hash =>
      change AccountInspection.lowerBuiltin scope "extcodehash" arguments = .ok lowered at compiled
      unfold AccountInspection.lowerBuiltin at compiled
      obtain ⟨world, _, compiled⟩ := lower_bind_eq_ok.mp compiled
      obtain ⟨complete, _, compiled⟩ := lower_bind_eq_ok.mp compiled
      rcases arguments with _ | ⟨first, _ | ⟨second, rest⟩⟩
      all_goals first
        | rfl
        | change Except.error _ = Except.ok lowered at compiled
          cases compiled

theorem balance_components {scope : Scope} {target : Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope "balance" [target] = .ok lowered) :
    ∃ balances, Effects.reference scope "balances" WordMapping.type = .ok balances ∧
      lowered = ⟨.word, WordMapping.lookup (.loadCell balances)
        (.binary .wordAnd target (.word (Word.ofNatModulo (2 ^ 160 - 1))))⟩ := by
  change (do
    let balances ← Effects.reference scope "balances" WordMapping.type
    pure (Lowered.mk .word (WordMapping.lookup (.loadCell balances)
      (.binary .wordAnd target (.word (Word.ofNatModulo (2 ^ 160 - 1))))))) = .ok lowered at compiled
  obtain ⟨balances, found, returned⟩ := lower_bind_eq_ok.mp compiled
  exact ⟨balances, found, (Except.ok.inj returned).symm⟩

theorem selfbalance_components {scope : Scope} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope "selfbalance" [] = .ok lowered) :
    ∃ balances address, Effects.reference scope "balances" WordMapping.type = .ok balances ∧
      Effects.reference scope "address" .word = .ok address ∧
      lowered = ⟨.word, WordMapping.lookup (.loadCell balances) (.loadCell address)⟩ := by
  change (do
    let balances ← Effects.reference scope "balances" WordMapping.type
    let address ← Effects.reference scope "address" .word
    pure (Lowered.mk .word (WordMapping.lookup (.loadCell balances) (.loadCell address)))) = .ok lowered at compiled
  obtain ⟨balances, balancesCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨address, addressCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
  exact ⟨balances, address, balancesCompiled, addressCompiled, (Except.ok.inj returned).symm⟩

theorem size_components {scope : Scope} {target : Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope "extcodesize" [target] = .ok lowered) :
    ∃ world complete, Effects.reference scope "world" AccountState.type = .ok world ∧
      Effects.reference scope "worldComplete" .bool = .ok complete ∧
      lowered = ⟨.word, AccountInspection.size world (.loadCell complete) target⟩ := by
  change (do
    let world ← Effects.reference scope "world" AccountState.type
    let complete ← Effects.reference scope "worldComplete" .bool
    pure (Lowered.mk .word (AccountInspection.size world (.loadCell complete) target))) = .ok lowered at compiled
  obtain ⟨world, worldCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨complete, completeCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
  exact ⟨world, complete, worldCompiled, completeCompiled, (Except.ok.inj returned).symm⟩

theorem copy_components {scope : Scope} {target destination source length : Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope "extcodecopy" [target, destination, source, length] = .ok lowered) :
    ∃ world complete memory size, Effects.reference scope "world" AccountState.type = .ok world ∧
      Effects.reference scope "worldComplete" .bool = .ok complete ∧
      Effects.reference scope "memory" WordMapping.type = .ok memory ∧
      Effects.reference scope "memorySize" .word = .ok size ∧
      lowered = ⟨.unit, AccountInspection.copy world (.loadCell complete) memory size target destination source length⟩ := by
  change (do
    let world ← Effects.reference scope "world" AccountState.type
    let complete ← Effects.reference scope "worldComplete" .bool
    let memory ← Effects.reference scope "memory" WordMapping.type
    let size ← Effects.reference scope "memorySize" .word
    pure (Lowered.mk .unit (AccountInspection.copy world (.loadCell complete) memory size target destination source length))) = .ok lowered at compiled
  obtain ⟨world, worldCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨complete, completeCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨memory, memoryCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨size, sizeCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
  exact ⟨world, complete, memory, size, worldCompiled, completeCompiled, memoryCompiled, sizeCompiled,
    (Except.ok.inj returned).symm⟩

theorem hash_components {scope : Scope} {target : Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope "extcodehash" [target] = .ok lowered) :
    ∃ world complete balances, Effects.reference scope "world" AccountState.type = .ok world ∧
      Effects.reference scope "worldComplete" .bool = .ok complete ∧
      Effects.reference scope "balances" WordMapping.type = .ok balances ∧
      lowered = ⟨.word, AccountInspection.hash world (.loadCell complete) balances target⟩ := by
  change (do
    let world ← Effects.reference scope "world" AccountState.type
    let complete ← Effects.reference scope "worldComplete" .bool
    let balances ← Effects.reference scope "balances" WordMapping.type
    pure (Lowered.mk .word (AccountInspection.hash world (.loadCell complete) balances target))) = .ok lowered at compiled
  obtain ⟨world, worldCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨complete, completeCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨balances, balancesCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
  exact ⟨world, complete, balances, worldCompiled, completeCompiled, balancesCompiled,
    (Except.ok.inj returned).symm⟩

end AccountObservationBuiltinCorrespondence
end Solcore.Frontend.RustHull
end

section
-- leanmerge: from Solcore.Frontend.RustHull.EnvironmentBuiltinCorrespondence
/-! Concrete environment observations through the actual Hull effect compiler.
Optional transaction data, absent gas and unknown code retain their distinct
language faults. Read helpers may allocate closures but retain existing cells. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.EnvironmentBuiltinCorrespondence
open Core Correspondence PureCallCorrespondence EffectBuiltinCorrespondence EnvironmentSemantics ScalarExecution

abbrev optionalWord := Core.Ty.sum .unit .word
abbrev optionalHashes := Core.Ty.sum .unit Core.WordMapping.type

def wordOption : Option Word → Core.Value
  | none => .inLeft .word .unit | some value => .inRight .unit (.word value)

def hashesOption : Option MemorySemantics.Entries → Core.Value
  | none => .inLeft WordMapping.type .unit | some values => .inRight .unit (WordMapping.encode values)

def observation (state : EnvironmentSemantics.State) (name : String) (type : Core.Ty) : Option Core.Value :=
  match name, type with
  | "address", .word => some (.word (state.direct .address))
  | "caller", .word => some (.word (state.direct .caller))
  | "callvalue", .word => some (.word (state.direct .callvalue))
  | "calldataSize", .word => some (.word (state.direct .calldataSize))
  | "returnDataSize", .word => some (.word (state.direct .returnDataSize))
  | "origin", .sum .unit .word => some (wordOption (state.ambient .origin))
  | "gasprice", .sum .unit .word => some (wordOption (state.ambient .gasprice))
  | "coinbase", .sum .unit .word => some (wordOption (state.ambient .coinbase))
  | "timestamp", .sum .unit .word => some (wordOption (state.ambient .timestamp))
  | "number", .sum .unit .word => some (wordOption (state.ambient .number))
  | "prevrandao", .sum .unit .word => some (wordOption (state.ambient .prevrandao))
  | "gaslimit", .sum .unit .word => some (wordOption (state.ambient .gaslimit))
  | "chainid", .sum .unit .word => some (wordOption (state.ambient .chainid))
  | "basefee", .sum .unit .word => some (wordOption (state.ambient .basefee))
  | "blobbasefee", .sum .unit .word => some (wordOption (state.ambient .blobbasefee))
  | "availableGas", .sum .unit .word => some (wordOption state.gas)
  | "codeSize", .word => some (.word state.codeSize)
  | "codeKnown", .bool => some (.bool state.codeKnown)
  | "calldata", type => if type = WordMapping.type then some (WordMapping.encode state.calldata) else none
  | "blockHashes", type => if type = optionalHashes then some (hashesOption state.blockHashes) else none
  | "blobHashes", type => if type = optionalHashes then some (hashesOption state.blobHashes) else none
  | _, _ => none

/-- Only slots present in the compiled runtime scope are observed. This does
not require optional linked-code slots when the selected code does not use them. -/
def StateRel (slots : List EffectSlot) (state : EnvironmentSemantics.State) (store : Store) : Prop :=
  ∀ slot ∈ slots, ∀ value, observation state slot.name slot.type = some value →
    store.read? slot.location = some value

def inputs : Operation → List (String × Core.Ty)
  | .direct operation => [(operation.slot, .word)]
  | .ambient operation => [(operation.name, optionalWord)]
  | .gas => [("availableGas", optionalWord)]
  | .codeSize => [("codeSize", .word), ("codeKnown", .bool)]
  | .calldataLoad => [("calldata", WordMapping.type)]
  | .blockHash => [("number", optionalWord), ("blockHashes", optionalHashes)]
  | .blobHash => [("blobHashes", optionalHashes)]

def Available (slots : List EffectSlot) (operation : Operation) : Prop :=
  ∀ name type, (name, type) ∈ inputs operation → ∃ location, ⟨name, type, location⟩ ∈ slots

theorem StateRel.retained {slots : List EffectSlot} {state : EnvironmentSemantics.State} {initial final : Store}
    (related : StateRel slots state initial) (retained : StoreRetains initial final) :
    StateRel slots state final := by
  intro slot member value represented
  have found := related slot member value represented
  rw [retained.read slot.location (List.getElem?_eq_some_iff.mp found).1]
  exact found

private theorem direct_observation (state : EnvironmentSemantics.State) (operation : Direct) :
    observation state operation.slot .word = some (.word (state.direct operation)) := by
  cases operation <;> rfl

private theorem ambient_observation (state : EnvironmentSemantics.State) (operation : AmbientWord) :
    observation state operation.name optionalWord = some (wordOption (state.ambient operation)) := by
  cases operation <;> rfl

private theorem direct_components (operation : Direct) {scope : Scope} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope operation.name [] = .ok lowered) :
    ∃ reference, Effects.reference scope operation.slot .word = .ok reference ∧
      lowered = ⟨.word, LanguageResult.success (.loadCell reference)⟩ := by
  have expanded : Effects.lowerBuiltin scope operation.name [] = (do
      let reference ← Effects.reference scope operation.slot .word
      pure ⟨.word, LanguageResult.success (.loadCell reference)⟩) := by
    cases operation <;> rfl
  rw [expanded] at compiled
  obtain ⟨reference, compiled, returned⟩ := lower_bind_eq_ok.mp compiled
  exact ⟨reference, compiled, (Except.ok.inj returned).symm⟩

def ambientBody (operation : AmbientWord) : Core.Expr :=
  LanguageResult.success (if operation.isAddress then
    .binary .wordAnd (.var 0) (.word (Word.ofNatModulo (2 ^ 160 - 1))) else .var 0)

private theorem ambient_read_components {scope : Scope} {name : String} {type : Core.Ty} {value : Core.Expr}
    (compiled : Ambient.read scope name type = .ok value) :
    ∃ reference, Effects.reference scope name type = .ok reference ∧ value = .loadCell reference := by
  unfold Ambient.read at compiled
  obtain ⟨⟨binding, index⟩, looked, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨guard, typed, returned⟩ := lower_bind_eq_ok.mp compiled
  cases guard
  refine ⟨.var index, ?_, (Except.ok.inj returned).symm⟩
  simp only [Effects.reference, Effects.slotName, Effects.reservedPrefix, looked, typed,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

private theorem ambient_components (operation : AmbientWord) {scope : Scope} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope operation.name [] = .ok lowered) :
    ∃ reference, Effects.reference scope operation.name optionalWord = .ok reference ∧
      lowered = ⟨.word, .caseE (.loadCell reference)
        (LanguageResult.failure .word (.word (Word.ofNatModulo 14))) (ambientBody operation)⟩ := by
  have expanded : Effects.lowerBuiltin scope operation.name [] = (do
      let value ← Ambient.read scope operation.name optionalWord
      pure ⟨.word, .caseE (value.rename (· + 0))
        (LanguageResult.failure .word (.word (Word.ofNatModulo 14))) (ambientBody operation)⟩) := by
    cases operation <;> rfl
  rw [expanded] at compiled
  obtain ⟨value, readCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨reference, referenceCompiled, rfl⟩ := ambient_read_components readCompiled
  refine ⟨reference, referenceCompiled, ?_⟩
  simpa only [show (fun x : Nat => x + 0) = Core.Renaming.id from rfl, Core.Expr.rename_id] using (Except.ok.inj returned).symm

private theorem gas_components {scope : Scope} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope "gas" [] = .ok lowered) :
    ∃ reference, Effects.reference scope "availableGas" optionalWord = .ok reference ∧
      lowered = ⟨.word, .caseE (.loadCell reference)
        (LanguageResult.failure .word (.word (Word.ofNatModulo 9))) (LanguageResult.success (.var 0))⟩ := by
  change (do
    let reference ← Effects.reference scope "availableGas" optionalWord
    pure (Lowered.mk .word (.caseE (.loadCell reference)
      (LanguageResult.failure .word (.word (Word.ofNatModulo 9))) (LanguageResult.success (.var 0))))) = .ok lowered at compiled
  obtain ⟨reference, compiled, returned⟩ := lower_bind_eq_ok.mp compiled
  exact ⟨reference, compiled, (Except.ok.inj returned).symm⟩

private theorem codeSize_components {scope : Scope} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope "codesize" [] = .ok lowered) :
    ∃ size known, Effects.reference scope "codeSize" .word = .ok size ∧
      Effects.reference scope "codeKnown" .bool = .ok known ∧
      lowered = ⟨.word, .ifE (.loadCell known) (LanguageResult.success (.loadCell size))
        (LanguageResult.failure .word (.word (Word.ofNatModulo 15)))⟩ := by
  change (do
    let size ← Effects.reference scope "codeSize" .word
    let expression ← (do
      let known ← Effects.reference scope "codeKnown" .bool
      pure (.ifE (.loadCell known) (LanguageResult.success (.loadCell size))
        (LanguageResult.failure .word (.word (Word.ofNatModulo 15)))) : LowerM Core.Expr)
    pure (Lowered.mk .word expression)) = .ok lowered at compiled
  obtain ⟨size, sizeCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨expression, guarded, returned⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨known, knownCompiled, guardedEqual⟩ := lower_bind_eq_ok.mp guarded
  cases guardedEqual
  exact ⟨size, known, sizeCompiled, knownCompiled, (Except.ok.inj returned).symm⟩

theorem direct_preserves (operation : Direct) {scope : Scope} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope operation.name [] = .ok lowered)
    {slots : List EffectSlot} {mapping : Renaming} {environment : Environment} {store : Store} {state : EnvironmentSemantics.State}
    (runtime : EffectEnvironmentRel slots scope mapping environment)
    (available : Available slots (.direct operation)) (related : StateRel slots state store) :
    ResultRel lowered.type (.value (.word (state.direct operation))) (.inRight .word (.word (state.direct operation))) ∧
      Evaluates environment store (lowered.expression.rename mapping) (.inRight .word (.word (state.direct operation))) store := by
  obtain ⟨reference, referenceCompiled, rfl⟩ := direct_components operation compiled
  obtain ⟨location, member⟩ := available operation.slot .word (by simp [inputs])
  exact ⟨.value (.word _), .inRight (.loadCell (reference_evaluates runtime member referenceCompiled store)
    (related _ member _ (direct_observation state operation)))⟩

def wordResult : Semantics.Result Semantics.Value → Core.Value
  | .value (.word value) => .inRight .word (.word value)
  | .fault (.language reason) => .inLeft .word (.word reason)
  | _ => .inLeft .word (.word Word.zero)

theorem ambient_preserves (operation : AmbientWord) {scope : Scope} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope operation.name [] = .ok lowered)
    {slots : List EffectSlot} {mapping : Renaming} {environment : Environment} {store : Store} {state : EnvironmentSemantics.State}
    (runtime : EffectEnvironmentRel slots scope mapping environment)
    (available : Available slots (.ambient operation)) (related : StateRel slots state store) :
    ResultRel lowered.type (ambientWord state operation) (wordResult (ambientWord state operation)) ∧
      Evaluates environment store (lowered.expression.rename mapping) (wordResult (ambientWord state operation)) store := by
  obtain ⟨reference, referenceCompiled, rfl⟩ := ambient_components operation compiled
  obtain ⟨location, member⟩ := available operation.name optionalWord (by simp [inputs])
  have read := Evaluates.loadCell (reference_evaluates runtime member referenceCompiled store)
    (related _ member _ (ambient_observation state operation))
  cases found : state.ambient operation with
  | none =>
      simp only [ambientWord, found, Option.map_none, EnvironmentSemantics.available, wordResult]
      exact ⟨.language _, .caseLeft (by simpa only [found, wordOption, Core.Expr.rename] using read) (.inLeft .word)⟩
  | some value =>
      simp only [ambientWord, found, Option.map_some, EnvironmentSemantics.available, wordResult]
      refine ⟨.value (.word _), .caseRight (by simpa only [found, wordOption, Core.Expr.rename] using read) ?_⟩
      cases masked : operation.isAddress
      · simpa [ambientBody, masked, LanguageResult.success, Core.Expr.rename, Renaming.lift] using
          (Evaluates.inRight (leftType := .word) (Evaluates.var (by rfl) :
            Evaluates (.word value :: environment) store (.var 0) (.word value) store))
      · simpa [ambientBody, masked, LanguageResult.success, Core.Expr.rename, Renaming.lift,
          EnvironmentSemantics.address] using
          (Evaluates.inRight (leftType := .word) (Evaluates.binary (Evaluates.var (by rfl)) Evaluates.word rfl :
            Evaluates (.word value :: environment) store
              (.binary .wordAnd (.var 0) (.word (Word.ofNatModulo (2 ^ 160 - 1))))
              (.word (EnvironmentSemantics.address value)) store))

theorem gas_preserves {scope : Scope} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope "gas" [] = .ok lowered)
    {slots : List EffectSlot} {mapping : Renaming} {environment : Environment} {store : Store} {state : EnvironmentSemantics.State}
    (runtime : EffectEnvironmentRel slots scope mapping environment)
    (available : Available slots .gas) (related : StateRel slots state store) :
    ResultRel lowered.type (EnvironmentSemantics.available 9 state.gas) (wordResult (EnvironmentSemantics.available 9 state.gas)) ∧
      Evaluates environment store (lowered.expression.rename mapping) (wordResult (EnvironmentSemantics.available 9 state.gas)) store := by
  obtain ⟨reference, referenceCompiled, rfl⟩ := gas_components compiled
  obtain ⟨location, member⟩ := available "availableGas" optionalWord (by simp [inputs])
  have read := Evaluates.loadCell (reference_evaluates runtime member referenceCompiled store)
    (related _ member _ (show observation state "availableGas" optionalWord = some (wordOption state.gas) from rfl))
  cases found : state.gas with
  | none =>
      simp only [EnvironmentSemantics.available, wordResult]
      exact ⟨.language _, .caseLeft (by simpa only [found, wordOption, Core.Expr.rename] using read) (.inLeft .word)⟩
  | some value =>
      simp only [EnvironmentSemantics.available, wordResult]
      exact ⟨.value (.word _), .caseRight (by simpa only [found, wordOption, Core.Expr.rename] using read) (.inRight (.var rfl))⟩

theorem codeSize_preserves {scope : Scope} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope "codesize" [] = .ok lowered)
    {slots : List EffectSlot} {mapping : Renaming} {environment : Environment} {store : Store} {state : EnvironmentSemantics.State}
    (runtime : EffectEnvironmentRel slots scope mapping environment)
    (available : Available slots .codeSize) (related : StateRel slots state store) :
    ∃ result target, observe state .codeSize [] = some result ∧ ResultRel lowered.type result target ∧
      Evaluates environment store (lowered.expression.rename mapping) target store := by
  obtain ⟨size, known, sizeCompiled, knownCompiled, rfl⟩ := codeSize_components compiled
  obtain ⟨sizeLocation, sizeMember⟩ := available "codeSize" .word (by simp [inputs])
  obtain ⟨knownLocation, knownMember⟩ := available "codeKnown" .bool (by simp [inputs])
  have read := Evaluates.loadCell (reference_evaluates runtime knownMember knownCompiled store)
    (related _ knownMember _ (show observation state "codeKnown" .bool = some (.bool state.codeKnown) from rfl))
  cases found : state.codeKnown with
  | false =>
      exact ⟨.fault (.language (Word.ofNatModulo 15)), .inLeft .word (.word (Word.ofNatModulo 15)),
        by simp [observe, found], .language _, .ifFalse (by simpa only [found, Core.Expr.rename] using read) (.inLeft .word)⟩
  | true =>
      exact ⟨.value (.word state.codeSize), .inRight .word (.word state.codeSize),
        by simp [observe, found], .value (.word _),
        .ifTrue (by simpa only [found, Core.Expr.rename] using read) (.inRight (.loadCell (reference_evaluates runtime sizeMember sizeCompiled store)
          (related _ sizeMember _ rfl)))⟩


private theorem reference_position {slots : List EffectSlot} {scope : Scope} {mapping : Renaming}
    {environment : Environment} {slot : EffectSlot} {reference : Core.Expr}
    (runtime : EffectEnvironmentRel slots scope mapping environment) (member : slot ∈ slots)
    (compiled : Effects.reference scope slot.name slot.type = .ok reference) :
    ∃ index, reference = .var index ∧ environment[mapping index]? = some (.cellRef slot.type slot.location) := by
  unfold Effects.reference at compiled
  obtain ⟨⟨binding, index⟩, looked, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨guard, _, returned⟩ := lower_bind_eq_ok.mp compiled
  cases guard
  cases returned
  exact ⟨index, rfl, runtime slot member binding index looked⟩

set_option linter.unusedSimpArgs false in
theorem readMemoryWord_rename (entries index : Core.Expr) (mapping : Renaming) :
    (Memory.readMemoryWord entries index).rename mapping =
      Memory.readMemoryWord (entries.rename mapping) (index.rename mapping) := by
  simp only [Memory.readMemoryWord, Core.Expr.rename]
  congr 1
  simp only [LanguageResult.bind, LanguageResult.success, LanguageResult.failure,
    WordMapping.lookup, WordMapping.runHelper, WordMapping.lookupBody, WordMapping.invoke,
    OptionalCell.allocate, OptionalCell.read, Core.Expr.rename, Core.Expr.renameList,
    Core.Renaming.lift, Core.Expr.weakenAt]
  rfl

set_option linter.unusedSimpArgs false in
theorem lookup_rename (entries index : Core.Expr) (mapping : Renaming) :
    (WordMapping.lookup entries index).rename mapping =
      WordMapping.lookup (entries.rename mapping) (index.rename mapping) := by
  simp only [WordMapping.lookup, Core.Expr.rename]
  congr 1
  simp only [LanguageResult.bind, LanguageResult.success, LanguageResult.failure,
    WordMapping.runHelper, WordMapping.lookupBody, WordMapping.invoke,
    OptionalCell.allocate, OptionalCell.read, Core.Expr.rename, Core.Expr.renameList,
    Core.Renaming.lift, Core.Expr.weakenAt]
  rfl

private theorem calldata_components {scope : Scope} {index : Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope "calldataload" [index] = .ok lowered) :
    ∃ reference, Effects.reference scope "calldata" WordMapping.type = .ok reference ∧
      lowered = ⟨.word, Memory.readMemoryWord (.loadCell reference) index⟩ := by
  change (do
    let reference ← Effects.reference scope "calldata" WordMapping.type
    pure (Lowered.mk .word (Memory.readMemoryWord (.loadCell reference) index))) = .ok lowered at compiled
  obtain ⟨reference, referenceCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
  exact ⟨reference, referenceCompiled, (Except.ok.inj returned).symm⟩

theorem calldata_preserves {scope : Scope} {indexExpr : Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope "calldataload" [indexExpr] = .ok lowered)
    {slots : List EffectSlot} {mapping : Renaming} {environment : Environment} {store : Store}
    {state : EnvironmentSemantics.State}
    (runtime : EffectEnvironmentRel slots scope mapping environment)
    (available : Available slots .calldataLoad) (related : StateRel slots state store)
    (index : Word) (evaluated : Evaluates environment store (indexExpr.rename mapping) (.word index) store) :
    ∃ final, ResultRel lowered.type (.value (.word (MemorySemantics.readWord state.calldata index)))
        (.inRight .word (.word (MemorySemantics.readWord state.calldata index))) ∧
      Evaluates environment store (lowered.expression.rename mapping)
        (.inRight .word (.word (MemorySemantics.readWord state.calldata index))) final ∧ StoreRetains store final := by
  obtain ⟨reference, referenceCompiled, rfl⟩ := calldata_components compiled
  obtain ⟨location, member⟩ := available "calldata" WordMapping.type (by simp [inputs])
  obtain ⟨suffix, extended⟩ := MemoryCorrespondence.readWordStore_extension store state.calldata index environment
  refine ⟨MemoryCorrespondence.readWordStore store state.calldata index environment, .value (.word _), ?_, ?_⟩
  · rw [readMemoryWord_rename]
    exact MemoryCorrespondence.readMemoryWord_evaluates state.calldata index
      (.loadCell (reference_evaluates runtime member referenceCompiled store)
        (related _ member _ (by simp [observation]))) evaluated
  · rw [extended]; exact StoreRetains.append store suffix

def blobCode (hashes index : Core.Expr) : Core.Expr :=
  .letE index (.caseE (hashes.rename (· + 1))
    (LanguageResult.failure .word (.word (Word.ofNatModulo 14)))
    (WordMapping.lookup (.var 0) (.var 1)))

def blockCode (current hashes index : Core.Expr) : Core.Expr :=
  .letE index (.caseE (current.rename (· + 1))
    (LanguageResult.failure .word (.word (Word.ofNatModulo 14)))
    (.caseE (hashes.rename (· + 2))
      (LanguageResult.failure .word (.word (Word.ofNatModulo 14)))
      (.ifE (.binary .wordGt (.var 1) (.var 2))
        (.ifE (.binary .wordGt (.binary .wordSub (.var 1) (.var 2)) (.word (Word.ofNatModulo 256)))
          (LanguageResult.success (.word Word.zero)) (WordMapping.lookup (.var 0) (.var 2)))
        (LanguageResult.success (.word Word.zero)))))

private theorem blob_components {scope : Scope} {index : Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope "blobhash" [index] = .ok lowered) :
    ∃ reference, Effects.reference scope "blobHashes" optionalHashes = .ok reference ∧
      lowered = ⟨.word, blobCode (.loadCell reference) index⟩ := by
  have expanded : Effects.lowerBuiltin scope "blobhash" [index] = (do
      let hashes ← Ambient.read scope "blobHashes" optionalHashes
      pure ⟨.word, blobCode hashes (index.rename (· + 0))⟩) := rfl
  rw [expanded] at compiled
  obtain ⟨hashes, readCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨reference, referenceCompiled, rfl⟩ := ambient_read_components readCompiled
  refine ⟨reference, referenceCompiled, ?_⟩
  simpa only [show (fun x : Nat => x + 0) = Core.Renaming.id from rfl, Core.Expr.rename_id] using (Except.ok.inj returned).symm

private theorem block_components {scope : Scope} {index : Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope "blockhash" [index] = .ok lowered) :
    ∃ current hashes, Effects.reference scope "number" optionalWord = .ok current ∧
      Effects.reference scope "blockHashes" optionalHashes = .ok hashes ∧
      lowered = ⟨.word, blockCode (.loadCell current) (.loadCell hashes) index⟩ := by
  have expanded : Effects.lowerBuiltin scope "blockhash" [index] = (do
      let current ← Ambient.read scope "number" optionalWord
      let hashes ← Ambient.read scope "blockHashes" optionalHashes
      pure ⟨.word, blockCode current hashes (index.rename (· + 0))⟩) := rfl
  rw [expanded] at compiled
  obtain ⟨current, currentCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨hashes, hashesCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨currentRef, currentReferenceCompiled, rfl⟩ := ambient_read_components currentCompiled
  obtain ⟨hashesRef, hashesReferenceCompiled, rfl⟩ := ambient_read_components hashesCompiled
  refine ⟨currentRef, hashesRef, currentReferenceCompiled, hashesReferenceCompiled, ?_⟩
  simpa only [show (fun x : Nat => x + 0) = Core.Renaming.id from rfl, Core.Expr.rename_id] using (Except.ok.inj returned).symm

private theorem lookup_retains (entries : MemorySemantics.Entries) (index : Word)
    (environment : Environment) (store : Store) :
    StoreRetains store (MemoryCorrespondence.lookupStore store entries index environment) :=
  StoreRetains.append store [_]

theorem blob_preserves {scope : Scope} {indexExpr : Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope "blobhash" [indexExpr] = .ok lowered)
    {slots : List EffectSlot} {mapping : Renaming} {environment : Environment} {store : Store}
    {state : EnvironmentSemantics.State}
    (runtime : EffectEnvironmentRel slots scope mapping environment)
    (available : Available slots .blobHash) (related : StateRel slots state store)
    (index : Word) (evaluated : Evaluates environment store (indexExpr.rename mapping) (.word index) store) :
    ∃ target final, ResultRel lowered.type (blobHash state index) target ∧
      Evaluates environment store (lowered.expression.rename mapping) target final ∧ StoreRetains store final := by
  obtain ⟨reference, referenceCompiled, rfl⟩ := blob_components compiled
  obtain ⟨location, member⟩ := available "blobHashes" optionalHashes (by simp [inputs])
  obtain ⟨position, rfl, found⟩ := reference_position runtime member referenceCompiled
  have read := related _ member _ (show observation state "blobHashes" optionalHashes = some (hashesOption state.blobHashes) by simp [observation])
  simp only [blobCode, Core.Expr.rename, Renaming.lift, lookup_rename, LanguageResult.failure]
  cases hashes : state.blobHashes with
  | none =>
      have missing : store.read? location = some (.inLeft WordMapping.type .unit) := by
        simpa only [hashes, hashesOption] using read
      refine ⟨_, store, ?_, .letE evaluated (.caseLeft (.loadCell (elementType := optionalHashes) (.var ?_) missing) (.inLeft .word)), StoreRetains.refl _⟩
      · simp only [blobHash, hashes, Option.map_none, EnvironmentSemantics.available]; exact .language _
      · simpa using found
  | some entries =>
      have historyRead : store.read? location = some (.inRight .unit (WordMapping.encode entries)) := by
        simpa only [hashes, hashesOption] using read
      refine ⟨.inRight .word (.word (WordMapping.lookupEntries index entries)),
        MemoryCorrespondence.lookupStore store entries index (WordMapping.encode entries :: .word index :: environment),
        ?_, .letE evaluated (.caseRight (.loadCell (elementType := optionalHashes) (.var ?_) historyRead) ?_),
        lookup_retains entries index (WordMapping.encode entries :: .word index :: environment) store⟩
      · simpa only [blobHash, hashes, Option.map_some, EnvironmentSemantics.available, MemoryCorrespondence.lookup_eq] using
          (ResultRel.value (ValueRel.word (WordMapping.lookupEntries index entries)))
      · simpa using found
      · exact WordMapping.lookup_evaluates entries index (.var rfl) (.var rfl)

theorem block_preserves {scope : Scope} {indexExpr : Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope "blockhash" [indexExpr] = .ok lowered)
    {slots : List EffectSlot} {mapping : Renaming} {environment : Environment} {store : Store}
    {state : EnvironmentSemantics.State}
    (runtime : EffectEnvironmentRel slots scope mapping environment)
    (available : Available slots .blockHash) (related : StateRel slots state store)
    (index : Word) (evaluated : Evaluates environment store (indexExpr.rename mapping) (.word index) store) :
    ∃ target final, ResultRel lowered.type (blockHash state index) target ∧
      Evaluates environment store (lowered.expression.rename mapping) target final ∧ StoreRetains store final := by
  obtain ⟨currentRef, hashesRef, currentCompiled, hashesCompiled, rfl⟩ := block_components compiled
  obtain ⟨currentLocation, currentMember⟩ := available "number" optionalWord (by simp [inputs])
  obtain ⟨hashesLocation, hashesMember⟩ := available "blockHashes" optionalHashes (by simp [inputs])
  obtain ⟨currentPosition, rfl, currentFound⟩ := reference_position runtime currentMember currentCompiled
  obtain ⟨hashesPosition, rfl, hashesFound⟩ := reference_position runtime hashesMember hashesCompiled
  have currentRead := related _ currentMember _ (ambient_observation state .number)
  have hashesRead := related _ hashesMember _ (show observation state "blockHashes" optionalHashes = some (hashesOption state.blockHashes) by simp [observation])
  simp only [blockCode, Core.Expr.rename, Renaming.lift, lookup_rename, LanguageResult.failure, LanguageResult.success]
  cases current : state.ambient .number with
  | none =>
      have missing : store.read? currentLocation = some (.inLeft .word .unit) := by
        simpa only [current, wordOption] using currentRead
      refine ⟨_, store, ?_, .letE evaluated (.caseLeft (.loadCell (elementType := optionalWord) (.var ?_) missing) (.inLeft .word)), StoreRetains.refl _⟩
      · simp only [blockHash, current]; exact .language _
      · simpa using currentFound
  | some number =>
      have numberRead : store.read? currentLocation = some (.inRight .unit (.word number)) := by
        simpa only [current, wordOption] using currentRead
      cases hashes : state.blockHashes with
      | none =>
          have missing : store.read? hashesLocation = some (.inLeft WordMapping.type .unit) := by
            simpa only [hashes, hashesOption] using hashesRead
          refine ⟨_, store, ?_, .letE evaluated (.caseRight (.loadCell (elementType := optionalWord) (.var ?_) numberRead)
            (.caseLeft (.loadCell (elementType := optionalHashes) (.var ?_) missing) (.inLeft .word))), StoreRetains.refl _⟩
          · simp only [blockHash, current, hashes]; exact .language _
          · simpa using currentFound
          · simpa [Nat.add_assoc] using hashesFound
      | some entries =>
          have historyRead : store.read? hashesLocation = some (.inRight .unit (WordMapping.encode entries)) := by
            simpa only [hashes, hashesOption] using hashesRead
          by_cases past : number > index
          · by_cases old : number.sub index > Word.ofNatModulo 256
            · refine ⟨_, store, ?_, .letE evaluated (.caseRight (.loadCell (elementType := optionalWord) (.var ?_) numberRead)
                (.caseRight (.loadCell (elementType := optionalHashes) (.var ?_) historyRead) (.ifTrue (.binary (.var rfl) (.var rfl) ?_)
                  (.ifTrue (.binary (.binary (.var rfl) (.var rfl) rfl) .word ?_) (.inRight .word))))), StoreRetains.refl _⟩
              · simp only [blockHash, current, hashes, past, old, ↓reduceIte]; exact .value (.word _)
              · simpa using currentFound
              · simpa [Nat.add_assoc] using hashesFound
              · simp [BinaryOp.apply, past]
              · simp [BinaryOp.apply, old]
            · refine ⟨.inRight .word (.word (WordMapping.lookupEntries index entries)),
                MemoryCorrespondence.lookupStore store entries index
                  (WordMapping.encode entries :: .word number :: .word index :: environment),
                ?_, .letE evaluated (.caseRight (.loadCell (elementType := optionalWord) (.var ?_) numberRead)
                (.caseRight (.loadCell (elementType := optionalHashes) (.var ?_) historyRead) (.ifTrue (.binary (.var rfl) (.var rfl) ?_)
                  (.ifFalse (.binary (.binary (.var rfl) (.var rfl) rfl) .word ?_) ?_)))), lookup_retains entries index
                  (WordMapping.encode entries :: .word number :: .word index :: environment) store⟩
              · simp only [blockHash, current, hashes, past, old, ↓reduceIte, MemoryCorrespondence.lookup_eq]; exact .value (.word _)
              · simpa using currentFound
              · simpa [Nat.add_assoc] using hashesFound
              · simp [BinaryOp.apply, past]
              · simp [BinaryOp.apply, old]
              · exact WordMapping.lookup_evaluates entries index (.var rfl) (.var rfl)
          · refine ⟨_, store, ?_, .letE evaluated (.caseRight (.loadCell (elementType := optionalWord) (.var ?_) numberRead)
              (.caseRight (.loadCell (elementType := optionalHashes) (.var ?_) historyRead) (.ifFalse (.binary (.var rfl) (.var rfl) ?_) (.inRight .word)))), StoreRetains.refl _⟩
            · simp only [blockHash, current, hashes, past, ↓reduceIte]; exact .value (.word _)
            · simpa using currentFound
            · simpa [Nat.add_assoc] using hashesFound
            · simp [BinaryOp.apply, past]


private theorem operation_supported (operation : Operation) : Effects.supports operation.name = true := by
  cases operation with
  | direct operation => cases operation <;> rfl
  | ambient operation => cases operation <;> rfl
  | gas | codeSize | calldataLoad | blockHash | blobHash => rfl

private theorem inner_arity (operation : Operation) {scope : Scope}
    {arguments : List Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope operation.name arguments = .ok lowered) :
    arguments.length = operation.arity := by
  cases operation <;> (try first | cases ‹Direct› | cases ‹AmbientWord›)
  all_goals rcases arguments with _ | ⟨first, _ | ⟨second, rest⟩⟩
  all_goals first
    | rfl
    | change Except.error _ = Except.ok lowered at compiled
      cases compiled

private theorem builtin_operation (operation : Operation) (type : Ty)
    (arguments : List Semantics.Value) (state : EnvironmentSemantics.State) :
    builtin operation.name type arguments state = (observe state operation arguments).map (fun result => (result, state)) := by
  have selected : operations.find? (fun candidate => candidate.name == operation.name) = some operation := by
    cases operation with
    | direct operation => cases operation <;> decide
    | ambient operation => cases operation <;> decide
    | gas | codeSize | calldataLoad | blockHash | blobHash => decide
  unfold builtin
  rw [selected]
  change (observe state operation arguments).bind (fun result => some (result, state)) = _
  cases observe state operation arguments <;> rfl

private theorem zero_preserves (operation : Operation) (arity : operation.arity = 0)
    {scope : Scope} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope operation.name [] = .ok lowered)
    {slots : List EffectSlot} {mapping : Renaming} {environment : Environment} {store : Store}
    {state : EnvironmentSemantics.State}
    (runtime : EffectEnvironmentRel slots scope mapping environment)
    (available : Available slots operation) (related : StateRel slots state store) :
    ∃ result target, observe state operation [] = some result ∧ ResultRel lowered.type result target ∧
      Evaluates environment store (lowered.expression.rename mapping) target store := by
  cases operation with
  | direct operation =>
      obtain ⟨relatedResult, evaluated⟩ := direct_preserves operation compiled runtime available related
      exact ⟨_, _, rfl, relatedResult, evaluated⟩
  | ambient operation =>
      obtain ⟨relatedResult, evaluated⟩ := ambient_preserves operation compiled runtime available related
      exact ⟨_, _, rfl, relatedResult, evaluated⟩
  | gas =>
      obtain ⟨relatedResult, evaluated⟩ := gas_preserves compiled runtime available related
      exact ⟨_, _, rfl, relatedResult, evaluated⟩
  | codeSize => exact codeSize_preserves compiled runtime available related
  | calldataLoad | blockHash | blobHash => cases arity

private theorem one_preserves (operation : Operation) (arity : operation.arity = 1)
    {scope : Scope} {indexExpr : Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope operation.name [indexExpr] = .ok lowered)
    {slots : List EffectSlot} {mapping : Renaming} {environment : Environment} {store : Store}
    {state : EnvironmentSemantics.State}
    (runtime : EffectEnvironmentRel slots scope mapping environment)
    (available : Available slots operation) (related : StateRel slots state store)
    (index : Word) (evaluated : Evaluates environment store (indexExpr.rename mapping) (.word index) store) :
    ∃ result target final, observe state operation [.word index] = some result ∧ ResultRel lowered.type result target ∧
      Evaluates environment store (lowered.expression.rename mapping) target final ∧ StoreRetains store final := by
  cases operation with
  | direct | ambient | gas | codeSize => cases arity
  | calldataLoad =>
      obtain ⟨final, relatedResult, executed, retained⟩ := calldata_preserves compiled runtime available related index evaluated
      exact ⟨_, _, final, rfl, relatedResult, executed, retained⟩
  | blockHash =>
      obtain ⟨target, final, relatedResult, executed, retained⟩ := block_preserves compiled runtime available related index evaluated
      exact ⟨_, target, final, rfl, relatedResult, executed, retained⟩
  | blobHash =>
      obtain ⟨target, final, relatedResult, executed, retained⟩ := blob_preserves compiled runtime available related index evaluated
      exact ⟨_, target, final, rfl, relatedResult, executed, retained⟩

/-- All twenty environment operations pass through the actual outer builtin
compiler. Optional failures and mapping-helper allocations preserve the source
observations and every cell that existed before the operation. -/
theorem preserves (operation : Operation)
    {scope : Scope} {expected : Core.Ty} {arguments : List Lowered} {lowered : Lowered}
    (compiled : lowerBuiltin scope operation.name expected arguments = .ok lowered)
    {sources : List Semantics.Value} {targets : List Core.Value}
    (related : ArgumentsRel arguments sources targets)
    {slots : List EffectSlot} {mapping : Renaming} {environment : Environment}
    {initial store : Store} {state : EnvironmentSemantics.State}
    (runtime : EffectEnvironmentRel slots scope mapping environment)
    (available : Available slots operation) (stateRelated : StateRel slots state store)
    (packed : Evaluates environment initial ((packArguments arguments).expression.rename mapping)
      (.inRight .word (bundleValues targets)) store) (sourceType : Ty) :
    ∃ result target final,
      builtin operation.name sourceType sources state = some (result, state) ∧
      ResultRel lowered.type result target ∧
      Evaluates environment initial (lowered.expression.rename mapping) target final ∧
      StateRel slots state final ∧ StoreRetains store final := by
  obtain ⟨words, raw, rawCompiled, typed, loweredEqual⟩ := outer_components (operation_supported operation) compiled
  have arity : arguments.length = operation.arity := by
    simpa only [List.length_map, List.length_range] using inner_arity operation rawCompiled
  by_cases zero : operation.arity = 0
  · have empty : arguments = [] := List.eq_nil_of_length_eq_zero (arity.trans zero)
    subst arguments
    cases related
    obtain ⟨result, target, observed, relatedResult, executed⟩ :=
      zero_preserves operation zero rawCompiled (runtime.temporary .unit .unit) available stateRelated
    cases typed
    cases loweredEqual
    exact ⟨result, target, store,
      by rw [builtin_operation, observed]; rfl,
      relatedResult, LanguageResult.bind_success _ packed executed, stateRelated, StoreRetains.refl _⟩
  · have one : operation.arity = 1 := by cases operation <;> simp_all [Operation.arity]
    obtain ⟨indexExpr, index, rfl, rfl, rfl⟩ := one_word related words (arity.trans one)
    obtain ⟨result, target, final, observed, relatedResult, executed, retained⟩ :=
      one_preserves operation one rawCompiled (runtime.temporary .word (.word index)) available stateRelated index (.var rfl)
    cases typed
    cases loweredEqual
    exact ⟨result, target, final,
      by rw [builtin_operation, observed]; rfl,
      relatedResult, LanguageResult.bind_success _ packed executed, stateRelated.retained retained, retained⟩

end Solcore.Frontend.RustHull.EnvironmentBuiltinCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.StorageBuiltinCorrespondence
/-! Concrete storage effects through successful Hull builtin lowering,
including the runtime registers written by rejected static writes. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.StorageBuiltinCorrespondence
open Core Correspondence PureCallCorrespondence EffectBuiltinCorrespondence

inductive Operation where
  | load (transient : Bool) | store (transient : Bool)
  deriving DecidableEq

def Operation.name : Operation → String
  | .load false => "sload" | .load true => "tload"
  | .store false => "sstore" | .store true => "tstore"

def Operation.arity : Operation → Nat
  | .load _ => 1 | .store _ => 2

structure Locations where
  world : Nat
  address : Nat
  complete : Nat
  isStatic : Nat
  exit : Nat
  returnOffset : Nat
  returnSize : Nat
  memorySize : Nat

def Locations.all (locations : Locations) : List Nat :=
  [locations.world, locations.address, locations.complete, locations.isStatic,
    locations.exit, locations.returnOffset, locations.returnSize, locations.memorySize]

def Locations.mutable (locations : Locations) : List Nat :=
  [locations.world, locations.exit, locations.returnOffset, locations.returnSize]

structure StateRel (locations : Locations) (state : StorageSemantics.State) (store : Store) : Prop where
  world : StorageCorrespondence.StateRel state.world locations.world store
  address : store.read? locations.address = some (.word state.address)
  complete : store.read? locations.complete = some (.bool state.complete)
  isStatic : store.read? locations.isStatic = some (.bool state.isStatic)
  exit : store.read? locations.exit = some (.word state.exit)
  returnOffset : store.read? locations.returnOffset = some (.word state.returnOffset)
  returnSize : store.read? locations.returnSize = some (.word state.returnSize)
  distinct : locations.all.Nodup

structure Frame (locations : Locations) (initial final : Store) : Prop where
  length_le : initial.length ≤ final.length
  preserved : ∀ location value, location ∉ locations.mutable →
    initial.read? location = some value → final.read? location = some value

theorem Frame.refl (locations : Locations) (store : Store) : Frame locations store store :=
  ⟨Nat.le_refl _, fun _ _ _ found => found⟩

theorem Frame.of_storage {locations : Locations} {initial final : Store}
    (frame : StorageCorrespondence.Frame locations.world initial final) : Frame locations initial final :=
  ⟨frame.length_le, fun location value outside found => frame.preserved location value
    (fun same => outside (by simp [Locations.mutable, same])) found⟩

private theorem inner_arity (operation : Operation) {scope : Scope}
    {arguments : List Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope operation.name arguments = .ok lowered) :
    arguments.length = operation.arity := by
  cases operation with
  | load transient | store transient =>
    cases transient <;>
      rcases arguments with _ | ⟨first, _ | ⟨second, _ | ⟨third, rest⟩⟩⟩
    all_goals first
      | rfl
      | change Except.error _ = Except.ok lowered at compiled
        cases compiled

private theorem load_components (transient : Bool) {scope : Scope} {key : Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope (Operation.load transient).name [key] = .ok lowered) :
    ∃ world address complete,
      Effects.reference scope "world" AccountState.type = .ok world ∧
      Effects.reference scope "address" .word = .ok address ∧
      Effects.reference scope "worldComplete" .bool = .ok complete ∧
      lowered = ⟨.word, AccountState.readStorage world (.loadCell address) (.loadCell complete) key transient⟩ := by
  have components : (do
      let raw ← (do
        let world ← Effects.reference scope "world" AccountState.type
        let address ← Effects.reference scope "address" .word
        let complete ← Effects.reference scope "worldComplete" .bool
        pure (Lowered.mk .word (AccountState.readStorage world (.loadCell address) (.loadCell complete) key transient)) : LowerM Lowered)
      pure raw) = .ok lowered := by
    cases transient <;> exact compiled
  obtain ⟨world, worldCompiled, components⟩ := lower_bind_eq_ok.mp components
  obtain ⟨address, addressCompiled, components⟩ := lower_bind_eq_ok.mp components
  obtain ⟨complete, completeCompiled, returned⟩ := lower_bind_eq_ok.mp components
  exact ⟨world, address, complete, worldCompiled, addressCompiled, completeCompiled, (Except.ok.inj returned).symm⟩

private theorem store_components (transient : Bool) {scope : Scope} {key value : Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope (Operation.store transient).name [key, value] = .ok lowered) :
    ∃ static stop world address complete,
      Effects.reference scope "isStatic" .bool = .ok static ∧
      Effects.terminate scope 3 (.word Word.zero) (.word Word.zero) = .ok stop ∧
      Effects.reference scope "world" AccountState.type = .ok world ∧
      Effects.reference scope "address" .word = .ok address ∧
      Effects.reference scope "worldComplete" .bool = .ok complete ∧
      lowered = ⟨.unit, .ifE (.loadCell static) stop
        (AccountState.writeStorage world (.loadCell address) (.loadCell complete) key value transient)⟩ := by
  have components : (do
      let raw ← (do
        let static ← Effects.reference scope "isStatic" .bool
        let stop ← Effects.terminate scope 3 (.word Word.zero) (.word Word.zero)
        let world ← Effects.reference scope "world" AccountState.type
        let address ← Effects.reference scope "address" .word
        let complete ← Effects.reference scope "worldComplete" .bool
        pure (Lowered.mk .unit (.ifE (.loadCell static) stop
          (AccountState.writeStorage world (.loadCell address) (.loadCell complete) key value transient))) : LowerM Lowered)
      pure raw) = .ok lowered := by
    cases transient <;> exact compiled
  obtain ⟨static, staticCompiled, components⟩ := lower_bind_eq_ok.mp components
  obtain ⟨stop, stopCompiled, components⟩ := lower_bind_eq_ok.mp components
  obtain ⟨world, worldCompiled, components⟩ := lower_bind_eq_ok.mp components
  obtain ⟨address, addressCompiled, components⟩ := lower_bind_eq_ok.mp components
  obtain ⟨complete, completeCompiled, returned⟩ := lower_bind_eq_ok.mp components
  exact ⟨static, stop, world, address, complete, staticCompiled, stopCompiled, worldCompiled,
    addressCompiled, completeCompiled, (Except.ok.inj returned).symm⟩

set_option linter.unusedSimpArgs false in
theorem readStorage_rename (world address complete key : Core.Expr) (transient : Bool) (mapping : Renaming) :
    (AccountState.readStorage world address complete key transient).rename mapping =
      AccountState.readStorage (world.rename mapping) (address.rename mapping) (complete.rename mapping) (key.rename mapping) transient := by
  simp only [AccountState.readStorage, CodeBuilder.bind, CodeBuilder.constant, bundle, Core.Expr.rename]
  congr 1
  cases transient <;>
    simp only [CodeBuilder.bindResult, CodeBuilder.part, CodeBuilder.load, CodeBuilder.lookup, projectArgument,
      AccountState.get, AccountState.lookup, AccountState.defaultRecord, bundle,
      LanguageResult.bind, LanguageResult.success, LanguageResult.failure,
      OrderedMapping.lookup, OrderedMapping.lookupBody, OrderedMapping.optionValue, OrderedMapping.invoke,
      OrderedMapping.runHelper, WordMapping.lookup, WordMapping.lookupBody, WordMapping.runHelper,
      WordMapping.invoke, WordMapping.empty, AccountState.equal, OptionalCell.allocate, OptionalCell.read,
      Core.Expr.rename, Core.Expr.renameList, Core.Renaming.lift, Core.Expr.weakenAt]
  all_goals rfl

set_option linter.unusedSimpArgs false in
theorem writeStorage_rename (world address complete key value : Core.Expr) (transient : Bool) (mapping : Renaming) :
    (AccountState.writeStorage world address complete key value transient).rename mapping =
      AccountState.writeStorage (world.rename mapping) (address.rename mapping) (complete.rename mapping)
        (key.rename mapping) (value.rename mapping) transient := by
  simp only [AccountState.writeStorage, CodeBuilder.bind, CodeBuilder.constant, bundle, Core.Expr.rename]
  congr 1
  cases transient <;>
    simp only [CodeBuilder.bindResult, CodeBuilder.part, CodeBuilder.load, CodeBuilder.insert, CodeBuilder.success,
      CodeBuilder.store, projectArgument, AccountState.get, AccountState.lookup, AccountState.put,
      AccountState.replace, AccountState.field, AccountState.defaultRecord, bundle,
      LanguageResult.bind, LanguageResult.success, LanguageResult.failure,
      OrderedMapping.lookup, OrderedMapping.lookupBody, OrderedMapping.insert, OrderedMapping.insertBody,
      OrderedMapping.cons, OrderedMapping.empty, OrderedMapping.invoke,
      OrderedMapping.runHelper, WordMapping.insert, WordMapping.insertBody, WordMapping.runHelper,
      WordMapping.invoke, WordMapping.cons, WordMapping.empty, AccountState.equal, OptionalCell.allocate, OptionalCell.read,
      Core.Expr.rename, Core.Expr.renameList, Core.Renaming.lift, Core.Expr.weakenAt]
  all_goals rfl


private theorem other_world {locations : Locations} (distinct : locations.all.Nodup) {location : Nat}
    (member : location ∈ [locations.address, locations.complete, locations.isStatic,
      locations.exit, locations.returnOffset, locations.returnSize, locations.memorySize]) : location ≠ locations.world := by
  intro same
  exact (List.nodup_cons.mp distinct).1 (same ▸ member)

theorem StateRel.withWorld {locations : Locations} {state : StorageSemantics.State}
    {initial final : Store} (related : StateRel locations state initial)
    {next : StorageSemantics.World} (world : StorageCorrespondence.StateRel next locations.world final)
    (frame : StorageCorrespondence.Frame locations.world initial final) :
    StateRel locations {state with world := next} final where
  world := world
  address := frame.preserved _ _ (other_world related.distinct (by simp)) related.address
  complete := frame.preserved _ _ (other_world related.distinct (by simp)) related.complete
  isStatic := frame.preserved _ _ (other_world related.distinct (by simp)) related.isStatic
  exit := frame.preserved _ _ (other_world related.distinct (by simp)) related.exit
  returnOffset := frame.preserved _ _ (other_world related.distinct (by simp)) related.returnOffset
  returnSize := frame.preserved _ _ (other_world related.distinct (by simp)) related.returnSize
  distinct := related.distinct

theorem load_result (state : StorageSemantics.State) (key : Word) (transient : Bool) :
    ResultRel .word (StorageSemantics.load state key transient).1
      (StorageCorrespondence.wordResult (StorageSemantics.readStorage state.world state.address state.complete key transient)) := by
  unfold StorageSemantics.load
  cases StorageSemantics.readStorage state.world state.address state.complete key transient with
  | ok value => exact .value (.word _)
  | error reason => exact .language _

theorem store_result (state : StorageSemantics.State) (key value : Word) (transient : Bool)
    (permitted : state.isStatic = false) :
    ResultRel .unit (StorageSemantics.store state key value transient).1
      (StorageCorrespondence.unitResult (StorageSemantics.writeStorage state.world state.address state.complete key value transient)) := by
  simp only [StorageSemantics.store, permitted, Bool.false_eq_true, ↓reduceIte]
  cases StorageSemantics.writeStorage state.world state.address state.complete key value transient with
  | ok next => exact .value .unit
  | error reason => exact .language _

theorem load_state (state : StorageSemantics.State) (key : Word) (transient : Bool) :
    (StorageSemantics.load state key transient).2 = state := by
  unfold StorageSemantics.load
  cases StorageSemantics.readStorage state.world state.address state.complete key transient <;> rfl

theorem store_state (state : StorageSemantics.State) (key value : Word) (transient : Bool)
    (permitted : state.isStatic = false) :
    (StorageSemantics.store state key value transient).2 =
      {state with world := (StorageSemantics.writeStorage state.world state.address state.complete key value transient).toOption.getD state.world} := by
  simp only [StorageSemantics.store, permitted, Bool.false_eq_true, ↓reduceIte]
  cases StorageSemantics.writeStorage state.world state.address state.complete key value transient <;>
    cases state <;> simp_all [Except.toOption]

theorem load_preserves (transient : Bool)
    {scope : Scope} {keyExpr : Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope (Operation.load transient).name [keyExpr] = .ok lowered)
    {slots : List EffectSlot} {mapping : Renaming} {environment : Environment} {store : Store}
    {locations : Locations} {state : StorageSemantics.State}
    (runtime : EffectEnvironmentRel slots scope mapping environment)
    (worldMember : ⟨"world", AccountState.type, locations.world⟩ ∈ slots)
    (addressMember : ⟨"address", .word, locations.address⟩ ∈ slots)
    (completeMember : ⟨"worldComplete", .bool, locations.complete⟩ ∈ slots)
    (stateRelated : StateRel locations state store)
    (key : Word) (keyEvaluated : Evaluates environment store (keyExpr.rename mapping) (.word key) store) :
    ∃ target final,
      ResultRel lowered.type (StorageSemantics.load state key transient).1 target ∧
      Evaluates environment store (lowered.expression.rename mapping) target final ∧
      StateRel locations (StorageSemantics.load state key transient).2 final ∧ Frame locations store final := by
  obtain ⟨world, address, complete, worldCompiled, addressCompiled, completeCompiled, rfl⟩ := load_components transient compiled
  obtain ⟨final, evaluated, worldRelated, frame⟩ := StorageCorrespondence.readStorage_preserves state.address state.complete key transient
    (.pair (reference_evaluates runtime worldMember worldCompiled store)
      (.pair (.loadCell (reference_evaluates runtime addressMember addressCompiled store) stateRelated.address)
        (.pair (.loadCell (reference_evaluates runtime completeMember completeCompiled store) stateRelated.complete) keyEvaluated)))
    stateRelated.world
  refine ⟨_, final, load_result state key transient, ?_, ?_, Frame.of_storage frame⟩
  · rw [readStorage_rename]
    exact evaluated
  · rw [load_state]
    exact stateRelated.withWorld worldRelated frame


def offsetStore (locations : Locations) (store : Store) : Store :=
  store.set locations.returnOffset (.word Word.zero)

def sizeStore (locations : Locations) (store : Store) : Store :=
  (offsetStore locations store).set locations.returnSize (.word Word.zero)

def haltStore (locations : Locations) (store : Store) : Store :=
  (sizeStore locations store).set
    locations.exit (.word (Word.ofNatModulo 3))

theorem haltStore_other {locations : Locations} {store : Store} {location : Nat} {value : Core.Value}
    (exit : location ≠ locations.exit) (offset : location ≠ locations.returnOffset) (size : location ≠ locations.returnSize)
    (found : store.read? location = some value) :
    (haltStore locations store).read? location = some value := by
  simp only [haltStore, sizeStore, offsetStore, Store.read?, List.getElem?_set_ne (Ne.symm exit),
    List.getElem?_set_ne (Ne.symm offset), List.getElem?_set_ne (Ne.symm size)]
  exact found

theorem haltStore_frame (locations : Locations) (store : Store) : Frame locations store (haltStore locations store) := by
  constructor
  · simp [haltStore, sizeStore, offsetStore]
  · intro location value outside found
    simp [Locations.mutable] at outside
    exact haltStore_other outside.2.1 outside.2.2.1 outside.2.2.2 found

theorem StateRel.halt {locations : Locations} {state : StorageSemantics.State} {store : Store}
    (related : StateRel locations state store) :
    StateRel locations {state with exit := Word.ofNatModulo 3, returnOffset := Word.zero, returnSize := Word.zero}
      (haltStore locations store) := by
  have distinct := related.distinct
  simp [Locations.all] at distinct
  have offsetBound := (List.getElem?_eq_some_iff.mp related.returnOffset).1
  have sizeBound := (List.getElem?_eq_some_iff.mp related.returnSize).1
  have exitBound := (List.getElem?_eq_some_iff.mp related.exit).1
  constructor
  · obtain ⟨accounts, source, found⟩ := related.world
    exact ⟨accounts, source, haltStore_other (locations := locations) (location := locations.world) (by intro same; simp_all) (by intro same; simp_all) (by intro same; simp_all) found⟩
  · exact haltStore_other (locations := locations) (location := locations.address) (by intro same; simp_all) (by intro same; simp_all) (by intro same; simp_all) related.address
  · exact haltStore_other (locations := locations) (location := locations.complete) (by intro same; simp_all) (by intro same; simp_all) (by intro same; simp_all) related.complete
  · exact haltStore_other (locations := locations) (location := locations.isStatic) (by intro same; simp_all) (by intro same; simp_all) (by intro same; simp_all) related.isStatic
  · simp [haltStore, sizeStore, offsetStore, Store.read?, exitBound]
  · simp only [haltStore, sizeStore, offsetStore, Store.read?, List.getElem?_set_ne (by intro same; simp_all : locations.exit ≠ locations.returnOffset),
      List.getElem?_set_ne (by intro same; simp_all : locations.returnSize ≠ locations.returnOffset)]
    simp [offsetBound]
  · simp only [haltStore, sizeStore, offsetStore, Store.read?, List.getElem?_set_ne (by intro same; simp_all : locations.exit ≠ locations.returnSize)]
    simp [sizeBound]
  · exact related.distinct

private theorem reference_position {slots : List EffectSlot} {scope : Scope} {mapping : Renaming}
    {environment : Environment} {slot : EffectSlot} {reference : Core.Expr}
    (related : EffectEnvironmentRel slots scope mapping environment) (member : slot ∈ slots)
    (compiled : Effects.reference scope slot.name slot.type = .ok reference) :
    ∃ index, reference = .var index ∧ environment[mapping index]? = some (.cellRef slot.type slot.location) := by
  unfold Effects.reference at compiled
  obtain ⟨⟨binding, index⟩, looked, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨guard, _, returned⟩ := lower_bind_eq_ok.mp compiled
  cases guard
  cases returned
  exact ⟨index, rfl, related slot member binding index looked⟩

private theorem stop_components {scope : Scope} {stop : Core.Expr}
    (compiled : Effects.terminate scope 3 (.word Word.zero) (.word Word.zero) = .ok stop) :
    ∃ memorySize exit offset size,
      Effects.reference scope "memorySize" .word = .ok memorySize ∧
      Effects.reference scope "exit" .word = .ok exit ∧
      Effects.reference scope "returnOffset" .word = .ok offset ∧
      Effects.reference scope "returnSize" .word = .ok size ∧
      stop = LocalSequence.discard .unit (Memory.touch memorySize (.word Word.zero) (.word Word.zero))
        ([Core.Expr.storeCell offset (.word Word.zero), .storeCell size (.word Word.zero),
          .storeCell exit (.word (Word.ofNatModulo 3))].foldr (fun store next => .letE store (next.weakenAt 0))
          (LanguageResult.failure .unit (.word Word.maximum))) := by
  unfold Effects.terminate at compiled
  obtain ⟨memorySize, memoryCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨exit, exitCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨offset, offsetCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨size, sizeCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
  exact ⟨memorySize, exit, offset, size, memoryCompiled, exitCompiled, offsetCompiled, sizeCompiled,
    (Except.ok.inj returned).symm⟩

def haltCells (exit offset size : Nat) (store : Store) : Store :=
  ((store.set offset (.word Word.zero)).set size (.word Word.zero)).set exit (.word (Word.ofNatModulo 3))

/-- Zero-length termination reads no memory-size value. Its execution needs
only the three destination cells and their pairwise separation. -/
theorem stop_evaluates_cells {scope : Scope} {stop : Core.Expr}
    (compiled : Effects.terminate scope 3 (.word Word.zero) (.word Word.zero) = .ok stop)
    {slots : List EffectSlot} {mapping : Renaming} {environment : Environment} {store : Store}
    {memorySizeLocation exitLocation offsetLocation sizeLocation : Nat}
    (runtime : EffectEnvironmentRel slots scope mapping environment)
    (memorySizeMember : ⟨"memorySize", .word, memorySizeLocation⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, exitLocation⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, offsetLocation⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, sizeLocation⟩ ∈ slots)
    {exitValue offsetValue sizeValue : Word}
    (exitInitial : store.read? exitLocation = some (.word exitValue))
    (offsetRead : store.read? offsetLocation = some (.word offsetValue))
    (sizeInitial : store.read? sizeLocation = some (.word sizeValue))
    (exitOffset : exitLocation ≠ offsetLocation) (exitSize : exitLocation ≠ sizeLocation)
    (sizeOffset : sizeLocation ≠ offsetLocation) :
    Evaluates environment store (stop.rename mapping) (.inLeft .unit (.word Word.maximum))
      (haltCells exitLocation offsetLocation sizeLocation store) := by
  let locations : Locations := ⟨0, 0, 0, 0, exitLocation, offsetLocation, sizeLocation, memorySizeLocation⟩
  change Evaluates environment store (stop.rename mapping) (.inLeft .unit (.word Word.maximum)) (haltStore locations store)
  obtain ⟨memorySize, exit, offset, size, memoryCompiled, exitCompiled, offsetCompiled, sizeCompiled, rfl⟩ := stop_components compiled
  obtain ⟨memoryIndex, rfl, memoryFound⟩ := reference_position runtime memorySizeMember memoryCompiled
  obtain ⟨exitIndex, rfl, exitFound⟩ := reference_position runtime exitMember exitCompiled
  obtain ⟨offsetIndex, rfl, offsetFound⟩ := reference_position runtime offsetMember offsetCompiled
  obtain ⟨sizeIndex, rfl, sizeFound⟩ := reference_position runtime sizeMember sizeCompiled
  have offsetWritten : store.write? locations.returnOffset (.word Word.zero) =
      some (offsetStore locations store) :=
    Store.write?_eq_some_iff.mpr ⟨(List.getElem?_eq_some_iff.mp offsetRead).1, rfl⟩
  have sizeRead : (offsetStore locations store).read? locations.returnSize = some (.word sizeValue) := by
    rw [Store.write?_preserves_other offsetWritten sizeOffset]
    exact sizeInitial
  have sizeWritten : (offsetStore locations store).write? locations.returnSize (.word Word.zero) =
      some (sizeStore locations store) :=
    Store.write?_eq_some_iff.mpr ⟨(List.getElem?_eq_some_iff.mp sizeRead).1, rfl⟩
  have exitRead : (sizeStore locations store).read? locations.exit =
      some (.word exitValue) := by
    rw [Store.write?_preserves_other sizeWritten exitSize, Store.write?_preserves_other offsetWritten exitOffset]
    exact exitInitial
  have exitWritten : (sizeStore locations store).write?
      locations.exit (.word (Word.ofNatModulo 3)) = some (haltStore locations store) :=
    Store.write?_eq_some_iff.mpr ⟨(List.getElem?_eq_some_iff.mp exitRead).1, rfl⟩
  simp [LocalSequence.discard, LanguageResult.bind, List.foldr_cons, List.foldr_nil,
    Core.Expr.weakenAt, Core.Expr.rename, Renaming.lift, LanguageResult.failure, Nat.add_assoc]
  apply Evaluates.caseRight
  · unfold Memory.touch
    simp only [Core.Expr.rename]
    apply Evaluates.letE (.pair (.var memoryFound) (.pair .word .word))
    exact .ifTrue (.binary (.second (.second (.var rfl))) .word rfl) (.inRight .unit)
  · apply Evaluates.letE (bodyStore := store.set locations.returnOffset (.word Word.zero))
    · exact .storeCell (.var (by simpa [Renaming.lift] using offsetFound)) offsetRead .word offsetWritten
    · apply Evaluates.letE (bodyStore := (offsetStore locations store).set locations.returnSize (.word Word.zero))
      · exact .storeCell (.var (by simpa [Renaming.lift, Nat.add_assoc] using sizeFound)) sizeRead .word sizeWritten
      · apply Evaluates.letE (bodyStore := haltStore locations store)
        · exact .storeCell (.var (by simpa [Renaming.lift, Nat.add_assoc] using exitFound)) exitRead .word exitWritten
        · exact .inLeft .word


theorem stop_evaluates {scope : Scope} {stop : Core.Expr}
    (compiled : Effects.terminate scope 3 (.word Word.zero) (.word Word.zero) = .ok stop)
    {slots : List EffectSlot} {mapping : Renaming} {environment : Environment} {store : Store}
    {locations : Locations} {state : StorageSemantics.State}
    (runtime : EffectEnvironmentRel slots scope mapping environment)
    (memorySizeMember : ⟨"memorySize", .word, locations.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, locations.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, locations.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, locations.returnSize⟩ ∈ slots)
    (stateRelated : StateRel locations state store) :
    Evaluates environment store (stop.rename mapping) (.inLeft .unit (.word Word.maximum)) (haltStore locations store) := by
  have distinct := stateRelated.distinct
  simp [Locations.all] at distinct
  exact stop_evaluates_cells compiled runtime memorySizeMember exitMember offsetMember sizeMember
    stateRelated.exit stateRelated.returnOffset stateRelated.returnSize
    (by intro same; simp_all) (by intro same; simp_all) (by intro same; simp_all)


theorem store_preserves (transient : Bool)
    {scope : Scope} {keyExpr valueExpr : Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope (Operation.store transient).name [keyExpr, valueExpr] = .ok lowered)
    {slots : List EffectSlot} {mapping : Renaming} {environment : Environment} {store : Store}
    {locations : Locations} {state : StorageSemantics.State}
    (runtime : EffectEnvironmentRel slots scope mapping environment)
    (worldMember : ⟨"world", AccountState.type, locations.world⟩ ∈ slots)
    (addressMember : ⟨"address", .word, locations.address⟩ ∈ slots)
    (completeMember : ⟨"worldComplete", .bool, locations.complete⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, locations.isStatic⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, locations.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, locations.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, locations.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, locations.returnSize⟩ ∈ slots)
    (stateRelated : StateRel locations state store)
    (key value : Word)
    (keyEvaluated : Evaluates environment store (keyExpr.rename mapping) (.word key) store)
    (valueEvaluated : Evaluates environment store (valueExpr.rename mapping) (.word value) store) :
    ∃ target final,
      ResultRel lowered.type (StorageSemantics.store state key value transient).1 target ∧
      Evaluates environment store (lowered.expression.rename mapping) target final ∧
      StateRel locations (StorageSemantics.store state key value transient).2 final ∧ Frame locations store final := by
  obtain ⟨static, stop, world, address, complete, staticCompiled, stopCompiled, worldCompiled,
    addressCompiled, completeCompiled, rfl⟩ := store_components transient compiled
  have staticRead := stateRelated.isStatic
  cases permitted : state.isStatic
  · rw [permitted] at staticRead
    obtain ⟨final, evaluated, worldRelated, frame⟩ := StorageCorrespondence.writeStorage_preserves state.address state.complete key value transient
      (.pair (reference_evaluates runtime worldMember worldCompiled store)
        (.pair (.loadCell (reference_evaluates runtime addressMember addressCompiled store) stateRelated.address)
          (.pair (.loadCell (reference_evaluates runtime completeMember completeCompiled store) stateRelated.complete)
            (.pair keyEvaluated valueEvaluated)))) stateRelated.world
    refine ⟨_, final, store_result state key value transient permitted, ?_, ?_, Frame.of_storage frame⟩
    · apply Evaluates.ifFalse (.loadCell (reference_evaluates runtime staticMember staticCompiled store) staticRead)
      rw [writeStorage_rename]
      exact evaluated
    · rw [store_state state key value transient permitted]
      exact stateRelated.withWorld worldRelated frame
  · rw [permitted] at staticRead
    refine ⟨.inLeft .unit (.word Word.maximum), haltStore locations store, ?_, ?_, ?_, haltStore_frame _ _⟩
    · simpa only [StorageSemantics.store, permitted, ↓reduceIte] using (ResultRel.language (type := .unit) Word.maximum)
    · apply Evaluates.ifTrue (.loadCell (reference_evaluates runtime staticMember staticCompiled store) staticRead)
      exact stop_evaluates stopCompiled runtime memorySizeMember exitMember offsetMember sizeMember stateRelated
    · simpa only [StorageSemantics.store, permitted, ↓reduceIte] using stateRelated.halt

/-- Successful compilation and initialized runtime cells determine each
storage observation, including static rejection and all resulting writes. -/
theorem preserves (operation : Operation)
    {scope : Scope} {expected : Core.Ty} {arguments : List Lowered} {lowered : Lowered}
    (compiled : lowerBuiltin scope operation.name expected arguments = .ok lowered)
    {sources : List Semantics.Value} {targets : List Core.Value}
    (related : ArgumentsRel arguments sources targets)
    {slots : List EffectSlot} {mapping : Renaming} {environment : Environment}
    {initial store : Store} {locations : Locations} {state : StorageSemantics.State}
    (runtime : EffectEnvironmentRel slots scope mapping environment)
    (worldMember : ⟨"world", AccountState.type, locations.world⟩ ∈ slots)
    (addressMember : ⟨"address", .word, locations.address⟩ ∈ slots)
    (completeMember : ⟨"worldComplete", .bool, locations.complete⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, locations.isStatic⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, locations.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, locations.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, locations.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, locations.returnSize⟩ ∈ slots)
    (stateRelated : StateRel locations state store)
    (packed : Evaluates environment initial ((packArguments arguments).expression.rename mapping)
      (.inRight .word (ScalarExecution.bundleValues targets)) store)
    (sourceType : Ty) :
    ∃ result finalState target finalStore,
      StorageSemantics.builtin operation.name sourceType sources state = some (result, finalState) ∧
      ResultRel lowered.type result target ∧
      Evaluates environment initial (lowered.expression.rename mapping) target finalStore ∧
      StateRel locations finalState finalStore ∧ Frame locations store finalStore := by
  have supported : Effects.supports operation.name = true := by
    cases operation with | load transient | store transient => cases transient <;> rfl
  obtain ⟨words, raw, rawCompiled, typed, loweredEqual⟩ := outer_components supported compiled
  have arity : arguments.length = operation.arity := by
    simpa only [List.length_map, List.length_range] using inner_arity operation rawCompiled
  cases operation with
  | load transient =>
      obtain ⟨keyExpr, key, rfl, rfl, rfl⟩ := one_word related words arity
      obtain ⟨target, final, resultRelated, evaluated, finalRelated, frame⟩ := load_preserves transient rawCompiled
        (runtime.temporary .word (.word key)) worldMember addressMember completeMember stateRelated key (.var rfl)
      cases typed
      cases loweredEqual
      refine ⟨(StorageSemantics.load state key transient).1, (StorageSemantics.load state key transient).2,
        target, final, ?_, resultRelated, ?_, finalRelated, frame⟩
      · cases transient <;> rfl
      · exact LanguageResult.bind_success _ packed evaluated
  | store transient =>
      obtain ⟨keyExpr, valueExpr, key, value, rfl, rfl, rfl⟩ := two_words related words arity
      obtain ⟨target, final, resultRelated, evaluated, finalRelated, frame⟩ := store_preserves transient rawCompiled
        (runtime.temporary (.product .word .word) (.pair (.word key) (.word value)))
        worldMember addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
        stateRelated key value (.first (.var rfl)) (.second (.var rfl))
      cases typed
      cases loweredEqual
      refine ⟨(StorageSemantics.store state key value transient).1, (StorageSemantics.store state key value transient).2,
        target, final, ?_, resultRelated, ?_, finalRelated, frame⟩
      · cases transient <;> rfl
      · exact LanguageResult.bind_success _ packed evaluated

end Solcore.Frontend.RustHull.StorageBuiltinCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.AccountObservationBuiltinCorrespondence
/-! Independent account observations reach the actual outer builtin compiler
with references obtained from the initialized runtime environment. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.AccountObservationBuiltinCorrespondence
open Core Correspondence PureCallCorrespondence EffectBuiltinCorrespondence
open AccountObservationSemantics (Operation)

theorem memory_unchanged {world : StorageSemantics.World} {complete : Bool}
    {balances : StorageSemantics.Words} {current : Word} {name : String}
    {sourceType : Ty} {sources : List Semantics.Value} {state finalState : MemorySemantics.State}
    {result : Semantics.Result Semantics.Value}
    (called : AccountObservationSemantics.Builtin world complete balances current name sourceType sources state result finalState)
    (readonly : name ≠ "extcodecopy") : finalState = state := by
  cases called <;> first | rfl | exact False.elim (readonly rfl)

private theorem retained_memory {memory size : Nat} {state : MemorySemantics.State} {store final : Store}
    (related : MemoryCorrespondence.StateRel memory size state store) (retained : StoreRetains store final) :
    MemoryCorrespondence.StateRel memory size state final ∧ MemoryCorrespondence.Frame memory size store final := by
  have keep : ∀ location value, store.read? location = some value → final.read? location = some value := by
    intro location value found
    exact (retained.read location (List.getElem?_eq_some_iff.mp found).1).trans found
  exact ⟨⟨related.distinct, keep _ _ related.memory, keep _ _ related.size⟩,
    ⟨retained.length_le, fun location value _ _ found => keep location value found⟩⟩

private theorem lookup_preserves {environment : Environment} {store : Store}
    {entries index : Core.Expr} {balances : StorageSemantics.Words} {key : Word}
    (entriesEvaluated : Evaluates environment store entries (WordMapping.encode balances) store)
    (indexEvaluated : Evaluates environment store index (.word key) store) :
    ∃ final,
      Evaluates environment store (WordMapping.lookup entries index)
        (.inRight .word (.word (StorageSemantics.readWord key balances))) final ∧ StoreRetains store final := by
  have evaluated := WordMapping.lookup_evaluates balances key entriesEvaluated indexEvaluated
  rw [← StorageCorrespondence.readWord_eq] at evaluated
  exact ⟨_, evaluated, StoreRetains.append _ _⟩

private theorem balance_result {world : StorageSemantics.World} {complete : Bool}
    {balances : StorageSemantics.Words} {current target : Word} {sourceType : Ty}
    {state finalState : MemorySemantics.State} {result : Semantics.Result Semantics.Value}
    (called : AccountObservationSemantics.Builtin world complete balances current "balance" sourceType
      [.word target] state result finalState) :
    result = .value (.word (StorageSemantics.readWord (AccountObservationSemantics.address target) balances)) := by
  generalize named : "balance" = name at called
  cases called <;> simp only [String.reduceEq] at named
  rfl

private theorem selfbalance_result {world : StorageSemantics.World} {complete : Bool}
    {balances : StorageSemantics.Words} {current : Word} {sourceType : Ty}
    {state finalState : MemorySemantics.State} {result : Semantics.Result Semantics.Value}
    (called : AccountObservationSemantics.Builtin world complete balances current "selfbalance" sourceType
      [] state result finalState) : result = .value (.word (StorageSemantics.readWord current balances)) := by
  generalize named : "selfbalance" = name at called
  cases called
  rfl

theorem preserves (operation : Operation)
    {scope : Scope} {expected : Core.Ty} {arguments : List Lowered} {lowered : Lowered}
    (compiled : lowerBuiltin scope operation.name expected arguments = .ok lowered)
    {storage : StorageSemantics.State} {balances : StorageSemantics.Words}
    {sourceType : Ty} {sources : List Semantics.Value}
    {state finalState : MemorySemantics.State} {result : Semantics.Result Semantics.Value}
    (called : AccountObservationSemantics.Builtin storage.world storage.complete balances storage.address
      operation.name sourceType sources state result finalState)
    {targets : List Core.Value} (related : ArgumentsRel arguments sources targets)
    {slots : List EffectSlot} {mapping : Renaming} {environment : Environment}
    {initial store : Store} {memoryLocation sizeLocation balancesLocation : Nat}
    {locations : StorageBuiltinCorrespondence.Locations}
    (runtime : EffectEnvironmentRel slots scope mapping environment)
    (memoryMember : ⟨"memory", WordMapping.type, memoryLocation⟩ ∈ slots)
    (sizeMember : ⟨"memorySize", .word, sizeLocation⟩ ∈ slots)
    (worldMember : ⟨"world", AccountState.type, locations.world⟩ ∈ slots)
    (addressMember : ⟨"address", .word, locations.address⟩ ∈ slots)
    (completeMember : ⟨"worldComplete", .bool, locations.complete⟩ ∈ slots)
    (balancesMember : ⟨"balances", WordMapping.type, balancesLocation⟩ ∈ slots)
    (stateRelated : MemoryCorrespondence.StateRel memoryLocation sizeLocation state store)
    (storageRelated : StorageBuiltinCorrespondence.StateRel locations storage store)
    (balancesRead : store.read? balancesLocation = some (WordMapping.encode balances))
    (packed : Evaluates environment initial ((packArguments arguments).expression.rename mapping)
      (.inRight .word (ScalarExecution.bundleValues targets)) store) :
    ∃ target finalStore,
      ResultRel lowered.type result target ∧
      Evaluates environment initial (lowered.expression.rename mapping) target finalStore ∧
      MemoryCorrespondence.StateRel memoryLocation sizeLocation finalState finalStore ∧
      MemoryCorrespondence.Frame memoryLocation sizeLocation store finalStore := by
  have supported : Effects.supports operation.name = true := by cases operation <;> rfl
  obtain ⟨words, raw, rawCompiled, typed, loweredEqual⟩ := outer_components supported compiled
  have arity : arguments.length = operation.arity := by
    simpa only [List.length_map, List.length_range] using inner_arity operation rawCompiled
  obtain ⟨accounts, accountsEqual, worldRead⟩ := storageRelated.world
  rw [← accountsEqual] at called
  cases operation with
  | balance =>
      obtain ⟨expression, value, rfl, rfl, rfl⟩ := one_word related words arity
      obtain ⟨balancesRef, balancesCompiled, rfl⟩ := balance_components rawCompiled
      cases typed
      cases loweredEqual
      have sameMemory := memory_unchanged called (by decide)
      cases sameMemory
      have resultEqual := balance_result called
      cases resultEqual
      have runtime' := runtime.temporary .word (.word value)
      obtain ⟨finalStore, evaluated, retained⟩ := lookup_preserves
        (.loadCell (reference_evaluates runtime' balancesMember balancesCompiled store) balancesRead)
        (.binary (op := .wordAnd) (.var (index := 0) rfl) (Evaluates.word (value := Word.ofNatModulo (2 ^ 160 - 1))) rfl)
      obtain ⟨finalRelated, frame⟩ := retained_memory stateRelated retained
      refine ⟨_, finalStore, .value (.word _), ?_, finalRelated, frame⟩
      apply LanguageResult.bind_success .word packed
      rw [EnvironmentBuiltinCorrespondence.lookup_rename]
      exact evaluated
  | selfbalance =>
      have empty : arguments = [] := List.eq_nil_of_length_eq_zero arity
      subst arguments
      cases related
      obtain ⟨balancesRef, addressRef, balancesCompiled, addressCompiled, rfl⟩ := selfbalance_components rawCompiled
      cases typed
      cases loweredEqual
      have sameMemory := memory_unchanged called (by decide)
      cases sameMemory
      have resultEqual := selfbalance_result called
      cases resultEqual
      have runtime' := runtime.temporary .unit .unit
      obtain ⟨finalStore, evaluated, retained⟩ := lookup_preserves
        (.loadCell (reference_evaluates runtime' balancesMember balancesCompiled store) balancesRead)
        (.loadCell (reference_evaluates runtime' addressMember addressCompiled store) storageRelated.address)
      obtain ⟨finalRelated, frame⟩ := retained_memory stateRelated retained
      refine ⟨_, finalStore, .value (.word _), ?_, finalRelated, frame⟩
      apply LanguageResult.bind_success .word packed
      rw [EnvironmentBuiltinCorrespondence.lookup_rename]
      exact evaluated
  | size =>
      obtain ⟨expression, value, rfl, rfl, rfl⟩ := one_word related words arity
      obtain ⟨worldRef, completeRef, worldCompiled, completeCompiled, rfl⟩ := size_components rawCompiled
      cases typed
      cases loweredEqual
      have sameMemory := memory_unchanged called (by decide)
      cases sameMemory
      have runtime' := runtime.temporary .word (.word value)
      obtain ⟨target, finalStore, resultRelated, evaluated, retained⟩ :=
        AccountInspectionCorrespondence.size_preserves called worldRead
          (reference_evaluates runtime' worldMember worldCompiled store)
          (.loadCell (reference_evaluates runtime' completeMember completeCompiled store) storageRelated.complete)
          (.var (index := 0) rfl)
      obtain ⟨finalRelated, frame⟩ := retained_memory stateRelated retained
      refine ⟨target, finalStore, resultRelated, ?_, finalRelated, frame⟩
      apply LanguageResult.bind_success .word packed
      rw [AccountInspectionCorrespondence.size_rename]
      exact evaluated
  | copy =>
      obtain ⟨targetExpr, destinationExpr, sourceExpr, lengthExpr, targetWord, destination, source, length, rfl, rfl, rfl⟩ :=
        four_words related words arity
      obtain ⟨worldRef, completeRef, memoryRef, sizeRef, worldCompiled, completeCompiled,
        memoryCompiled, sizeCompiled, rfl⟩ := copy_components rawCompiled
      cases typed
      cases loweredEqual
      have runtime' := runtime.temporary (.product .word (.product .word (.product .word .word)))
        (.pair (.word targetWord) (.pair (.word destination) (.pair (.word source) (.word length))))
      obtain ⟨target, finalStore, resultRelated, evaluated, finalRelated, frame⟩ :=
        AccountInspectionCorrespondence.copy_preserves called worldRead stateRelated
          (reference_evaluates runtime' worldMember worldCompiled store)
          (.loadCell (reference_evaluates runtime' completeMember completeCompiled store) storageRelated.complete)
          (reference_evaluates runtime' memoryMember memoryCompiled store)
          (reference_evaluates runtime' sizeMember sizeCompiled store)
          (.first (.var (index := 0) rfl)) (.first (.second (.var (index := 0) rfl)))
          (.first (.second (.second (.var (index := 0) rfl)))) (.second (.second (.second (.var (index := 0) rfl))))
      refine ⟨target, finalStore, resultRelated, ?_, finalRelated, frame⟩
      apply LanguageResult.bind_success .unit packed
      rw [AccountInspectionCorrespondence.copy_rename]
      exact evaluated
  | hash =>
      obtain ⟨expression, value, rfl, rfl, rfl⟩ := one_word related words arity
      obtain ⟨worldRef, completeRef, balancesRef, worldCompiled, completeCompiled, balancesCompiled, rfl⟩ :=
        hash_components rawCompiled
      cases typed
      cases loweredEqual
      have sameMemory := memory_unchanged called (by decide)
      cases sameMemory
      have runtime' := runtime.temporary .word (.word value)
      obtain ⟨target, finalStore, resultRelated, evaluated, retained⟩ :=
        AccountInspectionCorrespondence.hash_preserves called worldRead balancesRead
          (reference_evaluates runtime' worldMember worldCompiled store)
          (.loadCell (reference_evaluates runtime' completeMember completeCompiled store) storageRelated.complete)
          (reference_evaluates runtime' balancesMember balancesCompiled store)
          (.var (index := 0) rfl)
      obtain ⟨finalRelated, frame⟩ := retained_memory stateRelated retained
      refine ⟨target, finalStore, resultRelated, ?_, finalRelated, frame⟩
      apply LanguageResult.bind_success .word packed
      rw [AccountInspectionCorrespondence.hash_rename]
      exact evaluated

end Solcore.Frontend.RustHull.AccountObservationBuiltinCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.CodeImageBuiltinCorrespondence
/-! The actual outer compiler resolves the code-image guard and packed copying.
A known image reaches the existing source copy theorem; an unavailable image
returns its language fault before memory expansion or helper allocation. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.CodeImageBuiltinCorrespondence
open Core Correspondence PureCallCorrespondence EffectBuiltinCorrespondence
open CodeImageSemantics (Operation)

theorem inner_arity (operation : Operation) {scope : Scope}
    {arguments : List Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope operation.name arguments = .ok lowered) :
    arguments.length = 3 := by
  cases operation <;>
    rcases arguments with _ | ⟨first, _ | ⟨second, _ | ⟨third, _ | ⟨fourth, rest⟩⟩⟩⟩
  all_goals first
    | rfl
    | change Except.error _ = Except.ok lowered at compiled
      cases compiled

theorem components (operation : Operation) {scope : Scope} {destination source length : Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope operation.name [destination, source, length] = .ok lowered) :
    ∃ memory size code known,
      Effects.reference scope "memory" WordMapping.type = .ok memory ∧
      Effects.reference scope "memorySize" .word = .ok size ∧
      Effects.reference scope "code" WordMapping.type = .ok code ∧
      Effects.reference scope "codeKnown" .bool = .ok known ∧
      lowered = ⟨.unit, .ifE (.loadCell known)
        (Memory.copyPackedFrom memory size destination (.loadCell code) source length)
        (LanguageResult.failure .unit (.word (Word.ofNatModulo 15)))⟩ := by
  have expanded : (do
      let raw ← (do
        let memory ← Effects.reference scope "memory" WordMapping.type
        let size ← Effects.reference scope "memorySize" .word
        let code ← Effects.reference scope "code" WordMapping.type
        let guarded ← Effects.requireCode scope .unit
          (Memory.copyPackedFrom memory size destination (.loadCell code) source length)
        pure (Lowered.mk .unit guarded) : LowerM Lowered)
      pure raw) = .ok lowered := by
    cases operation <;> exact compiled
  obtain ⟨memory, memoryCompiled, expanded⟩ := lower_bind_eq_ok.mp expanded
  obtain ⟨size, sizeCompiled, expanded⟩ := lower_bind_eq_ok.mp expanded
  obtain ⟨code, codeCompiled, expanded⟩ := lower_bind_eq_ok.mp expanded
  obtain ⟨guarded, guardCompiled, returned⟩ := lower_bind_eq_ok.mp expanded
  obtain ⟨known, knownCompiled, guardResult⟩ := lower_bind_eq_ok.mp guardCompiled
  cases Except.ok.inj guardResult
  exact ⟨memory, size, code, known, memoryCompiled, sizeCompiled, codeCompiled, knownCompiled,
    (Except.ok.inj returned).symm⟩

theorem preserves (operation : Operation)
    {scope : Scope} {expected : Core.Ty} {arguments : List Lowered} {lowered : Lowered}
    (compiled : lowerBuiltin scope operation.name expected arguments = .ok lowered)
    {image : Option (List UInt8)} {sourceType : Ty} {sources : List Semantics.Value}
    {state finalState : MemorySemantics.State} {result : Semantics.Result Semantics.Value}
    (called : CodeImageSemantics.Builtin image operation.name sourceType sources state result finalState)
    {targets : List Core.Value} (related : ArgumentsRel arguments sources targets)
    {slots : List EffectSlot} {mapping : Renaming} {environment : Environment}
    {initial store : Store} {memoryLocation sizeLocation codeLocation knownLocation : Nat}
    (runtime : EffectEnvironmentRel slots scope mapping environment)
    (memoryMember : ⟨"memory", WordMapping.type, memoryLocation⟩ ∈ slots)
    (sizeMember : ⟨"memorySize", .word, sizeLocation⟩ ∈ slots)
    (codeMember : ⟨"code", WordMapping.type, codeLocation⟩ ∈ slots)
    (knownMember : ⟨"codeKnown", .bool, knownLocation⟩ ∈ slots)
    (codeRead : store.read? codeLocation = some (WordMapping.encode (Memory.packBytes (image.getD []))))
    (knownRead : store.read? knownLocation = some (.bool image.isSome))
    (stateRelated : MemoryCorrespondence.StateRel memoryLocation sizeLocation state store)
    (packed : Evaluates environment initial ((packArguments arguments).expression.rename mapping)
      (.inRight .word (ScalarExecution.bundleValues targets)) store) :
    ∃ target finalStore,
      ResultRel lowered.type result target ∧
      Evaluates environment initial (lowered.expression.rename mapping) target finalStore ∧
      MemoryCorrespondence.StateRel memoryLocation sizeLocation finalState finalStore ∧
      MemoryCorrespondence.Frame memoryLocation sizeLocation store finalStore := by
  have supported : Effects.supports operation.name = true := by cases operation <;> rfl
  obtain ⟨words, raw, rawCompiled, typed, loweredEqual⟩ := outer_components supported compiled
  have arity : arguments.length = 3 := by
    simpa only [List.length_map, List.length_range] using inner_arity operation rawCompiled
  obtain ⟨destinationExpr, sourceExpr, lengthExpr, destination, source, length, rfl, rfl, rfl⟩ :=
    MemoryCopyBuiltinCorrespondence.three_words related words arity
  obtain ⟨memory, size, code, known, memoryCompiled, sizeCompiled, codeCompiled, knownCompiled, rfl⟩ :=
    components operation rawCompiled
  cases typed
  cases loweredEqual
  let input := Value.pair (.word destination) (.pair (.word source) (.word length))
  let inputType := Core.Ty.product .word (.product .word .word)
  have runtime' := runtime.temporary inputType input
  generalize named : operation.name = name at called
  cases called with
  | copy sourceOperation executed =>
      cases executed with
      | unknown absent =>
          subst image
          refine ⟨.inLeft .unit (.word (Word.ofNatModulo 15)), store, .language _, ?_, stateRelated, .refl _ _ _⟩
          apply LanguageResult.bind_success .unit packed
          exact .ifFalse (.loadCell (reference_evaluates runtime' knownMember knownCompiled store) knownRead) (.inLeft .word)
      | copied present executed =>
          subst image
          obtain ⟨target, finalStore, resultRelated, evaluated, finalRelated, frame⟩ :=
            MemoryCopyCorrespondence.copyPackedFrom_preserves executed stateRelated
              (reference_evaluates runtime' memoryMember memoryCompiled store)
              (reference_evaluates runtime' sizeMember sizeCompiled store)
              (.first (.var (index := 0) rfl))
              (.loadCell (reference_evaluates runtime' codeMember codeCompiled store) codeRead)
              (.first (.second (.var (index := 0) rfl)))
              (by apply Evaluates.second; apply Evaluates.second; apply Evaluates.var (index := 0); rfl)
          refine ⟨target, finalStore, resultRelated, ?_, finalRelated, frame⟩
          apply LanguageResult.bind_success .unit packed
          apply Evaluates.ifTrue (.loadCell (reference_evaluates runtime' knownMember knownCompiled store) knownRead)
          rw [MemoryCopyCorrespondence.copyPackedFrom_rename]
          exact evaluated

end Solcore.Frontend.RustHull.CodeImageBuiltinCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.KeccakBuiltinCorrespondence
/-! Keccak source derivations pass through the actual outer builtin compiler,
including its word-argument checks and initialized memory references. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.KeccakBuiltinCorrespondence
open Core Correspondence PureCallCorrespondence EffectBuiltinCorrespondence

theorem inner_arity {scope : Scope} {arguments : List Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope "keccak256" arguments = .ok lowered) :
    arguments.length = 2 := by
  rcases arguments with _ | ⟨first, _ | ⟨second, _ | ⟨third, rest⟩⟩⟩
  all_goals first
    | rfl
    | change Except.error _ = Except.ok lowered at compiled
      cases compiled

theorem components {scope : Scope} {offset length : Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope "keccak256" [offset, length] = .ok lowered) :
    ∃ memory size, Effects.reference scope "memory" WordMapping.type = .ok memory ∧
      Effects.reference scope "memorySize" .word = .ok size ∧
      lowered = ⟨.word, Keccak.hash memory size offset length⟩ := by
  change (do
    let raw ← (do
      let memory ← Effects.reference scope "memory" WordMapping.type
      let size ← Effects.reference scope "memorySize" .word
      pure (Lowered.mk .word (Keccak.hash memory size offset length)) : LowerM Lowered)
    pure raw) = .ok lowered at compiled
  obtain ⟨memory, memoryCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨size, sizeCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
  exact ⟨memory, size, memoryCompiled, sizeCompiled, (Except.ok.inj returned).symm⟩

theorem preserves
    {scope : Scope} {expected : Core.Ty} {arguments : List Lowered} {lowered : Lowered}
    (compiled : lowerBuiltin scope "keccak256" expected arguments = .ok lowered)
    {sourceType : Ty} {sources : List Semantics.Value}
    {state finalState : MemorySemantics.State} {result : Semantics.Result Semantics.Value}
    (called : KeccakSemantics.Builtin "keccak256" sourceType sources state result finalState)
    {targets : List Core.Value} (related : ArgumentsRel arguments sources targets)
    {slots : List EffectSlot} {mapping : Renaming} {environment : Environment}
    {initial store : Store} {memoryLocation sizeLocation : Nat}
    (runtime : EffectEnvironmentRel slots scope mapping environment)
    (memoryMember : ⟨"memory", WordMapping.type, memoryLocation⟩ ∈ slots)
    (sizeMember : ⟨"memorySize", .word, sizeLocation⟩ ∈ slots)
    (stateRelated : MemoryCorrespondence.StateRel memoryLocation sizeLocation state store)
    (packed : Evaluates environment initial ((packArguments arguments).expression.rename mapping)
      (.inRight .word (ScalarExecution.bundleValues targets)) store) :
    ∃ target finalStore,
      ResultRel lowered.type result target ∧
      Evaluates environment initial (lowered.expression.rename mapping) target finalStore ∧
      MemoryCorrespondence.StateRel memoryLocation sizeLocation finalState finalStore ∧
      MemoryCorrespondence.Frame memoryLocation sizeLocation store finalStore := by
  obtain ⟨words, raw, rawCompiled, typed, loweredEqual⟩ := outer_components (by rfl) compiled
  have arity : arguments.length = 2 := by
    simpa only [List.length_map, List.length_range] using inner_arity rawCompiled
  obtain ⟨offsetExpr, lengthExpr, offset, length, rfl, rfl, rfl⟩ := two_words related words arity
  cases called with
  | hash executed =>
      obtain ⟨memory, size, memoryCompiled, sizeCompiled, rfl⟩ := components rawCompiled
      cases typed
      cases loweredEqual
      have runtime' := runtime.temporary (.product .word .word) (.pair (.word offset) (.word length))
      obtain ⟨target, finalStore, resultRelated, evaluated, finalRelated, frame⟩ :=
        KeccakHashCorrespondence.hash_preserves executed stateRelated
          (reference_evaluates runtime' memoryMember memoryCompiled store)
          (reference_evaluates runtime' sizeMember sizeCompiled store)
          (.first (.var (index := 0) rfl)) (.second (.var (index := 0) rfl))
      refine ⟨target, finalStore, resultRelated, ?_, finalRelated, frame⟩
      apply LanguageResult.bind_success .word packed
      rw [KeccakHashCorrespondence.hash_rename]
      exact evaluated

end Solcore.Frontend.RustHull.KeccakBuiltinCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.LogBuiltinCorrespondence
/-! Event capture through actual Hull builtin lowering, including the static
write guard and the runtime registers used by exceptional termination. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.LogBuiltinCorrespondence
open Core Correspondence PureCallCorrespondence EffectBuiltinCorrespondence LogsCorrespondence

structure Locations where
  logs : LogsCorrespondence.Locations
  address : Nat
  isStatic : Nat
  exit : Nat
  returnOffset : Nat
  returnSize : Nat

def Locations.all (locations : Locations) : List Nat :=
  locations.logs.all ++ [locations.address, locations.isStatic, locations.exit,
    locations.returnOffset, locations.returnSize]

def Locations.mutable (locations : Locations) : List Nat :=
  locations.logs.all ++ [locations.exit, locations.returnOffset, locations.returnSize]

structure StateRel (locations : Locations) (state : LogsSemantics.State) (store : Store) : Prop where
  logs : LogsCorrespondence.StateRel locations.logs state store
  address : store.read? locations.address = some (.word state.address)
  isStatic : store.read? locations.isStatic = some (.bool state.isStatic)
  exit : store.read? locations.exit = some (.word state.exit)
  returnOffset : store.read? locations.returnOffset = some (.word state.returnOffset)
  returnSize : store.read? locations.returnSize = some (.word state.returnSize)
  distinct : locations.all.Nodup

structure Frame (locations : Locations) (initial final : Store) : Prop where
  length_le : initial.length ≤ final.length
  preserved : ∀ location value, location ∉ locations.mutable →
    initial.read? location = some value → final.read? location = some value

theorem Frame.of_logs {locations : Locations} {initial final : Store}
    (frame : LogsCorrespondence.Frame locations.logs initial final) : Frame locations initial final :=
  ⟨frame.length, fun location value outside found => frame.read location value
    (fun member => outside (List.mem_append_left _ member)) found⟩

set_option linter.unusedSimpArgs false in
private theorem StateRel.withLogs {locations : Locations} {state finalState : LogsSemantics.State}
    {offset length : Word} {topics : List Word} {result : Semantics.Result Semantics.Value}
    {initial final : Store} (related : StateRel locations state initial)
    (appended : LogsSemantics.Append offset length topics state result finalState)
    (logs : LogsCorrespondence.StateRel locations.logs finalState final)
    (frame : LogsCorrespondence.Frame locations.logs initial final) : StateRel locations finalState final := by
  have distinct := related.distinct
  simp only [Locations.all, LogsCorrespondence.Locations.all, List.cons_append, List.nil_append,
    List.nodup_cons, List.mem_cons, List.mem_singleton, not_or] at distinct
  have address := frame.read _ _ (by simp only [LogsCorrespondence.Locations.all, List.mem_cons, List.mem_singleton]; intro same; rcases same with same | same | same | same <;> simp_all) related.address
  have isStatic := frame.read _ _ (by simp only [LogsCorrespondence.Locations.all, List.mem_cons, List.mem_singleton]; intro same; rcases same with same | same | same | same <;> simp_all) related.isStatic
  have exit := frame.read _ _ (by simp only [LogsCorrespondence.Locations.all, List.mem_cons, List.mem_singleton]; intro same; rcases same with same | same | same | same <;> simp_all) related.exit
  have returnOffset := frame.read _ _ (by simp only [LogsCorrespondence.Locations.all, List.mem_cons, List.mem_singleton]; intro same; rcases same with same | same | same | same <;> simp_all) related.returnOffset
  have returnSize := frame.read _ _ (by simp only [LogsCorrespondence.Locations.all, List.mem_cons, List.mem_singleton]; intro same; rcases same with same | same | same | same <;> simp_all) related.returnSize
  cases appended <;> exact ⟨logs, address, isStatic, exit, returnOffset, returnSize, related.distinct⟩

def haltStore (locations : Locations) (store : Store) : Store :=
  StorageBuiltinCorrespondence.haltCells locations.exit locations.returnOffset locations.returnSize store

theorem haltStore_other {locations : Locations} {store : Store} {location : Nat} {value : Core.Value}
    (exit : location ≠ locations.exit) (offset : location ≠ locations.returnOffset) (size : location ≠ locations.returnSize)
    (found : store.read? location = some value) :
    (haltStore locations store).read? location = some value := by
  simp only [haltStore, StorageBuiltinCorrespondence.haltCells, Store.read?,
    List.getElem?_set_ne (Ne.symm exit), List.getElem?_set_ne (Ne.symm offset), List.getElem?_set_ne (Ne.symm size)]
  exact found

theorem haltStore_frame (locations : Locations) (store : Store) : Frame locations store (haltStore locations store) := by
  constructor
  · simp [haltStore, StorageBuiltinCorrespondence.haltCells]
  · intro location value outside found
    simp [Locations.mutable] at outside
    exact haltStore_other outside.2.1 outside.2.2.1 outside.2.2.2 found

theorem StateRel.halt {locations : Locations} {state : LogsSemantics.State} {store : Store}
    (related : StateRel locations state store) :
    StateRel locations {state with exit := Word.ofNatModulo 3, returnOffset := Word.zero, returnSize := Word.zero}
      (haltStore locations store) := by
  have distinct := related.distinct
  simp [Locations.all, LogsCorrespondence.Locations.all] at distinct
  have offsetBound := (List.getElem?_eq_some_iff.mp related.returnOffset).1
  have sizeBound := (List.getElem?_eq_some_iff.mp related.returnSize).1
  have exitBound := (List.getElem?_eq_some_iff.mp related.exit).1
  constructor
  · constructor
    · exact related.logs.distinct
    · exact haltStore_other (by intro same; simp_all) (by intro same; simp_all) (by intro same; simp_all) related.logs.memory
    · exact haltStore_other (by intro same; simp_all) (by intro same; simp_all) (by intro same; simp_all) related.logs.memorySize
    · exact haltStore_other (by intro same; simp_all) (by intro same; simp_all) (by intro same; simp_all) related.logs.logs
    · exact haltStore_other (by intro same; simp_all) (by intro same; simp_all) (by intro same; simp_all) related.logs.logSize
  · exact haltStore_other (by intro same; simp_all) (by intro same; simp_all) (by intro same; simp_all) related.address
  · exact haltStore_other (by intro same; simp_all) (by intro same; simp_all) (by intro same; simp_all) related.isStatic
  · simp [haltStore, StorageBuiltinCorrespondence.haltCells, Store.read?, exitBound]
  · simp only [haltStore, StorageBuiltinCorrespondence.haltCells, Store.read?,
      List.getElem?_set_ne (by intro same; simp_all : locations.exit ≠ locations.returnOffset),
      List.getElem?_set_ne (by intro same; simp_all : locations.returnSize ≠ locations.returnOffset)]
    simp [offsetBound]
  · simp only [haltStore, StorageBuiltinCorrespondence.haltCells, Store.read?,
      List.getElem?_set_ne (by intro same; simp_all : locations.exit ≠ locations.returnSize)]
    simp [sizeBound]
  · exact related.distinct

private theorem log_components (operation : LogsSemantics.Operation) {scope : Scope}
    {offset length : Core.Expr} {topics : List Core.Expr} {lowered : Lowered}
    (count : topics.length = operation.count)
    (compiled : Effects.lowerBuiltin scope operation.name (offset :: length :: topics) = .ok lowered) :
    ∃ memory memorySize logs logSize address isStatic stop,
      Effects.reference scope "memory" WordMapping.type = .ok memory ∧
      Effects.reference scope "memorySize" .word = .ok memorySize ∧
      Effects.reference scope "logs" WordMapping.type = .ok logs ∧
      Effects.reference scope "logSize" .word = .ok logSize ∧
      Effects.reference scope "address" .word = .ok address ∧
      Effects.reference scope "isStatic" .bool = .ok isStatic ∧
      Effects.terminate scope 3 (.word Word.zero) (.word Word.zero) = .ok stop ∧
      lowered = ⟨.unit, .ifE (.loadCell isStatic) stop
        (Logs.append memory memorySize logs logSize (.loadCell address) topics offset length)⟩ := by
  let action : LowerM Lowered := do
    let memory ← Effects.reference scope "memory" WordMapping.type
    let memorySize ← Effects.reference scope "memorySize" .word
    let logs ← Effects.reference scope "logs" WordMapping.type
    let logSize ← Effects.reference scope "logSize" .word
    let address ← Effects.reference scope "address" .word
    let isStatic ← Effects.reference scope "isStatic" .bool
    let stop ← Effects.terminate scope 3 (.word Word.zero) (.word Word.zero)
    pure (Lowered.mk .unit (.ifE (.loadCell isStatic) stop
      (Logs.append memory memorySize logs logSize (.loadCell address) topics offset length)))
  have checked : ((if topics.length = operation.count then action
      else (fail "wrong number of log topics" : LowerM Unit) >>= fun _ => action) >>=
      fun raw => pure raw) = .ok lowered := by
    cases operation <;> exact compiled
  obtain ⟨raw, checked, returned⟩ := lower_bind_eq_ok.mp checked
  cases returned
  have components : action = .ok lowered := by
    simpa only [count, ↓reduceIte] using checked
  unfold action at components
  obtain ⟨memory, memoryCompiled, components⟩ := lower_bind_eq_ok.mp components
  obtain ⟨memorySize, memorySizeCompiled, components⟩ := lower_bind_eq_ok.mp components
  obtain ⟨logs, logsCompiled, components⟩ := lower_bind_eq_ok.mp components
  obtain ⟨logSize, logSizeCompiled, components⟩ := lower_bind_eq_ok.mp components
  obtain ⟨address, addressCompiled, components⟩ := lower_bind_eq_ok.mp components
  obtain ⟨isStatic, isStaticCompiled, components⟩ := lower_bind_eq_ok.mp components
  obtain ⟨stop, stopCompiled, returned⟩ := lower_bind_eq_ok.mp components
  exact ⟨memory, memorySize, logs, logSize, address, isStatic, stop, memoryCompiled, memorySizeCompiled,
    logsCompiled, logSizeCompiled, addressCompiled, isStaticCompiled, stopCompiled, (Except.ok.inj returned).symm⟩


theorem inner_preserves (operation : LogsSemantics.Operation)
    {scope : Scope} {offsetExpr lengthExpr : Core.Expr} {topicExprs : List Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope operation.name (offsetExpr :: lengthExpr :: topicExprs) = .ok lowered)
    {offset length : Word} {topics : List Word} (count : topics.length = operation.count)
    {state finalState : LogsSemantics.State} {result : Semantics.Result Semantics.Value}
    (executed : LogsSemantics.Execute offset length topics state result finalState)
    {slots : List EffectSlot} {mapping : Renaming} {environment : Environment} {store : Store}
    {locations : Locations} (runtime : EffectEnvironmentRel slots scope mapping environment)
    (memoryMember : ⟨"memory", WordMapping.type, locations.logs.memory⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, locations.logs.memorySize⟩ ∈ slots)
    (logsMember : ⟨"logs", WordMapping.type, locations.logs.logs⟩ ∈ slots)
    (logSizeMember : ⟨"logSize", .word, locations.logs.logSize⟩ ∈ slots)
    (addressMember : ⟨"address", .word, locations.address⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, locations.isStatic⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, locations.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, locations.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, locations.returnSize⟩ ∈ slots)
    (stateRelated : StateRel locations state store)
    (offsetEvaluated : Evaluates environment store (offsetExpr.rename mapping) (.word offset) store)
    (lengthEvaluated : Evaluates environment store (lengthExpr.rename mapping) (.word length) store)
    (topicsRelated : WordExpressions environment (topicExprs.map (·.rename mapping)) topics) :
    ∃ target finalStore, ResultRel lowered.type result target ∧
      Evaluates environment store (lowered.expression.rename mapping) target finalStore ∧
      StateRel locations finalState finalStore ∧ Frame locations store finalStore := by
  have topicLength : topicExprs.length = topics.length := by simpa using topicsRelated.length
  obtain ⟨memory, memorySize, logs, logSize, address, isStatic, stop,
    memoryCompiled, memorySizeCompiled, logsCompiled, logSizeCompiled, addressCompiled,
    staticCompiled, stopCompiled, rfl⟩ := log_components operation (topicLength.trans count) compiled
  cases executed with
  | static readOnly =>
      have distinct := stateRelated.distinct
      simp [Locations.all, LogsCorrespondence.Locations.all] at distinct
      refine ⟨.inLeft .unit (.word Word.maximum), haltStore locations store, .language _, ?_,
        stateRelated.halt, haltStore_frame _ _⟩
      apply Evaluates.ifTrue
      · exact .loadCell (reference_evaluates runtime staticMember staticCompiled store)
          (by simpa only [readOnly] using stateRelated.isStatic)
      · exact StorageBuiltinCorrespondence.stop_evaluates_cells stopCompiled runtime memorySizeMember
          exitMember offsetMember sizeMember stateRelated.exit stateRelated.returnOffset stateRelated.returnSize
          (by intro same; simp_all) (by intro same; simp_all) (by intro same; simp_all)
  | writable writable appended =>
      have allowed : topicExprs.length ≤ 4 := by rw [topicLength, count]; cases operation <;> decide
      obtain ⟨target, finalStore, resultRelated, evaluated, finalRelated, framed⟩ :=
        append_preserves appended stateRelated.logs
          (reference_evaluates runtime memoryMember memoryCompiled store)
          (reference_evaluates runtime memorySizeMember memorySizeCompiled store)
          (reference_evaluates runtime logsMember logsCompiled store)
          (reference_evaluates runtime logSizeMember logSizeCompiled store)
          (.loadCell (reference_evaluates runtime addressMember addressCompiled store) stateRelated.address)
          offsetEvaluated lengthEvaluated topicsRelated
      refine ⟨target, finalStore, resultRelated, ?_, stateRelated.withLogs appended finalRelated framed, Frame.of_logs framed⟩
      apply Evaluates.ifFalse
      · exact .loadCell (reference_evaluates runtime staticMember staticCompiled store)
          (by simpa only [writable] using stateRelated.isStatic)
      · rw [append_rename _ _ _ _ _ _ _ _ _ allowed]
        exact evaluated

private theorem wordPacket_eq_bundle (values : List Word) :
    wordPacket values = ScalarExecution.bundleValues (values.map Core.Value.word) := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
      cases tail with
      | nil => rfl
      | cons next rest => exact congrArg (Core.Value.pair (.word head)) ih

private theorem field_eq_project (index count : Nat) (expression : Core.Expr) :
    Logs.field index count expression = projectArgument index count expression := by
  induction count generalizing index expression with
  | zero => rfl
  | succ count ih =>
      cases count with
      | zero => rfl
      | succ count =>
          by_cases first : index = 0 <;> simp [Logs.field, projectArgument, first, ih]


/-- Source event execution is preserved by the actual public builtin compiler,
including its argument packing and temporary-scope renaming. -/
theorem preserves (operation : LogsSemantics.Operation)
    {scope : Scope} {expected : Core.Ty} {arguments : List Lowered} {lowered : Lowered}
    (compiled : lowerBuiltin scope operation.name expected arguments = .ok lowered)
    {offset length : Word} {topics : List Word} (count : topics.length = operation.count)
    {state finalState : LogsSemantics.State} {result : Semantics.Result Semantics.Value}
    (executed : LogsSemantics.Execute offset length topics state result finalState)
    {targets : List Core.Value}
    (related : ArgumentsRel arguments (.word offset :: .word length :: topics.map Semantics.Value.word) targets)
    {slots : List EffectSlot} {mapping : Renaming} {environment : Environment} {initial store : Store}
    {locations : Locations} (runtime : EffectEnvironmentRel slots scope mapping environment)
    (memoryMember : ⟨"memory", WordMapping.type, locations.logs.memory⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, locations.logs.memorySize⟩ ∈ slots)
    (logsMember : ⟨"logs", WordMapping.type, locations.logs.logs⟩ ∈ slots)
    (logSizeMember : ⟨"logSize", .word, locations.logs.logSize⟩ ∈ slots)
    (addressMember : ⟨"address", .word, locations.address⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, locations.isStatic⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, locations.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, locations.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, locations.returnSize⟩ ∈ slots)
    (stateRelated : StateRel locations state store)
    (packed : Evaluates environment initial ((packArguments arguments).expression.rename mapping)
      (.inRight .word (ScalarExecution.bundleValues targets)) store) :
    ∃ target finalStore, ResultRel lowered.type result target ∧
      Evaluates environment initial (lowered.expression.rename mapping) target finalStore ∧
      StateRel locations finalState finalStore ∧ Frame locations store finalStore := by
  have supported : Effects.supports operation.name = true := by cases operation <;> rfl
  obtain ⟨words, raw, rawCompiled, typed, loweredEqual⟩ := outer_components supported compiled
  obtain ⟨expressions, values, argumentsEqual, sourcesEqual, targetsEqual, lengths⟩ := word_arguments related words
  have valuesEqual : values = offset :: length :: topics :=
    (List.map_inj_right (fun _ _ equal => Semantics.Value.word.inj equal)).mp sourcesEqual.symm
  subst values
  have argumentsLength : arguments.length = (offset :: length :: topics).length := by
    rw [argumentsEqual, List.length_map, lengths]
  subst targets
  rw [← wordPacket_eq_bundle] at packed
  generalize projectedEqual : (List.range arguments.length).map
    (fun index => projectArgument index arguments.length (.var 0)) = projected at rawCompiled
  have fields : WordExpressions (wordPacket (offset :: length :: topics) :: environment)
      (projected.map (·.rename mapping.lift)) (offset :: length :: topics) := by
    have expressionsEqual : projected.map (·.rename mapping.lift) =
        (List.range (offset :: length :: topics).length).map
          (fun index => Logs.field index (offset :: length :: topics).length (.var 0)) := by
      rw [← projectedEqual, argumentsLength, List.map_map]
      apply List.map_congr_left
      intro index _
      simp only [Function.comp_apply]
      rw [projectArgument_rename, field_eq_project]
      rfl
    rw [expressionsEqual]
    exact (Stable.var (by rfl)).fields
  cases projected with
  | nil => cases fields
  | cons offsetExpr remaining =>
      cases remaining with
      | nil => cases fields with | cons first rest => cases rest
      | cons lengthExpr topicExprs =>
          cases fields with
          | cons first rest =>
            cases rest with
            | cons second topicFields =>
              obtain ⟨target, finalStore, resultRelated, evaluated, finalRelated, framed⟩ :=
                inner_preserves operation rawCompiled count executed
                  (runtime.temporary (packArguments arguments).type (wordPacket (offset :: length :: topics)))
                  memoryMember memorySizeMember logsMember logSizeMember addressMember staticMember
                  exitMember offsetMember sizeMember stateRelated (first.evaluates store) (second.evaluates store) topicFields
              cases typed
              cases loweredEqual
              exact ⟨target, finalStore, resultRelated, LanguageResult.bind_success raw.type packed evaluated,
                finalRelated, framed⟩

end Solcore.Frontend.RustHull.LogBuiltinCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.MemoryBuiltinCorrespondence
/-! Memory effects through the actual Hull builtin compiler. Successful
compilation supplies the argument constraints and runtime references. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.MemoryBuiltinCorrespondence
open Core Correspondence PureCallCorrespondence MemoryCorrespondence EffectBuiltinCorrespondence

inductive Operation where
  | load | store | store8 | size
  deriving DecidableEq

def Operation.name : Operation → String
  | .load => "mload" | .store => "mstore" | .store8 => "mstore8" | .size => "msize"

def Operation.arity : Operation → Nat
  | .load => 1 | .store | .store8 => 2 | .size => 0

private theorem inner_arity (operation : Operation) {scope : Scope}
    {arguments : List Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope operation.name arguments = .ok lowered) :
    arguments.length = operation.arity := by
  cases operation <;>
    rcases arguments with _ | ⟨first, _ | ⟨second, _ | ⟨third, rest⟩⟩⟩
  all_goals first
    | rfl
    | change Except.error _ = Except.ok lowered at compiled
      cases compiled

private theorem load_components {scope : Scope} {offset : Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope "mload" [offset] = .ok lowered) :
    ∃ memory size, Effects.reference scope "memory" WordMapping.type = .ok memory ∧
      Effects.reference scope "memorySize" .word = .ok size ∧
      lowered = ⟨.word, Memory.mload memory size offset⟩ := by
  change (do
    let raw ← (do
      let memory ← Effects.reference scope "memory" WordMapping.type
      let size ← Effects.reference scope "memorySize" .word
      pure (Lowered.mk .word (Memory.mload memory size offset)) : LowerM Lowered)
    pure raw) = .ok lowered at compiled
  obtain ⟨memory, memoryCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨size, sizeCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
  exact ⟨memory, size, memoryCompiled, sizeCompiled, (Except.ok.inj returned).symm⟩

private theorem store_components {scope : Scope} {offset value : Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope "mstore" [offset, value] = .ok lowered) :
    ∃ memory size, Effects.reference scope "memory" WordMapping.type = .ok memory ∧
      Effects.reference scope "memorySize" .word = .ok size ∧
      lowered = ⟨.unit, Memory.mstore memory size offset value⟩ := by
  change (do
    let raw ← (do
      let memory ← Effects.reference scope "memory" WordMapping.type
      let size ← Effects.reference scope "memorySize" .word
      pure (Lowered.mk .unit (Memory.mstore memory size offset value)) : LowerM Lowered)
    pure raw) = .ok lowered at compiled
  obtain ⟨memory, memoryCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨size, sizeCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
  exact ⟨memory, size, memoryCompiled, sizeCompiled, (Except.ok.inj returned).symm⟩

private theorem store8_components {scope : Scope} {offset value : Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope "mstore8" [offset, value] = .ok lowered) :
    ∃ memory size, Effects.reference scope "memory" WordMapping.type = .ok memory ∧
      Effects.reference scope "memorySize" .word = .ok size ∧
      lowered = ⟨.unit, Memory.mstore8 memory size offset value⟩ := by
  change (do
    let raw ← (do
      let memory ← Effects.reference scope "memory" WordMapping.type
      let size ← Effects.reference scope "memorySize" .word
      pure (Lowered.mk .unit (Memory.mstore8 memory size offset value)) : LowerM Lowered)
    pure raw) = .ok lowered at compiled
  obtain ⟨memory, memoryCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨size, sizeCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
  exact ⟨memory, size, memoryCompiled, sizeCompiled, (Except.ok.inj returned).symm⟩

private theorem size_components {scope : Scope} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope "msize" [] = .ok lowered) :
    ∃ size, Effects.reference scope "memorySize" .word = .ok size ∧
      lowered = ⟨.word, LanguageResult.success (.loadCell size)⟩ := by
  change (do
    let raw ← (do
      let size ← Effects.reference scope "memorySize" .word
      pure (Lowered.mk .word (LanguageResult.success (.loadCell size))) : LowerM Lowered)
    pure raw) = .ok lowered at compiled
  obtain ⟨size, sizeCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
  exact ⟨size, sizeCompiled, (Except.ok.inj returned).symm⟩

/-- The compiler, argument relation and actual runtime references determine
the source memory result. No premise supplies a computed source outcome. -/
theorem preserves (operation : Operation)
    {scope : Scope} {expected : Core.Ty} {arguments : List Lowered} {lowered : Lowered}
    (compiled : lowerBuiltin scope operation.name expected arguments = .ok lowered)
    {sources : List Semantics.Value} {targets : List Core.Value}
    (related : ArgumentsRel arguments sources targets)
    {slots : List EffectSlot} {mapping : Renaming} {environment : Environment}
    {initial store : Store} {memoryLocation sizeLocation : Nat} {state : MemorySemantics.State}
    (runtime : EffectEnvironmentRel slots scope mapping environment)
    (memoryMember : ⟨"memory", WordMapping.type, memoryLocation⟩ ∈ slots)
    (sizeMember : ⟨"memorySize", .word, sizeLocation⟩ ∈ slots)
    (stateRelated : MemoryCorrespondence.StateRel memoryLocation sizeLocation state store)
    (packed : Evaluates environment initial ((packArguments arguments).expression.rename mapping)
      (.inRight .word (ScalarExecution.bundleValues targets)) store)
    (sourceType : Ty) :
    ∃ result finalState target finalStore,
      MemorySemantics.builtin operation.name sourceType sources state = some (result, finalState) ∧
      ResultRel lowered.type result target ∧
      Evaluates environment initial (lowered.expression.rename mapping) target finalStore ∧
      MemoryCorrespondence.StateRel memoryLocation sizeLocation finalState finalStore ∧
      MemoryCorrespondence.Frame memoryLocation sizeLocation store finalStore := by
  have supported : Effects.supports operation.name = true := by cases operation <;> rfl
  obtain ⟨words, raw, rawCompiled, typed, loweredEqual⟩ := outer_components supported compiled
  have arity : arguments.length = operation.arity := by
    simpa only [List.length_map, List.length_range] using inner_arity operation rawCompiled
  cases operation with
  | size =>
      have empty : arguments = [] := List.eq_nil_of_length_eq_zero arity
      subst arguments
      cases related
      obtain ⟨size, sizeCompiled, rfl⟩ := size_components rawCompiled
      cases typed
      cases loweredEqual
      refine ⟨.value (.word state.size), state, .inRight .word (.word state.size), store,
        rfl, .value (.word _), ?_, stateRelated, Frame.refl _ _ _⟩
      apply LanguageResult.bind_success .word packed
      exact .inRight (.loadCell
        (reference_evaluates (runtime.temporary .unit .unit) sizeMember sizeCompiled store) stateRelated.size)
  | load =>
      obtain ⟨offsetExpr, offset, rfl, rfl, rfl⟩ := one_word related words arity
      obtain ⟨memory, size, memoryCompiled, sizeCompiled, rfl⟩ := load_components rawCompiled
      cases typed
      cases loweredEqual
      obtain ⟨resultRelated, finalRelated, framed⟩ := mload_preserves stateRelated offset (.word offset :: environment)
      refine ⟨(MemorySemantics.mload state offset).1, (MemorySemantics.mload state offset).2,
        mloadResult state offset, mloadStore store memoryLocation sizeLocation state offset (.word offset :: environment),
        rfl, resultRelated, ?_, finalRelated, framed⟩
      apply LanguageResult.bind_success .word packed
      rw [mload_rename]
      exact mload_evaluates state offset
        (reference_evaluates (runtime.temporary .word (.word offset)) memoryMember memoryCompiled store)
        (reference_evaluates (runtime.temporary .word (.word offset)) sizeMember sizeCompiled store)
        (.var rfl) stateRelated.memory stateRelated.size stateRelated.distinct
  | store =>
      obtain ⟨offsetExpr, valueExpr, offset, value, rfl, rfl, rfl⟩ := two_words related words arity
      obtain ⟨memory, size, memoryCompiled, sizeCompiled, rfl⟩ := store_components rawCompiled
      cases typed
      cases loweredEqual
      obtain ⟨resultRelated, finalRelated, framed⟩ :=
        mstore_preserves stateRelated offset value (.pair (.word offset) (.word value) :: environment)
      refine ⟨(MemorySemantics.mstore state offset value).1, (MemorySemantics.mstore state offset value).2,
        mstoreResult state offset, mstoreStore store memoryLocation sizeLocation state offset value
          (.pair (.word offset) (.word value) :: environment),
        rfl, resultRelated, ?_, finalRelated, framed⟩
      apply LanguageResult.bind_success .unit packed
      rw [mstore_rename]
      exact mstore_evaluates state offset value
        (reference_evaluates (runtime.temporary (.product .word .word) (.pair (.word offset) (.word value)))
          memoryMember memoryCompiled store)
        (reference_evaluates (runtime.temporary (.product .word .word) (.pair (.word offset) (.word value)))
          sizeMember sizeCompiled store)
        (.first (.var rfl)) (.second (.var rfl)) stateRelated.memory stateRelated.size stateRelated.distinct
  | store8 =>
      obtain ⟨offsetExpr, valueExpr, offset, value, rfl, rfl, rfl⟩ := two_words related words arity
      obtain ⟨memory, size, memoryCompiled, sizeCompiled, rfl⟩ := store8_components rawCompiled
      cases typed
      cases loweredEqual
      obtain ⟨resultRelated, finalRelated, framed⟩ :=
        mstore8_preserves stateRelated offset value (.pair (.word offset) (.word value) :: environment)
      refine ⟨(MemorySemantics.mstore8 state offset value).1, (MemorySemantics.mstore8 state offset value).2,
        mstore8Result state offset, mstore8Store store memoryLocation sizeLocation state offset value
          (.pair (.word offset) (.word value) :: environment),
        rfl, resultRelated, ?_, finalRelated, framed⟩
      apply LanguageResult.bind_success .unit packed
      rw [mstore8_rename]
      exact mstore8_evaluates state offset value
        (reference_evaluates (runtime.temporary (.product .word .word) (.pair (.word offset) (.word value)))
          memoryMember memoryCompiled store)
        (reference_evaluates (runtime.temporary (.product .word .word) (.pair (.word offset) (.word value)))
          sizeMember sizeCompiled store)
        (.first (.var rfl)) (.second (.var rfl)) stateRelated.memory stateRelated.size stateRelated.distinct

end Solcore.Frontend.RustHull.MemoryBuiltinCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.MemoryGuardBuiltinCorrespondence
/-! The real builtin compiler implements the independent memory guard by
returning its evaluated word, without changing the resulting argument store. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.MemoryGuardBuiltinCorrespondence
open Core Correspondence PureCallCorrespondence EffectBuiltinCorrespondence

private theorem inner_arity {scope : Scope} {arguments : List Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope "memoryguard" arguments = .ok lowered) :
    arguments.length = 1 := by
  rcases arguments with _ | ⟨first, _ | ⟨second, rest⟩⟩
  all_goals first
    | rfl
    | change Except.error _ = Except.ok lowered at compiled
      cases compiled

private theorem inner_components {scope : Scope} {value : Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope "memoryguard" [value] = .ok lowered) :
    lowered = ⟨.word, LanguageResult.success value⟩ := by
  change Except.ok (Lowered.mk .word (LanguageResult.success value)) = .ok lowered at compiled
  exact (Except.ok.inj compiled).symm

/-- Successful lowering and the evaluated arguments give the same source word.
The builtin uses no effect slots and performs no store writes or allocations. -/
theorem preserves {scope : Scope} {name : String} {sourceType : Ty} {expected : Core.Ty}
    {arguments : List Lowered} {lowered : Lowered}
    (compiled : lowerBuiltin scope name expected arguments = .ok lowered)
    {sources : List Semantics.Value} {result : Semantics.Result Semantics.Value}
    (called : MemoryGuardSemantics.Builtin name sourceType sources result)
    {targets : List Core.Value} (related : ArgumentsRel arguments sources targets)
    {mapping : Renaming} {environment : Environment} {initial store : Store}
    (packed : Evaluates environment initial ((packArguments arguments).expression.rename mapping)
      (.inRight .word (ScalarExecution.bundleValues targets)) store) :
    ∃ target, ResultRel lowered.type result target ∧
      Evaluates environment initial (lowered.expression.rename mapping) target store := by
  cases called with
  | @guarded _ value =>
      obtain ⟨words, raw, rawCompiled, typed, loweredEqual⟩ := outer_components rfl compiled
      have arity : arguments.length = 1 := by
        simpa only [List.length_map, List.length_range] using inner_arity rawCompiled
      obtain ⟨expression, input, rfl, same, rfl⟩ := one_word related words arity
      have same : value = input := by simpa only [List.cons.injEq, Semantics.Value.word.injEq, true_and, and_true] using same
      subst input
      obtain rfl := inner_components rawCompiled
      cases typed
      cases loweredEqual
      refine ⟨.inRight .word (.word value), .value (.word _), ?_⟩
      apply LanguageResult.bind_success .word packed
      exact .inRight (.var rfl)

end Solcore.Frontend.RustHull.MemoryGuardBuiltinCorrespondence
end
