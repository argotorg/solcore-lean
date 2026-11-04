import Solcore.ContractRuntime.Account
import Solcore.ContractRuntime.CreationAddressPolicy
import Solcore.ContractRuntime.AddressBytesBE
import Solcore.ContractRuntime.AddressWordBridge
import Solcore.ContractRuntime.RuntimeScalars
import Solcore.Core.Primitive
import Solcore.ContractRuntime.BalanceTransfer
import Solcore.ContractRuntime.CheckedHostCoreWordProgram
import Solcore.ContractRuntime.WorldState
import Solcore.ContractRuntime.WorldStateBalanceProperties
import Solcore.ContractRuntime.CheckedCoreProgram
import Solcore.ContractRuntime.WorldStateCode
import Solcore.Test.ContractRuntime.TopLevelExecution
import Solcore.ContractRuntime.WorldStateDelta
import Solcore.ContractRuntime.WorldStateNonceProperties
import Solcore.ContractRuntime.WorldStateStorageRead

/-!
# World state tests

World state reads, writes and deltas, balances, nonces, code, address encodings and returned frames.
-/

section
-- leanmerge: from Solcore.Test.AccountNonceIncrementProperties
/-! External compile and executable checks for creation foundation APIs. -/

set_option autoImplicit false

namespace Tests.AccountNonceIncrementProperties

open Solcore
open Solcore.ContractRuntime

example := @Account.incrementNonce?_isSome_iff
example := @Account.incrementNonce?_eq_none_iff
example := @Account.incrementNonce?_success_exact
example := @Account.incrementNonce?_maximum
example := @Account.incrementNonce?_preserves_payload
example := @Account.incrementNonce?_success_iff

private def word (value : Nat) (bound : value < Core.wordModulus := by decide) :
    Core.Word := ⟨value, bound⟩

private def policy : CreationAddressPolicy := {
  derive := fun creator nonce =>
    ⟨(creator.val + nonce.val) % addressModulus,
      Nat.mod_lt _ (by decide)⟩
}

private def creator : Address := ⟨7, by decide⟩

private theorem policyBoundaryCompiles :
    policy.derive creator (word 5) = ⟨12, by decide⟩ := by
  native_decide

private theorem checkedIncrementRunsExactly :
    (Account.empty.withNonce (word 5)).incrementNonce?.map Account.nonce =
      some (word 6) := by
  native_decide

private theorem maximumDoesNotWrap :
    (Account.empty.withNonce Core.Word.maximum).incrementNonce? = none := by
  native_decide

def testAccountNonceIncrement : IO Unit := do
  unless (Account.empty.withNonce (word 5)).incrementNonce?.map Account.nonce ==
      some (word 6) do
    throw (IO.userError "checked nonce increment did not return exact successor")
  unless (Account.empty.withNonce Core.Word.maximum).incrementNonce?.isNone do
    throw (IO.userError "maximum nonce wrapped instead of failing")

end Tests.AccountNonceIncrementProperties
end

section
-- leanmerge: from Solcore.Test.AddressBytesBE
/-! Executable boundary tests for exact 20-byte big-endian addresses. -/

set_option autoImplicit false

namespace Tests

open Solcore.ContractRuntime

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def bytes (values : List UInt8) : ByteArray :=
  values.toByteArray

private def addressZero : Address := ⟨0, by decide⟩
private def addressOne : Address := ⟨1, by decide⟩
private def addressMiddle : Address := ⟨0x123456789abcdef, by decide⟩
private def addressMaximum : Address := ⟨addressModulus - 1, by decide⟩

private def representativeAddresses : List Address :=
  [addressZero, addressOne, addressMiddle, addressMaximum]

private def zeroBytes : ByteArray :=
  bytes (List.replicate 20 0)

private def oneBytes : ByteArray :=
  bytes (List.replicate 19 0 ++ [1])

private def maximumBytes : ByteArray :=
  bytes (List.replicate 20 0xff)

private def nineteenBytes : ByteArray :=
  bytes (List.replicate 19 0)

private def twentyOneBytes : ByteArray :=
  bytes (List.replicate 21 0)

def testAddressBytesBE : IO Unit := do
  assertTrue (encodeAddressBytesBE addressZero == zeroBytes)
    "zero address encoding must contain exactly twenty zero octets"
  assertTrue (encodeAddressBytesBE addressOne == oneBytes)
    "address one encoding must preserve nineteen leading zero octets"
  assertTrue (encodeAddressBytesBE addressMaximum == maximumBytes)
    "maximum address encoding must contain exactly twenty 0xff octets"
  assertTrue (decodeAddressBytesBE? zeroBytes == some addressZero)
    "twenty zero octets must decode as the zero address"
  assertTrue (decodeAddressBytesBE? oneBytes == some addressOne)
    "nineteen zero octets followed by one must decode as address one"
  assertTrue (decodeAddressBytesBE? maximumBytes == some addressMaximum)
    "twenty 0xff octets must decode as the maximum address"
  assertTrue (decodeAddressBytesBE? nineteenBytes == none)
    "strict address decoding must reject nineteen bytes"
  assertTrue (decodeAddressBytesBE? twentyOneBytes == none)
    "strict address decoding must reject twenty-one bytes"
  assertTrue
    (representativeAddresses.all fun address =>
      decodeAddressBytesBE? (encodeAddressBytesBE address) == some address)
    "zero, one, a middle address, and the maximum must round-trip through exact bytes"
  assertTrue
    (representativeAddresses.all fun address =>
      let addressBytes := encodeAddressBytesBE address
      let wordBytes := encodeWordBytesBE (addressToWord address)
      addressBytes.size == 20 && wordBytes.size == 32 &&
        (List.range 20).all (fun index =>
          addressBytes.data[index]? == wordBytes.data[index + 12]?))
    "every representative address byte must match its widened word at offset twelve"

end Tests
end

section
-- leanmerge: from Solcore.Test.AddressCodecCoherence
/-! Executable coherence tests for canonical address text and exact bytes. -/

set_option autoImplicit false

namespace Tests

open Solcore.ContractRuntime

private def nineteenBytes_variant : ByteArray :=
  bytes ([0x12] ++ List.replicate 17 0 ++ [0x34])

private def twentyBytes : ByteArray :=
  bytes ([0x12] ++ List.replicate 18 0 ++ [0x34])

private def twentyOneBytes_variant : ByteArray :=
  bytes ([0x12] ++ List.replicate 19 0 ++ [0x34])

private def directAndByteMediated (text : String) : Option Address × Option Address :=
  (decodeAddressText? text, (decodeBytesText? text).bind decodeAddressBytesBE?)

private def canonicalByteTextAgrees (value : ByteArray) : Bool :=
  let text := encodeBytesText value
  decodeAddressText? text == decodeAddressBytesBE? value

private def decoderFixtures : List (String × String) :=
  [ ("canonical zero", encodeAddressText addressZero)
  , ("canonical middle", encodeAddressText addressMiddle)
  , ("uppercase", "0x00000000000000000000000000000000000000AB")
  , ("odd width", "0x0")
  , ("wrong width", "0x000000000000000000000000000000000000000")
  ]

private def firstDecoderMismatch? : Option String :=
  (decoderFixtures.find? fun fixture =>
    let paths := directAndByteMediated fixture.2
    paths.1 != paths.2).map Prod.fst

def testAddressCodecCoherence : IO Unit := do
  assertTrue
    (encodeBytesText (encodeAddressBytesBE addressZero) == encodeAddressText addressZero)
    "zero address text must equal the text of its exact byte encoding"
  assertTrue
    (encodeBytesText (encodeAddressBytesBE addressOne) == encodeAddressText addressOne)
    "address one text must preserve leading zeros across the byte codec"
  assertTrue
    (encodeBytesText (encodeAddressBytesBE addressMiddle) == encodeAddressText addressMiddle)
    "middle address text must equal the text of its exact byte encoding"
  assertTrue
    (encodeBytesText (encodeAddressBytesBE addressMaximum) == encodeAddressText addressMaximum)
    "maximum address text must equal the text of its exact byte encoding"
  assertTrue (canonicalByteTextAgrees nineteenBytes_variant)
    "canonical text for an independent nineteen-byte value must agree on rejection"
  assertTrue (canonicalByteTextAgrees twentyBytes)
    "canonical text for an independent twenty-byte value must agree on decoding"
  assertTrue (canonicalByteTextAgrees twentyOneBytes_variant)
    "canonical text for an independent twenty-one-byte value must agree on rejection"
  assertTrue firstDecoderMismatch?.isNone
    s!"direct and byte-mediated address decoding disagree for {firstDecoderMismatch?.getD "unknown fixture"}"

end Tests
end

section
-- leanmerge: from Solcore.Test.AddressWordBridge
/-! Executable boundary tests for strict address and word conversion. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.ContractRuntime

private def wordZero : Word := ⟨0, by decide⟩
private def wordOne : Word := ⟨1, by decide⟩
private def wordAddressMaximum : Word :=
  ⟨addressModulus - 1, by decide⟩
private def firstAddressOverflow : Word := ⟨addressModulus, by decide⟩
private def wordMaximum : Word := ⟨wordModulus - 1, by decide⟩

private def representativeAddress : Address :=
  ⟨0x123456789abcdef, by decide⟩
private def representativeWord : Word :=
  ⟨0x123456789abcdef, by decide⟩

private def representativeAddresses_variant : List Address :=
  [addressZero, addressOne, representativeAddress, addressMaximum]

private def representativeWords : List Word :=
  [wordZero, wordOne, representativeWord, wordAddressMaximum]

def testAddressWordBridge : IO Unit := do
  assertTrue (addressToWord addressZero == wordZero)
    "widening the zero address must produce the zero word"
  assertTrue (addressToWord addressOne == wordOne)
    "widening address one must preserve its natural-number value"
  assertTrue (addressToWord addressMaximum == wordAddressMaximum)
    "widening the maximum address must preserve all 160 bits"
  assertTrue (wordToAddress? wordZero == some addressZero)
    "the zero word must narrow to the zero address"
  assertTrue (wordToAddress? wordOne == some addressOne)
    "word one must narrow to address one"
  assertTrue (wordToAddress? wordAddressMaximum == some addressMaximum)
    "the largest in-range word must narrow to the maximum address"
  assertTrue (wordToAddress? firstAddressOverflow == none)
    "the first 160-bit overflow word must be rejected instead of truncated to zero"
  assertTrue (wordToAddress? wordMaximum == none)
    "the maximum word must be rejected instead of truncated to an address"
  assertTrue
    (representativeAddresses_variant.all fun address =>
      wordToAddress? (addressToWord address) == some address)
    "zero, one, a middle address, and the maximum must survive widening and narrowing"
  assertTrue
    (representativeWords.all fun word =>
      match wordToAddress? word with
      | some address => addressToWord address == word
      | none => false)
    "successfully narrowed zero, one, middle, and maximum-address words must reconstruct"

end Tests
end

section
-- leanmerge: from Solcore.Test.BalanceTransfer
/-! Executable boundary tests for checked balance transfer. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.ContractRuntime

private def sender : Address := ⟨0, by decide⟩
private def recipient : Address := ⟨1, by decide⟩
private def absent : Address := ⟨2, by decide⟩

private def word (value : Nat) (inBounds : value < Core.wordModulus := by decide) :
    Core.Word :=
  ⟨value, inBounds⟩

private def accountWith (balance : Core.Word) : Account :=
  Account.empty.withBalance balance

private def worldWith
    (senderBalance recipientBalance : Core.Word) : WorldState :=
  (WorldState.empty.putAccount sender (accountWith senderBalance)).putAccount
    recipient (accountWith recipientBalance)

def testBalanceTransfer : IO Unit := do
  assertTrue
    (Balance.checkedDebit? (word 4) (word 5) == none)
    "checked debit must reject underflow"
  assertTrue
    (Balance.checkedDebit? (word 5) (word 4) == some (word 1))
    "checked debit must return the exact mathematical difference"
  assertTrue
    (Balance.checkedCredit? Core.Word.maximum (word 1) == none)
    "checked credit must reject 256-bit overflow"
  assertTrue
    (Balance.checkedCredit? (word 5) (word 4) == some (word 9))
    "checked credit must return the exact mathematical sum"

  let base := worldWith (word 10) (word 3)
  assertTrue
    (match base.transferBalance sender recipient (word 4) with
      | .ok next =>
          next.balance? sender == some (word 6) &&
            next.balance? recipient == some (word 7)
      | .error _ => false)
    "a valid transfer must debit and credit the exact endpoints"
  assertTrue
    (match base.transferBalance absent recipient (word 1) with
      | .error .senderAbsent => true
      | _ => false)
    "an absent sender must be reported without account creation"
  assertTrue
    (match base.transferBalance sender absent (word 1) with
      | .error .recipientAbsent => true
      | _ => false)
    "an absent recipient must be reported without account creation"
  assertTrue
    (match base.transferBalance sender recipient (word 11) with
      | .error .insufficientBalance => true
      | _ => false)
    "a transfer larger than the sender balance must fail"

  let overflowing := worldWith (word 10) Core.Word.maximum
  assertTrue
    (match overflowing.transferBalance sender recipient (word 1) with
      | .error .recipientOverflow => true
      | _ => false)
    "recipient overflow must fail instead of wrapping"
  assertTrue
    (match base.transferBalance sender recipient Core.Word.zero with
      | .ok next =>
          next.balance? sender == base.balance? sender &&
            next.balance? recipient == base.balance? recipient
      | .error _ => false)
    "a zero transfer between present accounts must be exact identity"
  assertTrue
    (match base.transferBalance sender sender (word 10) with
      | .ok next => next.balance? sender == base.balance? sender
      | .error _ => false)
    "a funded self transfer must be exact identity"
  assertTrue
    (match base.transferBalance recipient recipient (word 4) with
      | .error .insufficientBalance => true
      | _ => false)
    "a self transfer must still enforce sufficient balance"

end Tests
end

section
-- leanmerge: from Solcore.Test.BalanceTransferInstallationExternalProperties
/-! External compile consumer for balance-transfer installation transport. -/

set_option autoImplicit false

namespace Tests.BalanceTransferInstallationExternalProperties

example := @Solcore.ContractRuntime.WorldState.transferBalance_preserves_installed

end Tests.BalanceTransferInstallationExternalProperties
end

section
-- leanmerge: from Solcore.Test.BalanceTransferProperties
/-! External compile consumers for every public balance-transfer theorem. -/
set_option autoImplicit false

namespace Tests
open Solcore
open Solcore.ContractRuntime

example (balance amount result : Core.Word) :
    Balance.checkedDebit? balance amount = some result ↔
      amount.val ≤ balance.val ∧ result.val = balance.val - amount.val :=
  Balance.checkedDebit_eq_some_iff balance amount result

example (balance amount : Core.Word) :
    Balance.checkedDebit? balance amount = none ↔ balance.val < amount.val :=
  Balance.checkedDebit_eq_none_iff balance amount

example (balance amount result : Core.Word) :
    Balance.checkedCredit? balance amount = some result ↔
      balance.val + amount.val < Core.wordModulus ∧
        result.val = balance.val + amount.val :=
  Balance.checkedCredit_eq_some_iff balance amount result

example (balance amount : Core.Word) :
    Balance.checkedCredit? balance amount = none ↔
      Core.wordModulus ≤ balance.val + amount.val :=
  Balance.checkedCredit_eq_none_iff balance amount

example (state : WorldState) (sender recipient : Address) (amount : Core.Word)
    (h : state.account? sender = none) :
    state.transferBalance sender recipient amount = .error .senderAbsent :=
  WorldState.transferBalance_senderAbsent state sender recipient amount h

example (state : WorldState) (sender recipient : Address) (amount : Core.Word)
    (senderAccount : Account) (hs : state.account? sender = some senderAccount)
    (hr : state.account? recipient = none) :
    state.transferBalance sender recipient amount = .error .recipientAbsent :=
  WorldState.transferBalance_recipientAbsent state sender recipient amount
    senderAccount hs hr

example (state : WorldState) (sender recipient : Address) (amount : Core.Word)
    (senderAccount recipientAccount : Account)
    (hs : state.account? sender = some senderAccount)
    (hr : state.account? recipient = some recipientAccount)
    (h : senderAccount.balance.val < amount.val) :
    state.transferBalance sender recipient amount = .error .insufficientBalance :=
  WorldState.transferBalance_insufficient state sender recipient amount
    senderAccount recipientAccount hs hr h

example (state : WorldState) (sender recipient : Address)
    (senderAccount recipientAccount : Account)
    (hs : state.account? sender = some senderAccount)
    (hr : state.account? recipient = some recipientAccount) :
    state.transferBalance sender recipient Core.Word.zero = .ok state :=
  WorldState.transferBalance_zero state sender recipient senderAccount
    recipientAccount hs hr

example (state : WorldState) (address : Address) (amount : Core.Word)
    (account : Account) (hp : state.account? address = some account)
    (h : amount.val ≤ account.balance.val) :
    state.transferBalance address address amount = .ok state :=
  WorldState.transferBalance_self state address amount account hp h

example (state : WorldState) (sender recipient : Address) (amount : Core.Word)
    (senderAccount recipientAccount : Account)
    (hs : state.account? sender = some senderAccount)
    (hr : state.account? recipient = some recipientAccount)
    (sufficient : amount.val ≤ senderAccount.balance.val)
    (nonzero : amount ≠ Core.Word.zero) (different : sender ≠ recipient)
    (overflow : Core.wordModulus ≤ recipientAccount.balance.val + amount.val) :
    state.transferBalance sender recipient amount = .error .recipientOverflow :=
  WorldState.transferBalance_overflow state sender recipient amount senderAccount
    recipientAccount hs hr sufficient nonzero different overflow

example (state : WorldState) (sender recipient : Address) (amount : Core.Word)
    (senderAccount recipientAccount : Account)
    (hs : state.account? sender = some senderAccount)
    (hr : state.account? recipient = some recipientAccount)
    (debited credited : Core.Word)
    (hd : Balance.checkedDebit? senderAccount.balance amount = some debited)
    (hc : Balance.checkedCredit? recipientAccount.balance amount = some credited)
    (nonzero : amount ≠ Core.Word.zero) (different : sender ≠ recipient) :
    state.transferBalance sender recipient amount = .ok
      ((state.putAccount sender (senderAccount.withBalance debited)).putAccount
        recipient (recipientAccount.withBalance credited)) :=
  WorldState.transferBalance_cross_eq state sender recipient amount senderAccount
    recipientAccount hs hr debited credited hd hc nonzero different

example (state : WorldState) (sender recipient : Address)
    (senderAccount recipientAccount : Account) (debited credited : Core.Word)
    (different : sender ≠ recipient) :
    let next := (state.putAccount sender (senderAccount.withBalance debited)).putAccount
      recipient (recipientAccount.withBalance credited)
    next.balance? sender = some debited ∧ next.balance? recipient = some credited :=
  WorldState.transferBalance_cross_balances state sender recipient senderAccount
    recipientAccount debited credited different

example (state : WorldState) (sender recipient other : Address)
    (senderAccount recipientAccount : Account) (debited credited : Core.Word)
    (hos : other ≠ sender) (hor : other ≠ recipient) :
    ((state.putAccount sender (senderAccount.withBalance debited)).putAccount
      recipient (recipientAccount.withBalance credited)).account? other =
      state.account? other :=
  WorldState.transferBalance_cross_account_other state sender recipient other
    senderAccount recipientAccount debited credited hos hor

example (senderAccount recipientAccount : Account) (debited credited : Core.Word) :
    (senderAccount.withBalance debited).code? = senderAccount.code? ∧
      (∀ slot, (senderAccount.withBalance debited).storageValue? slot =
        senderAccount.storageValue? slot) ∧
      (recipientAccount.withBalance credited).code? = recipientAccount.code? ∧
      (∀ slot, (recipientAccount.withBalance credited).storageValue? slot =
        recipientAccount.storageValue? slot) :=
  WorldState.transferBalance_cross_preserves_payload senderAccount
    recipientAccount debited credited

example (senderBalance recipientBalance amount debited credited : Core.Word)
    (hd : Balance.checkedDebit? senderBalance amount = some debited)
    (hc : Balance.checkedCredit? recipientBalance amount = some credited) :
    debited.val + credited.val = senderBalance.val + recipientBalance.val :=
  WorldState.transferBalance_cross_conserves senderBalance recipientBalance
    amount debited credited hd hc

end Tests
end

section
-- leanmerge: from Solcore.Test.WordReturnedFrameCompletionProperties
/-! Compile-only consumers for checked Word returned-frame proof contracts. -/

set_option autoImplicit false

namespace Solcore.Test.WordReturnedFrameCompletionProperties

open ContractRuntime

universe u v w

variable (checkedCode : CheckedHostCoreProgram)
variable (resultTypeEq : checkedCode.program.resultType = .word)
variable (resultTypeNe : checkedCode.program.resultType ≠ .word)

example : (CheckedHostCoreWordProgram.mk checkedCode resultTypeEq).code =
    checkedCode :=
  CheckedHostCoreWordProgram.mk_code checkedCode resultTypeEq

example :
    (CheckedHostCoreWordProgram.mk checkedCode resultTypeEq).code.program.resultType =
      .word :=
  CheckedHostCoreWordProgram.mk_resultType checkedCode resultTypeEq

example : CheckedHostCoreWordProgram.ofChecked? checkedCode =
    some ⟨checkedCode, resultTypeEq⟩ :=
  CheckedHostCoreWordProgram.ofChecked?_of_word checkedCode resultTypeEq

example : CheckedHostCoreWordProgram.ofChecked? checkedCode = none :=
  CheckedHostCoreWordProgram.ofChecked?_of_nonword checkedCode resultTypeNe

variable (program : Core.Program)
variable (checked : program.checkHost = true)
variable (rejected : program.checkHost = false)
variable (programWord : program.resultType = .word)
variable (programNonword : program.resultType ≠ .word)

example : CheckedHostCoreWordProgram.ofProgram? program =
    some ⟨⟨program, checked⟩, programWord⟩ :=
  CheckedHostCoreWordProgram.ofProgram?_of_checked_word
    program checked programWord

example : CheckedHostCoreWordProgram.ofProgram? program = none :=
  CheckedHostCoreWordProgram.ofProgram?_of_rejected program rejected

example : CheckedHostCoreWordProgram.ofProgram? program = none :=
  CheckedHostCoreWordProgram.ofProgram?_of_checked_nonword
    program checked programNonword

variable {RollbackState : Type u} {TraceState : Type v}
variable {TrapReason : Type w}

abbrev Context (RollbackState : Type u) (TraceState : Type v) :=
  HostStorageDriver.Context RollbackState TraceState
abbrev Completion (RollbackState : Type u) (TraceState : Type v) :=
  WordReturnedFrameCompletion RollbackState TraceState

variable (context : Context RollbackState TraceState)
variable (word : Core.Word) (store : Core.Store)
variable (value : Core.Value) (state : Core.State)
variable (error : Core.MachineFault)

example :
    (HostDriverResult.mk context
      (.done (.word word) store)).toWordReturnedFrameCompletion? =
      some ⟨context, word, store⟩ :=
  HostDriverResult.toWordReturnedFrameCompletion?_done_word
    context word store

example :
    (HostDriverResult.mk context
      (.done value store)).toWordReturnedFrameCompletion? = none ↔
      ∀ candidate, value ≠ .word candidate :=
  HostDriverResult.toWordReturnedFrameCompletion?_done_eq_none_iff
    context value store

example :
    (HostDriverResult.mk context
      (.outOfFuel state)).toWordReturnedFrameCompletion? = none :=
  HostDriverResult.toWordReturnedFrameCompletion?_outOfFuel context state

example :
    (HostDriverResult.mk context
      (.fault error state)).toWordReturnedFrameCompletion? = none :=
  HostDriverResult.toWordReturnedFrameCompletion?_fault
    context error state

variable (result : HostDriverResult (Context RollbackState TraceState))
variable (completion : Completion RollbackState TraceState)

example : (WordReturnedFrameCompletion.mk context word store).context =
    context :=
  WordReturnedFrameCompletion.mk_context context word store

example : (WordReturnedFrameCompletion.mk context word store).word = word :=
  WordReturnedFrameCompletion.mk_word context word store

example : (WordReturnedFrameCompletion.mk context word store).store = store :=
  WordReturnedFrameCompletion.mk_store context word store

example : result.toWordReturnedFrameCompletion? = some completion ↔
    result = completion.toHostDriverResult :=
  HostDriverResult.toWordReturnedFrameCompletion?_eq_some_iff
    result completion

example : completion.toHostDriverResult.toWordReturnedFrameCompletion? =
    some completion :=
  WordReturnedFrameCompletion.toWordReturnedFrameCompletion?_toHostDriverResult
    completion

example : completion.returnData.size = 32 :=
  WordReturnedFrameCompletion.returnData_size completion

example : decodeWordBytesBE? completion.returnData = some completion.word :=
  WordReturnedFrameCompletion.decodeWordBytesBE?_returnData completion

example :
    (completion.toFrameContinuationContext :
      FrameContinuationContext RollbackState TraceState TrapReason).stateCheckpoint =
      completion.context.context.values.checkpoint.state :=
  WordReturnedFrameCompletion.stateCheckpoint_toFrameContinuationContext
    completion

example :
    (completion.toFrameContinuationContext :
      FrameContinuationContext RollbackState TraceState TrapReason).effectCheckpoint =
      completion.context.context.values.checkpoint.effects :=
  WordReturnedFrameCompletion.effectCheckpoint_toFrameContinuationContext
    completion

example :
    (completion.toFrameContinuationContext :
      FrameContinuationContext RollbackState TraceState TrapReason).effectWorking =
      completion.context.context.values.working.2 :=
  WordReturnedFrameCompletion.effectWorking_toFrameContinuationContext
    completion

example :
    (completion.toFrameContinuationContext :
      FrameContinuationContext RollbackState TraceState TrapReason).result =
      ⟨completion.context.context.values.working.1,
        .returned completion.returnData⟩ :=
  WordReturnedFrameCompletion.result_toFrameContinuationContext completion

example :
    (completion.toFrameContinuationContext :
      FrameContinuationContext RollbackState TraceState TrapReason).resolve =
      .returned completion.context.context.values.working.1
        completion.context.context.values.working.2 completion.returnData :=
  WordReturnedFrameCompletion.resolve_toFrameContinuationContext completion

variable (leftStore rightStore : Core.Store)

example :
    ((⟨context, word, leftStore⟩ :
        Completion RollbackState TraceState).toFrameContinuationContext :
      FrameContinuationContext RollbackState TraceState TrapReason) =
    ((⟨context, word, rightStore⟩ :
        Completion RollbackState TraceState).toFrameContinuationContext :
      FrameContinuationContext RollbackState TraceState TrapReason) :=
  WordReturnedFrameCompletion.toFrameContinuationContext_store_independent
    context word leftStore rightStore

variable {definitions : Core.DataEnvironment}
variable (typing : result.outcome.HasType .word definitions)

example : result.toWordReturnedFrameCompletion? = none ↔
    (∃ finalContext exhausted,
      result = ⟨finalContext, .outOfFuel exhausted⟩) ∨
    ∃ finalContext suspension remainingFuel,
      result = ⟨finalContext, .unsupported suspension remainingFuel⟩ :=
  HostDriverResult.toWordReturnedFrameCompletion?_eq_none_iff_of_hasType
    result typing

variable (handler : HostHandler (Context RollbackState TraceState))
variable (additional : Nat)
variable (projected :
  result.toWordReturnedFrameCompletion? = some completion)

example : HostDriverResult.toWordReturnedFrameCompletion?
      (result.resumeWithFuel handler additional) = some completion :=
  HostDriverResult.toWordReturnedFrameCompletion?_resumeWithFuel_of_some
    result handler additional completion projected

variable (code : CheckedHostCoreWordProgram)
variable (inputs : HostStorageDriver.ExecutionInputs) (fuel : Nat)

example : (code.runWithStorage context inputs fuel).outcome.HasType
    .word code.code.program.dataDefinitions :=
  CheckedHostCoreWordProgram.runWithStorage_hasType
    code context inputs fuel

variable (faultState : Core.State)

example : (code.runWithStorage context inputs fuel).outcome ≠
    .fault error faultState :=
  CheckedHostCoreWordProgram.runWithStorage_ne_fault
    code context inputs fuel error faultState

variable (finalContext : Context RollbackState TraceState)

example : code.runWithStorage context inputs fuel ≠
    ⟨finalContext, .fault error faultState⟩ :=
  CheckedHostCoreWordProgram.runWithStorage_ne_fault_result
    code context finalContext inputs fuel error faultState

variable (execution : code.runWithStorage context inputs fuel =
  ⟨finalContext, .done value store⟩)

example : ∃ completedWord, value = .word completedWord :=
  CheckedHostCoreWordProgram.runWithStorage_done_word
    code context finalContext inputs execution

example :
    code.runWithStorageReturnedFrameCompletion? context inputs fuel =
        some completion ↔
      code.runWithStorage context inputs fuel =
        completion.toHostDriverResult :=
  CheckedHostCoreWordProgram.runWithStorageReturnedFrameCompletion?_eq_some_iff
    code context inputs fuel completion

example :
    code.runWithStorageReturnedFrameCompletion? context inputs fuel = none ↔
      (∃ retainedContext exhausted,
        code.runWithStorage context inputs fuel =
          ⟨retainedContext, .outOfFuel exhausted⟩) ∨
      ∃ retainedContext suspension remainingFuel,
        code.runWithStorage context inputs fuel =
          ⟨retainedContext,
            .unsupported suspension remainingFuel⟩ :=
  CheckedHostCoreWordProgram.runWithStorageReturnedFrameCompletion?_eq_none_iff
    code context inputs fuel

variable {completedFuel largerFuel : Nat}
variable (completed :
  code.runWithStorageReturnedFrameCompletion?
    context inputs completedFuel = some completion)
variable (more : completedFuel ≤ largerFuel)

example : code.runWithStorageReturnedFrameCompletion?
    context inputs largerFuel = some completion :=
  CheckedHostCoreWordProgram.runWithStorageReturnedFrameCompletion?_some_stable
    code context inputs completed more

example :
    (code.runWithStorage context inputs fuel).resumeWithFuel
        (@HostStorageDriver.handler RollbackState TraceState inputs)
        additional =
      code.runWithStorage context inputs (fuel + additional) :=
  CheckedHostCoreWordProgram.runWithStorage_resumeWithFuel
    code context inputs fuel additional

example :
    ((code.runWithStorage context inputs fuel).resumeWithFuel
        (@HostStorageDriver.handler RollbackState TraceState inputs)
        additional).toWordReturnedFrameCompletion? =
      code.runWithStorageReturnedFrameCompletion?
        context inputs (fuel + additional) :=
  CheckedHostCoreWordProgram.toWordReturnedFrameCompletion?_resumeWithFuel_runWithStorage
    code context inputs fuel additional

end Solcore.Test.WordReturnedFrameCompletionProperties
end

section
-- leanmerge: from Solcore.Test.WorldState
/-! Executable boundary tests for minimal accounts and word storage. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.ContractRuntime

private def addressA : Address := ⟨0, by decide⟩
private def addressB : Address := ⟨1, by decide⟩

private def keyA : Core.Word := ⟨0x11, by decide⟩
private def keyB : Core.Word := ⟨0x22, by decide⟩
private def valueA : Core.Word := ⟨0xaa, by decide⟩
private def valueB : Core.Word := ⟨0xbb, by decide⟩

private def accountB : Account :=
  Account.empty.storageWrite keyB valueB

private def stateWithB : WorldState :=
  WorldState.empty.putAccount addressB accountB

def testWorldState : IO Unit := do
  assertTrue (WorldState.empty.account? addressA).isNone
    "an empty world must report every address as absent"
  assertTrue
    (match (WorldState.empty.putAccount addressA Account.empty).account? addressA with
      | some account => account.storageValue? keyA == none
      | none => false)
    "putting an empty account must make its address explicitly present"
  assertTrue
    (match (stateWithB.putAccount addressA Account.empty).account? addressB with
      | some account => account.storageValue? keyB == some valueB
      | none => false)
    "putting one address must preserve the account at another address"
  assertTrue (Account.empty.storageValue? keyA == none)
    "an empty account must contain no semantic storage value"
  assertTrue (Account.empty.storageRead keyA == Core.Word.zero)
    "reading missing storage in an empty account must return zero"
  assertTrue
    ((Account.empty.storageWrite keyA valueA).storageRead keyA == valueA)
    "reading a nonzero value immediately after writing it must return that value"
  let deleted :=
    (Account.empty.storageWrite keyA valueA).storageWrite keyA Core.Word.zero
  assertTrue (deleted.storageValue? keyA == none)
    "writing zero must remove the selected semantic storage value"
  assertTrue
    ((Account.empty.storageWrite keyA valueA).storageValue? keyA == some valueA)
    "writing a nonzero value must create a semantic storage value"
  assertTrue
    ((accountB.storageWrite keyA valueA).storageRead keyB == valueB)
    "writing one storage key must preserve the value at another key"
  assertTrue (WorldState.empty.writeStorage? addressA keyA valueA).isNone
    "writing storage at an absent address must fail without creating an account"
  assertTrue
    (match (WorldState.empty.putAccount addressA Account.empty).writeStorage?
        addressA keyA valueA with
      | some updated =>
          match updated.account? addressA with
          | some account => account.storageValue? keyA == some valueA
          | none => false
      | none => false)
    "writing storage at a present address must update and preserve that account"
  assertTrue
    (match (stateWithB.putAccount addressA Account.empty).writeStorage?
        addressA keyA valueA with
      | some updated =>
          match updated.account? addressB with
          | some account => account.storageValue? keyB == some valueB
          | none => false
      | none => false)
    "writing storage at one address must preserve an account at another address"

end Tests
end

section
-- leanmerge: from Solcore.Test.WorldStateBalance
/-! Compile-time and executable regressions for account balances. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.ContractRuntime

example : Account.empty.balance = Core.Word.zero :=
  Account.balance_empty

example (account : Account) (balance : Core.Word) :
    (account.withBalance balance).balance = balance :=
  Account.balance_withBalance account balance

example (account : Account) (balance slot : Core.Word) :
    (account.withBalance balance).storageValue? slot =
      account.storageValue? slot :=
  Account.storageValue?_withBalance account balance slot

example (account : Account) (balance : Core.Word) :
    (account.withBalance balance).code? = account.code? :=
  Account.code?_withBalance account balance

example (account : Account) (code : CheckedHostCoreProgram) :
    (account.withCode code).balance = account.balance :=
  Account.balance_withCode account code

example (account : Account) (slot value : Core.Word) :
    (account.storageWrite slot value).balance = account.balance :=
  Account.balance_storageWrite account slot value

example (address : Address) :
    WorldState.empty.balance? address = none :=
  WorldState.balance?_empty address

example (state : WorldState) (address : Address) (account : Account) :
    (state.putAccount address account).balance? address =
      some account.balance :=
  WorldState.balance?_putAccount_same state address account

example (state : WorldState) (address other : Address) (account : Account)
    (different : other ≠ address) :
    (state.putAccount address account).balance? other =
      state.balance? other :=
  WorldState.balance?_putAccount_other state address other account different

example (state : WorldState) (address : Address) (balance : Core.Word)
    (absent : state.account? address = none) :
    state.writeBalance? address balance = none :=
  WorldState.writeBalance?_of_absent state address balance absent

example (state : WorldState) (address : Address) (account : Account)
    (balance : Core.Word) (present : state.account? address = some account) :
    state.writeBalance? address balance =
      some (state.putAccount address (account.withBalance balance)) :=
  WorldState.writeBalance?_of_present state address account balance present

example (state : WorldState) (address : Address) (account : Account)
    (balance : Core.Word) (present : state.account? address = some account) :
    (state.writeBalance? address balance).bind
        (fun next => next.balance? address) = some balance :=
  WorldState.balance?_writeBalance?_same state address account balance present

example (state : WorldState) (address other : Address) (account : Account)
    (balance : Core.Word) (present : state.account? address = some account)
    (different : other ≠ address) :
    (state.writeBalance? address balance).bind
        (fun next => next.account? other) = state.account? other :=
  WorldState.account?_writeBalance?_other state address other account balance
    present different

private def balanceA : Core.Word := ⟨17, by decide⟩

def testWorldStateBalance : IO Unit := do
  assertTrue (WorldState.empty.balance? addressA == none)
    "an absent account must not be reported as a zero-balance account"
  let present :=
    WorldState.empty.putAccount addressA
      (Account.empty.withBalance balanceA)
  assertTrue (present.balance? addressA == some balanceA)
    "a present account must expose its exact balance"
  assertTrue (present.writeBalance? addressB balanceA).isNone
    "writing balance must not create an absent account"
  assertTrue
    (match present.writeBalance? addressA Core.Word.zero with
      | some updated =>
          updated.balance? addressA == some Core.Word.zero &&
            (updated.account? addressB).isNone
      | none => false)
    "balance replacement must preserve presence and unrelated addresses"

end Tests
end

section
-- leanmerge: from Solcore.Test.WorldStateCode
/-! Runtime and direct-law regressions for address-selected host code. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.ContractRuntime

private def cellProgram : Program := {
  resultType := .cell .bool
  body := .newCell .bool (.bool true)
}

private def unitProgram : Program := {
  resultType := .unit
  body := .unit
}

private theorem cellProgram_checked : cellProgram.checkHost = true := by decide
private theorem unitProgram_checked : unitProgram.check = true := by decide

private def checkedCellProgram : CheckedHostCoreProgram :=
  ⟨cellProgram, cellProgram_checked⟩

private def checkedUnitProgram : CheckedHostCoreProgram :=
  (⟨unitProgram, unitProgram_checked⟩ : CheckedCoreProgram).toHost

private theorem compileTimePurePromotionRegression :
    checkedUnitProgram.program = unitProgram :=
  CheckedCoreProgram.toHost_program
    (⟨unitProgram, unitProgram_checked⟩ : CheckedCoreProgram)

private def slot : Word := ⟨0x11, by decide⟩
private def initialValue : Word := ⟨0xaa, by decide⟩
private def updatedValue : Word := ⟨0xbb, by decide⟩

private def accountA : Account :=
  (Account.empty.storageWrite slot initialValue).withCode checkedCellProgram

private def accountB_variant : Account :=
  Account.empty.withCode checkedUnitProgram

private def twoCodeAccounts : WorldState :=
  WorldState.empty
    |>.putAccount addressA accountA
    |>.putAccount addressB accountB_variant

private theorem compileTimeWithCodeStorageRegression
    (account : Account)
    (code : CheckedHostCoreProgram)
    (storedSlot : Word) :
    (account.withCode code).storageValue? storedSlot =
      account.storageValue? storedSlot :=
  Account.storageValue?_withCode account code storedSlot

private theorem compileTimeStoragePreservationRegression
    (account : Account)
    (code : CheckedHostCoreProgram)
    (writtenSlot value : Word) :
    ((account.withCode code).storageWrite writtenSlot value).code? = some code := by
  rw [Account.code?_storageWrite]
  exact Account.code?_withCode account code

private theorem compileTimeSelectionRegression
    (state : WorldState)
    (codeAddress : Address)
    (account : Account)
    (code : CheckedHostCoreProgram)
    (accountPresent : state.account? codeAddress = some account)
    (codePresent : account.code? = some code) :
    state.code? codeAddress = some code :=
  WorldState.code?_of_present state codeAddress account code
    accountPresent codePresent

private theorem compileTimeExecutionRegression
    (state : WorldState)
    (codeAddress : Address)
    (account : Account)
    (code : CheckedHostCoreProgram)
    (fuel : Nat)
    (accountPresent : state.account? codeAddress = some account)
    (codePresent : account.code? = some code) :
    state.runCode? codeAddress fuel = some (code.runStateful fuel) :=
  WorldState.runCode?_of_present state codeAddress account code fuel
    accountPresent codePresent

private theorem compileTimeWorldNoFaultRegression
    (state : WorldState)
    (codeAddress : Address)
    (fuel : Nat)
    (error : MachineFault)
    (faultState : State) :
    state.runCode? codeAddress fuel ≠ some (.fault error faultState) :=
  WorldState.runCode?_ne_some_fault state codeAddress fuel error faultState

def testWorldStateCode : IO Unit := do
  match Account.empty.code? with
  | none => pure ()
  | some _ => throw (IO.userError "an empty Account unexpectedly had code")
  match WorldState.empty.runCode? addressA 3 with
  | none => pure ()
  | some _ => throw (IO.userError "an absent Account unexpectedly executed")
  let withoutCode := WorldState.empty.putAccount addressA Account.empty
  match withoutCode.runCode? addressA 3 with
  | none => pure ()
  | some _ => throw (IO.userError "an Account without code unexpectedly executed")
  match twoCodeAccounts.code? addressA with
  | none => throw (IO.userError "address A did not select its checked code")
  | some code =>
      assertTrue (code.program == cellProgram)
        "address A selected code from another Account"
  assertTrue
    (twoCodeAccounts.runCode? addressA 3 ==
      some (.done (.cellRef .bool 0) [.bool true]))
    "address A must retain the stateful cell-program result"
  assertTrue
    (twoCodeAccounts.runCode? addressB 1 == some (.done .unit []))
    "address B must execute its own unit program"
  assertTrue (accountA.storageRead slot == initialValue)
    "associating checked code must preserve existing storage"
  match twoCodeAccounts.runCode? addressA 2 with
  | some (.outOfFuel _) => pure ()
  | result =>
      throw (IO.userError
        s!"selected insufficient-fuel execution changed class: {reprStr result}")
  let writtenAccount := accountA.storageWrite slot updatedValue
  assertTrue (writtenAccount.storageRead slot == updatedValue)
    "the storage write did not update the selected slot"
  match writtenAccount.code? with
  | none => throw (IO.userError "a storage write erased checked code")
  | some code =>
      assertTrue (code.program == cellProgram)
        "a storage write replaced checked code"
  let writtenWorld := twoCodeAccounts.putAccount addressA writtenAccount
  assertTrue
    (writtenWorld.runCode? addressA 3 ==
      some (.done (.cellRef .bool 0) [.bool true]))
    "a storage write changed selected checked-code execution"

end Tests
end

section
-- leanmerge: from Solcore.Test.WorldStateCodeWrite
/-! External and executable checks for checked-code replacement. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.ContractRuntime
open TopLevelExecutionFixture

example := WorldState.writeCode?_of_absent
example := WorldState.writeCode?_of_present
example := WorldState.account?_writeCode?_same
example := WorldState.code?_writeCode?_same
example := WorldState.account?_writeCode?_other
example := WorldState.writeCode?_preserves_payload

private def target : Address := ⟨0x148, by decide⟩
private def other : Address := ⟨0x149, by decide⟩
private def slot_variant : Core.Word := word 3
private def stored : Core.Word := word 9

private def targetAccount : Account :=
  Account.empty
    |>.withNonce (word 7)
    |>.withBalance (word 11)
    |>.storageWrite slot_variant stored

private def initialWorld : WorldState :=
  WorldState.empty
    |>.putAccount target targetAccount
    |>.putAccount other Account.empty

def testWorldStateCodeWrite : IO Unit := do
  assertTrue (WorldState.empty.writeCode? target contract.code).isNone
    "checked-code replacement must not create an absent Account"
  let updated ←
    match initialWorld.writeCode? target contract.code with
    | none => throw (IO.userError "present Account rejected code replacement")
    | some updated => pure updated
  let account ←
    match updated.account? target with
    | none => throw (IO.userError "code replacement removed its Account")
    | some account => pure account
  assertTrue
    (account.code?.map (fun code => code.program) == some contract.code.program)
    "code replacement did not install the requested checked program"
  assertTrue
    (account.balance == word 11 && account.nonce == word 7 &&
      account.storageValue? slot_variant == some stored)
    "code replacement changed balance, nonce, or storage"
  assertTrue ((updated.account? other).isSome)
    "code replacement changed an unrelated Account"

end Tests
end

section
-- leanmerge: from Solcore.Test.WorldStateDeltaBalanceProperties
/-! External consumers and runtime checks for balance delta observations. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.ContractRuntime

example := WorldStateDelta.balanceEndpoints_exact
example := WorldStateDelta.balanceEndpoints_identity
example := WorldStateDelta.balanceChange?_identity
example {initialWorld finalWorld : WorldState}
    (delta : WorldStateDelta initialWorld finalWorld)
    (address : Address) :
    delta.balanceChange? address = none ↔
      (delta.balanceEndpoints address).1 =
        (delta.balanceEndpoints address).2 :=
  WorldStateDelta.balanceChange?_eq_none_iff delta address

example {initialWorld finalWorld : WorldState}
    (delta : WorldStateDelta initialWorld finalWorld)
    (address : Address)
    (before after : Option Core.Word) :
    delta.balanceChange? address = some (before, after) ↔
      (delta.balanceEndpoints address).1 = before ∧
      (delta.balanceEndpoints address).2 = after ∧
      before ≠ after :=
  WorldStateDelta.balanceChange?_eq_some_iff delta address before after

private def untouched : Address := ⟨2, by decide⟩

private def initialWorld_variant : WorldState :=
  (WorldState.empty.putAccount sender
      (Account.empty.withBalance (word 10))).putAccount recipient
    (Account.empty.withBalance (word 3))

def testWorldStateDeltaBalance : IO Unit := do
  let next ←
    match initialWorld_variant.transferBalance sender recipient (word 4) with
    | .ok next => pure next
    | .error _ => throw (IO.userError "balance delta fixture transfer failed")
  let delta : WorldStateDelta initialWorld_variant next := .exact
  assertTrue
    (delta.balanceEndpoints sender ==
      (some (word 10), some (word 6)))
    "balance delta must expose the exact sender debit"
  assertTrue
    (delta.balanceChange? sender ==
      some (some (word 10), some (word 6)))
    "balance change must report a changed sender endpoint"
  assertTrue
    (delta.balanceEndpoints recipient ==
      (some (word 3), some (word 7)))
    "balance delta must expose the exact recipient credit"
  assertTrue
    (delta.balanceChange? untouched == none)
    "balance change must omit an untouched absent account"
  assertTrue
    ((WorldStateDelta.identity initialWorld_variant).balanceChange? sender == none)
    "identity delta must not report a balance change"

end Tests
end

section
-- leanmerge: from Solcore.Test.WorldStateDeltaCreationProperties
/-! External consumers and executable creation-delta checks. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.ContractRuntime
open TopLevelExecutionFixture

example := WorldStateDelta.nonceEndpoints_exact
example := WorldStateDelta.codeEndpoints_exact
example := WorldStateDelta.createdAccount?_exact
example := WorldStateDelta.nonceEndpoints_identity
example := WorldStateDelta.codeEndpoints_identity
example := WorldStateDelta.createdAccount?_identity
example := WorldStateDelta.nonceChange?_identity

example {initialWorld finalWorld : WorldState}
    (delta : WorldStateDelta initialWorld finalWorld)
    (address : Address) :
    delta.nonceChange? address = none ↔
      (delta.nonceEndpoints address).1 =
        (delta.nonceEndpoints address).2 :=
  WorldStateDelta.nonceChange?_eq_none_iff delta address

example {initialWorld finalWorld : WorldState}
    (delta : WorldStateDelta initialWorld finalWorld)
    (address : Address)
    (before after : Option Core.Word) :
    delta.nonceChange? address = some (before, after) ↔
      (delta.nonceEndpoints address).1 = before ∧
      (delta.nonceEndpoints address).2 = after ∧
      before ≠ after :=
  WorldStateDelta.nonceChange?_eq_some_iff delta address before after

private def creator : Address := ⟨0x148, by decide⟩
private def created : Address := ⟨0x149, by decide⟩
private def untouched_variant : Address := ⟨0x14a, by decide⟩
private def slot_variant2 : Core.Word := word 9
private def stored_variant : Core.Word := word 77

private def creatorAccount : Account :=
  Account.empty.withNonce (word 4) |>.withBalance (word 10)

private def initialWorld_variant2 : WorldState :=
  WorldState.empty.putAccount creator creatorAccount

private def finalWorld : WorldState :=
  initialWorld_variant2
    |>.putAccount creator (creatorAccount.withNonce (word 5))
    |>.putAccount created
      (Account.empty.withCode contract.code |>.storageWrite slot_variant2 stored_variant
        |>.withBalance (word 3))

private def delta : WorldStateDelta initialWorld_variant2 finalWorld := .exact

private def createdCodeProgramExact : Bool :=
  match (delta.codeEndpoints created).1, (delta.codeEndpoints created).2 with
  | none, some installed => installed.program == contract.code.program
  | _, _ => false

def testWorldStateDeltaCreation : IO Unit := do
  assertTrue
    (delta.nonceEndpoints creator == (some (word 4), some (word 5)))
    "creation delta must expose the consumed creator nonce"
  assertTrue
    (delta.nonceChange? creator ==
      some (some (word 4), some (word 5)))
    "creation delta must report the exact nonce change"
  assertTrue (delta.createdAccount? created)
    "creation delta must distinguish absent-to-present account creation"
  assertTrue (!delta.createdAccount? creator)
    "updating a present creator must not be reported as account creation"
  assertTrue (!delta.createdAccount? untouched_variant)
    "an untouched absent address must not be reported as created"
  assertTrue createdCodeProgramExact
    "creation delta must expose the installed checked runtime program"
  assertTrue
    (delta.balanceEndpoints created == (none, some (word 3)) &&
      delta.storageEndpoints created slot_variant2 == (none, some stored_variant))
    "existing delta queries must compose with created-account observations"
  let identity := WorldStateDelta.identity initialWorld_variant2
  assertTrue
    (identity.nonceChange? creator == none &&
      !identity.createdAccount? creator)
    "identity delta must report neither nonce change nor account creation"

end Tests
end

section
-- leanmerge: from Solcore.Test.WorldStateNonce
/-! Compile-time and executable regressions for account creation nonces. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.ContractRuntime

example : Account.empty.nonce = Core.Word.zero :=
  Account.nonce_empty

example (account : Account) (nonce : Core.Word) :
    (account.withNonce nonce).nonce = nonce :=
  Account.nonce_withNonce account nonce

example (account : Account) (nonce slot : Core.Word) :
    (account.withNonce nonce).storageValue? slot =
      account.storageValue? slot :=
  Account.storageValue?_withNonce account nonce slot

example (account : Account) (nonce : Core.Word) :
    (account.withNonce nonce).code? = account.code? :=
  Account.code?_withNonce account nonce

example (account : Account) (nonce : Core.Word) :
    (account.withNonce nonce).balance = account.balance :=
  Account.balance_withNonce account nonce

example (account : Account) (balance : Core.Word) :
    (account.withBalance balance).nonce = account.nonce :=
  Account.nonce_withBalance account balance

example (account : Account) (code : CheckedHostCoreProgram) :
    (account.withCode code).nonce = account.nonce :=
  Account.nonce_withCode account code

example (account : Account) (slot value : Core.Word) :
    (account.storageWrite slot value).nonce = account.nonce :=
  Account.nonce_storageWrite account slot value

example (address : Address) :
    WorldState.empty.nonce? address = none :=
  WorldState.nonce?_empty address

example (state : WorldState) (address : Address) (account : Account) :
    (state.putAccount address account).nonce? address =
      some account.nonce :=
  WorldState.nonce?_putAccount_same state address account

example (state : WorldState) (address other : Address) (account : Account)
    (different : other ≠ address) :
    (state.putAccount address account).nonce? other = state.nonce? other :=
  WorldState.nonce?_putAccount_other state address other account different

example (state : WorldState) (address : Address) (nonce : Core.Word)
    (absent : state.account? address = none) :
    state.writeNonce? address nonce = none :=
  WorldState.writeNonce?_of_absent state address nonce absent

example (state : WorldState) (address : Address) (account : Account)
    (nonce : Core.Word) (present : state.account? address = some account) :
    state.writeNonce? address nonce =
      some (state.putAccount address (account.withNonce nonce)) :=
  WorldState.writeNonce?_of_present state address account nonce present

example (state : WorldState) (address : Address) (account : Account)
    (nonce : Core.Word) (present : state.account? address = some account) :
    (state.writeNonce? address nonce).bind
        (fun next => next.account? address) =
      some (account.withNonce nonce) :=
  WorldState.account?_writeNonce?_same state address account nonce present

example (state : WorldState) (address : Address) (account : Account)
    (nonce : Core.Word) (present : state.account? address = some account) :
    (state.writeNonce? address nonce).bind
        (fun next => next.nonce? address) = some nonce :=
  WorldState.nonce?_writeNonce?_same state address account nonce present

example (state : WorldState) (address other : Address) (account : Account)
    (nonce : Core.Word) (present : state.account? address = some account)
    (different : other ≠ address) :
    (state.writeNonce? address nonce).bind
        (fun next => next.account? other) = state.account? other :=
  WorldState.account?_writeNonce?_other state address other account nonce
    present different

example (state : WorldState) (address : Address) (account : Account)
    (nonce : Core.Word) (present : state.account? address = some account) :
    (state.writeNonce? address nonce).bind (fun next =>
        (next.account? address).map fun updated =>
          (updated.code?, updated.balance,
            fun slot => updated.storageValue? slot)) =
      some (account.code?, account.balance,
        fun slot => account.storageValue? slot) :=
  WorldState.writeNonce?_preserves_payload state address account nonce present

private def nonceA : Core.Word := ⟨23, by decide⟩
private def balanceA_variant : Core.Word := ⟨41, by decide⟩
private def slotA : Core.Word := ⟨7, by decide⟩
private def storedA : Core.Word := ⟨99, by decide⟩
private def otherNonce : Core.Word := ⟨5, by decide⟩

def testWorldStateNonce : IO Unit := do
  assertTrue (Account.empty.nonce == Core.Word.zero)
    "an empty present account must start with nonce zero"
  assertTrue (WorldState.empty.nonce? addressA == none)
    "an absent account must not be reported as a zero-nonce account"
  assertTrue (WorldState.empty.writeNonce? addressA nonceA).isNone
    "writing nonce must not create an absent account"
  let account :=
    (Account.empty.storageWrite slotA storedA).withBalance balanceA_variant
  let world :=
    (WorldState.empty.putAccount addressA account).putAccount addressB
      (Account.empty.withNonce otherNonce)
  assertTrue (world.nonce? addressA == some Core.Word.zero)
    "a present account must expose its initial zero nonce"
  assertTrue
    (match world.writeNonce? addressA nonceA with
      | none => false
      | some updated =>
          match updated.account? addressA with
          | none => false
          | some changed =>
              changed.nonce == nonceA &&
                changed.balance == balanceA_variant &&
                changed.storageValue? slotA == some storedA &&
                changed.code?.isNone &&
                updated.nonce? addressB == some otherNonce)
    "nonce replacement must preserve presence, payload, and other accounts"
  assertTrue
    (match world.writeNonce? addressA Core.Word.zero with
      | none => false
      | some updated => updated.account? addressA |>.isSome)
    "writing nonce zero must preserve explicit account presence"

end Tests
end

section
-- leanmerge: from Solcore.Test.WorldStateStorageRead
/-! Runtime regressions for conditional WorldState storage reads. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.ContractRuntime

private def addressA_variant : Address := ⟨0x31, by decide⟩
private def addressB_variant : Address := ⟨0x52, by decide⟩
private def slotA_variant : Core.Word := ⟨0x73, by decide⟩
private def slotB : Core.Word := ⟨0x94, by decide⟩
private def valueA_variant : Core.Word := ⟨0xb5, by decide⟩
private def valueB_variant : Core.Word := ⟨0xd6, by decide⟩
private def otherSlotValue : Core.Word := ⟨0xf7, by decide⟩

private def accountA_variant : Account :=
  Account.empty
    |>.storageWrite slotA_variant valueA_variant
    |>.storageWrite slotB otherSlotValue

private def accountB_variant2 : Account :=
  Account.empty.storageWrite slotA_variant valueB_variant

private def stateWithB_variant : WorldState :=
  WorldState.empty.putAccount addressB_variant accountB_variant2

private def stateWithEmptyA : WorldState :=
  stateWithB_variant.putAccount addressA_variant Account.empty

private def stateWithBoth : WorldState :=
  stateWithB_variant.putAccount addressA_variant accountA_variant

def testWorldStateStorageRead : IO Unit := do
  assertTrue
    ((stateWithB_variant.readStorage? addressA_variant slotA_variant).isNone &&
      stateWithB_variant.readStorage? addressB_variant slotA_variant == some valueB_variant)
    "an unrelated present Account must not rescue an absent read target"
  assertTrue
    (stateWithEmptyA.readStorage? addressA_variant slotA_variant == some Core.Word.zero &&
      stateWithEmptyA.readStorage? addressB_variant slotA_variant == some valueB_variant)
    "a missing slot in a present Account must read as an available zero"
  assertTrue
    (stateWithBoth.readStorage? addressA_variant slotA_variant == some valueA_variant &&
      stateWithBoth.readStorage? addressA_variant slotB == some otherSlotValue &&
      stateWithBoth.readStorage? addressB_variant slotA_variant == some valueB_variant)
    "a stored read must select the exact address and slot"

end Tests
end

section
-- leanmerge: from Solcore.Test.WorldStateStorageReadWrite
/-! Compile-only regressions for stage-preserving storage read/write laws. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.ContractRuntime

private example
    (state : WorldState) (address : Address)
    (slot value : Core.Word) :
    (state.writeStorage? address slot value).map
        (fun next => next.readStorage? address slot) =
      (state.account? address).map (fun _ => some value) := by
  simp

private example
    (state : WorldState) (address : Address)
    (writtenSlot value readSlot : Core.Word)
    (different : readSlot ≠ writtenSlot) :
    (state.writeStorage? address writtenSlot value).map
        (fun next => next.readStorage? address readSlot) =
      (state.account? address).map
        (fun _ => state.readStorage? address readSlot) := by
  simp [different]

private example
    (state : WorldState)
    (writtenAddress readAddress : Address)
    (writtenSlot value readSlot : Core.Word)
    (different : readAddress ≠ writtenAddress) :
    (state.writeStorage? writtenAddress writtenSlot value).map
        (fun next => next.readStorage? readAddress readSlot) =
      (state.account? writtenAddress).map
        (fun _ => state.readStorage? readAddress readSlot) := by
  simp [different]

end Tests
end

section
-- leanmerge: from Solcore.Test.WorldStateStorageWriteAlgebra
/-! Executable composition tests for partial WorldState storage writes. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.ContractRuntime

private def slotA_variant2 : Core.Word := ⟨0x11, by decide⟩
private def slotB_variant : Core.Word := ⟨0x22, by decide⟩
private def replacement : Core.Word := ⟨0xcc, by decide⟩

private def writeThen?
    (state : WorldState)
    (firstAddress : Address) (firstSlot firstValue : Core.Word)
    (secondAddress : Address) (secondSlot secondValue : Core.Word) :
    Option WorldState := do
  let next ← state.writeStorage? firstAddress firstSlot firstValue
  next.writeStorage? secondAddress secondSlot secondValue

private def observedValue?
    (state? : Option WorldState) (address : Address) (slot : Core.Word) :
    Option Core.Word := do
  let state ← state?
  let account ← state.account? address
  account.storageValue? slot

private def accountWithOtherSlot : Account :=
  Account.empty.storageWrite slotA_variant2 valueA |>.storageWrite slotB_variant valueB

private def presentA : WorldState :=
  WorldState.empty.putAccount addressA accountWithOtherSlot

def testWorldStateStorageWriteAlgebra : IO Unit := do
  let overwritten :=
    writeThen? presentA addressA slotA_variant2 valueA addressA slotA_variant2 replacement
  let absentSequence :=
    writeThen? WorldState.empty addressA slotA_variant2 valueA addressA slotA_variant2 replacement
  assertTrue
    (observedValue? overwritten addressA slotA_variant2 == some replacement &&
      absentSequence.isNone &&
      (WorldState.empty.writeStorage? addressA slotA_variant2 replacement).isNone)
    "same-slot writes must keep the last value when present and fail when absent"
  let oneAccount := WorldState.empty.putAccount addressA Account.empty
  let slotsLeft :=
    writeThen? oneAccount addressA slotA_variant2 valueA addressA slotB_variant valueB
  let slotsRight :=
    writeThen? oneAccount addressA slotB_variant valueB addressA slotA_variant2 valueA
  assertTrue
    (observedValue? slotsLeft addressA slotA_variant2 == some valueA &&
      observedValue? slotsLeft addressA slotB_variant == some valueB &&
      observedValue? slotsRight addressA slotA_variant2 == some valueA &&
      observedValue? slotsRight addressA slotB_variant == some valueB)
    "writes to distinct slots at one address must agree in both orders"
  let bothAccounts := oneAccount.putAccount addressB Account.empty
  let addressesLeft :=
    writeThen? bothAccounts addressA slotA_variant2 valueA addressB slotB_variant valueB
  let addressesRight :=
    writeThen? bothAccounts addressB slotB_variant valueB addressA slotA_variant2 valueA
  let missingLeft :=
    writeThen? oneAccount addressA slotA_variant2 valueA addressB slotB_variant valueB
  let missingRight :=
    writeThen? oneAccount addressB slotB_variant valueB addressA slotA_variant2 valueA
  assertTrue
    (observedValue? addressesLeft addressA slotA_variant2 == some valueA &&
      observedValue? addressesLeft addressB slotB_variant == some valueB &&
      observedValue? addressesRight addressA slotA_variant2 == some valueA &&
      observedValue? addressesRight addressB slotB_variant == some valueB &&
      missingLeft.isNone && missingRight.isNone)
    "distinct-address writes must commute when present and fail if one is absent"
  assertTrue
    (match presentA.writeStorage? addressA slotA_variant2 Core.Word.zero with
      | some updated =>
          match updated.account? addressA with
          | some account =>
              account.storageValue? slotA_variant2 == none &&
              account.storageRead slotA_variant2 == Core.Word.zero &&
              account.storageValue? slotB_variant == some valueB
          | none => false
      | none => false)
    "a successful zero write must delete only its slot and keep the Account present"

end Tests
end

section
-- leanmerge: from Solcore.Test.WorldStateUpdateAlgebra
/-! Compile-time and executable regressions for WorldState update algebra. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.ContractRuntime

private theorem compileTimeExtRegression_account
    {left right : Account}
    (sameStorage : ∀ slot,
      left.storageValue? slot = right.storageValue? slot)
    (sameCode : left.code? = right.code?)
    (sameBalance : left.balance = right.balance)
    (sameNonce : left.nonce = right.nonce) :
    left = right :=
  Account.ext sameStorage sameCode sameBalance sameNonce

private theorem compileTimeExtRegression_worldState
    {left right : WorldState}
    (same : ∀ address, left.account? address = right.account? address) :
    left = right :=
  WorldState.ext same

private def accountA_variant2 : Account :=
  Account.empty.storageWrite slotA_variant2 valueA

private def accountB_variant3 : Account :=
  Account.empty.storageWrite slotB_variant valueB

private def worldValue?
    (state : WorldState) (address : Address) (slot : Core.Word) :
    Option Core.Word := do
  let account ← state.account? address
  account.storageValue? slot

def testWorldStateUpdateAlgebra : IO Unit := do
  let overwrittenAccount := accountA_variant2.storageWrite slotA_variant2 valueB
  assertTrue (overwrittenAccount.storageValue? slotA_variant2 == some valueB)
    "the last Account write to one slot must replace the earlier value"
  let accountLeftFirst := accountA_variant2.storageWrite slotB_variant valueB
  let accountRightFirst := accountB_variant3.storageWrite slotA_variant2 valueA
  assertTrue
    (accountLeftFirst.storageValue? slotA_variant2 == some valueA &&
      accountLeftFirst.storageValue? slotB_variant == some valueB &&
      accountRightFirst.storageValue? slotA_variant2 == some valueA &&
      accountRightFirst.storageValue? slotB_variant == some valueB)
    "Account writes to distinct slots must commute under public lookup"
  let overwrittenWorld :=
    (WorldState.empty.putAccount addressA accountA_variant2).putAccount addressA accountB_variant3
  assertTrue
    (worldValue? overwrittenWorld addressA slotA_variant2 == none &&
      worldValue? overwrittenWorld addressA slotB_variant == some valueB)
    "the last WorldState put at one address must replace the earlier Account"
  let worldLeftFirst :=
    (WorldState.empty.putAccount addressA accountA_variant2).putAccount addressB accountB_variant3
  let worldRightFirst :=
    (WorldState.empty.putAccount addressB accountB_variant3).putAccount addressA accountA_variant2
  assertTrue
    (worldValue? worldLeftFirst addressA slotA_variant2 == some valueA &&
      worldValue? worldLeftFirst addressB slotB_variant == some valueB &&
      worldValue? worldRightFirst addressA slotA_variant2 == some valueA &&
      worldValue? worldRightFirst addressB slotB_variant == some valueB)
    "WorldState puts at distinct addresses must commute under public lookup"

end Tests
end
