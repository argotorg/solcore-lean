import Solcore.Frontend.RustHull.RuntimeCallEffectsSemantics
import Solcore.Frontend.RustHull.CreationAddressSemantics

/-! CREATE and CREATE2 attempts. The refusal rules follow the EVM checks: a
static frame or init code longer than EIP-3860's 49,152 bytes halts the frame
exceptionally; the depth limit, an insufficient endowment and EIP-2681's
2^64 − 1 nonce limit make the attempt return zero. Refusals never advance the
creator nonce; admitted attempts do, before the new address is examined. The
admitted rules cover collisions, deployments of empty init code and the two
faults after the nonce advance; init frames are not described here. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.CreationSemantics
open Core

abbrev State := RuntimeCallEffectsSemantics.State

/-- EIP-3860: init code is at most twice the 24,576-byte EIP-170 code limit. -/
def maxInitCodeSize : Nat := 2 * 24576
/-- The outermost frame has depth zero; a frame at this depth cannot create. -/
def depthLimit : Nat := 1024
/-- EIP-2681: an account nonce cannot advance past 2^64 − 1. -/
def maxNonce : Nat := 2 ^ 64 - 1

def frame (state : State) : RuntimeEffectsSemantics.State :=
  state.runtime.runtime.runtime.runtime.runtime

/-- Forwarded gas is an explicit observation; none is supplied by default. -/
def availableGas (state : State) : Option Word :=
  state.runtime.runtime.runtime.runtime.environment.gas

/-- The creating account: the executing address as a 160-bit address. -/
def creator (state : State) : Word :=
  (frame state).storage.address.bitAnd (Word.ofNatModulo (2 ^ 160 - 1))

def creatorBalance (state : State) : Word :=
  StorageSemantics.readWord (creator state) state.runtime.runtime.balances

/-- After a refused attempt the creator's memory covers the init range and its
return data is empty. Balances, accounts, nonces and logs are unchanged. -/
def refused (state : State) (size : Word) : State :=
  RuntimeCallEffectsSemantics.withReturned state {(frame state).memory with size := size} [] Word.zero

/-- The checks run in this order. A static frame or oversized init code
halts the frame exceptionally. The EVM charges memory expansion first, but the
halt discards the frame, so these rules leave memory unchanged, as the static
guards of SSTORE and LOG do. Without a gas observation the attempt is a
language fault. An unaddressable init range is a memory fault that keeps the
previous return data. The remaining refusals expand memory over the init
range, clear return data and return zero. -/
inductive Refused (value offset length : Word) : State → Semantics.Result Semantics.Value → State → Prop where
  | staticFrame (state : State) (isStatic : (frame state).storage.isStatic = true) :
      Refused value offset length state
        (RuntimeCallEffectsSemantics.invalid state).1 (RuntimeCallEffectsSemantics.invalid state).2
  | oversized (state : State) (notStatic : (frame state).storage.isStatic = false)
      (oversized : maxInitCodeSize < length.val) :
      Refused value offset length state
        (RuntimeCallEffectsSemantics.invalid state).1 (RuntimeCallEffectsSemantics.invalid state).2
  | missingGas (state : State) (notStatic : (frame state).storage.isStatic = false)
      (bounded : length.val ≤ maxInitCodeSize) (missing : availableGas state = none) :
      Refused value offset length state (.fault (.language (Word.ofNatModulo 9))) state
  | inputOverflow (state : State) {gas : Word} (notStatic : (frame state).storage.isStatic = false)
      (bounded : length.val ≤ maxInitCodeSize) (available : availableGas state = some gas)
      (invalid : MemorySemantics.touchSize? (frame state).memory.size offset length = none) :
      Refused value offset length state MemorySemantics.overflow state
  | depthExceeded {state : State} {gas size : Word} (notStatic : (frame state).storage.isStatic = false)
      (bounded : length.val ≤ maxInitCodeSize) (available : availableGas state = some gas)
      (touched : MemorySemantics.touchSize? (frame state).memory.size offset length = some size)
      (exceeded : depthLimit ≤ state.callDepth.val) :
      Refused value offset length state (.value (.word Word.zero)) (refused state size)
  | underfunded {state : State} {gas size : Word} (notStatic : (frame state).storage.isStatic = false)
      (bounded : length.val ≤ maxInitCodeSize) (available : availableGas state = some gas)
      (touched : MemorySemantics.touchSize? (frame state).memory.size offset length = some size)
      (allowed : state.callDepth.val < depthLimit)
      (shortfall : (creatorBalance state).val < value.val) :
      Refused value offset length state (.value (.word Word.zero)) (refused state size)
  | nonceExhausted {state : State} {gas size : Word} {account : AccountState.Account}
      (notStatic : (frame state).storage.isStatic = false)
      (bounded : length.val ≤ maxInitCodeSize) (available : availableGas state = some gas)
      (touched : MemorySemantics.touchSize? (frame state).memory.size offset length = some size)
      (allowed : state.callDepth.val < depthLimit)
      (funded : value.val ≤ (creatorBalance state).val)
      (found : StorageSemantics.get (frame state).storage.world (creator state)
        (frame state).storage.complete = .ok account)
      (exhausted : maxNonce ≤ account.nonce.val) :
      Refused value offset length state (.value (.word Word.zero)) (refused state size)

/-- The checks an admitted attempt passes, in the order of the refusals. -/
structure Admission (value offset length : Word) (state : State) (size : Word)
    (account : AccountState.Account) : Prop where
  notStatic : (frame state).storage.isStatic = false
  bounded : length.val ≤ maxInitCodeSize
  available : ∃ gas, availableGas state = some gas
  touched : MemorySemantics.touchSize? (frame state).memory.size offset length = some size
  allowed : state.callDepth.val < depthLimit
  funded : value.val ≤ (creatorBalance state).val
  found : StorageSemantics.get (frame state).storage.world (creator state) (frame state).storage.complete = .ok account
  belowLimit : account.nonce.val < maxNonce

/-- The creator nonce advances before the new address is examined. The advance
survives every later outcome of the attempt. -/
def advanced (state : State) (account : AccountState.Account) : State :=
  let shared := RuntimeCallEffectsSemantics.shared state
  RuntimeCallEffectsSemantics.withShared state {shared with
    world := StorageSemantics.put (creator state)
      {account with nonce := account.nonce.add (Word.ofNatModulo 1)} shared.world}

/-- A new account has nonce one, empty code and storage, and is marked as
created in this transaction. -/
def createdAccount (target : Word) : AccountState.Account :=
  {address := target, nonce := Word.ofNatModulo 1, created := true}

/-- After a deployment the new account exists and holds the endowment. Memory
covers the init range and return data is empty. -/
def deployed (state : State) (target : Word) (balances : StorageSemantics.Words) (size : Word) : State :=
  let shared := RuntimeCallEffectsSemantics.shared state
  RuntimeCallEffectsSemantics.withReturned
    (RuntimeCallEffectsSemantics.withShared state {shared with
      world := StorageSemantics.put target (createdAccount target) shared.world, balances := balances})
    {(frame state).memory with size := size} [] Word.zero

/-- A target account that the world does not determine: absent from an
incomplete world, or recorded with a zero nonce and unknown code. -/
inductive Unknown (world : StorageSemantics.World) (target : Word) (complete : Bool) : Prop where
  | absent (absent : StorageSemantics.lookup target world = none) (incomplete : complete = false)
  | unknownCode {existing : AccountState.Account}
      (found : StorageSemantics.lookup target world = some existing)
      (zero : existing.nonce = Word.zero) (unknown : existing.code = none)

/-- An admitted attempt copies its init bytes from memory, advances the
creator nonce and derives the new address. Following EIP-684, an account with
a nonzero nonce or code size at that address is a collision: the attempt
returns zero and keeps the advanced nonce. An address absent from a complete
world receives a new account and the endowment; with empty init code no init
frame runs, the deployed code is empty and the attempt returns the address.
An unknown account at the address is language fault 7, and an endowment that
overflows the new account's balance is language fault 12. Both faults restore
the checkpoint taken after the nonce advance: only the advanced nonce remains,
and memory and return data are as for a refusal. Nonempty init code and an
existing account with a zero nonce and known empty code at the address are not
described here. -/
inductive Admitted (scheme : CreationAddressSemantics.Scheme) (value offset length : Word) :
    State → Semantics.Result Semantics.Value → State → Prop where
  | collision {state : State} {size target : Word} {account existing : AccountState.Account}
      {initCode : MemorySemantics.Entries}
      (admitted : Admission value offset length state size account)
      (copied : MemoryCopySemantics.Copy (frame state).memory.words Word.zero offset length [] initCode)
      (derived : CreationAddressSemantics.Derived (creator state) account.nonce initCode length scheme target)
      (occupied : StorageSemantics.lookup target (frame (advanced state account)).storage.world = some existing)
      (used : existing.nonce ≠ Word.zero ∨
        AccountObservationSemantics.codeSize (existing.code.getD []) ≠ Word.zero) :
      Admitted scheme value offset length state (.value (.word Word.zero)) (refused (advanced state account) size)
  | deployed {state : State} {size target : Word} {account : AccountState.Account}
      {initCode : MemorySemantics.Entries} {balances : StorageSemantics.Words}
      (admitted : Admission value offset length state size account)
      (copied : MemoryCopySemantics.Copy (frame state).memory.words Word.zero offset length [] initCode)
      (derived : CreationAddressSemantics.Derived (creator state) account.nonce initCode length scheme target)
      (absent : StorageSemantics.lookup target (frame (advanced state account)).storage.world = none)
      (complete : (frame state).storage.complete = true)
      (emptyInit : length = Word.zero)
      (transferred : AccountCallSemantics.transfer (creator state) target value
        (RuntimeCallEffectsSemantics.shared state).balances = .ok balances) :
      Admitted scheme value offset length state (.value (.word target))
        (deployed (advanced state account) target balances size)
  | unknown {state : State} {size target : Word} {account : AccountState.Account}
      {initCode : MemorySemantics.Entries}
      (admitted : Admission value offset length state size account)
      (copied : MemoryCopySemantics.Copy (frame state).memory.words Word.zero offset length [] initCode)
      (derived : CreationAddressSemantics.Derived (creator state) account.nonce initCode length scheme target)
      (unknown : Unknown (frame (advanced state account)).storage.world target (frame state).storage.complete) :
      Admitted scheme value offset length state (.fault (.language (Word.ofNatModulo 7)))
        (refused (advanced state account) size)
  | overflow {state : State} {size target : Word} {account : AccountState.Account}
      {initCode : MemorySemantics.Entries}
      (admitted : Admission value offset length state size account)
      (copied : MemoryCopySemantics.Copy (frame state).memory.words Word.zero offset length [] initCode)
      (derived : CreationAddressSemantics.Derived (creator state) account.nonce initCode length scheme target)
      (absent : StorageSemantics.lookup target (frame (advanced state account)).storage.world = none)
      (complete : (frame state).storage.complete = true)
      (overflowed : AccountCallSemantics.transfer (creator state) target value
        (RuntimeCallEffectsSemantics.shared state).balances = .error (Word.ofNatModulo 12)) :
      Admitted scheme value offset length state (.fault (.language (Word.ofNatModulo 12)))
        (refused (advanced state account) size)

end Solcore.Frontend.RustHull.CreationSemantics
