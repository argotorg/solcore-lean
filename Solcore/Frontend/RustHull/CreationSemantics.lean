import Solcore.Frontend.RustHull.RuntimeCallEffectsSemantics

/-! CREATE and CREATE2 attempts that are refused before any init code runs.
The rules follow the EVM checks: a static frame or init code longer than
EIP-3860's 49,152 bytes halts the frame exceptionally; the depth limit, an
insufficient endowment and EIP-2681's 2^64 − 1 nonce limit make the attempt
return zero. Refusals never advance the creator nonce; only admitted attempts
do. Successful creation is not described here, so the source semantics has no
derivation for an admitted attempt. -/
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

end Solcore.Frontend.RustHull.CreationSemantics
