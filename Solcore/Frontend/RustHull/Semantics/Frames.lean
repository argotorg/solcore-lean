import Solcore.Frontend.RustHull.Semantics.Memory
import Solcore.Frontend.RustHull.Semantics.Layers
import Solcore.Frontend.RustHull.Semantics.Accounts
import Solcore.Frontend.RustHull.Semantics.Digests
import Solcore.Frontend.RustHull.Semantics.World
import Solcore.Frontend.RustHull.Lowering

/-!
# Hull frames, creation and inline Yul

Child frames over a code catalog, call modes, refused and admitted creation, revert and inline Yul.
Main declarations: `RuntimeCallModeSemantics.State`, `RuntimeCallModeSemantics.Operation`,
`ChildFrameSemantics.Catalog`, `ChildFrameModeSemantics.Children`, `CreationSemantics`,
`YulSemantics`.
-/

section
-- leanmerge: from Solcore.Frontend.RustHull.ChildResultSemantics
/-! A completed child frame supplies its complete return or revert bytes.
Exceptional exits return false with empty data; ordinary language faults remain
faults for the enclosing account checkpoint. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ChildResultSemantics
open Core

def response (success : Bool) (size : Word) : Semantics.Result MemorySemantics.Entries → Semantics.Result AccountCallSemantics.Response
  | .value entries => .value ⟨success, entries, size⟩
  | .fault fault => .fault fault

inductive Respond (status : Semantics.Result Semantics.Value) (state : RuntimeEffectsSemantics.State) :
    Semantics.Result AccountCallSemantics.Response → Prop where
  | invalid (exit : state.storage.exit = Word.ofNatModulo 3) :
      Respond status state (.value (AccountCallSemantics.emptyResponse false))
  | reverted {data : Semantics.Result MemorySemantics.Entries}
      (exit : state.storage.exit = Word.ofNatModulo 2)
      (extracted : MemorySnapshotSemantics.Extract state.memory.words state.storage.returnOffset state.storage.returnSize data) :
      Respond status state (response false state.storage.returnSize data)
  | returned {data : Semantics.Result MemorySemantics.Entries}
      (exit : state.storage.exit = Word.ofNatModulo 1)
      (extracted : MemorySnapshotSemantics.Extract state.memory.words state.storage.returnOffset state.storage.returnSize data) :
      Respond status state (response true state.storage.returnSize data)
  | failed {fault : Semantics.Fault}
      (invalid : state.storage.exit ≠ Word.ofNatModulo 3)
      (reverted : state.storage.exit ≠ Word.ofNatModulo 2)
      (returned : state.storage.exit ≠ Word.ofNatModulo 1)
      (failed : status = .fault fault) : Respond status state (.fault fault)
  | completed
      (invalid : state.storage.exit ≠ Word.ofNatModulo 3)
      (reverted : state.storage.exit ≠ Word.ofNatModulo 2)
      (returned : state.storage.exit ≠ Word.ofNatModulo 1)
      (finished : status = .value .unit) :
      Respond status state (.value (AccountCallSemantics.emptyResponse true))

end Solcore.Frontend.RustHull.ChildResultSemantics
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ChildFrameSemantics
/-! Independent execution of linked Hull child frames. The catalog identifies
source code by execution address; a separate representation proof must link
that entry to the executable identity stored by the actual runtime.

Children receive the transferred shared state and a fresh local frame. They do
not finalize a transaction: account dispatch commits or restores their shared
state after inspecting the response. The finite-height family counts executed
child frames, independently of the Core evaluator's fuel. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ChildFrameSemantics
open Core

structure Code where
  program : Program
  body : CodeBlock
  bytes : List UInt8

/-- The source wrapper agrees with the object compiler's entry function. -/
def Code.entry (code : Code) : Function :=
  {name := "$lean$object$entry", args := [], ret := .unit, body := code.body.stmts}

def Code.functions (code : Code) : List Function :=
  code.program.functions ++ code.body.functions ++ [code.entry]

abbrev Catalog := List (Word × Code)

def select (catalog : Catalog) (address : Word) : Option Code :=
  (catalog.find? (fun entry => entry.1 == address)).map Prod.snd

/-- The code a creation's init frame may run, keyed by the bytes that begin the
init code, and the runtime images a deployment may install. -/
structure InitCatalog where
  templates : List Code := []
  runtimes : List (List UInt8) := []

/-- Only block and transaction observations are inherited from the parent.
Message observations, gas, code, memory and return data belong to this child. -/
def initial (parent : RuntimeCallEffectsSemantics.State) (request : AccountCallSemantics.Request)
    (shared : AccountCallSemantics.Shared) (bytes : List UInt8) : RuntimeCallEffectsSemantics.State :=
  let observations := parent.runtime.runtime.runtime.runtime.environment
  let observations : EnvironmentSemantics.State := {observations with
    direct := fun operation => match operation with
      | .address => request.target
      | .caller => request.caller
      | .callvalue => request.value
      | .calldataSize => request.calldataSize
      | .returnDataSize => Word.zero
    gas := some request.gas
    codeSize := Word.ofNatModulo bytes.length
    codeKnown := true
    calldata := request.calldata}
  let runtime : RuntimeEffectsSemantics.State := {
    memory := {}
    storage := {world := shared.world, address := request.target, complete := shared.complete, isStatic := request.isStatic}}
  let environment : RuntimeEnvironmentEffectsSemantics.State := ⟨runtime, observations⟩
  let logs : RuntimeLogEffectsSemantics.State := ⟨environment, shared.logs, shared.logSize⟩
  let account : RuntimeAccountEffectsSemantics.State := ⟨logs, shared.balances⟩
  ⟨⟨account, []⟩, request.depth⟩

/-- The frame wrapper performs a final account lookup before its result is
passed to childResult. An unsuccessful lookup replaces the body status. -/
def completedStatus (status : Semantics.Result Semantics.Value) (state : RuntimeEffectsSemantics.State) :
    Semantics.Result Semantics.Value :=
  match StorageSemantics.get state.storage.world state.storage.address state.storage.complete with
  | .ok _ => status
  | .error reason => .fault (.language reason)

/-- A finite child execution supplies only source derivations. Code selection
and known bytes are checked before entering its fresh frame. -/
inductive Children (catalog : Catalog)
    (effects : Option (List UInt8) → Semantics.ExternalSemantics RuntimeCallEffectsSemantics.State)
    (parent : RuntimeCallEffectsSemantics.State) : AccountCallSemantics.Children where
  | executed {source : Word} {request : AccountCallSemantics.Request}
      {shared : AccountCallSemantics.Shared} {account : AccountState.Account} {code : Code}
      {status : Semantics.Result Semantics.Value} {final : Semantics.State RuntimeCallEffectsSemantics.State}
      {response : Semantics.Result AccountCallSemantics.Response}
      (ordinaryAccount : AccountCallSemantics.isPrecompile request.target = false)
      (found : StorageSemantics.lookup request.target shared.world = some account)
      (selected : select catalog request.target = some code)
      (known : account.code = some code.bytes)
      (evaluated : Semantics.EvalFunction code.functions (effects (some code.bytes)) code.entry []
        ⟨[], initial parent request shared code.bytes⟩ status final)
      (responded : ChildResultSemantics.Respond
        (completedStatus status final.external.runtime.runtime.runtime.runtime.runtime)
        final.external.runtime.runtime.runtime.runtime.runtime response) :
      Children catalog effects parent .ordinary source request shared response
        (RuntimeCallEffectsSemantics.shared final.external)

/-- The first compiled-child instance executes the established effect language
without further message calls. Its result still uses the same account checkpoint. -/
inductive CallFree (catalog : Catalog) (parent : RuntimeCallEffectsSemantics.State) :
    AccountCallSemantics.Children where
  | executed {source : Word} {request : AccountCallSemantics.Request}
      {shared : AccountCallSemantics.Shared} {account : AccountState.Account} {code : Code}
      {status : Semantics.Result Semantics.Value} {final : Semantics.State RuntimeReturnDataEffectsSemantics.State}
      {response : Semantics.Result AccountCallSemantics.Response}
      (ordinaryAccount : AccountCallSemantics.isPrecompile request.target = false)
      (found : StorageSemantics.lookup request.target shared.world = some account)
      (selected : select catalog request.target = some code)
      (known : account.code = some code.bytes)
      (evaluated : Semantics.EvalFunction code.functions (RuntimeReturnDataEffectsSemantics.effects (some code.bytes))
        code.entry [] ⟨[], (initial parent request shared code.bytes).runtime⟩ status final)
      (responded : ChildResultSemantics.Respond
        (completedStatus status final.external.runtime.runtime.runtime.runtime)
        final.external.runtime.runtime.runtime.runtime response) :
      CallFree catalog parent .ordinary source request shared response
        (RuntimeCallEffectsSemantics.shared ⟨final.external, request.depth⟩)

def callFreeEffects (catalog : Catalog) (image : Option (List UInt8)) :
    Semantics.ExternalSemantics RuntimeCallEffectsSemantics.State :=
  RuntimeCallEffectsSemantics.effectsWith (CallFree catalog) image

/-- Height zero still permits local call outcomes such as absent accounts and
insufficient funds. Exhausting this height never invents a source failure. -/
def effectsAt (catalog : Catalog) : Nat → Option (List UInt8) →
    Semantics.ExternalSemantics RuntimeCallEffectsSemantics.State
  | 0, image => RuntimeCallEffectsSemantics.effects image
  | height + 1, image => RuntimeCallEffectsSemantics.effectsWith (Children catalog (effectsAt catalog height)) image

theorem initial_shared (parent : RuntimeCallEffectsSemantics.State) (request : AccountCallSemantics.Request)
    (shared : AccountCallSemantics.Shared) (bytes : List UInt8) :
    RuntimeCallEffectsSemantics.shared (initial parent request shared bytes) = shared := by
  cases shared
  rfl

theorem initial_transport (parent : RuntimeCallEffectsSemantics.State) (request : AccountCallSemantics.Request)
    (shared : AccountCallSemantics.Shared) (bytes : List UInt8) :
    RuntimeCallEffectsSemantics.transport (initial parent request shared bytes) = ⟨{}, [], Word.zero⟩ := rfl

theorem initial_depth (parent : RuntimeCallEffectsSemantics.State) (request : AccountCallSemantics.Request)
    (shared : AccountCallSemantics.Shared) (bytes : List UInt8) :
    (initial parent request shared bytes).callDepth = request.depth := rfl

theorem completedStatus_found {status : Semantics.Result Semantics.Value} {state : RuntimeEffectsSemantics.State}
    {account : AccountState.Account}
    (found : StorageSemantics.get state.storage.world state.storage.address state.storage.complete = .ok account) :
    completedStatus status state = status := by simp only [completedStatus, found]

end Solcore.Frontend.RustHull.ChildFrameSemantics
end

section
-- leanmerge: from Solcore.Frontend.RustHull.CreationAddressSemantics
/-! Contract addresses of CREATE and CREATE2, independent of Core. Byte strings
are lists of naturals below 256. RLP follows appendix B of the Yellow Paper,
and Keccak-256 of a byte string is the connected `KeccakSemantics` absorption
of those bytes stored from address zero. An address is the low 20 bytes of a
digest. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.CreationAddressSemantics
open Core

abbrev Bytes := List Nat

/-- RLP's BE: the big-endian bytes of a natural number, without leading zeros. -/
def bigEndian (value : Nat) : Bytes :=
  if value = 0 then [] else bigEndian (value / 256) ++ [value % 256]
termination_by value
decreasing_by omega

/-- RLP of a byte string. -/
def encodeBytes (bytes : Bytes) : Bytes :=
  if bytes.length = 1 ∧ bytes.headD 0 < 128 then bytes
  else if bytes.length < 56 then (128 + bytes.length) :: bytes
  else (183 + (bigEndian bytes.length).length) :: (bigEndian bytes.length ++ bytes)

/-- RLP of a list whose items are already encoded. -/
def encodeList (items : List Bytes) : Bytes :=
  let payload := items.flatten
  if payload.length < 56 then (192 + payload.length) :: payload
  else (247 + (bigEndian payload.length).length) :: (bigEndian payload.length ++ payload)

/-- The 32 big-endian bytes of a word. -/
def wordBytes (value : Word) : Bytes :=
  (List.range 32).map fun index => value.val / 256 ^ (31 - index) % 256

/-- An address occupies the low 20 bytes of a word. -/
def addressBytes (value : Word) : Bytes := (wordBytes value).drop 12

/-- CREATE hashes the RLP list of the creator address and its nonce. -/
def createPreimage (creator nonce : Word) : Bytes :=
  encodeList [encodeBytes (addressBytes creator), encodeBytes (bigEndian nonce.val)]

/-- CREATE2 hashes 0xff, the creator address, the salt and the init-code hash. -/
def create2Preimage (creator salt initHash : Word) : Bytes :=
  255 :: (addressBytes creator ++ wordBytes salt ++ wordBytes initHash)

/-- Bytes written one at a time from `index`. -/
def storeBytes : MemorySemantics.Entries → Nat → Bytes → MemorySemantics.Entries
  | words, _, [] => words
  | words, index, byte :: rest =>
      storeBytes (MemorySemantics.writeByte words (Word.ofNatModulo index) (Word.ofNatModulo byte)) (index + 1) rest

def stored (bytes : Bytes) : MemorySemantics.Entries := storeBytes [] 0 bytes

/-- Keccak-256 of a byte string. -/
def Keccak (bytes : Bytes) (digest : Word) : Prop :=
  KeccakSemantics.Absorb (stored bytes) Word.zero (Word.ofNatModulo bytes.length)
    (List.replicate 25 Word.zero) digest

def address (digest : Word) : Word := digest.bitAnd (Word.ofNatModulo (2 ^ 160 - 1))

inductive Scheme where
  | create
  | create2 (salt : Word)

/-- The address of a new account. CREATE2's init-code hash is taken over the
init bytes copied from address zero. -/
inductive Derived (creator nonce : Word) (initCode : MemorySemantics.Entries) (initLength : Word) :
    Scheme → Word → Prop where
  | create {digest : Word} (hashed : Keccak (createPreimage creator nonce) digest) :
      Derived creator nonce initCode initLength .create (address digest)
  | create2 {salt initHash digest : Word}
      (initHashed : KeccakSemantics.Absorb initCode Word.zero initLength (List.replicate 25 Word.zero) initHash)
      (hashed : Keccak (create2Preimage creator salt initHash) digest) :
      Derived creator nonce initCode initLength (.create2 salt) (address digest)

end Solcore.Frontend.RustHull.CreationAddressSemantics
end

section
-- leanmerge: from Solcore.Frontend.RustHull.CreationSemantics
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
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RevertSemantics
/-! Hull's explicit revert, independently of its lowering. The message holds at
most one EVM word of UTF-8 bytes. As in the pinned Yul backend, it is stored
left-aligned as one word at memory offset zero, and the frame reverts with
exactly the message bytes. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RevertSemantics
open Core

/-- The big-endian value of a byte string. -/
def bytesValue : List UInt8 → Nat
  | [] => 0
  | byte :: rest => byte.toNat * 256 ^ rest.length + bytesValue rest

/-- The message bytes left-aligned in one word. -/
def messageWord (message : String) : Word :=
  Word.ofNatModulo (bytesValue message.toUTF8.data.toList * 256 ^ (32 - message.toUTF8.size))

/-- The number of message bytes. -/
def messageLength (message : String) : Word := Word.ofNatModulo message.toUTF8.size

/-- The frame stores the message word at offset zero and then reverts with the
message bytes; the termination sentinel stops the frame. -/
inductive Reverted (message : String) (state : RuntimeCallEffectsSemantics.State) :
    Semantics.Control → RuntimeCallEffectsSemantics.State → Prop where
  | reverted {memory : MemorySemantics.State} {reason : Semantics.Fault} {halted : RuntimeEffectsSemantics.State}
      (fits : message.toUTF8.size ≤ 32)
      (stored : MemorySemantics.mstore state.runtime.runtime.runtime.runtime.runtime.memory Word.zero
        (messageWord message) = (.value .unit, memory))
      (terminated : TerminationSemantics.terminate {state.runtime.runtime.runtime.runtime.runtime with memory := memory}
        2 Word.zero (messageLength message) = (.fault reason, halted)) :
      Reverted message state (.fault reason)
        {state with runtime := RuntimeReturnDataEffectsSemantics.withRuntime state.runtime halted}

end Solcore.Frontend.RustHull.RevertSemantics
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeLifecycleSemantics
/-! Account destruction updates shared accounts and balances before completing
its frame. Failed lookups and overflowing credits retain the initial state. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeLifecycleSemantics
open Core

abbrev State := RuntimeCallEffectsSemantics.State

def updated (state : State) (world : StorageSemantics.World) (balances : StorageSemantics.Words) : State :=
  RuntimeCallEffectsSemantics.withShared state
    {RuntimeCallEffectsSemantics.shared state with world := world, balances := balances}

def terminate (state : State) (kind : Nat) : Semantics.Result Semantics.Value × State :=
  let stopped := TerminationSemantics.terminate state.runtime.runtime.runtime.runtime.runtime kind Word.zero Word.zero
  (stopped.1, {state with runtime := RuntimeReturnDataEffectsSemantics.withRuntime state.runtime stopped.2})

inductive Destroy (beneficiary : Word) : State → Semantics.Result Semantics.Value → State → Prop where
  | staticFrame (state : State)
      (isStatic : state.runtime.runtime.runtime.runtime.runtime.storage.isStatic = true) :
      Destroy beneficiary state (terminate state 3).1 (terminate state 3).2
  | rejected (state : State) (reason : Word)
      (notStatic : state.runtime.runtime.runtime.runtime.runtime.storage.isStatic = false)
      (destroyed : AccountLifecycleSemantics.destroy state.runtime.runtime.runtime.runtime.runtime.storage.world
        state.runtime.runtime.balances state.runtime.runtime.runtime.runtime.runtime.storage.address beneficiary
        state.runtime.runtime.runtime.runtime.runtime.storage.complete = .error reason) :
      Destroy beneficiary state (.fault (.language reason)) state
  | completed (state : State) (world : StorageSemantics.World) (balances : StorageSemantics.Words)
      (notStatic : state.runtime.runtime.runtime.runtime.runtime.storage.isStatic = false)
      (destroyed : AccountLifecycleSemantics.destroy state.runtime.runtime.runtime.runtime.runtime.storage.world
        state.runtime.runtime.balances state.runtime.runtime.runtime.runtime.runtime.storage.address beneficiary
        state.runtime.runtime.runtime.runtime.runtime.storage.complete = .ok (world, balances)) :
      Destroy beneficiary state (terminate (updated state world balances) 1).1
        (terminate (updated state world balances) 1).2

end Solcore.Frontend.RustHull.RuntimeLifecycleSemantics
end

section
-- leanmerge: from Solcore.Frontend.RustHull.YulSemantics
/-! The connected fragment of inline Yul, independently of its lowering. An
assembly block is a list of statements: `let` with one name and an optional
value, assignment to one name, expression statements, nested blocks, `if` and
`switch`. Expressions are literals, variables and calls of `mload`, `msize`,
`mstore`, `mstore8`, `return` and `revert`, and of the word operations `add`
and `sub` modulo 2^256, the unsigned comparisons `lt` and `gt`, `eq` and
`iszero`, which give one or zero. A call evaluates its arguments from right to
left, so nested calls with effects observe the order. Yul locals live
in the Hull heap like Hull locals and are visible until the end of their block;
a variable may also name a Hull word local, which the block reads and assigns in
place. An `if` runs its body when the condition word is nonzero, and a `switch`
runs the first case whose literal denotes the scrutinee, or else the default
body. Number and hexadecimal literals are words in the text of Hull word
literals, and `true` and `false` are one and zero. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.YulSemantics
open Core

abbrev State := Semantics.State RuntimeCallEffectsSemantics.State

/-- The word a literal denotes. String literals are outside the fragment. -/
def literalWord? : YulLit → Option Word
  | .number text | .hex text => Semantics.parseWord? text
  | .bool value => some (Word.ofNatModulo (if value then 1 else 0))
  | .string _ => none

/-- The memory and termination frame of a state. -/
def frame (state : State) : RuntimeEffectsSemantics.State := state.external.runtime.runtime.runtime.runtime.runtime

def withFrame (state : State) (next : RuntimeEffectsSemantics.State) : State :=
  {state with external := {state.external with
    runtime := (RuntimeReturnDataEffectsSemantics.withRuntime state.external.runtime next)}}

/-- The builtins of the fragment with effects on the frame. -/
def effectBuiltins : List String := ["mload", "msize", "mstore", "mstore8", "return", "revert"]

/-- The builtins of the fragment. -/
def builtins : List String := effectBuiltins ++ YulFragment.primitives

/-- A builtin of the fragment on its argument words, in Yul order: a memory read
or size, a memory write, the return or revert termination, or a word operation
that leaves the frame unchanged. -/
inductive Builtin : String → List Word → RuntimeEffectsSemantics.State →
    Semantics.Result Semantics.Value → RuntimeEffectsSemantics.State → Prop where
  | mload {frame : RuntimeEffectsSemantics.State} {offset : Word} :
      Builtin "mload" [offset] frame (MemorySemantics.mload frame.memory offset).1
        {frame with memory := (MemorySemantics.mload frame.memory offset).2}
  | msize {frame : RuntimeEffectsSemantics.State} :
      Builtin "msize" [] frame (.value (.word frame.memory.size)) frame
  | mstore {frame : RuntimeEffectsSemantics.State} {offset value : Word} :
      Builtin "mstore" [offset, value] frame (MemorySemantics.mstore frame.memory offset value).1
        {frame with memory := (MemorySemantics.mstore frame.memory offset value).2}
  | mstore8 {frame : RuntimeEffectsSemantics.State} {offset value : Word} :
      Builtin "mstore8" [offset, value] frame (MemorySemantics.mstore8 frame.memory offset value).1
        {frame with memory := (MemorySemantics.mstore8 frame.memory offset value).2}
  | returned {frame : RuntimeEffectsSemantics.State} {offset length : Word} :
      Builtin "return" [offset, length] frame (TerminationSemantics.terminate frame 1 offset length).1
        (TerminationSemantics.terminate frame 1 offset length).2
  | reverted {frame : RuntimeEffectsSemantics.State} {offset length : Word} :
      Builtin "revert" [offset, length] frame (TerminationSemantics.terminate frame 2 offset length).1
        (TerminationSemantics.terminate frame 2 offset length).2
  | add {frame : RuntimeEffectsSemantics.State} {left right : Word} :
      Builtin "add" [left, right] frame (.value (.word (left + right))) frame
  | sub {frame : RuntimeEffectsSemantics.State} {left right : Word} :
      Builtin "sub" [left, right] frame (.value (.word (left - right))) frame
  | lt {frame : RuntimeEffectsSemantics.State} {left right : Word} :
      Builtin "lt" [left, right] frame
        (.value (.word (if left < right then Word.ofNatModulo 1 else Word.zero))) frame
  | gt {frame : RuntimeEffectsSemantics.State} {left right : Word} :
      Builtin "gt" [left, right] frame
        (.value (.word (if left > right then Word.ofNatModulo 1 else Word.zero))) frame
  | eq {frame : RuntimeEffectsSemantics.State} {left right : Word} :
      Builtin "eq" [left, right] frame
        (.value (.word (if left = right then Word.ofNatModulo 1 else Word.zero))) frame
  | iszero {frame : RuntimeEffectsSemantics.State} {value : Word} :
      Builtin "iszero" [value] frame
        (.value (.word (if value = Word.zero then Word.ofNatModulo 1 else Word.zero))) frame

mutual
  /-- An expression's value. A call evaluates the reversed argument list from
  left to right, which is Yul's right-to-left order, and passes the words to the
  builtin in source order. A fault in an argument stops a builtin call. -/
  inductive Eval : Semantics.Environment → YulExpr → State → Semantics.Result Semantics.Value → State → Prop where
    | literal {environment : Semantics.Environment} {literal : YulLit} {span : Option Span} {state : State}
        {word : Word} (evaluated : literalWord? literal = some word) :
        Eval environment ⟨.literal literal, span⟩ state (.value (.word word)) state
    | ident {environment : Semantics.Environment} {name : YulName} {span : Option Span} {state : State}
        {location : Nat} {word : Word}
        (found : Semantics.lookupLocation environment name.name = some location)
        (read : state.heap[location]? = some (.word word)) :
        Eval environment ⟨.ident name, span⟩ state (.value (.word word)) state
    | call {environment : Semantics.Environment} {name : YulName} {arguments : List YulExpr} {span : Option Span}
        {initial middle : State} {words : List Word} {result : Semantics.Result Semantics.Value}
        {next : RuntimeEffectsSemantics.State}
        (evaluated : Arguments environment arguments.reverse initial (.value words) middle)
        (computed : Builtin name.name words.reverse (frame middle) result next) :
        Eval environment ⟨.call name arguments, span⟩ initial result (withFrame middle next)
    | callFault {environment : Semantics.Environment} {name : YulName} {arguments : List YulExpr}
        {span : Option Span} {initial final : State} {reason : Semantics.Fault} (named : name.name ∈ builtins)
        (evaluated : Arguments environment arguments.reverse initial (.fault reason) final) :
        Eval environment ⟨.call name arguments, span⟩ initial (.fault reason) final

  /-- Argument words in evaluation order. -/
  inductive Arguments : Semantics.Environment → List YulExpr → State → Semantics.Result (List Word) → State → Prop where
    | nil {environment : Semantics.Environment} {state : State} :
        Arguments environment [] state (.value []) state
    | cons {environment : Semantics.Environment} {argument : YulExpr} {rest : List YulExpr}
        {initial middle final : State} {word : Word} {words : List Word}
        (head : Eval environment argument initial (.value (.word word)) middle)
        (tail : Arguments environment rest middle (.value words) final) :
        Arguments environment (argument :: rest) initial (.value (word :: words)) final
    | tailFault {environment : Semantics.Environment} {argument : YulExpr} {rest : List YulExpr}
        {initial middle final : State} {word : Word} {reason : Semantics.Fault}
        (head : Eval environment argument initial (.value (.word word)) middle)
        (tail : Arguments environment rest middle (.fault reason) final) :
        Arguments environment (argument :: rest) initial (.fault reason) final
    | headFault {environment : Semantics.Environment} {argument : YulExpr} {rest : List YulExpr}
        {initial final : State} {reason : Semantics.Fault}
        (head : Eval environment argument initial (.fault reason) final) :
        Arguments environment (argument :: rest) initial (.fault reason) final
end

/-- The body of the first case whose literal denotes the word. -/
def select (word : Word) : List YulCase → Option (List YulStmt)
  | [] => none
  | arm :: rest => if literalWord? arm.lit = some word then some arm.body else select word rest

mutual
  /-- A statement list. `let` allocates the local's heap cell and an assignment
  writes the variable's cell. A fault, including the termination sentinel, stops
  the list, and so does any other control of a nested body. -/
  inductive Run : Semantics.Environment → List YulStmt → State → Semantics.Control → State → Prop where
    | nil {environment : Semantics.Environment} {state : State} :
        Run environment [] state .fallthrough state
    | letValue {environment : Semantics.Environment} {name : YulName} {value : YulExpr} {span : Option Span}
        {rest : List YulStmt} {initial middle final : State} {control : Semantics.Control} {word : Word}
        (evaluated : Eval environment value initial (.value (.word word)) middle)
        (tail : Run ((name.name, middle.heap.length) :: environment) rest
          (Semantics.allocate middle (.word word)).2 control final) :
        Run environment (⟨.letDecl [name] (some value), span⟩ :: rest) initial control final
    | letZero {environment : Semantics.Environment} {name : YulName} {span : Option Span} {rest : List YulStmt}
        {initial final : State} {control : Semantics.Control}
        (tail : Run ((name.name, initial.heap.length) :: environment) rest
          (Semantics.allocate initial (.word Word.zero)).2 control final) :
        Run environment (⟨.letDecl [name] none, span⟩ :: rest) initial control final
    | letFault {environment : Semantics.Environment} {name : YulName} {value : YulExpr} {span : Option Span}
        {rest : List YulStmt} {initial final : State} {reason : Semantics.Fault}
        (evaluated : Eval environment value initial (.fault reason) final) :
        Run environment (⟨.letDecl [name] (some value), span⟩ :: rest) initial (.fault reason) final
    | assign {environment : Semantics.Environment} {name : YulName} {value : YulExpr} {span : Option Span}
        {rest : List YulStmt} {initial middle final : State} {control : Semantics.Control} {word : Word}
        {location : Nat}
        (evaluated : Eval environment value initial (.value (.word word)) middle)
        (found : Semantics.lookupLocation environment name.name = some location)
        (tail : Run environment rest {middle with heap := middle.heap.set location (.word word)} control final) :
        Run environment (⟨.assign [name] value, span⟩ :: rest) initial control final
    | assignFault {environment : Semantics.Environment} {name : YulName} {value : YulExpr} {span : Option Span}
        {rest : List YulStmt} {initial final : State} {reason : Semantics.Fault}
        (evaluated : Eval environment value initial (.fault reason) final) :
        Run environment (⟨.assign [name] value, span⟩ :: rest) initial (.fault reason) final
    | expression {environment : Semantics.Environment} {value : YulExpr} {span : Option Span}
        {rest : List YulStmt} {initial middle final : State} {control : Semantics.Control}
        (evaluated : Eval environment value initial (.value .unit) middle)
        (tail : Run environment rest middle control final) :
        Run environment (⟨.expression value, span⟩ :: rest) initial control final
    | expressionFault {environment : Semantics.Environment} {value : YulExpr} {span : Option Span}
        {rest : List YulStmt} {initial final : State} {reason : Semantics.Fault}
        (evaluated : Eval environment value initial (.fault reason) final) :
        Run environment (⟨.expression value, span⟩ :: rest) initial (.fault reason) final
    | compound {environment : Semantics.Environment} {statement : YulStmt} {rest : List YulStmt}
        {initial middle final : State} {control : Semantics.Control}
        (head : Compound environment statement initial .fallthrough middle)
        (tail : Run environment rest middle control final) :
        Run environment (statement :: rest) initial control final
    | compoundStop {environment : Semantics.Environment} {statement : YulStmt} {rest : List YulStmt}
        {initial final : State} {control : Semantics.Control}
        (head : Compound environment statement initial control final) (stopped : control ≠ .fallthrough) :
        Run environment (statement :: rest) initial control final

  /-- A statement with nested bodies. The locals of a body end with it. -/
  inductive Compound : Semantics.Environment → YulStmt → State → Semantics.Control → State → Prop where
    | block {environment : Semantics.Environment} {body : List YulStmt} {span : Option Span}
        {initial final : State} {control : Semantics.Control}
        (inner : Run environment body initial control final) :
        Compound environment ⟨.block body, span⟩ initial control final
    | ifTrue {environment : Semantics.Environment} {condition : YulExpr} {body : List YulStmt}
        {span : Option Span} {initial middle final : State} {control : Semantics.Control} {word : Word}
        (evaluated : Eval environment condition initial (.value (.word word)) middle) (nonzero : word ≠ Word.zero)
        (branch : Run environment body middle control final) :
        Compound environment ⟨.ifThen condition body, span⟩ initial control final
    | ifFalse {environment : Semantics.Environment} {condition : YulExpr} {body : List YulStmt}
        {span : Option Span} {initial final : State}
        (evaluated : Eval environment condition initial (.value (.word Word.zero)) final) :
        Compound environment ⟨.ifThen condition body, span⟩ initial .fallthrough final
    | ifFault {environment : Semantics.Environment} {condition : YulExpr} {body : List YulStmt}
        {span : Option Span} {initial final : State} {reason : Semantics.Fault}
        (evaluated : Eval environment condition initial (.fault reason) final) :
        Compound environment ⟨.ifThen condition body, span⟩ initial (.fault reason) final
    | switchCase {environment : Semantics.Environment} {value : YulExpr} {cases : List YulCase}
        {defaultBody : Option (List YulStmt)} {span : Option Span} {initial middle final : State}
        {control : Semantics.Control} {word : Word} {body : List YulStmt}
        (evaluated : Eval environment value initial (.value (.word word)) middle)
        (selected : select word cases = some body) (branch : Run environment body middle control final) :
        Compound environment ⟨.switch value cases defaultBody, span⟩ initial control final
    | switchDefault {environment : Semantics.Environment} {value : YulExpr} {cases : List YulCase}
        {defaultBody : Option (List YulStmt)} {span : Option Span} {initial middle final : State}
        {control : Semantics.Control} {word : Word}
        (evaluated : Eval environment value initial (.value (.word word)) middle)
        (unselected : select word cases = none)
        (branch : Run environment (defaultBody.getD []) middle control final) :
        Compound environment ⟨.switch value cases defaultBody, span⟩ initial control final
    | switchFault {environment : Semantics.Environment} {value : YulExpr} {cases : List YulCase}
        {defaultBody : Option (List YulStmt)} {span : Option Span} {initial final : State}
        {reason : Semantics.Fault} (evaluated : Eval environment value initial (.fault reason) final) :
        Compound environment ⟨.switch value cases defaultBody, span⟩ initial (.fault reason) final
end

/-- An assembly block runs in the Hull environment; its locals end with it. -/
def Assembled (_functions : List Function) (environment : Semantics.Environment) (body : List YulStmt)
    (initial : State) (control : Semantics.Control) (final : State) : Prop :=
  Run environment body initial control final

end Solcore.Frontend.RustHull.YulSemantics
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeCallModeSemantics
/-! Message call modes share caller transport and account checkpoints. The
mode controls the handler, caller observation and stipend checks; account
dispatch controls execution address and balance transfer separately. Account
destruction shares the same frame state and transaction world, and so do
creation attempts. Hull's explicit revert follows `RevertSemantics`, and inline
Yul blocks follow `YulSemantics`. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeCallModeSemantics
open Core

abbrev State := RuntimeCallEffectsSemantics.State
abbrev shared := RuntimeCallEffectsSemantics.shared
abbrev transport := RuntimeCallEffectsSemantics.transport
abbrev withTransport := RuntimeCallEffectsSemantics.withTransport
abbrev invalid := RuntimeCallEffectsSemantics.invalid

inductive Operation where
  | ordinary | staticCall | callCode | delegateCall
  deriving DecidableEq, BEq, Repr

def Operation.name : Operation → String
  | .ordinary => "call" | .staticCall => "staticcall"
  | .callCode => "callcode" | .delegateCall => "delegatecall"

def Operation.mode : Operation → AccountCallSemantics.Mode
  | .ordinary | .staticCall => .ordinary
  | .callCode => .callCode | .delegateCall => .delegateCall

def Operation.hasStipend : Operation → Bool
  | .ordinary | .callCode => true
  | .staticCall | .delegateCall => false

def observations (state : State) : EnvironmentSemantics.State :=
  state.runtime.runtime.runtime.runtime.environment

def arguments (operation : Operation) (state : State)
    (gas target value inputOffset inputLength outputOffset outputLength : Word) : CallTransportSemantics.Arguments :=
  let runtime := state.runtime.runtime.runtime.runtime.runtime
  {caller := if operation = .delegateCall then (observations state).direct .caller else runtime.storage.address
   depth := state.callDepth
   isStatic := if operation = .staticCall then true else runtime.storage.isStatic
   gas := if operation.hasStipend ∧ value ≠ Word.zero then gas.add (Word.ofNatModulo 2300) else gas
   target := target, value := value, inputOffset := inputOffset, inputLength := inputLength
   outputOffset := outputOffset, outputLength := outputLength}

/-- CALLCODE admits nonzero value in a static frame, but its child still
inherits the static flag. Only ordinary CALL rejects that value at this stage. -/
inductive Call (children : State → AccountCallSemantics.Children) (operation : Operation)
    (gas target value inputOffset inputLength outputOffset outputLength : Word) :
    State → Semantics.Result Semantics.Value → State → Prop where
  | staticValue (state : State)
      (ordinary : operation = .ordinary)
      (isStatic : state.runtime.runtime.runtime.runtime.runtime.storage.isStatic = true)
      (nonzero : value ≠ Word.zero) :
      Call children operation gas target value inputOffset inputLength outputOffset outputLength
        state (invalid state).1 (invalid state).2
  | gasOverflow (state : State)
      (stipend : operation.hasStipend = true)
      (permitted : operation ≠ .ordinary ∨ state.runtime.runtime.runtime.runtime.runtime.storage.isStatic = false)
      (nonzero : value ≠ Word.zero)
      (overflow : gas > Word.ofNatModulo (wordModulus - 2301)) :
      Call children operation gas target value inputOffset inputLength outputOffset outputLength
        state (.fault (.language (Word.ofNatModulo 13))) state
  | invoked {state : State} {next : CallTransportSemantics.State} {nextShared : AccountCallSemantics.Shared}
      {result : Semantics.Result Semantics.Value}
      (permitted : operation ≠ .ordinary ∨ value = Word.zero ∨
        state.runtime.runtime.runtime.runtime.runtime.storage.isStatic = false)
      (stipend : operation.hasStipend = true → value ≠ Word.zero →
        ¬gas > Word.ofNatModulo (wordModulus - 2301))
      (executed : CallTransportSemantics.Execute
        (AccountCallSemantics.Dispatch (children state) operation.mode
          state.runtime.runtime.runtime.runtime.runtime.storage.address)
        true (arguments operation state gas target value inputOffset inputLength outputOffset outputLength)
        (transport state) (shared state) result next nextShared) :
      Call children operation gas target value inputOffset inputLength outputOffset outputLength
        state result (withTransport state next nextShared)

inductive Builtin (children : State → AccountCallSemantics.Children) (image : Option (List UInt8)) :
    String → Ty → List Semantics.Value → State → Semantics.Result Semantics.Value → State → Prop where
  | runtime {name type arguments state result final}
      (computed : RuntimeReturnDataEffectsSemantics.Builtin image name type arguments state.runtime result final) :
      Builtin children image name type arguments state result {state with runtime := final}
  | call {type state result final gas target value inputOffset inputLength outputOffset outputLength}
      (computed : Call children .ordinary gas target value inputOffset inputLength outputOffset outputLength state result final) :
      Builtin children image "call" type [.word gas, .word target, .word value, .word inputOffset,
        .word inputLength, .word outputOffset, .word outputLength] state result final
  | staticCall {type state result final gas target inputOffset inputLength outputOffset outputLength}
      (computed : Call children .staticCall gas target Word.zero inputOffset inputLength outputOffset outputLength state result final) :
      Builtin children image "staticcall" type [.word gas, .word target, .word inputOffset,
        .word inputLength, .word outputOffset, .word outputLength] state result final
  | callCode {type state result final gas target value inputOffset inputLength outputOffset outputLength}
      (computed : Call children .callCode gas target value inputOffset inputLength outputOffset outputLength state result final) :
      Builtin children image "callcode" type [.word gas, .word target, .word value, .word inputOffset,
        .word inputLength, .word outputOffset, .word outputLength] state result final
  | delegateCall {type state result final gas target inputOffset inputLength outputOffset outputLength}
      (computed : Call children .delegateCall gas target ((observations state).direct .callvalue)
        inputOffset inputLength outputOffset outputLength state result final) :
      Builtin children image "delegatecall" type [.word gas, .word target, .word inputOffset,
        .word inputLength, .word outputOffset, .word outputLength] state result final
  | destroy {type state result final beneficiary}
      (computed : RuntimeLifecycleSemantics.Destroy beneficiary state result final) :
      Builtin children image "selfdestruct" type [.word beneficiary] state result final
  | create {type state result final value offset length}
      (computed : CreationSemantics.Refused value offset length state result final) :
      Builtin children image "create" type [.word value, .word offset, .word length] state result final
  | create2 {type state result final value offset length salt}
      (computed : CreationSemantics.Refused value offset length state result final) :
      Builtin children image "create2" type [.word value, .word offset, .word length, .word salt] state result final
  | createAdmitted {type state result final value offset length}
      (computed : CreationSemantics.Admitted .create value offset length state result final) :
      Builtin children image "create" type [.word value, .word offset, .word length] state result final
  | create2Admitted {type state result final value offset length salt}
      (computed : CreationSemantics.Admitted (.create2 salt) value offset length state result final) :
      Builtin children image "create2" type [.word value, .word offset, .word length, .word salt] state result final

def effectsWith (children : State → AccountCallSemantics.Children) (image : Option (List UInt8)) :
    Semantics.ExternalSemantics State where
  builtin := Builtin children image
  assembly := YulSemantics.Assembled
  revert := RevertSemantics.Reverted

def effects (image : Option (List UInt8)) : Semantics.ExternalSemantics State :=
  effectsWith (fun _ => AccountCallSemantics.noChildren) image

end Solcore.Frontend.RustHull.RuntimeCallModeSemantics
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ChildFrameModeSemantics
/-! Linked child code is selected by the requested code address. CALLCODE and
DELEGATECALL execute that code at the invoking frame's address, using its
storage. Source derivations count child frames independently of execution fuel. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ChildFrameModeSemantics
open Core

abbrev Code := ChildFrameSemantics.Code
abbrev Catalog := ChildFrameSemantics.Catalog
abbrev select := ChildFrameSemantics.select
abbrev completedStatus := ChildFrameSemantics.completedStatus

def executionRequest (mode : AccountCallSemantics.Mode) (source : Word)
    (request : AccountCallSemantics.Request) : AccountCallSemantics.Request :=
  {request with target := if mode = .ordinary then request.target else source}

def initial (mode : AccountCallSemantics.Mode) (source : Word)
    (parent : RuntimeCallModeSemantics.State) (request : AccountCallSemantics.Request)
    (shared : AccountCallSemantics.Shared) (bytes : List UInt8) : RuntimeCallModeSemantics.State :=
  ChildFrameSemantics.initial parent (executionRequest mode source request) shared bytes

inductive Children (catalog : Catalog)
    (effects : Option (List UInt8) → Semantics.ExternalSemantics RuntimeCallModeSemantics.State)
    (parent : RuntimeCallModeSemantics.State) : AccountCallSemantics.Children where
  | executed {mode : AccountCallSemantics.Mode} {source : Word} {request : AccountCallSemantics.Request}
      {shared : AccountCallSemantics.Shared} {account : AccountState.Account} {code : Code}
      {status : Semantics.Result Semantics.Value} {final : Semantics.State RuntimeCallModeSemantics.State}
      {response : Semantics.Result AccountCallSemantics.Response}
      (ordinaryAccount : AccountCallSemantics.isPrecompile request.target = false)
      (found : StorageSemantics.lookup request.target shared.world = some account)
      (selected : select catalog request.target = some code)
      (known : account.code = some code.bytes)
      (evaluated : Semantics.EvalFunction code.functions (effects (some code.bytes)) code.entry []
        ⟨[], initial mode source parent request shared code.bytes⟩ status final)
      (responded : ChildResultSemantics.Respond
        (completedStatus status final.external.runtime.runtime.runtime.runtime.runtime)
        final.external.runtime.runtime.runtime.runtime.runtime response) :
      Children catalog effects parent mode source request shared response
        (RuntimeCallModeSemantics.shared final.external)

/-- Child frames at most `height` deep. `initCatalog` holds the init templates
and runtime images of creation; no rule of this file reads it yet. -/
def effectsAt (catalog : Catalog) (initCatalog : ChildFrameSemantics.InitCatalog) : Nat → Option (List UInt8) →
    Semantics.ExternalSemantics RuntimeCallModeSemantics.State
  | 0, image => RuntimeCallModeSemantics.effects image
  | height + 1, image =>
      RuntimeCallModeSemantics.effectsWith (Children catalog (effectsAt catalog initCatalog height)) image

theorem initial_shared (mode : AccountCallSemantics.Mode) (source : Word)
    (parent : RuntimeCallModeSemantics.State) (request : AccountCallSemantics.Request)
    (shared : AccountCallSemantics.Shared) (bytes : List UInt8) :
    RuntimeCallModeSemantics.shared (initial mode source parent request shared bytes) = shared :=
  ChildFrameSemantics.initial_shared _ _ _ _

theorem initial_transport (mode : AccountCallSemantics.Mode) (source : Word)
    (parent : RuntimeCallModeSemantics.State) (request : AccountCallSemantics.Request)
    (shared : AccountCallSemantics.Shared) (bytes : List UInt8) :
    RuntimeCallModeSemantics.transport (initial mode source parent request shared bytes) = ⟨{}, [], Word.zero⟩ := rfl

theorem initial_depth (mode : AccountCallSemantics.Mode) (source : Word)
    (parent : RuntimeCallModeSemantics.State) (request : AccountCallSemantics.Request)
    (shared : AccountCallSemantics.Shared) (bytes : List UInt8) :
    (initial mode source parent request shared bytes).callDepth = request.depth := rfl

end Solcore.Frontend.RustHull.ChildFrameModeSemantics
end
