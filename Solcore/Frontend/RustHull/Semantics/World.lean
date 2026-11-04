import Solcore.Frontend.RustHull.Effects
import Solcore.Frontend.RustHull.Semantics
import Solcore.Frontend.RustHull.Semantics.Memory
import Solcore.Frontend.RustHull.Semantics.Digests
import Solcore.Frontend.RustHull.Memory

/-!
# Hull world semantics

Storage, message and block observations, logs, the code image, account observation and account
destruction. Main declarations: `StorageSemantics.World`, `EnvironmentSemantics.Operation`,
`LogsSemantics`, `CodeImageSemantics`, `AccountObservationSemantics`, `AccountLifecycleSemantics`.
-/

section
-- leanmerge: from Solcore.Frontend.RustHull.StorageSemantics
/-! Account storage observations independent of lowering and machine execution.
Executable code identities belong to the representation and do not occur here. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.StorageSemantics
open Core

abbrev World := List AccountState.Account
abbrev Words := List (Word × Word)

def readWord (key : Word) : Words → Word
  | [] => Word.zero
  | (stored, value) :: rest => if key == stored then value else readWord key rest

def writeWord (key value : Word) : Words → Words
  | [] => [(key, value)]
  | (stored, old) :: rest =>
      if key == stored then (key, value) :: rest else (stored, old) :: writeWord key value rest

def lookup (address : Word) : World → Option AccountState.Account
  | [] => none
  | account :: rest => if address == account.address then some account else lookup address rest

def put (address : Word) (account : AccountState.Account) : World → World
  | [] => [{account with address := address}]
  | head :: rest => if address == head.address then {account with address := address} :: rest
      else head :: put address account rest

def get (world : World) (address : Word) (complete : Bool) : Except Word AccountState.Account :=
  match lookup address world with
  | some account => .ok account
  | none => if complete then .ok {address := address} else .error (Word.ofNatModulo 7)

def storage (account : AccountState.Account) (transient : Bool) : Words :=
  if transient then account.transient else account.storage

def update (account : AccountState.Account) (transient : Bool) (key value : Word) : AccountState.Account :=
  if transient then {account with transient := writeWord key value account.transient}
  else {account with storage := writeWord key value account.storage}

def readStorage (world : World) (address : Word) (complete : Bool) (key : Word)
    (transient : Bool := false) : Except Word Word := do
  return readWord key (storage (← get world address complete) transient)

def writeStorage (world : World) (address : Word) (complete : Bool) (key value : Word)
    (transient : Bool := false) : Except Word World := do
  let account ← get world address complete
  return put address (update account transient key value) world

def clearTransaction (account : AccountState.Account) : AccountState.Account :=
  {account with transient := [], created := false, destroyed := false}

def finalize : World → Words → World × Words
  | [], balances => ([], balances)
  | account :: rest, balances =>
      if account.created && account.destroyed then
        finalize rest (writeWord account.address Word.zero balances)
      else
        let (world, balances) := finalize rest balances
        (clearTransaction account :: world, balances)


structure State where
  world : World := []
  address : Word := Word.zero
  complete : Bool := false
  isStatic : Bool := false
  exit : Word := Word.zero
  returnOffset : Word := Word.zero
  returnSize : Word := Word.zero
  deriving Repr

def load (state : State) (key : Word) (transient : Bool) : Semantics.Result Semantics.Value × State :=
  match readStorage state.world state.address state.complete key transient with
  | .ok value => (.value (.word value), state)
  | .error reason => (.fault (.language reason), state)

def store (state : State) (key value : Word) (transient : Bool) : Semantics.Result Semantics.Value × State :=
  if state.isStatic then
    (.fault (.language Word.maximum), {state with
      exit := Word.ofNatModulo 3
      returnOffset := Word.zero
      returnSize := Word.zero})
  else
    match writeStorage state.world state.address state.complete key value transient with
    | .ok world => (.value .unit, {state with world := world})
    | .error reason => (.fault (.language reason), state)

def builtin (name : String) (_type : Ty) (arguments : List Semantics.Value)
    (state : State) : Option (Semantics.Result Semantics.Value × State) :=
  match name, arguments with
  | "sload", [.word key] => some (load state key false)
  | "tload", [.word key] => some (load state key true)
  | "sstore", [.word key, .word value] => some (store state key value false)
  | "tstore", [.word key, .word value] => some (store state key value true)
  | _, _ => none

def effects : Semantics.ExternalSemantics State where
  builtin := fun name type arguments initial result final =>
    builtin name type arguments initial = some (result, final)
  assembly := fun _ _ _ _ _ _ => False
  revert := fun _ _ _ _ => False

end Solcore.Frontend.RustHull.StorageSemantics
end

section
-- leanmerge: from Solcore.Frontend.RustHull.AccountLifecycleSemantics
/-! Independent account destruction. Balances move immediately, while account
removal is delayed until successful transaction finalization. Code identities
and Core evaluation do not occur in this description. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.AccountLifecycleSemantics
open Core
open StorageSemantics (World Words readWord writeWord)

def address (value : Word) : Word := value.bitAnd (Word.ofNatModulo (2 ^ 160 - 1))

/-- A zero transfer retains the original ordered ledger. A newly created
account burns its balance when it names itself; an existing account keeps it. -/
def balances (created : Bool) (current beneficiary : Word) (initial : Words) : Except Word Words :=
  let amount := readWord current initial
  if current == beneficiary then
    if created then
      if amount == Word.zero then .ok initial else .ok (writeWord current Word.zero initial)
    else .ok initial
  else if amount == Word.zero then .ok initial
  else
    let recipient := readWord beneficiary initial
    if recipient > Word.maximum.sub amount then .error (Word.ofNatModulo 12)
    else .ok (writeWord beneficiary (recipient.add amount) (writeWord current Word.zero initial))

def publish (world : World) (current : Word) (account : AccountState.Account) : World :=
  if account.created then StorageSemantics.put current {account with destroyed := true} world else world

/-- Missing current accounts are errors in incomplete worlds. Beneficiaries
need only a ledger entry, with an absent balance interpreted as zero. Failed
lookups and overflowing credits make no account or balance update. -/
def destroy (world : World) (initial : Words) (current beneficiary : Word) (complete : Bool) :
    Except Word (World × Words) := do
  let current := address current
  let beneficiary := address beneficiary
  let account ← StorageSemantics.get world current complete
  let next ← balances account.created current beneficiary initial
  return (publish world current account, next)

end Solcore.Frontend.RustHull.AccountLifecycleSemantics
end

section
-- leanmerge: from Solcore.Frontend.RustHull.AccountObservationSemantics
/-! Account observations read the independent world and balance ledger.
Copying code changes caller memory; code hashing uses isolated scratch memory.
The byte packer is the shared pure representation function, without evaluation. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.AccountObservationSemantics
open Core

inductive Operation where
  | balance | selfbalance | size | copy | hash
  deriving DecidableEq, Repr

def Operation.name : Operation → String
  | .balance => "balance" | .selfbalance => "selfbalance"
  | .size => "extcodesize" | .copy => "extcodecopy" | .hash => "extcodehash"

def address (target : Word) : Word := target.bitAnd (Word.ofNatModulo (2 ^ 160 - 1))
def codeSize (bytes : List UInt8) : Word := Word.ofNatModulo bytes.length
abbrev packed := Memory.packBytes

def emptyAccount (account : AccountState.Account) (bytes : List UInt8) (balance : Word) : Bool :=
  if account.nonce == Word.zero then
    if codeSize bytes == Word.zero then balance == Word.zero else false
  else false

def failure (reason : Word) : Semantics.Result Semantics.Value := .fault (.language reason)
def unknownCode : Semantics.Result Semantics.Value := failure (Word.ofNatModulo 15)

inductive Builtin (world : StorageSemantics.World) (complete : Bool) (balances : StorageSemantics.Words)
    (current : Word) : String → Ty → List Semantics.Value →
    MemorySemantics.State → Semantics.Result Semantics.Value → MemorySemantics.State → Prop where
  | balance (type : Ty) (target : Word) (memory : MemorySemantics.State) :
      Builtin world complete balances current "balance" type [.word target] memory
        (.value (.word (StorageSemantics.readWord (address target) balances))) memory
  | selfbalance (type : Ty) (memory : MemorySemantics.State) :
      Builtin world complete balances current "selfbalance" type [] memory
        (.value (.word (StorageSemantics.readWord current balances))) memory
  | sizeFailure {type : Ty} {target reason : Word} {memory : MemorySemantics.State}
      (found : StorageSemantics.get world (address target) complete = .error reason) :
      Builtin world complete balances current "extcodesize" type [.word target] memory (failure reason) memory
  | sizeUnknown {type : Ty} {target : Word} {memory : MemorySemantics.State} {account : AccountState.Account}
      (found : StorageSemantics.get world (address target) complete = .ok account) (unknown : account.code = none) :
      Builtin world complete balances current "extcodesize" type [.word target] memory unknownCode memory
  | sizeKnown {type : Ty} {target : Word} {memory : MemorySemantics.State} {account : AccountState.Account} {bytes : List UInt8}
      (found : StorageSemantics.get world (address target) complete = .ok account) (known : account.code = some bytes) :
      Builtin world complete balances current "extcodesize" type [.word target] memory (.value (.word (codeSize bytes))) memory
  | copyFailure {type : Ty} {target destination source length reason : Word} {memory : MemorySemantics.State}
      (found : StorageSemantics.get world (address target) complete = .error reason) :
      Builtin world complete balances current "extcodecopy" type [.word target, .word destination, .word source, .word length]
        memory (failure reason) memory
  | copyUnknown {type : Ty} {target destination source length : Word} {memory : MemorySemantics.State} {account : AccountState.Account}
      (found : StorageSemantics.get world (address target) complete = .ok account) (unknown : account.code = none) :
      Builtin world complete balances current "extcodecopy" type [.word target, .word destination, .word source, .word length]
        memory unknownCode memory
  | copyKnown {type : Ty} {target destination source length : Word} {memory finalMemory : MemorySemantics.State}
      {account : AccountState.Account} {bytes : List UInt8} {result : Semantics.Result Semantics.Value}
      (found : StorageSemantics.get world (address target) complete = .ok account) (known : account.code = some bytes)
      (copied : MemoryCopySemantics.From (packed bytes) destination source length memory result finalMemory) :
      Builtin world complete balances current "extcodecopy" type [.word target, .word destination, .word source, .word length]
        memory result finalMemory
  | hashFailure {type : Ty} {target reason : Word} {memory : MemorySemantics.State}
      (found : StorageSemantics.get world (address target) complete = .error reason) :
      Builtin world complete balances current "extcodehash" type [.word target] memory (failure reason) memory
  | hashUnknown {type : Ty} {target : Word} {memory : MemorySemantics.State} {account : AccountState.Account}
      (found : StorageSemantics.get world (address target) complete = .ok account) (unknown : account.code = none) :
      Builtin world complete balances current "extcodehash" type [.word target] memory unknownCode memory
  | hashEmpty {type : Ty} {target : Word} {memory : MemorySemantics.State} {account : AccountState.Account} {bytes : List UInt8}
      (found : StorageSemantics.get world (address target) complete = .ok account) (known : account.code = some bytes)
      (empty : emptyAccount account bytes (StorageSemantics.readWord (address target) balances) = true) :
      Builtin world complete balances current "extcodehash" type [.word target] memory (.value (.word Word.zero)) memory
  | hashKnown {type : Ty} {target : Word} {memory scratchFinal : MemorySemantics.State}
      {account : AccountState.Account} {bytes : List UInt8} {result : Semantics.Result Semantics.Value}
      (found : StorageSemantics.get world (address target) complete = .ok account) (known : account.code = some bytes)
      (nonempty : emptyAccount account bytes (StorageSemantics.readWord (address target) balances) = false)
      (hashed : KeccakSemantics.Hash Word.zero (codeSize bytes) ⟨packed bytes, Word.zero⟩ result scratchFinal) :
      Builtin world complete balances current "extcodehash" type [.word target] memory result memory

theorem Builtin.named {world : StorageSemantics.World} {complete : Bool} {balances : StorageSemantics.Words}
    {current : Word} {name : String} {type : Ty} {arguments : List Semantics.Value}
    {initial final : MemorySemantics.State} {result : Semantics.Result Semantics.Value}
    (evaluated : Builtin world complete balances current name type arguments initial result final) :
    ∃ operation : Operation, operation.name = name := by
  cases evaluated
  all_goals first
    | exact ⟨.balance, rfl⟩
    | exact ⟨.selfbalance, rfl⟩
    | exact ⟨.size, rfl⟩
    | exact ⟨.copy, rfl⟩
    | exact ⟨.hash, rfl⟩

end Solcore.Frontend.RustHull.AccountObservationSemantics
end

section
-- leanmerge: from Solcore.Frontend.RustHull.CodeImageSemantics
/-! Copying the current object's immutable code image uses packed source bytes.
The supplied image is an execution parameter and does not add mutable state. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.CodeImageSemantics
open Core

inductive Operation where
  | codeCopy | dataCopy
  deriving DecidableEq, Repr

def Operation.name : Operation → String
  | .codeCopy => "codecopy"
  | .dataCopy => "datacopy"

theorem Operation.name_injective : Function.Injective Operation.name := by
  intro first second same
  cases first <;> cases second <;> simp_all [Operation.name]

def unavailable : Semantics.Result Semantics.Value := .fault (.language (Word.ofNatModulo 15))

inductive Execute (image : Option (List UInt8)) (destination source length : Word) :
    MemorySemantics.State → Semantics.Result Semantics.Value → MemorySemantics.State → Prop where
  | unknown {state : MemorySemantics.State} (absent : image = none) :
      Execute image destination source length state unavailable state
  | copied {bytes : List UInt8} {initial final : MemorySemantics.State} {result : Semantics.Result Semantics.Value}
      (present : image = some bytes)
      (executed : MemoryCopySemantics.From (Memory.packBytes bytes) destination source length initial result final) :
      Execute image destination source length initial result final

inductive Builtin (image : Option (List UInt8)) : String → Ty → List Semantics.Value →
    MemorySemantics.State → Semantics.Result Semantics.Value → MemorySemantics.State → Prop where
  | copy (operation : Operation) {type : Ty} {destination source length : Word}
      {initial final : MemorySemantics.State} {result : Semantics.Result Semantics.Value}
      (executed : Execute image destination source length initial result final) :
      Builtin image operation.name type [.word destination, .word source, .word length] initial result final

theorem Builtin.named {image : Option (List UInt8)} {name : String} {type : Ty}
    {arguments : List Semantics.Value} {initial final : MemorySemantics.State} {result : Semantics.Result Semantics.Value}
    (called : Builtin image name type arguments initial result final) :
    ∃ operation : Operation, operation.name = name := by
  cases called with
  | copy operation _ => exact ⟨operation, rfl⟩

end Solcore.Frontend.RustHull.CodeImageSemantics
end

section
-- leanmerge: from Solcore.Frontend.RustHull.EnvironmentSemantics
/-! Immutable message, transaction and block observations for independent Hull
execution. Missing optional information remains distinct from a supplied zero. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.EnvironmentSemantics
open Core

inductive Direct where
  | address | caller | callvalue | calldataSize | returnDataSize
  deriving DecidableEq, Repr

def Direct.name : Direct → String
  | .address => "address" | .caller => "caller" | .callvalue => "callvalue"
  | .calldataSize => "calldatasize" | .returnDataSize => "returndatasize"

def Direct.slot : Direct → String
  | .calldataSize => "calldataSize" | .returnDataSize => "returnDataSize"
  | operation => operation.name

inductive AmbientWord where
  | origin | gasprice | coinbase | timestamp | number | prevrandao
  | gaslimit | chainid | basefee | blobbasefee
  deriving DecidableEq, Repr

def AmbientWord.name : AmbientWord → String
  | .origin => "origin" | .gasprice => "gasprice" | .coinbase => "coinbase"
  | .timestamp => "timestamp" | .number => "number" | .prevrandao => "prevrandao"
  | .gaslimit => "gaslimit" | .chainid => "chainid" | .basefee => "basefee" | .blobbasefee => "blobbasefee"

def AmbientWord.isAddress : AmbientWord → Bool
  | .origin | .coinbase => true | _ => false

inductive Operation where
  | direct (operation : Direct) | ambient (operation : AmbientWord)
  | gas | codeSize | calldataLoad | blockHash | blobHash
  deriving DecidableEq, Repr

def Operation.name : Operation → String
  | .direct operation => operation.name | .ambient operation => operation.name
  | .gas => "gas" | .codeSize => "codesize" | .calldataLoad => "calldataload"
  | .blockHash => "blockhash" | .blobHash => "blobhash"

def Operation.arity : Operation → Nat
  | .calldataLoad | .blockHash | .blobHash => 1 | _ => 0

structure State where
  direct : Direct → Word := fun _ => Word.zero
  ambient : AmbientWord → Option Word := fun _ => none
  gas : Option Word := none
  codeSize : Word := Word.zero
  codeKnown : Bool := false
  calldata : MemorySemantics.Entries := []
  blockHashes : Option MemorySemantics.Entries := none
  blobHashes : Option MemorySemantics.Entries := none

def available (reason : Nat) : Option Word → Semantics.Result Semantics.Value
  | none => .fault (.language (Word.ofNatModulo reason))
  | some value => .value (.word value)

def address (value : Word) : Word := value.bitAnd (Word.ofNatModulo (2 ^ 160 - 1))

def ambientWord (state : State) (operation : AmbientWord) : Semantics.Result Semantics.Value :=
  available 14 ((state.ambient operation).map fun value => if operation.isAddress then address value else value)

def blockHash (state : State) (index : Word) : Semantics.Result Semantics.Value :=
  match state.ambient .number, state.blockHashes with
  | some current, some hashes =>
      .value (.word (if current > index then
        if current.sub index > Word.ofNatModulo 256 then Word.zero else MemorySemantics.lookup index hashes
        else Word.zero))
  | _, _ => .fault (.language (Word.ofNatModulo 14))

def blobHash (state : State) (index : Word) : Semantics.Result Semantics.Value :=
  available 14 (state.blobHashes.map (MemorySemantics.lookup index))

def observe (state : State) (operation : Operation) (arguments : List Semantics.Value) :
    Option (Semantics.Result Semantics.Value) :=
  match operation, arguments with
  | .direct operation, [] => some (.value (.word (state.direct operation)))
  | .ambient operation, [] => some (ambientWord state operation)
  | .gas, [] => some (available 9 state.gas)
  | .codeSize, [] => some (if state.codeKnown then .value (.word state.codeSize)
      else .fault (.language (Word.ofNatModulo 15)))
  | .calldataLoad, [.word index] => some (.value (.word (MemorySemantics.readWord state.calldata index)))
  | .blockHash, [.word index] => some (blockHash state index)
  | .blobHash, [.word index] => some (blobHash state index)
  | _, _ => none

def operations : List Operation :=
  [.direct .address, .direct .caller, .direct .callvalue, .direct .calldataSize, .direct .returnDataSize,
    .ambient .origin, .ambient .gasprice, .ambient .coinbase, .ambient .timestamp,
    .ambient .number, .ambient .prevrandao, .ambient .gaslimit, .ambient .chainid,
    .ambient .basefee, .ambient .blobbasefee, .gas, .codeSize, .calldataLoad, .blockHash, .blobHash]

def builtin (name : String) (_type : Ty) (arguments : List Semantics.Value)
    (state : State) : Option (Semantics.Result Semantics.Value × State) := do
  let operation ← operations.find? (fun operation => operation.name == name)
  let result ← observe state operation arguments
  some (result, state)

def effects : Semantics.ExternalSemantics State where
  builtin := fun name type arguments initial result final =>
    builtin name type arguments initial = some (result, final)
  assembly := fun _ _ _ _ _ _ => False
  revert := fun _ _ _ _ => False

end Solcore.Frontend.RustHull.EnvironmentSemantics
end

section
-- leanmerge: from Solcore.Frontend.RustHull.LogsSemantics
/-! Independent event capture. The stream contains word-sized headers and
zero-padded payload snapshots. The copy relation describes byte ranges using
only mathematical words and source memory; it contains no compiled code. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.LogsSemantics
open Core

abbrev Words := MemorySemantics.Entries

def wordCount (length : Word) : Word :=
  (length.udiv (Word.ofNatModulo 32)).add
    (if length.umod (Word.ofNatModulo 32) == Word.zero then Word.zero else Word.ofNatModulo 1)

def chunk (length : Word) : Word :=
  if length > Word.ofNatModulo 31 then Word.ofNatModulo 32 else length

def padding (length : Word) : Word :=
  ((Word.ofNatModulo 32).sub (chunk length)).mul (Word.ofNatModulo 8)

def paddedWord (memory : Words) (offset length : Word) : Word :=
  ((MemorySemantics.readWord memory offset).shiftRight (padding length)).shiftLeft (padding length)

def insertWords (mapping : Words) (cursor : Word) : List Word → Words
  | [] => mapping
  | value :: rest => insertWords (MemorySemantics.insert cursor value mapping)
      (cursor.add (Word.ofNatModulo 1)) rest

/-- Payload words are copied from one immutable memory snapshot. Each step
advances by the actual number of bytes in its word and clears trailing bytes. -/
inductive Copy (memory : Words) : Word → Word → Words → Word → Words → Prop where
  | empty (offset cursor : Word) (mapping : Words) : Copy memory offset Word.zero mapping cursor mapping
  | step {offset length cursor : Word} {mapping result : Words}
      (nonempty : length ≠ Word.zero)
      (rest : Copy memory (offset.add (chunk length)) (length.sub (chunk length))
        (MemorySemantics.insert cursor (paddedWord memory offset length) mapping)
        (cursor.add (Word.ofNatModulo 1)) result) :
      Copy memory offset length mapping cursor result

structure State where
  memory : MemorySemantics.State := {}
  words : Words := []
  cursor : Word := Word.zero
  address : Word := Word.zero
  isStatic : Bool := false
  exit : Word := Word.zero
  returnOffset : Word := Word.zero
  returnSize : Word := Word.zero
  deriving Repr

def nextCursor (cursor length : Word) (topics : List Word) : Word :=
  cursor.add ((Word.ofNatModulo (3 + topics.length)).add (wordCount length))

def headers (address length : Word) (topics : List Word) : List Word :=
  [address, Word.ofNatModulo topics.length, length] ++ topics

inductive Append (offset length : Word) (topics : List Word) :
    State → Semantics.Result Semantics.Value → State → Prop where
  | topics {state : State} (tooMany : topics.length > 4) :
      Append offset length topics state (.fault (.language (Word.ofNatModulo 11))) state
  | capacity {state : State} (allowed : topics.length ≤ 4)
      (overflow : state.cursor > nextCursor state.cursor length topics) :
      Append offset length topics state (.fault (.language (Word.ofNatModulo 10))) state
  | memory {state : State} (allowed : topics.length ≤ 4)
      (capacity : ¬state.cursor > nextCursor state.cursor length topics)
      (overflow : MemorySemantics.touchSize? state.memory.size offset length = none) :
      Append offset length topics state MemorySemantics.overflow state
  | done {state : State} {size : Word} {words : Words} (allowed : topics.length ≤ 4)
      (capacity : ¬state.cursor > nextCursor state.cursor length topics)
      (expanded : MemorySemantics.touchSize? state.memory.size offset length = some size)
      (copied : Copy state.memory.words offset length
        (insertWords state.words state.cursor (headers state.address length topics))
        (state.cursor.add (Word.ofNatModulo (3 + topics.length))) words) :
      Append offset length topics state (.value .unit)
        {state with
          memory := {state.memory with size := size}
          words := words
          cursor := nextCursor state.cursor length topics}

inductive Operation where | log0 | log1 | log2 | log3 | log4
  deriving DecidableEq

def Operation.name : Operation → String
  | .log0 => "log0" | .log1 => "log1" | .log2 => "log2" | .log3 => "log3" | .log4 => "log4"

def Operation.count : Operation → Nat
  | .log0 => 0 | .log1 => 1 | .log2 => 2 | .log3 => 3 | .log4 => 4

inductive Execute (offset length : Word) (topics : List Word) :
    State → Semantics.Result Semantics.Value → State → Prop where
  | static {state : State} (readOnly : state.isStatic = true) :
      Execute offset length topics state (.fault (.language Word.maximum))
        {state with exit := Word.ofNatModulo 3, returnOffset := Word.zero, returnSize := Word.zero}
  | writable {state final : State} {result : Semantics.Result Semantics.Value}
      (writable : state.isStatic = false) (appended : Append offset length topics state result final) :
      Execute offset length topics state result final

inductive Builtin : String → Ty → List Semantics.Value →
    State → Semantics.Result Semantics.Value → State → Prop where
  | log (operation : Operation) (type : Ty) (offset length : Word) (topics : List Word)
      {initial final : State} {result : Semantics.Result Semantics.Value}
      (count : topics.length = operation.count)
      (executed : Execute offset length topics initial result final) :
      Builtin operation.name type (.word offset :: .word length :: topics.map Semantics.Value.word) initial result final

def effects : Semantics.ExternalSemantics State where
  builtin := Builtin
  assembly := fun _ _ _ _ _ _ => False
  revert := fun _ _ _ _ => False

end Solcore.Frontend.RustHull.LogsSemantics
end
