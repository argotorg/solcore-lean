import Solcore.Frontend.RustHull.AccountRuntime
import Solcore.Frontend.RustHull.Semantics.Frames
import Solcore.Core.ByteSelection
import Solcore.Frontend.RustHull.Internal.Digests
import Solcore.Frontend.RustHull.Internal.MemoryState
import Solcore.Frontend.RustHull.Internal.StorageState
import Solcore.Frontend.RustHull.Internal.AccountCalls
import Solcore.Frontend.RustHull.Internal.CallTransport

/-!
# Creation

Address derivation, preimages, handlers and transport of CREATE and CREATE2.
-/

section
-- leanmerge: from Solcore.Frontend.RustHull.CreationImplementation
/-! `Effects`, `Creation`, `CreationRuntime` and `AccountRuntime` keep the
creation builders private. This module restates them with public builders and
proves each restatement by `rfl`, so the implementation files stay unchanged. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.CreationImplementation
open Core CodeBuilder

/-- The actual CREATE/CREATE2 lowering after argument packing. -/
def lowerCreate (scope : Scope) (create2 : Bool)
    (value offset length salt : Core.Expr) : LowerM Lowered := do
  let isStatic := Core.Expr.loadCell (← Effects.reference scope "isStatic" .bool)
  let invalid ← Effects.terminate scope 3 (.word Core.Word.zero) (.word Core.Word.zero)
  let invalidWord := Core.LanguageResult.bind .word invalid
    (Core.LanguageResult.success (.word Core.Word.zero))
  let gas := Core.Expr.loadCell (← Effects.reference scope "availableGas" (.sum .unit .word))
  let inner := scope.temporary .word
  let invoke := Creation.invoke
    (← Effects.reference inner "memory" Core.WordMapping.type) (← Effects.reference inner "memorySize" .word)
    (← Effects.reference inner "returnData" Core.WordMapping.type) (← Effects.reference inner "returnDataSize" .word)
    (← Effects.reference inner "createHandler" (Core.OptionalCell.cellType Creation.callbackType))
    (.loadCell (← Effects.reference inner "address" .word))
    (.loadCell (← Effects.reference inner "callDepth" .word))
    (value.weakenAt 0) (salt.weakenAt 0) (.bool create2) (.var 0)
    (offset.weakenAt 0) (length.weakenAt 0)
  let withGas := Core.Expr.caseE gas
    (Core.LanguageResult.failure .word (.word (Core.Word.ofNatModulo 9))) invoke
  pure ⟨.word, .ifE isStatic invalidWord
    (.ifE (.binary .wordGt length (.word (Core.Word.ofNatModulo 49152))) invalidWord withGas)⟩

theorem lowerBuiltin_create (scope : Scope) (value offset length : Core.Expr) :
    Effects.lowerBuiltin scope "create" [value, offset, length] =
      Except.bind (lowerCreate scope false value offset length (.word Word.zero)) Except.ok := rfl

theorem lowerBuiltin_create2 (scope : Scope) (value offset length salt : Core.Expr) :
    Effects.lowerBuiltin scope "create2" [value, offset, length, salt] =
      Except.bind (lowerCreate scope true value offset length salt) Except.ok := rfl

/-- Field `index` of the thirteen-field invocation packet bound at depth zero:
memory, memory size, return data, return-data size, callback cell, creator,
current depth, value, salt, CREATE2 flag, gas, init offset and init length. -/
def input (index : Nat) : Code := part index 13 (fun depth => .var depth)

def finish (result : Code) : Code :=
  bind (store (input 2) (fun depth => Creation.responseField 1 (result depth))) fun _ =>
  bind (store (input 3) (fun depth => Creation.responseField 2 (result depth))) fun _ =>
  success (fun depth => Creation.responseField 0 (result depth))

/-- The request passed to the creation callback; `initCode` holds the copied
init bytes. -/
def request (initCode : Code) : Code :=
  packet [address (input 5), input 7, input 8, input 9, binary .wordAdd (input 6) (number 1),
    input 10, load initCode, input 12]

def dispatch : Code :=
  bind (load (input 0)) fun snapshot =>
  bind (allocate WordMapping.type empty) fun initCode =>
  bind (allocate .word (number 0)) fun size =>
  bindResult .word (fun depth => Memory.copyPackedFrom (initCode depth) (size depth) (number 0 depth)
    (snapshot depth) (input 11 depth) (input 12 depth)) fun _ =>
  bindResult .word (fun depth =>
    OptionalCell.read Creation.callbackType (input 4 depth) Creation.unavailableReason) fun function =>
  bindResult .word (apply function (request initCode)) finish

def invokeCode : Code :=
  bindResult .word (fun depth => Memory.touch (input 1 depth) (input 11 depth) (input 12 depth)) fun _ =>
  bind (store (input 2) empty) fun _ =>
  bind (store (input 3) (number 0)) fun _ =>
  choose (binary .wordGt (input 6) (number (Creation.depthLimit - 1))) (success (number 0)) dispatch

theorem invoke_eq (memoryReference sizeReference returnDataReference returnSizeReference
    callbackReference creatorAddress depth transferredValue saltValue isCreate2 suppliedGas
    offset length : Core.Expr) :
    Creation.invoke memoryReference sizeReference returnDataReference returnSizeReference
      callbackReference creatorAddress depth transferredValue saltValue isCreate2 suppliedGas offset length =
      .letE (bundle [memoryReference, sizeReference, returnDataReference, returnSizeReference,
        callbackReference, creatorAddress, depth, transferredValue, saltValue, isCreate2,
        suppliedGas, offset, length]) (invokeCode 0) := rfl

def response (address data size : Code) : Code := success (packet [address, data, size])
def refused : Code := response (number 0) empty (number 0)

def checkpoint (references : List Code) (continuation : Code → Code) : Code :=
  let rec capture : List Code → List (Code × Code) → Code
    | [], saved =>
        continuation (saved.foldr (fun (cell, value) next =>
          bind (store cell value) (fun _ => next)) unit)
    | reference :: rest, saved => bind (load reference) fun value =>
        capture rest ((reference, value) :: saved)
  capture references []

def protect (restore attempt : Code) : Code := fun depth =>
  .caseE (attempt depth)
    ((bind restore fun _ => failure Creation.responseType
      (fun here => .var (here - depth - 1))) (depth + 1))
    (LanguageResult.success (.var 0))

def deriveAddress (creator nonce request : Code) : Code :=
  choose (part 3 8 request)
    (bind (allocate WordMapping.type (part 6 8 request)) fun memory =>
      bind (allocate .word (number 0)) fun size =>
      fun depth => Creation.create2Address (memory depth) (size depth) (creator depth)
        (part 2 8 request depth) (number 0 depth) (part 7 8 request depth))
    (fun depth => Creation.createAddress (creator depth) (nonce depth))

def transfer (balances creator target value creatorBalance : Code) : Code :=
  choose (binary .wordEq value (number 0)) (success unit) <|
  bindResult .unit (lookup (load balances) target) fun targetBalance =>
  choose (binary .wordGt targetBalance (binary .wordSub (number (wordModulus - 1)) value))
    (failure .unit (number 12)) <|
  bindResult .unit (insert (load balances) creator (binary .wordSub creatorBalance value)) fun debited =>
  bindResult .unit (insert debited target (binary .wordAdd targetBalance value)) fun credited =>
  success (store balances credited)

/-- A new account at an unused target: insert the record, move the endowment,
run init code unless it is empty, validate the returned image and install it.
Failures after the checkpoint restore it. -/
def deployment (runInit installRuntime : Code → Code → Code)
    (world balances creator value creatorBalance request target restore : Code) : Code :=
  let rollback (result : Code) := bind restore fun _ => result
  bindResult Creation.responseType (fun depth => AccountState.put (load world depth) (target depth)
    (AccountState.replace (AccountState.replace AccountState.defaultRecord 2 (number 1 depth)) 7 (.bool true))) fun inserted =>
  bind (store world inserted) fun _ =>
  bindResult Creation.responseType (transfer balances creator target value creatorBalance) fun _ =>
  bindResult Creation.responseType
    (choose (binary .wordEq (part 7 8 request) (number 0))
      (success (packet [CodeBuilder.boolean true, empty, number 0])) (runInit target request)) fun child =>
  choose (part 0 3 child)
    (choose (binary .wordGt (part 2 3 child) (number 24576)) (rollback refused) <|
      bindResult Creation.responseType (fun depth =>
        Memory.readMemoryByte (part 1 3 child depth) (number 0 depth)) fun first =>
      let invalidPrefix := choose (binary .wordGt (part 2 3 child) (number 0))
        (binary .wordEq first (number 0xef)) (CodeBuilder.boolean false)
      choose invalidPrefix (rollback refused) <|
      bindResult Creation.responseType (installRuntime target child) fun _ =>
      response target empty (number 0))
    (rollback (response (number 0) (part 1 3 child) (part 2 3 child)))

/-- The checks on the target after the checkpoint: an account with a nonzero
nonce or code size is a collision, and unknown code is failure 7. -/
def attempt (runInit installRuntime : Code → Code → Code)
    (world balances complete creator value creatorBalance request target restore : Code) : Code :=
  bindResult Creation.responseType (fun depth => AccountState.get (load world depth) (target depth)
    (complete depth)) fun existing =>
  choose (binary .wordGt (part 2 9 existing) (number 0)) refused <|
  choose (binary .wordGt (part 5 9 existing) (number 0)) refused <|
  choose (part 6 9 existing)
    (deployment runInit installRuntime world balances creator value creatorBalance request target restore)
    (failure Creation.responseType (number 7))

/-- The dispatcher after both refusal checks: address derivation, the nonce
increment, the checkpoint and the attempt on the target. `args` binds the six
dispatcher arguments; the balance and creator record are the values already
read by the checks. -/
def admitted (runInit installRuntime : Code → Code → Code)
    (args creatorBalance creatorRecord : Code) : Code :=
  let world := part 0 6 args
  let balances := part 1 6 args
  let logs := part 2 6 args
  let logSize := part 3 6 args
  let complete := part 4 6 args
  let request := part 5 6 args
  let creator := address (part 0 8 request)
  let value := part 1 8 request
  let nonce := part 2 9 creatorRecord
  bindResult Creation.responseType (deriveAddress creator nonce request) fun target =>
  bindResult Creation.responseType (fun depth => AccountState.writeField (world depth) (creator depth)
    (complete depth) 2 (binary .wordAdd nonce (number 1) depth)) fun _ =>
  checkpoint [world, balances, logs, logSize] fun restore =>
  protect restore
    (attempt runInit installRuntime world balances complete creator value creatorBalance request target restore)

/-- The dispatcher's funds check and creator-nonce check, before `rest`. -/
def dispatchWith (worldReference balancesReference logsReference logSizeReference complete request : Code)
    (rest : Code → Code → Code → Code) : Code :=
  bind (packet [worldReference, balancesReference, logsReference, logSizeReference, complete, request]) fun args =>
  let world := part 0 6 args
  let balances := part 1 6 args
  let complete := part 4 6 args
  let request := part 5 6 args
  let creator := address (part 0 8 request)
  let value := part 1 8 request
  bindResult Creation.responseType (lookup (load balances) creator) fun creatorBalance =>
  choose (binary .wordGt value creatorBalance) refused <|
  bindResult Creation.responseType (fun depth =>
    AccountState.get (load world depth) (creator depth) (complete depth)) fun creatorRecord =>
  choose (binary .wordGt (part 2 9 creatorRecord) (number (2 ^ 64 - 2))) refused <|
  rest args creatorBalance creatorRecord

theorem dispatch_eq (worldReference balancesReference logsReference logSizeReference complete request : Code)
    (runInit installRuntime : Code → Code → Code) :
    CreationRuntime.dispatch worldReference balancesReference logsReference logSizeReference complete request
      runInit installRuntime =
      dispatchWith worldReference balancesReference logsReference logSizeReference complete request
        (admitted runInit installRuntime) := rfl

/-- Runtime-image installation: an empty image has identity zero, any other
image is identified by `identify`, and the identity and exact bytes are
recorded in the target's account record. -/
def installWith (identify : Code → Code) (shared : AccountRuntime.References) (target response : Code) : Code :=
  bindResult .unit
    (choose (binary .wordEq (part 2 3 response) (number 0)) (success (number 0)) (identify response)) fun identity =>
  bindResult .unit (AccountRuntime.worldGet shared target) fun record =>
  let updated := fun depth =>
    AccountState.replace (AccountState.replace (AccountState.replace
      (AccountState.replace (record depth) 3 (identity depth))
      4 (part 1 3 response depth)) 5 (part 2 3 response depth)) 6 (.bool true)
  bindResult .unit (fun depth => AccountState.put (load (AccountRuntime.reference shared "world") depth)
    (target depth) (updated depth)) fun world => success (store (AccountRuntime.reference shared "world") world)

/-- The create handler installed by the actual object initializer, with its
actual runtime installation. Init selection and the identification of a
nonempty runtime image stay abstract. -/
theorem objectHandlers_create (slots : List (String × Core.Ty)) (count : Nat)
    (images : List (Nat × List UInt8)) (catalog : List AccountRuntime.CodeDefinition)
    (functions : Code) (shared : AccountRuntime.References) (dispatcher creator : Code) :
    ∃ (runInit : Code → Code → Code) (identify : Code → Code),
      (AccountRuntime.objectHandlers slots count images catalog functions shared dispatcher creator).2 =
        lambda Creation.requestType (LanguageResult.resultType Creation.responseType) fun request =>
          CreationRuntime.dispatch (AccountRuntime.reference shared "world")
            (AccountRuntime.reference shared "balances") (AccountRuntime.reference shared "logs")
            (AccountRuntime.reference shared "logSize")
            (load (AccountRuntime.reference shared "worldComplete")) request runInit (installWith identify shared) :=
  ⟨_, _, rfl⟩

/-! The address builders of `Creation`, with their scratch memory. -/

def writeByte (memory size offset value : Code) : Code := fun depth =>
  Memory.mstore8 (memory depth) (size depth) (offset depth) (value depth)
def writeWord (memory size offset value : Code) : Code := fun depth =>
  Memory.mstore (memory depth) (size depth) (offset depth) (value depth)
def hash (memory size offset length : Code) : Code := fun depth =>
  Keccak.hash (memory depth) (size depth) (offset depth) (length depth)
def scratch (body : Code → Code → Code) : Code :=
  bind (allocate WordMapping.type empty) fun memory =>
  bind (allocate .word (number 0)) fun size => body memory size

/-- Hash the CREATE preimage and keep its low 160 bits. -/
def createFinish (memory size encodedLength : Code) : Code :=
  bindResult .word (hash memory size (number 0) (binary .wordAdd (number 22) encodedLength)) fun digest =>
    success (address digest)

/-- The RLP list header, the address header and the address. -/
def createPrefix (creator memory size encodedLength rest : Code) : Code :=
  bindResult .word (writeByte memory size (number 0) (binary .wordAdd (number 213) encodedLength)) fun _ =>
  bindResult .word (writeByte memory size (number 1) (number 148)) fun _ =>
  bindResult .word (writeWord memory size (number 2) (binary .wordShl (address creator) (number 96))) fun _ =>
  rest

/-- The RLP of the nonce, then the hash. -/
def createTail (memory size nonce byteCount encodedLength : Code) : Code :=
  choose (binary .wordEq nonce (number 0))
    (bindResult .word (writeByte memory size (number 22) (number 128)) fun _ =>
      createFinish memory size encodedLength)
    (choose (binary .wordGt nonce (number 127))
      (bindResult .word (writeByte memory size (number 22) (binary .wordAdd (number 128) byteCount)) fun _ =>
        bindResult .word (writeWord memory size (number 23)
          (binary .wordShl nonce (binary .wordMul (binary .wordSub (number 32) byteCount) (number 8)))) fun _ =>
        createFinish memory size encodedLength)
      (bindResult .word (writeByte memory size (number 22) nonce) fun _ =>
        createFinish memory size encodedLength))

def createAddressCode : Code :=
  let creator := part 0 2 (fun depth => .var depth)
  let nonce := part 1 2 (fun depth => .var depth)
  bind (binary .wordSub (number 32)
    (binary .wordDiv (fun depth => .unary .wordClz (nonce depth)) (number 8))) fun byteCount =>
  bind (choose (binary .wordGt nonce (number 127))
    (binary .wordAdd byteCount (number 1)) (number 1)) fun encodedLength =>
  scratch fun memory size =>
  createPrefix creator memory size encodedLength (createTail memory size nonce byteCount encodedLength)

theorem createAddress_eq (creator nonce : Core.Expr) :
    Creation.createAddress creator nonce = .letE (.pair creator nonce) (createAddressCode 0) := rfl

def create2AddressCode : Code :=
  let input (index : Nat) := part index 6 (fun depth => .var depth)
  bindResult .word (hash (input 0) (input 1) (input 4) (input 5)) fun initHash =>
  scratch fun memory size =>
  bindResult .word (writeByte memory size (number 0) (number 255)) fun _ =>
  bindResult .word (writeWord memory size (number 1) (binary .wordShl (address (input 2)) (number 96))) fun _ =>
  bindResult .word (writeWord memory size (number 21) (input 3)) fun _ =>
  bindResult .word (writeWord memory size (number 53) initHash) fun _ =>
  bindResult .word (hash memory size (number 0) (number 85)) fun digest => success (address digest)

theorem create2Address_eq (memoryReference sizeReference creator salt offset length : Core.Expr) :
    Creation.create2Address memoryReference sizeReference creator salt offset length =
      .letE (bundle [memoryReference, sizeReference, creator, salt, offset, length]) (create2AddressCode 0) := rfl

end Solcore.Frontend.RustHull.CreationImplementation
end

section
-- leanmerge: from Solcore.Frontend.RustHull.CreationBytes
/-! Byte reads of the source memory after byte and word writes, and the
independence of Keccak absorption from bytes outside the absorbed range. The
proofs compare individual bits of the packed big-endian words. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.CreationBytes
open Core


theorem modulus : wordModulus = 2 ^ 256 := rfl

theorem val_small {n : Nat} (small : n < 2 ^ 256) : (Word.ofNatModulo n).val = n := Nat.mod_eq_of_lt small

theorem val_bitAnd (a b : Word) : (a.bitAnd b).val = a.val &&& b.val :=
  Nat.mod_eq_of_lt (Nat.and_lt_two_pow _ b.isLt)

theorem val_bitOr (a b : Word) : (a.bitOr b).val = a.val ||| b.val :=
  Nat.mod_eq_of_lt (Nat.or_lt_two_pow a.isLt b.isLt)

theorem val_bitNot (a : Word) : a.bitNot.val = 2 ^ 256 - (a.val + 1) := by
  show (Word.maximum - a).val = _
  rw [Fin.sub_val_of_le (Fin.le_def.mpr (by show a.val ≤ wordModulus - 1; have := a.isLt; omega))]
  show wordModulus - 1 - a.val = _
  have := a.isLt
  change a.val < 2 ^ 256 at this
  change 2 ^ 256 - 1 - a.val = _
  omega

theorem val_shiftLeft (a s : Word) (small : s.val < 256) : (a.shiftLeft s).val = (a.val <<< s.val) % 2 ^ 256 := by
  simp only [Word.shiftLeft, small, ↓reduceIte]; rfl

theorem val_shiftRight (a s : Word) (small : s.val < 256) : (a.shiftRight s).val = a.val >>> s.val := by
  simp only [Word.shiftRight, small, ↓reduceIte]
  show (a.val >>> s.val) % wordModulus = _
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) a.isLt)

theorem val_byteAt (i a : Word) (small : i.val < 32) :
    (Word.byteAt i a).val = a.val / 2 ^ (8 * (31 - i.val)) % 2 ^ 8 := by
  simp only [Word.byteAt, small, ↓reduceIte]
  exact Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide))

theorem testBit_word (a : Word) {i : Nat} (large : 256 ≤ i) : a.val.testBit i = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le a.isLt (Nat.pow_le_pow_right (by decide) large))

/-- Byte `lane` of a word equals byte `lane'` of another when their bits agree there. -/
theorem byte_eq {x y : Nat} {s s' : Nat} (agree : ∀ t, t < 8 → x.testBit (s + t) = y.testBit (s' + t)) :
    x / 2 ^ s % 2 ^ 8 = y / 2 ^ s' % 2 ^ 8 := by
  apply Nat.eq_of_testBit_eq
  intro t
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases small : t < 8
  · simp only [small, decide_true, Bool.true_and]
    rw [Nat.add_comm t s, Nat.add_comm t s']
    exact agree t small
  · simp [small]


theorem lookup_insert_same (key value : Word) (entries : MemorySemantics.Entries) :
    MemorySemantics.lookup key (MemorySemantics.insert key value entries) = value := by
  induction entries with
  | nil => simp [MemorySemantics.insert, MemorySemantics.lookup]
  | cons entry rest ih =>
    rcases entry with ⟨stored, old⟩
    simp only [MemorySemantics.insert]
    split <;> simp_all [MemorySemantics.lookup]

theorem lookup_insert_other {key other : Word} (different : other ≠ key) (value : Word)
    (entries : MemorySemantics.Entries) :
    MemorySemantics.lookup other (MemorySemantics.insert key value entries) = MemorySemantics.lookup other entries := by
  induction entries with
  | nil => simp [MemorySemantics.insert, MemorySemantics.lookup, different]
  | cons entry rest ih =>
    rcases entry with ⟨stored, old⟩
    simp only [MemorySemantics.insert]
    by_cases same : key = stored
    · subst same
      simp [MemorySemantics.lookup, different]
    · simp only [beq_iff_eq, same, ↓reduceIte, MemorySemantics.lookup, ih]

theorem val_index (offset : Word) : (MemorySemantics.index offset).val = offset.val / 32 := by
  simp only [MemorySemantics.index, Word.udiv]
  rw [if_neg (by decide)]
  rfl

theorem val_position (offset : Word) : (MemorySemantics.position offset).val = offset.val % 32 := by
  simp only [MemorySemantics.position, Word.umod]
  rw [if_neg (by decide)]
  rfl

theorem testBit_lane (x s t : Nat) : (x / 2 ^ s % 2 ^ 8).testBit t = (decide (t < 8) && x.testBit (s + t)) := by
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.add_comm t s]

theorem testBit_255 (t : Nat) : (255 : Nat).testBit t = decide (t < 8) := by
  simpa using Nat.testBit_two_pow_sub_one 8 t

theorem val_distance (offset : Word) :
    (((Word.ofNatModulo 31).sub (MemorySemantics.position offset)).mul (Word.ofNatModulo 8)).val =
      8 * (31 - offset.val % 32) := by
  have thirtyOne : (Word.ofNatModulo 31).val = 31 := Nat.mod_eq_of_lt (by decide)
  have eight : (Word.ofNatModulo 8).val = 8 := Nat.mod_eq_of_lt (by decide)
  have below : offset.val % 32 < 32 := Nat.mod_lt _ (by decide)
  have small : (MemorySemantics.position offset) ≤ Word.ofNatModulo 31 := by
    rw [Fin.le_def, val_position, thirtyOne]; omega
  show ((Word.ofNatModulo 31 - MemorySemantics.position offset).val * (Word.ofNatModulo 8).val) % wordModulus = _
  rw [Fin.sub_val_of_le small, val_position, thirtyOne, eight]
  rw [Nat.mod_eq_of_lt (by change _ < 2 ^ 256; omega)]
  omega

theorem readByte_writeByte_same (entries : MemorySemantics.Entries) (offset value : Word) :
    MemoryCopySemantics.readByte (MemorySemantics.writeByte entries offset value) offset =
      value.bitAnd (Word.ofNatModulo 255) := by
  have positionSmall : (MemorySemantics.position offset).val < 32 := by
    rw [val_position]; exact Nat.mod_lt _ (by decide)
  have distance := val_distance offset
  unfold MemoryCopySemantics.readByte MemorySemantics.writeByte
  simp only [lookup_insert_same]
  apply Fin.ext
  rw [val_byteAt _ _ positionSmall, val_bitAnd, val_position, val_bitOr, val_bitAnd, val_bitNot,
    val_shiftLeft _ _ (by rw [distance]; omega), val_shiftLeft _ _ (by rw [distance]; omega), val_bitAnd, distance,
    val_small (show 255 < 2 ^ 256 by decide)]
  apply Nat.eq_of_testBit_eq
  intro t
  rw [testBit_lane]
  by_cases small : t < 8
  · have lane : 8 * (31 - offset.val % 32) + t < 256 := by omega
    simp only [small, decide_true, Bool.true_and, Nat.testBit_or, Nat.testBit_and,
      Nat.testBit_two_pow_sub_succ (Nat.mod_lt _ (by decide) : _ < 2 ^ 256), Nat.testBit_mod_two_pow,
      Nat.testBit_shiftLeft, lane, ge_iff_le, Nat.le_add_right, Nat.add_sub_cancel_left]
    simp only [testBit_255, small, decide_true, Bool.and_true, Bool.not_true, Bool.and_false, Bool.false_or]
  · simp [small, Nat.testBit_and, testBit_255]


theorem index_ne_of {offset other : Word} (different : (MemorySemantics.index other).val ≠ (MemorySemantics.index offset).val) :
    MemorySemantics.index other ≠ MemorySemantics.index offset := fun same => different (congrArg Fin.val same)

theorem readByte_writeByte_other (entries : MemorySemantics.Entries) {offset other : Word} (value : Word)
    (different : other ≠ offset) :
    MemoryCopySemantics.readByte (MemorySemantics.writeByte entries offset value) other =
      MemoryCopySemantics.readByte entries other := by
  have distance := val_distance offset
  have otherSmall : (MemorySemantics.position other).val < 32 := by
    rw [val_position]; exact Nat.mod_lt _ (by decide)
  unfold MemoryCopySemantics.readByte MemorySemantics.writeByte
  by_cases sameIndex : other.val / 32 = offset.val / 32
  · have keys : MemorySemantics.index other = MemorySemantics.index offset := Fin.ext (by rw [val_index, val_index, sameIndex])
    rw [keys, lookup_insert_same]
    have lanes : other.val % 32 ≠ offset.val % 32 := by
      intro same
      apply different
      apply Fin.ext
      have := Nat.div_add_mod other.val 32
      have := Nat.div_add_mod offset.val 32
      omega
    apply Fin.ext
    rw [val_byteAt _ _ otherSmall, val_byteAt _ _ otherSmall, val_position, val_bitOr, val_bitAnd, val_bitNot,
      val_shiftLeft _ _ (by rw [distance]; omega), val_shiftLeft _ _ (by rw [distance]; omega), val_bitAnd, distance,
      val_small (show 255 < 2 ^ 256 by decide)]
    apply Nat.eq_of_testBit_eq
    intro t
    rw [testBit_lane, testBit_lane]
    by_cases small : t < 8
    · have bound : 8 * (31 - other.val % 32) + t < 256 := by omega
      have otherLane := Nat.mod_lt other.val (show 32 > 0 by decide)
      have offsetLane := Nat.mod_lt offset.val (show 32 > 0 by decide)
      simp only [small, decide_true, Bool.true_and, Nat.testBit_or, Nat.testBit_and,
        Nat.testBit_two_pow_sub_succ (Nat.mod_lt _ (by decide) : _ < 2 ^ 256), Nat.testBit_mod_two_pow,
        Nat.testBit_shiftLeft, bound, testBit_255]
      by_cases above : 8 * (31 - offset.val % 32) ≤ 8 * (31 - other.val % 32) + t
      · have far : ¬(8 * (31 - other.val % 32) + t - 8 * (31 - offset.val % 32) < 8) := by omega
        simp [above, far]
      · simp [above]
    · simp [small]
  · rw [lookup_insert_other (index_ne_of (by rw [val_index, val_index]; exact sameIndex))]


theorem testBit_ones (k : Nat) : (2 ^ 256 - 1).testBit k = decide (k < 256) := Nat.testBit_two_pow_sub_one 256 k

/-- Lane `lane` of `(first & ~mask) | (value >> 8r)` with `mask = ones >> 8r`. -/
theorem lane_high (first value : Word) {r lane : Nat} (rSmall : r < 32) (laneSmall : lane < 32) :
    (first.val &&& (2 ^ 256 - ((2 ^ 256 - 1) >>> (8 * r) + 1)) ||| value.val >>> (8 * r)) / 2 ^ (8 * (31 - lane)) % 2 ^ 8 =
      if r ≤ lane then value.val / 2 ^ (8 * (31 - (lane - r))) % 2 ^ 8
      else first.val / 2 ^ (8 * (31 - lane)) % 2 ^ 8 := by
  have maskSmall : (2 ^ 256 - 1) >>> (8 * r) < 2 ^ 256 :=
    Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) (by decide)
  split
  · apply byte_eq
    intro t small
    have bound : 8 * (31 - lane) + t < 256 := by omega
    simp only [Nat.testBit_or, Nat.testBit_and, Nat.testBit_two_pow_sub_succ maskSmall, Nat.testBit_shiftRight,
      testBit_ones, bound]
    have inside : 8 * r + (8 * (31 - lane) + t) < 256 := by omega
    simp only [inside, decide_true, Bool.not_true, Bool.and_false, Bool.false_or]
    congr 1
    omega
  · apply byte_eq
    intro t small
    have bound : 8 * (31 - lane) + t < 256 := by omega
    have outside : ¬(8 * r + (8 * (31 - lane) + t) < 256) := by omega
    simp only [Nat.testBit_or, Nat.testBit_and, Nat.testBit_two_pow_sub_succ maskSmall, Nat.testBit_shiftRight,
      testBit_ones, bound, outside, decide_true, decide_false, Bool.not_false, Bool.and_true]
    rw [testBit_word value (by omega), Bool.or_false]

/-- Lane `lane` of `(second & mask) | (value << (256 - 8r))`. -/
theorem lane_low (second value : Word) {r lane : Nat} (rPositive : 0 < r) (rSmall : r < 32) (laneSmall : lane < 32) :
    (second.val &&& (2 ^ 256 - 1) >>> (8 * r) ||| (value.val <<< (256 - 8 * r)) % 2 ^ 256) / 2 ^ (8 * (31 - lane)) % 2 ^ 8 =
      if lane < r then value.val / 2 ^ (8 * (31 - (32 + lane - r))) % 2 ^ 8
      else second.val / 2 ^ (8 * (31 - lane)) % 2 ^ 8 := by
  split
  · apply byte_eq
    intro t small
    have bound : 8 * (31 - lane) + t < 256 := by omega
    have outside : ¬(8 * r + (8 * (31 - lane) + t) < 256) := by omega
    have above : 256 - 8 * r ≤ 8 * (31 - lane) + t := by omega
    simp only [Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftRight, testBit_ones, outside, decide_false,
      Bool.and_false, Bool.false_or, Nat.testBit_mod_two_pow, bound, decide_true, Bool.true_and,
      Nat.testBit_shiftLeft, ge_iff_le, above]
    congr 1
    omega
  · apply byte_eq
    intro t small
    have bound : 8 * (31 - lane) + t < 256 := by omega
    have inside : 8 * r + (8 * (31 - lane) + t) < 256 := by omega
    have below : ¬(256 - 8 * r ≤ 8 * (31 - lane) + t) := by omega
    simp only [Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftRight, testBit_ones, inside, decide_true,
      Bool.and_true, Nat.testBit_mod_two_pow, bound, Bool.true_and, Nat.testBit_shiftLeft, ge_iff_le, below,
      decide_false, Bool.false_and, Bool.or_false]


theorem val_shift (offset : Word) : (MemorySemantics.shift offset).val = 8 * (offset.val % 32) := by
  have eight : (Word.ofNatModulo 8).val = 8 := Nat.mod_eq_of_lt (by decide)
  show ((MemorySemantics.position offset).val * (Word.ofNatModulo 8).val) % wordModulus = _
  rw [val_position, eight, Nat.mod_eq_of_lt (by have := Nat.mod_lt offset.val (show 32 > 0 by decide); change _ < 2 ^ 256; omega)]
  omega

theorem val_next (offset : Word) :
    ((MemorySemantics.index offset).add (Word.ofNatModulo 1)).val = offset.val / 32 + 1 := by
  show ((MemorySemantics.index offset).val + (Word.ofNatModulo 1).val) % wordModulus = _
  rw [val_index, show (Word.ofNatModulo 1).val = 1 from rfl]
  apply Nat.mod_eq_of_lt
  have := offset.isLt
  change offset.val < 2 ^ 256 at this
  change _ < 2 ^ 256
  omega

theorem readByte_writeWord (entries : MemorySemantics.Entries) (offset value other : Word) :
    MemoryCopySemantics.readByte (MemorySemantics.writeWord entries offset value) other =
      if offset.val ≤ other.val ∧ other.val < offset.val + 32 then
        Word.byteAt (Word.ofNatModulo (other.val - offset.val)) value
      else MemoryCopySemantics.readByte entries other := by
  have otherSmall : (MemorySemantics.position other).val < 32 := by
    rw [val_position]; exact Nat.mod_lt _ (by decide)
  have otherSplit := Nat.div_add_mod other.val 32
  have offsetSplit := Nat.div_add_mod offset.val 32
  have otherLane := Nat.mod_lt other.val (show 32 > 0 by decide)
  have offsetLane := Nat.mod_lt offset.val (show 32 > 0 by decide)
  have byteOf {position : Nat} (small : position < 32) (word : Word) :
      (Word.byteAt (Word.ofNatModulo position) word).val = word.val / 2 ^ (8 * (31 - position)) % 2 ^ 8 := by
    rw [val_byteAt _ _ (by rw [val_small (by omega)]; exact small), val_small (by omega)]
  unfold MemoryCopySemantics.readByte MemorySemantics.writeWord
  by_cases aligned : offset.val % 32 = 0
  · have test : (MemorySemantics.position offset == Word.zero) = true :=
      beq_iff_eq.mpr (Fin.ext (by rw [val_position]; exact aligned))
    simp only [test, ↓reduceIte]
    by_cases sameIndex : other.val / 32 = offset.val / 32
    · have keys : MemorySemantics.index other = MemorySemantics.index offset :=
        Fin.ext (by rw [val_index, val_index, sameIndex])
      rw [keys, lookup_insert_same, if_pos (by omega)]
      apply Fin.ext
      rw [val_byteAt _ _ otherSmall, byteOf (by omega), val_position]
      congr 3
      omega
    · rw [lookup_insert_other (index_ne_of (by rw [val_index, val_index]; exact sameIndex)), if_neg (by omega)]
  · have test : (MemorySemantics.position offset == Word.zero) = false :=
      beq_eq_false_iff_ne.mpr (fun same => aligned (by rw [← val_position, same]; rfl))
    simp only [test, Bool.false_eq_true, ↓reduceIte]
    have distance := val_shift offset
    have distanceSmall : (MemorySemantics.shift offset).val < 256 := by omega
    have complement : ((Word.ofNatModulo 256).sub (MemorySemantics.shift offset)).val = 256 - 8 * (offset.val % 32) := by
      have below : MemorySemantics.shift offset ≤ Word.ofNatModulo 256 := by
        rw [Fin.le_def, distance, show (Word.ofNatModulo 256).val = 256 from rfl]; omega
      show (Word.ofNatModulo 256 - MemorySemantics.shift offset).val = _
      rw [Fin.sub_val_of_le below, distance]; rfl
    have ones : (Word.ofNatModulo (wordModulus - 1)).val = 2 ^ 256 - 1 := Nat.mod_eq_of_lt (by decide)
    have maskValue : ((Word.ofNatModulo (wordModulus - 1)).shiftRight (MemorySemantics.shift offset)).val =
        (2 ^ 256 - 1) >>> (8 * (offset.val % 32)) := by
      rw [val_shiftRight _ _ distanceSmall, ones, distance]
    have nextIndex : (MemorySemantics.index offset).add (Word.ofNatModulo 1) ≠ MemorySemantics.index offset := by
      intro same
      have := congrArg Fin.val same
      rw [val_next, val_index] at this
      omega
    by_cases sameIndex : other.val / 32 = offset.val / 32
    · have keys : MemorySemantics.index other = MemorySemantics.index offset :=
        Fin.ext (by rw [val_index, val_index, sameIndex])
      rw [keys, lookup_insert_other (Ne.symm nextIndex), lookup_insert_same]
      apply Fin.ext
      rw [val_byteAt _ _ otherSmall, val_position, val_bitOr, val_bitAnd, val_bitNot, maskValue,
        val_shiftRight _ _ distanceSmall, distance, lane_high _ _ offsetLane otherLane]
      by_cases inside : offset.val % 32 ≤ other.val % 32
      · rw [if_pos inside, if_pos (by omega), byteOf (by omega)]
        congr 3
        omega
      · rw [if_neg inside, if_neg (by omega), val_byteAt _ _ otherSmall, val_position]
    · by_cases nextSame : other.val / 32 = offset.val / 32 + 1
      · have keys : MemorySemantics.index other = (MemorySemantics.index offset).add (Word.ofNatModulo 1) :=
          Fin.ext (by rw [val_index, val_next, nextSame])
        rw [keys, lookup_insert_same, lookup_insert_other nextIndex]
        apply Fin.ext
        rw [val_byteAt _ _ otherSmall, val_position, val_bitOr, val_bitAnd, maskValue,
          val_shiftLeft _ _ (by rw [complement]; omega), complement,
          lane_low _ _ (by omega) offsetLane otherLane]
        by_cases inside : other.val % 32 < offset.val % 32
        · rw [if_pos inside, if_pos (by omega), byteOf (by omega)]
          congr 3
          omega
        · rw [if_neg inside, if_neg (by omega), val_byteAt _ _ otherSmall, val_position, ← keys]
      · have notNext : MemorySemantics.index other ≠ (MemorySemantics.index offset).add (Word.ofNatModulo 1) := by
          intro same
          have := congrArg Fin.val same
          rw [val_index, val_next] at this
          exact nextSame this
        rw [lookup_insert_other notNext,
          lookup_insert_other (index_ne_of (by rw [val_index, val_index]; exact sameIndex)), if_neg (by omega)]


theorem readByte_writeByte (entries : MemorySemantics.Entries) (offset value other : Word) :
    MemoryCopySemantics.readByte (MemorySemantics.writeByte entries offset value) other =
      if other = offset then value.bitAnd (Word.ofNatModulo 255) else MemoryCopySemantics.readByte entries other := by
  split
  · rename_i same
    subst same
    exact readByte_writeByte_same entries other value
  · rename_i different
    exact readByte_writeByte_other entries value different

theorem readByte_empty (other : Word) : MemoryCopySemantics.readByte [] other = Word.zero := by
  simp [MemoryCopySemantics.readByte, MemorySemantics.lookup]

theorem byte_bitAnd {byte : Nat} (small : byte < 256) :
    (Word.ofNatModulo byte).bitAnd (Word.ofNatModulo 255) = Word.ofNatModulo byte := by
  apply Fin.ext
  rw [val_bitAnd, val_small (by omega), val_small (by decide)]
  rw [show (255 : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_eq_of_lt small

/-- Bytes written one at a time are read back in order; other addresses keep
their previous bytes. -/
theorem readByte_storeBytes (other : Word) :
    ∀ (bytes : CreationAddressSemantics.Bytes) (words : MemorySemantics.Entries) (index : Nat),
      index + bytes.length ≤ 2 ^ 256 →
      MemoryCopySemantics.readByte (CreationAddressSemantics.storeBytes words index bytes) other =
        if index ≤ other.val ∧ other.val < index + bytes.length then
          (Word.ofNatModulo (bytes.getD (other.val - index) 0)).bitAnd (Word.ofNatModulo 255)
        else MemoryCopySemantics.readByte words other := by
  intro bytes
  induction bytes with
  | nil =>
      intro words index _
      rw [if_neg (by simp)]
      rfl
  | cons byte rest ih =>
      intro words index fits
      simp only [CreationAddressSemantics.storeBytes, List.length_cons] at fits ⊢
      rw [ih _ (index + 1) (by omega), readByte_writeByte]
      by_cases here : other.val = index
      · have same : other = Word.ofNatModulo index := Fin.ext (by rw [val_small (by omega)]; exact here)
        rw [if_neg (by omega), if_pos same, if_pos (by omega), here, Nat.sub_self]
        rfl
      · have different : other ≠ Word.ofNatModulo index := fun same => here (by rw [same, val_small (by omega)])
        rw [if_neg different]
        by_cases later : index + 1 ≤ other.val ∧ other.val < index + 1 + rest.length
        · rw [if_pos later, if_pos (by omega)]
          congr 2
          rw [show other.val - index = (other.val - (index + 1)) + 1 by omega]
          rfl
        · rw [if_neg later, if_neg (by omega)]

theorem readByte_stored {bytes : CreationAddressSemantics.Bytes} (small : ∀ byte ∈ bytes, byte < 256)
    (fits : bytes.length ≤ 2 ^ 256) {index : Nat} (inside : index < bytes.length) :
    MemoryCopySemantics.readByte (CreationAddressSemantics.stored bytes) (Word.ofNatModulo index) =
      Word.ofNatModulo (bytes.getD index 0) := by
  unfold CreationAddressSemantics.stored
  rw [readByte_storeBytes _ bytes [] 0 (by omega), val_small (by omega), if_pos (by omega), Nat.sub_zero]
  apply byte_bitAnd
  have same : bytes.getD index 0 = bytes[index] := (List.getElem_eq_getD 0).symm
  rw [same]
  exact small _ (List.getElem_mem inside)

/-- Byte `lane` of a word shifted left by whole bytes. -/
theorem lane_shiftLeft (value : Word) {shift lane : Nat} (small : lane + shift < 32) :
    (value.val <<< (8 * shift)) % 2 ^ 256 / 2 ^ (8 * (31 - lane)) % 2 ^ 8 =
      value.val / 2 ^ (8 * (31 - (lane + shift))) % 2 ^ 8 := by
  apply byte_eq
  intro t inside
  have bound : 8 * (31 - lane) + t < 256 := by omega
  have above : 8 * shift ≤ 8 * (31 - lane) + t := by omega
  simp only [Nat.testBit_mod_two_pow, bound, decide_true, Bool.true_and, Nat.testBit_shiftLeft, ge_iff_le, above]
  congr 1
  omega

/-- The low 20 bytes of a word survive the 160-bit address mask. -/
theorem lane_mask (value : Word) {lane : Nat} (low : 12 ≤ lane) (small : lane < 32) :
    (value.val &&& (2 ^ 160 - 1)) / 2 ^ (8 * (31 - lane)) % 2 ^ 8 = value.val / 2 ^ (8 * (31 - lane)) % 2 ^ 8 := by
  apply byte_eq
  intro t inside
  have bound : 8 * (31 - lane) + t < 160 := by omega
  simp only [Nat.testBit_and, Nat.testBit_two_pow_sub_one, bound, decide_true, Bool.and_true]

/-! Keccak absorption reads only the bytes inside its range. -/


theorem paddedByte_congr {first second : MemorySemantics.Entries} {offset remaining : Word} {index : Nat}
    (small : index < 136)
    (agree : index < remaining.val →
      MemoryCopySemantics.readByte first (offset.add (Word.ofNatModulo index)) =
        MemoryCopySemantics.readByte second (offset.add (Word.ofNatModulo index))) :
    KeccakSemantics.paddedByte first offset remaining index = KeccakSemantics.paddedByte second offset remaining index := by
  unfold KeccakSemantics.paddedByte
  by_cases inside : remaining > Word.ofNatModulo index
  · have bound : index < remaining.val := by
      have := Fin.lt_def.mp inside
      rwa [val_small (by omega)] at this
    simp only [inside, ↓reduceIte, agree bound]
  · simp only [inside, ↓reduceIte]

theorem readLane_congr {first second : MemorySemantics.Entries} {offset remaining : Word}
    (agree : ∀ index, index < 136 → index < remaining.val →
      MemoryCopySemantics.readByte first (offset.add (Word.ofNatModulo index)) =
        MemoryCopySemantics.readByte second (offset.add (Word.ofNatModulo index))) :
    ∀ count index accumulator, index + count ≤ 136 →
      KeccakSemantics.readLane count index first offset remaining accumulator =
        KeccakSemantics.readLane count index second offset remaining accumulator := by
  intro count
  induction count with
  | zero => intro index accumulator _; rfl
  | succ count ih =>
      intro index accumulator bounded
      simp only [KeccakSemantics.readLane]
      rw [paddedByte_congr (by omega) (agree index (by omega))]
      exact ih (index + 1) _ (by omega)

theorem absorbBlock_congr {first second : MemorySemantics.Entries} {offset remaining : Word}
    (state : KeccakSemantics.State)
    (agree : ∀ index, index < 136 → index < remaining.val →
      MemoryCopySemantics.readByte first (offset.add (Word.ofNatModulo index)) =
        MemoryCopySemantics.readByte second (offset.add (Word.ofNatModulo index))) :
    KeccakSemantics.absorbBlock first offset remaining state = KeccakSemantics.absorbBlock second offset remaining state := by
  unfold KeccakSemantics.absorbBlock
  apply List.map_congr_left
  intro index member
  split
  · rename_i small
    rw [readLane_congr agree 8 (8 * index) Word.zero (by omega)]
  · rfl

theorem add_add (offset : Word) (step index : Nat) (small : step + index < 2 ^ 256) :
    (offset.add (Word.ofNatModulo step)).add (Word.ofNatModulo index) = offset.add (Word.ofNatModulo (step + index)) := by
  apply Fin.ext
  show ((offset.val + step % wordModulus) % wordModulus + index % wordModulus) % wordModulus =
    (offset.val + (step + index) % wordModulus) % wordModulus
  change ((offset.val + step % 2 ^ 256) % 2 ^ 256 + index % 2 ^ 256) % 2 ^ 256 =
    (offset.val + (step + index) % 2 ^ 256) % 2 ^ 256
  rw [Nat.mod_eq_of_lt (show step < 2 ^ 256 by omega), Nat.mod_eq_of_lt (show index < 2 ^ 256 by omega),
    Nat.mod_eq_of_lt small, Nat.mod_add_mod, Nat.add_assoc]

theorem Absorb.congr {first second : MemorySemantics.Entries} {offset remaining : Word}
    {state : KeccakSemantics.State} {result : Word}
    (absorbed : KeccakSemantics.Absorb first offset remaining state result)
    (agree : ∀ index, index < remaining.val →
      MemoryCopySemantics.readByte first (offset.add (Word.ofNatModulo index)) =
        MemoryCopySemantics.readByte second (offset.add (Word.ofNatModulo index))) :
    KeccakSemantics.Absorb second offset remaining state result := by
  induction absorbed with
  | last offset remaining state short =>
      rw [absorbBlock_congr state (fun index _ inside => agree index inside)]
      exact .last offset remaining state short
  | more full rest ih =>
      rename_i offset remaining state result
      have large : 136 ≤ remaining.val := by
        have := Nat.not_lt.mp (fun lt => full (Fin.lt_def.mpr (by rw [val_small (by decide)]; exact lt)))
        exact this
      have remainingSub : (remaining.sub (Word.ofNatModulo 136)).val = remaining.val - 136 := by
        show (remaining - Word.ofNatModulo 136).val = _
        rw [Fin.sub_val_of_le (Fin.le_def.mpr (by rw [val_small (by decide)]; exact large)), val_small (by decide)]
      have same := absorbBlock_congr state (fun index _ inside => agree index inside)
      refine .more full ?_
      rw [← same]
      refine ih ?_
      intro index inside
      rw [remainingSub] at inside
      have remainingSmall := remaining.isLt
      change remaining.val < 2 ^ 256 at remainingSmall
      rw [add_add _ _ _ (by omega)]
      exact agree (136 + index) (by omega)

theorem Absorb.deterministic {words : MemorySemantics.Entries} {offset remaining : Word}
    {state : KeccakSemantics.State} {first second : Word}
    (left : KeccakSemantics.Absorb words offset remaining state first)
    (right : KeccakSemantics.Absorb words offset remaining state second) : first = second := by
  induction left generalizing second with
  | last offset remaining state short =>
      cases right with
      | last => rfl
      | more full => exact absurd short full
  | more full rest ih =>
      cases right with
      | last _ _ _ short => exact absurd short full
      | more _ rest' => exact ih rest'

theorem Keccak.deterministic {bytes : CreationAddressSemantics.Bytes} {first second : Word}
    (left : CreationAddressSemantics.Keccak bytes first) (right : CreationAddressSemantics.Keccak bytes second) :
    first = second :=
  Absorb.deterministic left right

end Solcore.Frontend.RustHull.CreationBytes
end

section
-- leanmerge: from Solcore.Frontend.RustHull.CreationPreimage
/-! The CREATE and CREATE2 preimages as the actual address builders store them.
`createScratch` and `create2Scratch` replay, on source memory, the byte and
word writes of `Creation.createAddress` and `Creation.create2Address`. Their
bytes equal the independent RLP and CREATE2 preimages over the hashed range, so
their Keccak absorption is the specified Keccak-256 of those preimages. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.CreationPreimage
open Core CreationAddressSemantics CreationBytes

theorem getD_append_left {first second : List Nat} {index : Nat} (inside : index < first.length) :
    (first ++ second).getD index 0 = first.getD index 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left inside]

theorem getD_append_right {first second : List Nat} {index : Nat} (beyond : first.length ≤ index) :
    (first ++ second).getD index 0 = second.getD (index - first.length) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right beyond]

theorem bigEndian_zero : bigEndian 0 = [] := by
  rw [bigEndian]; simp

theorem bigEndian_pos {value : Nat} (positive : 0 < value) :
    bigEndian value = bigEndian (value / 256) ++ [value % 256] := by
  rw [bigEndian, if_neg (by omega)]

theorem bigEndian_upper (value : Nat) : value < 256 ^ (bigEndian value).length := by
  by_cases zero : value = 0
  · subst zero; rw [bigEndian_zero]; decide
  · rw [bigEndian_pos (by omega), List.length_append, List.length_singleton, Nat.pow_succ]
    have := bigEndian_upper (value / 256)
    exact (Nat.div_lt_iff_lt_mul (by decide)).mp this
termination_by value
decreasing_by omega

theorem bigEndian_lower (value : Nat) (positive : 0 < value) :
    256 ^ ((bigEndian value).length - 1) ≤ value := by
  rw [bigEndian_pos positive, List.length_append, List.length_singleton, Nat.add_sub_cancel]
  by_cases small : value < 256
  · rw [Nat.div_eq_of_lt small, bigEndian_zero]
    simp only [List.length_nil, Nat.pow_zero]
    omega
  · have lower := bigEndian_lower (value / 256) (by omega)
    have positiveLength : 0 < (bigEndian (value / 256)).length := by
      rw [bigEndian_pos (by omega)]; simp
    generalize (bigEndian (value / 256)).length = count at lower positiveLength ⊢
    obtain ⟨previous, rfl⟩ : ∃ previous, count = previous + 1 := ⟨count - 1, by omega⟩
    rw [Nat.add_sub_cancel] at lower
    rw [Nat.pow_succ]
    exact Nat.le_trans (Nat.mul_le_mul_right 256 lower) (Nat.div_mul_le_self value 256)
termination_by value
decreasing_by omega

theorem bigEndian_length {value : Nat} (positive : 0 < value) :
    (bigEndian value).length = Nat.log2 value / 8 + 1 := by
  have upper := bigEndian_upper value
  have lower := bigEndian_lower value positive
  have nonzero : value ≠ 0 := by omega
  have pow (count : Nat) : (256 : Nat) ^ count = 2 ^ (8 * count) := by
    rw [Nat.pow_mul]
  rw [pow] at upper lower
  have high := (Nat.log2_lt nonzero).mpr upper
  have low := (Nat.le_log2 nonzero).mpr lower
  have positiveLength : 0 < (bigEndian value).length := by
    rw [bigEndian_pos positive]; simp
  omega

theorem bigEndian_getD (value : Nat) :
    ∀ index, index < (bigEndian value).length →
      (bigEndian value).getD index 0 = value / 256 ^ ((bigEndian value).length - 1 - index) % 256 := by
  intro index inside
  by_cases zero : value = 0
  · subst zero; rw [bigEndian_zero] at inside; simp at inside
  · have unfolded := bigEndian_pos (value := value) (by omega)
    rw [unfolded] at inside ⊢
    rw [List.length_append, List.length_singleton] at inside ⊢
    by_cases last : index = (bigEndian (value / 256)).length
    · subst last
      rw [getD_append_right (Nat.le_refl _), Nat.sub_self]
      simp
    · rw [getD_append_left (by omega), bigEndian_getD (value / 256) index (by omega),
        Nat.div_div_eq_div_mul, ← Nat.pow_succ']
      congr 3
      omega
termination_by value
decreasing_by omega

theorem bigEndian_bytes (value : Nat) : ∀ byte ∈ bigEndian value, byte < 256 := by
  intro byte member
  by_cases zero : value = 0
  · subst zero; rw [bigEndian_zero] at member; simp at member
  · rw [bigEndian_pos (by omega)] at member
    rcases List.mem_append.mp member with rest | here
    · exact bigEndian_bytes (value / 256) byte rest
    · simp at here; omega
termination_by value
decreasing_by omega


theorem pow256 (count : Nat) : (256 : Nat) ^ count = 2 ^ (8 * count) := by
  rw [Nat.pow_mul]

theorem wordBytes_length (value : Word) : (wordBytes value).length = 32 := by
  simp [wordBytes]

theorem wordBytes_getD (value : Word) {index : Nat} (inside : index < 32) :
    (wordBytes value).getD index 0 = value.val / 256 ^ (31 - index) % 256 := by
  simp [wordBytes, List.getD_eq_getElem?_getD, inside]

theorem addressBytes_length (value : Word) : (addressBytes value).length = 20 := by
  simp [addressBytes, wordBytes_length]

theorem addressBytes_getD (value : Word) {index : Nat} (inside : index < 20) :
    (addressBytes value).getD index 0 = value.val / 256 ^ (19 - index) % 256 := by
  have shifted : (addressBytes value).getD index 0 = (wordBytes value).getD (12 + index) 0 := by
    simp [addressBytes, List.getD_eq_getElem?_getD, List.getElem?_drop]
  rw [shifted, wordBytes_getD _ (by omega)]
  congr 3
  omega

theorem encodeBytes_address (value : Word) : encodeBytes (addressBytes value) = 148 :: addressBytes value := by
  unfold encodeBytes
  rw [addressBytes_length]
  simp

def nonceBytes (nonce : Word) : Bytes := encodeBytes (bigEndian nonce.val)

theorem bigEndian_short {value : Nat} (positive : 0 < value) (small : value < 256) : bigEndian value = [value] := by
  rw [bigEndian_pos positive, Nat.div_eq_of_lt small, bigEndian_zero, Nat.mod_eq_of_lt small]
  rfl

theorem nonceBytes_zero {nonce : Word} (zero : nonce.val = 0) : nonceBytes nonce = [128] := by
  simp [nonceBytes, zero, bigEndian_zero, encodeBytes]

theorem nonceBytes_small {nonce : Word} (positive : 0 < nonce.val) (small : nonce.val < 128) :
    nonceBytes nonce = [nonce.val] := by
  simp [nonceBytes, bigEndian_short positive (by omega), encodeBytes, small]

theorem bigEndian_word_length (nonce : Word) (positive : 0 < nonce.val) :
    (bigEndian nonce.val).length ≤ 32 := by
  rw [bigEndian_length positive]
  have := (Nat.log2_lt (n := nonce.val) (k := 256) (by omega)).mpr nonce.isLt
  omega

theorem nonceBytes_large {nonce : Word} (large : 128 ≤ nonce.val) :
    nonceBytes nonce = (128 + (bigEndian nonce.val).length) :: bigEndian nonce.val := by
  have bounded := bigEndian_word_length nonce (by omega)
  unfold nonceBytes encodeBytes
  rw [if_neg, if_pos (by omega)]
  intro ⟨single, head⟩
  have upper := bigEndian_upper nonce.val
  rw [single] at upper
  rw [bigEndian_short (by omega) (by simpa using upper)] at head
  simp at head
  omega


theorem nonceBytes_length_le (nonce : Word) : (nonceBytes nonce).length ≤ 33 := by
  by_cases zero : nonce.val = 0
  · rw [nonceBytes_zero zero]; simp
  · by_cases small : nonce.val < 128
    · rw [nonceBytes_small (by omega) small]; simp
    · rw [nonceBytes_large (by omega)]
      have := bigEndian_word_length nonce (by omega)
      simp only [List.length_cons]
      omega

theorem createPreimage_eq (creator nonce : Word) :
    createPreimage creator nonce =
      (213 + (nonceBytes nonce).length) :: 148 :: (addressBytes creator ++ nonceBytes nonce) := by
  have bounded := nonceBytes_length_le nonce
  show encodeList [encodeBytes (addressBytes creator), nonceBytes nonce] = _
  rw [encodeBytes_address]
  unfold encodeList
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.length_cons,
    List.length_append, addressBytes_length]
  rw [if_pos (by omega)]
  congr 1
  omega

theorem createPreimage_length (creator nonce : Word) :
    (createPreimage creator nonce).length = 22 + (nonceBytes nonce).length := by
  rw [createPreimage_eq]
  simp only [List.length_cons, List.length_append, addressBytes_length]
  omega

theorem createPreimage_getD (creator nonce : Word) (index : Nat) :
    (createPreimage creator nonce).getD index 0 =
      if index = 0 then 213 + (nonceBytes nonce).length
      else if index = 1 then 148
      else if index < 22 then (addressBytes creator).getD (index - 2) 0
      else (nonceBytes nonce).getD (index - 22) 0 := by
  rw [createPreimage_eq]
  rcases index with _ | _ | index
  · simp
  · simp
  · rw [if_neg (by omega), if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_succ]
    rw [← List.getD_eq_getElem?_getD]
    by_cases small : index + 2 < 22
    · rw [if_pos small, getD_append_left (by rw [addressBytes_length]; omega)]
      rfl
    · rw [if_neg small, getD_append_right (by rw [addressBytes_length]; omega), addressBytes_length]
      congr 1

theorem createPreimage_bytes (creator nonce : Word) : ∀ byte ∈ createPreimage creator nonce, byte < 256 := by
  have bounded := nonceBytes_length_le nonce
  intro byte member
  rw [createPreimage_eq] at member
  simp only [List.mem_cons, List.mem_append] at member
  rcases member with rfl | rfl | address | nonceByte
  · omega
  · omega
  · simp only [addressBytes, wordBytes] at address
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp (List.mem_of_mem_drop address)
    exact Nat.mod_lt _ (by decide)
  · by_cases zero : nonce.val = 0
    · rw [nonceBytes_zero zero] at nonceByte; simp at nonceByte; omega
    · by_cases small : nonce.val < 128
      · rw [nonceBytes_small (by omega) small] at nonceByte; simp at nonceByte; omega
      · rw [nonceBytes_large (by omega)] at nonceByte
        simp only [List.mem_cons] at nonceByte
        rcases nonceByte with rfl | rest
        · have := bigEndian_word_length nonce (by omega); omega
        · exact bigEndian_bytes _ _ rest

def addressMask : Word := Word.ofNatModulo (2 ^ 160 - 1)

def byteCount (nonce : Word) : Word := (Word.ofNatModulo 32).sub (nonce.clz.udiv (Word.ofNatModulo 8))

def encodedLength (nonce : Word) : Word :=
  if nonce > Word.ofNatModulo 127 then (byteCount nonce).add (Word.ofNatModulo 1) else Word.ofNatModulo 1

def createLength (nonce : Word) : Word := (Word.ofNatModulo 22).add (encodedLength nonce)

def createPrefix (creator nonce : Word) : MemorySemantics.Entries :=
  MemorySemantics.writeWord
    (MemorySemantics.writeByte
      (MemorySemantics.writeByte [] (Word.ofNatModulo 0) ((Word.ofNatModulo 213).add (encodedLength nonce)))
      (Word.ofNatModulo 1) (Word.ofNatModulo 148))
    (Word.ofNatModulo 2) ((creator.bitAnd addressMask).shiftLeft (Word.ofNatModulo 96))

def createScratch (creator nonce : Word) : MemorySemantics.Entries :=
  if nonce == Word.ofNatModulo 0 then
    MemorySemantics.writeByte (createPrefix creator nonce) (Word.ofNatModulo 22) (Word.ofNatModulo 128)
  else if nonce > Word.ofNatModulo 127 then
    MemorySemantics.writeWord
      (MemorySemantics.writeByte (createPrefix creator nonce) (Word.ofNatModulo 22)
        ((Word.ofNatModulo 128).add (byteCount nonce)))
      (Word.ofNatModulo 23) (nonce.shiftLeft (((Word.ofNatModulo 32).sub (byteCount nonce)).mul (Word.ofNatModulo 8)))
  else MemorySemantics.writeByte (createPrefix creator nonce) (Word.ofNatModulo 22) nonce

theorem byteCount_val {nonce : Word} (positive : 0 < nonce.val) :
    (byteCount nonce).val = (bigEndian nonce.val).length := by
  have logSmall := (Nat.log2_lt (n := nonce.val) (k := 256) (by omega)).mpr nonce.isLt
  have clzValue : nonce.clz.val = 255 - Nat.log2 nonce.val := by
    simp only [Word.clz, show nonce.val ≠ 0 by omega, ↓reduceIte]
    exact val_small (by omega)
  have divided : (nonce.clz.udiv (Word.ofNatModulo 8)).val = (255 - Nat.log2 nonce.val) / 8 := by
    simp only [Word.udiv, show (Word.ofNatModulo 8).val ≠ 0 from by decide, ↓reduceIte]
    show nonce.clz.val / (Word.ofNatModulo 8).val = _
    rw [clzValue, val_small (by decide)]
  rw [bigEndian_length positive]
  show ((Word.ofNatModulo 32) - nonce.clz.udiv (Word.ofNatModulo 8)).val = _
  rw [Fin.sub_val_of_le (Fin.le_def.mpr (by rw [divided, val_small (by decide)]; omega)), divided, val_small (by decide)]
  omega

theorem encodedLength_val (nonce : Word) : (encodedLength nonce).val = (nonceBytes nonce).length := by
  unfold encodedLength
  by_cases large : nonce > Word.ofNatModulo 127
  · have bound : 128 ≤ nonce.val := by
      have := Fin.lt_def.mp large; rw [val_small (by decide)] at this; omega
    rw [if_pos large, nonceBytes_large bound]
    have := bigEndian_word_length nonce (by omega)
    show ((byteCount nonce).val + (Word.ofNatModulo 1).val) % wordModulus = _
    rw [byteCount_val (by omega), val_small (by decide), Nat.mod_eq_of_lt (by change _ < 2 ^ 256; omega)]
    simp
  · have bound : nonce.val < 128 := by
      have := Fin.not_lt.mp large; rw [Fin.le_def, val_small (by decide)] at this; omega
    rw [if_neg large]
    by_cases zero : nonce.val = 0
    · rw [nonceBytes_zero zero]; rfl
    · rw [nonceBytes_small (by omega) bound]; rfl

theorem createLength_val (creator nonce : Word) :
    (createLength nonce).val = (createPreimage creator nonce).length := by
  have := nonceBytes_length_le nonce
  show ((Word.ofNatModulo 22).val + (encodedLength nonce).val) % wordModulus = _
  rw [encodedLength_val, val_small (by decide), Nat.mod_eq_of_lt (by change _ < 2 ^ 256; omega), createPreimage_length]

theorem readByte_writeByte_at (entries : MemorySemantics.Entries) {position index : Nat} (value : Word)
    (positionSmall : position < 2 ^ 256) (indexSmall : index < 2 ^ 256) :
    MemoryCopySemantics.readByte (MemorySemantics.writeByte entries (Word.ofNatModulo position) value)
        (Word.ofNatModulo index) =
      if index = position then value.bitAnd (Word.ofNatModulo 255)
      else MemoryCopySemantics.readByte entries (Word.ofNatModulo index) := by
  rw [readByte_writeByte]
  by_cases same : index = position
  · rw [if_pos (by rw [same]), if_pos same]
  · rw [if_neg (fun equal => same (by
      have := congrArg Fin.val equal; rwa [val_small indexSmall, val_small positionSmall] at this)), if_neg same]

theorem readByte_writeWord_at (entries : MemorySemantics.Entries) {position index : Nat} (value : Word)
    (positionSmall : position < 2 ^ 256) (indexSmall : index < 2 ^ 256) :
    MemoryCopySemantics.readByte (MemorySemantics.writeWord entries (Word.ofNatModulo position) value)
        (Word.ofNatModulo index) =
      if position ≤ index ∧ index < position + 32 then Word.byteAt (Word.ofNatModulo (index - position)) value
      else MemoryCopySemantics.readByte entries (Word.ofNatModulo index) := by
  rw [readByte_writeWord, val_small positionSmall, val_small indexSmall]

theorem address_lane (creator : Word) {lane : Nat} (inside : lane < 20) :
    Word.byteAt (Word.ofNatModulo lane) ((creator.bitAnd addressMask).shiftLeft (Word.ofNatModulo 96)) =
      Word.ofNatModulo ((addressBytes creator).getD lane 0) := by
  rw [addressBytes_getD _ inside]
  apply Fin.ext
  rw [val_byteAt _ _ (by rw [val_small (by omega)]; omega), val_small (by omega),
    val_shiftLeft _ _ (by rw [val_small (by decide)]; decide), val_small (show 96 < 2 ^ 256 by decide),
    val_small (Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide)),
    show (96 : Nat) = 8 * 12 from rfl, lane_shiftLeft _ (by omega), val_bitAnd,
    show addressMask.val = 2 ^ 160 - 1 from val_small (by decide), lane_mask _ (by omega) (by omega), pow256]
  congr 3
  omega

theorem createPrefix_byte (creator nonce : Word) {index : Nat} (inside : index < 22) :
    MemoryCopySemantics.readByte (createPrefix creator nonce) (Word.ofNatModulo index) =
      Word.ofNatModulo ((createPreimage creator nonce).getD index 0) := by
  unfold createPrefix
  rw [readByte_writeWord_at _ _ (by decide) (by omega), createPreimage_getD]
  by_cases address : 2 ≤ index
  · rw [if_pos ⟨address, by omega⟩, if_neg (by omega), if_neg (by omega), if_pos inside]
    exact address_lane creator (by omega)
  · rw [if_neg (by omega), readByte_writeByte_at _ _ (by decide) (by omega)]
    by_cases one : index = 1
    · rw [if_pos one, if_neg (by omega), if_pos one]
      exact byte_bitAnd (by decide)
    · have bounded := nonceBytes_length_le nonce
      rw [if_neg one, readByte_writeByte_at _ _ (by decide) (by omega), if_pos (by omega), if_pos (by omega)]
      have header : (Word.ofNatModulo 213).add (encodedLength nonce) = Word.ofNatModulo (213 + (nonceBytes nonce).length) := by
        apply Fin.ext
        show ((Word.ofNatModulo 213).val + (encodedLength nonce).val) % wordModulus = _
        rw [encodedLength_val, val_small (by decide), val_small (by omega)]
        exact Nat.mod_eq_of_lt (by change _ < 2 ^ 256; omega)
      rw [header]
      exact byte_bitAnd (by omega)


theorem nonce_lane {nonce : Word} (large : 128 ≤ nonce.val) {lane : Nat} (inside : lane < (bigEndian nonce.val).length) :
    Word.byteAt (Word.ofNatModulo lane)
        (nonce.shiftLeft (((Word.ofNatModulo 32).sub (byteCount nonce)).mul (Word.ofNatModulo 8))) =
      Word.ofNatModulo ((bigEndian nonce.val).getD lane 0) := by
  have bounded := bigEndian_word_length nonce (by omega)
  have count := byteCount_val (nonce := nonce) (by omega)
  have remaining : ((Word.ofNatModulo 32).sub (byteCount nonce)).val = 32 - (bigEndian nonce.val).length := by
    show (Word.ofNatModulo 32 - byteCount nonce).val = _
    rw [Fin.sub_val_of_le (Fin.le_def.mpr (by rw [count, val_small (by decide)]; omega)), count, val_small (by decide)]
  have shift : (((Word.ofNatModulo 32).sub (byteCount nonce)).mul (Word.ofNatModulo 8)).val =
      8 * (32 - (bigEndian nonce.val).length) := by
    show (((Word.ofNatModulo 32).sub (byteCount nonce)).val * (Word.ofNatModulo 8).val) % wordModulus = _
    rw [remaining, val_small (by decide), Nat.mod_eq_of_lt (by change _ < 2 ^ 256; omega)]
    omega
  have positiveLength : 0 < (bigEndian nonce.val).length := by omega
  rw [bigEndian_getD _ _ inside]
  apply Fin.ext
  rw [val_byteAt _ _ (by rw [val_small (by omega)]; omega), val_small (by omega),
    val_shiftLeft _ _ (by rw [shift]; omega), shift, lane_shiftLeft _ (by omega),
    val_small (Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide)), pow256]
  congr 3
  omega

theorem createScratch_byte (creator nonce : Word) {index : Nat}
    (inside : index < (createPreimage creator nonce).length) :
    MemoryCopySemantics.readByte (createScratch creator nonce) (Word.ofNatModulo index) =
      Word.ofNatModulo ((createPreimage creator nonce).getD index 0) := by
  have total := createPreimage_length creator nonce
  have bounded := nonceBytes_length_le nonce
  unfold createScratch
  by_cases zero : nonce.val = 0
  · have test : (nonce == Word.ofNatModulo 0) = true := beq_iff_eq.mpr (Fin.ext (by rw [zero]; rfl))
    rw [if_pos test, readByte_writeByte_at _ _ (by decide) (by omega)]
    by_cases last : index = 22
    · rw [if_pos last, createPreimage_getD, if_neg (by omega), if_neg (by omega), if_neg (by omega), last,
        nonceBytes_zero zero]
      exact byte_bitAnd (by decide)
    · rw [if_neg last]
      rw [nonceBytes_zero zero] at total
      exact createPrefix_byte creator nonce (by simp at total; omega)
  · have test : (nonce == Word.ofNatModulo 0) = false :=
      beq_eq_false_iff_ne.mpr (fun same => zero (by rw [same]; rfl))
    rw [if_neg (by rw [test]; decide)]
    by_cases large : nonce > Word.ofNatModulo 127
    · have bound : 128 ≤ nonce.val := by
        have := Fin.lt_def.mp large; rw [val_small (by decide)] at this; omega
      have lengthBound := bigEndian_word_length nonce (by omega)
      rw [if_pos large, nonceBytes_large bound] at *
      simp only [List.length_cons] at total
      rw [readByte_writeWord_at _ _ (by decide) (by omega)]
      by_cases tail : 23 ≤ index
      · rw [if_pos ⟨tail, by omega⟩, nonce_lane bound (by omega), createPreimage_getD, if_neg (by omega),
          if_neg (by omega), if_neg (by omega), nonceBytes_large bound,
          show index - 22 = (index - 23) + 1 by omega]
        rfl
      · rw [if_neg (by omega), readByte_writeByte_at _ _ (by decide) (by omega)]
        by_cases last : index = 22
        · rw [if_pos last, createPreimage_getD, if_neg (by omega), if_neg (by omega), if_neg (by omega), last,
            nonceBytes_large bound]
          have header : (Word.ofNatModulo 128).add (byteCount nonce) =
              Word.ofNatModulo (128 + (bigEndian nonce.val).length) := by
            apply Fin.ext
            show ((Word.ofNatModulo 128).val + (byteCount nonce).val) % wordModulus = _
            rw [byteCount_val (by omega), val_small (by decide), val_small (by omega)]
            exact Nat.mod_eq_of_lt (by change _ < 2 ^ 256; omega)
          rw [header]
          exact byte_bitAnd (by omega)
        · rw [if_neg last]
          exact createPrefix_byte creator nonce (by omega)
    · have bound : nonce.val < 128 := by
        have := Fin.not_lt.mp large; rw [Fin.le_def, val_small (by decide)] at this; omega
      rw [if_neg large, readByte_writeByte_at _ _ (by decide) (by omega)]
      rw [nonceBytes_small (by omega) bound] at total
      simp only [List.length_cons, List.length_nil] at total
      by_cases last : index = 22
      · rw [if_pos last, createPreimage_getD, if_neg (by omega), if_neg (by omega), if_neg (by omega), last,
          nonceBytes_small (by omega) bound]
        apply Fin.ext
        rw [val_bitAnd, val_small (show 255 < 2 ^ 256 by decide)]
        show nonce.val &&& 255 = (Word.ofNatModulo ([nonce.val].getD 0 0)).val
        rw [show [nonce.val].getD 0 0 = nonce.val from rfl, val_small (by omega)]
        rw [show (255 : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
        exact Nat.mod_eq_of_lt (by omega)
      · rw [if_neg last]
        exact createPrefix_byte creator nonce (by omega)

theorem zero_add (index : Nat) (small : index < 2 ^ 256) :
    Word.zero.add (Word.ofNatModulo index) = Word.ofNatModulo index := by
  apply Fin.ext
  show (0 + (Word.ofNatModulo index).val) % wordModulus = _
  rw [Nat.zero_add, val_small small]
  exact Nat.mod_eq_of_lt small

/-- A memory holding a byte string from address zero absorbs as the string. -/
theorem keccak_of_bytes {bytes : Bytes} {words : MemorySemantics.Entries} {length : Word}
    (small : ∀ byte ∈ bytes, byte < 256) (fits : bytes.length < 2 ^ 256)
    (sameLength : length.val = bytes.length)
    (agree : ∀ index, index < bytes.length →
      MemoryCopySemantics.readByte words (Word.ofNatModulo index) = Word.ofNatModulo (bytes.getD index 0))
    {digest : Word} :
    Keccak bytes digest ↔ KeccakSemantics.Absorb words Word.zero length (List.replicate 25 Word.zero) digest := by
  have lengthWord : length = Word.ofNatModulo bytes.length := Fin.ext (by rw [sameLength, val_small fits])
  have reads : ∀ index, index < length.val →
      MemoryCopySemantics.readByte (stored bytes) (Word.zero.add (Word.ofNatModulo index)) =
        MemoryCopySemantics.readByte words (Word.zero.add (Word.ofNatModulo index)) := by
    intro index inside
    rw [sameLength] at inside
    rw [zero_add _ (by omega), readByte_stored small (by omega) inside, agree index inside]
  unfold Keccak
  rw [← lengthWord]
  exact ⟨fun hashed => Absorb.congr hashed reads,
    fun absorbed => Absorb.congr absorbed (fun index inside => (reads index inside).symm)⟩

/-- Keccak-256 of a string shorter than the 136-byte rate absorbs one padded
block. -/
def shortDigest (bytes : Bytes) : Word :=
  KeccakSemantics.digest (KeccakSemantics.permute (KeccakSemantics.absorbBlock (stored bytes) Word.zero
    (Word.ofNatModulo bytes.length) (List.replicate 25 Word.zero)))

theorem shortDigest_keccak {bytes : Bytes} (short : bytes.length < 136) : Keccak bytes (shortDigest bytes) :=
  .last _ _ _ (by
    change (Word.ofNatModulo bytes.length).val < (Word.ofNatModulo 136).val
    rw [val_small (by omega), val_small (by decide)]
    exact short)

theorem createScratch_keccak (creator nonce : Word) {digest : Word} :
    Keccak (createPreimage creator nonce) digest ↔
      KeccakSemantics.Absorb (createScratch creator nonce) Word.zero (createLength nonce)
        (List.replicate 25 Word.zero) digest := by
  have total := createPreimage_length creator nonce
  have bounded := nonceBytes_length_le nonce
  exact keccak_of_bytes (createPreimage_bytes creator nonce) (by omega) (createLength_val creator nonce)
    (fun index inside => createScratch_byte creator nonce inside)

def create2Scratch (creator salt initHash : Word) : MemorySemantics.Entries :=
  MemorySemantics.writeWord
    (MemorySemantics.writeWord
      (MemorySemantics.writeWord (MemorySemantics.writeByte [] (Word.ofNatModulo 0) (Word.ofNatModulo 255))
        (Word.ofNatModulo 1) ((creator.bitAnd addressMask).shiftLeft (Word.ofNatModulo 96)))
      (Word.ofNatModulo 21) salt)
    (Word.ofNatModulo 53) initHash

theorem create2Preimage_length (creator salt initHash : Word) :
    (create2Preimage creator salt initHash).length = 85 := by
  simp [create2Preimage, addressBytes_length, wordBytes_length]

theorem create2Preimage_getD (creator salt initHash : Word) (index : Nat) :
    (create2Preimage creator salt initHash).getD index 0 =
      if index = 0 then 255
      else if index < 21 then (addressBytes creator).getD (index - 1) 0
      else if index < 53 then (wordBytes salt).getD (index - 21) 0
      else (wordBytes initHash).getD (index - 53) 0 := by
  rcases index with _ | index
  · rfl
  · rw [if_neg (by omega)]
    simp only [create2Preimage, List.getD_eq_getElem?_getD, List.getElem?_cons_succ]
    rw [← List.getD_eq_getElem?_getD, List.append_assoc]
    by_cases address : index + 1 < 21
    · rw [if_pos address, getD_append_left (by rw [addressBytes_length]; omega)]
      rfl
    · rw [if_neg address, getD_append_right (by rw [addressBytes_length]; omega), addressBytes_length]
      by_cases saltByte : index + 1 < 53
      · rw [if_pos saltByte, getD_append_left (by rw [wordBytes_length]; omega)]
        congr 1
      · rw [if_neg saltByte, getD_append_right (by rw [wordBytes_length]; omega), wordBytes_length]
        congr 1

theorem create2Preimage_bytes (creator salt initHash : Word) :
    ∀ byte ∈ create2Preimage creator salt initHash, byte < 256 := by
  intro byte member
  simp only [create2Preimage, List.mem_cons, List.mem_append, addressBytes, wordBytes] at member
  rcases member with rfl | (address | saltByte) | hashByte
  · omega
  · obtain ⟨_, _, rfl⟩ := List.mem_map.mp (List.mem_of_mem_drop address)
    exact Nat.mod_lt _ (by decide)
  · obtain ⟨_, _, rfl⟩ := List.mem_map.mp saltByte
    exact Nat.mod_lt _ (by decide)
  · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hashByte
    exact Nat.mod_lt _ (by decide)

theorem word_lane (value : Word) {lane : Nat} (inside : lane < 32) :
    Word.byteAt (Word.ofNatModulo lane) value = Word.ofNatModulo ((wordBytes value).getD lane 0) := by
  rw [wordBytes_getD _ inside]
  apply Fin.ext
  rw [val_byteAt _ _ (by rw [val_small (by omega)]; omega), val_small (by omega),
    val_small (Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide)), pow256]

theorem create2Scratch_byte (creator salt initHash : Word) {index : Nat} (inside : index < 85) :
    MemoryCopySemantics.readByte (create2Scratch creator salt initHash) (Word.ofNatModulo index) =
      Word.ofNatModulo ((create2Preimage creator salt initHash).getD index 0) := by
  unfold create2Scratch
  rw [readByte_writeWord_at _ _ (by decide) (by omega), create2Preimage_getD]
  by_cases hashByte : 53 ≤ index
  · rw [if_pos ⟨hashByte, by omega⟩, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    exact word_lane initHash (by omega)
  · rw [if_neg (by omega), readByte_writeWord_at _ _ (by decide) (by omega)]
    by_cases saltByte : 21 ≤ index
    · rw [if_pos ⟨saltByte, by omega⟩, if_neg (by omega), if_neg (by omega), if_pos (by omega)]
      exact word_lane salt (by omega)
    · rw [if_neg (by omega), readByte_writeWord_at _ _ (by decide) (by omega)]
      by_cases address : 1 ≤ index
      · rw [if_pos ⟨address, by omega⟩, if_neg (by omega), if_pos (by omega)]
        exact address_lane creator (by omega)
      · rw [if_neg (by omega), readByte_writeByte_at _ _ (by decide) (by omega), if_pos (by omega), if_pos (by omega)]
        exact byte_bitAnd (by decide)

theorem create2Scratch_keccak (creator salt initHash : Word) {digest : Word} :
    Keccak (create2Preimage creator salt initHash) digest ↔
      KeccakSemantics.Absorb (create2Scratch creator salt initHash) Word.zero (Word.ofNatModulo 85)
        (List.replicate 25 Word.zero) digest :=
  keccak_of_bytes (create2Preimage_bytes creator salt initHash) (by rw [create2Preimage_length]; decide)
    (by rw [create2Preimage_length]; rfl)
    (fun index inside => create2Scratch_byte creator salt initHash (by rwa [create2Preimage_length] at inside))

end Solcore.Frontend.RustHull.CreationPreimage
end

section
-- leanmerge: from Solcore.Frontend.RustHull.CreationAddressCorrespondence
/-! The actual address builders compute the independent CREATE and CREATE2
addresses. Each builder writes its preimage into fresh scratch cells with the
actual `mstore8` and `mstore` and hashes it with the connected Keccak; the
scratch bytes are the specified preimage, so the masked digest is the address.
CREATE2 first hashes the copied init bytes held in their own cells. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.CreationAddressCorrespondence
open Core Correspondence ScalarExecution CodeBuilder CreationPreimage CreationBytes

abbrev StateRel := MemoryCorrespondence.StateRel
abbrev Frame := MemoryCorrespondence.Frame

theorem touch_some (size offset length : Word) (small : offset.val + length.val < 2 ^ 255) :
    ∃ touched, MemorySemantics.touchSize? size offset length = some touched := by
  unfold MemorySemantics.touchSize?
  by_cases zero : length == Word.zero
  · simp [zero]
  · simp only [zero, Bool.false_eq_true, ↓reduceIte]
    have sum : (offset.add length).val = offset.val + length.val := by
      show (offset.val + length.val) % wordModulus = _
      exact Nat.mod_eq_of_lt (by change _ < 2 ^ 256; omega)
    have notWrapped : ¬offset > offset.add length := by
      rw [GT.gt, Fin.lt_def, sum]
      omega
    have notLarge : ¬offset.add length > Word.ofNatModulo (wordModulus - 32) := by
      rw [GT.gt, Fin.lt_def, sum, val_small (show wordModulus - 32 < 2 ^ 256 by decide)]
      change ¬(2 ^ 256 - 32 < offset.val + length.val)
      omega
    simp only [notWrapped, notLarge, ↓reduceIte]
    exact ⟨_, rfl⟩

theorem writeByte_evaluates {depth : Nat} {environment : Environment} {store : Store}
    {memory size offset value : Code} {memoryLocation sizeLocation : Nat} {state : MemorySemantics.State}
    {offsetWord valueWord touched : Word}
    (memoryCode : CodeValue depth environment memory (.cellRef WordMapping.type memoryLocation))
    (sizeCode : CodeValue depth environment size (.cellRef .word sizeLocation))
    (offsetCode : CodeValue depth environment offset (.word offsetWord))
    (valueCode : CodeValue depth environment value (.word valueWord))
    (related : StateRel memoryLocation sizeLocation state store)
    (fits : MemorySemantics.touchSize? state.size offsetWord (Word.ofNatModulo 1) = some touched) :
    ∃ next, Evaluates environment store (CreationImplementation.writeByte memory size offset value depth)
        (.inRight .word .unit) next ∧
      StateRel memoryLocation sizeLocation ⟨MemorySemantics.writeByte state.words offsetWord valueWord, touched⟩ next ∧
      Frame memoryLocation sizeLocation store next := by
  have evaluated := MemoryCorrespondence.mstore8_evaluates state offsetWord valueWord
    (memoryCode.evaluates store) (sizeCode.evaluates store) (offsetCode.evaluates store) (valueCode.evaluates store)
    related.memory related.size related.distinct
  obtain ⟨_, nextRelated, frame⟩ := MemoryCorrespondence.mstore8_preserves related offsetWord valueWord environment
  simp only [MemoryCorrespondence.mstore8Result, fits] at evaluated
  simp only [MemorySemantics.mstore8, fits] at nextRelated
  exact ⟨_, evaluated, nextRelated, frame⟩

theorem writeWord_evaluates {depth : Nat} {environment : Environment} {store : Store}
    {memory size offset value : Code} {memoryLocation sizeLocation : Nat} {state : MemorySemantics.State}
    {offsetWord valueWord touched : Word}
    (memoryCode : CodeValue depth environment memory (.cellRef WordMapping.type memoryLocation))
    (sizeCode : CodeValue depth environment size (.cellRef .word sizeLocation))
    (offsetCode : CodeValue depth environment offset (.word offsetWord))
    (valueCode : CodeValue depth environment value (.word valueWord))
    (related : StateRel memoryLocation sizeLocation state store)
    (fits : MemorySemantics.touchSize? state.size offsetWord (Word.ofNatModulo 32) = some touched) :
    ∃ next, Evaluates environment store (CreationImplementation.writeWord memory size offset value depth)
        (.inRight .word .unit) next ∧
      StateRel memoryLocation sizeLocation ⟨MemorySemantics.writeWord state.words offsetWord valueWord, touched⟩ next ∧
      Frame memoryLocation sizeLocation store next := by
  have evaluated := MemoryCorrespondence.mstore_evaluates state offsetWord valueWord
    (memoryCode.evaluates store) (sizeCode.evaluates store) (offsetCode.evaluates store) (valueCode.evaluates store)
    related.memory related.size related.distinct
  obtain ⟨_, nextRelated, frame⟩ := MemoryCorrespondence.mstore_preserves related offsetWord valueWord environment
  simp only [MemoryCorrespondence.mstoreResult, fits] at evaluated
  simp only [MemorySemantics.mstore, fits] at nextRelated
  exact ⟨_, evaluated, nextRelated, frame⟩

theorem hash_evaluates {depth : Nat} {environment : Environment} {store : Store}
    {memory size offset length : Code} {memoryLocation sizeLocation : Nat} {state : MemorySemantics.State}
    {lengthWord touched digest : Word}
    (memoryCode : CodeValue depth environment memory (.cellRef WordMapping.type memoryLocation))
    (sizeCode : CodeValue depth environment size (.cellRef .word sizeLocation))
    (offsetCode : CodeValue depth environment offset (.word (Word.ofNatModulo 0)))
    (lengthCode : CodeValue depth environment length (.word lengthWord))
    (related : StateRel memoryLocation sizeLocation state store)
    (fits : MemorySemantics.touchSize? state.size (Word.ofNatModulo 0) lengthWord = some touched)
    (absorbed : KeccakSemantics.Absorb state.words (Word.ofNatModulo 0) lengthWord (List.replicate 25 Word.zero) digest) :
    ∃ next, Evaluates environment store (CreationImplementation.hash memory size offset length depth)
        (.inRight .word (.word digest)) next ∧ Frame memoryLocation sizeLocation store next := by
  obtain ⟨target, next, resultRelated, evaluated, _, frame⟩ := KeccakHashCorrespondence.hash_preserves
    (.done fits absorbed) related (memoryCode.evaluates store) (sizeCode.evaluates store)
    (offsetCode.evaluates store) (lengthCode.evaluates store)
  cases resultRelated with
  | value valueRelated =>
      cases valueRelated
      exact ⟨next, evaluated, frame⟩


theorem binary_code {depth : Nat} {environment : Environment} {left right : Code} {leftValue rightValue result : Value}
    {op : BinaryOp} (leftCode : CodeValue depth environment left leftValue)
    (rightCode : CodeValue depth environment right rightValue) (applied : op.apply leftValue rightValue = some result) :
    CodeValue depth environment (binary op left right) result :=
  fun extra store => .binary (leftCode extra store) (rightCode extra store) applied

theorem createFinish_evaluates {depth : Nat} {environment : Environment} {store : Store}
    {memory size encoded : Code} {memoryLocation sizeLocation : Nat} {creator nonce touched digest : Word}
    (memoryCode : CodeValue depth environment memory (.cellRef WordMapping.type memoryLocation))
    (sizeCode : CodeValue depth environment size (.cellRef .word sizeLocation))
    (encodedCode : CodeValue depth environment encoded (.word (encodedLength nonce)))
    (related : StateRel memoryLocation sizeLocation ⟨createScratch creator nonce, touched⟩ store)
    (hashed : CreationAddressSemantics.Keccak (CreationAddressSemantics.createPreimage creator nonce) digest) :
    ∃ final, Evaluates environment store (CreationImplementation.createFinish memory size encoded depth)
        (.inRight .word (.word (CreationAddressSemantics.address digest))) final ∧
      Frame memoryLocation sizeLocation store final := by
  have lengthCode : CodeValue depth environment (binary .wordAdd (number 22) encoded) (.word (createLength nonce)) :=
    binary_code (CodeValue.number 22 depth environment) encodedCode rfl
  have total := createPreimage_length creator nonce
  have bounded := nonceBytes_length_le nonce
  have lengthValue := createLength_val creator nonce
  obtain ⟨hashTouched, fits⟩ := touch_some touched (Word.ofNatModulo 0) (createLength nonce)
    (by rw [lengthValue, val_small (by decide)]; omega)
  obtain ⟨final, evaluated, frame⟩ := hash_evaluates memoryCode sizeCode (CodeValue.number 0 depth environment)
    lengthCode related fits ((createScratch_keccak creator nonce).mp hashed)
  refine ⟨final, LanguageResult.bind_success .word evaluated (.inRight ?_), frame⟩
  exact .binary ((CodeValue.bound depth environment (.word digest)).evaluates final) .word rfl


theorem touch_byte (size : Word) (offset : Nat) (small : offset < 1000) :
    ∃ touched, MemorySemantics.touchSize? size (Word.ofNatModulo offset) (Word.ofNatModulo 1) = some touched :=
  touch_some size _ _ (by rw [val_small (by omega), val_small (by decide)]; omega)

theorem touch_word (size : Word) (offset : Nat) (small : offset < 1000) :
    ∃ touched, MemorySemantics.touchSize? size (Word.ofNatModulo offset) (Word.ofNatModulo 32) = some touched :=
  touch_some size _ _ (by rw [val_small (by omega), val_small (by decide)]; omega)

theorem createTail_evaluates {depth : Nat} {environment : Environment} {store : Store}
    {memory size nonceCode count encoded : Code} {memoryLocation sizeLocation : Nat}
    {creator nonce touched digest : Word}
    (memoryCode : CodeValue depth environment memory (.cellRef WordMapping.type memoryLocation))
    (sizeCode : CodeValue depth environment size (.cellRef .word sizeLocation))
    (nonceValue : CodeValue depth environment nonceCode (.word nonce))
    (countCode : CodeValue depth environment count (.word (byteCount nonce)))
    (encodedCode : CodeValue depth environment encoded (.word (encodedLength nonce)))
    (related : StateRel memoryLocation sizeLocation ⟨CreationPreimage.createPrefix creator nonce, touched⟩ store)
    (hashed : CreationAddressSemantics.Keccak (CreationAddressSemantics.createPreimage creator nonce) digest) :
    ∃ final, Evaluates environment store
        (CreationImplementation.createTail memory size nonceCode count encoded depth)
        (.inRight .word (.word (CreationAddressSemantics.address digest))) final ∧
      Frame memoryLocation sizeLocation store final := by
  unfold CreationImplementation.createTail
  by_cases zero : nonce.val = 0
  · have test : (nonce == Word.ofNatModulo 0) = true := beq_iff_eq.mpr (Fin.ext (by rw [zero]; rfl))
    obtain ⟨written, fits⟩ := touch_byte touched 22 (by decide)
    obtain ⟨store1, evaluated1, related1, frame1⟩ := writeByte_evaluates memoryCode sizeCode
      (CodeValue.number 22 depth environment) (CodeValue.number 128 depth environment) related fits
    have scratchSame : MemorySemantics.writeByte (CreationPreimage.createPrefix creator nonce) (Word.ofNatModulo 22)
        (Word.ofNatModulo 128) = createScratch creator nonce := by
      unfold createScratch; rw [if_pos test]
    rw [scratchSame] at related1
    obtain ⟨final, evaluated, frame⟩ := createFinish_evaluates (memoryCode.prepend [.unit]) (sizeCode.prepend [.unit])
      (encodedCode.prepend [.unit]) related1 hashed
    exact ⟨final, .ifTrue (.binary (nonceValue.evaluates store) .word (by simp only [BinaryOp.apply, test]))
      (LanguageResult.bind_success .word evaluated1 evaluated), frame1.trans frame⟩
  · have test : (nonce == Word.ofNatModulo 0) = false :=
      beq_eq_false_iff_ne.mpr (fun same => zero (by rw [same]; rfl))
    have zeroTest : Evaluates environment store (binary .wordEq nonceCode (number 0) depth) (.bool false) store :=
      .binary (nonceValue.evaluates store) .word (by simp only [BinaryOp.apply, test])
    by_cases large : nonce > Word.ofNatModulo 127
    · obtain ⟨written, fits⟩ := touch_byte touched 22 (by decide)
      obtain ⟨store1, evaluated1, related1, frame1⟩ := writeByte_evaluates memoryCode sizeCode
        (CodeValue.number 22 depth environment)
        (binary_code (op := .wordAdd) (CodeValue.number 128 depth environment) countCode rfl) related fits
      obtain ⟨wordWritten, wordFits⟩ := touch_word written 23 (by decide)
      have shiftCode := binary_code (op := .wordShl) (nonceValue.prepend [.unit])
        (binary_code (op := .wordMul)
          (binary_code (op := .wordSub) (CodeValue.number 32 (depth + 1) (.unit :: environment))
            (countCode.prepend [.unit]) rfl)
          (CodeValue.number 8 (depth + 1) (.unit :: environment)) rfl) rfl
      obtain ⟨store2, evaluated2, related2, frame2⟩ := writeWord_evaluates (memoryCode.prepend [.unit])
        (sizeCode.prepend [.unit]) (CodeValue.number 23 (depth + 1) (.unit :: environment)) shiftCode related1 wordFits
      have scratchSame : MemorySemantics.writeWord
          (MemorySemantics.writeByte (CreationPreimage.createPrefix creator nonce) (Word.ofNatModulo 22)
            ((Word.ofNatModulo 128).add (byteCount nonce))) (Word.ofNatModulo 23)
          (nonce.shiftLeft (((Word.ofNatModulo 32).sub (byteCount nonce)).mul (Word.ofNatModulo 8))) =
          createScratch creator nonce := by
        unfold createScratch; rw [if_neg (by rw [test]; decide), if_pos large]
      rw [scratchSame] at related2
      obtain ⟨final, evaluated, frame⟩ := createFinish_evaluates ((memoryCode.prepend [.unit]).prepend [.unit])
        ((sizeCode.prepend [.unit]).prepend [.unit]) ((encodedCode.prepend [.unit]).prepend [.unit]) related2 hashed
      exact ⟨final, .ifFalse zeroTest (.ifTrue (.binary (nonceValue.evaluates store) .word
          (by simp only [BinaryOp.apply, large, decide_true]))
        (LanguageResult.bind_success .word evaluated1 (LanguageResult.bind_success .word evaluated2 evaluated))),
        (frame1.trans frame2).trans frame⟩
    · obtain ⟨written, fits⟩ := touch_byte touched 22 (by decide)
      obtain ⟨store1, evaluated1, related1, frame1⟩ := writeByte_evaluates memoryCode sizeCode
        (CodeValue.number 22 depth environment) nonceValue related fits
      have scratchSame : MemorySemantics.writeByte (CreationPreimage.createPrefix creator nonce) (Word.ofNatModulo 22)
          nonce = createScratch creator nonce := by
        unfold createScratch; rw [if_neg (by rw [test]; decide), if_neg large]
      rw [scratchSame] at related1
      obtain ⟨final, evaluated, frame⟩ := createFinish_evaluates (memoryCode.prepend [.unit]) (sizeCode.prepend [.unit])
        (encodedCode.prepend [.unit]) related1 hashed
      exact ⟨final, .ifFalse zeroTest (.ifFalse (.binary (nonceValue.evaluates store) .word
          (by simp only [BinaryOp.apply, large, decide_false]))
        (LanguageResult.bind_success .word evaluated1 evaluated)), frame1.trans frame⟩


theorem createPrefix_evaluates {depth : Nat} {environment : Environment} {store : Store}
    {creatorCode memory size encoded rest : Code} {memoryLocation sizeLocation : Nat}
    {creator nonce empty : Word} {result : Value}
    (creatorValue : CodeValue depth environment creatorCode (.word creator))
    (memoryCode : CodeValue depth environment memory (.cellRef WordMapping.type memoryLocation))
    (sizeCode : CodeValue depth environment size (.cellRef .word sizeLocation))
    (encodedCode : CodeValue depth environment encoded (.word (encodedLength nonce)))
    (related : StateRel memoryLocation sizeLocation ⟨[], empty⟩ store)
    (continued : ∀ next touched,
      StateRel memoryLocation sizeLocation ⟨CreationPreimage.createPrefix creator nonce, touched⟩ next →
      ∃ final, Evaluates (.unit :: .unit :: .unit :: environment) next (rest (depth + 3)) result final ∧
        Frame memoryLocation sizeLocation next final) :
    ∃ final, Evaluates environment store
        (CreationImplementation.createPrefix creatorCode memory size encoded rest depth) result final ∧
      Frame memoryLocation sizeLocation store final := by
  obtain ⟨touched0, fits0⟩ := touch_byte empty 0 (by decide)
  obtain ⟨store1, evaluated1, related1, frame1⟩ := writeByte_evaluates memoryCode sizeCode
    (CodeValue.number 0 depth environment)
    (binary_code (op := .wordAdd) (CodeValue.number 213 depth environment) encodedCode rfl) related fits0
  obtain ⟨touched1, fits1⟩ := touch_byte touched0 1 (by decide)
  obtain ⟨store2, evaluated2, related2, frame2⟩ := writeByte_evaluates (memoryCode.prepend [.unit])
    (sizeCode.prepend [.unit]) (CodeValue.number 1 (depth + 1) (.unit :: environment))
    (CodeValue.number 148 (depth + 1) (.unit :: environment)) related1 fits1
  obtain ⟨touched2, fits2⟩ := touch_word touched1 2 (by decide)
  have addressCode := binary_code (op := .wordShl)
    (binary_code (op := .wordAnd) ((creatorValue.prepend [.unit]).prepend [.unit])
      (CodeValue.number (2 ^ 160 - 1) (depth + 1 + 1) (.unit :: .unit :: environment)) rfl)
    (CodeValue.number 96 (depth + 1 + 1) (.unit :: .unit :: environment)) rfl
  obtain ⟨store3, evaluated3, related3, frame3⟩ := writeWord_evaluates ((memoryCode.prepend [.unit]).prepend [.unit])
    ((sizeCode.prepend [.unit]).prepend [.unit]) (CodeValue.number 2 (depth + 1 + 1) (.unit :: .unit :: environment))
    addressCode related2 fits2
  obtain ⟨final, evaluated, frame⟩ := continued store3 touched2 related3
  exact ⟨final, LanguageResult.bind_success .word evaluated1 (LanguageResult.bind_success .word evaluated2
    (LanguageResult.bind_success .word evaluated3 evaluated)), ((frame1.trans frame2).trans frame3).trans frame⟩

/-- Fresh scratch cells keep every existing cell when only they change. -/
theorem scratch_retains {store final : Store} {first second : Value}
    (frame : Frame store.length (store.length + 1) (store ++ [first, second]) final) : StoreRetains store final := by
  constructor
  · have := frame.length
    simp only [List.length_append, List.length_cons, List.length_nil] at this
    omega
  · intro location bound
    have found : (store ++ [first, second]).read? location = some store[location] := by
      show (store ++ [first, second])[location]? = some store[location]
      rw [List.getElem?_append_left bound, List.getElem?_eq_getElem bound]
    rw [frame.read location _ (by omega) (by omega) found]
    exact (List.getElem?_eq_getElem bound).symm

theorem createAddress_evaluates {environment : Environment} {store : Store}
    {creatorExpr nonceExpr : Core.Expr} {creator nonce digest : Word}
    (evaluated : Evaluates environment store (.pair creatorExpr nonceExpr) (.pair (.word creator) (.word nonce)) store)
    (hashed : CreationAddressSemantics.Keccak (CreationAddressSemantics.createPreimage creator nonce) digest) :
    ∃ final, Evaluates environment store (Creation.createAddress creatorExpr nonceExpr)
        (.inRight .word (.word (CreationAddressSemantics.address digest))) final ∧ StoreRetains store final := by
  rw [CreationImplementation.createAddress_eq]
  let pairValue : Value := .pair (.word creator) (.word nonce)
  have inputs : CodeValue 0 (pairValue :: environment) (fun depth => .var depth)
      (bundleValues [.word creator, .word nonce]) := by
    intro extra store
    exact .var (by simp [pairValue, bundleValues])
  have creatorCode := inputs.part (index := 0) rfl
  have nonceCode := inputs.part (index := 1) rfl
  let count := byteCount nonce
  have countEvaluated : Evaluates (pairValue :: environment) store
      (binary .wordSub (number 32)
        (binary .wordDiv (fun depth => .unary .wordClz (part 1 2 (fun depth => .var depth) depth)) (number 8)) 0)
      (.word count) store :=
    .binary .word (.binary (.unary (nonceCode.evaluates store) rfl) .word rfl) rfl
  have countValue := CodeValue.bound 0 (pairValue :: environment) (.word count)
  have encodedEvaluated : Evaluates (.word count :: pairValue :: environment) store
      (choose (binary .wordGt (part 1 2 (fun depth => .var depth)) (number 127))
        (binary .wordAdd (fun here => .var (here - 0 - 1)) (number 1)) (number 1) 1)
      (.word (encodedLength nonce)) store := by
    unfold encodedLength
    by_cases large : nonce > Word.ofNatModulo 127
    · rw [if_pos large]
      exact .ifTrue (.binary ((nonceCode.prepend [.word count]).evaluates store) .word
        (by simp only [BinaryOp.apply, large, decide_true])) (.binary (countValue.evaluates store) .word rfl)
    · rw [if_neg large]
      exact .ifFalse (.binary ((nonceCode.prepend [.word count]).evaluates store) .word
        (by simp only [BinaryOp.apply, large, decide_false])) .word
  let encoded := encodedLength nonce
  have encodedValue := CodeValue.bound 1 (.word count :: pairValue :: environment) (.word encoded)
  let memoryRef := Value.cellRef WordMapping.type store.length
  let sizeRef := Value.cellRef .word (store.length + 1)
  let allocated : Store := store ++ [WordMapping.encode [], .word (Word.ofNatModulo 0)]
  have scratchRelated : StateRel store.length (store.length + 1) ⟨[], Word.ofNatModulo 0⟩ allocated := by
    refine ⟨by omega, ?_, ?_⟩ <;> simp [allocated, Store.read?]
  let E2 : Environment := .word encoded :: .word count :: pairValue :: environment
  have memoryValue := CodeValue.bound 2 E2 memoryRef
  have sizeValue := CodeValue.bound 3 (memoryRef :: E2) sizeRef
  obtain ⟨final, prefixEvaluated, frame⟩ := createPrefix_evaluates
    (rest := CreationImplementation.createTail (fun here => .var (here - 2 - 1)) (fun here => .var (here - 3 - 1))
      (part 1 2 (fun depth => .var depth)) (fun here => .var (here - 0 - 1)) (fun here => .var (here - 1 - 1)))
    (creatorCode.prepend [sizeRef, memoryRef, .word encoded, .word count]) (memoryValue.prepend [sizeRef]) sizeValue
    (encodedValue.prepend [sizeRef, memoryRef]) scratchRelated
    (fun next touched related => createTail_evaluates
      (((memoryValue.prepend [sizeRef]).prepend [.unit, .unit, .unit]))
      ((sizeValue.prepend [.unit, .unit, .unit]))
      ((nonceCode.prepend [sizeRef, memoryRef, .word encoded, .word count]).prepend [.unit, .unit, .unit])
      ((countValue.prepend [sizeRef, memoryRef, .word encoded]).prepend [.unit, .unit, .unit])
      ((encodedValue.prepend [sizeRef, memoryRef]).prepend [.unit, .unit, .unit]) related hashed)
  refine ⟨final, .letE evaluated (.letE countEvaluated (.letE encodedEvaluated ?_)), scratch_retains frame⟩
  apply Evaluates.letE (bodyStore := store ++ [WordMapping.encode []])
  · exact .newCell (.construct .unit)
  · apply Evaluates.letE (bodyStore := allocated)
    · simpa only [allocated, List.length_append, List.length_cons, List.length_nil, List.append_assoc,
        List.cons_append, List.nil_append, CodeBuilder.allocate, CodeBuilder.number, CodeBuilder.constant] using
        (Evaluates.newCell (elementType := .word) (environment := memoryRef :: E2)
          (initialStore := store ++ [WordMapping.encode []]) Evaluates.word (initialValue := .word (Word.ofNatModulo 0)))
    · exact prefixEvaluated


/-- Fresh scratch cells keep every cell that an earlier frame keeps. -/
theorem scratch_frame {memoryLocation sizeLocation : Nat} {initial store final : Store} {first second : Value}
    (earlier : Frame memoryLocation sizeLocation initial store)
    (later : Frame store.length (store.length + 1) (store ++ [first, second]) final) :
    Frame memoryLocation sizeLocation initial final := by
  have retained := scratch_retains later
  refine ⟨Nat.le_trans earlier.length retained.length_le, ?_⟩
  intro location value memory size found
  have kept := earlier.read location value memory size found
  have bound := (List.getElem?_eq_some_iff.mp kept).1
  rw [retained.read location bound]
  exact kept

theorem create2Address_evaluates {environment : Environment} {store : Store}
    {memoryExpr sizeExpr creatorExpr saltExpr offsetExpr lengthExpr : Core.Expr}
    {initLocation initSizeLocation : Nat} {initCode : MemorySemantics.Entries}
    {initSize creator salt length initHash digest : Word}
    (evaluated : Evaluates environment store (bundle [memoryExpr, sizeExpr, creatorExpr, saltExpr, offsetExpr, lengthExpr])
      (bundleValues [.cellRef WordMapping.type initLocation, .cellRef .word initSizeLocation, .word creator,
        .word salt, .word (Word.ofNatModulo 0), .word length]) store)
    (initRelated : StateRel initLocation initSizeLocation ⟨initCode, initSize⟩ store)
    (bounded : length.val ≤ 49152)
    (initHashed : KeccakSemantics.Absorb initCode Word.zero length (List.replicate 25 Word.zero) initHash)
    (hashed : CreationAddressSemantics.Keccak (CreationAddressSemantics.create2Preimage creator salt initHash) digest) :
    ∃ final, Evaluates environment store
        (Creation.create2Address memoryExpr sizeExpr creatorExpr saltExpr offsetExpr lengthExpr)
        (.inRight .word (.word (CreationAddressSemantics.address digest))) final ∧
      Frame initLocation initSizeLocation store final := by
  rw [CreationImplementation.create2Address_eq]
  let argumentValues : List Value := [.cellRef WordMapping.type initLocation, .cellRef .word initSizeLocation,
    .word creator, .word salt, .word (Word.ofNatModulo 0), .word length]
  have inputs : CodeValue 0 (bundleValues argumentValues :: environment) (fun depth => .var depth)
      (bundleValues argumentValues) := by
    intro extra store
    exact .var (by simp)
  have input (index : Nat) {value : Value} (found : argumentValues[index]? = some value) :=
    inputs.part (index := index) found
  obtain ⟨initTouched, initFits⟩ := touch_some initSize (Word.ofNatModulo 0) length
    (by rw [val_small (by decide)]; omega)
  obtain ⟨hashStore, hashEvaluated, hashFrame⟩ := hash_evaluates (input 0 rfl) (input 1 rfl) (input 4 rfl)
    (input 5 rfl) initRelated initFits initHashed
  let E1 : Environment := .word initHash :: bundleValues argumentValues :: environment
  have hashValue := CodeValue.bound 0 (bundleValues argumentValues :: environment) (.word initHash)
  let memoryRef := Value.cellRef WordMapping.type hashStore.length
  let sizeRef := Value.cellRef .word (hashStore.length + 1)
  let allocated : Store := hashStore ++ [WordMapping.encode [], .word (Word.ofNatModulo 0)]
  have scratchRelated : StateRel hashStore.length (hashStore.length + 1) ⟨[], Word.ofNatModulo 0⟩ allocated := by
    refine ⟨by omega, ?_, ?_⟩ <;> simp [allocated, Store.read?]
  have memoryValue := (CodeValue.bound 1 E1 memoryRef).prepend [sizeRef]
  have sizeValue := CodeValue.bound 2 (memoryRef :: E1) sizeRef
  let E3 : Environment := sizeRef :: memoryRef :: E1
  obtain ⟨touched0, fits0⟩ := touch_byte (Word.ofNatModulo 0) 0 (by decide)
  obtain ⟨store1, evaluated1, related1, frame1⟩ := writeByte_evaluates memoryValue sizeValue
    (CodeValue.number 0 3 E3) (CodeValue.number 255 3 E3) scratchRelated fits0
  obtain ⟨touched1, fits1⟩ := touch_word touched0 1 (by decide)
  have addressCode := binary_code (op := .wordShl)
    (binary_code (op := .wordAnd) ((input 2 rfl).prepend [.unit, sizeRef, memoryRef, .word initHash])
      (CodeValue.number (2 ^ 160 - 1) 4 (.unit :: E3)) rfl)
    (CodeValue.number 96 4 (.unit :: E3)) rfl
  obtain ⟨store2, evaluated2, related2, frame2⟩ := writeWord_evaluates (memoryValue.prepend [.unit])
    (sizeValue.prepend [.unit]) (CodeValue.number 1 4 (.unit :: E3)) addressCode related1 fits1
  obtain ⟨touched2, fits2⟩ := touch_word touched1 21 (by decide)
  obtain ⟨store3, evaluated3, related3, frame3⟩ := writeWord_evaluates ((memoryValue.prepend [.unit]).prepend [.unit])
    ((sizeValue.prepend [.unit]).prepend [.unit]) (CodeValue.number 21 5 (.unit :: .unit :: E3))
    ((input 3 rfl).prepend [.unit, .unit, sizeRef, memoryRef, .word initHash]) related2 fits2
  obtain ⟨touched3, fits3⟩ := touch_word touched2 53 (by decide)
  obtain ⟨store4, evaluated4, related4, frame4⟩ := writeWord_evaluates
    (((memoryValue.prepend [.unit]).prepend [.unit]).prepend [.unit])
    (((sizeValue.prepend [.unit]).prepend [.unit]).prepend [.unit])
    (CodeValue.number 53 6 (.unit :: .unit :: .unit :: E3))
    (hashValue.prepend [.unit, .unit, .unit, sizeRef, memoryRef]) related3 fits3
  obtain ⟨touched4, fits4⟩ := touch_some touched3 (Word.ofNatModulo 0) (Word.ofNatModulo 85)
    (by rw [val_small (by decide), val_small (by decide)]; decide)
  obtain ⟨store5, evaluated5, frame5⟩ := hash_evaluates
    ((((memoryValue.prepend [.unit]).prepend [.unit]).prepend [.unit]).prepend [.unit])
    ((((sizeValue.prepend [.unit]).prepend [.unit]).prepend [.unit]).prepend [.unit])
    (CodeValue.number 0 7 (.unit :: .unit :: .unit :: .unit :: E3))
    (CodeValue.number 85 7 (.unit :: .unit :: .unit :: .unit :: E3)) related4 fits4
    ((create2Scratch_keccak creator salt initHash).mp hashed)
  refine ⟨store5, .letE evaluated (LanguageResult.bind_success .word hashEvaluated ?_),
    scratch_frame hashFrame ((((frame1.trans frame2).trans frame3).trans frame4).trans frame5)⟩
  apply Evaluates.letE (bodyStore := hashStore ++ [WordMapping.encode []])
  · exact .newCell (.construct .unit)
  · apply Evaluates.letE (bodyStore := allocated)
    · simpa only [allocated, List.length_append, List.length_cons, List.length_nil, List.append_assoc,
        List.cons_append, List.nil_append, CodeBuilder.allocate, CodeBuilder.number, CodeBuilder.constant] using
        (Evaluates.newCell (elementType := .word) (environment := memoryRef :: E1)
          (initialStore := hashStore ++ [WordMapping.encode []]) Evaluates.word (initialValue := .word (Word.ofNatModulo 0)))
    · exact LanguageResult.bind_success .word evaluated1 (LanguageResult.bind_success .word evaluated2
        (LanguageResult.bind_success .word evaluated3 (LanguageResult.bind_success .word evaluated4
          (LanguageResult.bind_success .word evaluated5 (.inRight (.binary
            ((CodeValue.bound 7 (.unit :: .unit :: .unit :: .unit :: E3) (.word digest)).evaluates store5) .word rfl))))))

end Solcore.Frontend.RustHull.CreationAddressCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.CreationHandlerCorrespondence
/-! The create handler installed by the object initializer refuses an attempt
whose endowment exceeds the creator's balance, or whose creator nonce is
exhausted, before it derives an address. The closure records the actual
captured shared references and runtime installation; init selection and the
identification of a nonempty runtime image stay abstract. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.CreationCorrespondence
open Core Correspondence ScalarExecution CodeBuilder AccountCallCorrespondence

def addressMask : Word := Word.ofNatModulo (2 ^ 160 - 1)

theorem mask_idempotent (address : Word) :
    (address.bitAnd addressMask).bitAnd addressMask = address.bitAnd addressMask := by
  apply Fin.ext
  simp [Word.bitAnd, Nat.and_assoc]

/-- A creation request as the creating frame passes it to the create handler. -/
structure Request where
  creator : Word
  value : Word
  salt : Word
  create2 : Bool
  depth : Word
  gas : Word
  initCode : MemorySemantics.Entries
  initLength : Word

def requestValue (request : Request) : Value :=
  bundleValues [.word request.creator, .word request.value, .word request.salt, .bool request.create2,
    .word request.depth, .word request.gas, WordMapping.encode request.initCode, .word request.initLength]

/-- The successful callback result of a refused attempt: no address and no
revert bytes. -/
def refusedValue : Value :=
  .inRight .word (bundleValues [.word Word.zero, WordMapping.encode [], .word Word.zero])

/-- The installed create handler and its captured shared references. -/
structure HandlerClosure (locations : SharedLocations) (value : Value) where
  depth : Nat
  captured : Environment
  shared : AccountRuntime.References
  runInit : Code → Code → Code
  identify : Code → Code
  closure : CapturedClosure
    (lambda Creation.requestType (LanguageResult.resultType Creation.responseType) (fun request =>
      CreationRuntime.dispatch (AccountRuntime.reference shared "world")
        (AccountRuntime.reference shared "balances") (AccountRuntime.reference shared "logs")
        (AccountRuntime.reference shared "logSize") (load (AccountRuntime.reference shared "worldComplete"))
        request runInit (CreationImplementation.installWith identify shared)) depth) captured value
  references : SharedReferences depth captured shared locations

/-- The dispatcher's two refusals, read from the shared account state. -/
inductive Refusing (state : AccountCallSemantics.Shared) (request : Request) : Prop where
  | underfunded
      (shortfall : request.value > StorageSemantics.readWord (request.creator.bitAnd addressMask) state.balances)
  | exhausted {account : AccountState.Account}
      (funded : ¬request.value > StorageSemantics.readWord (request.creator.bitAnd addressMask) state.balances)
      (found : StorageSemantics.get state.world (request.creator.bitAnd addressMask) state.complete = .ok account)
      (limit : account.nonce > Word.ofNatModulo (2 ^ 64 - 2))

private theorem refused_evaluates (depth : Nat) (environment : Environment) (store : Store) :
    Evaluates environment store (CreationImplementation.refused depth) refusedValue store :=
  .inRight (.pair .word (.pair (.construct .unit) .word))

theorem dispatchWith_refused {depth : Nat} {environment : Environment} {store : Store}
    {shared : AccountRuntime.References} {locations : SharedLocations}
    {requestCode : Code} {request : Request} {state : AccountCallSemantics.Shared}
    (rest : Code → Code → Code → Code)
    (references : SharedReferences depth environment shared locations)
    (requestRelated : CodeValue depth environment requestCode (requestValue request))
    (related : SharedStateRel locations state store)
    (refusing : Refusing state request) :
    ∃ final, Evaluates environment store
      (CreationImplementation.dispatchWith (AccountRuntime.reference shared "world")
        (AccountRuntime.reference shared "balances") (AccountRuntime.reference shared "logs")
        (AccountRuntime.reference shared "logSize") (load (AccountRuntime.reference shared "worldComplete"))
        requestCode rest depth) refusedValue final ∧ StoreRetains store final := by
  obtain ⟨accounts, worldSame, worldRead⟩ := related.world
  let argsValue := bundleValues [.cellRef AccountState.type locations.world,
    .cellRef WordMapping.type locations.balances, .cellRef WordMapping.type locations.logs,
    .cellRef .word locations.logSize, .bool state.complete, requestValue request]
  have packed : Evaluates environment store
      (packet [AccountRuntime.reference shared "world", AccountRuntime.reference shared "balances",
        AccountRuntime.reference shared "logs", AccountRuntime.reference shared "logSize",
        load (AccountRuntime.reference shared "worldComplete"), requestCode] depth) argsValue store :=
    .pair (references.world.evaluates store) (.pair (references.balances.evaluates store)
      (.pair (references.logs.evaluates store) (.pair (references.logSize.evaluates store)
        (.pair (.loadCell (references.complete.evaluates store) related.complete) (requestRelated.evaluates store)))))
  have argsCode := CodeValue.bound depth environment argsValue
  have requestCode' : CodeValue (depth + 1) (argsValue :: environment)
      (part 5 6 (fun here => .var (here - depth - 1))) (requestValue request) :=
    argsCode.part (index := 5) rfl
  let key := request.creator.bitAnd addressMask
  have keyEvaluated : Evaluates (argsValue :: environment) store
      (address (part 0 8 (part 5 6 (fun here => .var (here - depth - 1)))) (depth + 1)) (.word key) store :=
    .binary ((requestCode'.part (index := 0) rfl).evaluates store) .word rfl
  obtain ⟨looked, lookedEvaluated, lookedRetained⟩ := lookup_preserves
    (.loadCell ((argsCode.part (index := 1) rfl).evaluates store) related.balances) keyEvaluated
  let balance := StorageSemantics.readWord key state.balances
  have afterBalance := argsCode.prepend [.word balance]
  have valueEvaluated : Evaluates (.word balance :: argsValue :: environment) looked
      (part 1 8 (part 5 6 (fun here => .var (here - depth - 1))) (depth + 1 + 1)) (.word request.value) looked :=
    ((requestCode'.part (index := 1) rfl).prepend [.word balance]).evaluates looked
  have balanceEvaluated : Evaluates (.word balance :: argsValue :: environment) looked
      ((fun here => Expr.var (here - (depth + 1) - 1)) (depth + 1 + 1)) (.word balance) looked :=
    (CodeValue.bound (depth + 1) (argsValue :: environment) (.word balance)).evaluates looked
  unfold CreationImplementation.dispatchWith
  cases refusing with
  | underfunded shortfall =>
      refine ⟨looked, .letE packed ?_, lookedRetained⟩
      apply LanguageResult.bind_success Creation.responseType lookedEvaluated
      exact .ifTrue (.binary valueEvaluated balanceEvaluated (by simp [BinaryOp.apply, balance, key, shortfall]))
        (refused_evaluates _ _ _)
  | exhausted funded found limit =>
      have sourced := StorageCorrespondence.get_source accounts key state.complete
      rw [worldSame, found] at sourced
      obtain ⟨⟨account, identity⟩, got, same⟩ : ∃ entry, StorageCorrespondence.get accounts key state.complete = .ok entry ∧
          entry.1 = _ := by
        cases got : StorageCorrespondence.get accounts key state.complete with
        | error reason => simp [got, Except.map] at sourced
        | ok entry =>
            simp only [got, Except.map, Except.ok.injEq] at sourced
            exact ⟨entry, rfl, sourced⟩
      cases same
      let recordValue := StorageCorrespondence.record account identity
      have worldLoaded : Evaluates (.word balance :: argsValue :: environment) looked
          (load (part 0 6 (fun here => .var (here - depth - 1))) (depth + 1 + 1))
          (StorageCorrespondence.world accounts) looked :=
        .loadCell (((argsCode.part (index := 0) rfl).prepend [.word balance]).evaluates looked)
          ((lookedRetained.read _ (List.getElem?_eq_some_iff.mp worldRead).1).trans worldRead)
      have creatorEvaluated : Evaluates (.word balance :: argsValue :: environment) looked
          (address (part 0 8 (part 5 6 (fun here => .var (here - depth - 1)))) (depth + 1 + 1)) (.word key) looked :=
        .binary (((requestCode'.part (index := 0) rfl).prepend [.word balance]).evaluates looked) .word rfl
      have completeEvaluated : Evaluates (.word balance :: argsValue :: environment) looked
          (part 4 6 (fun here => .var (here - depth - 1)) (depth + 1 + 1)) (.bool state.complete) looked :=
        ((argsCode.part (index := 4) rfl).prepend [.word balance]).evaluates looked
      have recordRead := StorageCorrespondence.get_evaluates accounts key state.complete
        worldLoaded creatorEvaluated completeEvaluated
      rw [got] at recordRead
      let recordStore := StorageCorrespondence.getStore accounts key state.complete
        (.word balance :: argsValue :: environment) looked
      have recordRetained : StoreRetains looked recordStore := StoreRetains.append _ _
      have nonceEvaluated : Evaluates (recordValue :: .word balance :: argsValue :: environment) recordStore
          (part 2 9 (fun here => .var (here - (depth + 1 + 1) - 1)) (depth + 1 + 1 + 1)) (.word account.nonce) recordStore :=
        ((CodeValue.bound (depth + 1 + 1) (.word balance :: argsValue :: environment) recordValue).part
          (index := 2) rfl).evaluates recordStore
      refine ⟨recordStore, .letE packed ?_, lookedRetained.trans recordRetained⟩
      apply LanguageResult.bind_success Creation.responseType lookedEvaluated
      apply Evaluates.ifFalse (.binary valueEvaluated balanceEvaluated (by simp [BinaryOp.apply, balance, key, funded]))
      apply LanguageResult.bind_success Creation.responseType recordRead
      exact .ifTrue (.binary nonceEvaluated .word (by simp [BinaryOp.apply, limit])) (refused_evaluates _ _ _)

/-- Applying the actual installed closure to a refusing request returns the
refused response. Only helper cells are appended; no existing cell changes. -/
theorem HandlerClosure.apply_refused {locations : SharedLocations} {value : Value}
    (closure : HandlerClosure locations value) {request : Request} {state : AccountCallSemantics.Shared}
    {environment : Environment} {before middle initial : Store} {function argument : Core.Expr}
    (related : SharedStateRel locations state initial) (refusing : Refusing state request)
    (resolved : Evaluates environment before function value middle)
    (supplied : Evaluates environment middle argument (requestValue request) initial) :
    ∃ final, Evaluates environment before (.apply function argument) refusedValue final ∧
      StoreRetains initial final := by
  rcases closure with ⟨depth, captured, shared, runInit, identify, capturedClosure, references⟩
  cases capturedClosure
  obtain ⟨final, evaluated, retained⟩ := dispatchWith_refused
    (CreationImplementation.admitted runInit (CreationImplementation.installWith identify shared))
    (references.prepend [requestValue request]) (CodeValue.bound depth captured (requestValue request))
    related refusing
  exact ⟨final, .apply resolved supplied evaluated, retained⟩

end Solcore.Frontend.RustHull.CreationCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.CreationAdmittedCorrespondence
/-! The installed create handler completes admitted attempts that run no init
frame. The actual dispatcher derives the address, advances the creator nonce,
loads its checkpoint and examines the target: a nonzero nonce or code size is a
collision that returns zero, and an address absent from a complete world
receives a new account, the endowment and the empty runtime image. An unknown
target and an endowment overflow fail with reasons 7 and 12; the protection
then runs the checkpoint's restoration, so only the nonce advance remains.
Catalog code links survive every outcome. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.CreationCorrespondence
open Core Correspondence ScalarExecution CodeBuilder AccountCallCorrespondence

theorem bundle_evaluates {environment : Environment} {store : Store} :
    ∀ {expressions : List Core.Expr} {values : List Value}, expressions.length = values.length →
      (∀ (index : Nat) (expression : Core.Expr) (value : Value), expressions[index]? = some expression →
        values[index]? = some value → Evaluates environment store expression value store) →
      Evaluates environment store (bundle expressions) (bundleValues values) store
  | [], [], _, _ => .unit
  | [expression], [value], _, each => each 0 expression value rfl rfl
  | expression :: next :: rest, value :: nextValue :: restValues, same, each =>
      .pair (each 0 expression value rfl rfl)
        (bundle_evaluates (expressions := next :: rest) (values := nextValue :: restValues)
          (by simpa using same) (fun index => each (index + 1)))
  | [], _ :: _, same, _ => by simp at same
  | _ :: _, [], same, _ => by simp at same
  | [_], _ :: _ :: _, same, _ => by simp at same
  | _ :: _ :: _, [_], same, _ => by simp at same

/-- `AccountState.replace` over an evaluated nine-field record. -/
theorem replace_evaluates {environment : Environment} {store : Store} {recordExpr valueExpr : Core.Expr}
    {fields : List Value} {value : Value} (index : Nat) (nine : fields.length = 9)
    (recordEvaluated : Evaluates environment store recordExpr (bundleValues fields) store)
    (valueEvaluated : Evaluates environment store valueExpr value store) :
    Evaluates environment store (AccountState.replace recordExpr index valueExpr)
      (bundleValues (fields.set index value)) store := by
  unfold AccountState.replace
  apply bundle_evaluates (by simp [nine])
  intro item expression result expressionFound valueFound
  have itemSmall : item < 9 := by
    have := (List.getElem?_eq_some_iff.mp expressionFound).1
    simpa using this
  simp only [List.getElem?_map, List.getElem?_range itemSmall, Option.map_some, Option.some.injEq] at expressionFound
  subst expressionFound
  by_cases same : item = index
  · subst same
    rw [List.getElem?_set_self (by omega), Option.some.injEq] at valueFound
    subst valueFound
    simpa using valueEvaluated
  · rw [List.getElem?_set_ne (Ne.symm same)] at valueFound
    have different : (item == index) = false := beq_eq_false_iff_ne.mpr same
    simp only [different, Bool.false_eq_true, ↓reduceIte, AccountState.field]
    rw [← nine]
    exact projectArgument_evaluates recordEvaluated valueFound

def fields (account : AccountState.Account) (identity : Nat) : List Value :=
  [WordMapping.encode account.storage, WordMapping.encode account.transient,
    .word account.nonce, .word (Word.ofNatModulo identity),
    WordMapping.encode (Memory.packBytes (account.code.getD [])),
    .word (Word.ofNatModulo (account.code.getD []).length),
    .bool account.code.isSome, .bool account.created, .bool account.destroyed]

theorem fields_record (account : AccountState.Account) (identity : Nat) :
    bundleValues (fields account identity) = StorageCorrespondence.record account identity := rfl

theorem fields_length (account : AccountState.Account) (identity : Nat) : (fields account identity).length = 9 := rfl

/-- The address scheme a request selects. -/
def Request.scheme (request : Request) : CreationAddressSemantics.Scheme :=
  if request.create2 then .create2 request.salt else .create

theorem deriveAddress_evaluates {depth : Nat} {environment : Environment} {store : Store}
    {creatorCode nonceCode requestCode : Code} {creator nonce target : Word} {request : Request}
    (creatorValue : CodeValue depth environment creatorCode (.word creator))
    (nonceValue : CodeValue depth environment nonceCode (.word nonce))
    (requested : CodeValue depth environment requestCode (requestValue request))
    (bounded : request.initLength.val ≤ 49152)
    (derived : CreationAddressSemantics.Derived creator nonce request.initCode request.initLength
      request.scheme target) :
    ∃ next, Evaluates environment store (CreationImplementation.deriveAddress creatorCode nonceCode requestCode depth)
      (.inRight .word (.word target)) next ∧ StoreRetains store next := by
  unfold CreationImplementation.deriveAddress
  have flag : Evaluates environment store (part 3 8 requestCode depth) (.bool request.create2) store :=
    (requested.part (index := 3) rfl).evaluates store
  cases create2 : request.create2 with
  | false =>
      rw [create2] at flag
      simp only [Request.scheme, create2, Bool.false_eq_true, ↓reduceIte] at derived
      cases derived with
      | create hashed =>
          obtain ⟨final, evaluated, retained⟩ := CreationAddressCorrespondence.createAddress_evaluates
            (.pair (creatorValue.evaluates store) (nonceValue.evaluates store)) hashed
          exact ⟨final, .ifFalse flag evaluated, retained⟩
  | true =>
      rw [create2] at flag
      simp only [Request.scheme, create2, ↓reduceIte] at derived
      cases derived with
      | create2 initHashed hashed =>
          let initRef := Value.cellRef WordMapping.type store.length
          let sizeRef := Value.cellRef .word (store.length + 1)
          let allocated : Store := store ++ [WordMapping.encode request.initCode, .word (Word.ofNatModulo 0)]
          have initRelated : MemoryCorrespondence.StateRel store.length (store.length + 1)
              ⟨request.initCode, Word.ofNatModulo 0⟩ allocated := by
            refine ⟨by omega, ?_, ?_⟩ <;> simp [allocated, Store.read?]
          have memoryValue := (CodeValue.bound depth environment initRef).prepend [sizeRef]
          have sizeValue := CodeValue.bound (depth + 1) (initRef :: environment) sizeRef
          have argumentsEvaluated := Evaluates.pair (memoryValue.evaluates allocated)
            (.pair (sizeValue.evaluates allocated) (.pair ((creatorValue.prepend [sizeRef, initRef]).evaluates allocated)
              (.pair (((requested.part (index := 2) rfl).prepend [sizeRef, initRef]).evaluates allocated)
                (.pair (Evaluates.word (value := Word.ofNatModulo 0))
                  (((requested.part (index := 7) rfl).prepend [sizeRef, initRef]).evaluates allocated)))))
          obtain ⟨final, evaluated, frame⟩ := CreationAddressCorrespondence.create2Address_evaluates
            argumentsEvaluated initRelated bounded initHashed hashed
          refine ⟨final, .ifTrue flag ?_, CreationAddressCorrespondence.scratch_retains frame⟩
          apply Evaluates.letE (bodyStore := store ++ [WordMapping.encode request.initCode])
          · exact .newCell ((requested.part (index := 6) rfl).evaluates store)
          · apply Evaluates.letE (bodyStore := allocated)
            · simpa only [allocated, List.length_append, List.length_cons, List.length_nil, List.append_assoc,
                List.cons_append, List.nil_append, CodeBuilder.allocate, CodeBuilder.number, CodeBuilder.constant] using
                (Evaluates.newCell (elementType := .word) (environment := initRef :: environment)
                  (initialStore := store ++ [WordMapping.encode request.initCode]) Evaluates.word
                  (initialValue := .word (Word.ofNatModulo 0)))
            · exact evaluated

theorem putStore_extension (accounts : StorageCorrespondence.Accounts) (address : Word) (account : AccountState.Account)
    (identity : Nat) (environment : Environment) (store : Store) :
    ∃ suffix, StorageCorrespondence.putStore accounts address account identity environment store = store ++ suffix :=
  ⟨_, rfl⟩

/-- Writes that change one cell and append helper cells. -/
structure Overwrites (location : Nat) (initial final : Store) : Prop where
  length_le : initial.length ≤ final.length
  read : ∀ other value, other ≠ location → initial.read? other = some value → final.read? other = some value

theorem Overwrites.append (location : Nat) (store suffix : Store) : Overwrites location store (store ++ suffix) :=
  ⟨by simp, fun _ _ _ found => StorageCorrespondence.appended_read found _⟩

theorem Overwrites.set {location : Nat} {initial final : Store} (overwrites : Overwrites location initial final)
    (value : Value) : Overwrites location initial (final.set location value) :=
  ⟨by simpa using overwrites.length_le, fun other old different found => by
    change (final.set location value)[other]? = some old
    rw [List.getElem?_set_ne (Ne.symm different)]
    exact overwrites.read other old different found⟩

theorem Overwrites.trans {location : Nat} {initial middle final : Store}
    (first : Overwrites location initial middle) (second : Overwrites location middle final) :
    Overwrites location initial final :=
  ⟨Nat.le_trans first.length_le second.length_le, fun other value different found =>
    second.read other value different (first.read other value different found)⟩

theorem Overwrites.ofRetains {location : Nat} {initial final : Store} (retained : StoreRetains initial final) :
    Overwrites location initial final :=
  ⟨retained.length_le, fun other _ _ found =>
    (retained.read other (List.getElem?_eq_some_iff.mp found).1).trans found⟩

/-- The actual nonce write: read the account, replace field 2, store the world. -/
theorem writeNonce_evaluates {environment : Environment} {initial store : Store}
    {worldReference addressExpr completeExpr valueExpr : Core.Expr}
    (accounts : StorageCorrespondence.Accounts) (location : Nat) (address : Word) (complete : Bool) (nonce : Word)
    (arguments : Evaluates environment initial (bundle [worldReference, addressExpr, completeExpr, valueExpr])
      (bundleValues [.cellRef AccountState.type location, .word address, .bool complete, .word nonce]) store)
    (found : store.read? location = some (StorageCorrespondence.world accounts))
    {account : AccountState.Account} {identity : Nat}
    (obtained : StorageCorrespondence.get accounts address complete = .ok (account, identity)) :
    ∃ next, Evaluates environment initial (AccountState.writeField worldReference addressExpr completeExpr 2 valueExpr)
        (.inRight .word .unit) next ∧
      next.read? location = some (StorageCorrespondence.world
        (StorageCorrespondence.put address {account with nonce := nonce} identity accounts)) ∧
      Overwrites location store next := by
  let argumentValue := bundleValues [.cellRef AccountState.type location, .word address, .bool complete, .word nonce]
  have fetched := StorageCorrespondence.get_evaluates
    (environment := argumentValue :: environment)
    (initial := store) (worldStore := store) (addressStore := store) (final := store)
    (worldExpr := .loadCell (.first (.var 0)))
    (addressExpr := .first (.second (.var 0)))
    (completeExpr := .first (.second (.second (.var 0)))) accounts address complete
    (.loadCell (.first (.var rfl)) found)
    (.first (.second (.var rfl))) (.first (.second (.second (.var rfl))))
  rw [obtained] at fetched
  let fetchedStore := StorageCorrespondence.getStore accounts address complete (argumentValue :: environment) store
  obtain ⟨fetchedSuffix, _, fetchedSame⟩ := StorageCorrespondence.getStore_extension accounts address complete
    (argumentValue :: environment) store
  have current : fetchedStore.read? location = some (StorageCorrespondence.world accounts) := by
    change (StorageCorrespondence.getStore accounts address complete (argumentValue :: environment) store).read? location = _
    rw [fetchedSame]
    exact StorageCorrespondence.appended_read found _
  let updatedAccount : AccountState.Account := {account with nonce := nonce}
  have updated := StorageCorrespondence.put_evaluates
    (environment := StorageCorrespondence.record account identity :: argumentValue :: environment)
    (initial := fetchedStore) (mappingStore := fetchedStore) (addressStore := fetchedStore) (final := fetchedStore)
    (mapping := .loadCell (projectArgument 0 4 (.var 1)))
    (addressExpr := projectArgument 1 4 (.var 1))
    (accountExpr := AccountState.replace (.var 0) 2 (projectArgument 3 4 (.var 1)))
    accounts address updatedAccount identity
    (.loadCell (.first (.var rfl)) current) (.first (.second (.var rfl)))
    (replace_evaluates (fields := fields account identity) 2 rfl (.var rfl) (.second (.second (.second (.var rfl)))))
  let putStore := StorageCorrespondence.putStore accounts address updatedAccount identity
    (StorageCorrespondence.record account identity :: argumentValue :: environment) fetchedStore
  obtain ⟨putSuffix, putSame⟩ := putStore_extension accounts address updatedAccount identity
    (StorageCorrespondence.record account identity :: argumentValue :: environment) fetchedStore
  have latest : putStore.read? location = some (StorageCorrespondence.world accounts) := by
    change (StorageCorrespondence.putStore accounts address updatedAccount identity _ fetchedStore).read? location = _
    rw [putSame]
    exact StorageCorrespondence.appended_read current _
  have overwrites : Overwrites location store putStore := by
    change Overwrites location store (StorageCorrespondence.putStore accounts address updatedAccount identity _ fetchedStore)
    rw [putSame]
    change Overwrites location store ((StorageCorrespondence.getStore accounts address complete _ store) ++ putSuffix)
    rw [fetchedSame, List.append_assoc]
    exact Overwrites.append location store _
  refine ⟨putStore.set location (StorageCorrespondence.world (StorageCorrespondence.put address updatedAccount identity accounts)),
    ?_, ?_, overwrites.set _⟩
  · unfold AccountState.writeField CodeBuilder.bind CodeBuilder.constant
    apply Evaluates.letE arguments
    apply LanguageResult.bind_success .unit fetched
    apply LanguageResult.bind_success .unit updated
    exact .inRight (.storeCell (.first (.var rfl)) latest (.var rfl)
      (Store.write?_eq_some_iff.mpr ⟨(List.getElem?_eq_some_iff.mp latest).1, rfl⟩))
  · have bound := (List.getElem?_eq_some_iff.mp latest).1
    change (putStore.set location _)[location]? = _
    rw [List.getElem?_set_self bound]

/-- The restoration code of the checkpoint, storing the four loaded values. -/
def restoreCode (world balances logs logSize : Code) (depth : Nat) : Code :=
  bind (CodeBuilder.store logSize (fun here => .var (here - (depth + 3) - 1))) fun _ =>
  bind (CodeBuilder.store logs (fun here => .var (here - (depth + 2) - 1))) fun _ =>
  bind (CodeBuilder.store balances (fun here => .var (here - (depth + 1) - 1))) fun _ =>
  bind (CodeBuilder.store world (fun here => .var (here - depth - 1))) fun _ => CodeBuilder.unit

/-- The checkpoint loads the four shared cells in order; its restoration code
is only reached by a failure. -/
theorem checkpoint_evaluates {depth : Nat} {environment : Environment} {store final : Store}
    {world balances logs logSize : Code} {continuation : Code → Code}
    {worldValue balancesValue logsValue logSizeValue result : Value}
    {worldType balancesType logsType logSizeType : Core.Ty}
    {worldLocation balancesLocation logsLocation logSizeLocation : Nat}
    (worldCode : CodeValue depth environment world (.cellRef worldType worldLocation))
    (balancesCode : CodeValue depth environment balances (.cellRef balancesType balancesLocation))
    (logsCode : CodeValue depth environment logs (.cellRef logsType logsLocation))
    (logSizeCode : CodeValue depth environment logSize (.cellRef logSizeType logSizeLocation))
    (worldRead : store.read? worldLocation = some worldValue)
    (balancesRead : store.read? balancesLocation = some balancesValue)
    (logsRead : store.read? logsLocation = some logsValue)
    (logSizeRead : store.read? logSizeLocation = some logSizeValue)
    (continued : Evaluates (logSizeValue :: logsValue :: balancesValue :: worldValue :: environment) store
      (continuation (restoreCode world balances logs logSize depth) (depth + 4)) result final) :
    Evaluates environment store
      (CreationImplementation.checkpoint [world, balances, logs, logSize] continuation depth) result final := by
  simp only [CreationImplementation.checkpoint, CreationImplementation.checkpoint.capture, CodeBuilder.bind, CodeBuilder.load]
  apply Evaluates.letE (.loadCell (worldCode.evaluates store) worldRead)
  apply Evaluates.letE (.loadCell ((balancesCode.prepend [worldValue]).evaluates store) balancesRead)
  apply Evaluates.letE (.loadCell ((logsCode.prepend [balancesValue, worldValue]).evaluates store) logsRead)
  apply Evaluates.letE (.loadCell ((logSizeCode.prepend [logsValue, balancesValue, worldValue]).evaluates store) logSizeRead)
  exact continued

/-- The restoration stores the four values loaded by the checkpoint. -/
theorem restoreCode_evaluates {checkpoint depth : Nat} {environment : Environment} {store : Store}
    {world balances logs logSize : Code} {worldType balancesType logsType logSizeType : Core.Ty}
    {worldLocation balancesLocation logsLocation logSizeLocation : Nat}
    {worldValue balancesValue logsValue logSizeValue : Value}
    (worldCode : CodeValue depth environment world (.cellRef worldType worldLocation))
    (balancesCode : CodeValue depth environment balances (.cellRef balancesType balancesLocation))
    (logsCode : CodeValue depth environment logs (.cellRef logsType logsLocation))
    (logSizeCode : CodeValue depth environment logSize (.cellRef logSizeType logSizeLocation))
    (savedWorld : CodeValue depth environment (fun here => .var (here - checkpoint - 1)) worldValue)
    (savedBalances : CodeValue depth environment (fun here => .var (here - (checkpoint + 1) - 1)) balancesValue)
    (savedLogs : CodeValue depth environment (fun here => .var (here - (checkpoint + 2) - 1)) logsValue)
    (savedLogSize : CodeValue depth environment (fun here => .var (here - (checkpoint + 3) - 1)) logSizeValue)
    (worldBound : worldLocation < store.length) (balancesBound : balancesLocation < store.length)
    (logsBound : logsLocation < store.length) (logSizeBound : logSizeLocation < store.length) :
    Evaluates environment store (restoreCode world balances logs logSize checkpoint depth) .unit
      ((((store.set logSizeLocation logSizeValue).set logsLocation logsValue).set balancesLocation balancesValue).set
        worldLocation worldValue) := by
  have logsBound' : logsLocation < (store.set logSizeLocation logSizeValue).length := by
    simpa only [List.length_set] using logsBound
  have balancesBound' : balancesLocation <
      ((store.set logSizeLocation logSizeValue).set logsLocation logsValue).length := by
    simpa only [List.length_set] using balancesBound
  have worldBound' : worldLocation <
      (((store.set logSizeLocation logSizeValue).set logsLocation logsValue).set balancesLocation balancesValue).length := by
    simpa only [List.length_set] using worldBound
  unfold restoreCode
  apply Evaluates.letE (.storeCell (logSizeCode.evaluates store) (List.getElem?_eq_getElem logSizeBound)
    (savedLogSize.evaluates store) (Store.write?_eq_some_iff.mpr ⟨logSizeBound, rfl⟩))
  apply Evaluates.letE (.storeCell ((logsCode.prepend [.unit]).evaluates _) (List.getElem?_eq_getElem logsBound')
    ((savedLogs.prepend [.unit]).evaluates _) (Store.write?_eq_some_iff.mpr ⟨logsBound', rfl⟩))
  apply Evaluates.letE (.storeCell ((balancesCode.prepend [.unit, .unit]).evaluates _)
    (List.getElem?_eq_getElem balancesBound') ((savedBalances.prepend [.unit, .unit]).evaluates _)
    (Store.write?_eq_some_iff.mpr ⟨balancesBound', rfl⟩))
  apply Evaluates.letE (.storeCell ((worldCode.prepend [.unit, .unit, .unit]).evaluates _)
    (List.getElem?_eq_getElem worldBound') ((savedWorld.prepend [.unit, .unit, .unit]).evaluates _)
    (Store.write?_eq_some_iff.mpr ⟨worldBound', rfl⟩))
  exact .unit

/-- A successful attempt passes through the protection unchanged. -/
theorem protect_succeeded {depth : Nat} {environment : Environment} {store final : Store}
    {restore attempt : Code} {payload : Value}
    (attempted : Evaluates environment store (attempt depth) (.inRight .word payload) final) :
    Evaluates environment store (CreationImplementation.protect restore attempt depth) (.inRight .word payload) final :=
  .caseRight attempted (.inRight (.var rfl))

/-- A failed attempt restores the checkpoint and keeps its reason. -/
theorem protect_failed {depth : Nat} {environment : Environment} {store current final : Store}
    {restore attempt : Code} {reason : Word} {failedType : Core.Ty}
    (attempted : Evaluates environment store (attempt depth) (.inLeft failedType (.word reason)) current)
    (restored : Evaluates (.word reason :: environment) current (restore (depth + 1)) .unit final) :
    Evaluates environment store (CreationImplementation.protect restore attempt depth)
      (.inLeft Creation.responseType (.word reason)) final :=
  .caseLeft attempted (.letE restored
    (.inLeft (((CodeValue.bound depth environment (.word reason)).prepend [.unit]).evaluates final)))

/-- The endowment moves from the creator to a different new account, using the
creator balance already read by the funds check. -/
theorem transfer_evaluates {depth : Nat} {environment : Environment} {store : Store}
    {balancesCode creatorCode targetCode valueCode creatorBalanceCode : Code}
    {location : Nat} {creator target value : Word} {balances next : StorageSemantics.Words}
    (reference : CodeValue depth environment balancesCode (.cellRef WordMapping.type location))
    (creatorValue : CodeValue depth environment creatorCode (.word creator))
    (targetValue : CodeValue depth environment targetCode (.word target))
    (valueValue : CodeValue depth environment valueCode (.word value))
    (creatorBalanceValue : CodeValue depth environment creatorBalanceCode
      (.word (StorageSemantics.readWord creator balances)))
    (balancesRead : store.read? location = some (WordMapping.encode balances))
    (different : creator ≠ target)
    (transferred : AccountCallSemantics.transfer creator target value balances = .ok next) :
    ∃ final, Evaluates environment store
        (CreationImplementation.transfer balancesCode creatorCode targetCode valueCode creatorBalanceCode depth)
        (.inRight .word .unit) final ∧
      final.read? location = some (WordMapping.encode next) ∧ Overwrites location store final := by
  unfold CreationImplementation.transfer
  by_cases zero : value == Word.zero
  · simp only [AccountCallSemantics.transfer, zero, ↓reduceIte, Except.ok.injEq] at transferred
    subst transferred
    refine ⟨store, ?_, balancesRead, .ofRetains (.refl _)⟩
    exact .ifTrue (.binary (valueValue.evaluates store) .word
      (by change some (Value.bool (value == Word.zero)) = some (Value.bool _); simp only [zero])) (.inRight .unit)
  have zeroFalse : (value == Word.zero) = false := Bool.eq_false_iff.mpr zero
  have sameFalse : (creator == target) = false := beq_eq_false_iff_ne.mpr different
  let creatorBalance := StorageSemantics.readWord creator balances
  let targetBalance := StorageSemantics.readWord target balances
  by_cases overflow : targetBalance > Word.maximum.sub value
  · simp only [AccountCallSemantics.transfer, zeroFalse, sameFalse, Bool.false_eq_true, ↓reduceIte] at transferred
    rw [if_pos overflow] at transferred
    cases transferred
  simp only [AccountCallSemantics.transfer, zeroFalse, sameFalse, Bool.false_eq_true, ↓reduceIte] at transferred
  rw [if_neg overflow, Except.ok.injEq] at transferred
  subst transferred
  obtain ⟨first, targetLooked, firstRetained⟩ := lookup_preserves
    (.loadCell (reference.evaluates store) balancesRead) (targetValue.evaluates store)
  have targetBound := CodeValue.bound depth environment (.word targetBalance)
  let firstEnv : Environment := [.word targetBalance]
  have overflowTest : Evaluates (firstEnv ++ environment) first
      (binary .wordGt (fun here => .var (here - depth - 1))
        (binary .wordSub (number (wordModulus - 1)) valueCode) (depth + 1))
      (.bool (decide (targetBalance > Word.maximum.sub value))) first :=
    .binary (targetBound.evaluates first) (.binary .word ((valueValue.prepend firstEnv).evaluates first) rfl) rfl
  let debited := StorageSemantics.writeWord creator (creatorBalance.sub value) balances
  obtain ⟨second, debitEvaluated, secondRetained⟩ := AccountCallCorrespondence.insert_preserves
    (entries := balances) (key := creator) (value := creatorBalance.sub value)
    (.loadCell ((reference.prepend firstEnv).evaluates first) (AccountCallCorrespondence.retained_read firstRetained balancesRead))
    ((creatorValue.prepend firstEnv).evaluates first)
    (.binary (op := .wordSub) ((creatorBalanceValue.prepend firstEnv).evaluates first)
      ((valueValue.prepend firstEnv).evaluates first) rfl)
  let secondEnv : Environment := WordMapping.encode debited :: firstEnv
  have debitBound := CodeValue.bound (depth + 1) (firstEnv ++ environment) (WordMapping.encode debited)
  obtain ⟨third, creditEvaluated, thirdRetained⟩ := AccountCallCorrespondence.insert_preserves
    (entries := debited) (key := target) (value := targetBalance.add value)
    (debitBound.evaluates second) ((targetValue.prepend secondEnv).evaluates second)
    (.binary (op := .wordAdd) ((targetBound.prepend [WordMapping.encode debited]).evaluates second)
      ((valueValue.prepend secondEnv).evaluates second) rfl)
  let credited := StorageSemantics.writeWord target (targetBalance.add value) debited
  let thirdEnv : Environment := WordMapping.encode credited :: secondEnv
  have creditBound := CodeValue.bound (depth + 2) (secondEnv ++ environment) (WordMapping.encode credited)
  have retainedAll := (firstRetained.trans secondRetained).trans thirdRetained
  have readable := AccountCallCorrespondence.retained_read retainedAll balancesRead
  have bound := (List.getElem?_eq_some_iff.mp readable).1
  refine ⟨third.set location (WordMapping.encode credited), ?_, ?_, (Overwrites.ofRetains retainedAll).set _⟩
  · apply Evaluates.ifFalse (.binary (valueValue.evaluates store) .word
      (by change some (Value.bool (value == Word.zero)) = some (Value.bool _); simp only [zero]))
    apply LanguageResult.bind_success .unit targetLooked
    apply Evaluates.ifFalse (by simpa only [overflow, decide_false, firstEnv, List.cons_append, List.nil_append] using overflowTest)
    apply LanguageResult.bind_success .unit debitEvaluated
    apply LanguageResult.bind_success .unit creditEvaluated
    exact .inRight (.storeCell ((reference.prepend thirdEnv).evaluates third) readable (creditBound.evaluates third)
      (Store.write?_eq_some_iff.mpr ⟨bound, rfl⟩))
  · change (third.set location _)[location]? = _
    rw [List.getElem?_set_self bound]

/-- An endowment that would overflow the target balance is failure 12 and
changes no balance. -/
theorem transfer_overflow {depth : Nat} {environment : Environment} {store : Store}
    {balancesCode creatorCode targetCode valueCode creatorBalanceCode : Code}
    {location : Nat} {creator target value : Word} {balances : StorageSemantics.Words}
    (reference : CodeValue depth environment balancesCode (.cellRef WordMapping.type location))
    (targetValue : CodeValue depth environment targetCode (.word target))
    (valueValue : CodeValue depth environment valueCode (.word value))
    (balancesRead : store.read? location = some (WordMapping.encode balances))
    (overflowed : AccountCallSemantics.transfer creator target value balances = .error (Word.ofNatModulo 12)) :
    ∃ final, Evaluates environment store
        (CreationImplementation.transfer balancesCode creatorCode targetCode valueCode creatorBalanceCode depth)
        (.inLeft .unit (.word (Word.ofNatModulo 12))) final ∧ StoreRetains store final := by
  unfold CreationImplementation.transfer
  by_cases zero : value == Word.zero
  · simp only [AccountCallSemantics.transfer, zero, ↓reduceIte] at overflowed
    cases overflowed
  have zeroFalse : (value == Word.zero) = false := Bool.eq_false_iff.mpr zero
  let targetBalance := StorageSemantics.readWord target balances
  have overflow : targetBalance > Word.maximum.sub value := by
    by_cases same : creator == target
    · simp only [AccountCallSemantics.transfer, zeroFalse, same, Bool.false_eq_true, ↓reduceIte] at overflowed
      cases overflowed
    by_cases fits : targetBalance > Word.maximum.sub value
    · exact fits
    simp only [AccountCallSemantics.transfer, zeroFalse, same, Bool.false_eq_true, ↓reduceIte] at overflowed
    rw [if_neg fits] at overflowed
    cases overflowed
  obtain ⟨first, targetLooked, firstRetained⟩ := lookup_preserves
    (.loadCell (reference.evaluates store) balancesRead) (targetValue.evaluates store)
  have targetBound := CodeValue.bound depth environment (.word targetBalance)
  let firstEnv : Environment := [.word targetBalance]
  have overflowTest : Evaluates (firstEnv ++ environment) first
      (binary .wordGt (fun here => .var (here - depth - 1))
        (binary .wordSub (number (wordModulus - 1)) valueCode) (depth + 1))
      (.bool (decide (targetBalance > Word.maximum.sub value))) first :=
    .binary (targetBound.evaluates first) (.binary .word ((valueValue.prepend firstEnv).evaluates first) rfl) rfl
  refine ⟨first, ?_, firstRetained⟩
  apply Evaluates.ifFalse (.binary (valueValue.evaluates store) .word
    (by change some (Value.bool (value == Word.zero)) = some (Value.bool _); simp only [zeroFalse]))
  apply LanguageResult.bind_success .unit targetLooked
  exact .ifTrue (by simpa only [overflow, decide_true, firstEnv, List.cons_append, List.nil_append] using overflowTest)
    (.inLeft .word)

/-- Writes that change only the listed cells and append helper cells. -/
structure Rewrites (changed : List Nat) (initial final : Store) : Prop where
  length_le : initial.length ≤ final.length
  read : ∀ other value, other ∉ changed → initial.read? other = some value → final.read? other = some value

theorem Rewrites.trans {changed : List Nat} {initial middle final : Store}
    (first : Rewrites changed initial middle) (second : Rewrites changed middle final) : Rewrites changed initial final :=
  ⟨Nat.le_trans first.length_le second.length_le, fun other value outside found =>
    second.read other value outside (first.read other value outside found)⟩

theorem Rewrites.ofOverwrites {changed : List Nat} {location : Nat} {initial final : Store}
    (overwrites : Overwrites location initial final) (member : location ∈ changed) : Rewrites changed initial final :=
  ⟨overwrites.length_le, fun other value outside found =>
    overwrites.read other value (fun same => outside (same ▸ member)) found⟩

theorem put_put (address : Word) (account other : AccountState.Account) (identity otherIdentity : Nat) :
    ∀ accounts : StorageCorrespondence.Accounts,
      StorageCorrespondence.put address account identity (StorageCorrespondence.put address other otherIdentity accounts) =
        StorageCorrespondence.put address account identity accounts
  | [] => by simp [StorageCorrespondence.put]
  | (head, headIdentity) :: rest => by
      by_cases same : address = head.address
      · simp [StorageCorrespondence.put, same]
      · have different : (address == head.address) = false := beq_eq_false_iff_ne.mpr same
        simp only [StorageCorrespondence.put, different, Bool.false_eq_true, ↓reduceIte]
        rw [put_put address account other identity otherIdentity rest]

/-- With empty init code no init frame runs: the new account receives the
endowment, its empty runtime image installs with identity zero, and the
attempt returns the address with empty revert data. -/
theorem deployment_evaluates {depth : Nat} {environment : Environment} {store : Store}
    {runInit : Code → Code → Code} {identify : Code → Code} {shared : AccountRuntime.References}
    {locations : SharedLocations} {world balances creator value creatorBalance request target restore : Code}
    {accounts : StorageCorrespondence.Accounts} {before after : StorageSemantics.Words}
    {creatorWord valueWord targetWord : Word} {requested : Request}
    (references : SharedReferences depth environment shared locations)
    (worldCode : CodeValue depth environment world (.cellRef AccountState.type locations.world))
    (balancesCode : CodeValue depth environment balances (.cellRef WordMapping.type locations.balances))
    (creatorValue : CodeValue depth environment creator (.word creatorWord))
    (valueValue : CodeValue depth environment value (.word valueWord))
    (creatorBalanceValue : CodeValue depth environment creatorBalance
      (.word (StorageSemantics.readWord creatorWord before)))
    (requestCode : CodeValue depth environment request (requestValue requested))
    (targetValue : CodeValue depth environment target (.word targetWord))
    (worldRead : store.read? locations.world = some (StorageCorrespondence.world accounts))
    (balancesRead : store.read? locations.balances = some (WordMapping.encode before))
    (completeRead : store.read? locations.complete = some (.bool true))
    (distinct : locations.all.Nodup)
    (different : creatorWord ≠ targetWord)
    (emptyInit : requested.initLength = Word.zero)
    (transferred : AccountCallSemantics.transfer creatorWord targetWord valueWord before = .ok after) :
    ∃ final, Evaluates environment store
        (CreationImplementation.deployment runInit (CreationImplementation.installWith identify shared)
          world balances creator value creatorBalance request target restore depth)
        (.inRight .word (bundleValues [.word targetWord, WordMapping.encode [], .word (Word.ofNatModulo 0)])) final ∧
      final.read? locations.world = some (StorageCorrespondence.world
        (StorageCorrespondence.put targetWord (CreationSemantics.createdAccount targetWord) 0 accounts)) ∧
      final.read? locations.balances = some (WordMapping.encode after) ∧
      Rewrites [locations.world, locations.balances] store final := by
  simp only [SharedLocations.all, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at distinct
  obtain ⟨⟨worldLogs, worldSize, worldBalances, worldComplete⟩, ⟨logsSize, logsBalances, logsComplete⟩,
    ⟨sizeBalances, sizeComplete⟩, balancesComplete⟩ := distinct
  let created := CreationSemantics.createdAccount targetWord
  -- the new account record
  have createdRecord (env : Environment) (current : Store) : Evaluates env current
      (AccountState.replace (AccountState.replace AccountState.defaultRecord 2 (.word (Word.ofNatModulo 1))) 7 (.bool true))
      (StorageCorrespondence.record created 0) current :=
    replace_evaluates (fields := (fields {address := targetWord} 0).set 2 (.word (Word.ofNatModulo 1))) 7 rfl
      (replace_evaluates (fields := fields {address := targetWord} 0) 2 rfl
        (StorageCorrespondence.default_evaluates targetWord env current) .word) .bool
  have inserted := StorageCorrespondence.put_evaluates (environment := environment)
    (initial := store) (mappingStore := store) (addressStore := store) (final := store)
    accounts targetWord created 0 (.loadCell (worldCode.evaluates store) worldRead) (targetValue.evaluates store)
    (createdRecord _ _)
  let created1 := StorageCorrespondence.put targetWord created 0 accounts
  let insertedValue := StorageCorrespondence.world created1
  let store1 := StorageCorrespondence.putStore accounts targetWord created 0 environment store
  obtain ⟨suffix1, same1⟩ := putStore_extension accounts targetWord created 0 environment store
  have keep1 {location : Nat} {old : Value} (found : store.read? location = some old) : store1.read? location = some old := by
    change (StorageCorrespondence.putStore accounts targetWord created 0 environment store).read? location = _
    rw [same1]
    exact StorageCorrespondence.appended_read found _
  have bound1 := (List.getElem?_eq_some_iff.mp (keep1 worldRead)).1
  let store2 : Store := store1.set locations.world insertedValue
  have stored : Evaluates (insertedValue :: environment) store1
      (CodeBuilder.store world (fun here => .var (here - depth - 1)) (depth + 1)) .unit store2 :=
    .storeCell ((worldCode.prepend [insertedValue]).evaluates store1) (keep1 worldRead)
      ((CodeValue.bound depth environment insertedValue).evaluates store1) (Store.write?_eq_some_iff.mpr ⟨bound1, rfl⟩)
  have keep2 {location : Nat} {old : Value} (different : location ≠ locations.world)
      (found : store.read? location = some old) : store2.read? location = some old := by
    change (store1.set locations.world insertedValue)[location]? = _
    rw [List.getElem?_set_ne (Ne.symm different)]
    exact keep1 found
  have worldRead2 : store2.read? locations.world = some insertedValue := by
    change (store1.set locations.world insertedValue)[locations.world]? = _
    rw [List.getElem?_set_self bound1]
  have frame2 : Rewrites [locations.world, locations.balances] store store2 := by
    refine ⟨?_, fun other old outside found => keep2 (fun same => outside (by simp [same])) found⟩
    change store.length ≤ (store1.set _ _).length
    rw [List.length_set]
    change store.length ≤ (StorageCorrespondence.putStore accounts targetWord created 0 environment store).length
    rw [same1]; simp
  -- the endowment
  let E2 : Environment := .unit :: insertedValue :: environment
  obtain ⟨store3, transferEvaluated, balancesRead3, transferFrame⟩ := transfer_evaluates
    (balancesCode.prepend [.unit, insertedValue]) (creatorValue.prepend [.unit, insertedValue])
    (targetValue.prepend [.unit, insertedValue]) (valueValue.prepend [.unit, insertedValue])
    (creatorBalanceValue.prepend [.unit, insertedValue]) (keep2 (Ne.symm worldBalances) balancesRead) different
    transferred
  have keep3 {location : Nat} {old : Value} (different : location ≠ locations.balances)
      (found : store2.read? location = some old) : store3.read? location = some old :=
    transferFrame.read location old different found
  -- empty init code returns an empty successful response
  let E3 : Environment := .unit :: E2
  let childValue : Value := bundleValues [.bool true, WordMapping.encode [], .word (Word.ofNatModulo 0)]
  have lengthTest : Evaluates E3 store3 (binary .wordEq (part 7 8 request) (number 0) (depth + 3)) (.bool true) store3 :=
    .binary (((requestCode.part (index := 7) rfl).prepend [.unit, .unit, insertedValue]).evaluates store3) .word
      (by simp [BinaryOp.apply, emptyInit]; rfl)
  have childEvaluated : Evaluates E3 store3
      (choose (binary .wordEq (part 7 8 request) (number 0))
        (success (packet [CodeBuilder.boolean true, empty, number 0])) (runInit target request) (depth + 3))
      (.inRight .word childValue) store3 :=
    .ifTrue lengthTest (.inRight (.pair .bool (.pair (.construct .unit) .word)))
  let E4 : Environment := childValue :: E3
  have childCode := CodeValue.bound (depth + 3) E3 childValue
  have successTest : Evaluates E4 store3 (part 0 3 (fun here => .var (here - (depth + 3) - 1)) (depth + 4))
      (.bool true) store3 := (childCode.part (index := 0) rfl).evaluates store3
  have sizeTest : Evaluates E4 store3 (binary .wordGt (part 2 3 (fun here => .var (here - (depth + 3) - 1)))
      (number 24576) (depth + 4)) (.bool false) store3 :=
    .binary ((childCode.part (index := 2) rfl).evaluates store3) .word (by simp [BinaryOp.apply]; decide)
  obtain ⟨suffix5, firstRead⟩ := MemoryCopyCorrespondence.readMemoryByte_evaluates (environment := E4) (store := store3)
    [] (Word.ofNatModulo 0) ((childCode.part (index := 1) rfl).evaluates store3) .word
  rw [CreationBytes.readByte_empty] at firstRead
  let store5 : Store := store3 ++ suffix5
  let E5 : Environment := .word Word.zero :: E4
  have childCode5 := childCode.prepend [.word Word.zero]
  have prefixTest : Evaluates E5 store5
      (choose (binary .wordGt (part 2 3 (fun here => .var (here - (depth + 3) - 1))) (number 0))
        (binary .wordEq (fun here => .var (here - (depth + 4) - 1)) (number 0xef)) (CodeBuilder.boolean false) (depth + 5))
      (.bool false) store5 :=
    .ifFalse (.binary ((childCode5.part (index := 2) rfl).evaluates store5) .word (by simp [BinaryOp.apply])) .bool
  have keep5 {location : Nat} {old : Value} (found : store3.read? location = some old) : store5.read? location = some old :=
    StorageCorrespondence.appended_read found _
  -- installation of the empty runtime image
  have identityEvaluated : Evaluates E5 store5
      (choose (binary .wordEq (part 2 3 (fun here => .var (here - (depth + 3) - 1))) (number 0))
        (success (number 0)) (identify (fun here => .var (here - (depth + 3) - 1))) (depth + 5))
      (.inRight .word (.word (Word.ofNatModulo 0))) store5 :=
    .ifTrue (.binary ((childCode5.part (index := 2) rfl).evaluates store5) .word (by simp [BinaryOp.apply])) (.inRight .word)
  let E6 : Environment := .word (Word.ofNatModulo 0) :: E5
  let extra6 : Environment := [.word (Word.ofNatModulo 0), .word Word.zero, childValue, .unit, .unit, insertedValue]
  have references6 := references.prepend extra6
  have worldRead5 : store5.read? locations.world = some insertedValue :=
    keep5 (keep3 (Ne.symm (Ne.symm worldBalances)) worldRead2)
  have completeRead5 : store5.read? locations.complete = some (.bool true) :=
    keep5 (keep3 (Ne.symm balancesComplete.1) (keep2 (Ne.symm worldComplete) completeRead))
  have found : StorageCorrespondence.get created1 targetWord true = .ok (created, 0) := by
    simp only [StorageCorrespondence.get, created1, CatalogWorldCorrespondence.lookup_put_same]
    rfl
  have recordEvaluated := StorageCorrespondence.get_evaluates (environment := E6) (initial := store5)
    (worldStore := store5) (addressStore := store5) (final := store5) created1 targetWord true
    (.loadCell (references6.world.evaluates store5) worldRead5) ((targetValue.prepend extra6).evaluates store5)
    (.loadCell (references6.complete.evaluates store5) completeRead5)
  rw [found] at recordEvaluated
  let store6 := StorageCorrespondence.getStore created1 targetWord true E6 store5
  obtain ⟨suffix6, _, same6⟩ := StorageCorrespondence.getStore_extension created1 targetWord true E6 store5
  have keep6 {location : Nat} {old : Value} (found : store5.read? location = some old) : store6.read? location = some old := by
    change (StorageCorrespondence.getStore created1 targetWord true E6 store5).read? location = _
    rw [same6]
    exact StorageCorrespondence.appended_read found _
  let recordValue := StorageCorrespondence.record created 0
  let E7 : Environment := recordValue :: E6
  have childCode7 := childCode.prepend [recordValue, .word (Word.ofNatModulo 0), .word Word.zero]
  have recordCode := CodeValue.bound (depth + 6) E6 recordValue
  have identityCode := (CodeValue.bound (depth + 5) E5 (.word (Word.ofNatModulo 0))).prepend [recordValue]
  have updatedEvaluated := replace_evaluates (fields := (((fields created 0).set 3 (.word (Word.ofNatModulo 0))).set 4
        (WordMapping.encode [])).set 5 (.word (Word.ofNatModulo 0))) 6 rfl
      (replace_evaluates (fields := ((fields created 0).set 3 (.word (Word.ofNatModulo 0))).set 4 (WordMapping.encode [])) 5 rfl
        (replace_evaluates (fields := (fields created 0).set 3 (.word (Word.ofNatModulo 0))) 4 rfl
          (replace_evaluates (fields := fields created 0) 3 rfl (recordCode.evaluates store6) (identityCode.evaluates store6))
          ((childCode7.part (index := 1) rfl).evaluates store6))
        ((childCode7.part (index := 2) rfl).evaluates store6)) (Evaluates.bool (value := true))
  have putEvaluated := StorageCorrespondence.put_evaluates (environment := E7) (initial := store6)
    (mappingStore := store6) (addressStore := store6) (final := store6) created1 targetWord created 0
    (.loadCell ((references6.world.prepend [recordValue]).evaluates store6) (keep6 worldRead5))
    ((targetValue.prepend (recordValue :: extra6)).evaluates store6) (by exact updatedEvaluated)
  rw [put_put] at putEvaluated
  let store7 := StorageCorrespondence.putStore created1 targetWord created 0 E7 store6
  obtain ⟨suffix7, same7⟩ := putStore_extension created1 targetWord created 0 E7 store6
  have keep7 {location : Nat} {old : Value} (found : store6.read? location = some old) : store7.read? location = some old := by
    change (StorageCorrespondence.putStore created1 targetWord created 0 E7 store6).read? location = _
    rw [same7]
    exact StorageCorrespondence.appended_read found _
  have worldRead7 := keep7 (keep6 worldRead5)
  have bound7 := (List.getElem?_eq_some_iff.mp worldRead7).1
  let store8 : Store := store7.set locations.world insertedValue
  have installEvaluated : Evaluates E5 store5
      (CreationImplementation.installWith identify shared target (fun here => .var (here - (depth + 3) - 1)) (depth + 5))
      (.inRight .word .unit) store8 := by
    unfold CreationImplementation.installWith
    apply LanguageResult.bind_success _ identityEvaluated
    apply LanguageResult.bind_success _ recordEvaluated
    dsimp only
    apply LanguageResult.bind_success _ putEvaluated
    exact .inRight (.storeCell ((references6.world.prepend [insertedValue, recordValue]).evaluates store7) worldRead7
      ((CodeValue.bound (depth + 7) E7 insertedValue).evaluates store7) (Store.write?_eq_some_iff.mpr ⟨bound7, rfl⟩))
  have responseEvaluated : Evaluates (.unit :: E5) store8
      (CreationImplementation.response target empty (number 0) (depth + 6))
      (.inRight .word (bundleValues [.word targetWord, WordMapping.encode [], .word (Word.ofNatModulo 0)])) store8 :=
    .inRight (.pair ((targetValue.prepend (.unit :: .word Word.zero :: childValue :: .unit :: .unit :: [insertedValue])).evaluates store8)
      (.pair (.construct .unit) .word))
  refine ⟨store8, ?_, ?_, ?_, ?_⟩
  · unfold CreationImplementation.deployment
    apply LanguageResult.bind_success _ inserted
    apply Evaluates.letE stored
    apply LanguageResult.bind_success _ transferEvaluated
    apply LanguageResult.bind_success _ childEvaluated
    apply Evaluates.ifTrue successTest
    apply Evaluates.ifFalse sizeTest
    apply LanguageResult.bind_success _ firstRead
    apply Evaluates.ifFalse prefixTest
    apply LanguageResult.bind_success _ installEvaluated
    exact responseEvaluated
  · change (store7.set locations.world insertedValue)[locations.world]? = _
    rw [List.getElem?_set_self bound7]
  · change (store7.set locations.world insertedValue)[locations.balances]? = _
    rw [List.getElem?_set_ne worldBalances]
    exact keep7 (keep6 (keep5 balancesRead3))
  · have appended : Rewrites [locations.world, locations.balances] store3 store7 := by
      refine ⟨?_, fun other old _ found => keep7 (keep6 (keep5 found))⟩
      change store3.length ≤ (StorageCorrespondence.putStore created1 targetWord created 0 E7 store6).length
      rw [same7]
      change store3.length ≤ ((StorageCorrespondence.getStore created1 targetWord true E6 store5) ++ suffix7).length
      rw [same6]
      simp [store5]
    have written : Rewrites [locations.world, locations.balances] store7 store8 := by
      refine ⟨by simp [store8], fun other old outside found => ?_⟩
      change (store7.set locations.world insertedValue)[other]? = _
      rw [List.getElem?_set_ne (fun same => outside (by simp [same]))]
      exact found
    exact ((frame2.trans (Rewrites.ofOverwrites transferFrame (by simp))).trans appended).trans written

/-- Rewriting an account with the identity it already has keeps every code
link when its code is unchanged. -/
theorem links_put_same {anchors : List CatalogWorldCorrespondence.Anchor} {accounts : StorageCorrespondence.Accounts}
    (linked : CatalogWorldCorrespondence.Links anchors accounts) {address : Word} {complete : Bool}
    {account updated : AccountState.Account} {identity : Nat}
    (obtained : StorageCorrespondence.get accounts address complete = .ok (account, identity))
    (code : updated.code = account.code) :
    CatalogWorldCorrespondence.Links anchors (StorageCorrespondence.put address updated identity accounts) := by
  intro anchor member
  obtain ⟨selected, selectedAt, selectedCode⟩ := linked anchor member
  by_cases same : address = anchor.address
  · subst address
    have original : StorageCorrespondence.get accounts anchor.address complete = .ok (selected, anchor.identity) := by
      simp only [StorageCorrespondence.get, selectedAt]
    have equal := Except.ok.inj (obtained.symm.trans original)
    cases equal
    exact ⟨_, CatalogWorldCorrespondence.lookup_put_same accounts anchor.address _ anchor.identity,
      by simpa [code] using selectedCode⟩
  · exact ⟨selected, (CatalogWorldCorrespondence.lookup_put_other same accounts _ identity).trans selectedAt, selectedCode⟩

/-- A new account at an address without a record breaks no code link. -/
theorem links_put_absent {anchors : List CatalogWorldCorrespondence.Anchor} {accounts : StorageCorrespondence.Accounts}
    (linked : CatalogWorldCorrespondence.Links anchors accounts) {address : Word}
    (absent : StorageCorrespondence.lookup address accounts = none) (account : AccountState.Account) (identity : Nat) :
    CatalogWorldCorrespondence.Links anchors (StorageCorrespondence.put address account identity accounts) := by
  intro anchor member
  obtain ⟨selected, selectedAt, selectedCode⟩ := linked anchor member
  have different : address ≠ anchor.address := by
    intro same
    rw [same, selectedAt] at absent
    cases absent
  exact ⟨selected, (CatalogWorldCorrespondence.lookup_put_other different accounts _ identity).trans selectedAt, selectedCode⟩

/-- A target with a nonzero nonce or code size is a collision. -/
theorem attempt_collision {depth : Nat} {environment : Environment} {store : Store}
    {runInit installRuntime : Code → Code → Code}
    {world balances complete creator value creatorBalance request target restore : Code}
    {location : Nat} {accounts : StorageCorrespondence.Accounts} {targetWord : Word} {completeFlag : Bool}
    {existing : AccountState.Account} {identity : Nat}
    (worldCode : CodeValue depth environment world (.cellRef AccountState.type location))
    (targetValue : CodeValue depth environment target (.word targetWord))
    (completeValue : CodeValue depth environment complete (.bool completeFlag))
    (worldRead : store.read? location = some (StorageCorrespondence.world accounts))
    (obtained : StorageCorrespondence.get accounts targetWord completeFlag = .ok (existing, identity))
    (used : existing.nonce ≠ Word.zero ∨
      AccountObservationSemantics.codeSize (existing.code.getD []) ≠ Word.zero) :
    ∃ final, Evaluates environment store
        (CreationImplementation.attempt runInit installRuntime world balances complete creator value creatorBalance
          request target restore depth) refusedValue final ∧ StoreRetains store final := by
  have fetched := StorageCorrespondence.get_evaluates (environment := environment) (initial := store)
    (worldStore := store) (addressStore := store) (final := store) accounts targetWord completeFlag
    (.loadCell (worldCode.evaluates store) worldRead) (targetValue.evaluates store) (completeValue.evaluates store)
  rw [obtained] at fetched
  let fetchedStore := StorageCorrespondence.getStore accounts targetWord completeFlag environment store
  let recordValue := StorageCorrespondence.record existing identity
  have recordCode := CodeValue.bound depth environment recordValue
  have nonceTest : Evaluates (recordValue :: environment) fetchedStore
      (binary .wordGt (part 2 9 (fun here => .var (here - depth - 1))) (number 0) (depth + 1))
      (.bool (decide (existing.nonce > Word.ofNatModulo 0))) fetchedStore :=
    .binary ((recordCode.part (index := 2) rfl).evaluates fetchedStore) .word rfl
  have sizeTest : Evaluates (recordValue :: environment) fetchedStore
      (binary .wordGt (part 5 9 (fun here => .var (here - depth - 1))) (number 0) (depth + 1))
      (.bool (decide (AccountObservationSemantics.codeSize (existing.code.getD []) > Word.ofNatModulo 0))) fetchedStore :=
    .binary ((recordCode.part (index := 5) rfl).evaluates fetchedStore) .word rfl
  refine ⟨fetchedStore, ?_, StoreRetains.append _ _⟩
  unfold CreationImplementation.attempt
  apply LanguageResult.bind_success _ fetched
  by_cases nonceUsed : existing.nonce ≠ Word.zero
  · have positive : existing.nonce > Word.ofNatModulo 0 := by
      rw [GT.gt, Fin.lt_def]
      exact Nat.pos_of_ne_zero (fun zero => nonceUsed (Fin.ext zero))
    exact .ifTrue (by simpa only [positive, decide_true] using nonceTest) (refused_evaluates _ _ _)
  · have sizeUsed := used.resolve_left nonceUsed
    have notPositive : ¬existing.nonce > Word.ofNatModulo 0 := by
      rw [GT.gt, Fin.lt_def]
      exact fun lt => nonceUsed (fun zero => by rw [zero] at lt; exact Nat.lt_irrefl _ lt)
    have positive : AccountObservationSemantics.codeSize (existing.code.getD []) > Word.ofNatModulo 0 := by
      rw [GT.gt, Fin.lt_def]
      exact Nat.pos_of_ne_zero (fun zero => sizeUsed (Fin.ext zero))
    exact .ifFalse (by simpa only [notPositive, decide_false] using nonceTest)
      (.ifTrue (by simpa only [positive, decide_true] using sizeTest) (refused_evaluates _ _ _))

theorem Rewrites.append (changed : List Nat) (store suffix : Store) : Rewrites changed store (store ++ suffix) :=
  ⟨by simp, fun _ _ _ found => StorageCorrespondence.appended_read found _⟩

/-- A target absent from a complete world reads as a fresh record and receives
the new account. -/
theorem attempt_deployed {depth : Nat} {environment : Environment} {store : Store}
    {runInit : Code → Code → Code} {identify : Code → Code} {shared : AccountRuntime.References}
    {locations : SharedLocations}
    {world balances complete creator value creatorBalance request target restore : Code}
    {accounts : StorageCorrespondence.Accounts} {before after : StorageSemantics.Words}
    {creatorWord valueWord targetWord : Word} {requested : Request}
    (references : SharedReferences depth environment shared locations)
    (worldCode : CodeValue depth environment world (.cellRef AccountState.type locations.world))
    (balancesCode : CodeValue depth environment balances (.cellRef WordMapping.type locations.balances))
    (completeValue : CodeValue depth environment complete (.bool true))
    (creatorValue : CodeValue depth environment creator (.word creatorWord))
    (valueValue : CodeValue depth environment value (.word valueWord))
    (creatorBalanceValue : CodeValue depth environment creatorBalance
      (.word (StorageSemantics.readWord creatorWord before)))
    (requestCode : CodeValue depth environment request (requestValue requested))
    (targetValue : CodeValue depth environment target (.word targetWord))
    (worldRead : store.read? locations.world = some (StorageCorrespondence.world accounts))
    (balancesRead : store.read? locations.balances = some (WordMapping.encode before))
    (completeRead : store.read? locations.complete = some (.bool true))
    (distinct : locations.all.Nodup)
    (absent : StorageCorrespondence.lookup targetWord accounts = none)
    (different : creatorWord ≠ targetWord)
    (emptyInit : requested.initLength = Word.zero)
    (transferred : AccountCallSemantics.transfer creatorWord targetWord valueWord before = .ok after) :
    ∃ final, Evaluates environment store
        (CreationImplementation.attempt runInit (CreationImplementation.installWith identify shared)
          world balances complete creator value creatorBalance request target restore depth)
        (.inRight .word (bundleValues [.word targetWord, WordMapping.encode [], .word (Word.ofNatModulo 0)])) final ∧
      final.read? locations.world = some (StorageCorrespondence.world
        (StorageCorrespondence.put targetWord (CreationSemantics.createdAccount targetWord) 0 accounts)) ∧
      final.read? locations.balances = some (WordMapping.encode after) ∧
      Rewrites [locations.world, locations.balances] store final := by
  have fetched := StorageCorrespondence.get_evaluates (environment := environment) (initial := store)
    (worldStore := store) (addressStore := store) (final := store) accounts targetWord true
    (.loadCell (worldCode.evaluates store) worldRead) (targetValue.evaluates store) (completeValue.evaluates store)
  have obtained : StorageCorrespondence.get accounts targetWord true = .ok ({address := targetWord}, 0) := by
    simp only [StorageCorrespondence.get, absent, ↓reduceIte]
  rw [obtained] at fetched
  let fetchedStore := StorageCorrespondence.getStore accounts targetWord true environment store
  obtain ⟨suffix, _, same⟩ := StorageCorrespondence.getStore_extension accounts targetWord true environment store
  have keep {location : Nat} {old : Value} (found : store.read? location = some old) :
      fetchedStore.read? location = some old := by
    change (StorageCorrespondence.getStore accounts targetWord true environment store).read? location = _
    rw [same]
    exact StorageCorrespondence.appended_read found _
  let recordValue := StorageCorrespondence.record {address := targetWord} 0
  have recordCode := CodeValue.bound depth environment recordValue
  obtain ⟨final, deployed, worldFinal, balancesFinal, frame⟩ := deployment_evaluates (runInit := runInit)
    (identify := identify) (restore := restore) (references.prepend [recordValue])
    (worldCode.prepend [recordValue]) (balancesCode.prepend [recordValue]) (creatorValue.prepend [recordValue])
    (valueValue.prepend [recordValue]) (creatorBalanceValue.prepend [recordValue]) (requestCode.prepend [recordValue])
    (targetValue.prepend [recordValue]) (keep worldRead) (keep balancesRead) (keep completeRead) distinct different
    emptyInit transferred
  refine ⟨final, ?_, worldFinal, balancesFinal, ?_⟩
  · unfold CreationImplementation.attempt
    apply LanguageResult.bind_success _ fetched
    apply Evaluates.ifFalse (.binary ((recordCode.part (index := 2) rfl).evaluates fetchedStore) .word
      (by simp [BinaryOp.apply]; decide))
    apply Evaluates.ifFalse (.binary ((recordCode.part (index := 5) rfl).evaluates fetchedStore) .word
      (by simp [BinaryOp.apply]))
    exact .ifTrue ((recordCode.part (index := 6) rfl).evaluates fetchedStore) deployed
  · have appended : Rewrites [locations.world, locations.balances] store fetchedStore := by
      change Rewrites _ store (StorageCorrespondence.getStore accounts targetWord true environment store)
      rw [same]
      exact Rewrites.append _ _ _
    exact appended.trans frame

/-- The shared world after the creator nonce advances. -/
def advancedWorld (state : AccountCallSemantics.Shared) (creator : Word) (account : AccountState.Account) :
    StorageSemantics.World :=
  StorageSemantics.put creator {account with nonce := account.nonce.add (Word.ofNatModulo 1)} state.world

/-- The response of a deployment: the new address and no revert bytes. -/
def deployedValue (target : Word) : Value :=
  .inRight .word (bundleValues [.word target, WordMapping.encode [], .word (Word.ofNatModulo 0)])

/-- Admitted attempts that the dispatcher completes without an init frame:
a collision, a deployment of empty init code at an address absent from a
complete world, and the two faults after the nonce advance, an unknown target
(failure 7) and an endowment overflow (failure 12). The faults restore the
checkpoint, so only the nonce advance remains. -/
inductive Admitting (state : AccountCallSemantics.Shared) (request : Request) :
    Value → AccountCallSemantics.Shared → Prop where
  | collision {account existing : AccountState.Account} {target : Word}
      (funded : ¬request.value > StorageSemantics.readWord (request.creator.bitAnd addressMask) state.balances)
      (found : StorageSemantics.get state.world (request.creator.bitAnd addressMask) state.complete = .ok account)
      (belowLimit : ¬account.nonce > Word.ofNatModulo (2 ^ 64 - 2))
      (bounded : request.initLength.val ≤ 49152)
      (derived : CreationAddressSemantics.Derived (request.creator.bitAnd addressMask) account.nonce
        request.initCode request.initLength request.scheme target)
      (occupied : StorageSemantics.lookup target (advancedWorld state (request.creator.bitAnd addressMask) account) =
        some existing)
      (used : existing.nonce ≠ Word.zero ∨
        AccountObservationSemantics.codeSize (existing.code.getD []) ≠ Word.zero) :
      Admitting state request refusedValue
        {state with world := advancedWorld state (request.creator.bitAnd addressMask) account}
  | deployed {account : AccountState.Account} {target : Word} {balances : StorageSemantics.Words}
      (funded : ¬request.value > StorageSemantics.readWord (request.creator.bitAnd addressMask) state.balances)
      (found : StorageSemantics.get state.world (request.creator.bitAnd addressMask) state.complete = .ok account)
      (belowLimit : ¬account.nonce > Word.ofNatModulo (2 ^ 64 - 2))
      (bounded : request.initLength.val ≤ 49152)
      (derived : CreationAddressSemantics.Derived (request.creator.bitAnd addressMask) account.nonce
        request.initCode request.initLength request.scheme target)
      (absent : StorageSemantics.lookup target (advancedWorld state (request.creator.bitAnd addressMask) account) = none)
      (complete : state.complete = true)
      (emptyInit : request.initLength = Word.zero)
      (transferred : AccountCallSemantics.transfer (request.creator.bitAnd addressMask) target request.value
        state.balances = .ok balances) :
      Admitting state request (deployedValue target)
        {state with
          world := (StorageSemantics.put target (CreationSemantics.createdAccount target)
            (advancedWorld state (request.creator.bitAnd addressMask) account))
          balances := balances}
  | unknown {account : AccountState.Account} {target : Word}
      (funded : ¬request.value > StorageSemantics.readWord (request.creator.bitAnd addressMask) state.balances)
      (found : StorageSemantics.get state.world (request.creator.bitAnd addressMask) state.complete = .ok account)
      (belowLimit : ¬account.nonce > Word.ofNatModulo (2 ^ 64 - 2))
      (bounded : request.initLength.val ≤ 49152)
      (derived : CreationAddressSemantics.Derived (request.creator.bitAnd addressMask) account.nonce
        request.initCode request.initLength request.scheme target)
      (unknown : CreationSemantics.Unknown (advancedWorld state (request.creator.bitAnd addressMask) account) target
        state.complete) :
      Admitting state request (.inLeft Creation.responseType (.word (Word.ofNatModulo 7)))
        {state with world := advancedWorld state (request.creator.bitAnd addressMask) account}
  | overflow {account : AccountState.Account} {target : Word}
      (funded : ¬request.value > StorageSemantics.readWord (request.creator.bitAnd addressMask) state.balances)
      (found : StorageSemantics.get state.world (request.creator.bitAnd addressMask) state.complete = .ok account)
      (belowLimit : ¬account.nonce > Word.ofNatModulo (2 ^ 64 - 2))
      (bounded : request.initLength.val ≤ 49152)
      (derived : CreationAddressSemantics.Derived (request.creator.bitAnd addressMask) account.nonce
        request.initCode request.initLength request.scheme target)
      (absent : StorageSemantics.lookup target (advancedWorld state (request.creator.bitAnd addressMask) account) = none)
      (complete : state.complete = true)
      (overflowed : AccountCallSemantics.transfer (request.creator.bitAnd addressMask) target request.value
        state.balances = .error (Word.ofNatModulo 12)) :
      Admitting state request (.inLeft Creation.responseType (.word (Word.ofNatModulo 12)))
        {state with world := advancedWorld state (request.creator.bitAnd addressMask) account}

theorem Rewrites.ofRetains {changed : List Nat} {initial final : Store} (retained : StoreRetains initial final) :
    Rewrites changed initial final :=
  ⟨retained.length_le, fun other _ _ found => (retained.read other (List.getElem?_eq_some_iff.mp found).1).trans found⟩

/-- An endowment overflow after the new record is inserted is failure 12; the
world keeps the inserted record until the checkpoint is restored. -/
theorem deployment_overflow {depth : Nat} {environment : Environment} {store : Store}
    {runInit installRuntime : Code → Code → Code}
    {locations : SharedLocations} {world balances creator value creatorBalance request target restore : Code}
    {accounts : StorageCorrespondence.Accounts} {before : StorageSemantics.Words}
    {creatorWord valueWord targetWord : Word}
    (worldCode : CodeValue depth environment world (.cellRef AccountState.type locations.world))
    (balancesCode : CodeValue depth environment balances (.cellRef WordMapping.type locations.balances))
    (valueValue : CodeValue depth environment value (.word valueWord))
    (targetValue : CodeValue depth environment target (.word targetWord))
    (worldRead : store.read? locations.world = some (StorageCorrespondence.world accounts))
    (balancesRead : store.read? locations.balances = some (WordMapping.encode before))
    (worldBalances : locations.world ≠ locations.balances)
    (overflowed : AccountCallSemantics.transfer creatorWord targetWord valueWord before = .error (Word.ofNatModulo 12)) :
    ∃ final, Evaluates environment store
        (CreationImplementation.deployment runInit installRuntime world balances creator value creatorBalance request
          target restore depth)
        (.inLeft Creation.responseType (.word (Word.ofNatModulo 12))) final ∧
      Rewrites [locations.world] store final := by
  let created := CreationSemantics.createdAccount targetWord
  have createdRecord (env : Environment) (current : Store) : Evaluates env current
      (AccountState.replace (AccountState.replace AccountState.defaultRecord 2 (.word (Word.ofNatModulo 1))) 7 (.bool true))
      (StorageCorrespondence.record created 0) current :=
    replace_evaluates (fields := (fields {address := targetWord} 0).set 2 (.word (Word.ofNatModulo 1))) 7 rfl
      (replace_evaluates (fields := fields {address := targetWord} 0) 2 rfl
        (StorageCorrespondence.default_evaluates targetWord env current) .word) .bool
  have inserted := StorageCorrespondence.put_evaluates (environment := environment)
    (initial := store) (mappingStore := store) (addressStore := store) (final := store)
    accounts targetWord created 0 (.loadCell (worldCode.evaluates store) worldRead) (targetValue.evaluates store)
    (createdRecord _ _)
  let insertedValue := StorageCorrespondence.world (StorageCorrespondence.put targetWord created 0 accounts)
  let store1 := StorageCorrespondence.putStore accounts targetWord created 0 environment store
  obtain ⟨suffix1, same1⟩ := putStore_extension accounts targetWord created 0 environment store
  have keep1 {location : Nat} {old : Value} (found : store.read? location = some old) : store1.read? location = some old := by
    change (StorageCorrespondence.putStore accounts targetWord created 0 environment store).read? location = _
    rw [same1]
    exact StorageCorrespondence.appended_read found _
  have bound1 := (List.getElem?_eq_some_iff.mp (keep1 worldRead)).1
  let store2 : Store := store1.set locations.world insertedValue
  have stored : Evaluates (insertedValue :: environment) store1
      (CodeBuilder.store world (fun here => .var (here - depth - 1)) (depth + 1)) .unit store2 :=
    .storeCell ((worldCode.prepend [insertedValue]).evaluates store1) (keep1 worldRead)
      ((CodeValue.bound depth environment insertedValue).evaluates store1) (Store.write?_eq_some_iff.mpr ⟨bound1, rfl⟩)
  have balancesRead2 : store2.read? locations.balances = some (WordMapping.encode before) := by
    change (store1.set locations.world insertedValue)[locations.balances]? = _
    rw [List.getElem?_set_ne worldBalances]
    exact keep1 balancesRead
  have frame2 : Rewrites [locations.world] store store2 := by
    refine ⟨?_, fun other old outside found => ?_⟩
    · change store.length ≤ (store1.set _ _).length
      rw [List.length_set]
      change store.length ≤ (StorageCorrespondence.putStore accounts targetWord created 0 environment store).length
      rw [same1]; simp
    · change (store1.set locations.world insertedValue)[other]? = _
      rw [List.getElem?_set_ne (fun same => outside (by simp [same]))]
      exact keep1 found
  obtain ⟨store3, failed, retained⟩ := transfer_overflow (creatorCode := creator) (creatorBalanceCode := creatorBalance)
    (balancesCode.prepend [.unit, insertedValue]) (targetValue.prepend [.unit, insertedValue])
    (valueValue.prepend [.unit, insertedValue]) balancesRead2 overflowed
  refine ⟨store3, ?_, frame2.trans (Rewrites.ofRetains retained)⟩
  unfold CreationImplementation.deployment
  apply LanguageResult.bind_success _ inserted
  apply Evaluates.letE stored
  exact LanguageResult.bind_failure _ failed

/-- A target absent from an incomplete world is failure 7. -/
theorem attempt_absent {depth : Nat} {environment : Environment} {store : Store}
    {runInit installRuntime : Code → Code → Code}
    {world balances complete creator value creatorBalance request target restore : Code}
    {location : Nat} {accounts : StorageCorrespondence.Accounts} {targetWord : Word}
    (worldCode : CodeValue depth environment world (.cellRef AccountState.type location))
    (targetValue : CodeValue depth environment target (.word targetWord))
    (completeValue : CodeValue depth environment complete (.bool false))
    (worldRead : store.read? location = some (StorageCorrespondence.world accounts))
    (absent : StorageCorrespondence.lookup targetWord accounts = none) :
    ∃ final, Evaluates environment store
        (CreationImplementation.attempt runInit installRuntime world balances complete creator value creatorBalance
          request target restore depth) (.inLeft Creation.responseType (.word (Word.ofNatModulo 7))) final ∧
      StoreRetains store final := by
  have fetched := StorageCorrespondence.get_evaluates (environment := environment) (initial := store)
    (worldStore := store) (addressStore := store) (final := store) accounts targetWord false
    (.loadCell (worldCode.evaluates store) worldRead) (targetValue.evaluates store) (completeValue.evaluates store)
  have obtained : StorageCorrespondence.get accounts targetWord false = .error (Word.ofNatModulo 7) := by
    simp only [StorageCorrespondence.get, absent, Bool.false_eq_true, ↓reduceIte]
  rw [obtained] at fetched
  refine ⟨StorageCorrespondence.getStore accounts targetWord false environment store, ?_, StoreRetains.append _ _⟩
  unfold CreationImplementation.attempt
  exact LanguageResult.bind_failure _ fetched

/-- A record with a zero nonce and unknown code is failure 7. -/
theorem attempt_unknownCode {depth : Nat} {environment : Environment} {store : Store}
    {runInit installRuntime : Code → Code → Code}
    {world balances complete creator value creatorBalance request target restore : Code}
    {location : Nat} {accounts : StorageCorrespondence.Accounts} {targetWord : Word} {completeFlag : Bool}
    {existing : AccountState.Account} {identity : Nat}
    (worldCode : CodeValue depth environment world (.cellRef AccountState.type location))
    (targetValue : CodeValue depth environment target (.word targetWord))
    (completeValue : CodeValue depth environment complete (.bool completeFlag))
    (worldRead : store.read? location = some (StorageCorrespondence.world accounts))
    (obtained : StorageCorrespondence.get accounts targetWord completeFlag = .ok (existing, identity))
    (zero : existing.nonce = Word.zero) (unknown : existing.code = none) :
    ∃ final, Evaluates environment store
        (CreationImplementation.attempt runInit installRuntime world balances complete creator value creatorBalance
          request target restore depth) (.inLeft Creation.responseType (.word (Word.ofNatModulo 7))) final ∧
      StoreRetains store final := by
  have fetched := StorageCorrespondence.get_evaluates (environment := environment) (initial := store)
    (worldStore := store) (addressStore := store) (final := store) accounts targetWord completeFlag
    (.loadCell (worldCode.evaluates store) worldRead) (targetValue.evaluates store) (completeValue.evaluates store)
  rw [obtained] at fetched
  let fetchedStore := StorageCorrespondence.getStore accounts targetWord completeFlag environment store
  let recordValue := StorageCorrespondence.record existing identity
  have recordCode := CodeValue.bound depth environment recordValue
  have nonceZero : ¬existing.nonce > Word.ofNatModulo 0 := by rw [zero]; decide
  have sizeZero : ¬Word.ofNatModulo (existing.code.getD []).length > Word.ofNatModulo 0 := by rw [unknown]; decide
  refine ⟨fetchedStore, ?_, StoreRetains.append _ _⟩
  unfold CreationImplementation.attempt
  apply LanguageResult.bind_success _ fetched
  apply Evaluates.ifFalse (.binary ((recordCode.part (index := 2) rfl).evaluates fetchedStore) .word
    (by simp only [BinaryOp.apply, nonceZero, decide_false]))
  apply Evaluates.ifFalse (.binary ((recordCode.part (index := 5) rfl).evaluates fetchedStore) .word
    (by simp only [BinaryOp.apply, sizeZero, decide_false]))
  exact .ifFalse ((recordCode.part (index := 6) (value := .bool false) (by simp [unknown])).evaluates
    fetchedStore) (.inLeft .word)

/-- A target absent from a complete world whose endowment would overflow is
failure 12 after the new record is inserted. -/
theorem attempt_overflow {depth : Nat} {environment : Environment} {store : Store}
    {runInit installRuntime : Code → Code → Code} {locations : SharedLocations}
    {world balances complete creator value creatorBalance request target restore : Code}
    {accounts : StorageCorrespondence.Accounts} {before : StorageSemantics.Words}
    {creatorWord valueWord targetWord : Word}
    (worldCode : CodeValue depth environment world (.cellRef AccountState.type locations.world))
    (balancesCode : CodeValue depth environment balances (.cellRef WordMapping.type locations.balances))
    (completeValue : CodeValue depth environment complete (.bool true))
    (valueValue : CodeValue depth environment value (.word valueWord))
    (targetValue : CodeValue depth environment target (.word targetWord))
    (worldRead : store.read? locations.world = some (StorageCorrespondence.world accounts))
    (balancesRead : store.read? locations.balances = some (WordMapping.encode before))
    (worldBalances : locations.world ≠ locations.balances)
    (absent : StorageCorrespondence.lookup targetWord accounts = none)
    (overflowed : AccountCallSemantics.transfer creatorWord targetWord valueWord before = .error (Word.ofNatModulo 12)) :
    ∃ final, Evaluates environment store
        (CreationImplementation.attempt runInit installRuntime world balances complete creator value creatorBalance
          request target restore depth) (.inLeft Creation.responseType (.word (Word.ofNatModulo 12))) final ∧
      Rewrites [locations.world] store final := by
  have fetched := StorageCorrespondence.get_evaluates (environment := environment) (initial := store)
    (worldStore := store) (addressStore := store) (final := store) accounts targetWord true
    (.loadCell (worldCode.evaluates store) worldRead) (targetValue.evaluates store) (completeValue.evaluates store)
  have obtained : StorageCorrespondence.get accounts targetWord true = .ok ({address := targetWord}, 0) := by
    simp only [StorageCorrespondence.get, absent, ↓reduceIte]
  rw [obtained] at fetched
  let fetchedStore := StorageCorrespondence.getStore accounts targetWord true environment store
  obtain ⟨suffix, _, same⟩ := StorageCorrespondence.getStore_extension accounts targetWord true environment store
  have keep {location : Nat} {old : Value} (found : store.read? location = some old) :
      fetchedStore.read? location = some old := by
    change (StorageCorrespondence.getStore accounts targetWord true environment store).read? location = _
    rw [same]
    exact StorageCorrespondence.appended_read found _
  let recordValue := StorageCorrespondence.record {address := targetWord} 0
  have recordCode := CodeValue.bound depth environment recordValue
  obtain ⟨final, failed, frame⟩ := deployment_overflow (runInit := runInit) (installRuntime := installRuntime)
    (creator := creator) (creatorBalance := creatorBalance) (request := request) (restore := restore)
    (worldCode.prepend [recordValue]) (balancesCode.prepend [recordValue]) (valueValue.prepend [recordValue])
    (targetValue.prepend [recordValue]) (keep worldRead) (keep balancesRead) worldBalances overflowed
  refine ⟨final, ?_, ?_⟩
  · unfold CreationImplementation.attempt
    apply LanguageResult.bind_success _ fetched
    apply Evaluates.ifFalse (.binary ((recordCode.part (index := 2) rfl).evaluates fetchedStore) .word
      (by simp [BinaryOp.apply]; decide))
    apply Evaluates.ifFalse (.binary ((recordCode.part (index := 5) rfl).evaluates fetchedStore) .word
      (by simp [BinaryOp.apply]))
    exact .ifTrue ((recordCode.part (index := 6) rfl).evaluates fetchedStore) failed
  · have appended : Rewrites [locations.world] store fetchedStore := by
      change Rewrites _ store (StorageCorrespondence.getStore accounts targetWord true environment store)
      rw [same]
      exact Rewrites.append _ _ _
    exact appended.trans frame

theorem Rewrites.set_member {changed : List Nat} {initial current : Store} {location : Nat} {value : Value}
    (rewrites : Rewrites changed initial current) (member : location ∈ changed) :
    Rewrites changed initial (current.set location value) :=
  ⟨by simpa only [List.length_set] using rewrites.length_le, fun other old outside found => by
    change (current.set location value)[other]? = _
    rw [List.getElem?_set_ne (fun same : location = other => outside (same ▸ member))]
    exact rewrites.read other old outside found⟩

/-- Restoring a cell to its initial value keeps the frame. -/
theorem Rewrites.set_same {changed : List Nat} {initial current : Store} {location : Nat} {value : Value}
    (rewrites : Rewrites changed initial current) (found : initial.read? location = some value) :
    Rewrites changed initial (current.set location value) := by
  refine ⟨by simpa only [List.length_set] using rewrites.length_le, fun other old outside foundOther => ?_⟩
  change (current.set location value)[other]? = _
  by_cases same : location = other
  · subst same
    have bound : location < current.length :=
      Nat.lt_of_lt_of_le (List.getElem?_eq_some_iff.mp found).1 rewrites.length_le
    rw [List.getElem?_set_self bound]
    exact found.symm.trans foundOther
  · rw [List.getElem?_set_ne same]
    exact rewrites.read other old outside foundOther

theorem source_get {accounts : StorageCorrespondence.Accounts} {world : StorageSemantics.World}
    (same : accounts.map Prod.fst = world) {address : Word} {complete : Bool} {account : AccountState.Account}
    (found : StorageSemantics.get world address complete = .ok account) :
    ∃ identity, StorageCorrespondence.get accounts address complete = .ok (account, identity) := by
  have sourced := StorageCorrespondence.get_source accounts address complete
  rw [same, found] at sourced
  cases obtained : StorageCorrespondence.get accounts address complete with
  | error reason => simp [obtained, Except.map] at sourced
  | ok entry =>
      simp only [obtained, Except.map, Except.ok.injEq] at sourced
      exact ⟨entry.2, by rw [← sourced]⟩

/-- The admitted remainder up to the protected attempt on the target: the
address, the nonce advance and the checkpoint. The protected attempt is
evaluated after the nonce write. -/
theorem admitted_prefix {depth : Nat} {environment : Environment} {store : Store}
    {runInit installRuntime : Code → Code → Code} {args creatorBalance creatorRecord : Code}
    {locations : SharedLocations} {accounts : StorageCorrespondence.Accounts} {account : AccountState.Account}
    {identity : Nat} {target : Word} {complete : Bool} {balances : StorageSemantics.Words}
    {logs : MemorySemantics.Entries} {logSize : Word} {request : Request} {result : Value}
    {property : Store → Prop}
    (argsCode : CodeValue depth environment args (bundleValues [.cellRef AccountState.type locations.world,
      .cellRef WordMapping.type locations.balances, .cellRef WordMapping.type locations.logs,
      .cellRef .word locations.logSize, .bool complete, requestValue request]))
    (recordCode : CodeValue depth environment creatorRecord (StorageCorrespondence.record account identity))
    (distinct : locations.all.Nodup)
    (worldRead : store.read? locations.world = some (StorageCorrespondence.world accounts))
    (balancesRead : store.read? locations.balances = some (WordMapping.encode balances))
    (logsRead : store.read? locations.logs = some (WordMapping.encode logs))
    (logSizeRead : store.read? locations.logSize = some (.word logSize))
    (obtained : StorageCorrespondence.get accounts (request.creator.bitAnd addressMask) complete = .ok (account, identity))
    (bounded : request.initLength.val ≤ 49152)
    (derived : CreationAddressSemantics.Derived (request.creator.bitAnd addressMask) account.nonce
      request.initCode request.initLength request.scheme target)
    (attempted : ∀ current, Overwrites locations.world store current →
      current.read? locations.world = some (StorageCorrespondence.world (StorageCorrespondence.put
        (request.creator.bitAnd addressMask) {account with nonce := account.nonce.add (Word.ofNatModulo 1)} identity accounts)) →
      ∃ final, Evaluates ([.word logSize, WordMapping.encode logs, WordMapping.encode balances,
          StorageCorrespondence.world (StorageCorrespondence.put (request.creator.bitAnd addressMask)
            {account with nonce := account.nonce.add (Word.ofNatModulo 1)} identity accounts),
          .unit, .word target] ++ environment) current
        (CreationImplementation.protect
          (restoreCode (part 0 6 args) (part 1 6 args) (part 2 6 args) (part 3 6 args) (depth + 2))
          (CreationImplementation.attempt runInit installRuntime (part 0 6 args) (part 1 6 args) (part 4 6 args)
            (address (part 0 8 (part 5 6 args))) (part 1 8 (part 5 6 args)) creatorBalance (part 5 6 args)
            (fun here => .var (here - depth - 1))
            (restoreCode (part 0 6 args) (part 1 6 args) (part 2 6 args) (part 3 6 args) (depth + 2))) (depth + 6))
        result final ∧ property final) :
    ∃ final, Evaluates environment store
      (CreationImplementation.admitted runInit installRuntime args creatorBalance creatorRecord depth)
      result final ∧ property final := by
  simp only [SharedLocations.all, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at distinct
  obtain ⟨⟨worldLogs, worldSize, worldBalances, _⟩, _, _, _⟩ := distinct
  have requestCode := argsCode.part (index := 5) rfl
  have creatorCode : CodeValue depth environment (address (part 0 8 (part 5 6 args)))
      (.word (request.creator.bitAnd addressMask)) :=
    CreationAddressCorrespondence.binary_code (op := .wordAnd) (requestCode.part (index := 0) rfl)
      (CodeValue.number (2 ^ 160 - 1) depth environment) rfl
  have nonceCode := recordCode.part (index := 2) rfl
  obtain ⟨store4, derivedEvaluated, derivedRetained⟩ := deriveAddress_evaluates creatorCode nonceCode requestCode
    bounded derived
  have keep4 {location : Nat} {old : Value} (found : store.read? location = some old) :
      store4.read? location = some old :=
    (derivedRetained.read location (List.getElem?_eq_some_iff.mp found).1).trans found
  have argumentsEvaluated : Evaluates (.word target :: environment) store4
      (bundle [part 0 6 args (depth + 1), address (part 0 8 (part 5 6 args)) (depth + 1), part 4 6 args (depth + 1),
        binary .wordAdd (part 2 9 creatorRecord) (number 1) (depth + 1)])
      (bundleValues [.cellRef AccountState.type locations.world, .word (request.creator.bitAnd addressMask),
        .bool complete, .word (account.nonce.add (Word.ofNatModulo 1))]) store4 :=
    .pair (((argsCode.part (index := 0) rfl).prepend [.word target]).evaluates store4)
      (.pair ((creatorCode.prepend [.word target]).evaluates store4)
        (.pair (((argsCode.part (index := 4) rfl).prepend [.word target]).evaluates store4)
          (.binary ((nonceCode.prepend [.word target]).evaluates store4) .word rfl)))
  obtain ⟨store5, nonceEvaluated, worldRead5, overwrites5⟩ := writeNonce_evaluates accounts locations.world _ complete _
    argumentsEvaluated (keep4 worldRead) obtained
  have keep5 {location : Nat} {old : Value} (different : location ≠ locations.world)
      (found : store.read? location = some old) : store5.read? location = some old :=
    overwrites5.read location old different (keep4 found)
  obtain ⟨final, attemptEvaluated, property⟩ := attempted store5
    ((Overwrites.ofRetains derivedRetained).trans overwrites5) worldRead5
  refine ⟨final, ?_, property⟩
  unfold CreationImplementation.admitted
  apply LanguageResult.bind_success _ derivedEvaluated
  apply LanguageResult.bind_success _ nonceEvaluated
  apply checkpoint_evaluates (((argsCode.part (index := 0) rfl).prepend [.unit, .word target]))
    (((argsCode.part (index := 1) rfl).prepend [.unit, .word target]))
    (((argsCode.part (index := 2) rfl).prepend [.unit, .word target]))
    (((argsCode.part (index := 3) rfl).prepend [.unit, .word target])) worldRead5
    (keep5 (Ne.symm worldBalances) balancesRead) (keep5 (Ne.symm worldLogs) logsRead) (keep5 (Ne.symm worldSize) logSizeRead)
  exact attemptEvaluated

/-- The six dispatcher arguments as the handler packs them. -/
def argumentsValue (locations : SharedLocations) (complete : Bool) (request : Request) : Value :=
  bundleValues [.cellRef AccountState.type locations.world,
    .cellRef WordMapping.type locations.balances, .cellRef WordMapping.type locations.logs,
    .cellRef .word locations.logSize, .bool complete, requestValue request]

/-- The environment of the attempt on the target, after the checkpoint loads. -/
def attemptEnvironment (environment : Environment) (locations : SharedLocations) (state : AccountCallSemantics.Shared)
    (request : Request) (account : AccountState.Account) (identity : Nat) (target : Word)
    (advanced : StorageCorrespondence.Accounts) : Environment :=
  [.word state.logSize, WordMapping.encode state.logs, WordMapping.encode state.balances,
    StorageCorrespondence.world advanced, .unit, .word target,
    StorageCorrespondence.record account identity,
    .word (StorageSemantics.readWord (request.creator.bitAnd addressMask) state.balances),
    argumentsValue locations state.complete request] ++ environment

/-- The accounts after the creator nonce advances. -/
def advancedAccounts (accounts : StorageCorrespondence.Accounts) (creator : Word) (account : AccountState.Account)
    (identity : Nat) : StorageCorrespondence.Accounts :=
  StorageCorrespondence.put creator {account with nonce := account.nonce.add (Word.ofNatModulo 1)} identity accounts

/-- The checkpoint restoration seen by the attempt of a dispatcher whose
arguments are bound at `depth`. -/
def attemptRestore (depth : Nat) : Code :=
  restoreCode (part 0 6 (fun here => .var (here - depth - 1))) (part 1 6 (fun here => .var (here - depth - 1)))
    (part 2 6 (fun here => .var (here - depth - 1))) (part 3 6 (fun here => .var (here - depth - 1))) (depth + 5)

/-- A failed attempt inside the dispatcher restores the four checkpointed
cells: the world keeps the nonce advance, and balances and logs return to their
values before the attempt. -/
theorem attempt_restored {depth : Nat} {environment : Environment} {store current failed : Store}
    {locations : SharedLocations} {state : AccountCallSemantics.Shared} {request : Request}
    {account : AccountState.Account} {identity : Nat} {target : Word} {advanced : StorageCorrespondence.Accounts}
    {attempt : Code} {reason : Word} {failedType : Core.Ty}
    (related : SharedStateRel locations state store)
    (attempted : Evaluates (attemptEnvironment environment locations state request account identity target advanced)
      current (attempt (depth + 9)) (.inLeft failedType (.word reason)) failed)
    (rewrites : Rewrites [locations.world, locations.balances] store failed) :
    ∃ final, Evaluates (attemptEnvironment environment locations state request account identity target advanced)
        current (CreationImplementation.protect (attemptRestore depth) attempt (depth + 9))
        (.inLeft Creation.responseType (.word reason)) final ∧
      final.read? locations.world = some (StorageCorrespondence.world advanced) ∧
      final.read? locations.balances = some (WordMapping.encode state.balances) ∧
      final.read? locations.logs = some (WordMapping.encode state.logs) ∧
      final.read? locations.logSize = some (.word state.logSize) ∧
      Rewrites [locations.world, locations.balances] store final := by
  have distinct := related.distinct
  simp only [SharedLocations.all, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at distinct
  obtain ⟨⟨worldLogs, worldSize, worldBalances, _⟩, ⟨logsSize, logsBalances, _⟩, ⟨sizeBalances, _⟩, _⟩ := distinct
  obtain ⟨_, _, worldRead⟩ := related.world
  have bound {location : Nat} {value : Value} (found : store.read? location = some value) :
      location < failed.length :=
    Nat.lt_of_lt_of_le (List.getElem?_eq_some_iff.mp found).1 rewrites.length_le
  let argsValue := argumentsValue locations state.complete request
  let creatorBalance : Value := .word (StorageSemantics.readWord (request.creator.bitAnd addressMask) state.balances)
  let below : Environment := [.unit, .word target, StorageCorrespondence.record account identity, creatorBalance,
    argsValue] ++ environment
  have args := (CodeValue.bound depth environment argsValue).prepend [.word reason, .word state.logSize,
    WordMapping.encode state.logs, WordMapping.encode state.balances, StorageCorrespondence.world advanced, .unit,
    .word target, StorageCorrespondence.record account identity, creatorBalance]
  have savedWorld := (CodeValue.bound (depth + 5) below (StorageCorrespondence.world advanced)).prepend
    [.word reason, .word state.logSize, WordMapping.encode state.logs, WordMapping.encode state.balances]
  have savedBalances := (CodeValue.bound (depth + 6) (StorageCorrespondence.world advanced :: below)
    (WordMapping.encode state.balances)).prepend [.word reason, .word state.logSize, WordMapping.encode state.logs]
  have savedLogs := (CodeValue.bound (depth + 7)
    (WordMapping.encode state.balances :: StorageCorrespondence.world advanced :: below)
    (WordMapping.encode state.logs)).prepend [.word reason, .word state.logSize]
  have savedLogSize := (CodeValue.bound (depth + 8)
    (WordMapping.encode state.logs :: WordMapping.encode state.balances :: StorageCorrespondence.world advanced :: below)
    (.word state.logSize)).prepend [.word reason]
  have restored := restoreCode_evaluates (checkpoint := depth + 5) (args.part (index := 0) rfl)
    (args.part (index := 1) rfl) (args.part (index := 2) rfl) (args.part (index := 3) rfl)
    savedWorld savedBalances savedLogs savedLogSize (bound worldRead) (bound related.balances) (bound related.logs)
    (bound related.logSize)
  refine ⟨_, protect_failed attempted restored, ?_, ?_, ?_, ?_,
    (((rewrites.set_same related.logSize).set_same related.logs).set_member (by simp)).set_member (by simp)⟩
  · change (List.set _ locations.world _)[locations.world]? = _
    rw [List.getElem?_set_self (by simp only [List.length_set]; exact bound worldRead)]
  · change (List.set _ locations.world _)[locations.balances]? = _
    rw [List.getElem?_set_ne worldBalances, List.getElem?_set_self (by simp only [List.length_set]; exact bound related.balances)]
  · change (List.set _ locations.world _)[locations.logs]? = _
    rw [List.getElem?_set_ne worldLogs, List.getElem?_set_ne (Ne.symm logsBalances),
      List.getElem?_set_self (by simp only [List.length_set]; exact bound related.logs)]
  · change (List.set _ locations.world _)[locations.logSize]? = _
    rw [List.getElem?_set_ne worldSize, List.getElem?_set_ne (Ne.symm sizeBalances), List.getElem?_set_ne logsSize,
      List.getElem?_set_self (bound related.logSize)]

/-- The funds and nonce checks pass, the creator record is read and the
admitted remainder runs; the protected attempt on the target is supplied. -/
theorem dispatchWith_admit {depth : Nat} {environment : Environment} {store : Store}
    {shared : AccountRuntime.References} {locations : SharedLocations}
    {requestCode : Code} {request : Request} {state : AccountCallSemantics.Shared}
    {runInit : Code → Code → Code} {identify : Code → Code}
    {accounts : StorageCorrespondence.Accounts} {account : AccountState.Account} {target : Word}
    {result : Value} {property : Store → Prop}
    (references : SharedReferences depth environment shared locations)
    (requestRelated : CodeValue depth environment requestCode (requestValue request))
    (related : SharedStateRel locations state store)
    (worldSame : accounts.map Prod.fst = state.world)
    (worldRead : store.read? locations.world = some (StorageCorrespondence.world accounts))
    (funded : ¬request.value > StorageSemantics.readWord (request.creator.bitAnd addressMask) state.balances)
    (found : StorageSemantics.get state.world (request.creator.bitAnd addressMask) state.complete = .ok account)
    (belowLimit : ¬account.nonce > Word.ofNatModulo (2 ^ 64 - 2))
    (bounded : request.initLength.val ≤ 49152)
    (derived : CreationAddressSemantics.Derived (request.creator.bitAnd addressMask) account.nonce
      request.initCode request.initLength request.scheme target)
    (attempted : ∀ identity,
      StorageCorrespondence.get accounts (request.creator.bitAnd addressMask) state.complete = .ok (account, identity) →
      ∀ current, Overwrites locations.world store current →
      current.read? locations.world = some (StorageCorrespondence.world
        (advancedAccounts accounts (request.creator.bitAnd addressMask) account identity)) →
      ∃ final, Evaluates (attemptEnvironment environment locations state request account identity target
          (advancedAccounts accounts (request.creator.bitAnd addressMask) account identity)) current
        (CreationImplementation.protect (attemptRestore depth)
          (CreationImplementation.attempt runInit (CreationImplementation.installWith identify shared)
            (part 0 6 (fun here => .var (here - depth - 1))) (part 1 6 (fun here => .var (here - depth - 1)))
            (part 4 6 (fun here => .var (here - depth - 1)))
            (address (part 0 8 (part 5 6 (fun here => .var (here - depth - 1)))))
            (part 1 8 (part 5 6 (fun here => .var (here - depth - 1)))) (fun here => .var (here - (depth + 1) - 1))
            (part 5 6 (fun here => .var (here - depth - 1))) (fun here => .var (here - (depth + 3) - 1))
            (attemptRestore depth))
          (depth + 9))
        result final ∧ property final) :
    ∃ final, Evaluates environment store
      (CreationImplementation.dispatchWith (AccountRuntime.reference shared "world")
        (AccountRuntime.reference shared "balances") (AccountRuntime.reference shared "logs")
        (AccountRuntime.reference shared "logSize") (load (AccountRuntime.reference shared "worldComplete"))
        requestCode (CreationImplementation.admitted runInit (CreationImplementation.installWith identify shared)) depth)
        result final ∧ property final := by
  let argsValue := argumentsValue locations state.complete request
  have packed : Evaluates environment store
      (packet [AccountRuntime.reference shared "world", AccountRuntime.reference shared "balances",
        AccountRuntime.reference shared "logs", AccountRuntime.reference shared "logSize",
        load (AccountRuntime.reference shared "worldComplete"), requestCode] depth) argsValue store :=
    .pair (references.world.evaluates store) (.pair (references.balances.evaluates store)
      (.pair (references.logs.evaluates store) (.pair (references.logSize.evaluates store)
        (.pair (.loadCell (references.complete.evaluates store) related.complete) (requestRelated.evaluates store)))))
  have argsCode := CodeValue.bound depth environment argsValue
  have requestCode' : CodeValue (depth + 1) (argsValue :: environment)
      (part 5 6 (fun here => .var (here - depth - 1))) (requestValue request) :=
    argsCode.part (index := 5) rfl
  let key := request.creator.bitAnd addressMask
  have keyEvaluated : Evaluates (argsValue :: environment) store
      (address (part 0 8 (part 5 6 (fun here => .var (here - depth - 1)))) (depth + 1)) (.word key) store :=
    .binary ((requestCode'.part (index := 0) rfl).evaluates store) .word rfl
  obtain ⟨looked, lookedEvaluated, lookedRetained⟩ := lookup_preserves
    (.loadCell ((argsCode.part (index := 1) rfl).evaluates store) related.balances) keyEvaluated
  let balance := StorageSemantics.readWord key state.balances
  have valueEvaluated : Evaluates (.word balance :: argsValue :: environment) looked
      (part 1 8 (part 5 6 (fun here => .var (here - depth - 1))) (depth + 1 + 1)) (.word request.value) looked :=
    ((requestCode'.part (index := 1) rfl).prepend [.word balance]).evaluates looked
  have balanceCode := CodeValue.bound (depth + 1) (argsValue :: environment) (.word balance)
  have keepLooked {location : Nat} {old : Value} (found : store.read? location = some old) :
      looked.read? location = some old :=
    (lookedRetained.read location (List.getElem?_eq_some_iff.mp found).1).trans found
  obtain ⟨identity, got⟩ := source_get worldSame found
  let recordValue := StorageCorrespondence.record account identity
  have worldLoaded : Evaluates (.word balance :: argsValue :: environment) looked
      (load (part 0 6 (fun here => .var (here - depth - 1))) (depth + 1 + 1))
      (StorageCorrespondence.world accounts) looked :=
    .loadCell (((argsCode.part (index := 0) rfl).prepend [.word balance]).evaluates looked) (keepLooked worldRead)
  have creatorEvaluated : Evaluates (.word balance :: argsValue :: environment) looked
      (address (part 0 8 (part 5 6 (fun here => .var (here - depth - 1)))) (depth + 1 + 1)) (.word key) looked :=
    .binary (((requestCode'.part (index := 0) rfl).prepend [.word balance]).evaluates looked) .word rfl
  have completeEvaluated : Evaluates (.word balance :: argsValue :: environment) looked
      (part 4 6 (fun here => .var (here - depth - 1)) (depth + 1 + 1)) (.bool state.complete) looked :=
    ((argsCode.part (index := 4) rfl).prepend [.word balance]).evaluates looked
  have recordRead := StorageCorrespondence.get_evaluates accounts key state.complete
    worldLoaded creatorEvaluated completeEvaluated
  rw [got] at recordRead
  let recordStore := StorageCorrespondence.getStore accounts key state.complete
    (.word balance :: argsValue :: environment) looked
  have recordRetained : StoreRetains looked recordStore := StoreRetains.append _ _
  have retained := lookedRetained.trans recordRetained
  have keepRecord {location : Nat} {old : Value} (found : store.read? location = some old) :
      recordStore.read? location = some old :=
    (retained.read location (List.getElem?_eq_some_iff.mp found).1).trans found
  have recordCode := CodeValue.bound (depth + 2) (.word balance :: argsValue :: environment) recordValue
  obtain ⟨final, admittedEvaluated, holds⟩ := admitted_prefix (property := property)
    (argsCode.prepend [recordValue, .word balance]) recordCode related.distinct (keepRecord worldRead)
    (keepRecord related.balances) (keepRecord related.logs) (keepRecord related.logSize) got bounded derived
    (fun current overwrites read => attempted identity got current
      ((Overwrites.ofRetains retained).trans overwrites) read)
  refine ⟨final, ?_, holds⟩
  unfold CreationImplementation.dispatchWith
  apply Evaluates.letE packed
  apply LanguageResult.bind_success Creation.responseType lookedEvaluated
  apply Evaluates.ifFalse (.binary valueEvaluated (balanceCode.evaluates looked)
    (by simp [BinaryOp.apply, balance, key, funded]))
  apply LanguageResult.bind_success Creation.responseType recordRead
  apply Evaluates.ifFalse (.binary ((recordCode.part (index := 2) rfl).evaluates recordStore) .word
    (by simp [BinaryOp.apply, belowLimit]))
  exact admittedEvaluated

theorem Rewrites.mono {changed wider : List Nat} {initial final : Store} (rewrites : Rewrites changed initial final)
    (included : ∀ location ∈ changed, location ∈ wider) : Rewrites wider initial final :=
  ⟨rewrites.length_le, fun other value outside found =>
    rewrites.read other value (fun member => outside (included other member)) found⟩

theorem advanced_source {accounts : StorageCorrespondence.Accounts} {state : AccountCallSemantics.Shared}
    (worldSame : accounts.map Prod.fst = state.world) (creator : Word) (account : AccountState.Account) (identity : Nat) :
    (advancedAccounts accounts creator account identity).map Prod.fst = advancedWorld state creator account := by
  unfold advancedAccounts advancedWorld
  rw [StorageCorrespondence.put_source, worldSame]

/-- Applying the dispatcher to an admitted attempt without an init frame
publishes its account and balance changes. Logs and other cells are kept. -/
theorem dispatchWith_admitted {depth : Nat} {environment : Environment} {store : Store}
    {shared : AccountRuntime.References} {locations : SharedLocations}
    {anchors : List CatalogWorldCorrespondence.Anchor}
    {requestCode : Code} {request : Request} {state next : AccountCallSemantics.Shared} {response : Value}
    {runInit : Code → Code → Code} {identify : Code → Code}
    (references : SharedReferences depth environment shared locations)
    (requestRelated : CodeValue depth environment requestCode (requestValue request))
    (related : LinkedSharedStateRel anchors locations state store)
    (admitting : Admitting state request response next) :
    ∃ final, Evaluates environment store
      (CreationImplementation.dispatchWith (AccountRuntime.reference shared "world")
        (AccountRuntime.reference shared "balances") (AccountRuntime.reference shared "logs")
        (AccountRuntime.reference shared "logSize") (load (AccountRuntime.reference shared "worldComplete"))
        requestCode (CreationImplementation.admitted runInit (CreationImplementation.installWith identify shared)) depth)
        response final ∧
      LinkedSharedStateRel anchors locations next final ∧ Rewrites [locations.world, locations.balances] store final := by
  obtain ⟨accounts, worldSame, links, worldRead⟩ := related.linked
  have sharedRelated := related.shared
  have distinct := sharedRelated.distinct
  simp only [SharedLocations.all, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at distinct
  obtain ⟨⟨worldLogs, worldSize, worldBalances, worldComplete⟩, ⟨logsSize, logsBalances, logsComplete⟩,
    ⟨sizeBalances, sizeComplete⟩, balancesComplete⟩ := distinct
  let key := request.creator.bitAnd addressMask
  let argsValue := argumentsValue locations state.complete request
  have argsCode := CodeValue.bound depth environment argsValue
  have identityOf {account : AccountState.Account} {identity other : Nat}
      (first : StorageCorrespondence.get accounts key state.complete = .ok (account, identity))
      (second : StorageCorrespondence.get accounts key state.complete = .ok (account, other)) : identity = other := by
    have equal := Except.ok.inj (first.symm.trans second)
    exact (Prod.mk.inj equal).2
  cases admitting with
  | collision funded found belowLimit bounded derived occupied used =>
      rename_i account existing target
      obtain ⟨identity, got⟩ := source_get worldSame found
      let advanced := advancedAccounts accounts key account identity
      have advancedSame := advanced_source worldSame key account identity
      obtain ⟨final, evaluated, worldFinal, rewrites⟩ := dispatchWith_admit (runInit := runInit) (identify := identify)
        (property := fun final => final.read? locations.world = some (StorageCorrespondence.world advanced) ∧
          Rewrites [locations.world] store final)
        references requestRelated sharedRelated worldSame worldRead funded found belowLimit bounded derived
        (fun other gotOther current overwrites read => by
          have same := identityOf got gotOther
          subst same
          obtain ⟨identityE, lookedUp⟩ := CatalogWorldCorrespondence.lookup_of_source
            (accounts := advanced) (by rw [advancedSame]; exact occupied)
          have obtainedE : StorageCorrespondence.get advanced target state.complete = .ok (existing, identityE) := by
            simp only [StorageCorrespondence.get, lookedUp]
          let extra : Environment := [.word state.logSize, WordMapping.encode state.logs,
            WordMapping.encode state.balances, StorageCorrespondence.world advanced, .unit, .word target,
            StorageCorrespondence.record account identity, .word (StorageSemantics.readWord key state.balances)]
          have args9 := argsCode.prepend extra
          have target9 := (CodeValue.bound (depth + 3) ([StorageCorrespondence.record account identity,
            .word (StorageSemantics.readWord key state.balances)] ++ argsValue :: environment) (.word target)).prepend
            [.word state.logSize, WordMapping.encode state.logs, WordMapping.encode state.balances,
              StorageCorrespondence.world advanced, .unit]
          obtain ⟨final, evaluated, retained⟩ := attempt_collision (runInit := runInit)
            (installRuntime := CreationImplementation.installWith identify shared)
            (args9.part (index := 0) rfl) target9 (args9.part (index := 4) rfl) read obtainedE used
          exact ⟨final, protect_succeeded evaluated,
            (retained.read locations.world (List.getElem?_eq_some_iff.mp read).1).trans read,
            (Rewrites.ofOverwrites overwrites (by simp)).trans (Rewrites.ofRetains retained)⟩)
      refine ⟨final, evaluated, ⟨⟨⟨advanced, advancedSame, worldFinal⟩, ?_, ?_, ?_, ?_, sharedRelated.distinct⟩,
        ⟨advanced, advancedSame, links_put_same links got rfl, worldFinal⟩⟩, rewrites.mono (by simp)⟩
      · exact rewrites.read _ _ (by simp [Ne.symm worldLogs]) sharedRelated.logs
      · exact rewrites.read _ _ (by simp [Ne.symm worldSize]) sharedRelated.logSize
      · exact rewrites.read _ _ (by simp [Ne.symm worldBalances]) sharedRelated.balances
      · exact rewrites.read _ _ (by simp [Ne.symm worldComplete]) sharedRelated.complete
  | deployed funded found belowLimit bounded derived absent complete emptyInit transferred =>
      rename_i account target balances
      obtain ⟨identity, got⟩ := source_get worldSame found
      let advanced := advancedAccounts accounts key account identity
      have advancedSame := advanced_source worldSame key account identity
      have absentAdvanced : StorageCorrespondence.lookup target advanced = none := by
        have sourced := StorageCorrespondence.lookup_source advanced target
        rw [advancedSame, absent] at sourced
        cases lookedUp : StorageCorrespondence.lookup target advanced with
        | none => rfl
        | some entry => simp [lookedUp] at sourced
      have different : key ≠ target := by
        intro same
        have present := CatalogWorldCorrespondence.lookup_put_same accounts key
          {account with nonce := account.nonce.add (Word.ofNatModulo 1)} identity
        change StorageCorrespondence.lookup target (StorageCorrespondence.put key _ identity accounts) = none at absentAdvanced
        rw [← same, present] at absentAdvanced
        cases absentAdvanced
      let deployedAccounts := StorageCorrespondence.put target (CreationSemantics.createdAccount target) 0 advanced
      obtain ⟨final, evaluated, worldFinal, balancesFinal, rewrites⟩ := dispatchWith_admit (runInit := runInit)
        (identify := identify)
        (property := fun final => final.read? locations.world = some (StorageCorrespondence.world deployedAccounts) ∧
          final.read? locations.balances = some (WordMapping.encode balances) ∧
          Rewrites [locations.world, locations.balances] store final)
        references requestRelated sharedRelated worldSame worldRead funded found belowLimit bounded derived
        (fun other gotOther current overwrites read => by
          have same := identityOf got gotOther
          subst same
          let extra : Environment := [.word state.logSize, WordMapping.encode state.logs,
            WordMapping.encode state.balances, StorageCorrespondence.world advanced, .unit, .word target,
            StorageCorrespondence.record account identity, .word (StorageSemantics.readWord key state.balances)]
          have args9 := argsCode.prepend extra
          have target9 := (CodeValue.bound (depth + 3) ([StorageCorrespondence.record account identity,
            .word (StorageSemantics.readWord key state.balances)] ++ argsValue :: environment) (.word target)).prepend
            [.word state.logSize, WordMapping.encode state.logs, WordMapping.encode state.balances,
              StorageCorrespondence.world advanced, .unit]
          have balance9 := (CodeValue.bound (depth + 1) (argsValue :: environment)
            (.word (StorageSemantics.readWord key state.balances))).prepend
            [.word state.logSize, WordMapping.encode state.logs, WordMapping.encode state.balances,
              StorageCorrespondence.world advanced, .unit, .word target, StorageCorrespondence.record account identity]
          have request9 := args9.part (index := 5) rfl
          have creator9 := CreationAddressCorrespondence.binary_code (op := .wordAnd) (request9.part (index := 0) rfl)
            (CodeValue.number (2 ^ 160 - 1) _ _) rfl
          have complete9 := args9.part (index := 4) rfl
          rw [complete] at complete9
          have balancesRead := overwrites.read _ _ (Ne.symm worldBalances) sharedRelated.balances
          have completeRead := overwrites.read _ _ (Ne.symm worldComplete) sharedRelated.complete
          rw [complete] at completeRead
          obtain ⟨final, evaluated, worldFinal, balancesFinal, rewrites⟩ := attempt_deployed (runInit := runInit)
            (identify := identify) (restore := restoreCode (part 0 6 (fun here => .var (here - depth - 1)))
              (part 1 6 (fun here => .var (here - depth - 1))) (part 2 6 (fun here => .var (here - depth - 1)))
              (part 3 6 (fun here => .var (here - depth - 1))) (depth + 5))
            (references.prepend (extra ++ [argsValue])) (args9.part (index := 0) rfl) (args9.part (index := 1) rfl)
            complete9 creator9 (request9.part (index := 1) rfl) balance9 request9 target9 read balancesRead completeRead
            sharedRelated.distinct absentAdvanced different emptyInit transferred
          exact ⟨final, protect_succeeded evaluated, worldFinal, balancesFinal,
            (Rewrites.ofOverwrites overwrites (by simp)).trans rewrites⟩)
      refine ⟨final, evaluated, ⟨⟨⟨deployedAccounts, ?_, worldFinal⟩, ?_, ?_, balancesFinal, ?_, sharedRelated.distinct⟩,
        ⟨deployedAccounts, ?_, links_put_absent (accounts := advanced)
          (links_put_same (updated := {account with nonce := account.nonce.add (Word.ofNatModulo 1)}) links got rfl)
          absentAdvanced _ 0, worldFinal⟩⟩, rewrites⟩
      · rw [StorageCorrespondence.put_source, advancedSame]
      · exact rewrites.read _ _ (by simp [Ne.symm worldLogs, logsBalances]) sharedRelated.logs
      · exact rewrites.read _ _ (by simp [Ne.symm worldSize, sizeBalances]) sharedRelated.logSize
      · exact rewrites.read _ _ (by simp [Ne.symm worldComplete, Ne.symm balancesComplete.1]) sharedRelated.complete
      · rw [StorageCorrespondence.put_source, advancedSame]
  | unknown funded found belowLimit bounded derived unknown =>
      rename_i account target
      obtain ⟨identity, got⟩ := source_get worldSame found
      let advanced := advancedAccounts accounts key account identity
      have advancedSame := advanced_source worldSame key account identity
      obtain ⟨final, evaluated, worldFinal, balancesFinal, logsFinal, logSizeFinal, rewrites⟩ := dispatchWith_admit
        (runInit := runInit) (identify := identify)
        (property := fun final => final.read? locations.world = some (StorageCorrespondence.world advanced) ∧
          final.read? locations.balances = some (WordMapping.encode state.balances) ∧
          final.read? locations.logs = some (WordMapping.encode state.logs) ∧
          final.read? locations.logSize = some (.word state.logSize) ∧
          Rewrites [locations.world, locations.balances] store final)
        references requestRelated sharedRelated worldSame worldRead funded found belowLimit bounded derived
        (fun other gotOther current overwrites read => by
          have same := identityOf got gotOther
          subst same
          let extra : Environment := [.word state.logSize, WordMapping.encode state.logs,
            WordMapping.encode state.balances, StorageCorrespondence.world advanced, .unit, .word target,
            StorageCorrespondence.record account identity, .word (StorageSemantics.readWord key state.balances)]
          have args9 := argsCode.prepend extra
          have target9 := (CodeValue.bound (depth + 3) ([StorageCorrespondence.record account identity,
            .word (StorageSemantics.readWord key state.balances)] ++ argsValue :: environment) (.word target)).prepend
            [.word state.logSize, WordMapping.encode state.logs, WordMapping.encode state.balances,
              StorageCorrespondence.world advanced, .unit]
          cases unknown with
          | absent absent incomplete =>
              have absentAdvanced : StorageCorrespondence.lookup target advanced = none := by
                have sourced := StorageCorrespondence.lookup_source advanced target
                rw [advancedSame, absent] at sourced
                cases lookedUp : StorageCorrespondence.lookup target advanced with
                | none => rfl
                | some entry => simp [lookedUp] at sourced
              have complete9 := args9.part (index := 4) rfl
              rw [incomplete] at complete9
              obtain ⟨failed, attempted, retained⟩ := attempt_absent (runInit := runInit)
                (installRuntime := CreationImplementation.installWith identify shared)
                (args9.part (index := 0) rfl) target9 complete9 read absentAdvanced
              exact attempt_restored sharedRelated attempted
                ((Rewrites.ofOverwrites overwrites (by simp)).trans (Rewrites.ofRetains retained))
          | unknownCode occupied zero unknownCode =>
              rename_i existing
              obtain ⟨identityE, lookedUp⟩ := CatalogWorldCorrespondence.lookup_of_source
                (accounts := advanced) (by rw [advancedSame]; exact occupied)
              have obtainedE : StorageCorrespondence.get advanced target state.complete = .ok (existing, identityE) := by
                simp only [StorageCorrespondence.get, lookedUp]
              obtain ⟨failed, attempted, retained⟩ := attempt_unknownCode (runInit := runInit)
                (installRuntime := CreationImplementation.installWith identify shared)
                (args9.part (index := 0) rfl) target9 (args9.part (index := 4) rfl) read obtainedE zero unknownCode
              exact attempt_restored sharedRelated attempted
                ((Rewrites.ofOverwrites overwrites (by simp)).trans (Rewrites.ofRetains retained)))
      refine ⟨final, evaluated, ⟨⟨⟨advanced, advancedSame, worldFinal⟩, logsFinal, logSizeFinal, balancesFinal, ?_,
        sharedRelated.distinct⟩, ⟨advanced, advancedSame, links_put_same links got rfl, worldFinal⟩⟩, rewrites⟩
      exact rewrites.read _ _ (by simp [Ne.symm worldComplete, Ne.symm balancesComplete.1]) sharedRelated.complete
  | overflow funded found belowLimit bounded derived absent complete overflowed =>
      rename_i account target
      obtain ⟨identity, got⟩ := source_get worldSame found
      let advanced := advancedAccounts accounts key account identity
      have advancedSame := advanced_source worldSame key account identity
      have absentAdvanced : StorageCorrespondence.lookup target advanced = none := by
        have sourced := StorageCorrespondence.lookup_source advanced target
        rw [advancedSame, absent] at sourced
        cases lookedUp : StorageCorrespondence.lookup target advanced with
        | none => rfl
        | some entry => simp [lookedUp] at sourced
      obtain ⟨final, evaluated, worldFinal, balancesFinal, logsFinal, logSizeFinal, rewrites⟩ := dispatchWith_admit
        (runInit := runInit) (identify := identify)
        (property := fun final => final.read? locations.world = some (StorageCorrespondence.world advanced) ∧
          final.read? locations.balances = some (WordMapping.encode state.balances) ∧
          final.read? locations.logs = some (WordMapping.encode state.logs) ∧
          final.read? locations.logSize = some (.word state.logSize) ∧
          Rewrites [locations.world, locations.balances] store final)
        references requestRelated sharedRelated worldSame worldRead funded found belowLimit bounded derived
        (fun other gotOther current overwrites read => by
          have same := identityOf got gotOther
          subst same
          let extra : Environment := [.word state.logSize, WordMapping.encode state.logs,
            WordMapping.encode state.balances, StorageCorrespondence.world advanced, .unit, .word target,
            StorageCorrespondence.record account identity, .word (StorageSemantics.readWord key state.balances)]
          have args9 := argsCode.prepend extra
          have target9 := (CodeValue.bound (depth + 3) ([StorageCorrespondence.record account identity,
            .word (StorageSemantics.readWord key state.balances)] ++ argsValue :: environment) (.word target)).prepend
            [.word state.logSize, WordMapping.encode state.logs, WordMapping.encode state.balances,
              StorageCorrespondence.world advanced, .unit]
          have request9 := args9.part (index := 5) rfl
          have complete9 := args9.part (index := 4) rfl
          rw [complete] at complete9
          have balancesRead := overwrites.read _ _ (Ne.symm worldBalances) sharedRelated.balances
          obtain ⟨failed, attempted, frame⟩ := attempt_overflow (runInit := runInit)
            (installRuntime := CreationImplementation.installWith identify shared)
            (args9.part (index := 0) rfl) (args9.part (index := 1) rfl) complete9 (request9.part (index := 1) rfl)
            target9 read balancesRead worldBalances absentAdvanced overflowed
          exact attempt_restored sharedRelated attempted
            ((Rewrites.ofOverwrites overwrites (by simp)).trans (frame.mono (by simp))))
      refine ⟨final, evaluated, ⟨⟨⟨advanced, advancedSame, worldFinal⟩, logsFinal, logSizeFinal, balancesFinal, ?_,
        sharedRelated.distinct⟩, ⟨advanced, advancedSame, links_put_same links got rfl, worldFinal⟩⟩, rewrites⟩
      exact rewrites.read _ _ (by simp [Ne.symm worldComplete, Ne.symm balancesComplete.1]) sharedRelated.complete

/-- Applying the actual installed closure to an admitted attempt without an
init frame returns its response and publishes its shared changes. -/
theorem HandlerClosure.apply_admitted {locations : SharedLocations} {value : Value}
    (closure : HandlerClosure locations value) {request : Request} {state next : AccountCallSemantics.Shared}
    {response : Value} {anchors : List CatalogWorldCorrespondence.Anchor}
    {environment : Environment} {before middle initial : Store} {function argument : Core.Expr}
    (related : LinkedSharedStateRel anchors locations state initial) (admitting : Admitting state request response next)
    (resolved : Evaluates environment before function value middle)
    (supplied : Evaluates environment middle argument (requestValue request) initial) :
    ∃ final, Evaluates environment before (.apply function argument) response final ∧
      LinkedSharedStateRel anchors locations next final ∧ Rewrites [locations.world, locations.balances] initial final := by
  rcases closure with ⟨depth, captured, shared, runInit, identify, capturedClosure, references⟩
  cases capturedClosure
  obtain ⟨final, evaluated, nextRelated, rewrites⟩ := dispatchWith_admitted (runInit := runInit) (identify := identify)
    (references.prepend [requestValue request]) (CodeValue.bound depth captured (requestValue request)) related admitting
  exact ⟨final, .apply resolved supplied evaluated, nextRelated, rewrites⟩

end Solcore.Frontend.RustHull.CreationCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.CreationTransportCorrespondence
/-! The actual `Creation.invoke` transport. An unaddressable init range faults
before any frame cell changes. Otherwise memory covers the init range and
return data is cleared; at the depth limit the attempt returns zero, and below
it the init bytes are copied into fresh scratch cells and the installed
handler's response is published: a refusal, or an admitted attempt that runs
no init frame together with its shared account changes. A fault of the
handler is returned as is, and return data stays cleared. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.CreationCorrespondence
open Core Correspondence ScalarExecution CodeBuilder CallTransportCorrespondence

/-- Word inputs of one creation attempt, as the lowering evaluates them. -/
structure Arguments where
  creator : Word
  depth : Word
  value : Word
  salt : Word
  create2 : Bool
  gas : Word
  offset : Word
  length : Word

def argumentValues (locations : Locations) (callback : Nat) (arguments : Arguments) : List Value :=
  [.cellRef WordMapping.type locations.memory, .cellRef .word locations.memorySize,
    .cellRef WordMapping.type locations.returnData, .cellRef .word locations.returnDataSize,
    .cellRef (OptionalCell.cellType Creation.callbackType) callback,
    .word arguments.creator, .word arguments.depth, .word arguments.value, .word arguments.salt,
    .bool arguments.create2, .word arguments.gas, .word arguments.offset, .word arguments.length]

abbrev Inputs (depth : Nat) (environment : Environment) (locations : Locations) (callback : Nat)
    (arguments : Arguments) :=
  CodeValue depth environment (fun depth => .var depth) (bundleValues (argumentValues locations callback arguments))

theorem input_part {depth : Nat} {environment : Environment} {locations : Locations} {callback : Nat}
    {arguments : Arguments} (related : Inputs depth environment locations callback arguments)
    {index : Nat} {value : Value} (found : (argumentValues locations callback arguments)[index]? = some value) :
    CodeValue depth environment (CreationImplementation.input index) value := related.part found

theorem input_initial (locations : Locations) (callback : Nat) (arguments : Arguments) (environment : Environment) :
    Inputs 0 (bundleValues (argumentValues locations callback arguments) :: environment) locations callback arguments := by
  intro extra store
  exact .var (by simp)

/-- The request built from the copied init bytes. -/
def request (arguments : Arguments) (initCode : MemorySemantics.Entries) : Request :=
  ⟨arguments.creator.bitAnd addressMask, arguments.value, arguments.salt, arguments.create2,
    arguments.depth.add (Word.ofNatModulo 1), arguments.gas, initCode, arguments.length⟩

/-- Memory covers the init range and return data is empty. -/
def cleared (state : CallTransportSemantics.State) (size : Word) : CallTransportSemantics.State :=
  ⟨{state.memory with size := size}, [], Word.zero⟩

theorem Copy.exists (sourceWords : MemorySemantics.Entries) (destination source length : Word)
    (destinationWords : MemorySemantics.Entries) :
    ∃ finalWords, MemoryCopySemantics.Copy sourceWords destination source length destinationWords finalWords := by
  by_cases zero : length = Word.zero
  · subst zero
    exact ⟨destinationWords, .empty _ _ _ _⟩
  · have positive : 0 < length.val := by
      rcases Nat.eq_zero_or_pos length.val with same | positive
      · exact False.elim (zero (Fin.ext same))
      · exact positive
    have bounded : MemoryCopySemantics.width length ≤ length.val := by
      unfold MemoryCopySemantics.width
      split
      · rename_i large
        change 31 % wordModulus < length.val at large
        rw [Nat.mod_eq_of_lt (by decide)] at large
        omega
      · omega
    have widthSmall : MemoryCopySemantics.width length < wordModulus := by
      unfold MemoryCopySemantics.width; split <;> decide
    have value : (Word.ofNatModulo (MemoryCopySemantics.width length)).val = MemoryCopySemantics.width length :=
      Nat.mod_eq_of_lt widthSmall
    have widthPositive : 0 < MemoryCopySemantics.width length := by
      unfold MemoryCopySemantics.width; split <;> omega
    have smaller : (length.sub (Word.ofNatModulo (MemoryCopySemantics.width length))).val < length.val := by
      have subtracted : (length.sub (Word.ofNatModulo (MemoryCopySemantics.width length))).val =
          length.val - MemoryCopySemantics.width length := by
        simp only [Word.sub]
        rw [Fin.sub_val_of_le (by rw [Fin.le_def, value]; exact bounded), value]
      omega
    obtain ⟨finalWords, rest⟩ := Copy.exists
      (MemoryCopySemantics.remainingSource sourceWords source length)
      (destination.add (Word.ofNatModulo (MemoryCopySemantics.width length)))
      (source.add (Word.ofNatModulo (MemoryCopySemantics.width length)))
      (length.sub (Word.ofNatModulo (MemoryCopySemantics.width length)))
      (MemoryCopySemantics.written destinationWords destination length
        (MemoryCopySemantics.copiedWord sourceWords source length))
    exact ⟨finalWords, .step zero rest⟩
termination_by length.val

private theorem clear_evaluates {depth : Nat} {environment : Environment} {store final : Store}
    {locations : Locations} {callback : Nat} {arguments : Arguments} {state : CallTransportSemantics.State}
    {target : Value} {body : Code}
    (inputs : Inputs depth environment locations callback arguments)
    (related : StateRel locations state store)
    (continued : Evaluates ([Value.unit, .unit] ++ environment)
      (publishStore locations store [] Word.zero) (body (depth + 2)) target final) :
    Evaluates environment store
      (bind (CodeBuilder.store (CreationImplementation.input 2) CodeBuilder.empty) (fun _ =>
        bind (CodeBuilder.store (CreationImplementation.input 3) (number 0)) (fun _ => body)) depth) target final := by
  let writtenData : Store := store.set locations.returnData (WordMapping.encode [])
  have distinct := related.distinct
  simp [Locations.resources, LogsCorrespondence.Locations.all] at distinct
  have dataWritten : store.write? locations.returnData (WordMapping.encode []) = some writtenData :=
    Store.write?_eq_some_iff.mpr ⟨(List.getElem?_eq_some_iff.mp related.logs).1, rfl⟩
  have sizeFound : writtenData.read? locations.returnDataSize = some (.word state.returnDataSize) := by
    rw [Store.write?_preserves_other dataWritten (by intro same; simp_all)]
    exact related.logSize
  have sizeWritten : writtenData.write? locations.returnDataSize (.word Word.zero) =
      some (publishStore locations store [] Word.zero) :=
    Store.write?_eq_some_iff.mpr ⟨(List.getElem?_eq_some_iff.mp sizeFound).1, rfl⟩
  apply Evaluates.letE (bodyStore := writtenData)
  · exact .storeCell ((input_part inputs (index := 2) rfl).evaluates store) related.logs (.construct .unit) dataWritten
  · apply Evaluates.letE (bodyStore := publishStore locations store [] Word.zero)
    · exact .storeCell ((input_part (inputs.prepend [.unit]) (index := 3) rfl).evaluates writtenData)
        sizeFound .word sizeWritten
    · exact continued

/-- The dispatch prefix copies the init bytes into two fresh scratch cells; the
caller's cells are retained. -/
private theorem snapshot_evaluates {depth : Nat} {environment : Environment} {store : Store}
    {locations : Locations} {callback : Nat} {arguments : Arguments} {state : CallTransportSemantics.State}
    (inputs : Inputs depth environment locations callback arguments)
    (related : StateRel locations state store)
    (bounded : arguments.length.val ≤ CreationSemantics.maxInitCodeSize) :
    ∃ extra copiedStore initCode input,
      extra.length = 4 ∧ StoreRetains store copiedStore ∧
      Inputs (depth + 4) (extra ++ environment) locations callback arguments ∧
      CodeValue (depth + 4) (extra ++ environment) initCode (.cellRef WordMapping.type store.length) ∧
      MemoryCopySemantics.Copy state.memory.words Word.zero arguments.offset arguments.length [] input ∧
      copiedStore.read? store.length = some (WordMapping.encode input) ∧
      ∀ target final,
        Evaluates (extra ++ environment) copiedStore
          ((bindResult .word (fun depth => OptionalCell.read Creation.callbackType
              (CreationImplementation.input 4 depth) Creation.unavailableReason) fun function =>
            bindResult .word (apply function (CreationImplementation.request initCode))
              CreationImplementation.finish) (depth + 4)) target final →
        Evaluates environment store (CreationImplementation.dispatch depth) target final := by
  let snapshot := WordMapping.encode state.memory.words
  let inputRef := Value.cellRef WordMapping.type store.length
  let sizeRef := Value.cellRef .word (store.length + 1)
  let allocated : Store := store ++ [WordMapping.encode [], .word Word.zero]
  let inputCode : Code := fun here => .var (here - (depth + 1) - 1)
  have snapshotRelated := CodeValue.bound depth environment snapshot
  have inputRelated := CodeValue.bound (depth + 1) (snapshot :: environment) inputRef
  have sizeRelated := CodeValue.bound (depth + 2) (inputRef :: snapshot :: environment) sizeRef
  have scratchRelated : MemoryCorrespondence.StateRel store.length (store.length + 1) {} allocated := by
    refine ⟨by omega, ?_, ?_⟩ <;> simp [allocated, Store.read?]
  let extraInput : Environment := [sizeRef, inputRef, snapshot]
  obtain ⟨size, touched⟩ : ∃ size,
      MemorySemantics.touchSize? ({} : MemorySemantics.State).size Word.zero arguments.length = some size := by
    change ∃ size, MemorySemantics.touchSize? Word.zero Word.zero arguments.length = some size
    unfold MemorySemantics.touchSize?
    by_cases zero : arguments.length = Word.zero
    · simp [zero]
    · have sum : Word.zero.add arguments.length = arguments.length := by
        apply Fin.ext
        show (0 + arguments.length.val) % wordModulus = arguments.length.val
        rw [Nat.zero_add, Nat.mod_eq_of_lt arguments.length.isLt]
      have notWrapped : ¬Word.zero > arguments.length := fun wrapped => Nat.not_lt_zero _ wrapped
      have notLarge : ¬arguments.length > Word.ofNatModulo (wordModulus - 32) := by
        intro large
        change (Word.ofNatModulo (wordModulus - 32)).val < arguments.length.val at large
        have limit : (Word.ofNatModulo (wordModulus - 32)).val = wordModulus - 32 :=
          Nat.mod_eq_of_lt (by decide)
        have small : (49152 : Nat) < wordModulus - 32 := by decide
        simp only [CreationSemantics.maxInitCodeSize] at bounded
        omega
      simp only [beq_iff_eq, zero, ↓reduceIte, sum, notWrapped, notLarge]
      exact ⟨_, rfl⟩
  obtain ⟨words, copiedWords⟩ := Copy.exists state.memory.words Word.zero arguments.offset arguments.length []
  have copied : MemoryCopySemantics.From state.memory.words Word.zero arguments.offset arguments.length
      {} (.value .unit) ⟨words, size⟩ := .done touched copiedWords
  obtain ⟨target, copiedStore, resultRelated, evaluated, inputMemory, frame⟩ :=
    MemoryCopyCorrespondence.copyPackedFrom_preserves copied scratchRelated
      ((inputRelated.prepend [sizeRef]).evaluates allocated) (sizeRelated.evaluates allocated) .word
      ((snapshotRelated.prepend [sizeRef, inputRef]).evaluates allocated)
      ((input_part (inputs.prepend extraInput) (index := 11) rfl).evaluates allocated)
      ((input_part (inputs.prepend extraInput) (index := 12) rfl).evaluates allocated)
  cases resultRelated with
  | value valueRelated =>
      cases valueRelated
      have retained : StoreRetains store copiedStore := by
        constructor
        · have length := frame.length
          simp only [allocated, List.length_append, List.length_cons, List.length_nil] at length
          omega
        · intro location bounded
          have found : store.read? location = some store[location] := List.getElem?_eq_getElem bounded
          have after : copiedStore.read? location = some store[location] :=
            frame.read location _ (by omega) (by omega)
              (by simpa only [allocated, Store.read?, List.getElem?_append_left bounded] using found)
          exact after.trans found.symm
      refine ⟨.unit :: extraInput, copiedStore, inputCode, words, rfl, retained, inputs.prepend (.unit :: extraInput),
        inputRelated.prepend [.unit, sizeRef], copiedWords, inputMemory.memory, ?_⟩
      intro target final completed
      unfold CreationImplementation.dispatch CodeBuilder.bind
      apply Evaluates.letE (.loadCell ((input_part inputs (index := 0) rfl).evaluates store) related.memory)
      apply Evaluates.letE (bodyStore := store ++ [WordMapping.encode []])
      · exact .newCell (.construct .unit)
      · apply Evaluates.letE (bodyStore := allocated)
        · simpa only [allocated, List.length_append, List.length_cons, List.length_nil, List.append_assoc,
            List.cons_append, List.nil_append, inputRef, snapshot, resources, CodeBuilder.allocate, CodeBuilder.number,
            CodeBuilder.constant, show Word.ofNatModulo 0 = Word.zero from rfl] using
            (Evaluates.newCell (elementType := .word) (environment := inputRef :: snapshot :: environment)
              (initialStore := store ++ [WordMapping.encode []]) Evaluates.word (initialValue := .word Word.zero))
        · exact LanguageResult.bind_success .word evaluated completed

/-- The payload of a handler response with empty revert data. -/
def responsePayload (address : Word) : Value := bundleValues [.word address, WordMapping.encode [], .word Word.zero]

/-- The payload of the refused handler response. -/
def refusedPayload : Value := responsePayload Word.zero

private theorem finish_evaluates {depth : Nat} {environment : Environment} {store : Store}
    {locations : Locations} {callback : Nat} {arguments : Arguments} {state : CallTransportSemantics.State}
    (address : Word) (inputs : Inputs depth environment locations callback arguments)
    (related : StateRel locations state store) :
    Evaluates (responsePayload address :: environment) store
      (CreationImplementation.finish (fun here => .var (here - depth - 1)) (depth + 1))
      (.inRight .word (.word address)) (publishStore locations store [] Word.zero) := by
  let writtenData : Store := store.set locations.returnData (WordMapping.encode [])
  have distinct := related.distinct
  simp [Locations.resources, LogsCorrespondence.Locations.all] at distinct
  have dataWritten : store.write? locations.returnData (WordMapping.encode []) = some writtenData :=
    Store.write?_eq_some_iff.mpr ⟨(List.getElem?_eq_some_iff.mp related.logs).1, rfl⟩
  have sizeFound : writtenData.read? locations.returnDataSize = some (.word state.returnDataSize) := by
    rw [Store.write?_preserves_other dataWritten (by intro same; simp_all)]
    exact related.logSize
  have sizeWritten : writtenData.write? locations.returnDataSize (.word Word.zero) =
      some (publishStore locations store [] Word.zero) :=
    Store.write?_eq_some_iff.mpr ⟨(List.getElem?_eq_some_iff.mp sizeFound).1, rfl⟩
  have payloadCode := CodeValue.bound depth environment (responsePayload address)
  unfold CreationImplementation.finish CodeBuilder.bind
  apply Evaluates.letE (bodyStore := writtenData)
  · exact .storeCell (((input_part inputs (index := 2) rfl).prepend [responsePayload address]).evaluates store)
      related.logs ((payloadCode.part (index := 1) rfl).evaluates store) dataWritten
  · apply Evaluates.letE (bodyStore := publishStore locations store [] Word.zero)
    · exact .storeCell (((input_part inputs (index := 3) rfl).prepend [.unit, responsePayload address]).evaluates writtenData)
        sizeFound (((payloadCode.part (index := 2) rfl).prepend [.unit]).evaluates writtenData) sizeWritten
    · exact .inRight (((payloadCode.part (index := 0) rfl).prepend [.unit, .unit]).evaluates _)

theorem invoke_overflow {locations : Locations} {callback : Nat} {arguments : Arguments}
    {state : CallTransportSemantics.State} {environment : Environment} {initial store : Store}
    {memoryReference sizeReference returnDataReference returnSizeReference callbackReference
      creatorAddress depth transferredValue saltValue isCreate2 suppliedGas offset length : Core.Expr}
    (packed : Evaluates environment initial
      (bundle [memoryReference, sizeReference, returnDataReference, returnSizeReference,
        callbackReference, creatorAddress, depth, transferredValue, saltValue, isCreate2,
        suppliedGas, offset, length])
      (bundleValues (argumentValues locations callback arguments)) store)
    (related : StateRel locations state store)
    (invalid : MemorySemantics.touchSize? state.memory.size arguments.offset arguments.length = none) :
    Evaluates environment initial
      (Creation.invoke memoryReference sizeReference returnDataReference returnSizeReference callbackReference
        creatorAddress depth transferredValue saltValue isCreate2 suppliedGas offset length)
      (.inLeft .word (.word Memory.overflowReason)) store := by
  rw [CreationImplementation.invoke_eq]
  apply Evaluates.letE packed
  have inputs := input_initial locations callback arguments environment
  have touched := MemoryCorrespondence.touch_evaluates (size := state.memory.size)
    ((input_part inputs (index := 1) rfl).evaluates store)
    ((input_part inputs (index := 11) rfl).evaluates store)
    ((input_part inputs (index := 12) rfl).evaluates store) related.memorySize
  simp only [MemoryCorrespondence.touchResult, invalid, MemoryCorrespondence.touchStore_failure invalid] at touched
  exact LanguageResult.bind_failure .word touched

theorem invoke_depth {locations : Locations} {callback : Nat} {arguments : Arguments}
    {state : CallTransportSemantics.State} {environment : Environment} {initial store : Store}
    {memoryReference sizeReference returnDataReference returnSizeReference callbackReference
      creatorAddress depth transferredValue saltValue isCreate2 suppliedGas offset length : Core.Expr}
    (packed : Evaluates environment initial
      (bundle [memoryReference, sizeReference, returnDataReference, returnSizeReference,
        callbackReference, creatorAddress, depth, transferredValue, saltValue, isCreate2,
        suppliedGas, offset, length])
      (bundleValues (argumentValues locations callback arguments)) store)
    (related : StateRel locations state store) {size : Word}
    (touchedSize : MemorySemantics.touchSize? state.memory.size arguments.offset arguments.length = some size)
    (exceeded : arguments.depth > Word.ofNatModulo 1023) :
    ∃ final, Evaluates environment initial
      (Creation.invoke memoryReference sizeReference returnDataReference returnSizeReference callbackReference
        creatorAddress depth transferredValue saltValue isCreate2 suppliedGas offset length)
      (.inRight .word (.word Word.zero)) final ∧
      StateRel locations (cleared state size) final ∧ Frame locations store final := by
  rw [CreationImplementation.invoke_eq]
  have inputs := input_initial locations callback arguments environment
  have touched := MemoryCorrespondence.touch_evaluates (size := state.memory.size)
    ((input_part inputs (index := 1) rfl).evaluates store)
    ((input_part inputs (index := 11) rfl).evaluates store)
    ((input_part inputs (index := 12) rfl).evaluates store) related.memorySize
  simp only [MemoryCorrespondence.touchResult, touchedSize] at touched
  let inputStore := MemoryCorrespondence.touchStore store locations.memorySize state.memory.size
    arguments.offset arguments.length
  have inputRelated : StateRel locations {state with memory := {state.memory with size := size}} inputStore :=
    related.touch touchedSize
  have inputFrame := LogsCorrespondence.Frame.touch locations.resources store state.memory.size
    arguments.offset arguments.length
  have clearedRelated : StateRel locations (cleared state size)
      (publishStore locations inputStore [] Word.zero) := published inputRelated [] Word.zero
  have clearFrame := LogsCorrespondence.Frame.publish locations.resources inputStore [] Word.zero
  refine ⟨publishStore locations inputStore [] Word.zero, .letE packed ?_, clearedRelated,
    inputFrame.trans clearFrame⟩
  apply LanguageResult.bind_success .word touched
  apply clear_evaluates (inputs.prepend [.unit]) inputRelated
  exact .ifTrue (.binary ((input_part (inputs.prepend [.unit, .unit, .unit]) (index := 6) rfl).evaluates _) .word
    (by simp [BinaryOp.apply, Creation.depthLimit, exceeded])) (.inRight .word)

/-- Below the depth limit the actual dispatch copies the init bytes and
publishes the handler's refusal: return data stays empty and the result is
zero. The handler and the shared state are those of the creating frame. -/
theorem invoke_refused {locations : Locations} {callback : Nat} {arguments : Arguments}
    {state : CallTransportSemantics.State} {environment : Environment} {initial store : Store}
    {memoryReference sizeReference returnDataReference returnSizeReference callbackReference
      creatorAddress depth transferredValue saltValue isCreate2 suppliedGas offset length : Core.Expr}
    {sharedLocations : AccountCallCorrespondence.SharedLocations} {shared : AccountCallSemantics.Shared}
    {function : Value}
    (packed : Evaluates environment initial
      (bundle [memoryReference, sizeReference, returnDataReference, returnSizeReference,
        callbackReference, creatorAddress, depth, transferredValue, saltValue, isCreate2,
        suppliedGas, offset, length])
      (bundleValues (argumentValues locations callback arguments)) store)
    (related : StateRel locations state store) {size : Word}
    (touchedSize : MemorySemantics.touchSize? state.memory.size arguments.offset arguments.length = some size)
    (allowed : ¬arguments.depth > Word.ofNatModulo 1023)
    (bounded : arguments.length.val ≤ CreationSemantics.maxInitCodeSize)
    (callbackRead : store.read? callback = some (.inRight .unit function))
    (callbackOutside : callback ∉ locations.resources.all)
    (handler : HandlerClosure sharedLocations function)
    (sharedRelated : AccountCallCorrespondence.SharedStateRel sharedLocations shared store)
    (separate : ∀ location ∈ sharedLocations.all, location ∉ locations.resources.all)
    (refusing : ∀ initCode, Refusing shared (request arguments initCode)) :
    ∃ final, Evaluates environment initial
      (Creation.invoke memoryReference sizeReference returnDataReference returnSizeReference callbackReference
        creatorAddress depth transferredValue saltValue isCreate2 suppliedGas offset length)
      (.inRight .word (.word Word.zero)) final ∧
      StateRel locations (cleared state size) final ∧ Frame locations store final := by
  rw [CreationImplementation.invoke_eq]
  have inputs := input_initial locations callback arguments environment
  have touched := MemoryCorrespondence.touch_evaluates (size := state.memory.size)
    ((input_part inputs (index := 1) rfl).evaluates store)
    ((input_part inputs (index := 11) rfl).evaluates store)
    ((input_part inputs (index := 12) rfl).evaluates store) related.memorySize
  simp only [MemoryCorrespondence.touchResult, touchedSize] at touched
  let inputStore := MemoryCorrespondence.touchStore store locations.memorySize state.memory.size
    arguments.offset arguments.length
  have inputRelated : StateRel locations {state with memory := {state.memory with size := size}} inputStore :=
    related.touch touchedSize
  have inputFrame := LogsCorrespondence.Frame.touch locations.resources store state.memory.size
    arguments.offset arguments.length
  let clearedStore := publishStore locations inputStore [] Word.zero
  have clearedRelated : StateRel locations (cleared state size) clearedStore := published inputRelated [] Word.zero
  have clearFrame := LogsCorrespondence.Frame.publish locations.resources inputStore [] Word.zero
  have framed := inputFrame.trans clearFrame
  have dispatchInputs := inputs.prepend [.unit, .unit, .unit]
  obtain ⟨extra, copiedStore, initCode, input, extraLength, retained, inputs', initRelated, _, initRead, entered⟩ :=
    snapshot_evaluates dispatchInputs clearedRelated bounded
  have keep {location : Nat} {value : Value} (outside : location ∉ locations.resources.all)
      (found : store.read? location = some value) : copiedStore.read? location = some value := by
    have afterClear := framed.read location value outside found
    exact (retained.read location (List.getElem?_eq_some_iff.mp afterClear).1).trans afterClear
  have callbackFound := keep callbackOutside callbackRead
  have functionRead := OptionalCell.read_success Creation.unavailableReason
    ((input_part inputs' (index := 4) rfl).evaluates copiedStore) callbackFound
  have sharedCopied : AccountCallCorrespondence.SharedStateRel sharedLocations shared copiedStore := by
    obtain ⟨accounts, worldSame, worldRead⟩ := sharedRelated.world
    exact ⟨⟨accounts, worldSame, keep (separate _ (by simp [AccountCallCorrespondence.SharedLocations.all])) worldRead⟩,
      keep (separate _ (by simp [AccountCallCorrespondence.SharedLocations.all])) sharedRelated.logs,
      keep (separate _ (by simp [AccountCallCorrespondence.SharedLocations.all])) sharedRelated.logSize,
      keep (separate _ (by simp [AccountCallCorrespondence.SharedLocations.all])) sharedRelated.balances,
      keep (separate _ (by simp [AccountCallCorrespondence.SharedLocations.all])) sharedRelated.complete,
      sharedRelated.distinct⟩
  have functionCode := CodeValue.bound (0 + [Value.unit, Value.unit, Value.unit].length + 4)
    (extra ++ ([.unit, .unit, .unit] ++ bundleValues (argumentValues locations callback arguments) :: environment)) function
  have callInputs := inputs'.prepend [function]
  have requestEvaluated : Evaluates (function :: extra ++ ([.unit, .unit, .unit] ++
      bundleValues (argumentValues locations callback arguments) :: environment)) copiedStore
      (CreationImplementation.request initCode (0 + 3 + 4 + 1))
      (requestValue (request arguments input)) copiedStore := by
    refine .pair (.binary ((input_part callInputs (index := 5) rfl).evaluates copiedStore) .word rfl) ?_
    refine .pair ((input_part callInputs (index := 7) rfl).evaluates copiedStore) ?_
    refine .pair ((input_part callInputs (index := 8) rfl).evaluates copiedStore) ?_
    refine .pair ((input_part callInputs (index := 9) rfl).evaluates copiedStore) ?_
    refine .pair (.binary ((input_part callInputs (index := 6) rfl).evaluates copiedStore) .word rfl) ?_
    refine .pair ((input_part callInputs (index := 10) rfl).evaluates copiedStore) ?_
    exact .pair (.loadCell ((initRelated.prepend [function]).evaluates copiedStore) initRead)
      ((input_part callInputs (index := 12) rfl).evaluates copiedStore)
  obtain ⟨afterCall, called, callRetained⟩ := handler.apply_refused sharedCopied (refusing input)
    ((functionCode.evaluates copiedStore)) requestEvaluated
  have afterRelated := state_retained clearedRelated (retained.trans callRetained)
  have finished := finish_evaluates Word.zero callInputs afterRelated
  refine ⟨publishStore locations afterCall [] Word.zero, .letE packed ?_, published afterRelated [] Word.zero,
    (framed.trans (retained_frame locations (retained.trans callRetained))).trans
      (LogsCorrespondence.Frame.publish locations.resources afterCall [] Word.zero)⟩
  apply LanguageResult.bind_success .word touched
  apply clear_evaluates (inputs.prepend [.unit]) inputRelated
  apply Evaluates.ifFalse (.binary ((input_part dispatchInputs (index := 6) rfl).evaluates _) .word
    (by simp [BinaryOp.apply, Creation.depthLimit, allowed]))
  apply entered
  apply LanguageResult.bind_success .word functionRead
  apply LanguageResult.bind_success .word called
  exact finished

theorem state_rewritten {locations : Locations} {state : CallTransportSemantics.State} {initial final : Store}
    {changed : List Nat} (related : StateRel locations state initial) (rewrites : Rewrites changed initial final)
    (separate : ∀ location ∈ changed, location ∉ locations.resources.all) : StateRel locations state final := by
  have outside {location : Nat} (member : location ∈ locations.resources.all) : location ∉ changed :=
    fun inside => separate location inside member
  refine ⟨related.distinct, ?_, ?_, ?_, ?_⟩
  · exact rewrites.read _ _ (outside (by simp [Locations.resources, LogsCorrespondence.Locations.all])) related.memory
  · exact rewrites.read _ _ (outside (by simp [Locations.resources, LogsCorrespondence.Locations.all])) related.memorySize
  · exact rewrites.read _ _ (outside (by simp [Locations.resources, LogsCorrespondence.Locations.all])) related.logs
  · exact rewrites.read _ _ (outside (by simp [Locations.resources, LogsCorrespondence.Locations.all])) related.logSize

theorem LinkedSharedStateRel.preserved {anchors : List CatalogWorldCorrespondence.Anchor}
    {locations : AccountCallCorrespondence.SharedLocations} {state : AccountCallSemantics.Shared} {initial final : Store}
    (related : AccountCallCorrespondence.LinkedSharedStateRel anchors locations state initial)
    (preserved : ∀ location ∈ locations.all, ∀ value, initial.read? location = some value → final.read? location = some value) :
    AccountCallCorrespondence.LinkedSharedStateRel anchors locations state final := by
  obtain ⟨⟨⟨accounts, worldSame, worldRead⟩, logs, logSize, balances, complete, distinct⟩, linked⟩ := related
  refine ⟨⟨⟨accounts, worldSame, preserved _ (by simp [AccountCallCorrespondence.SharedLocations.all]) _ worldRead⟩,
    preserved _ (by simp [AccountCallCorrespondence.SharedLocations.all]) _ logs,
    preserved _ (by simp [AccountCallCorrespondence.SharedLocations.all]) _ logSize,
    preserved _ (by simp [AccountCallCorrespondence.SharedLocations.all]) _ balances,
    preserved _ (by simp [AccountCallCorrespondence.SharedLocations.all]) _ complete, distinct⟩,
    linked.read_preserved (preserved _ (by simp [AccountCallCorrespondence.SharedLocations.all]))⟩

/-- Below the depth limit an admitted attempt that runs no init frame returns
its address with empty return data, and its shared account changes are
published. The handler and the shared state are those of the creating frame. -/
theorem invoke_admitted {locations : Locations} {callback : Nat} {arguments : Arguments}
    {state : CallTransportSemantics.State} {environment : Environment} {initial store : Store}
    {memoryReference sizeReference returnDataReference returnSizeReference callbackReference
      creatorAddress depth transferredValue saltValue isCreate2 suppliedGas offset length : Core.Expr}
    {sharedLocations : AccountCallCorrespondence.SharedLocations} {shared next : AccountCallSemantics.Shared}
    {anchors : List CatalogWorldCorrespondence.Anchor} {function : Value} {address : Word}
    (packed : Evaluates environment initial
      (bundle [memoryReference, sizeReference, returnDataReference, returnSizeReference,
        callbackReference, creatorAddress, depth, transferredValue, saltValue, isCreate2,
        suppliedGas, offset, length])
      (bundleValues (argumentValues locations callback arguments)) store)
    (related : StateRel locations state store) {size : Word}
    (touchedSize : MemorySemantics.touchSize? state.memory.size arguments.offset arguments.length = some size)
    (allowed : ¬arguments.depth > Word.ofNatModulo 1023)
    (bounded : arguments.length.val ≤ CreationSemantics.maxInitCodeSize)
    (callbackRead : store.read? callback = some (.inRight .unit function))
    (callbackOutside : callback ∉ locations.resources.all)
    (handler : HandlerClosure sharedLocations function)
    (sharedRelated : AccountCallCorrespondence.LinkedSharedStateRel anchors sharedLocations shared store)
    (separate : ∀ location ∈ sharedLocations.all, location ∉ locations.resources.all)
    (admitting : ∀ initCode,
      MemoryCopySemantics.Copy state.memory.words Word.zero arguments.offset arguments.length [] initCode →
      Admitting shared (request arguments initCode) (.inRight .word (responsePayload address)) next) :
    ∃ final, Evaluates environment initial
      (Creation.invoke memoryReference sizeReference returnDataReference returnSizeReference callbackReference
        creatorAddress depth transferredValue saltValue isCreate2 suppliedGas offset length)
      (.inRight .word (.word address)) final ∧
      StateRel locations (cleared state size) final ∧
      AccountCallCorrespondence.LinkedSharedStateRel anchors sharedLocations next final ∧
      store.length ≤ final.length ∧
      ∀ location value, location ∉ locations.resources.all →
        location ∉ [sharedLocations.world, sharedLocations.balances] →
        store.read? location = some value → final.read? location = some value := by
  rw [CreationImplementation.invoke_eq]
  have inputs := input_initial locations callback arguments environment
  have touched := MemoryCorrespondence.touch_evaluates (size := state.memory.size)
    ((input_part inputs (index := 1) rfl).evaluates store)
    ((input_part inputs (index := 11) rfl).evaluates store)
    ((input_part inputs (index := 12) rfl).evaluates store) related.memorySize
  simp only [MemoryCorrespondence.touchResult, touchedSize] at touched
  let inputStore := MemoryCorrespondence.touchStore store locations.memorySize state.memory.size
    arguments.offset arguments.length
  have inputRelated : StateRel locations {state with memory := {state.memory with size := size}} inputStore :=
    related.touch touchedSize
  have inputFrame := LogsCorrespondence.Frame.touch locations.resources store state.memory.size
    arguments.offset arguments.length
  let clearedStore := publishStore locations inputStore [] Word.zero
  have clearedRelated : StateRel locations (cleared state size) clearedStore := published inputRelated [] Word.zero
  have clearFrame := LogsCorrespondence.Frame.publish locations.resources inputStore [] Word.zero
  have framed := inputFrame.trans clearFrame
  have dispatchInputs := inputs.prepend [.unit, .unit, .unit]
  obtain ⟨extra, copiedStore, initCode, input, extraLength, retained, inputs', initRelated, copiedInit, initRead, entered⟩ :=
    snapshot_evaluates dispatchInputs clearedRelated bounded
  have keep {location : Nat} {value : Value} (outside : location ∉ locations.resources.all)
      (found : store.read? location = some value) : copiedStore.read? location = some value := by
    have afterClear := framed.read location value outside found
    exact (retained.read location (List.getElem?_eq_some_iff.mp afterClear).1).trans afterClear
  have callbackFound := keep callbackOutside callbackRead
  have functionRead := OptionalCell.read_success Creation.unavailableReason
    ((input_part inputs' (index := 4) rfl).evaluates copiedStore) callbackFound
  have sharedCopied := LinkedSharedStateRel.preserved sharedRelated
    (fun location member _ found => keep (separate location member) found)
  have functionCode := CodeValue.bound (0 + [Value.unit, Value.unit, Value.unit].length + 4)
    (extra ++ ([.unit, .unit, .unit] ++ bundleValues (argumentValues locations callback arguments) :: environment)) function
  have callInputs := inputs'.prepend [function]
  have requestEvaluated : Evaluates (function :: extra ++ ([.unit, .unit, .unit] ++
      bundleValues (argumentValues locations callback arguments) :: environment)) copiedStore
      (CreationImplementation.request initCode (0 + 3 + 4 + 1))
      (requestValue (request arguments input)) copiedStore := by
    refine .pair (.binary ((input_part callInputs (index := 5) rfl).evaluates copiedStore) .word rfl) ?_
    refine .pair ((input_part callInputs (index := 7) rfl).evaluates copiedStore) ?_
    refine .pair ((input_part callInputs (index := 8) rfl).evaluates copiedStore) ?_
    refine .pair ((input_part callInputs (index := 9) rfl).evaluates copiedStore) ?_
    refine .pair (.binary ((input_part callInputs (index := 6) rfl).evaluates copiedStore) .word rfl) ?_
    refine .pair ((input_part callInputs (index := 10) rfl).evaluates copiedStore) ?_
    exact .pair (.loadCell ((initRelated.prepend [function]).evaluates copiedStore) initRead)
      ((input_part callInputs (index := 12) rfl).evaluates copiedStore)
  obtain ⟨afterCall, called, nextRelated, rewrites⟩ := handler.apply_admitted sharedCopied
    (admitting input copiedInit) (functionCode.evaluates copiedStore) requestEvaluated
  have localSeparate : ∀ location ∈ [sharedLocations.world, sharedLocations.balances],
      location ∉ locations.resources.all := by
    intro location member
    apply separate
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> simp [AccountCallCorrespondence.SharedLocations.all]
  have afterRelated := state_rewritten (state_retained clearedRelated retained) rewrites localSeparate
  have finished := finish_evaluates address callInputs afterRelated
  have publishFrame := LogsCorrespondence.Frame.publish locations.resources afterCall [] Word.zero
  refine ⟨publishStore locations afterCall [] Word.zero, .letE packed ?_, published afterRelated [] Word.zero,
    LinkedSharedStateRel.preserved nextRelated
      (fun location member value found => publishFrame.read location value (separate location member) found),
    ?_, ?_⟩
  · apply LanguageResult.bind_success .word touched
    apply clear_evaluates (inputs.prepend [.unit]) inputRelated
    apply Evaluates.ifFalse (.binary ((input_part dispatchInputs (index := 6) rfl).evaluates _) .word
      (by simp [BinaryOp.apply, Creation.depthLimit, allowed]))
    apply entered
    apply LanguageResult.bind_success .word functionRead
    apply LanguageResult.bind_success .word called
    exact finished
  · exact Nat.le_trans (Nat.le_trans framed.length retained.length_le)
      (Nat.le_trans rewrites.length_le publishFrame.length)
  · intro location value outside unshared found
    exact publishFrame.read location value outside (rewrites.read location value unshared (keep outside found))

/-- Below the depth limit an admitted attempt that faults after the nonce
advance returns its failure reason. Return data stays cleared, and the shared
cells hold the changes the handler keeps. -/
theorem invoke_failed {locations : Locations} {callback : Nat} {arguments : Arguments}
    {state : CallTransportSemantics.State} {environment : Environment} {initial store : Store}
    {memoryReference sizeReference returnDataReference returnSizeReference callbackReference
      creatorAddress depth transferredValue saltValue isCreate2 suppliedGas offset length : Core.Expr}
    {sharedLocations : AccountCallCorrespondence.SharedLocations} {shared next : AccountCallSemantics.Shared}
    {anchors : List CatalogWorldCorrespondence.Anchor} {function : Value} {reason : Word}
    (packed : Evaluates environment initial
      (bundle [memoryReference, sizeReference, returnDataReference, returnSizeReference,
        callbackReference, creatorAddress, depth, transferredValue, saltValue, isCreate2,
        suppliedGas, offset, length])
      (bundleValues (argumentValues locations callback arguments)) store)
    (related : StateRel locations state store) {size : Word}
    (touchedSize : MemorySemantics.touchSize? state.memory.size arguments.offset arguments.length = some size)
    (allowed : ¬arguments.depth > Word.ofNatModulo 1023)
    (bounded : arguments.length.val ≤ CreationSemantics.maxInitCodeSize)
    (callbackRead : store.read? callback = some (.inRight .unit function))
    (callbackOutside : callback ∉ locations.resources.all)
    (handler : HandlerClosure sharedLocations function)
    (sharedRelated : AccountCallCorrespondence.LinkedSharedStateRel anchors sharedLocations shared store)
    (separate : ∀ location ∈ sharedLocations.all, location ∉ locations.resources.all)
    (admitting : ∀ initCode,
      MemoryCopySemantics.Copy state.memory.words Word.zero arguments.offset arguments.length [] initCode →
      Admitting shared (request arguments initCode) (.inLeft Creation.responseType (.word reason)) next) :
    ∃ final, Evaluates environment initial
      (Creation.invoke memoryReference sizeReference returnDataReference returnSizeReference callbackReference
        creatorAddress depth transferredValue saltValue isCreate2 suppliedGas offset length)
      (.inLeft .word (.word reason)) final ∧
      StateRel locations (cleared state size) final ∧
      AccountCallCorrespondence.LinkedSharedStateRel anchors sharedLocations next final ∧
      store.length ≤ final.length ∧
      ∀ location value, location ∉ locations.resources.all →
        location ∉ [sharedLocations.world, sharedLocations.balances] →
        store.read? location = some value → final.read? location = some value := by
  rw [CreationImplementation.invoke_eq]
  have inputs := input_initial locations callback arguments environment
  have touched := MemoryCorrespondence.touch_evaluates (size := state.memory.size)
    ((input_part inputs (index := 1) rfl).evaluates store)
    ((input_part inputs (index := 11) rfl).evaluates store)
    ((input_part inputs (index := 12) rfl).evaluates store) related.memorySize
  simp only [MemoryCorrespondence.touchResult, touchedSize] at touched
  let inputStore := MemoryCorrespondence.touchStore store locations.memorySize state.memory.size
    arguments.offset arguments.length
  have inputRelated : StateRel locations {state with memory := {state.memory with size := size}} inputStore :=
    related.touch touchedSize
  have inputFrame := LogsCorrespondence.Frame.touch locations.resources store state.memory.size
    arguments.offset arguments.length
  let clearedStore := publishStore locations inputStore [] Word.zero
  have clearedRelated : StateRel locations (cleared state size) clearedStore := published inputRelated [] Word.zero
  have clearFrame := LogsCorrespondence.Frame.publish locations.resources inputStore [] Word.zero
  have framed := inputFrame.trans clearFrame
  have dispatchInputs := inputs.prepend [.unit, .unit, .unit]
  obtain ⟨extra, copiedStore, initCode, input, extraLength, retained, inputs', initRelated, copiedInit, initRead, entered⟩ :=
    snapshot_evaluates dispatchInputs clearedRelated bounded
  have keep {location : Nat} {value : Value} (outside : location ∉ locations.resources.all)
      (found : store.read? location = some value) : copiedStore.read? location = some value := by
    have afterClear := framed.read location value outside found
    exact (retained.read location (List.getElem?_eq_some_iff.mp afterClear).1).trans afterClear
  have callbackFound := keep callbackOutside callbackRead
  have functionRead := OptionalCell.read_success Creation.unavailableReason
    ((input_part inputs' (index := 4) rfl).evaluates copiedStore) callbackFound
  have sharedCopied := LinkedSharedStateRel.preserved sharedRelated
    (fun location member _ found => keep (separate location member) found)
  have functionCode := CodeValue.bound (0 + [Value.unit, Value.unit, Value.unit].length + 4)
    (extra ++ ([.unit, .unit, .unit] ++ bundleValues (argumentValues locations callback arguments) :: environment)) function
  have callInputs := inputs'.prepend [function]
  have requestEvaluated : Evaluates (function :: extra ++ ([.unit, .unit, .unit] ++
      bundleValues (argumentValues locations callback arguments) :: environment)) copiedStore
      (CreationImplementation.request initCode (0 + 3 + 4 + 1))
      (requestValue (request arguments input)) copiedStore := by
    refine .pair (.binary ((input_part callInputs (index := 5) rfl).evaluates copiedStore) .word rfl) ?_
    refine .pair ((input_part callInputs (index := 7) rfl).evaluates copiedStore) ?_
    refine .pair ((input_part callInputs (index := 8) rfl).evaluates copiedStore) ?_
    refine .pair ((input_part callInputs (index := 9) rfl).evaluates copiedStore) ?_
    refine .pair (.binary ((input_part callInputs (index := 6) rfl).evaluates copiedStore) .word rfl) ?_
    refine .pair ((input_part callInputs (index := 10) rfl).evaluates copiedStore) ?_
    exact .pair (.loadCell ((initRelated.prepend [function]).evaluates copiedStore) initRead)
      ((input_part callInputs (index := 12) rfl).evaluates copiedStore)
  obtain ⟨afterCall, called, nextRelated, rewrites⟩ := handler.apply_admitted sharedCopied
    (admitting input copiedInit) (functionCode.evaluates copiedStore) requestEvaluated
  have localSeparate : ∀ location ∈ [sharedLocations.world, sharedLocations.balances],
      location ∉ locations.resources.all := by
    intro location member
    apply separate
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> simp [AccountCallCorrespondence.SharedLocations.all]
  have afterRelated := state_rewritten (state_retained clearedRelated retained) rewrites localSeparate
  refine ⟨afterCall, .letE packed ?_, afterRelated, nextRelated, ?_, ?_⟩
  · apply LanguageResult.bind_success .word touched
    apply clear_evaluates (inputs.prepend [.unit]) inputRelated
    apply Evaluates.ifFalse (.binary ((input_part dispatchInputs (index := 6) rfl).evaluates _) .word
      (by simp [BinaryOp.apply, Creation.depthLimit, allowed]))
    apply entered
    apply LanguageResult.bind_success .word functionRead
    exact LanguageResult.bind_failure .word called
  · exact Nat.le_trans (Nat.le_trans framed.length retained.length_le) rewrites.length_le
  · intro location value outside unshared found
    exact rewrites.read location value unshared (keep outside found)

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
/-- The transport preserves the variable renaming of the outer lowering. -/
theorem invoke_rename (memoryReference sizeReference returnDataReference returnSizeReference
    callbackReference creatorAddress depth transferredValue saltValue isCreate2 suppliedGas
    offset length : Core.Expr) (mapping : Renaming) :
    (Creation.invoke memoryReference sizeReference returnDataReference returnSizeReference
      callbackReference creatorAddress depth transferredValue saltValue isCreate2 suppliedGas offset length).rename mapping =
    Creation.invoke (memoryReference.rename mapping) (sizeReference.rename mapping)
      (returnDataReference.rename mapping) (returnSizeReference.rename mapping) (callbackReference.rename mapping)
      (creatorAddress.rename mapping) (depth.rename mapping) (transferredValue.rename mapping)
      (saltValue.rename mapping) (isCreate2.rename mapping) (suppliedGas.rename mapping)
      (offset.rename mapping) (length.rename mapping) := by
  rw [CreationImplementation.invoke_eq, CreationImplementation.invoke_eq]
  simp only [bundle, Core.Expr.rename]
  congr 1
  simp [CreationImplementation.invokeCode, CreationImplementation.dispatch, CreationImplementation.finish,
    CreationImplementation.request, CreationImplementation.input, CodeBuilder.bind, CodeBuilder.bindResult,
    CodeBuilder.store, CodeBuilder.load, CodeBuilder.allocate, CodeBuilder.empty, CodeBuilder.choose,
    CodeBuilder.binary, CodeBuilder.success, CodeBuilder.number, CodeBuilder.constant, CodeBuilder.part,
    CodeBuilder.apply, CodeBuilder.packet, CodeBuilder.address, MemoryCopyCorrespondence.copyPackedFrom_rename,
    Memory.touch, Memory.packet, Memory.field, Memory.number, Memory.add, Creation.responseField, projectArgument, bundle,
    LanguageResult.bind, LanguageResult.success, LanguageResult.failure,
    OptionalCell.read, WordMapping.empty, Core.Expr.rename, Core.Renaming.lift]
  all_goals rfl

end Solcore.Frontend.RustHull.CreationCorrespondence
end
