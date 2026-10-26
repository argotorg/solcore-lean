import Solcore.Frontend.RustHull.AccountRuntime

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
