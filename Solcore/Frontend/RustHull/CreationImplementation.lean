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

/-- The dispatcher after both refusal checks: address derivation, the nonce
increment, the checkpoint, collision checks, init execution and installation.
`args` binds the six dispatcher arguments; the balance and creator record are
the values already read by the checks. -/
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
  let rollback (result : Code) := bind restore fun _ => result
  protect restore <|
  bindResult Creation.responseType (fun depth => AccountState.get (load world depth) (target depth)
    (complete depth)) fun existing =>
  choose (binary .wordGt (part 2 9 existing) (number 0)) refused <|
  choose (binary .wordGt (part 5 9 existing) (number 0)) refused <|
  choose (part 6 9 existing)
    (bindResult Creation.responseType (fun depth => AccountState.put (load world depth) (target depth)
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
        (rollback (response (number 0) (part 1 3 child) (part 2 3 child))))
    (failure Creation.responseType (number 7))

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

/-- The create handler installed by the actual object initializer; its init
selection and runtime installation stay abstract. -/
theorem objectHandlers_create (slots : List (String × Core.Ty)) (count : Nat)
    (images : List (Nat × List UInt8)) (catalog : List AccountRuntime.CodeDefinition)
    (functions : Code) (shared : AccountRuntime.References) (dispatcher creator : Code) :
    ∃ runInit installRuntime : Code → Code → Code,
      (AccountRuntime.objectHandlers slots count images catalog functions shared dispatcher creator).2 =
        lambda Creation.requestType (LanguageResult.resultType Creation.responseType) fun request =>
          CreationRuntime.dispatch (AccountRuntime.reference shared "world")
            (AccountRuntime.reference shared "balances") (AccountRuntime.reference shared "logs")
            (AccountRuntime.reference shared "logSize")
            (load (AccountRuntime.reference shared "worldComplete")) request runInit installRuntime :=
  ⟨_, _, rfl⟩

end Solcore.Frontend.RustHull.CreationImplementation
