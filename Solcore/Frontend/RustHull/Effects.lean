import Solcore.Frontend.RustHull.LoweringSupport
import Solcore.Frontend.RustHull.Memory
import Solcore.Frontend.RustHull.Keccak
import Solcore.Frontend.RustHull.Precompiles
import Solcore.Frontend.RustHull.Logs
import Solcore.Frontend.RustHull.Calls

/-! EVM effects expressed with ordinary Core cells. Message calls use an
explicit callback installed by the contract runner.
Termination records a byte range and propagates through the language-result
envelope, so no later Hull or Yul instruction executes. -/
set_option autoImplicit false

namespace Solcore.Frontend.RustHull.Effects

def reservedPrefix : String := "$lean$evm$"
def slotName (name : String) : String := reservedPrefix ++ name

def slots : List (String × Core.Ty) :=
  [("memory", Core.WordMapping.type), ("memorySize", .word),
   ("calldata", Core.WordMapping.type), ("calldataSize", .word),
   ("storage", Core.WordMapping.type), ("transient", Core.WordMapping.type),
   ("callvalue", .word), ("caller", .word), ("address", .word),
   ("returnData", Core.WordMapping.type), ("returnDataSize", .word),
   ("logs", Core.WordMapping.type), ("logSize", .word),
   ("balances", Core.WordMapping.type), ("isStatic", .bool), ("callDepth", .word),
   ("callHandler", Core.OptionalCell.cellType Calls.callbackType),
   ("availableGas", .sum .unit .word),
   ("exit", .word), ("returnOffset", .word), ("returnSize", .word)]

/-- Installed only when the caller supplies a concrete linked code image. -/
def codeSlots : List (String × Core.Ty) :=
  [("code", Core.WordMapping.type), ("codeSize", .word)]

def reference (scope : Scope) (name : String) (type : Core.Ty) : LowerM Core.Expr := do
  let (binding, index) ← scope.lookup (slotName name)
  expectType type binding.type
  pure (.var index)

def supports (name : String) : Bool := name ∈
  ["mload", "mstore", "mstore8", "msize", "calldataload", "calldatasize",
   "callvalue", "caller", "address", "sload", "sstore", "tload", "tstore",
   "memoryguard", "mcopy", "calldatacopy", "keccak256", "codesize", "codecopy", "datacopy",
   "gas", "returndatasize", "returndatacopy", "staticcall", "call", "selfbalance", "balance",
   "log0", "log1", "log2", "log3", "log4",
   "return", "revert", "stop", "invalid"]

private def writeMapping (reference key value : Core.Expr) : Core.Expr :=
  .letE reference
    (Core.LanguageResult.bind .unit
      (Core.WordMapping.insert (.loadCell (.var 0)) (key.weakenAt 0) (value.weakenAt 0))
      (Core.LanguageResult.success (.storeCell (.var 1) (.var 0))))

private def terminate (scope : Scope) (kind : Nat) (offset size : Core.Expr) : LowerM Core.Expr := do
  let memorySize ← reference scope "memorySize" .word
  let exit ← reference scope "exit" .word
  let returnOffset ← reference scope "returnOffset" .word
  let returnSize ← reference scope "returnSize" .word
  let stores : List Core.Expr :=
    [.storeCell returnOffset offset, .storeCell returnSize size,
     .storeCell exit (.word (Core.Word.ofNatModulo kind))]
  let finish : Core.Expr := stores.foldr (fun store next =>
    .letE store (next.weakenAt 0))
      (Core.LanguageResult.failure .unit (.word Core.Word.maximum))
  pure (Core.LocalSequence.discard .unit (Memory.touch memorySize offset size) finish)

private def log (scope : Scope) (count : Nat) (arguments : List Core.Expr) : LowerM Lowered := do
  let offset :: length :: topics := arguments | fail "log requires memory offset and size"
  unless topics.length = count do fail "wrong number of log topics"
  let append := Logs.append
    (← reference scope "memory" Core.WordMapping.type) (← reference scope "memorySize" .word)
    (← reference scope "logs" Core.WordMapping.type) (← reference scope "logSize" .word)
    (.loadCell (← reference scope "address" .word)) topics offset length
  pure ⟨.unit, .ifE (.loadCell (← reference scope "isStatic" .bool))
    (← terminate scope 3 (.word Core.Word.zero) (.word Core.Word.zero)) append⟩

private def call (scope : Scope) (staticCall : Bool)
    (gas target value inputOffset inputLength outputOffset outputLength : Core.Expr) : LowerM Lowered := do
  let isStatic := Core.Expr.loadCell (← reference scope "isStatic" .bool)
  let zeroValue := Core.Expr.binary .wordEq value (.word Core.Word.zero)
  let suppliedGas := if staticCall then gas else Core.Expr.ifE zeroValue gas
    (.binary .wordAdd gas (.word (Core.Word.ofNatModulo 2300)))
  let invoke := Calls.invoke
    (← reference scope "memory" Core.WordMapping.type) (← reference scope "memorySize" .word)
    (← reference scope "returnData" Core.WordMapping.type) (← reference scope "returnDataSize" .word)
    (← reference scope "callHandler" (Core.OptionalCell.cellType Calls.callbackType))
    (.loadCell (← reference scope "address" .word))
    (.loadCell (← reference scope "callDepth" .word))
    (if staticCall then .bool true else isStatic)
    suppliedGas target value inputOffset inputLength outputOffset outputLength
  if staticCall then pure ⟨.word, invoke⟩
  else
    let invalid ← terminate scope 3 (.word Core.Word.zero) (.word Core.Word.zero)
    let invalidWord := Core.LanguageResult.bind .word invalid
      (Core.LanguageResult.success (.word Core.Word.zero))
    let withStipend := Core.Expr.ifE zeroValue invoke
      (.ifE (.binary .wordGt gas (.word (Core.Word.ofNatModulo (Core.wordModulus - 2301))))
        (Core.LanguageResult.failure .word (.word (Core.Word.ofNatModulo 13))) invoke)
    pure ⟨.word, .ifE isStatic (.ifE zeroValue invoke invalidWord) withStipend⟩

/-- Arguments are already evaluated word values in `scope`; the caller owns
the Hull or Yul argument order and failure propagation. -/
def lowerBuiltin (scope : Scope) (name : String) (arguments : List Core.Expr) : LowerM Lowered := do
  let result ← match name, arguments with
    | "memoryguard", [value] => pure ⟨.word, Core.LanguageResult.success value⟩
    | "mload", [offset] => pure ⟨.word, Memory.mload
        (← reference scope "memory" Core.WordMapping.type)
        (← reference scope "memorySize" .word) offset⟩
    | "mstore", [offset, value] => pure ⟨.unit, Memory.mstore
        (← reference scope "memory" Core.WordMapping.type)
        (← reference scope "memorySize" .word) offset value⟩
    | "mstore8", [offset, value] => pure ⟨.unit, Memory.mstore8
        (← reference scope "memory" Core.WordMapping.type)
        (← reference scope "memorySize" .word) offset value⟩
    | "mcopy", [destination, source, length] => pure ⟨.unit, Memory.mcopy
        (← reference scope "memory" Core.WordMapping.type)
        (← reference scope "memorySize" .word) destination source length⟩
    | "keccak256", [offset, length] => pure ⟨.word, Keccak.hash
        (← reference scope "memory" Core.WordMapping.type)
        (← reference scope "memorySize" .word) offset length⟩
    | "calldatacopy", [destination, source, length] => pure ⟨.unit, Memory.copyPackedFrom
        (← reference scope "memory" Core.WordMapping.type)
        (← reference scope "memorySize" .word) destination
        (.loadCell (← reference scope "calldata" Core.WordMapping.type)) source length⟩
    | "codecopy", [destination, source, length]
    | "datacopy", [destination, source, length] => pure ⟨.unit, Memory.copyPackedFrom
        (← reference scope "memory" Core.WordMapping.type)
        (← reference scope "memorySize" .word) destination
        (.loadCell (← reference scope "code" Core.WordMapping.type)) source length⟩
    | "codesize", [] => pure ⟨.word, Core.LanguageResult.success
        (.loadCell (← reference scope "codeSize" .word))⟩
    | "gas", [] => pure ⟨.word, .caseE
        (.loadCell (← reference scope "availableGas" (.sum .unit .word)))
        (Core.LanguageResult.failure .word (.word (Core.Word.ofNatModulo 9)))
        (Core.LanguageResult.success (.var 0))⟩
    | "staticcall", [gas, target, inputOffset, inputLength, outputOffset, outputLength] =>
        call scope true gas target (.word Core.Word.zero) inputOffset inputLength outputOffset outputLength
    | "call", [gas, target, value, inputOffset, inputLength, outputOffset, outputLength] =>
        call scope false gas target value inputOffset inputLength outputOffset outputLength
    | "selfbalance", [] => pure ⟨.word, Core.WordMapping.lookup
        (.loadCell (← reference scope "balances" Core.WordMapping.type))
        (.loadCell (← reference scope "address" .word))⟩
    | "balance", [address] => pure ⟨.word, Core.WordMapping.lookup
        (.loadCell (← reference scope "balances" Core.WordMapping.type))
        (.binary .wordAnd address (.word (Core.Word.ofNatModulo (2 ^ 160 - 1))))⟩
    | "log0", arguments => log scope 0 arguments
    | "log1", arguments => log scope 1 arguments
    | "log2", arguments => log scope 2 arguments
    | "log3", arguments => log scope 3 arguments
    | "log4", arguments => log scope 4 arguments
    | "returndatasize", [] => pure ⟨.word, Core.LanguageResult.success
        (.loadCell (← reference scope "returnDataSize" .word))⟩
    | "returndatacopy", [destination, source, length] => do
        let size := Core.Expr.loadCell (← reference scope "returnDataSize" .word)
        let invalid ← terminate scope 3 (.word Core.Word.zero) (.word Core.Word.zero)
        let copy := Memory.copyPackedFrom
          (← reference scope "memory" Core.WordMapping.type)
          (← reference scope "memorySize" .word) destination
          (.loadCell (← reference scope "returnData" Core.WordMapping.type)) source length
        pure ⟨.unit, .ifE (.binary .wordGt source size) invalid
          (.ifE (.binary .wordGt length (.binary .wordSub size source)) invalid copy)⟩
    | "msize", [] => pure ⟨.word, Core.LanguageResult.success
        (.loadCell (← reference scope "memorySize" .word))⟩
    | "calldataload", [offset] => pure ⟨.word, Memory.readMemoryWord
        (.loadCell (← reference scope "calldata" Core.WordMapping.type)) offset⟩
    | "calldatasize", [] => pure ⟨.word, Core.LanguageResult.success
        (.loadCell (← reference scope "calldataSize" .word))⟩
    | "callvalue", [] | "caller", [] | "address", [] => pure ⟨.word,
        Core.LanguageResult.success (.loadCell (← reference scope name .word))⟩
    | "sload", [key] | "tload", [key] => pure ⟨.word, Core.WordMapping.lookup
        (.loadCell (← reference scope (if name = "sload" then "storage" else "transient") Core.WordMapping.type)) key⟩
    | "sstore", [key, value] | "tstore", [key, value] => pure ⟨.unit,
        .ifE (.loadCell (← reference scope "isStatic" .bool))
          (← terminate scope 3 (.word Core.Word.zero) (.word Core.Word.zero))
          (writeMapping (← reference scope (if name = "sstore" then "storage" else "transient") Core.WordMapping.type) key value)⟩
    | "return", [offset, size] => pure ⟨.unit, ← terminate scope 1 offset size⟩
    | "revert", [offset, size] => pure ⟨.unit, ← terminate scope 2 offset size⟩
    | "stop", [] => pure ⟨.unit, ← terminate scope 1 (.word Core.Word.zero) (.word Core.Word.zero)⟩
    | "invalid", [] => pure ⟨.unit, ← terminate scope 3 (.word Core.Word.zero) (.word Core.Word.zero)⟩
    | _, _ => fail s!"unsupported EVM operation or wrong arity: {name}"
  pure result

/-- Hull's explicit revert writes one short UTF-8 message at byte zero, as in
the pinned Yul backend. Oversized messages are diagnosed rather than truncated. -/
def revertMessage (scope : Scope) (message : String) : LowerM Core.Expr := do
  let bytes := message.toUTF8
  if bytes.size > 32 then fail "Hull revert message exceeds one EVM word"
  else
    let leading := bytes.data.foldl (fun value byte => value * 256 + byte.toNat) 0
    let value := Core.Word.ofNatModulo (leading * 256 ^ (32 - bytes.size))
    let write ← lowerBuiltin scope "mstore" [.word Core.Word.zero, .word value]
    let exit ← lowerBuiltin scope "revert" [.word Core.Word.zero, .word (Core.Word.ofNatModulo bytes.size)]
    pure (Core.LocalSequence.discard .unit write.expression exit.expression)

end Solcore.Frontend.RustHull.Effects
