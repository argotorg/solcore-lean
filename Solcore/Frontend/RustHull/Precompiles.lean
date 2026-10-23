import Solcore.Frontend.RustHull.Secp256k1
import Solcore.Frontend.RustHull.Sha256
import Solcore.Frontend.RustHull.Ripemd160
import Solcore.Frontend.RustHull.P256

/-! Ethereum precompiles 1–4 and EIP-7951 P256VERIFY at 0x100 expressed entirely
in existing Core operations.
The caller supplies distinct cells for memory, memory size, return data and
return-data size. Gas is the amount forwarded to the precompile; instruction
and caller memory-expansion charging belongs to the surrounding runtime.

Input padding, return lengths and costs follow go-ethereum's implementations:
https://github.com/ethereum/go-ethereum/blob/master/core/vm/contracts.go
https://github.com/ethereum/go-ethereum/blob/master/params/protocol_params.go
-/
set_option autoImplicit false

namespace Solcore.Frontend.RustHull.Precompiles
open Core

/-- Calls outside the implemented precompile set need account dispatch. -/
def unsupportedTargetReason : Word := Word.ofNatModulo 7

private def packet : List Expr → Expr
  | [] => .unit
  | [value] => value
  | value :: rest => .pair value (packet rest)
private def field (index : Nat) : Nat → Expr → Expr
  | 0, _ => .unit
  | 1, value => value
  | count + 2, value => if index = 0 then .first value
      else field (index - 1) (count + 1) (.second value)

private abbrev Code := Nat → Expr
private def number (value : Nat) : Code := fun _ => .word (Word.ofNatModulo value)
private def integer (value : Nat) : Code := fun _ => .integer (Int.ofNat value)
private def arg : Code := fun depth => .var depth
private def part (index count : Nat) (value : Code) : Code := fun depth => field index count (value depth)
private def bind (value : Code) (body : Code → Code) : Code := fun depth =>
  .letE (value depth) (body (fun here => .var (here - depth - 1)) (depth + 1))
private def bindResult (value : Code) (body : Code → Code) : Code := fun depth =>
  LanguageResult.bind .word (value depth)
    (body (fun here => .var (here - depth - 1)) (depth + 1))
private def success (value : Code) : Code := fun depth => LanguageResult.success (value depth)
private def unary (op : UnaryOp) (value : Code) : Code := fun depth => .unary op (value depth)
private def binary (op : BinaryOp) (a b : Code) : Code := fun depth => .binary op (a depth) (b depth)
private def choose (test yes no : Code) : Code := fun depth => .ifE (test depth) (yes depth) (no depth)
private def matchOption (value : Code) (none : Code) (some : Code → Code) : Code := fun depth =>
  .caseE (value depth) (none (depth + 1))
    (some (fun here => .var (here - depth - 1)) (depth + 1))
private def load (reference : Code) : Code := fun depth => .loadCell (reference depth)
private def store (reference value : Code) : Code := fun depth => .storeCell (reference depth) (value depth)
private def allocate (type : Ty) (value : Code) : Code := fun depth => .newCell type (value depth)
private def empty : Code := fun _ => WordMapping.empty
private def touch (size offset length : Code) : Code := fun depth =>
  Memory.touch (size depth) (offset depth) (length depth)
private def copy (memory size destination mapping source length : Code) : Code := fun depth =>
  Memory.copyPackedFrom (memory depth) (size depth) (destination depth)
    (mapping depth) (source depth) (length depth)

private def memory : Code := part 0 10 arg
private def memorySize : Code := part 1 10 arg
private def returnData : Code := part 2 10 arg
private def returnSize : Code := part 3 10 arg
private def gas : Code := part 4 10 arg
private def target : Code := part 5 10 arg
private def inputOffset : Code := part 6 10 arg
private def inputLength : Code := part 7 10 arg
private def outputOffset : Code := part 8 10 arg
private def outputLength : Code := part 9 10 arg

/-- Cost comparison uses unbounded Core integers, including the multiplication.
RIPEMD's cost can exceed a Word even for a representable memory range. -/
private def enoughGas (base perWord : Nat) : Code :=
  unary .boolNot (binary .integerLt (unary .wordToInteger gas)
    (binary .integerAdd (integer base)
      (binary .integerMul (integer perWord)
        (binary .integerDiv
          (binary .integerAdd (unary .wordToInteger inputLength) (integer 31)) (integer 32)))))

private def finish (mapping length : Code) : Code :=
  bind mapping fun snapshot =>
  bind (store returnData snapshot) fun _ =>
  bind (store returnSize length) fun _ =>
  bindResult (copy memory memorySize outputOffset snapshot (number 0)
    (choose (binary .wordGt length outputLength) outputLength length)) fun _ =>
  success (number 1)

private def finishWord (value : Code) : Code :=
  bindResult (fun depth => WordMapping.insert WordMapping.empty (number 0 depth) (value depth)) fun mapping =>
  finish mapping (number 32)

/-- The supplied length, not the caller memory contents beyond that length,
determines the zero padding for each recovery argument. -/
private def inputWord (snapshot : Code) (start : Nat) : Code :=
  choose (binary .wordGt inputLength (number start))
    (bindResult (fun depth => Memory.readMemoryWord (snapshot depth)
      (binary .wordAdd inputOffset (number start) depth)) fun value =>
      bind (binary .wordSub inputLength (number start)) fun remaining =>
      success (choose (binary .wordGt remaining (number 31)) value
        (binary .wordAnd value
          (binary .wordShl (number (wordModulus - 1))
            (binary .wordMul (binary .wordSub (number 32) remaining) (number 8))))))
    (success (number 0))

private def recover (snapshot : Code) : Code :=
  bindResult (inputWord snapshot 0) fun hash =>
  bindResult (inputWord snapshot 32) fun v =>
  bindResult (inputWord snapshot 64) fun r =>
  bindResult (inputWord snapshot 96) fun s =>
  bindResult (fun depth => Secp256k1.recover (hash depth) (v depth) (r depth) (s depth)) fun recovered =>
  matchOption recovered (success (number 1)) finishWord

private def verifyP256 (snapshot : Code) : Code :=
  choose (binary .wordEq inputLength (number 160))
    (bindResult (inputWord snapshot 0) fun hash =>
     bindResult (inputWord snapshot 32) fun r =>
     bindResult (inputWord snapshot 64) fun s =>
     bindResult (inputWord snapshot 96) fun x =>
     bindResult (inputWord snapshot 128) fun y =>
     bindResult (fun depth => P256.verify (hash depth) (r depth) (s depth) (x depth) (y depth)) fun valid =>
     choose valid (finishWord (number 1)) (success (number 1)))
    (success (number 1))

private def hash (operation : Expr → Expr → Expr → Expr → Expr) (snapshot : Code) : Code :=
  bind (allocate WordMapping.type snapshot) fun sourceMemory =>
  bind (allocate .word (number 0)) fun sourceSize =>
  bindResult (fun depth => operation (sourceMemory depth) (sourceSize depth)
    (inputOffset depth) (inputLength depth)) finishWord

private def identity (snapshot : Code) : Code :=
  bind (allocate WordMapping.type empty) fun resultMemory =>
  bind (allocate .word (number 0)) fun resultSize =>
  bindResult (copy resultMemory resultSize (number 0) snapshot inputOffset inputLength) fun _ =>
  finish (load resultMemory) inputLength

private def dispatch (snapshot : Code) : Code :=
  bind (binary .wordAnd target (number (2 ^ 160 - 1))) fun address =>
  choose (binary .wordEq address (number 1))
    (choose (enoughGas 3000 0) (recover snapshot) (success (number 0))) <|
  choose (binary .wordEq address (number 2))
    (choose (enoughGas 60 12) (hash Sha256.hash snapshot) (success (number 0))) <|
  choose (binary .wordEq address (number 3))
    (choose (enoughGas 600 120) (hash Ripemd160.hash snapshot) (success (number 0))) <|
  choose (binary .wordEq address (number 4))
    (choose (enoughGas 15 3) (identity snapshot) (success (number 0))) <|
  choose (binary .wordEq address (number 0x100))
    (choose (enoughGas 6900 0) (verifyP256 snapshot) (success (number 0)))
    (fun _ => LanguageResult.failure .word (.word unsupportedTargetReason))

private def callCode : Code :=
  bindResult (touch memorySize inputOffset inputLength) fun _ =>
  bindResult (touch memorySize outputOffset outputLength) fun _ =>
  bind (load memory) fun snapshot =>
  bind (store returnData empty) fun _ =>
  bind (store returnSize (number 0)) fun _ =>
  dispatch snapshot

/-- Call a supported precompile, evaluating every argument once. The retained
input snapshot permits overlapping input/output ranges. Complete packed return
data is recorded independently of the requested output length. Invalid recovery
returns success with no bytes; insufficient forwarded gas returns zero and no
bytes. Neither case overwrites the caller's output bytes. -/
def staticCall (memoryReference sizeReference returnDataReference returnSizeReference
    suppliedGas address sourceOffset sourceLength destinationOffset destinationLength : Expr) : Expr :=
  .letE (packet [memoryReference, sizeReference, returnDataReference, returnSizeReference,
    suppliedGas, address, sourceOffset, sourceLength, destinationOffset, destinationLength]) (callCode 0)

end Solcore.Frontend.RustHull.Precompiles
