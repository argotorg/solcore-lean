import Solcore.Frontend.RustHull.LoweringSupport
import Solcore.Frontend.RustHull.Keccak

/-! Contract address derivation and CREATE frame transport on ordinary Core.
The callback controls account nonce, collision checks, constructor selection,
deployment and rollback. This module preserves init bytes and return data. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.Creation
open Core

/-- Creator, value, salt, CREATE2 flag, child depth, forwarded gas, packed init
bytes and init byte length. The creator uses its low 160 bits. -/
def requestType : Core.Ty := bundleType
  [.word, .word, .word, .bool, .word, .word, WordMapping.type, .word]

/-- Created address or zero, complete revert data, and its byte length. The
callback returns empty data on successful creation or exceptional failure. -/
def responseType : Core.Ty := bundleType [.word, WordMapping.type, .word]
def callbackType : Core.Ty := .function requestType (LanguageResult.resultType responseType)
def callbackReferenceType : Core.Ty := OptionalCell.referenceType callbackType
def unavailableReason : Word := Word.ofNatModulo 7
def depthLimit : Nat := 1024
def requestField (index : Nat) (value : Core.Expr) : Core.Expr := projectArgument index 8 value
def responseField (index : Nat) (value : Core.Expr) : Core.Expr := projectArgument index 3 value
def response (address mapping length : Core.Expr) : Core.Expr := bundle [address, mapping, length]

private abbrev Code := Nat → Core.Expr
private def number (value : Nat) : Code := fun _ => .word (Word.ofNatModulo value)
private def part (index count : Nat) : Code := fun depth => projectArgument index count (.var depth)
private def bind (value : Code) (body : Code → Code) : Code := fun depth =>
  .letE (value depth) (body (fun here => .var (here - depth - 1)) (depth + 1))
private def bindResult (value : Code) (body : Code → Code) : Code := fun depth =>
  LanguageResult.bind .word (value depth)
    (body (fun here => .var (here - depth - 1)) (depth + 1))
private def success (value : Code) : Code := fun depth => LanguageResult.success (value depth)
private def binary (operation : BinaryOp) (left right : Code) : Code := fun depth =>
  .binary operation (left depth) (right depth)
private def choose (condition yes no : Code) : Code :=
  fun depth => .ifE (condition depth) (yes depth) (no depth)
private def load (reference : Code) : Code := fun depth => .loadCell (reference depth)
private def store (reference value : Code) : Code :=
  fun depth => .storeCell (reference depth) (value depth)
private def allocate (type : Core.Ty) (value : Code) : Code :=
  fun depth => .newCell type (value depth)
private def empty : Code := fun _ => WordMapping.empty
private def maskedAddress (value : Code) : Code := binary .wordAnd value (number (2 ^ 160 - 1))
private def writeWord (memory size offset value : Code) : Code := fun depth =>
  Memory.mstore (memory depth) (size depth) (offset depth) (value depth)
private def writeByte (memory size offset value : Code) : Code := fun depth =>
  Memory.mstore8 (memory depth) (size depth) (offset depth) (value depth)
private def hash (memory size offset length : Code) : Code := fun depth =>
  Keccak.hash (memory depth) (size depth) (offset depth) (length depth)
private def scratch (body : Code → Code → Code) : Code :=
  bind (allocate WordMapping.type empty) fun memory =>
  bind (allocate .word (number 0)) fun size => body memory size

private def createAddressCode : Code :=
  let creator := part 0 2
  let nonce := part 1 2
  bind (binary .wordSub (number 32)
    (binary .wordDiv (fun depth => .unary .wordClz (nonce depth)) (number 8))) fun byteCount =>
  bind (choose (binary .wordGt nonce (number 127))
    (binary .wordAdd byteCount (number 1)) (number 1)) fun encodedLength =>
  scratch fun memory size =>
  bindResult (writeByte memory size (number 0) (binary .wordAdd (number 213) encodedLength)) fun _ =>
  bindResult (writeByte memory size (number 1) (number 148)) fun _ =>
  bindResult (writeWord memory size (number 2)
    (binary .wordShl (maskedAddress creator) (number 96))) fun _ =>
  let finish := bindResult (hash memory size (number 0)
    (binary .wordAdd (number 22) encodedLength)) fun digest => success (maskedAddress digest)
  choose (binary .wordEq nonce (number 0))
    (bindResult (writeByte memory size (number 22) (number 128)) fun _ => finish)
    (choose (binary .wordGt nonce (number 127))
      (bindResult (writeByte memory size (number 22) (binary .wordAdd (number 128) byteCount)) fun _ =>
        bindResult (writeWord memory size (number 23)
          (binary .wordShl nonce (binary .wordMul
            (binary .wordSub (number 32) byteCount) (number 8)))) fun _ => finish)
      (bindResult (writeByte memory size (number 22) nonce) fun _ => finish))

/-- Exact RLP of the 20-byte address and minimally encoded nonnegative nonce.
The runtime checks its account nonce limit separately before incrementing it. -/
def createAddress (creator nonce : Core.Expr) : Core.Expr :=
  .letE (.pair creator nonce) (createAddressCode 0)

private def create2AddressCode : Code :=
  bindResult (hash (part 0 6) (part 1 6) (part 4 6) (part 5 6)) fun initHash =>
  scratch fun memory size =>
  bindResult (writeByte memory size (number 0) (number 255)) fun _ =>
  bindResult (writeWord memory size (number 1)
    (binary .wordShl (maskedAddress (part 2 6)) (number 96))) fun _ =>
  bindResult (writeWord memory size (number 21) (part 3 6)) fun _ =>
  bindResult (writeWord memory size (number 53) initHash) fun _ =>
  bindResult (hash memory size (number 0) (number 85)) fun digest => success (maskedAddress digest)

/-- Hash the exact init byte range and the 85-byte CREATE2 preimage. Scratch
memory is separate from the caller; only its input range expands caller memory. -/
def create2Address (memoryReference sizeReference creator salt offset length : Core.Expr) : Core.Expr :=
  .letE (bundle [memoryReference, sizeReference, creator, salt, offset, length]) (create2AddressCode 0)

private def memory : Code := part 0 13
private def memorySize : Code := part 1 13
private def returnData : Code := part 2 13
private def returnSize : Code := part 3 13
private def callback : Code := part 4 13
private def creator : Code := part 5 13
private def currentDepth : Code := part 6 13
private def value : Code := part 7 13
private def salt : Code := part 8 13
private def create2 : Code := part 9 13
private def gas : Code := part 10 13
private def inputOffset : Code := part 11 13
private def inputLength : Code := part 12 13

private def finish (result : Code) : Code :=
  bind (store returnData (fun depth => responseField 1 (result depth))) fun _ =>
  bind (store returnSize (fun depth => responseField 2 (result depth))) fun _ =>
  success (fun depth => responseField 0 (result depth))

private def dispatch : Code :=
  bind (load memory) fun snapshot =>
  bind (allocate WordMapping.type empty) fun input =>
  bind (allocate .word (number 0)) fun size =>
  bindResult (fun depth => Memory.copyPackedFrom (input depth) (size depth) (number 0 depth)
    (snapshot depth) (inputOffset depth) (inputLength depth)) fun _ =>
  bindResult (fun depth => OptionalCell.read callbackType (callback depth) unavailableReason) fun function =>
  bindResult (fun depth => .apply (function depth) (bundle [maskedAddress creator depth,
    value depth, salt depth, create2 depth, binary .wordAdd currentDepth (number 1) depth,
    gas depth, load input depth, inputLength depth])) finish

private def invokeCode : Code :=
  bindResult (fun depth => Memory.touch (memorySize depth) (inputOffset depth) (inputLength depth)) fun _ =>
  bind (store returnData empty) fun _ =>
  bind (store returnSize (number 0)) fun _ =>
  choose (binary .wordGt currentDepth (number (depthLimit - 1))) (success (number 0)) dispatch

/-- Evaluate inputs once, touch the input range, clear prior return data and
copy init bytes to a private map starting at zero. A depth refusal returns zero.
The callback's full revert bytes become return data; caller memory is not used
as an output buffer. The four mutable frame cells must be distinct. -/
def invoke (memoryReference sizeReference returnDataReference returnSizeReference callbackReference
    creatorAddress depth transferredValue saltValue isCreate2 suppliedGas offset length : Core.Expr) : Core.Expr :=
  .letE (bundle [memoryReference, sizeReference, returnDataReference, returnSizeReference,
    callbackReference, creatorAddress, depth, transferredValue, saltValue, isCreate2,
    suppliedGas, offset, length]) (invokeCode 0)

end Solcore.Frontend.RustHull.Creation
