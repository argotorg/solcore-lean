import Solcore.Frontend.RustHull.LoweringSupport
import Solcore.Frontend.RustHull.Memory

/-! CALL/STATICCALL frame transport through an ordinary Core closure. Account
dispatch, transfer, shared state checkpoints and static-write restrictions are
the callback's responsibility. Caller memory and return data stay frame-local.
Depth follows the execution specification's zero-based message depth:
https://ethereum.github.io/execution-specs/src/ethereum/forks/cancun/vm/instructions/system.py.html
-/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.Calls
open Core

/-- target, caller, value, static flag, child depth, forwarded gas, packed
calldata, calldata size. Addresses are reduced to their low 160 bits. -/
def requestType : Core.Ty := bundleType
  [.word, .word, .word, .bool, .word, .word, WordMapping.type, .word]

/-- Success flag, complete packed return data, return-data size. A reverted
child returns false with its revert bytes. An exceptional child returns false
with empty bytes. Unsupported execution uses the outer language failure. -/
def responseType : Core.Ty := bundleType [.bool, WordMapping.type, .word]
def callbackType : Core.Ty := .function requestType (LanguageResult.resultType responseType)
def callbackReferenceType : Core.Ty := OptionalCell.referenceType callbackType
def unavailableReason : Word := Word.ofNatModulo 7
def depthLimit : Nat := 1024
def requestField (index : Nat) (value : Core.Expr) : Core.Expr := projectArgument index 8 value
def responseField (index : Nat) (value : Core.Expr) : Core.Expr := projectArgument index 3 value
def response (success mapping length : Core.Expr) : Core.Expr := bundle [success, mapping, length]

abbrev Code := Nat → Core.Expr
def number (value : Nat) : Code := fun _ => .word (Word.ofNatModulo value)
def arg : Code := fun depth => .var depth
def part (index : Nat) : Code := fun depth => projectArgument index 15 (arg depth)
def bind (value : Code) (body : Code → Code) : Code := fun depth =>
  .letE (value depth) (body (fun here => .var (here - depth - 1)) (depth + 1))
def bindResult (value : Code) (body : Code → Code) : Code := fun depth =>
  LanguageResult.bind .word (value depth)
    (body (fun here => .var (here - depth - 1)) (depth + 1))
def success (value : Code) : Code := fun depth => LanguageResult.success (value depth)
def binary (op : BinaryOp) (left right : Code) : Code := fun depth =>
  .binary op (left depth) (right depth)
def choose (test yes no : Code) : Code := fun depth => .ifE (test depth) (yes depth) (no depth)
def load (reference : Code) : Code := fun depth => .loadCell (reference depth)
def store (reference value : Code) : Code := fun depth => .storeCell (reference depth) (value depth)
def allocate (type : Core.Ty) (value : Code) : Code := fun depth => .newCell type (value depth)
def empty : Code := fun _ => WordMapping.empty
def copy (memory size destination mapping source length : Code) : Code := fun depth =>
  Memory.copyPackedFrom (memory depth) (size depth) (destination depth)
    (mapping depth) (source depth) (length depth)
def touch (size offset length : Code) : Code := fun depth =>
  Memory.touch (size depth) (offset depth) (length depth)
def memory : Code := part 0
def memorySize : Code := part 1
def returnData : Code := part 2
def returnSize : Code := part 3
def callback : Code := part 4
def caller : Code := part 5
def depth : Code := part 6
def childStatic : Code := part 7
def gas : Code := part 8
def target : Code := part 9
def value : Code := part 10
def inputOffset : Code := part 11
def inputLength : Code := part 12
def outputOffset : Code := part 13
def outputLength : Code := part 14

def finish (result : Code) : Code :=
  let returned : Code := fun depth => responseField 1 (result depth)
  let length : Code := fun depth => responseField 2 (result depth)
  bind (store returnData returned) fun _ =>
  bind (store returnSize length) fun _ =>
  bindResult (copy memory memorySize outputOffset returned (number 0)
    (choose (binary .wordGt length outputLength) outputLength length)) fun _ =>
  success (choose (fun depth => responseField 0 (result depth)) (number 1) (number 0))

def dispatch : Code :=
  bind (load memory) fun snapshot =>
  bind (allocate WordMapping.type empty) fun input =>
  bind (allocate .word (number 0)) fun inputSize =>
  bindResult (copy input inputSize (number 0) snapshot inputOffset inputLength) fun _ =>
  bindResult (fun depth => OptionalCell.read callbackType (callback depth) unavailableReason) fun function =>
  bindResult (fun depth => .apply (function depth) (bundle [
    binary .wordAnd target (number (2 ^ 160 - 1)) depth,
    binary .wordAnd caller (number (2 ^ 160 - 1)) depth,
    value depth, childStatic depth, binary .wordAdd Calls.depth (number 1) depth,
    gas depth, load input depth, inputLength depth])) finish

def callCode : Code :=
  bindResult (touch memorySize inputOffset inputLength) fun _ =>
  bindResult (touch memorySize outputOffset outputLength) fun _ =>
  bind (store returnData empty) fun _ =>
  bind (store returnSize (number 0)) fun _ =>
  choose (binary .wordGt depth (number (depthLimit - 1))) (success (number 0)) dispatch

/-- Evaluate every argument once. Both memory ranges are checked before a call
starts; return data is then cleared even when depth prevents dispatch. Depth
zero is the outer frame: child depth 1024 is permitted and depth 1025 is refused.
The four mutable frame cells must be distinct. The callback receives copied
calldata starting at byte zero, independently of later caller memory writes. -/
def invoke (memoryReference sizeReference returnDataReference returnSizeReference callbackReference
    callerAddress currentDepth staticFlag suppliedGas address transferredValue
    sourceOffset sourceLength destinationOffset destinationLength : Core.Expr) : Core.Expr :=
  .letE (bundle [memoryReference, sizeReference, returnDataReference, returnSizeReference,
    callbackReference, callerAddress, currentDepth, staticFlag, suppliedGas, address,
    transferredValue, sourceOffset, sourceLength, destinationOffset, destinationLength]) (callCode 0)

end Solcore.Frontend.RustHull.Calls
