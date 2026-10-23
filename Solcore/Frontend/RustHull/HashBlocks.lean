import Solcore.Frontend.RustHull.Memory

/-! Core block streaming shared by SHA-256 and RIPEMD-160. Input stays in packed
memory; the marker, zero padding and 64-bit bit count are generated in Core. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.HashBlocks
open Core

def number (value : Nat) : Expr := .word (Word.ofNatModulo value)
def add (left right : Expr) : Expr := .binary .wordAdd left right
def xor (left right : Expr) : Expr := .binary .wordXor left right
def shift (value : Expr) (distance : Nat) : Expr := .binary .wordShl value (number distance)
def move (expression : Expr) (depth : Nat) : Expr := expression.rename fun index => index + depth
def mask32 (value : Expr) : Expr := .binary .wordAnd value (number (2 ^ 32 - 1))
def sum32 (values : List Expr) : Expr := mask32 (values.foldl add (number 0))
def rotateLeft (value : Expr) (distance : Nat) : Expr :=
  mask32 (.binary .wordOr (shift value distance) (.binary .wordShr value (number (32 - distance))))
def rotateRight (value : Expr) (distance : Nat) : Expr := rotateLeft value (32 - distance)

def packet : List Expr → Expr
  | [] => .unit
  | [value] => value
  | value :: rest => .pair value (packet rest)
def types : List Ty → Ty
  | [] => .unit
  | [type] => type
  | type :: rest => .product type (types rest)
def field (index : Nat) : Nat → Expr → Expr
  | 0, _ => .unit
  | 1, value => value
  | count + 2, value => if index = 0 then .first value
      else field (index - 1) (count + 1) (.second value)

def blockType : Ty := types (List.replicate 16 .word)

structure Algorithm where
  stateType : Ty
  initial : Expr
  compress : Expr → Expr → Expr
  digest : Expr → Expr
  littleEndian : Bool

private def paddedByte (littleEndian : Bool) (mapping offset remaining bits markerUsed : Expr)
    (index : Nat) : Expr :=
  .ifE (.binary .wordGt remaining (number index))
    (Memory.readMemoryByte mapping (add offset (number index)))
    (LanguageResult.success
      (.ifE (.ifE (.binary .wordEq remaining (number index)) (.unary .boolNot markerUsed) (.bool false))
        (number 128)
        (if index < 56 then number 0
          else .ifE (.binary .wordGt (number 56) remaining)
            (.binary .wordByte (number (if littleEndian then 31 - (index - 56) else 24 + (index - 56))) bits)
            (number 0))))

private def readWord (littleEndian : Bool) : Nat → Nat → Expr → Expr → Expr → Expr → Expr → Expr → Expr
  | 0, _, _, _, _, _, _, accumulator => LanguageResult.success accumulator
  | count + 1, index, mapping, offset, remaining, bits, markerUsed, accumulator =>
      LanguageResult.bind .word (paddedByte littleEndian mapping offset remaining bits markerUsed index)
        (readWord littleEndian count (index + 1) (mapping.weakenAt 0) (offset.weakenAt 0)
          (remaining.weakenAt 0) (bits.weakenAt 0) (markerUsed.weakenAt 0)
          (.binary .wordOr (accumulator.weakenAt 0)
            (shift (.var 0) (8 * (if littleEndian then index % 4 else 3 - index % 4)))))

private def readBlock (littleEndian : Bool) (parameters : Expr) : Expr :=
  let computations := (List.range 16).map fun index =>
    let params := move parameters index
    readWord littleEndian 4 (4 * index) (field 0 6 params) (field 1 6 params)
      (field 2 6 params) (field 3 6 params) (field 5 6 params) (number 0)
  computations.foldr (LanguageResult.bind blockType)
    (LanguageResult.success (packet ((List.range 16).map fun index => .var (15 - index))))

private def parameterType (algorithm : Algorithm) : Ty :=
  types [WordMapping.type, .word, .word, .word, algorithm.stateType, .bool]

private def absorbBody (algorithm : Algorithm) : Expr :=
  LanguageResult.bind .word (readBlock algorithm.littleEndian (.var 0))
    (.letE (algorithm.compress (field 4 6 (.var 1)) (.var 0))
      (let params := Expr.var 2
       let next := fun offset remaining marker =>
         WordMapping.invoke (parameterType algorithm) .word (.var 3)
           (packet [field 0 6 params, offset, remaining, field 3 6 params, .var 0, marker])
       .ifE (.binary .wordGt (field 2 6 params) (number 63))
         (next (add (field 1 6 params) (number 64))
           (.binary .wordSub (field 2 6 params) (number 64)) (.bool false))
         (.ifE (.binary .wordGt (field 2 6 params) (number 55))
           (next (field 1 6 params) (number 0) (.bool true))
           (LanguageResult.success (algorithm.digest (.var 0))))))

/-- Digest bytes are returned in a Word, with zero high bits for shorter hashes.
Only input bytes expand memory; padding never changes user memory. -/
def hash (algorithm : Algorithm) (memoryReference sizeReference offset length : Expr) : Expr :=
  .letE (packet [memoryReference, sizeReference, offset, length])
    (LanguageResult.bind .word
      (Memory.touch (field 1 4 (.var 0)) (field 2 4 (.var 0)) (field 3 4 (.var 0)))
      (WordMapping.runHelper (parameterType algorithm) .word (absorbBody algorithm)
        (packet [.loadCell (field 0 4 (.var 1)), field 2 4 (.var 1), field 3 4 (.var 1),
          .binary .wordAnd (.binary .wordMul (field 3 4 (.var 1)) (number 8)) (number (2 ^ 64 - 1)),
          algorithm.initial, .bool false])))

end Solcore.Frontend.RustHull.HashBlocks
