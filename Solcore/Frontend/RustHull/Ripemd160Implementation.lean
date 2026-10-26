import Solcore.Frontend.RustHull.Ripemd160
import Solcore.Frontend.RustHull.Ripemd160Semantics

/-! `HashBlocks` and `Ripemd160` keep their builders private. This module
restates the RIPEMD-160 instance with public names; `hash_eq` and
`compress_eq` prove by `rfl` that the restatement is the implemented expression,
including its step tables. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.Ripemd160Implementation
open Core HashBlocks

def lane (index : Nat) (state : Core.Expr) : Core.Expr := field index 5 state
def initial : Core.Expr := packet ([0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476, 0xc3d2e1f0].map number)

def nonlinear (phase : Nat) (x y z : Core.Expr) : Core.Expr := match phase with
  | 0 => xor (xor x y) z
  | 1 => .binary .wordOr (.binary .wordAnd x y) (.binary .wordAnd (.unary .wordNot x) z)
  | 2 => xor (.binary .wordOr x (.unary .wordNot y)) z
  | 3 => .binary .wordOr (.binary .wordAnd x z) (.binary .wordAnd y (.unary .wordNot z))
  | _ => xor x (.binary .wordOr y (.unary .wordNot z))

/-- One step of a line; the state is the expression `state` and the selected
message word is `message`. -/
def step (phase constant rotation : Nat) (state message : Core.Expr) : Core.Expr :=
  let t := sum32 [rotateLeft (sum32 [lane 0 state,
    nonlinear phase (lane 1 state) (lane 2 state) (lane 3 state), message, number constant]) rotation,
    lane 4 state]
  let state := state.weakenAt 0
  .letE t (packet [lane 4 state, .var 0, lane 1 state, rotateLeft (lane 2 state) 10, lane 3 state])

/-- Step `index` of both lines: the line pair is bound at index 0 and the
original (chaining, block) pair at index `index + 1`. -/
def round (index : Nat) : Core.Expr :=
  let message := Core.Expr.second (.var (index + 1))
  .pair
    (step (index / 16) (Ripemd160Semantics.leftConstants[index / 16]?.getD 0)
      (Ripemd160Semantics.leftRotations[index]?.getD 0)
      (.first (.var 0)) (field (Ripemd160Semantics.leftWords[index]?.getD 0) 16 message))
    (step (4 - index / 16) (Ripemd160Semantics.rightConstants[index / 16]?.getD 0)
      (Ripemd160Semantics.rightRotations[index]?.getD 0)
      (.second (.var 0)) (field (Ripemd160Semantics.rightWords[index]?.getD 0) 16 message))

/-- After eighty rounds the original pair is at index 81 and the final lines at 0. -/
def result : Core.Expr :=
  let old := Core.Expr.first (.var 81)
  let left := Core.Expr.first (.var 0)
  let right := Core.Expr.second (.var 0)
  packet [sum32 [lane 1 old, lane 2 left, lane 3 right],
    sum32 [lane 2 old, lane 3 left, lane 4 right], sum32 [lane 3 old, lane 4 left, lane 0 right],
    sum32 [lane 4 old, lane 0 left, lane 1 right], sum32 [lane 0 old, lane 1 left, lane 2 right]]

def compress (state block : Core.Expr) : Core.Expr :=
  .letE (.pair state block)
    (.letE (.pair (.first (.var 0)) (.first (.var 0))) (((List.range 80).map round).foldr Core.Expr.letE result))

def digest (state : Core.Expr) : Core.Expr :=
  (List.range 20).foldl (fun result index =>
    .binary .wordOr (shift result 8)
      (.binary .wordByte (number (31 - index % 4)) (lane (index / 4) state))) (number 0)

def paddedByte (mapping offset remaining bits markerUsed : Core.Expr) (index : Nat) : Core.Expr :=
  .ifE (.binary .wordGt remaining (number index))
    (Memory.readMemoryByte mapping (add offset (number index)))
    (LanguageResult.success
      (.ifE (.ifE (.binary .wordEq remaining (number index)) (.unary .boolNot markerUsed) (.bool false))
        (number 128)
        (if index < 56 then number 0
          else .ifE (.binary .wordGt (number 56) remaining)
            (.binary .wordByte (number (31 - (index - 56))) bits)
            (number 0))))

def readWord : Nat → Nat → Core.Expr → Core.Expr → Core.Expr → Core.Expr → Core.Expr → Core.Expr → Core.Expr
  | 0, _, _, _, _, _, _, accumulator => LanguageResult.success accumulator
  | count + 1, index, mapping, offset, remaining, bits, markerUsed, accumulator =>
      LanguageResult.bind .word (paddedByte mapping offset remaining bits markerUsed index)
        (readWord count (index + 1) (mapping.weakenAt 0) (offset.weakenAt 0)
          (remaining.weakenAt 0) (bits.weakenAt 0) (markerUsed.weakenAt 0)
          (.binary .wordOr (accumulator.weakenAt 0) (shift (.var 0) (8 * (index % 4)))))

def readBlock (parameters : Core.Expr) : Core.Expr :=
  let computations := (List.range 16).map fun index =>
    let params := move parameters index
    readWord 4 (4 * index) (field 0 6 params) (field 1 6 params)
      (field 2 6 params) (field 3 6 params) (field 5 6 params) (number 0)
  computations.foldr (LanguageResult.bind blockType)
    (LanguageResult.success (packet ((List.range 16).map fun index => .var (15 - index))))

def parameterType : Core.Ty := types [WordMapping.type, .word, .word, .word, Ripemd160.stateType, .bool]

/-- Parameters: mapping, offset, remaining length, bit length, chaining state
and whether the marker byte was already written. -/
def absorbBody : Core.Expr :=
  LanguageResult.bind .word (readBlock (.var 0))
    (.letE (compress (field 4 6 (.var 1)) (.var 0))
      (let params := Core.Expr.var 2
       let next := fun offset remaining marker =>
         WordMapping.invoke parameterType .word (.var 3)
           (packet [field 0 6 params, offset, remaining, field 3 6 params, .var 0, marker])
       .ifE (.binary .wordGt (field 2 6 params) (number 63))
         (next (add (field 1 6 params) (number 64))
           (.binary .wordSub (field 2 6 params) (number 64)) (.bool false))
         (.ifE (.binary .wordGt (field 2 6 params) (number 55))
           (next (field 1 6 params) (number 0) (.bool true))
           (LanguageResult.success (digest (.var 0))))))

def hash (memoryReference sizeReference offset length : Core.Expr) : Core.Expr :=
  .letE (packet [memoryReference, sizeReference, offset, length])
    (LanguageResult.bind .word
      (Memory.touch (field 1 4 (.var 0)) (field 2 4 (.var 0)) (field 3 4 (.var 0)))
      (WordMapping.runHelper parameterType .word absorbBody
        (packet [.loadCell (field 0 4 (.var 1)), field 2 4 (.var 1), field 3 4 (.var 1),
          .binary .wordAnd (.binary .wordMul (field 3 4 (.var 1)) (number 8)) (number (2 ^ 64 - 1)),
          initial, .bool false])))

theorem compress_eq (state block : Core.Expr) : Ripemd160.compress state block = compress state block := rfl

theorem hash_eq (memoryReference sizeReference offset length : Core.Expr) :
    Ripemd160.hash memoryReference sizeReference offset length =
      hash memoryReference sizeReference offset length := rfl

end Solcore.Frontend.RustHull.Ripemd160Implementation
