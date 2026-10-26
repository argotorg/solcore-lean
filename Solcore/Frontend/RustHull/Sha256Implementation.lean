import Solcore.Frontend.RustHull.Sha256
import Solcore.Frontend.RustHull.Sha256Semantics

/-! `HashBlocks` and `Sha256` keep their builders private. This module restates
the SHA-256 instance with public names; `hash_eq` and `compress_eq` prove by
`rfl` that the restatement is the implemented expression. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.Sha256Implementation
open Core HashBlocks

def lane (index : Nat) (state : Core.Expr) : Core.Expr := field index 8 state
def initial : Core.Expr := packet ([0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
  0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19].map number)
def constants : List Nat := Sha256Semantics.constants

def xor3 (a b c : Core.Expr) : Core.Expr := xor (xor a b) c
def small0 (x : Core.Expr) : Core.Expr := xor3 (rotateRight x 7) (rotateRight x 18) (.binary .wordShr x (number 3))
def small1 (x : Core.Expr) : Core.Expr := xor3 (rotateRight x 17) (rotateRight x 19) (.binary .wordShr x (number 10))
def large0 (x : Core.Expr) : Core.Expr := xor3 (rotateRight x 2) (rotateRight x 13) (rotateRight x 22)
def large1 (x : Core.Expr) : Core.Expr := xor3 (rotateRight x 6) (rotateRight x 11) (rotateRight x 25)
def choose (x y z : Core.Expr) : Core.Expr := xor (.binary .wordAnd x y) (.binary .wordAnd (.unary .wordNot x) z)
def majority (x y z : Core.Expr) : Core.Expr :=
  xor3 (.binary .wordAnd x y) (.binary .wordAnd x z) (.binary .wordAnd y z)

/-- One round: the state is bound at index 0 and W(t) at index 64. -/
def round (constant : Nat) : Core.Expr :=
  let state := Core.Expr.var 0
  let t1 := sum32 [lane 7 state, large1 (lane 4 state), choose (lane 4 state) (lane 5 state) (lane 6 state),
    number constant, .var 64]
  let t2 := sum32 [large0 (lane 0 (.var 1)), majority (lane 0 (.var 1)) (lane 1 (.var 1)) (lane 2 (.var 1))]
  .letE t1 (.letE t2 (packet [sum32 [.var 1, .var 0], lane 0 (.var 2), lane 1 (.var 2),
    lane 2 (.var 2), sum32 [lane 3 (.var 2), .var 1], lane 4 (.var 2), lane 5 (.var 2), lane 6 (.var 2)]))

def scheduleWord (index : Nat) : Core.Expr :=
  if index < 16 then field index 16 (.second (.var index))
  else sum32 [small1 (.var 1), .var 6, small0 (.var 14), .var 15]

def completed : Core.Expr :=
  packet ((List.range 8).map fun index => sum32 [lane index (.var 64), lane index (.var 0)])

def compress (state block : Core.Expr) : Core.Expr :=
  .letE (.pair state block)
    (((List.range 64).map scheduleWord).foldr Core.Expr.letE
      (.letE (.first (.var 64)) ((constants.map round).foldr Core.Expr.letE completed)))

def digest (state : Core.Expr) : Core.Expr :=
  (List.range 8).foldl (fun result index => .binary .wordOr (shift result 32) (lane index state)) (number 0)

def paddedByte (mapping offset remaining bits markerUsed : Core.Expr) (index : Nat) : Core.Expr :=
  .ifE (.binary .wordGt remaining (number index))
    (Memory.readMemoryByte mapping (add offset (number index)))
    (LanguageResult.success
      (.ifE (.ifE (.binary .wordEq remaining (number index)) (.unary .boolNot markerUsed) (.bool false))
        (number 128)
        (if index < 56 then number 0
          else .ifE (.binary .wordGt (number 56) remaining)
            (.binary .wordByte (number (24 + (index - 56))) bits)
            (number 0))))

def readWord : Nat → Nat → Core.Expr → Core.Expr → Core.Expr → Core.Expr → Core.Expr → Core.Expr → Core.Expr
  | 0, _, _, _, _, _, _, accumulator => LanguageResult.success accumulator
  | count + 1, index, mapping, offset, remaining, bits, markerUsed, accumulator =>
      LanguageResult.bind .word (paddedByte mapping offset remaining bits markerUsed index)
        (readWord count (index + 1) (mapping.weakenAt 0) (offset.weakenAt 0)
          (remaining.weakenAt 0) (bits.weakenAt 0) (markerUsed.weakenAt 0)
          (.binary .wordOr (accumulator.weakenAt 0) (shift (.var 0) (8 * (3 - index % 4)))))

def readBlock (parameters : Core.Expr) : Core.Expr :=
  let computations := (List.range 16).map fun index =>
    let params := move parameters index
    readWord 4 (4 * index) (field 0 6 params) (field 1 6 params)
      (field 2 6 params) (field 3 6 params) (field 5 6 params) (number 0)
  computations.foldr (LanguageResult.bind blockType)
    (LanguageResult.success (packet ((List.range 16).map fun index => .var (15 - index))))

def parameterType : Core.Ty := types [WordMapping.type, .word, .word, .word, Sha256.stateType, .bool]

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

theorem compress_eq (state block : Core.Expr) : Sha256.compress state block = compress state block := rfl

theorem hash_eq (memoryReference sizeReference offset length : Core.Expr) :
    Sha256.hash memoryReference sizeReference offset length = hash memoryReference sizeReference offset length := rfl

end Solcore.Frontend.RustHull.Sha256Implementation
