import Solcore.Frontend.RustHull.HashBlocks

/-! RIPEMD-160 compiled to ordinary Core, following the designers' specification:
https://homes.esat.kuleuven.be/~bosselae/ripemd/rmd160.txt. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.Ripemd160
open Core HashBlocks

def stateType : Ty := types (List.replicate 5 .word)
private def lane (index : Nat) (state : Expr) : Expr := field index 5 state
private def initial : Expr := packet ([0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476, 0xc3d2e1f0].map number)
private def leftWords : List Nat := [
  0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
  7, 4, 13, 1, 10, 6, 15, 3, 12, 0, 9, 5, 2, 14, 11, 8,
  3, 10, 14, 4, 9, 15, 8, 1, 2, 7, 0, 6, 13, 11, 5, 12,
  1, 9, 11, 10, 0, 8, 12, 4, 13, 3, 7, 15, 14, 5, 6, 2,
  4, 0, 5, 9, 7, 12, 2, 10, 14, 1, 3, 8, 11, 6, 15, 13]
private def rightWords : List Nat := [
  5, 14, 7, 0, 9, 2, 11, 4, 13, 6, 15, 8, 1, 10, 3, 12,
  6, 11, 3, 7, 0, 13, 5, 10, 14, 15, 8, 12, 4, 9, 1, 2,
  15, 5, 1, 3, 7, 14, 6, 9, 11, 8, 12, 2, 10, 0, 4, 13,
  8, 6, 4, 1, 3, 11, 15, 0, 5, 12, 2, 13, 9, 7, 10, 14,
  12, 15, 10, 4, 1, 5, 8, 7, 6, 2, 13, 14, 0, 3, 9, 11]
private def leftRotations : List Nat := [
  11, 14, 15, 12, 5, 8, 7, 9, 11, 13, 14, 15, 6, 7, 9, 8,
  7, 6, 8, 13, 11, 9, 7, 15, 7, 12, 15, 9, 11, 7, 13, 12,
  11, 13, 6, 7, 14, 9, 13, 15, 14, 8, 13, 6, 5, 12, 7, 5,
  11, 12, 14, 15, 14, 15, 9, 8, 9, 14, 5, 6, 8, 6, 5, 12,
  9, 15, 5, 11, 6, 8, 13, 12, 5, 12, 13, 14, 11, 8, 5, 6]
private def rightRotations : List Nat := [
  8, 9, 9, 11, 13, 15, 15, 5, 7, 7, 8, 11, 14, 14, 12, 6,
  9, 13, 15, 7, 12, 8, 9, 11, 7, 7, 12, 7, 6, 15, 13, 11,
  9, 7, 15, 11, 8, 6, 6, 14, 12, 13, 5, 14, 13, 13, 7, 5,
  15, 5, 8, 11, 14, 14, 6, 14, 6, 9, 12, 9, 12, 5, 15, 8,
  8, 5, 12, 9, 12, 5, 14, 6, 8, 13, 6, 5, 15, 13, 11, 11]
private def leftConstants : List Nat := [0, 0x5a827999, 0x6ed9eba1, 0x8f1bbcdc, 0xa953fd4e]
private def rightConstants : List Nat := [0x50a28be6, 0x5c4dd124, 0x6d703ef3, 0x7a6d76e9, 0]

private def nonlinear (phase : Nat) (x y z : Expr) : Expr := match phase with
  | 0 => xor (xor x y) z
  | 1 => .binary .wordOr (.binary .wordAnd x y) (.binary .wordAnd (.unary .wordNot x) z)
  | 2 => xor (.binary .wordOr x (.unary .wordNot y)) z
  | 3 => .binary .wordOr (.binary .wordAnd x z) (.binary .wordAnd y (.unary .wordNot z))
  | _ => xor x (.binary .wordOr y (.unary .wordNot z))

private def step (phase constant rotation : Nat) (state message : Expr) : Expr :=
  let t := sum32 [rotateLeft (sum32 [lane 0 state,
    nonlinear phase (lane 1 state) (lane 2 state) (lane 3 state), message, number constant]) rotation,
    lane 4 state]
  let state := state.weakenAt 0
  .letE t (packet [lane 4 state, .var 0, lane 1 state, rotateLeft (lane 2 state) 10, lane 3 state])

/-- Compress a sixteen-word block using both eighty-step parallel lines. -/
def compress (state block : Expr) : Expr :=
  let rounds := (List.range 80).map fun index =>
    let message := Expr.second (.var (index + 1))
    .pair
      (step (index / 16) (leftConstants[index / 16]?.getD 0) (leftRotations[index]?.getD 0)
        (.first (.var 0)) (field (leftWords[index]?.getD 0) 16 message))
      (step (4 - index / 16) (rightConstants[index / 16]?.getD 0) (rightRotations[index]?.getD 0)
        (.second (.var 0)) (field (rightWords[index]?.getD 0) 16 message))
  let old := Expr.first (.var 81)
  let left := Expr.first (.var 0)
  let right := Expr.second (.var 0)
  let result := packet [sum32 [lane 1 old, lane 2 left, lane 3 right],
    sum32 [lane 2 old, lane 3 left, lane 4 right], sum32 [lane 3 old, lane 4 left, lane 0 right],
    sum32 [lane 4 old, lane 0 left, lane 1 right], sum32 [lane 0 old, lane 1 left, lane 2 right]]
  .letE (.pair state block)
    (.letE (.pair (.first (.var 0)) (.first (.var 0))) (rounds.foldr Expr.letE result))

private def digest (state : Expr) : Expr :=
  (List.range 20).foldl (fun result index =>
    .binary .wordOr (shift result 8)
      (.binary .wordByte (number (31 - index % 4)) (lane (index / 4) state))) (number 0)

/-- The 160-bit digest occupies the low bits, matching the EVM's 32-byte result. -/
def hash (memoryReference sizeReference offset length : Expr) : Expr :=
  HashBlocks.hash {stateType, initial, compress, digest, littleEndian := true}
    memoryReference sizeReference offset length

end Solcore.Frontend.RustHull.Ripemd160
