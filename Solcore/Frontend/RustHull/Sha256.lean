import Solcore.Frontend.RustHull.HashBlocks

/-! SHA-256 expressed in ordinary Core using FIPS 180-4, sections 4.1.2,
4.2.2, 5.3.3 and 6.2: https://doi.org/10.6028/NIST.FIPS.180-4. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.Sha256
open Core HashBlocks

def stateType : Ty := types (List.replicate 8 .word)
private def lane (index : Nat) (state : Expr) : Expr := field index 8 state
private def initial : Expr := packet ([0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
  0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19].map number)
private def constants : List Nat := [
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

private def xor3 (a b c : Expr) : Expr := xor (xor a b) c
private def small0 (x : Expr) : Expr := xor3 (rotateRight x 7) (rotateRight x 18) (.binary .wordShr x (number 3))
private def small1 (x : Expr) : Expr := xor3 (rotateRight x 17) (rotateRight x 19) (.binary .wordShr x (number 10))
private def large0 (x : Expr) : Expr := xor3 (rotateRight x 2) (rotateRight x 13) (rotateRight x 22)
private def large1 (x : Expr) : Expr := xor3 (rotateRight x 6) (rotateRight x 11) (rotateRight x 25)
private def choose (x y z : Expr) : Expr := xor (.binary .wordAnd x y) (.binary .wordAnd (.unary .wordNot x) z)
private def majority (x y z : Expr) : Expr :=
  xor3 (.binary .wordAnd x y) (.binary .wordAnd x z) (.binary .wordAnd y z)

private def round (constant : Nat) : Expr :=
  let state := Expr.var 0
  let t1 := sum32 [lane 7 state, large1 (lane 4 state), choose (lane 4 state) (lane 5 state) (lane 6 state),
    number constant, .var 64]
  let t2 := sum32 [large0 (lane 0 (.var 1)), majority (lane 0 (.var 1)) (lane 1 (.var 1)) (lane 2 (.var 1))]
  .letE t1 (.letE t2 (packet [sum32 [.var 1, .var 0], lane 0 (.var 2), lane 1 (.var 2),
    lane 2 (.var 2), sum32 [lane 3 (.var 2), .var 1], lane 4 (.var 2), lane 5 (.var 2), lane 6 (.var 2)]))

/-- Compress one sixteen-word message block into an eight-word chaining state. -/
def compress (state block : Expr) : Expr :=
  let schedule := (List.range 64).map fun index =>
    if index < 16 then field index 16 (.second (.var index))
    else sum32 [small1 (.var 1), .var 6, small0 (.var 14), .var 15]
  let completed := packet ((List.range 8).map fun index => sum32 [lane index (.var 64), lane index (.var 0)])
  .letE (.pair state block)
    (schedule.foldr Expr.letE (.letE (.first (.var 64)) ((constants.map round).foldr Expr.letE completed)))

private def digest (state : Expr) : Expr :=
  (List.range 8).foldl (fun result index => .binary .wordOr (shift result 32) (lane index state)) (number 0)

def hash (memoryReference sizeReference offset length : Expr) : Expr :=
  HashBlocks.hash {stateType, initial, compress, digest, littleEndian := false}
    memoryReference sizeReference offset length

end Solcore.Frontend.RustHull.Sha256
