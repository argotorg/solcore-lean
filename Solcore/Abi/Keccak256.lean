import Solcore.Semantics.RuntimeScalars

/-! Ethereum-compatible Keccak-256 over runtime bytes. -/

set_option autoImplicit false

namespace Solcore.Abi.V1.Keccak256

open Solcore.Semantics

private abbrev State := Array UInt64

def rateBytes : Nat := 136

private def roundConstants : Array UInt64 := #[
  0x0000000000000001, 0x0000000000008082,
  0x800000000000808a, 0x8000000080008000,
  0x000000000000808b, 0x0000000080000001,
  0x8000000080008081, 0x8000000000008009,
  0x000000000000008a, 0x0000000000000088,
  0x0000000080008009, 0x000000008000000a,
  0x000000008000808b, 0x800000000000008b,
  0x8000000000008089, 0x8000000000008003,
  0x8000000000008002, 0x8000000000000080,
  0x000000000000800a, 0x800000008000000a,
  0x8000000080008081, 0x8000000000008080,
  0x0000000080000001, 0x8000000080008008
]

private def rotationOffsets : Array Nat := #[
   0,  1, 62, 28, 27,
  36, 44,  6, 55, 20,
   3, 10, 43, 25, 39,
  41, 45, 15, 21,  8,
  18,  2, 61, 56, 14
]

private def rotateLeft (value : UInt64) (distance : Nat) : UInt64 :=
  UInt64.ofBitVec (value.toBitVec.rotateLeft distance)

private def columnParity (state : State) (x : Nat) : UInt64 :=
  (List.range 5).foldl
    (fun parity y => parity ^^^ state[x + 5 * y]!) 0

private def theta (state : State) : State :=
  let parities := (List.range 5).map (columnParity state) |>.toArray
  let deltas := (List.range 5).map (fun x =>
    parities[(x + 4) % 5]! ^^^ rotateLeft parities[(x + 1) % 5]! 1)
  (List.range 25).foldl
    (fun next index => next.set! index
      (state[index]! ^^^ deltas[index % 5]!))
    state

private def rhoPi (state : State) : State :=
  (List.range 25).foldl (fun next index =>
    let x := index % 5
    let y := index / 5
    let target := y + 5 * ((2 * x + 3 * y) % 5)
    next.set! target (rotateLeft state[index]! rotationOffsets[index]!))
    (Array.replicate 25 0)

private def chi (state : State) : State :=
  (List.range 25).foldl (fun next index =>
    let x := index % 5
    let y := index / 5
    let first := state[((x + 1) % 5) + 5 * y]!
    let second := state[((x + 2) % 5) + 5 * y]!
    next.set! index (state[index]! ^^^ (~~~first &&& second)))
    state

private def round (state : State) (constant : UInt64) : State :=
  let state := chi (rhoPi (theta state))
  state.set! 0 (state[0]! ^^^ constant)

private def permute (state : State) : State :=
  roundConstants.foldl round state

private def loadLaneLE (bytes : Bytes) (offset : Nat) : UInt64 :=
  (List.range 8).foldl (fun lane index =>
    lane ||| (bytes.get! (offset + index)).toUInt64 <<<
      UInt64.ofNat (8 * index)) 0

private def absorbBlock (state : State) (bytes : Bytes) (offset : Nat) : State :=
  let absorbed := (List.range 17).foldl (fun next lane =>
    next.set! lane (state[lane]! ^^^ loadLaneLE bytes (offset + 8 * lane)))
    state
  permute absorbed

private def padding (input : Bytes) : Bytes :=
  let remaining := rateBytes - input.size % rateBytes
  if remaining = 1 then
    input.push 0x81
  else
    input.push 0x01
      |>.append ((List.replicate (remaining - 2) 0).toByteArray)
      |>.push 0x80

private def absorb (input : Bytes) : State :=
  let padded := padding input
  (List.range (padded.size / rateBytes)).foldl
    (fun state block => absorbBlock state padded (block * rateBytes))
    (Array.replicate 25 0)

private def laneBytesLE (lane : UInt64) : List UInt8 :=
  (List.range 8).map fun index =>
    UInt8.ofNat ((lane >>> UInt64.ofNat (8 * index)).toNat % 256)

/-- The 32-byte Ethereum Keccak digest (domain byte `0x01`, not SHA3-256). -/
def hash (input : Bytes) : Bytes :=
  let state := absorb input
  ((List.range 4).flatMap fun lane => laneBytesLE state[lane]!).toByteArray

end Solcore.Abi.V1.Keccak256
