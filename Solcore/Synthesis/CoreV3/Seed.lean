import Std

/-!
A small, versioned source of deterministic choices for Core v3 synthesis.

The algorithm is intentionally part of the public replay contract. Changing its
constants or draw semantics requires a new `algorithmId`.
-/

set_option autoImplicit false

namespace Solcore.Synthesis.CoreV3

/-- Replayable state for the versioned Core v3 synthesis generator. -/
structure Seed where
  private mk ::
  state : UInt64
deriving Repr, BEq, DecidableEq

namespace Seed

/-- Stable identifier for the generator's 64-bit linear congruential algorithm. -/
def algorithmId : String := "lcg64-v1"

private def multiplier : UInt64 := 6364136223846793005

private def increment : UInt64 := 1442695040888963407

/-- Construct a seed from its exact 64-bit replay state. -/
def ofUInt64 (value : UInt64) : Seed :=
  ⟨value⟩

/-- Construct a seed by reducing a natural number to 64 bits. -/
def ofNat (value : Nat) : Seed :=
  ofUInt64 (UInt64.ofNat value)

/-- Reveal the exact 64-bit replay state. -/
def toUInt64 (seed : Seed) : UInt64 :=
  seed.state

/-- Reveal the replay state as a natural number. -/
def toNat (seed : Seed) : Nat :=
  seed.state.toNat

private def advance (state : UInt64) : UInt64 :=
  state * multiplier + increment

/--
Advance once, returning the new state both as the drawn value and as the next
seed. `UInt64` arithmetic gives the specified wraparound modulo `2^64`.
-/
def draw (seed : Seed) : UInt64 × Seed :=
  let value := advance seed.state
  (value, ofUInt64 value)

/--
Draw a choice in `[0, bound)`. A zero bound still consumes exactly one draw and
returns zero, keeping replay state advancement independent of that edge case.
-/
def choose (seed : Seed) (bound : Nat) : Nat × Seed :=
  let (value, next) := seed.draw
  if bound = 0 then (0, next) else (value.toNat % bound, next)

end Seed

end Solcore.Synthesis.CoreV3
