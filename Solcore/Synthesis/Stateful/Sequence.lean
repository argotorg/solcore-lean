import Lean.Data.Json
import Solcore.Synthesis.Core.Seed

/-! Generated stateful sequences: the bound on a scenario's ordered
transactions, shared by the case modules and the imported-Hull scenario
runners, and the three-transaction blocks a generated sequence is drawn from.
Three transactions are exactly the original single-block sequence. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Stateful.Sequence
open Lean Solcore.Synthesis.Core

/-- A stateful scenario has one to eight ordered transactions. Generation keeps
three unless a longer random sequence is requested, and the fixed corpora keep
one to three. -/
def maxTransactions : Nat := 8

/-- The number of three-transaction blocks that `count` transactions use. -/
def blockCount (count : Nat) : Nat := (count + 2) / 3

/-- Block zero uses the scenario seed. Block `k + 1` uses the high half of draw
`k + 1` of a separate stream: the low bits of a power-of-two LCG have short
periods. -/
def blockSeeds (seed : Seed) (blocks : Nat) : List Seed := Id.run do
  let mut state := Seed.ofNat (seed.toNat ^^^ 0x74782d626c6f636b)
  let mut seeds : Array Seed := #[]
  for block in List.range blocks do
    if block == 0 then
      seeds := seeds.push seed
    else
      let (value, next) := state.draw
      seeds := seeds.push (Seed.ofNat (value.toNat / 2 ^ 32))
      state := next
  return seeds.toList

/-- The first `count` elements of consecutive blocks; `block` draws one block
from its seed, given the index of the block's first transaction. -/
def blocks {α : Type} (block : Seed → Nat → List α) (seed : Seed) (count : Nat) : List α :=
  ((blockSeeds seed (blockCount count)).zipIdx.flatMap fun (blockSeed, index) =>
    block blockSeed (3 * index)).take count

/-- The sequence choices of every block that `count` transactions use. -/
def blockChoices (choices : Seed → List Nat) (seed : Seed) (count : Nat) : List Nat :=
  (blockSeeds seed (blockCount count)).flatMap choices

def checkCount (count : Nat) : Except String Unit :=
  unless 1 ≤ count && count ≤ maxTransactions do
    throw s!"a generated sequence has 1 to {maxTransactions} transactions"

/-- A generated origin records a transaction count other than three. -/
def recordCount (origin : Json) (count : Nat) : Json :=
  if count == 3 then origin else origin.setObjVal! "transactionCount" (toJson count)

/-- A generated origin's transaction count; a recorded three is noncanonical. -/
def savedCount (origin : Json) : Except String Nat :=
  match origin.getObjVal? "transactionCount" with
  | .error _ => return 3
  | .ok value => do
      let count ← value.getNat?
      checkCount count
      if count == 3 then throw "a saved origin records the default transaction count"
      return count

end Solcore.Synthesis.Stateful.Sequence
