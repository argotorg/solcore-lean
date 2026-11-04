import Lean.Data.Json
import Solcore.Core.Syntax
import Solcore.Synthesis.Core.Generator

/-!
# Acceptance and input selection

Which generated functions a profile accepts, and which inputs a case runs. Generated origins record
both, so replay applies the same rules. Main declarations: `Acceptance`, `Acceptance.check`,
`InputSelection`, `InputSelection.inputs`.
-/

section
-- leanmerge: from Solcore.Synthesis.Source.Acceptance
/-! Which generated runtime-input functions a profile accepts. Every profile
keeps its own filters; the identity filter also excludes a function that
returns each of its boundary inputs unchanged, which would exercise only the
ABI decoding and return of each path. Generated origins name the filter, so
replay applies the same one. Imported and reduced cases are never filtered. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source
open Lean
open Solcore.Core (Word)

/-- The acceptance filter of a generated runtime-input function. -/
inductive Acceptance where
  /-- The profile's own filters only; fixed corpora use this. -/
  | profile
  /-- The profile's own filters, then the exclusion of boundary identities. -/
  | nonIdentity
  deriving Repr, BEq, DecidableEq, Inhabited

namespace Acceptance

def nonIdentityVersion : String := "exclude-boundary-identity-v1"

def ofVersion? (version : String) : Option Acceptance :=
  if version = nonIdentityVersion then some .nonIdentity else none

/-- The exclusion reason of every profile that applies the identity filter. -/
def identityReason : String := "every boundary input returned itself"

/-- Applied to the boundary results that the profile's own filter computed. -/
def check (acceptance : Acceptance) (inputs results : List Word) : Except String Unit :=
  match acceptance with
  | .profile => .ok ()
  | .nonIdentity => if results == inputs then .error identityReason else .ok ()

/-- Filtered origins name the filter; unfiltered origins are unchanged. -/
def record (acceptance : Acceptance) (origin : Json) : Json :=
  match acceptance with
  | .profile => origin
  | .nonIdentity => origin.setObjVal! "acceptance" (toJson nonIdentityVersion)

/-- The filter a saved generated origin names. -/
def ofOrigin (origin : Json) : Except String Acceptance :=
  match origin.getObjVal? "acceptance" with
  | .error _ => .ok .profile
  | .ok value =>
      match value.getStr? with
      | .ok version =>
          match ofVersion? version with
          | some acceptance => .ok acceptance
          | none => .error "unsupported acceptance filter"
      | .error _ => .error "unsupported acceptance filter"

end Acceptance

end Solcore.Synthesis.Source
end

section
-- leanmerge: from Solcore.Synthesis.Source.InputSelection
/-! Runtime inputs of generated runtime-input cases. Every generated function
keeps its profile's boundary inputs; seeded selection appends four inputs
derived from the case seed. Saved cases name their selection, so replay
recomputes the same list. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source
open Lean
open Solcore.Core (Word)
open Solcore.Synthesis.Core

/-- How a generated function's runtime inputs are listed. -/
inductive InputSelection where
  /-- The profile's boundary inputs only; fixed corpora use this. -/
  | boundary
  /-- The boundary inputs followed by `seededInputs` of the case seed. -/
  | seeded
  deriving Repr, BEq, DecidableEq, Inhabited

namespace InputSelection

def seededVersion : String := "seeded-inputs-v1/splitmix64"

def ofVersion? (version : String) : Option InputSelection :=
  if version = seededVersion then some .seeded else none

/-- Separates this stream from other uses of a case seed. -/
private def domain : UInt64 := 0x696e707574733031

private def gamma : UInt64 := 0x9e3779b97f4a7c15

/-- SplitMix64 outputs `1..count` from the domain-separated case seed. -/
private def stream (seed : Seed) (count : Nat) : List UInt64 :=
  (List.range count).map fun index =>
    GeneratorV2.mix ((seed.toUInt64 ^^^ domain) + UInt64.ofNat (index + 1) * gamma)

private def limbs : List UInt64 → Nat
  | [high, next, nextLow, low] =>
      high.toNat * 2 ^ 192 + next.toNat * 2 ^ 128 + nextLow.toNat * 2 ^ 64 + low.toNat
  | _ => 0

/-- One slot of five outputs: four limbs and a width or small value. -/
private def slot (outputs : List UInt64) (index : Nat) : Nat × Nat :=
  let part := (outputs.drop (5 * index)).take 5
  (limbs (part.take 4), (part.getD 4 0).toNat)

/--
Four inputs from the case seed: a full random Word, a random Word of uniform
bit width one to 256, a small value below 512, and the negation of another
uniform-width value.
-/
def seededInputs (seed : Seed) : List Word :=
  let outputs := stream seed 20
  let (full, _) := slot outputs 0
  let (wide, width) := slot outputs 1
  let (_, small) := slot outputs 2
  let (negated, negatedWidth) := slot outputs 3
  [Word.ofNatModulo full,
    Word.ofNatModulo (wide % 2 ^ (1 + width % 256)),
    Word.ofNatModulo (small % 512),
    Word.ofNatModulo (2 ^ 256 - negated % 2 ^ (1 + negatedWidth % 256))]

/-- The inputs of one generated function, in `inputIndex` order. -/
def inputs (selection : InputSelection) (boundaries : List Word) (seed : Seed) : List Word :=
  match selection with
  | .boundary => boundaries
  | .seeded => boundaries ++ seededInputs seed

/-- Seeded origins name their selection; boundary origins are unchanged. -/
def record (selection : InputSelection) (origin : Json) : Json :=
  match selection with
  | .boundary => origin
  | .seeded => origin.setObjVal! "inputSelection" (toJson seededVersion)

/-- The selection a saved generated origin names. -/
def ofOrigin (origin : Json) : Except String InputSelection :=
  match origin.getObjVal? "inputSelection" with
  | .error _ => .ok .boundary
  | .ok value =>
      match value.getStr? with
      | .ok version =>
          match ofVersion? version with
          | some selection => .ok selection
          | none => .error "unsupported input selection"
      | .error _ => .error "unsupported input selection"

end InputSelection

end Solcore.Synthesis.Source
end
