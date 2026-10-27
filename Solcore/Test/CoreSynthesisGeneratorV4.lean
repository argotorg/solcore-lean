import Solcore.Synthesis.Core.Generator
import Solcore.Synthesis.Source.ScalarRenderer

/-! Executable regressions for revision four of the checked G0 generator:
revision three's swarm mask restricted to the features of a profile's emitter,
the fallback when that removes every operator, equality with revision three
under the full feature set, and the stateful tools' refusal of the revision.
The source tests check each profile's features against its emitter. -/

set_option autoImplicit false

namespace Tests.CoreSynthesisGeneratorV4

open Solcore.Core.Wire
open Solcore.Synthesis.Core
open Solcore.Synthesis.Source (scalarSupport)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def indices (mask : FeatureMask) : List Nat :=
  (FeatureMask.catalog.zipIdx.filter fun (feature, _) => mask.allows feature).map (·.2)

private def ofIndices (selected : List Nat) : FeatureMask :=
  FeatureMask.ofBits (selected.foldl (fun bits index => bits + 2 ^ index) 0)

private def scalar (seed : Nat) : FeatureMask := GeneratorRevision.v4.caseMask (Seed.ofNat seed) scalarSupport

private def generated (seed bound : Nat) (revision : GeneratorRevision) (mask : FeatureMask) :
    IO GeneratedProgram :=
  match generate {seed := Seed.ofNat seed, maxProgramNodes := bound, revision, mask} with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"generation failed: {reprStr error}")

private def vectorChecks : IO Unit := do
  ensure (GeneratorRevision.v4.version == "core-g0-v4/lcg64-v1" &&
      GeneratorRevision.ofPureVersion? "core-g0-v4/lcg64-v1" == some .v4)
    "the revision-four version changed"
  -- The stateful tools parse with `ofVersion?`, which stops at revision three.
  ensure (GeneratorRevision.all.all fun revision =>
      GeneratorRevision.ofPureVersion? revision.version == some revision &&
      (GeneratorRevision.ofVersion? revision.version == some revision) == (revision != .v4))
    "a revision is parsed by the wrong tools"
  ensure (GeneratorRevision.all.filter (·.masked) == [.v3, .v4]) "only revisions three and four draw masks"
  ensure (indices (scalar 0) == [0, 1, 4, 8, 19, 24] && indices (scalar 2) == [0, 1, 3, 5, 8, 9, 10, 20, 24])
    "the revision-four mask vector changed"
  -- Seed 323's swarm mask enables six operators, none of them scalar.
  ensure (indices (GeneratorRevision.v3.caseMask (Seed.ofNat 323)) == [6, 7, 14, 21, 22, 23] &&
      scalar 323 == scalarSupport)
    "a restriction that removes every operator does not fall back to the emitter's features"
  -- A mask with no operator restricts plainly; one whose operators survive keeps only those.
  ensure ((ofIndices [24, 25]).within scalarSupport == ofIndices [24, 25] &&
      (ofIndices [2, 24]).within scalarSupport == scalarSupport &&
      (ofIndices [2, 3, 22, 25]).within scalarSupport == ofIndices [3, 25])
    "the restriction of constructed masks changed"
  ensure ((List.range 2048).all fun seed =>
      let mask := scalar seed
      FeatureMask.ofFeatures? mask.enabled == some mask && mask.subset scalarSupport && mask.hasOperator &&
        GeneratorRevision.v4.caseMask (Seed.ofNat seed) FeatureMask.all ==
          GeneratorRevision.v3.caseMask (Seed.ofNat seed))
    "a revision-four mask is noncanonical, escapes its features or differs from revision three under all"

private def bounds : List Nat := [3, 4, 5, 8, 16, 32, 64]

private def leaf (feature : Feature) : Bool := feature matches .wordLiteral | .local | .boolLiteral

private def generationChecks : IO Unit := do
  let mut fallbacks := 0
  for seed in List.range 128 do
    let mask := scalar seed
    if mask == scalarSupport then fallbacks := fallbacks + 1
    for bound in bounds do
      let value ← generated seed bound .v4 mask
      ensure (value.nodeCount ≤ bound && value.program.check && value.revision == .v4 && value.mask == mask)
        "a revision-four program escaped its checked budget or lost its mask"
      ensure (value.features.all fun feature => leaf feature || mask.allows feature)
        "a revision-four program used a feature its mask disables"
      -- Revision four is revision three's grammar under the restricted mask,
      -- and revision three itself under the full feature set.
      let three ← generated seed bound .v3 mask
      ensure (encodeProgram value.program == encodeProgram three.program && value.finalSeed == three.finalSeed)
        "revision four differs from revision three under the same mask"
      let full ← generated seed bound .v4 (GeneratorRevision.v4.caseMask (Seed.ofNat seed) FeatureMask.all)
      let original ← generated seed bound .v3 (GeneratorRevision.v3.caseMask (Seed.ofNat seed))
      ensure (encodeProgram full.program == encodeProgram original.program && full.finalSeed == original.finalSeed)
        "revision four under every feature differs from revision three"
  ensure (fallbacks ≤ 2) s!"{fallbacks} of 128 scalar masks fell back to the emitter's features"

def testCoreSynthesisGeneratorV4 : IO Unit := do
  vectorChecks
  generationChecks

end Tests.CoreSynthesisGeneratorV4
