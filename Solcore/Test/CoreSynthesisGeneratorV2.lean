import Solcore.Synthesis.Core.Generator

/-! Executable regressions for revision two of the checked G0 generator: its
replay vectors, its checker and budget bounds, and the decorrelation of its
choices. Revision one's own exact behavior is pinned by the existing tests and
fixed corpora. -/

set_option autoImplicit false

namespace Tests.CoreSynthesisGeneratorV2

open Solcore.Core (Word)
open Solcore.Core.Wire
open Solcore.Synthesis.Core

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def request (seed bound : Nat) (revision : GeneratorRevision := .v2) : GenerationRequest :=
  {seed := Seed.ofNat seed, maxProgramNodes := bound, revision}

private def generated (seed bound : Nat) (revision : GeneratorRevision := .v2) :
    IO GeneratedProgram :=
  match generate (request seed bound revision) with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"generation failed: {reprStr error}")

private def chooseValues : List Nat → Seed → List Nat × Seed
  | [], seed => ([], seed)
  | bound :: bounds, seed =>
      let (value, next) := GeneratorV2.choose seed bound
      let (values, finalSeed) := chooseValues bounds next
      (value :: values, finalSeed)

private def wordValues : Nat → Seed → List Nat × Seed
  | 0, seed => ([], seed)
  | count + 1, seed =>
      let (value, next) := GeneratorV2.drawWord seed
      let (values, finalSeed) := wordValues count next
      (value.val :: values, finalSeed)

private def word (value : Nat) : Expr := .word (Word.ofNatModulo value)

/-- Seed 2 at a 32-node budget; any change to this program needs a new revision. -/
private def pinnedBody : Expr :=
  .binary .wordByte (word (2 ^ 32))
    (.unary .wordNot
      (.letE
        (.ternary .wordAddMod
          (word 58776200593107087877498445594665358012522562555746522916260173453486719764460)
          (word 61257103412546197960633691692829092041022166143235981156631755156305019596000)
          (word (2 ^ 192)))
        (word 15059245801192277483352447598272883119367250069704906357382193883813969988912)))

private def vectorChecks : IO Unit := do
  ensure (GeneratorRevision.v1.version == generatorVersion &&
      generatorVersion == "core-g0-v1/lcg64-v1" &&
      GeneratorRevision.v2.version == "core-g0-v2/lcg64-v1")
    "G0 revision version strings changed"
  ensure (GeneratorRevision.all.all fun revision =>
      GeneratorRevision.ofVersion? revision.version == some revision)
    "a G0 revision does not round-trip through its version"
  ensure (GeneratorRevision.ofVersion? "core-g0-v4/lcg64-v1" == none &&
      GeneratorRevision.ofVersion? "core-primitives-v1/core-g0-v2/lcg64-v1" == none)
    "an unknown version named a G0 revision"
  -- SplitMix64's first output from state zero.
  ensure (GeneratorV2.mix 0x9e3779b97f4a7c15 == 0xe220a8397b1dcdaf)
    "the v2 mixer is not the SplitMix64 finalizer"
  ensure (chooseValues [1, 2, 3, 17, 0, 65537] (Seed.ofNat 42) ==
      ([0, 0, 1, 11, 0, 42700], Seed.ofUInt64 483838003013946848))
    "the v2 bounded-choice vector changed"
  ensure (wordValues 4 (Seed.ofNat 7) ==
      ([2 ^ 32 - 1, 255,
        65351026003261654626954439029979190336370795858679125620385447918294780264974,
        37788469697379889739109967857431538320966943693411706229219554434276053901074],
        Seed.ofUInt64 3970079635837256351))
    "the v2 literal vector changed"
  let pinned ← generated 2 32
  ensure (pinned.finalSeed == Seed.ofUInt64 10927198619237024990 && pinned.nodeCount == 11 &&
      encodeProgram pinned.program ==
        encodeProgram {resultType := .word, dataDefinitions := [], body := pinnedBody})
    "the pinned v2 program changed"
  let bank := GeneratorV2.edgeBank.toList.map (·.val)
  ensure (bank.length == 32 && bank.eraseDups.length == 32 &&
      [0, 1, 255, 256, 257, 2 ^ 16, 2 ^ 32, 2 ^ 64, 2 ^ 160 - 1, 2 ^ 255 - 1, 2 ^ 255,
        2 ^ 256 - 1].all bank.contains)
    "the v2 edge bank changed"

private def bounds : List Nat := [3, 4, 5, 8, 16, 32, 64]

private def generationChecks : IO Unit := do
  for budget in [0, 1, 2] do
    ensure (match generate (request 0 budget) with | .error .budgetTooSmall => true | _ => false)
      "v2 accepted a budget below the program minimum"
  let minimum ← generated 0 minimumProgramNodes
  ensure (minimum.nodeCount == minimumProgramNodes) "v2 missed the exact minimum budget"
  let first ← generated 37 64
  let second ← generated 37 64
  ensure (first.initialSeed == second.initialSeed && first.finalSeed == second.finalSeed &&
      first.revision == .v2 && second.revision == .v2 &&
      encodeProgram first.program == encodeProgram second.program &&
      first.features == second.features)
    "v2 replay of one request is not deterministic"
  let mut differs := false
  for seed in List.range 128 do
    for bound in bounds do
      let value ← generated seed bound
      ensure (value.initialSeed == Seed.ofNat seed && value.maxProgramNodes == bound &&
          value.nodeCount ≤ bound && value.program.check && accepts .word value.program.body)
        "a v2 program escaped its checked budget"
      let original ← generated seed bound .v1
      let implicit ← match generate {seed := Seed.ofNat seed, maxProgramNodes := bound} with
        | .ok value => pure value
        | .error error => throw (IO.userError s!"v1 generation failed: {reprStr error}")
      ensure (original.revision == .v1 && implicit.revision == .v1 &&
          encodeProgram implicit.program == encodeProgram original.program &&
          implicit.finalSeed == original.finalSeed)
        "a request without a revision no longer selects v1"
      differs := differs || encodeProgram value.program != encodeProgram original.program
  ensure differs "v2 reproduced every v1 program"

/-- Leaves in generation order, which is left-to-right preorder. -/
private def wordLeaves : Expr → List Word
  | .word value => [value]
  | .letE initializer body => wordLeaves initializer ++ wordLeaves body
  | .ifE condition thenBranch elseBranch =>
      wordLeaves condition ++ wordLeaves thenBranch ++ wordLeaves elseBranch
  | .unary _ operand => wordLeaves operand
  | .binary _ left right => wordLeaves left ++ wordLeaves right
  | .ternary _ first second third => wordLeaves first ++ wordLeaves second ++ wordLeaves third
  | _ => []

private def boolLeaves : Expr → List Bool
  | .bool value => [value]
  | .letE initializer body => boolLeaves initializer ++ boolLeaves body
  | .ifE condition thenBranch elseBranch =>
      boolLeaves condition ++ boolLeaves thenBranch ++ boolLeaves elseBranch
  | .unary _ operand => boolLeaves operand
  | .binary _ left right => boolLeaves left ++ boolLeaves right
  | .ternary _ first second third => boolLeaves first ++ boolLeaves second ++ boolLeaves third
  | _ => []

/-- Two literal operands of one binary operation. -/
private def literalOperands : Expr → List (Word × Word)
  | .binary _ (.word left) (.word right) => [(left, right)]
  | .letE initializer body => literalOperands initializer ++ literalOperands body
  | .ifE condition thenBranch elseBranch =>
      literalOperands condition ++ literalOperands thenBranch ++ literalOperands elseBranch
  | .unary _ operand => literalOperands operand
  | .binary _ left right => literalOperands left ++ literalOperands right
  | .ternary _ first second third =>
      literalOperands first ++ literalOperands second ++ literalOperands third
  | _ => []

/-- The root form index chosen by the grammar for a budget of at least four. -/
private def rootForm : Expr → Nat
  | .word _ => 0
  | .unary .. => 1
  | .binary .. => 2
  | .ternary .. => 3
  | .letE .. => 4
  | _ => 5

private def edge (value : Word) : Bool := GeneratorV2.edgeBank.contains value

/-- Counts of two-edge, mixed and two-random pairs. -/
private def pairings (pairs : List (Word × Word)) : Nat × Nat × Nat :=
  pairs.foldl (fun (both, mixed, neither) (left, right) =>
    match edge left, edge right with
    | true, true => (both + 1, mixed, neither)
    | false, false => (both, mixed, neither + 1)
    | _, _ => (both, mixed + 1, neither)) (0, 0, 0)

/-- `low/scale ≤ part/whole ≤ high/scale`. -/
private def within (part whole low high scale : Nat) : Bool :=
  whole > 0 && low * whole ≤ part * scale && part * scale ≤ high * whole

/-- One thousand and twenty-four consecutive seeds at a 32-node budget. -/
private def statisticsChecks : IO Unit := do
  let mut adjacent : List (Word × Word) := []
  let mut operands : List (Word × Word) := []
  let mut words : List Word := []
  let mut flips := 0
  let mut boolPairs := 0
  let mut roots : List Nat := []
  for seed in List.range 1024 do
    let body := (← generated seed 32).program.body
    let leaves := wordLeaves body
    adjacent := adjacent ++ leaves.zip leaves.tail
    operands := operands ++ literalOperands body
    words := words ++ leaves
    let bools := boolLeaves body
    for (left, right) in bools.zip bools.tail do
      boolPairs := boolPairs + 1
      if left != right then flips := flips + 1
    roots := roots ++ [rootForm body]
  let (both, mixed, neither) := pairings adjacent
  let total := both + mixed + neither
  ensure (both > 0 && mixed > 0 && neither > 0)
    "v2 lost an adjacent edge/random literal pairing"
  ensure (within both total 20 30 100 && within neither total 20 30 100 &&
      within mixed total 42 58 100)
    s!"adjacent v2 literals are not independent: {both} edge, {mixed} mixed, {neither} random"
  let (operandBoth, operandMixed, operandNeither) := pairings operands
  ensure (operandBoth > 0 && operandMixed > 0 && operandNeither > 0)
    "the operands of one v2 binary operation lost a pairing"
  ensure (within (words.filter edge).length words.length 45 55 100)
    "v2 no longer draws about half of its literals from the edge bank"
  ensure (GeneratorV2.edgeBank.all words.contains) "a v2 edge value never appeared"
  ensure (flips > 0 && flips < boolPairs && within flips boolPairs 42 58 100)
    s!"adjacent v2 Bool literals are correlated: {flips} of {boolPairs} differ"
  -- Consecutive seeds must not lock their first choice together.
  let steps := (roots.zip roots.tail).map fun (left, right) => (right + 6 - left) % 6
  ensure ((List.range 6).all steps.contains)
    "the root forms of consecutive v2 seeds follow a fixed step"
  ensure (within (steps.filter (· == 0)).length steps.length 10 25 100)
    "consecutive v2 seeds repeat their root form too often or too rarely"

def testCoreSynthesisGeneratorV2 : IO Unit := do
  vectorChecks
  generationChecks
  statisticsChecks

end Tests.CoreSynthesisGeneratorV2
