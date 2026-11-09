import Solcore.Synthesis.Internal.CallGraphs
import Solcore.Core.Machine
import Solcore.Synthesis.Core.Fragment
import Solcore.Synthesis.Core.Generator
import Solcore.Synthesis.Source.Emitter
import Solcore.Synthesis.Core.Seed
import Solcore.Synthesis.Core.Shrink
import Solcore.Synthesis.Internal.Functions
import Solcore.Synthesis.Internal.LanguageFeatures
import Solcore.Synthesis.Internal.Loops
import Solcore.Synthesis.Internal.Aggregates
import Solcore.Synthesis.Internal.Assembly
import Solcore.Synthesis.Internal.Enums
import Solcore.Synthesis.Internal.Traits
import Solcore.Synthesis.Internal.MemoryValues
import Solcore.Synthesis.Internal.MemoryCalls
import Solcore.Synthesis.Internal.RevertData
import Solcore.Synthesis.Internal.Storage
import Solcore.Synthesis.Internal.Calls
import Solcore.Synthesis.Internal.AbiValues
import Solcore.Synthesis.Internal.AdtStorage
import Solcore.Synthesis.Source.Cases

/-!
# Generator tests

The G0 generators and their revisions, seeds, shrinking, swarm masks, identity filters and acceptance.
-/

section
-- leanmerge: from Solcore.Test.CallGraphGenerator
/-! Generator regressions use the original checked Core program. Structural
coverage below describes generated syntax, not measured compiler/EVM traces. -/
set_option autoImplicit false

namespace Tests.CallGraphGenerator

open Solcore.Core
open Solcore.Synthesis.Core

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def generated (seed budget : Nat) : IO CallGraph.Generated :=
  match CallGraph.generate {seed := Seed.ofNat seed, maxProgramNodes := budget} with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"call graph generation failed at {seed}/{budget}: {reprStr error}")

private def invariantChecks (value : CallGraph.Generated) : IO Unit := do
  ensure value.function.program.check "generated function is not accepted by the whole Core checker"
  ensure ((value.function.instantiate Word.maximum).check) "runtime application is not typed"
  ensure (value.nodeCount ≤ value.maxProgramNodes) "actual applied graph exceeds its budget"
  ensure (value.function.helpers.length ≥ 1 && value.function.helpers.length ≤ 3)
    "helper count is outside the supported range"
  ensure (value.bodyBudgets.length == value.function.helpers.length + 1 &&
      value.bodyBudgets.all (· > 0) &&
      value.bodyBudgets.foldl (· + ·) 0 + CallGraph.appliedOverhead value.function.helpers.length ==
        value.maxProgramNodes) "body allocations do not account for the exact whole-program budget"
  for (body, budget) in (value.function.helpers ++ [value.function.entry]).zip value.bodyBudgets do
    ensure (Wire.exprNodes body ≤ budget) "generated body exceeds its assigned expression budget"
  let some decoded := CheckedWordFunctionDAG.ofProgram? value.program |
    throw (IO.userError "generated original program cannot be readmitted")
  ensure (Wire.encodeProgram decoded.program == Wire.encodeProgram value.program)
    "readmission changed the original graph"

private def boundsAndReplay : IO Unit := do
  ensure (CallGraph.version == "core-call-graph-grammar-v1/lcg64-v1") "generator version drift"
  for count in [1, 2, 3] do
    let minimum := CallGraph.minimumAppliedNodes count
    ensure (minimum == CallGraph.appliedOverhead count + count + 1)
      "minimum graph accounting omitted a body or a wrapper"
  ensure ([1, 2, 3].map CallGraph.minimumAppliedNodes == [13, 18, 23] &&
    [1, 2, 3].map CallGraph.appliedOverhead == [11, 15, 19])
    "canonical applied wrapper accounting changed"
  for (seed, finalSeed, count, budgets, nodes) in [
      (0, 10886584781152613473, 2, [33, 6, 42], 59),
      (1, 4158591199845347631, 2, [56, 2, 23], 72),
      (7, 4960277783812433452, 2, [15, 47, 19], 87),
      (31, 7742363979015232405, 1, [68, 17], 67)] do
    let value ← generated seed 96
    ensure (value.finalSeed.toNat == finalSeed && value.function.helpers.length == count &&
      value.bodyBudgets == budgets && value.nodeCount == nodes)
      "versioned choice order or budget distribution changed"
  for budget in [0, CallGraph.minimumAppliedNodes 1 - 1] do
    ensure (match CallGraph.generate {seed := Seed.ofNat 0, maxProgramNodes := budget} with
      | .error .budgetTooSmall => true | _ => false) "undersized budget was not rejected"
  ensure (match CallGraph.generate {seed := Seed.ofNat 0, maxProgramNodes := 513} with
    | .error .budgetTooLarge => true | _ => false) "oversized budget was not rejected"
  for budget in [CallGraph.minimumAppliedNodes 1, 24, 48, 96, 256, 512] do
    for seed in [0, 1, 2, 3, 7, 31, 127, 255, 65535, 2 ^ 64 - 1] do
      let first ← generated seed budget
      let second ← generated seed budget
      invariantChecks first
      ensure (Wire.encodeProgram first.program == Wire.encodeProgram second.program &&
        first.initialSeed == Seed.ofNat seed && first.finalSeed == second.finalSeed &&
        first.bodyBudgets == second.bodyBudgets) "seed replay changed the graph or generation provenance"
  let minimum ← generated 0 (CallGraph.minimumAppliedNodes 1)
  ensure (minimum.nodeCount == CallGraph.minimumAppliedNodes 1) "minimum request was not exact"
  ensure ((CheckedWordFunctionDAG.ofParts? [.apply (.var 1) (.var 0)] (.var 0)).isNone)
    "a helper was allowed to call itself"
  ensure ((CheckedWordFunctionDAG.ofParts? [.var 0] (.apply (.var 2) (.var 0))).isNone)
    "an out-of-scope helper was admitted"

/-- A bounded census of generated ASTs guards against silently reverting to the
old immediate-predecessor chain or fixed aggregate templates. -/
private def structuralDiversity : IO Unit := do
  let mut shapes : List String := []
  let mut features : List String := []
  let mut counts : List Nat := []
  let mut programs : List String := []
  for seed in List.range 256 do
    let value ← generated seed 256
    invariantChecks value
    shapes := (shapes ++ CallGraph.structuralShapes value.function).eraseDups
    features := (features ++ value.features).eraseDups
    counts := (value.function.helpers.length :: counts).eraseDups
    programs := (Wire.encodeProgram value.program).compress :: programs
  for shape in ["skipped-helper", "multiple-callees", "shared-callee", "nested-call",
      "branch-call", "local-call", "diamond", "predicate-call", "primitive-operand-call"] do
    ensure (shapes.contains shape) s!"generated graph census lacks {shape}"
  let scalarFeatures := ["wordLiteral", "boolLiteral", "local", "let", "if"] ++
    (unaryOps.toList.map fun operation => "unary:" ++ reprStr operation) ++
    (binaryOps.toList.map fun operation => "binary:" ++ reprStr operation) ++
    (ternaryOps.toList.map fun operation => "ternary:" ++ reprStr operation)
  for feature in scalarFeatures do
    ensure (features.contains feature) s!"generated scalar grammar lacks {feature}"
  ensure (features.contains "functionCall") "call form was never generated"
  ensure ([1, 2, 3].all counts.contains) "helper counts did not vary"
  ensure (programs.eraseDups.length > 240) "seed census collapsed to too few graph shapes"

private def executionChecks : IO Unit := do
  for seed in [0, 1, 2, 3, 7, 31, 127, 255] do
    let value ← generated seed 96
    let program := value.function.instantiate (Word.ofNatModulo 7)
    match program.toCore.runStateful 0 with
    | .outOfFuel _ => pure ()
    | _ => throw (IO.userError "zero fuel was treated as a completed generated execution")
    match program.toCore.runStateful 100000 with
    | .done (.word _) _ => pure ()
    | .outOfFuel _ => throw (IO.userError "bounded generated execution exhausted its test budget")
    | _ => throw (IO.userError "checked generated graph did not return a Word")

def testCallGraphGenerator : IO Unit := do
  boundsAndReplay
  structuralDiversity
  executionChecks

end Tests.CallGraphGenerator
end

section
-- leanmerge: from Solcore.Test.CoreSynthesisFragment
/-! Focused regressions for the checked Core synthesis fragment. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.Synthesis.Core

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def zero : Wire.Expr :=
  .word Word.zero

private def literalProgram : Wire.Program := {
  resultType := .word
  dataDefinitions := []
  body := zero
}

private def boolResultProgram : Wire.Program := {
  resultType := .bool
  dataDefinitions := []
  body := .bool true
}

private def definitionProgram : Wire.Program := {
  resultType := .word
  dataDefinitions := [{ constructorPayloadTypes := [] }]
  body := zero
}

private def hostProgram : Wire.Program := {
  resultType := .word
  dataDefinitions := []
  body := .apply (.var 0) zero
}

example : accepts .word zero = true := by
  decide

example : accepts .bool (.bool false) = true := by
  decide

example : accepts .word (.var 0) = false := by
  decide

example : acceptsAt 1 .word (.var 0) = true := by
  decide

example : acceptsAt 1 .word (.var 1) = false := by
  decide

example : accepts .bool zero = false := by
  decide

example : accepts .word (.pair zero zero) = false := by
  decide

example : accepts .word (.integer 0) = false := rfl
example : accepts .word (.unary .integerToWord (.integer 0)) = false := rfl
example : accepts .word (.unary .wordToInteger zero) = false := rfl
example : accepts .bool (.binary .integerEq zero zero) = false := rfl

example : literalProgram.check = true := by
  native_decide

private def featureWitness : Feature → Nat × Target × Wire.Expr
  | .wordLiteral => (0, .word, zero)
  | .local => (1, .word, .var 0)
  | .boolLiteral => (0, .bool, .bool true)
  | .letE => (0, .word, .letE zero (.var 0))
  | .ifE => (0, .word, .ifE (.bool true) zero zero)
  | .unary op =>
      let operand := match Target.unaryOperand op with
        | .word => zero
        | .bool => .bool true
      (0, Target.unaryResult op, .unary op operand)
  | .binary op =>
      (0, Target.binaryResult op, .binary op zero zero)
  | .ternary op =>
      (0, .word, .ternary op zero zero zero)

private def featureHasBasicWitness (feature : Feature) : Bool :=
  let (depth, target, expression) := featureWitness feature
  acceptsAt depth target expression && (features expression).contains feature

private def catalogHasNoDuplicates : Bool :=
  Feature.catalog.toList.eraseDups.length == Feature.catalog.size

def testCoreSynthesisFragment : IO Unit := do
  assertTrue (accepts .word zero)
    "the synthesis fragment rejected a Word literal"
  assertTrue (accepts .bool (.bool true))
    "the synthesis fragment rejected a Bool literal"
  assertTrue (acceptsAt 1 .word (.var 0))
    "the synthesis fragment rejected an in-scope Word local"
  assertTrue (!accepts .word (.var 0))
    "the synthesis fragment admitted the first root host variable"
  assertTrue (!acceptsAt 1 .word (.var 1))
    "the synthesis fragment admitted a host variable after a local binder"
  assertTrue (!accepts .bool zero && !accepts .word (.bool true))
    "the synthesis fragment accepted a literal at the wrong target type"
  assertTrue
    (!accepts .word (.unary .boolNot (.bool true)) &&
      !accepts .bool (.binary .wordAdd zero zero))
    "the synthesis fragment accepted an operator at the wrong result type"
  assertTrue
    (!accepts .word (.unit) &&
      !accepts .word (.pair zero zero) &&
      !accepts .word (.apply (.var 0) zero))
    "a constructor outside the synthesis fragment was admitted"
  assertTrue (Feature.catalog.size == 29)
    "the frozen synthesis feature catalog changed size"
  assertTrue catalogHasNoDuplicates
    "the frozen synthesis feature catalog contains a duplicate"
  assertTrue (Feature.catalog.all featureHasBasicWitness)
    "a catalog feature lacks an accepted expression witness"
  match CheckedWordProgram.ofProgram? literalProgram with
  | none =>
      throw (IO.userError "the checked fragment rejected its basic program")
  | some code =>
      assertTrue (code.program.check && accepts .word code.program.body)
        "checked fragment evidence did not retain the admitted program"
  assertTrue (CheckedWordProgram.ofProgram? boolResultProgram).isNone
    "checked fragment admission accepted a non-Word program"
  assertTrue (CheckedWordProgram.ofProgram? definitionProgram).isNone
    "checked fragment admission accepted named-data definitions"
  assertTrue (CheckedWordProgram.ofProgram? hostProgram).isNone
    "checked fragment admission accepted a host expression"

end Tests
end

section
-- leanmerge: from Solcore.Test.CoreSynthesisGenerator
/-! Focused executable regressions for deterministic checked Core generation. -/

set_option autoImplicit false

namespace Tests.CoreSynthesisGenerator

open Solcore.Synthesis.Core

private def request (seed bound : Nat) : GenerationRequest := {
  seed := Seed.ofNat seed
  maxProgramNodes := bound
}

private def rejectsSmallBound (bound : Nat) : Bool :=
  match generate (request 0 bound) with
  | .error .budgetTooSmall => true
  | _ => false

private def minimumBoundIsExact : Bool :=
  match generate (request 0 minimumProgramNodes) with
  | .ok generated =>
      generated.nodeCount == minimumProgramNodes &&
        generated.program.check &&
        accepts .word generated.program.body
  | .error _ => false

private def sameInputIsExact : Bool :=
  match generate (request 37 64), generate (request 37 64) with
  | .ok first, .ok second =>
      first.initialSeed == second.initialSeed &&
        first.finalSeed == second.finalSeed &&
        first.maxProgramNodes == second.maxProgramNodes &&
        Solcore.Core.Wire.encodeProgram first.program ==
          Solcore.Core.Wire.encodeProgram second.program &&
        first.features == second.features
  | _, _ => false

private def bounds : List Nat :=
  [3, 4, 5, 8, 16, 32, 64]

private def corpusIsCheckedAndBounded : Bool :=
  (List.range 128).all fun seedValue =>
    bounds.all fun bound =>
      match generate (request seedValue bound) with
      | .ok generated =>
          generated.initialSeed == Seed.ofNat seedValue &&
            generated.maxProgramNodes == bound &&
            generated.nodeCount ≤ bound &&
            generated.program.check &&
            accepts .word generated.program.body
      | .error _ => false

private def generatedLocalBinder : Bool :=
  (List.range 512).any fun seedValue =>
    match generate (request seedValue 64) with
    | .ok generated =>
        generated.features.contains .letE &&
          generated.features.contains .local
    | .error _ => false

private def allChecks : Bool :=
  rejectsSmallBound 0 && rejectsSmallBound 1 && rejectsSmallBound 2 &&
    minimumBoundIsExact && sameInputIsExact &&
    corpusIsCheckedAndBounded && generatedLocalBinder

private theorem allChecks_exact : allChecks = true := by
  native_decide

def testCoreSynthesisGenerator : IO Unit := do
  unless allChecks do
    throw (IO.userError "Core checked generator changed")

end Tests.CoreSynthesisGenerator
end

section
-- leanmerge: from Solcore.Test.CoreSynthesisGeneratorV2
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
      GeneratorRevision.ofPureVersion? revision.version == some revision)
    "a G0 revision does not round-trip through its version"
  ensure (GeneratorRevision.ofPureVersion? "core-g0-v5/lcg64-v1" == none &&
      GeneratorRevision.ofPureVersion? "core-primitives-v1/core-g0-v2/lcg64-v1" == none)
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
end

section
-- leanmerge: from Solcore.Test.CoreSynthesisGeneratorV3
/-! Executable regressions for revision three of the checked G0 generator:
its swarm masks, their equivalence with revision two under the full mask, and
the shape of masked programs. Revision two's own vectors are pinned by its
tests. -/

set_option autoImplicit false

namespace Tests.CoreSynthesisGeneratorV3

open Solcore.Core (Word)
open Solcore.Core.Wire
open Solcore.Synthesis.Core

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def maskOf (seed : Nat) : FeatureMask := GeneratorRevision.v3.caseMask (Seed.ofNat seed)

private def generated (seed bound : Nat) (revision : GeneratorRevision)
    (mask : FeatureMask := maskOf seed) : IO GeneratedProgram :=
  match generate {seed := Seed.ofNat seed, maxProgramNodes := bound, revision, mask} with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"generation failed: {reprStr error}")

private def indices (mask : FeatureMask) : List Nat :=
  (FeatureMask.catalog.zipIdx.filter fun (feature, _) => mask.allows feature).map (·.2)

private def word (value : Nat) : Expr := .word (Word.ofNatModulo value)

/-- Seed 2 at a 32-node budget: revision two's shape with its mask's operators. -/
private def pinnedBody : Expr :=
  .binary .wordSignExtend (word (2 ^ 32))
    (.unary .wordNot
      (.letE
        (.ternary .wordAddMod
          (word 58776200593107087877498445594665358012522562555746522916260173453486719764460)
          (word 61257103412546197960633691692829092041022166143235981156631755156305019596000)
          (word (2 ^ 192)))
        (word 15059245801192277483352447598272883119367250069704906357382193883813969988912)))

private def vectorChecks : IO Unit := do
  ensure (GeneratorRevision.v3.version == "core-g0-v3/lcg64-v1" &&
      GeneratorRevision.ofVersion? "core-g0-v3/lcg64-v1" == some .v3)
    "the revision-three version changed"
  ensure (FeatureMask.catalog.length == 26 && FeatureMask.catalog.eraseDups.length == 26 &&
      FeatureMask.all.enabled == FeatureMask.catalog &&
      GeneratorRevision.v2.caseMask (Seed.ofNat 5) == FeatureMask.all)
    "the swarm catalog or the full mask changed"
  ensure (indices (maskOf 0) == [0, 1, 4, 6, 8, 11, 13, 17, 18, 19, 21, 24] &&
      indices (maskOf 2) == [0, 1, 2, 3, 5, 7, 8, 9, 10, 14, 15, 16, 17, 20, 22, 24])
    "the swarm mask vector changed"
  ensure ((List.range 64).all fun seed =>
      FeatureMask.ofFeatures? (maskOf seed).enabled == some (maskOf seed) &&
        FeatureMask.ofBits (2 ^ 26 - 1) == FeatureMask.all)
    "a swarm mask is not canonical"
  ensure (FeatureMask.ofFeatures? [.ifE, .letE] == none &&
      FeatureMask.ofFeatures? [.letE, .letE] == none && FeatureMask.ofFeatures? [.wordLiteral] == none)
    "a noncanonical mask was accepted"
  let pinned ← generated 2 32 .v3
  ensure (pinned.finalSeed == Seed.ofUInt64 10927198619237024990 && pinned.nodeCount == 11 &&
      pinned.mask == maskOf 2 &&
      encodeProgram pinned.program ==
        encodeProgram {resultType := .word, dataDefinitions := [], body := pinnedBody})
    "the pinned revision-three program changed"

private def bounds : List Nat := [3, 4, 5, 8, 16, 32, 64]

private def generationChecks : IO Unit := do
  let mut redirected := false
  for seed in List.range 128 do
    for bound in bounds do
      let value ← generated seed bound .v3
      ensure (value.nodeCount ≤ bound && value.program.check && accepts .word value.program.body &&
          value.revision == .v3 && value.mask == maskOf seed)
        "a revision-three program escaped its checked budget"
      ensure (value.features.all fun feature =>
          feature matches .wordLiteral | .local | .boolLiteral || (maskOf seed).allows feature)
        "a revision-three program used a feature its mask disables"
      -- The full mask is revision two itself.
      let full ← generated seed bound .v3 FeatureMask.all
      let two ← generated seed bound .v2
      ensure (encodeProgram full.program == encodeProgram two.program && full.finalSeed == two.finalSeed)
        "revision three under the full mask differs from revision two"
      redirected := redirected || value.finalSeed != two.finalSeed
  ensure redirected "no mask ever replaced a disabled form"
  let first ← generated 37 64 .v3
  let second ← generated 37 64 .v3
  ensure (encodeProgram first.program == encodeProgram second.program &&
      first.finalSeed == second.finalSeed && first.mask == second.mask)
    "revision three is not deterministic"

private def head : Expr → Option Feature
  | .unary op _ => some (.unary op)
  | .binary op _ _ => some (.binary op)
  | .ternary op _ _ _ => some (.ternary op)
  | .letE _ _ => some .letE
  | .ifE _ _ _ => some .ifE
  | _ => none

private def pairs (parent : Feature) (children : List Expr) : List (Feature × Feature) :=
  children.filterMap fun child => (head child).map (parent, ·)

/-- Operators with their nesting depth, and parent-child operator pairs. -/
private def shape : Nat → Expr → List (Feature × Nat) × List (Feature × Feature)
  | depth, .unary op operand =>
      let (operators, children) := shape (depth + 1) operand
      ((.unary op, depth) :: operators, pairs (.unary op) [operand] ++ children)
  | depth, .binary op left right =>
      let (leftOperators, leftPairs) := shape (depth + 1) left
      let (rightOperators, rightPairs) := shape (depth + 1) right
      ((.binary op, depth) :: leftOperators ++ rightOperators,
        pairs (.binary op) [left, right] ++ leftPairs ++ rightPairs)
  | depth, .ternary op first second third =>
      let (firstOperators, firstPairs) := shape (depth + 1) first
      let (secondOperators, secondPairs) := shape (depth + 1) second
      let (thirdOperators, thirdPairs) := shape (depth + 1) third
      ((.ternary op, depth) :: firstOperators ++ secondOperators ++ thirdOperators,
        pairs (.ternary op) [first, second, third] ++ firstPairs ++ secondPairs ++ thirdPairs)
  | depth, .letE value body =>
      let (valueOperators, valuePairs) := shape (depth + 1) value
      let (bodyOperators, bodyPairs) := shape (depth + 1) body
      ((.letE, depth) :: valueOperators ++ bodyOperators,
        pairs .letE [value, body] ++ valuePairs ++ bodyPairs)
  | depth, .ifE condition thenBranch elseBranch =>
      let (conditionOperators, conditionPairs) := shape (depth + 1) condition
      let (thenOperators, thenPairs) := shape (depth + 1) thenBranch
      let (elseOperators, elsePairs) := shape (depth + 1) elseBranch
      ((.ifE, depth) :: conditionOperators ++ thenOperators ++ elseOperators,
        pairs .ifE [condition, thenBranch, elseBranch] ++ conditionPairs ++ thenPairs ++ elsePairs)
  | _, _ => ([], [])

private structure Totals where
  operators : Nat := 0
  distinct : Nat := 0
  repeated : Nat := 0
  depth : Nat := 0
  /-- An operator directly inside the same operator, other than `let` in `let`. -/
  selfNested : Nat := 0
  seen : List Feature := []
  pairs : List (Feature × Feature) := []

/-- 1,024 consecutive seeds at a 32-node budget. -/
private def totals (revision : GeneratorRevision) : IO Totals := do
  let mut result : Totals := {}
  for seed in List.range 1024 do
    let (operators, pairs) := shape 1 (← generated seed 32 revision).program.body
    let names := (operators.map (·.1)).eraseDups
    result := {
      operators := result.operators + operators.length
      distinct := result.distinct + names.length
      repeated := result.repeated +
        if names.any (fun name => (operators.filter (·.1 == name)).length ≥ 3) then 1 else 0
      depth := result.depth + (operators.map (·.2)).foldl max 0
      selfNested := result.selfNested +
        (pairs.filter fun (parent, child) => parent == child && parent != .letE).length
      seen := (result.seen ++ names).eraseDups
      pairs := (result.pairs ++ pairs).eraseDups }
  return result

/-- Masks enable about half of the catalog; masked programs keep revision two's
size and depth while combining fewer distinct operators, each more often and
more often inside itself, and the sample as a whole holds more operator pairs. -/
private def statisticsChecks : IO Unit := do
  let masks := (List.range 2048).map maskOf
  for feature in FeatureMask.catalog do
    let count := (masks.filter (·.allows feature)).length
    ensure (900 ≤ count && count ≤ 1148) s!"a catalog feature is enabled in {count} of 2048 masks"
  let two ← totals .v2
  let three ← totals .v3
  ensure (three.seen.length == 26 && two.seen.length == 26)
    "a catalog feature never appeared in 1,024 programs"
  ensure (10 * three.operators ≥ 9 * two.operators && 10 * three.depth ≥ 9 * two.depth)
    s!"masked programs shrank: {three.operators} against {two.operators} operators"
  ensure (10 * three.distinct ≤ 9 * two.distinct)
    s!"masked programs do not combine fewer operators: {three.distinct} against {two.distinct}"
  ensure (three.repeated > two.repeated)
    s!"masked programs do not repeat operators more often: {three.repeated} against {two.repeated}"
  ensure (2 * three.selfNested ≥ 3 * two.selfNested)
    s!"masked programs nest an operator in itself {three.selfNested} times against {two.selfNested}"
  ensure (three.pairs.length > two.pairs.length)
    s!"masked programs hold {three.pairs.length} operator pairs against {two.pairs.length}"

def testCoreSynthesisGeneratorV3 : IO Unit := do
  vectorChecks
  generationChecks
  statisticsChecks

end Tests.CoreSynthesisGeneratorV3
end

section
-- leanmerge: from Solcore.Test.CoreSynthesisGeneratorV4
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
end

section
-- leanmerge: from Solcore.Test.CoreSynthesisSeed
/-! Focused replay-contract regressions for Core synthesis seeds. -/

set_option autoImplicit false

namespace Tests.CoreSynthesisSeed

open Solcore.Synthesis.Core

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def drawValues : Nat → Seed → List UInt64
  | 0, _ => []
  | count + 1, seed =>
      let (value, next) := seed.draw
      value :: drawValues count next

private def chooseValues : List Nat → Seed → List Nat × Seed
  | [], seed => ([], seed)
  | bound :: bounds, seed =>
      let (value, next) := seed.choose bound
      let (values, finalSeed) := chooseValues bounds next
      (value :: values, finalSeed)

private def seedZeroVector : List UInt64 := [
  1442695040888963407,
  1876011003808476466,
  11166244414315200793,
  7401132627792533940,
  7076646890315895283,
  10346034117385188870
]

example : drawValues 6 (Seed.ofNat 0) = seedZeroVector := by
  native_decide

example :
    (Seed.ofNat 42).choose 0 =
      (0, Seed.ofUInt64 10481999410520546993) := by
  native_decide

private def replayBounds : List Nat := [1, 2, 3, 17, 0, 65537]

private def replayFrom42 : List Nat × Seed :=
  chooseValues replayBounds (Seed.ofNat 42)

example :
    replayFrom42 =
      ([0, 0, 2, 12, 0, 19656], Seed.ofUInt64 483838003013946848) := by
  native_decide

def testCoreSynthesisSeed : IO Unit := do
  assertTrue
    (drawValues 6 (Seed.ofNat 0) == seedZeroVector)
    "the lcg64-v1 exact draw vector changed"
  assertTrue
    ((Seed.ofNat 42).choose 0 ==
      (0, Seed.ofUInt64 10481999410520546993))
    "a zero-bound choice did not consume exactly one draw"
  assertTrue
    (replayFrom42 ==
      ([0, 0, 2, 12, 0, 19656], Seed.ofUInt64 483838003013946848))
    "the lcg64-v1 bounded-choice vector changed"

end Tests.CoreSynthesisSeed
end

section
-- leanmerge: from Solcore.Test.CoreSynthesisShrink
/-! Focused regressions for deterministic checked Core shrinking. -/

set_option autoImplicit false

namespace Tests.CoreSynthesisShrink

open Solcore.Core
open Solcore.Synthesis.Core

private def word (value : Nat) : Wire.Expr :=
  .word (Word.ofNatModulo value)

private def program (body : Wire.Expr) : Wire.Program := {
  resultType := .word
  dataDefinitions := []
  body
}

private def admitProgram (body : Wire.Expr) : Option CheckedWordProgram :=
  CheckedWordProgram.ofProgram? (program body)

private def bodyKey (body : Wire.Expr) : String :=
  (Wire.encodeExpr body).compress

private def candidateKeys (candidates : List ShrinkCandidate) : List String :=
  candidates.map fun candidate => bodyKey candidate.body

private def allUnique : List String → Bool
  | [] => true
  | key :: rest => !rest.contains key && allUnique rest

private def hasBody
    (expected : Wire.Expr)
    (candidates : List ShrinkCandidate) : Bool :=
  (candidateKeys candidates).contains (bodyKey expected)

private def everyCandidateValid
    (source : CheckedWordProgram)
    (candidates : List ShrinkCandidate) : Bool :=
  candidates.all fun candidate =>
    candidate.checkedProgram.program.check &&
      accepts .word candidate.body &&
      candidate.candidateComplexity.isStrictlySmaller
        candidate.sourceComplexity &&
      candidate.sourceComplexity == complexity source.program.body &&
      candidate.candidateComplexity == complexity candidate.body &&
      candidate.candidateComplexity.exprNodes ≤
        candidate.sourceComplexity.exprNodes

private def nonzeroShrinksToZero : Bool :=
  match admitProgram (word 9) with
  | none => false
  | some source =>
      let candidates := shrink source
      candidates.length = 1 &&
        hasBody (word 0) candidates &&
        everyCandidateValid source candidates

private def compoundBody : Wire.Expr :=
  .letE (word 7)
    (.ifE
      (.binary .wordEq (.var 0) (word 3))
      (.binary .wordAdd (.var 0) (word 9))
      (.unary .wordNot (word 2)))

private def isTopLet : Wire.Expr → Bool
  | .letE _ _ => true
  | _ => false

private def containsTopLetAndInnerOp
    (candidates : List ShrinkCandidate) : Bool :=
  candidates.any fun candidate =>
    isTopLet candidate.body &&
      (features candidate.body).contains (.binary .wordAdd)

private def compoundCandidatesRespectBoundary : Bool :=
  match admitProgram compoundBody with
  | none => false
  | some source =>
      let candidates := shrink source
      !candidates.isEmpty &&
        hasBody (word 0) candidates &&
        containsTopLetAndInnerOp candidates &&
        everyCandidateValid source candidates

private def captureBody : Wire.Expr :=
  .letE (word 1) (.var 0)

private def captureCandidateIsRejected : Bool :=
  match admitProgram captureBody with
  | none => false
  | some source =>
      let candidates := shrink source
      !(hasBody (.var 0) candidates) &&
        everyCandidateValid source candidates

private def nestedCaptureBody : Wire.Expr :=
  .letE (word 9) (.letE (word 1) (.var 0))

private def nestedCaptureIsRejected : Bool :=
  match admitProgram nestedCaptureBody with
  | none => false
  | some source =>
      let candidates := shrink source
      !(hasBody (.letE (word 9) (.var 0)) candidates) &&
        everyCandidateValid source candidates

private def unusedBinderBody : Wire.Expr :=
  .letE (word 9) (.letE (word 1) (.var 1))

private def unusedBinderIsLowered : Bool :=
  match admitProgram unusedBinderBody with
  | none => false
  | some source =>
      let candidates := shrink source
      hasBody (.letE (word 9) (.var 0)) candidates &&
        everyCandidateValid source candidates

private def determinismOrderAndDedup : Bool :=
  match admitProgram compoundBody with
  | none => false
  | some source =>
      let first := candidateKeys (shrink source)
      let second := candidateKeys (shrink source)
      first == second &&
        first.head? == some (bodyKey (word 0)) &&
        allUnique first

private def literalWeightIsExact : Bool :=
  literalWeight (.ifE (.bool true) (word 5) (word 7)) = 13 &&
    complexity (word 9) == { exprNodes := 1, literalWeight := 9 }

private def allChecks : Bool :=
  nonzeroShrinksToZero &&
    compoundCandidatesRespectBoundary &&
    captureCandidateIsRejected &&
    nestedCaptureIsRejected &&
    unusedBinderIsLowered &&
    determinismOrderAndDedup &&
    literalWeightIsExact

private theorem allChecks_exact : allChecks = true := by
  native_decide

def testCoreSynthesisShrink : IO Unit := do
  unless allChecks do
    throw (IO.userError "Core checked shrinker changed")

end Tests.CoreSynthesisShrink
end

section
-- leanmerge: from Solcore.Test.SourceAcceptanceCases
/-! The identity filter `exclude-boundary-identity-v1` of the eighteen runtime-input
profiles whose generated functions can be identities. Over a window of
attempts it excludes exactly the functions that return every boundary input
unchanged, under its own reason and code, and keeps every other function with
all of its cases. Filtered cases record the filter, replay exactly, compose
with seeded inputs and leave their reductions unfiltered; a saved identity
cannot claim the filter. The loop profiles already exclude identities, and a
generic selection returns equal or adjacent Words for inputs 0 and 1. -/
set_option autoImplicit false

namespace Tests.SourceAcceptanceCases

open Lean
open Solcore.Core (Word)
open Solcore.Synthesis.Core
open Solcore.Synthesis.Source

private def get {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def errorOf {α : Type} : Except String α → Option String
  | .error error => some error
  | .ok _ => none

private structure Profile where
  name : String
  generate : Seed → Nat → Nat → Nat → Nat → InputSelection → Acceptance → Json
  replay : Json → Nat → Except String Json
  shrink : Json → Nat → Nat → Except String Json
  nodes : Nat
  /-- Boundary inputs per function. -/
  inputs : Nat
  /-- A seed whose function is a boundary identity under the profile's own filters. -/
  identity : Option Nat

private def profiles : List Profile := [
  {name := "runtime-word", generate := fun seed nodes count attempts fuel inputs acceptance =>
      Input.generateCases seed nodes count attempts fuel .v4 inputs acceptance,
    replay := Input.replayCase, shrink := Input.shrinkCases, nodes := 32, inputs := 4, identity := some 8},
  {name := "runtime-primitives", generate := fun seed nodes count attempts fuel inputs acceptance =>
      Primitive.generateCases seed nodes count attempts fuel .v4 inputs acceptance,
    replay := Primitive.replayCase, shrink := Primitive.shrinkCases, nodes := 96, inputs := 8,
    identity := some 8},
  {name := "runtime-assembly", generate := fun seed nodes count attempts fuel inputs acceptance =>
      Assembly.generateCases seed nodes count attempts fuel .v4 inputs acceptance,
    replay := Assembly.replayCase, shrink := Assembly.shrinkCases, nodes := 96, inputs := 8,
    identity := some 8},
  {name := "runtime-assembly-memory", generate := fun seed nodes count attempts fuel inputs acceptance =>
      AssemblyMemory.generateCases seed nodes count attempts fuel .v4 inputs acceptance,
    replay := AssemblyMemory.replayCase, shrink := AssemblyMemory.shrinkCases, nodes := 96, inputs := 8,
    identity := some 108},
  {name := "runtime-functions", generate := fun seed nodes count attempts fuel inputs acceptance =>
      Solcore.Synthesis.Source.Function.generateCases seed nodes count attempts fuel .v4 inputs acceptance,
    replay := Solcore.Synthesis.Source.Function.replayCase, shrink := Solcore.Synthesis.Source.Function.shrinkCases,
    nodes := 32, inputs := 4, identity := some 12},
  {name := "runtime-mutation", generate := fun seed nodes count attempts fuel inputs acceptance =>
      Mutation.generateCases seed nodes count attempts fuel .v4 inputs acceptance,
    replay := Mutation.replayCase, shrink := Mutation.shrinkCases, nodes := 192, inputs := 4,
    identity := some 184},
  {name := "runtime-aggregates", generate := fun seed nodes count attempts fuel inputs acceptance =>
      Aggregate.generateCases seed nodes count attempts fuel .v4 inputs acceptance,
    replay := Aggregate.replayCase, shrink := Aggregate.shrinkCases, nodes := 256, inputs := 4,
    identity := some 3},
  {name := "runtime-closures", generate := fun seed nodes count attempts fuel inputs acceptance =>
      Closure.generateCases seed nodes count attempts fuel .v4 inputs acceptance,
    replay := Closure.replayCase, shrink := Closure.shrinkCases, nodes := 384, inputs := 4, identity := none},
  {name := "runtime-comptime", generate := fun seed nodes count attempts fuel inputs acceptance =>
      Comptime.generateCases seed nodes count attempts fuel .v4 inputs acceptance,
    replay := Comptime.replayCase, shrink := Comptime.shrinkCases, nodes := 384, inputs := 4,
    identity := some 60},
  {name := "runtime-modules", generate := fun seed nodes count attempts fuel inputs acceptance =>
      Modules.generateCases seed nodes count attempts fuel .v4 inputs acceptance,
    replay := Modules.replayCase, shrink := Modules.shrinkCases, nodes := 384, inputs := 4, identity := none},
  {name := "runtime-call-graphs", generate := fun seed nodes count attempts fuel inputs acceptance =>
      CallGraph.generateCases seed nodes count attempts fuel inputs acceptance,
    replay := CallGraph.replayCase, shrink := CallGraph.shrinkCases, nodes := 192, inputs := 8,
    identity := some 2},
  {name := "runtime-aggregate-call-graphs", generate := fun seed nodes count attempts fuel inputs acceptance =>
      AggregateCallGraph.generateCases seed nodes count attempts fuel inputs acceptance,
    replay := AggregateCallGraph.replayCase, shrink := AggregateCallGraph.shrinkCases, nodes := 192,
    inputs := 8, identity := some 5},
  {name := "runtime-enums", generate := fun seed nodes count attempts fuel inputs acceptance =>
      Enums.generateCases seed nodes count attempts fuel inputs acceptance,
    replay := Enums.replayCase, shrink := Enums.shrinkCases, nodes := 2048, inputs := 8, identity := none},
  {name := "runtime-traits", generate := fun seed nodes count attempts fuel inputs acceptance =>
      Traits.generateCases seed nodes count attempts fuel inputs acceptance,
    replay := Traits.replayCase, shrink := Traits.shrinkCases, nodes := 2048, inputs := 8, identity := none},
  {name := "runtime-trait-hierarchies", generate := fun seed nodes count attempts fuel inputs acceptance =>
      Hierarchies.generateCases seed nodes count attempts fuel inputs acceptance,
    replay := Hierarchies.replayCase, shrink := Hierarchies.shrinkCases, nodes := 2048, inputs := 8,
    identity := none},
  {name := "runtime-memory-values", generate := fun seed nodes count attempts fuel inputs acceptance =>
      MemoryValues.generateCases seed nodes count attempts fuel inputs acceptance,
    replay := MemoryValues.replayCase, shrink := MemoryValues.shrinkCases, nodes := 1024, inputs := 8,
    identity := some 29},
  {name := "runtime-memory-calls", generate := fun seed nodes count attempts fuel inputs acceptance =>
      MemoryCalls.generateCases seed nodes count attempts fuel inputs acceptance,
    replay := MemoryCalls.replayCase, shrink := MemoryCalls.shrinkCases, nodes := 1024, inputs := 8,
    identity := some 19},
  {name := "runtime-revert-data", generate := fun seed nodes count attempts fuel inputs acceptance =>
      RevertData.generateCases seed nodes count attempts fuel inputs acceptance,
    replay := RevertData.replayCase, shrink := RevertData.shrinkCases, nodes := 1024, inputs := 8,
    identity := some 273}]

private def fuel : Nat := 1000000

/-- Every function of one window is returned, so the two filters compare whole. -/
private def window : Nat := 24

private def cases (corpus : Json) : IO (Array Json) :=
  get (corpus.getObjValAs? (Array Json) "cases")

private def excluded (corpus : Json) : IO (Array Json) :=
  get (corpus.getObjValAs? (Array Json) "excluded")

private def origin (case : Json) : IO Json := do
  get ((← get (case.getObjVal? "provenance")).getObjVal? "origin")

private def withOrigin (case : Json) (change : Json → Json) : IO Json := do
  let provenance ← get (case.getObjVal? "provenance")
  return case.setObjVal! "provenance" (provenance.setObjVal! "origin" (change (← origin case)))

private def withoutAcceptance : Json → Json
  | .obj fields => .obj (fields.erase "acceptance")
  | other => other

/-- One accepted function yields its inputs consecutively, in input order. -/
private def functions (all : Array Json) (size : Nat) : List (Array Json) :=
  (List.range (all.size / size)).map fun index => all.extract (index * size) ((index + 1) * size)

/-- The function returned each of these inputs unchanged; a reverted case,
which only `runtime-memory-values`, `runtime-memory-calls` and
`runtime-revert-data` observe, is never part of one. -/
private def isIdentity (function : Array Json) : IO Bool := do
  for case in function do
    let input ← get (case.getObjValAs? String "input")
    let direct ← get (case.getObjVal? "directCore")
    unless (direct.getObjValAs? String "status").toOption == some "returned" do return false
    let result ← get (direct.getObjValAs? String "word")
    unless input == result do return false
  return true

private def reason (entry : Json) : String :=
  (entry.getObjValAs? String "reason").toOption.getD ""

private def checkWindow (profile : Profile) : IO Unit := do
  let generate := fun acceptance =>
    profile.generate (Seed.ofNat 1) profile.nodes 1024 window fuel .boundary acceptance
  let (unfiltered, filtered) := (generate .profile, generate .nonIdentity)
  let all ← cases unfiltered
  ensure (all.size % profile.inputs == 0) s!"{profile.name}: a function lost some of its boundary inputs"
  let mut kept : Array Json := #[]
  let mut identities := 0
  for function in functions all profile.inputs do
    if ← isIdentity function then identities := identities + 1 else kept := kept ++ function
  let accepted ← cases filtered
  ensure ((← accepted.mapM fun case => withOrigin case withoutAcceptance) == kept)
    s!"{profile.name}: the filter did not keep exactly the functions that change a boundary input"
  let before ← excluded unfiltered
  let after ← excluded filtered
  let identityEntries := after.filter (reason · == Acceptance.identityReason)
  ensure (identityEntries.size == identities && after.filter (reason · != Acceptance.identityReason) == before)
    s!"{profile.name}: the filter excluded something other than the boundary identities"
  for entry in identityEntries do
    ensure ((entry.getObjValAs? String "code").toOption == some "boundary-identity" &&
        (entry.getObjValAs? String "category").toOption == some "excluded")
      s!"{profile.name}: an identity exclusion lacks its own code"
  if let some seed := profile.identity then
    if seed ≤ window then
      ensure (identities > 0) s!"{profile.name}: the window holds no identity to exclude"
  for case in accepted.extract 0 (2 * profile.inputs) do
    ensure (((← origin case).getObjValAs? String "acceptance").toOption == some Acceptance.nonIdentityVersion)
      s!"{profile.name}: a filtered case does not record its filter"
    ensure ((← get (profile.replay case fuel)) == case) s!"{profile.name}: a filtered case failed exact replay"
    let unlabeled ← withOrigin case withoutAcceptance
    ensure ((← get (profile.replay unlabeled fuel)) == unlabeled)
      s!"{profile.name}: a filtered case is not also a case of the profile's own filters"
    let unknown ← withOrigin case (·.setObjVal! "acceptance" (toJson "exclude-boundary-identity-v9"))
    ensure (errorOf (profile.replay unknown fuel) == some "unsupported acceptance filter")
      s!"{profile.name}: an unknown acceptance filter replayed"

/-- A function that returns every boundary input is excluded under the filter
alone, and its saved unfiltered case cannot claim the filter. -/
private def checkIdentity (profile : Profile) (seed : Nat) : IO Unit := do
  let generate := fun acceptance =>
    profile.generate (Seed.ofNat seed) profile.nodes profile.inputs 1 fuel .boundary acceptance
  let identity ← cases (generate .profile)
  ensure (identity.size == profile.inputs && (← isIdentity identity))
    s!"{profile.name}: seed {seed} is not a boundary identity of the profile's own filters"
  let filtered := generate .nonIdentity
  ensure ((← cases filtered).isEmpty && ((← excluded filtered).map reason) == #[Acceptance.identityReason])
    s!"{profile.name}: the filter did not exclude the identity of seed {seed}"
  for case in identity do
    let claimed ← withOrigin case (·.setObjVal! "acceptance" (toJson Acceptance.nonIdentityVersion))
    ensure (errorOf (profile.replay claimed fuel) == some Acceptance.identityReason)
      s!"{profile.name}: a saved identity replayed under the filter"

/-- Seeded inputs follow the boundary inputs; reductions are never filtered. -/
private def checkSeededAndReductions (profile : Profile) : IO Unit := do
  let seeded ← cases (profile.generate (Seed.ofNat 1) profile.nodes (profile.inputs + 4) 64 fuel .seeded .nonIdentity)
  ensure (seeded.size == profile.inputs + 4) s!"{profile.name}: seeded filtered generation did not complete"
  for case in seeded do
    let saved ← origin case
    ensure ((saved.getObjValAs? String "acceptance").toOption == some Acceptance.nonIdentityVersion &&
        (saved.getObjValAs? String "inputSelection").toOption == some InputSelection.seededVersion)
      s!"{profile.name}: a seeded filtered case does not record both choices"
    ensure ((← get (profile.replay case fuel)) == case) s!"{profile.name}: a seeded filtered case failed exact replay"
  let some first := seeded[0]? | throw (IO.userError s!"{profile.name}: no filtered case")
  let reduced ← cases (← get (profile.shrink first 3 fuel))
  ensure (!reduced.isEmpty) s!"{profile.name}: a filtered case has no reduction candidate"
  for candidate in reduced do
    let saved ← origin candidate
    ensure ((saved.getObjValAs? String "kind").toOption == some "reduced" &&
        (saved.getObjVal? "acceptance").toOption.isNone)
      s!"{profile.name}: a reduction carries the acceptance filter"
    ensure ((← get (profile.replay candidate fuel)) == candidate)
      s!"{profile.name}: a reduction of a filtered case failed exact replay"

private def resultWord (case : Json) : IO Nat := do
  let text ← get ((← get (case.getObjVal? "directCore")).getObjValAs? String "word")
  let some value := text.toNat? | throw (IO.userError "invalid result Word")
  return value

/-- The profiles left unchanged: every loop changes a positive-trip boundary
input, so none is an identity, and a generic function returns `f 1` or
`f 1 + 1` for input 0, so it cannot return both 0 and 1. -/
private def unchangedProfiles : IO Unit := do
  for (name, corpus, size) in [
      ("runtime-loops", Loop.generateCases (Seed.ofNat 1) 384 1024 window fuel .v4, 6),
      ("runtime-call-graph-loops", CallGraphLoop.generateCases (Seed.ofNat 1) 256 1024 (4 * window) fuel, 6)] do
    let all ← cases corpus
    ensure (all.size ≥ 4 * size) s!"{name}: too few loops to check"
    for function in functions all size do
      ensure (!(← isIdentity function)) s!"{name}: a generated loop returned every boundary input"
  let generic ← cases (Generic.generateCases (Seed.ofNat 1) 384 1024 window fuel .v4)
  ensure (generic.size ≥ 16) "runtime-generics: too few functions to check"
  for function in functions generic 4 do
    let (atZero, atOne) := (← resultWord function[0]!, ← resultWord function[1]!)
    ensure (atZero == atOne || atZero == (atOne + 1) % 2 ^ 256)
      "runtime-generics: input 0 returned neither the result of input 1 nor its successor"

private def acceptanceChecks : IO Unit := do
  ensure (Acceptance.ofVersion? Acceptance.nonIdentityVersion == some .nonIdentity &&
      Acceptance.ofVersion? "profile" == none) "acceptance filter versions changed"
  let origin := Json.mkObj [("kind", toJson "input-generated")]
  ensure ((Acceptance.ofOrigin origin).toOption == some .profile && Acceptance.record .profile origin == origin &&
      (Acceptance.ofOrigin (Acceptance.record .nonIdentity origin)).toOption == some .nonIdentity &&
      errorOf (Acceptance.ofOrigin (origin.setObjVal! "acceptance" (toJson (1 : Nat)))) ==
        some "unsupported acceptance filter")
    "acceptance filters do not round-trip through an origin"
  let inputs := [Word.zero, Word.ofNatModulo 1]
  ensure (errorOf (Acceptance.check .nonIdentity inputs inputs) == some Acceptance.identityReason &&
      errorOf (Acceptance.check .nonIdentity inputs [Word.zero, Word.zero]) == none &&
      errorOf (Acceptance.check .profile inputs inputs) == none) "the identity filter decides the wrong functions"

def testSourceAcceptanceCases : IO Unit := do
  acceptanceChecks
  ensure (profiles.length == 18) "a profile whose functions can be identities is missing"
  for profile in profiles do
    checkWindow profile
    if let some seed := profile.identity then checkIdentity profile seed
    checkSeededAndReductions profile
  unchangedProfiles

end Tests.SourceAcceptanceCases
end

section
-- leanmerge: from Solcore.Test.SourceEmitterSupportCases
/-! The G0 features each pure profile declares are exactly those its emitter
renders: a probe program for each catalog feature emits if and only if the
feature is declared. Revision four restricts swarm masks to these sets. -/
set_option autoImplicit false

namespace Tests.SourceEmitterSupportCases

open Solcore.Core.Wire
open Solcore.Synthesis.Core
open Solcore.Synthesis.Source

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def word (value : Nat) : Expr := .word (Solcore.Core.Word.ofNatModulo value)

private def comparison : BinaryOp → Bool
  | .wordEq | .wordGt | .wordSgt => true
  | _ => false

/-- A Word expression over `argument` whose only operator or form is `feature`,
except that a Bool-valued feature selects between two Words with `if`. -/
private def probe (argument : Expr) : Feature → Expr
  | .unary .boolNot => .ifE (.unary .boolNot (.bool true)) argument (word 1)
  | .unary operation => .unary operation argument
  | .binary operation =>
      if comparison operation then .ifE (.binary operation argument (word 3)) argument (word 1)
      else .binary operation argument (word 3)
  | .ternary operation => .ternary operation argument (word 2) (word 3)
  | .letE => .letE argument (.var 0)
  | .ifE => .ifE (.bool true) argument (word 1)
  | _ => argument

private def emits {ε α : Type} (result : Except ε α) : Bool := result matches .ok _

private def closed (body : Expr) : Option CheckedWordProgram :=
  CheckedWordProgram.ofProgram? {resultType := .word, dataDefinitions := [], body}

/-- The entry of a one-helper graph applies the helper to the input. -/
private def entry : Expr := .apply (.var 1) (.var 0)

private def step (helper : Expr) : Option Aggregates.CheckedDAG := Aggregates.CheckedDAG.ofParts? [helper] entry

private def fixedConstant : Option CheckedWordProgram := closed (.binary .wordAdd (word 1) (word 2))

private def fixedStep : Option Aggregates.CheckedDAG := step (.binary .wordAdd (.var 0) (word 1))

/-- Two stages, one with each width, an unaligned final read and a 33-byte hash. -/
private def memorySchedule : AssemblyMemory.Schedule :=
  {stages := [⟨7, .word, 13⟩, ⟨40, .byte, 70⟩], final := 33, hash := some ⟨5, 33⟩}

private structure Profile where
  name : String
  support : FeatureMask
  /-- Whether the emitter renders the probe of a feature; none when the probe
  itself fails the profile's checker. -/
  emits : Feature → Option Bool

private def profiles : List Profile := [
  ⟨"closed-g0", featureSupport, fun feature =>
    (closed (probe (word 5) feature)).map (emits ∘ emit)⟩,
  ⟨"runtime-word", Input.featureSupport, fun feature =>
    (CheckedWordFunction.ofBody? (probe (.var 0) feature)).map (emits ∘ Input.emit)⟩,
  ⟨"runtime-primitives", Primitive.featureSupport, fun feature =>
    (CheckedWordFunction.ofBody? (probe (.var 0) feature)).map (emits ∘ Primitive.emit)⟩,
  ⟨"runtime-assembly switch", Assembly.featureSupport, fun feature =>
    (CheckedWordFunction.ofBody? (probe (.var 0) feature)).map (emits ∘ Assembly.emit .switch)⟩,
  ⟨"runtime-assembly if", Assembly.featureSupport, fun feature =>
    (CheckedWordFunction.ofBody? (probe (.var 0) feature)).map (emits ∘ Assembly.emit .branches)⟩,
  ⟨"runtime-assembly operations", Assembly.featureSupport, fun feature =>
    (CheckedWordFunction.ofBody? (probe (.var 0) feature)).map (emits ∘ Assembly.emit .operations)⟩,
  ⟨"runtime-assembly-memory", AssemblyMemory.featureSupport, fun feature =>
    (CheckedWordFunction.ofBody? (probe (.var 0) feature)).map fun function =>
      emits (AssemblyMemory.emit function memorySchedule)⟩,
  ⟨"runtime-functions", Solcore.Synthesis.Source.Function.featureSupport, fun feature =>
    (CheckedWordFunctionDAG.ofParts? [probe (.var 0) feature] entry).map
      (emits ∘ Solcore.Synthesis.Source.Function.emit)⟩,
  ⟨"runtime-mutation", Mutation.featureSupport, fun feature =>
    (LocalMutation.CheckedDAG.ofParts? [probe (.var 0) feature] entry).map (emits ∘ Mutation.emit)⟩,
  ⟨"runtime-aggregates", Aggregate.featureSupport, fun feature =>
    (step (probe (.var 0) feature)).map (emits ∘ Aggregate.emit)⟩,
  ⟨"runtime-loops", Loop.featureSupport, fun feature => do
    let plan ← BoundedLoop.CheckedPlan.ofParts? (← step (probe (.var 0) feature)) 3
    return emits (Loop.emit plan)⟩,
  ⟨"runtime-nested-loops", NestedLoop.featureSupport, fun feature => do
    let plan ← Solcore.Synthesis.Core.NestedLoop.CheckedPlan.ofParts? (← step (probe (.var 0) feature)) 3 3
      .accumulator
    return emits (NestedLoop.emit plan)⟩,
  ⟨"runtime-recursion", Recursion.featureSupport, fun feature => do
    let plan ← Solcore.Synthesis.Core.Recursion.CheckedPlan.ofParts? (← step (probe (.var 0) feature)) 7 .mutual
    return emits (Recursion.emit plan)⟩,
  ⟨"runtime-recursive-loops", RecursiveLoop.featureSupport, fun feature => do
    let plan ← Solcore.Synthesis.Core.RecursiveLoop.CheckedPlan.ofParts? (← step (probe (.var 0) feature)) 3 3 .mutual
    return emits (RecursiveLoop.emit plan)⟩,
  ⟨"runtime-loop-closures", LoopClosure.featureSupport, fun feature => do
    let plan ← Solcore.Synthesis.Core.LoopClosure.CheckedPlan.ofParts? (← step (probe (.var 0) feature)) 7 .counter
    return emits (LoopClosure.emit plan)⟩,
  ⟨"runtime-generics", Generic.featureSupport, fun feature => do
    let plan ← Solcore.Synthesis.Core.Generic.CheckedPlan.ofParts? (← step (probe (.var 0) feature)) .word
    return emits (Generic.emit plan)⟩,
  ⟨"runtime-closures", Closure.featureSupport, fun feature => do
    let plan ← Solcore.Synthesis.Core.Closure.CheckedPlan.ofParts? (← step (probe (.var 0) feature)) .snapshot
    return emits (Closure.emit plan)⟩,
  ⟨"runtime-comptime step", Comptime.featureSupport, fun feature => do
    let plan ← Solcore.Synthesis.Core.Comptime.CheckedPlan.ofParts? (← fixedConstant)
      (← step (probe (.var 0) feature)) .offset
    return emits (Comptime.emit plan)⟩,
  ⟨"runtime-comptime constant", Comptime.constantSupport, fun feature => do
    let plan ← Solcore.Synthesis.Core.Comptime.CheckedPlan.ofParts? (← closed (probe (word 5) feature))
      (← fixedStep) .offset
    return emits (Comptime.emit plan)⟩,
  ⟨"runtime-modules step", Modules.featureSupport, fun feature => do
    let plan ← Solcore.Synthesis.Core.Modules.CheckedPlan.ofParts? (← fixedConstant)
      (← step (probe (.var 0) feature))
    return emits (Modules.emit plan)⟩,
  ⟨"runtime-modules constant", Modules.constantSupport, fun feature => do
    let plan ← Solcore.Synthesis.Core.Modules.CheckedPlan.ofParts? (← closed (probe (word 5) feature))
      (← fixedStep)
    return emits (Modules.emit plan)⟩]

private def indices (mask : FeatureMask) : List Nat :=
  (FeatureMask.catalog.zipIdx.filter fun (feature, _) => mask.allows feature).map (·.2)

def testSourceEmitterSupportCases : IO Unit := do
  ensure (indices scalarSupport == [0, 1, 3, 4, 5, 8, 9, 10, 19, 20, 24, 25] &&
      PrimitiveRenderer.support == FeatureMask.all && AssemblyRenderer.support == FeatureMask.all &&
      AggregateRenderer.support == FeatureMask.all &&
      MutationRenderer.support == scalarSupport)
    "a renderer's declared G0 features changed"
  for profile in profiles do
    for feature in FeatureMask.catalog do
      let some emitted := profile.emits feature |
        throw (IO.userError s!"{profile.name}: the probe of {featureName feature} failed its checker")
      ensure (emitted == profile.support.allows feature)
        s!"{profile.name}: {featureName feature} emits {emitted} against its declared support"

end Tests.SourceEmitterSupportCases
end

section
-- leanmerge: from Solcore.Test.SourceGeneratorRevisionCases
/-! Every G0-based case profile generates, records, replays and reduces cases
of either G0 revision. Generation without a revision keeps `v1`, which the
existing case tests and fixed corpora pin. -/
set_option autoImplicit false

namespace Tests.SourceGeneratorRevisionCases

open Lean
open Solcore.Synthesis.Core
open Solcore.Synthesis.Source

private def get {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private structure Profile where
  name : String
  generate : Seed → Nat → Nat → Nat → Nat → GeneratorRevision → Json
  replay : Json → Nat → Except String Json
  shrink : Json → Nat → Nat → Except String Json
  nodes : Nat
  count : Nat
  /-- The provenance fields that name the G0 revision. -/
  versions : GeneratorRevision → List (String × String)

private def g0Version (revision : GeneratorRevision) : List (String × String) :=
  [("generatorVersion", revision.version)]

private def profiles : List Profile := [
  ⟨"closed-g0", fun seed nodes count attempts fuel revision =>
      generateCases seed nodes count attempts fuel revision,
    replayCase, shrinkCases, 24, 2, g0Version⟩,
  ⟨"runtime-word", fun seed nodes count attempts fuel revision =>
      Input.generateCases seed nodes count attempts fuel revision,
    Input.replayCase, Input.shrinkCases, 32, 4, g0Version⟩,
  ⟨"runtime-primitives", fun seed nodes count attempts fuel revision =>
      Primitive.generateCases seed nodes count attempts fuel revision,
    Primitive.replayCase, Primitive.shrinkCases, 96, 8, fun revision =>
      [("generatorVersion", Primitive.generatorVersionFor revision),
       ("baseGeneratorVersion", revision.version)]⟩,
  ⟨"runtime-functions", fun seed nodes count attempts fuel revision =>
      Function.generateCases seed nodes count attempts fuel revision,
    Function.replayCase, Function.shrinkCases, 64, 4, g0Version⟩,
  ⟨"runtime-mutation", fun seed nodes count attempts fuel revision =>
      Mutation.generateCases seed nodes count attempts fuel revision,
    Mutation.replayCase, Mutation.shrinkCases, 192, 4, g0Version⟩,
  ⟨"runtime-aggregates", fun seed nodes count attempts fuel revision =>
      Aggregate.generateCases seed nodes count attempts fuel revision,
    Aggregate.replayCase, Aggregate.shrinkCases, 256, 4, g0Version⟩,
  ⟨"runtime-loops", fun seed nodes count attempts fuel revision =>
      Loop.generateCases seed nodes count attempts fuel revision,
    Loop.replayCase, Loop.shrinkCases, 384, 6, g0Version⟩,
  ⟨"runtime-generics", fun seed nodes count attempts fuel revision =>
      Generic.generateCases seed nodes count attempts fuel revision,
    Generic.replayCase, Generic.shrinkCases, 384, 4, g0Version⟩,
  ⟨"runtime-closures", fun seed nodes count attempts fuel revision =>
      Closure.generateCases seed nodes count attempts fuel revision,
    Closure.replayCase, Closure.shrinkCases, 384, 4, g0Version⟩,
  ⟨"runtime-comptime", fun seed nodes count attempts fuel revision =>
      Comptime.generateCases seed nodes count attempts fuel revision,
    Comptime.replayCase, Comptime.shrinkCases, 384, 4, g0Version⟩,
  ⟨"runtime-modules", fun seed nodes count attempts fuel revision =>
      Modules.generateCases seed nodes count attempts fuel revision,
    Modules.replayCase, Modules.shrinkCases, 384, 4, g0Version⟩]

private def fuel : Nat := 100000

private def provenance (case : Json) : IO Json := get (case.getObjVal? "provenance")

private def records (profile : Profile) (revision : GeneratorRevision) (case : Json) : IO Bool := do
  let saved ← provenance case
  return (profile.versions revision).all fun (name, version) =>
    (saved.getObjValAs? String name).toOption == some version

private def withVersions (case : Json) (fields : List (String × String)) : IO Json := do
  let saved ← provenance case
  return case.setObjVal! "provenance"
    (fields.foldl (fun json (name, version) => json.setObjVal! name (toJson version)) saved)

private def cases (corpus : Json) : IO (Array Json) :=
  get (corpus.getObjValAs? (Array Json) "cases")

private def checkProfile (profile : Profile) : IO Unit := do
  let generate := fun revision =>
    profile.generate (Seed.ofNat 11) profile.nodes profile.count 64 fuel revision
  let current ← cases (generate .v2)
  ensure (generate .v2 == generate .v2) s!"{profile.name}: v2 generation is not deterministic"
  ensure (current.size == profile.count) s!"{profile.name}: v2 generation did not complete"
  let original ← cases (generate .v1)
  ensure (original.size == profile.count) s!"{profile.name}: v1 generation did not complete"
  for case in original do
    ensure (← records profile .v1 case) s!"{profile.name}: v1 case lost its version"
  ensure (current != original) s!"{profile.name}: v2 reproduced the v1 cases"
  for case in current do
    ensure (← records profile .v2 case) s!"{profile.name}: v2 case does not record its version"
    ensure ((← get (profile.replay case fuel)) == case)
      s!"{profile.name}: v2 case failed exact replay"
    -- Replaying under the other revision regenerates a different program.
    ensure (profile.replay (← withVersions case (profile.versions .v1)) fuel matches .error _)
      s!"{profile.name}: a v2 case replayed as v1"
    let unknown := (profile.versions .v2).map fun (name, _) => (name, "core-g0-v5/lcg64-v1")
    ensure (profile.replay (← withVersions case unknown) fuel matches .error _)
      s!"{profile.name}: an unknown G0 version replayed"
  let some first := current[0]? | throw (IO.userError s!"{profile.name}: no v2 case")
  let reduced ← cases (← get (profile.shrink first 3 fuel))
  ensure (!reduced.isEmpty) s!"{profile.name}: v2 case has no reduction candidate"
  for candidate in reduced do
    ensure (← records profile .v2 candidate)
      s!"{profile.name}: a reduction lost the parent's G0 revision"
    ensure ((← get (profile.replay candidate fuel)) == candidate)
      s!"{profile.name}: a v2 reduction failed exact replay"

def testSourceGeneratorRevisionCases : IO Unit := do
  ensure (profiles.length == 11) "a G0-based profile is missing from the revision checks"
  for profile in profiles do
    checkProfile profile

end Tests.SourceGeneratorRevisionCases
end

section
-- leanmerge: from Solcore.Test.SourceRevisionFourCases
/-! Revision-four cases of every G0-based profile record their case seed's
swarm mask restricted to the features of the profile's emitter, use no other
feature, replay exactly, refuse a mask outside those features and pass the
mask to their reductions. Where the emitter renders every feature, revision
four is revision three apart from its version. -/
set_option autoImplicit false

namespace Tests.SourceRevisionFourCases

open Lean
open Solcore.Synthesis.Core
open Solcore.Synthesis.Source

private def get {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private structure Profile where
  name : String
  generate : Seed → Nat → Nat → Nat → Nat → GeneratorRevision → Json
  replay : Json → Nat → Except String Json
  shrink : Json → Nat → Nat → Except String Json
  nodes : Nat
  count : Nat
  /-- The provenance version fields of a revision. -/
  versions : GeneratorRevision → List (String × String)
  /-- The features of the emitter that renders the case's recorded mask. -/
  support : FeatureMask
  /-- The features of the comptime and module constants' own renderer. -/
  constant : Option FeatureMask := none
  /-- Whether every recorded feature comes from G0 alone, without a template. -/
  scalar : Bool := false

private def g0Version (revision : GeneratorRevision) : List (String × String) :=
  [("generatorVersion", revision.version)]

private def profiles : List Profile := [
  {name := "closed-g0", generate := fun seed nodes count attempts fuel revision =>
      generateCases seed nodes count attempts fuel revision,
    replay := replayCase, shrink := shrinkCases, nodes := 24, count := 2, versions := g0Version,
    support := featureSupport, scalar := true},
  {name := "runtime-word", generate := fun seed nodes count attempts fuel revision =>
      Input.generateCases seed nodes count attempts fuel revision,
    replay := Input.replayCase, shrink := Input.shrinkCases, nodes := 32, count := 4, versions := g0Version,
    support := Input.featureSupport, scalar := true},
  {name := "runtime-primitives", generate := fun seed nodes count attempts fuel revision =>
      Primitive.generateCases seed nodes count attempts fuel revision,
    replay := Primitive.replayCase, shrink := Primitive.shrinkCases, nodes := 96, count := 8,
    versions := fun revision =>
      [("generatorVersion", Primitive.generatorVersionFor revision), ("baseGeneratorVersion", revision.version)],
    support := Primitive.featureSupport, scalar := true},
  {name := "runtime-assembly", generate := fun seed nodes count attempts fuel revision =>
      Assembly.generateCases seed nodes count attempts fuel revision,
    replay := Assembly.replayCase, shrink := Assembly.shrinkCases, nodes := 96, count := 8,
    versions := fun revision =>
      [("generatorVersion", Primitive.generatorVersionFor revision), ("baseGeneratorVersion", revision.version)],
    support := Assembly.featureSupport, scalar := true},
  {name := "runtime-assembly-memory", generate := fun seed nodes count attempts fuel revision =>
      AssemblyMemory.generateCases seed nodes count attempts fuel revision,
    replay := AssemblyMemory.replayCase, shrink := AssemblyMemory.shrinkCases, nodes := 96, count := 8,
    versions := fun revision =>
      [("generatorVersion", Primitive.generatorVersionFor revision), ("baseGeneratorVersion", revision.version)],
    support := AssemblyMemory.featureSupport, scalar := true},
  {name := "runtime-functions", generate := fun seed nodes count attempts fuel revision =>
      Solcore.Synthesis.Source.Function.generateCases seed nodes count attempts fuel revision,
    replay := Solcore.Synthesis.Source.Function.replayCase, shrink := Solcore.Synthesis.Source.Function.shrinkCases,
    nodes := 64, count := 4, versions := g0Version, support := Solcore.Synthesis.Source.Function.featureSupport},
  {name := "runtime-mutation", generate := fun seed nodes count attempts fuel revision =>
      Mutation.generateCases seed nodes count attempts fuel revision,
    replay := Mutation.replayCase, shrink := Mutation.shrinkCases, nodes := 192, count := 4,
    versions := g0Version, support := Mutation.featureSupport},
  {name := "runtime-aggregates", generate := fun seed nodes count attempts fuel revision =>
      Aggregate.generateCases seed nodes count attempts fuel revision,
    replay := Aggregate.replayCase, shrink := Aggregate.shrinkCases, nodes := 256, count := 4,
    versions := g0Version, support := Aggregate.featureSupport},
  {name := "runtime-loops", generate := fun seed nodes count attempts fuel revision =>
      Loop.generateCases seed nodes count attempts fuel revision,
    replay := Loop.replayCase, shrink := Loop.shrinkCases, nodes := 384, count := 6,
    versions := g0Version, support := Loop.featureSupport},
  {name := "runtime-nested-loops", generate := fun seed nodes count attempts fuel revision =>
      NestedLoop.generateCases seed nodes count attempts fuel revision,
    replay := NestedLoop.replayCase, shrink := NestedLoop.shrinkCases, nodes := 384, count := 6,
    versions := g0Version, support := NestedLoop.featureSupport},
  {name := "runtime-recursion", generate := fun seed nodes count attempts fuel revision =>
      Recursion.generateCases seed nodes count attempts fuel revision,
    replay := Recursion.replayCase, shrink := Recursion.shrinkCases, nodes := 384, count := 7,
    versions := g0Version, support := Recursion.featureSupport},
  {name := "runtime-recursive-loops", generate := fun seed nodes count attempts fuel revision =>
      RecursiveLoop.generateCases seed nodes count attempts fuel revision,
    replay := RecursiveLoop.replayCase, shrink := RecursiveLoop.shrinkCases, nodes := 384, count := 6,
    versions := g0Version, support := RecursiveLoop.featureSupport},
  {name := "runtime-loop-closures", generate := fun seed nodes count attempts fuel revision =>
      LoopClosure.generateCases seed nodes count attempts fuel revision,
    replay := LoopClosure.replayCase, shrink := LoopClosure.shrinkCases, nodes := 384, count := 6,
    versions := g0Version, support := LoopClosure.featureSupport},
  {name := "runtime-generics", generate := fun seed nodes count attempts fuel revision =>
      Generic.generateCases seed nodes count attempts fuel revision,
    replay := Generic.replayCase, shrink := Generic.shrinkCases, nodes := 384, count := 4,
    versions := g0Version, support := Generic.featureSupport},
  {name := "runtime-closures", generate := fun seed nodes count attempts fuel revision =>
      Closure.generateCases seed nodes count attempts fuel revision,
    replay := Closure.replayCase, shrink := Closure.shrinkCases, nodes := 384, count := 4,
    versions := g0Version, support := Closure.featureSupport},
  {name := "runtime-comptime", generate := fun seed nodes count attempts fuel revision =>
      Comptime.generateCases seed nodes count attempts fuel revision,
    replay := Comptime.replayCase, shrink := Comptime.shrinkCases, nodes := 384, count := 4,
    versions := g0Version, support := Comptime.featureSupport, constant := some Comptime.constantSupport},
  {name := "runtime-modules", generate := fun seed nodes count attempts fuel revision =>
      Modules.generateCases seed nodes count attempts fuel revision,
    replay := Modules.replayCase, shrink := Modules.shrinkCases, nodes := 384, count := 4,
    versions := g0Version, support := Modules.featureSupport, constant := some Modules.constantSupport}]

private def fuel : Nat := 100000

private def cases (corpus : Json) : IO (Array Json) :=
  get (corpus.getObjValAs? (Array Json) "cases")

private def provenance (case : Json) : IO Json := get (case.getObjVal? "provenance")

private def withProvenance (case : Json) (change : Json → Json) : IO Json := do
  return case.setObjVal! "provenance" (change (← provenance case))

private def withoutMask : Json → Json
  | .obj fields => .obj (fields.erase "swarmMask")
  | other => other

private def relabel (profile : Profile) (revision : GeneratorRevision) (case : Json) : IO Json :=
  withProvenance case fun saved =>
    (profile.versions revision).foldl (fun json (name, version) => json.setObjVal! name (toJson version)) saved

private def catalogName (name : String) : Bool := FeatureMask.catalog.any (featureName · = name)

/-- Every recorded catalog feature is allowed; leaves and template features are not catalog features. -/
private def within (mask : FeatureMask) (names : List String) : Bool :=
  names.all fun name => !catalogName name || mask.enabled.any (featureName · = name)

private def checkProfile (profile : Profile) : IO Unit := do
  let generate := fun revision =>
    profile.generate (Seed.ofNat 11) profile.nodes profile.count 64 fuel revision
  let current ← cases (generate .v4)
  ensure (generate .v4 == generate .v4) s!"{profile.name}: revision four is not deterministic"
  ensure (current.size == profile.count) s!"{profile.name}: revision-four generation did not complete"
  if profile.support == FeatureMask.all && profile.constant.isNone then
    let three ← cases (generate .v3)
    ensure ((← current.mapM (relabel profile .v3)) == three)
      s!"{profile.name}: revision four differs from revision three although its emitter renders every feature"
  for case in current do
    let saved ← provenance case
    let seedText ← get ((← get (saved.getObjVal? "origin")).getObjValAs? String "seed")
    let some seed := seedText.toNat? | throw (IO.userError s!"{profile.name}: invalid seed")
    let mask := GeneratorRevision.v4.caseMask (Seed.ofNat seed) profile.support
    ensure ((← get (saved.getObjVal? "swarmMask")) == maskJson mask && mask.subset profile.support)
      s!"{profile.name}: a case does not record its seed's mask restricted to its emitter"
    let features ← get (saved.getObjValAs? (List String) "features")
    ensure (within (if profile.scalar then mask else profile.support) features)
      s!"{profile.name}: a case uses a feature outside its mask or its emitter"
    if let some constant := profile.constant then
      let constantFeatures ← get (saved.getObjValAs? (List String) "constantFeatures")
      ensure (within (mask.within constant) constantFeatures)
        s!"{profile.name}: a constant uses a feature outside its renderer's restriction of the mask"
    ensure ((← get (profile.replay case fuel)) == case) s!"{profile.name}: a revision-four case failed exact replay"
    ensure (profile.replay (← withProvenance case withoutMask) fuel matches .error _)
      s!"{profile.name}: a revision-four case replayed without its mask"
    let other := GeneratorRevision.v4.caseMask (Seed.ofNat (seed + 1)) profile.support
    if other != mask then
      ensure (profile.replay (← withProvenance case (·.setObjVal! "swarmMask" (maskJson other))) fuel matches .error _)
        s!"{profile.name}: another seed's mask replayed"
    if profile.support != FeatureMask.all then
      ensure (profile.replay (← withProvenance case (·.setObjVal! "swarmMask" (maskJson FeatureMask.all))) fuel
          matches .error _)
        s!"{profile.name}: a mask outside its emitter's features replayed"
    -- Under revision three's label a case replays with revision three's mask
    -- only. A comptime or module constant is restricted further, so there an
    -- equal recorded mask decides nothing.
    let downgraded ← relabel profile .v3 case
    if mask != GeneratorRevision.v3.caseMask (Seed.ofNat seed) then
      ensure (profile.replay downgraded fuel matches .error _)
        s!"{profile.name}: a revision-four case replayed under revision three with another mask"
    else if profile.constant.isNone then
      ensure (profile.replay downgraded fuel matches .ok _)
        s!"{profile.name}: a revision-four case with revision three's mask is not revision three's case"
  let some first := current[0]? | throw (IO.userError s!"{profile.name}: no revision-four case")
  let parentMask ← get ((← provenance first).getObjVal? "swarmMask")
  let reduced ← cases (← get (profile.shrink first 3 fuel))
  ensure (!reduced.isEmpty) s!"{profile.name}: a revision-four case has no reduction candidate"
  for candidate in reduced do
    ensure ((← get ((← provenance candidate).getObjVal? "swarmMask")) == parentMask)
      s!"{profile.name}: a reduction lost its parent's mask"
    ensure ((← get (profile.replay candidate fuel)) == candidate)
      s!"{profile.name}: a reduction of a revision-four case failed exact replay"

private def unsupportedExclusions (corpus : Json) : IO Nat := do
  let excluded ← get (corpus.getObjValAs? (Array Json) "excluded")
  return (excluded.filter fun entry =>
    match entry.getObjValAs? String "reason" with
    | .ok reason => (reason.splitOn "EmitError.unsupported").length > 1
    | .error _ => false).size

private def distinctSources (corpus : Json) : IO Nat := do
  let sources ← (← cases corpus).toList.mapM fun case => get (case.getObjValAs? String "source")
  return sources.eraseDups.length

/-- From seed one, revision four never generates a program the emitter rejects,
and `runtime-word` accepts its functions with far fewer attempts and repeats. -/
private def statisticsChecks : IO Unit := do
  for profile in profiles do
    if profile.support != FeatureMask.all || profile.constant.isSome then
      let corpus := profile.generate (Seed.ofNat 1) profile.nodes (16 * profile.count) 4096 fuel .v4
      ensure ((← cases corpus).size == 16 * profile.count) s!"{profile.name}: revision four exhausted generation"
      ensure ((← unsupportedExclusions corpus) == 0)
        s!"{profile.name}: revision four generated a program its emitter rejects"
  let word := fun revision => Input.generateCases (Seed.ofNat 1) 32 256 4096 fuel revision
  let attempted := fun (corpus : Json) => get (corpus.getObjValAs? Nat "attempted")
  let (three, four) := (word .v3, word .v4)
  ensure (2 * (← attempted four) ≤ (← attempted three))
    s!"runtime-word: revision four needed {← attempted four} attempts against {← attempted three}"
  ensure ((← distinctSources four) ≥ 3 * (← distinctSources three))
    s!"runtime-word: revision four has {← distinctSources four} sources against {← distinctSources three}"

def testSourceRevisionFourCases : IO Unit := do
  ensure (profiles.length == 17) "a G0-based profile is missing from the revision-four checks"
  for profile in profiles do
    checkProfile profile
  statisticsChecks

end Tests.SourceRevisionFourCases
end

section
-- leanmerge: from Solcore.Test.SourceSeededInputCases
/-! Seeded runtime inputs: their replay vectors and value ranges, and their
generation, recording, replay, tampering and reduction in every runtime-input
profile. Generation without a selection keeps the boundary inputs, which the
existing case tests and fixed corpora pin. -/
set_option autoImplicit false

namespace Tests.SourceSeededInputCases

open Lean
open Solcore.Core (Word)
open Solcore.Synthesis.Core
open Solcore.Synthesis.Source

private def get {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def seeded (seed : Nat) : List Nat :=
  (InputSelection.seededInputs (Seed.ofNat seed)).map (·.val)

private def vectorChecks : IO Unit := do
  ensure (seeded 0 == [
      56189052813837018966195966706874179130487732287838569029762288915300383936473,
      15797683219724309265658083358374668, 106, 2 ^ 256 - 6])
    "the seeded input vector of seed 0 changed"
  ensure (seeded 4254 == [
      87847550103885626486316609148408507170101340273028280478259265334201237472442,
      37415062808491099348759069756, 470, 0])
    "the seeded input vector of seed 4254 changed"
  ensure (InputSelection.ofVersion? InputSelection.seededVersion == some .seeded &&
      InputSelection.seededVersion == "seeded-inputs-v1/splitmix64" &&
      InputSelection.ofVersion? "core-g0-v2/lcg64-v1" == none)
    "the seeded input version changed"
  let boundaries := Input.boundaryInputs
  ensure (InputSelection.boundary.inputs boundaries (Seed.ofNat 9) == boundaries &&
      InputSelection.seeded.inputs boundaries (Seed.ofNat 9) ==
        boundaries ++ InputSelection.seededInputs (Seed.ofNat 9))
    "a selection changed its boundary prefix"
  let origin := Json.mkObj [("kind", toJson "input-generated")]
  ensure (InputSelection.boundary.record origin == origin &&
      (InputSelection.ofOrigin origin).toOption == some .boundary &&
      (InputSelection.ofOrigin (InputSelection.seeded.record origin)).toOption == some .seeded)
    "an origin does not round-trip its selection"
  for value in [toJson "seeded-inputs-v2/splitmix64", toJson (1 : Nat)] do
    ensure (InputSelection.ofOrigin (origin.setObjVal! "inputSelection" value) matches .error _)
      "an unknown input selection was accepted"

/-- Bit length; zero has length zero. -/
private def bits (value : Nat) : Nat :=
  if value = 0 then 0 else Nat.log2 value + 1

/-- 2,048 consecutive seeds: each slot keeps its range and spreads within it. -/
private def rangeChecks : IO Unit := do
  let samples := (List.range 2048).map seeded
  let slot := fun (index : Nat) => samples.map (·.getD index 0)
  ensure (samples.all (·.length == 4)) "a seed did not give four inputs"
  let full := slot 0
  let high := (full.filter (· ≥ 2 ^ 255)).length
  ensure (900 ≤ high && high ≤ 1148) s!"full random inputs set the top bit {high} times of 2048"
  let widths := (slot 1).map bits
  ensure (widths.any (· ≤ 8) && widths.any (fun width => 64 < width && width ≤ 128) &&
      widths.any (· > 248)) "uniform-width inputs miss small, middle or full widths"
  let small := slot 2
  ensure (small.all (· < 512) && small.eraseDups.length > 400 && small.any (· < 32) &&
      small.any (· ≥ 256)) "small inputs leave their range or cluster"
  let negated := slot 3
  let negative := (negated.filter (· ≥ 2 ^ 255)).length
  ensure (negative ≥ 2000 && negated.any (· ≥ 2 ^ 256 - 256))
    s!"negated inputs are negative {negative} times of 2048 or never near -1"

private structure Profile where
  name : String
  generate : Seed → Nat → Nat → Nat → Nat → InputSelection → Json
  replay : Json → Nat → Except String Json
  shrink : Json → Nat → Nat → Except String Json
  boundaries : List Word
  nodes : Nat

/-- G0-based profiles run with revision two, as random campaigns do. -/
private def profiles : List Profile := [
  ⟨"runtime-word", fun seed nodes count attempts fuel inputs =>
      Input.generateCases seed nodes count attempts fuel .v2 inputs,
    Input.replayCase, Input.shrinkCases, Input.boundaryInputs, 32⟩,
  ⟨"runtime-primitives", fun seed nodes count attempts fuel inputs =>
      Primitive.generateCases seed nodes count attempts fuel .v2 inputs,
    Primitive.replayCase, Primitive.shrinkCases, Primitive.boundaryInputs, 96⟩,
  ⟨"runtime-functions", fun seed nodes count attempts fuel inputs =>
      Function.generateCases seed nodes count attempts fuel .v2 inputs,
    Function.replayCase, Function.shrinkCases, Input.boundaryInputs, 64⟩,
  ⟨"runtime-mutation", fun seed nodes count attempts fuel inputs =>
      Mutation.generateCases seed nodes count attempts fuel .v2 inputs,
    Mutation.replayCase, Mutation.shrinkCases, Input.boundaryInputs, 192⟩,
  ⟨"runtime-aggregates", fun seed nodes count attempts fuel inputs =>
      Aggregate.generateCases seed nodes count attempts fuel .v2 inputs,
    Aggregate.replayCase, Aggregate.shrinkCases, Input.boundaryInputs, 256⟩,
  ⟨"runtime-loops", fun seed nodes count attempts fuel inputs =>
      Loop.generateCases seed nodes count attempts fuel .v2 inputs,
    Loop.replayCase, Loop.shrinkCases, Loop.boundaryInputs, 384⟩,
  ⟨"runtime-generics", fun seed nodes count attempts fuel inputs =>
      Generic.generateCases seed nodes count attempts fuel .v2 inputs,
    Generic.replayCase, Generic.shrinkCases, Generic.boundaryInputs, 384⟩,
  ⟨"runtime-closures", fun seed nodes count attempts fuel inputs =>
      Closure.generateCases seed nodes count attempts fuel .v2 inputs,
    Closure.replayCase, Closure.shrinkCases, Closure.boundaryInputs, 384⟩,
  ⟨"runtime-comptime", fun seed nodes count attempts fuel inputs =>
      Comptime.generateCases seed nodes count attempts fuel .v2 inputs,
    Comptime.replayCase, Comptime.shrinkCases, Comptime.boundaryInputs, 384⟩,
  ⟨"runtime-modules", fun seed nodes count attempts fuel inputs =>
      Modules.generateCases seed nodes count attempts fuel .v2 inputs,
    Modules.replayCase, Modules.shrinkCases, Modules.boundaryInputs, 384⟩,
  ⟨"runtime-call-graphs", fun seed nodes count attempts fuel inputs =>
      CallGraph.generateCases seed nodes count attempts fuel inputs,
    CallGraph.replayCase, CallGraph.shrinkCases, CallGraph.boundaryInputs, 192⟩,
  ⟨"runtime-call-graph-loops", fun seed nodes count attempts fuel inputs =>
      CallGraphLoop.generateCases seed nodes count attempts fuel inputs,
    CallGraphLoop.replayCase, CallGraphLoop.shrinkCases, CallGraphLoop.boundaryInputs, 256⟩,
  ⟨"runtime-aggregate-call-graphs", fun seed nodes count attempts fuel inputs =>
      AggregateCallGraph.generateCases seed nodes count attempts fuel inputs,
    AggregateCallGraph.replayCase, AggregateCallGraph.shrinkCases, AggregateCallGraph.boundaryInputs, 192⟩]

private def fuel : Nat := 100000

private def cases (corpus : Json) : IO (Array Json) :=
  get (corpus.getObjValAs? (Array Json) "cases")

private def origin (case : Json) : IO Json :=
  get ((case.getObjVal? "provenance").bind (·.getObjVal? "origin"))

private def withOrigin (case : Json) (origin : Json) : IO Json := do
  let provenance ← get (case.getObjVal? "provenance")
  return case.setObjVal! "provenance" (provenance.setObjVal! "origin" origin)

private def withoutSelection : Json → Json
  | .obj fields => .obj (fields.erase "inputSelection")
  | other => other

private def checkProfile (profile : Profile) : IO Unit := do
  let count := profile.boundaries.length + 4
  let generate := fun inputs => profile.generate (Seed.ofNat 31) profile.nodes count 64 fuel inputs
  let current ← cases (generate .seeded)
  ensure (generate .seeded == generate .seeded) s!"{profile.name}: seeded generation is not deterministic"
  ensure (current.size == count) s!"{profile.name}: one function did not give every seeded input"
  let some first := current[0]? | throw (IO.userError s!"{profile.name}: no seeded case")
  let seedText ← get ((← origin first).getObjValAs? String "seed")
  let some seed := seedText.toNat? | throw (IO.userError s!"{profile.name}: invalid seed")
  let inputs ← current.toList.mapM fun case => get (case.getObjValAs? String "input")
  ensure (inputs == (InputSelection.seeded.inputs profile.boundaries (Seed.ofNat seed)).map
      (toString ·.val)) s!"{profile.name}: inputs are not the boundaries followed by the seeded inputs"
  -- Boundary selection gives the same first cases, only without the selection.
  let original ← cases (generate .boundary)
  let boundaryCases ← (current.extract 0 profile.boundaries.length).mapM fun case => do
    withOrigin case (withoutSelection (← origin case))
  ensure (original.extract 0 profile.boundaries.length == boundaryCases)
    s!"{profile.name}: seeded selection changed a boundary case"
  for case in current do
    ensure ((← get ((← origin case).getObjValAs? String "inputSelection")) == InputSelection.seededVersion)
      s!"{profile.name}: a seeded case does not name its selection"
    ensure ((← get (profile.replay case fuel)) == case) s!"{profile.name}: a seeded case failed exact replay"
  let some last := current.back? | throw (IO.userError s!"{profile.name}: no seeded case")
  let lastOrigin ← origin last
  ensure (profile.replay (← withOrigin last (withoutSelection lastOrigin)) fuel matches .error _)
    s!"{profile.name}: a seeded input replayed without its selection"
  ensure (profile.replay (← withOrigin last (lastOrigin.setObjVal! "inputSelection"
      (toJson "seeded-inputs-v2/splitmix64"))) fuel matches .error _)
    s!"{profile.name}: an unknown input selection replayed"
  let forged := last.setObjVal! "input" (toJson "12345")
  ensure (profile.replay forged fuel matches .error _) s!"{profile.name}: a changed seeded input replayed"
  let reduced ← cases (← get (profile.shrink last 3 fuel))
  ensure (!reduced.isEmpty) s!"{profile.name}: a seeded case has no reduction candidate"
  for candidate in reduced do
    ensure ((← get (profile.replay candidate fuel)) == candidate)
      s!"{profile.name}: a reduction of a seeded case failed exact replay"

def testSourceSeededInputCases : IO Unit := do
  vectorChecks
  rangeChecks
  ensure (profiles.length == 13) "a runtime-input profile is missing from the seeded input checks"
  for profile in profiles do
    checkProfile profile

end Tests.SourceSeededInputCases
end

section
-- leanmerge: from Solcore.Test.SourceStatefulGeneratorRevisionCases
/-! Every stateful profile generates its checked step with any G0 revision,
records it, replays it and passes it to its reductions, together with revision
three's swarm mask. Generation without a revision keeps `v1`, which the
existing case tests and fixed corpora pin. -/
set_option autoImplicit false

namespace Tests.SourceStatefulGeneratorRevisionCases

open Lean
open Solcore.Synthesis.Core
open Solcore.Synthesis.Source

private def get {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private structure Profile where
  name : String
  generate : Seed → Nat → Nat → Nat → Nat → GeneratorRevision → Json
  replay : Json → Nat → Except String Json
  shrink : Json → Nat → Nat → Except String Json

private def profiles : List Profile := [
  ⟨"stateful-storage", fun seed nodes count attempts fuel revision =>
      Storage.generateCases seed nodes count attempts fuel revision, Storage.replayCase, Storage.shrinkCases⟩,
  ⟨"stateful-storage-rollback", fun seed nodes count attempts fuel revision =>
      StorageRollback.generateCases seed nodes count attempts fuel revision,
    StorageRollback.replayCase, StorageRollback.shrinkCases⟩,
  ⟨"stateful-calls", fun seed nodes count attempts fuel revision =>
      NestedCall.generateCases seed nodes count attempts fuel revision, NestedCall.replayCase, NestedCall.shrinkCases⟩,
  ⟨"stateful-keyed-storage", fun seed nodes count attempts fuel revision =>
      KeyedStorage.generateCases seed nodes count attempts fuel revision,
    KeyedStorage.replayCase, KeyedStorage.shrinkCases⟩,
  ⟨"stateful-dynamic-array", fun seed nodes count attempts fuel revision =>
      DynamicArray.generateCases seed nodes count attempts fuel revision,
    DynamicArray.replayCase, DynamicArray.shrinkCases⟩,
  ⟨"stateful-logs", fun seed nodes count attempts fuel revision =>
      EventLog.generateCases seed nodes count attempts fuel revision, EventLog.replayCase, EventLog.shrinkCases⟩,
  ⟨"stateful-call-value", fun seed nodes count attempts fuel revision =>
      CallValue.generateCases seed nodes count attempts fuel revision, CallValue.replayCase, CallValue.shrinkCases⟩,
  ⟨"stateful-bytes", fun seed nodes count attempts fuel revision =>
      DynamicBytes.generateCases seed nodes count attempts fuel revision,
    DynamicBytes.replayCase, DynamicBytes.shrinkCases⟩,
  ⟨"stateful-forwarded-value", fun seed nodes count attempts fuel revision =>
      ForwardedCall.generateCases seed nodes count attempts fuel revision,
    ForwardedCall.replayCase, ForwardedCall.shrinkCases⟩,
  ⟨"stateful-mapping", fun seed nodes count attempts fuel revision =>
      StorageMapping.generateCases seed nodes count attempts fuel revision,
    StorageMapping.replayCase, StorageMapping.shrinkCases⟩,
  ⟨"stateful-ledger", fun seed nodes count attempts fuel revision =>
      StorageLedger.generateCases seed nodes count attempts fuel revision,
    StorageLedger.replayCase, StorageLedger.shrinkCases⟩,
  ⟨"stateful-long-bytes", fun seed nodes count attempts fuel revision =>
      LongBytes.generateCases seed nodes count attempts fuel revision, LongBytes.replayCase, LongBytes.shrinkCases⟩,
  ⟨"stateful-nested-array", fun seed nodes count attempts fuel revision =>
      NestedArray.generateCases seed nodes count attempts fuel revision,
    NestedArray.replayCase, NestedArray.shrinkCases⟩]

private def fuel : Nat := 1000000

private def recordedVersion (case : Json) : IO String := do
  get ((← get (case.getObjVal? "provenance")).getObjValAs? String "generatorVersion")

private def withVersion (case : Json) (version : String) : IO Json := do
  let saved ← get (case.getObjVal? "provenance")
  return case.setObjVal! "provenance" (saved.setObjVal! "generatorVersion" (toJson version))

private def firstCase (corpus : Json) (name : String) : IO Json := do
  let some case := (← get (corpus.getObjValAs? (Array Json) "cases"))[0]?
    | throw (IO.userError s!"{name}: generation produced no case")
  return case

private def checkProfile (profile : Profile) : IO Unit := do
  let generate := fun revision => profile.generate (Seed.ofNat 5) 384 1 64 fuel revision
  let current ← firstCase (generate .v2) profile.name
  ensure (generate .v2 == generate .v2) s!"{profile.name}: v2 generation is not deterministic"
  let original ← firstCase (generate .v1) profile.name
  ensure ((← recordedVersion original) == GeneratorRevision.v1.version) s!"{profile.name}: v1 case lost its version"
  ensure ((← recordedVersion current) == GeneratorRevision.v2.version) s!"{profile.name}: v2 case does not record its version"
  ensure (current != original) s!"{profile.name}: v2 reproduced the v1 scenario"
  ensure ((← get (profile.replay current fuel)) == current) s!"{profile.name}: v2 case failed exact replay"
  -- Replaying under the other revision regenerates a different step.
  ensure (profile.replay (← withVersion current GeneratorRevision.v1.version) fuel matches .error _)
    s!"{profile.name}: a v2 case replayed as v1"
  ensure (profile.replay (← withVersion current "core-g0-v9/lcg64-v1") fuel matches .error _)
    s!"{profile.name}: an unknown G0 version replayed"
  let reduced ← get ((← get (profile.shrink current 2 fuel)).getObjValAs? (Array Json) "cases")
  ensure (!reduced.isEmpty) s!"{profile.name}: v2 case has no reduction candidate"
  for candidate in reduced do
    ensure ((← recordedVersion candidate) == GeneratorRevision.v2.version)
      s!"{profile.name}: a reduction lost the parent's G0 revision"
    ensure ((← get (profile.replay candidate fuel)) == candidate) s!"{profile.name}: a v2 reduction failed exact replay"

private def provenance (case : Json) : IO Json := get (case.getObjVal? "provenance")

private def withProvenance (case : Json) (change : Json → Json) : IO Json := do
  return case.setObjVal! "provenance" (change (← provenance case))

private def withoutMask : Json → Json
  | .obj fields => .obj (fields.erase "swarmMask")
  | other => other

/-- Revision three records the scenario seed's swarm mask, which every helper
of the step uses. Replay requires and checks it, the other revisions refuse
one, and reductions copy it. -/
private def checkMask (profile : Profile) : IO Unit := do
  let generate := fun revision => profile.generate (Seed.ofNat 5) 384 1 64 fuel revision
  ensure (generate .v3 == generate .v3) s!"{profile.name}: v3 generation is not deterministic"
  let masked ← firstCase (generate .v3) profile.name
  let plain ← firstCase (generate .v2) profile.name
  ensure ((← provenance plain).getObjVal? "swarmMask" matches .error _) s!"{profile.name}: a v2 case records a swarm mask"
  ensure ((← recordedVersion masked) == GeneratorRevision.v3.version) s!"{profile.name}: v3 case does not record its version"
  let saved ← provenance masked
  let some seed := (← get ((← get (saved.getObjVal? "origin")).getObjValAs? String "seed")).toNat?
    | throw (IO.userError s!"{profile.name}: invalid saved seed")
  let mask := GeneratorRevision.v3.caseMask (Seed.ofNat seed)
  ensure ((← get (saved.getObjVal? "swarmMask")) == maskJson mask)
    s!"{profile.name}: a v3 case does not record the mask of its seed"
  ensure ((← get (profile.replay masked fuel)) == masked) s!"{profile.name}: v3 case failed exact replay"
  ensure (profile.replay (← withProvenance masked withoutMask) fuel matches .error _)
    s!"{profile.name}: a v3 case replayed without its mask"
  let changed := toJson ((mask.enabled.drop 1).map featureName)
  ensure (profile.replay (← withProvenance masked (·.setObjVal! "swarmMask" changed)) fuel matches .error _)
    s!"{profile.name}: a changed swarm mask replayed"
  ensure (profile.replay (← withVersion masked GeneratorRevision.v2.version) fuel matches .error _)
    s!"{profile.name}: a swarm mask replayed under revision two"
  let reduced ← get ((← get (profile.shrink masked 2 fuel)).getObjValAs? (Array Json) "cases")
  ensure (!reduced.isEmpty) s!"{profile.name}: v3 case has no reduction candidate"
  for candidate in reduced do
    ensure (((← provenance candidate).getObjVal? "swarmMask").toOption == some (maskJson mask))
      s!"{profile.name}: a reduction lost the parent's swarm mask"
    ensure ((← get (profile.replay candidate fuel)) == candidate) s!"{profile.name}: a v3 reduction failed exact replay"

def testSourceStatefulGeneratorRevisionCases : IO Unit := do
  ensure (profiles.length == 13) "a stateful profile is missing from the revision checks"
  for profile in profiles do
    checkProfile profile
    checkMask profile

end Tests.SourceStatefulGeneratorRevisionCases
end

section
-- leanmerge: from Solcore.Test.SourceStatefulSequenceCases
/-! Every stateful profile generates a requested sequence length as the first
transactions of its consecutive three-transaction blocks, records any length
other than three, replays exactly that length and first removes the last
transaction when it shrinks. The existing case tests and fixed corpora pin the
three-transaction default. -/
set_option autoImplicit false

namespace Tests.SourceStatefulSequenceCases

open Lean
open Solcore.Core (Word)
open Solcore.Synthesis.Core
open Solcore.Synthesis.Source
open Solcore.Synthesis.Stateful.Sequence (maxTransactions blockSeeds)

private def get {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private structure Profile where
  name : String
  generate : Seed → Nat → Nat → Nat → Nat → GeneratorRevision → Nat → Json
  replay : Json → Nat → Except String Json
  shrink : Json → Nat → Nat → Except String Json

private def profiles : List Profile := [
  ⟨"stateful-storage", fun seed nodes count attempts fuel revision transactions =>
      Storage.generateCases seed nodes count attempts fuel revision transactions,
    Storage.replayCase, Storage.shrinkCases⟩,
  ⟨"stateful-storage-rollback", fun seed nodes count attempts fuel revision transactions =>
      StorageRollback.generateCases seed nodes count attempts fuel revision transactions,
    StorageRollback.replayCase, StorageRollback.shrinkCases⟩,
  ⟨"stateful-calls", fun seed nodes count attempts fuel revision transactions =>
      NestedCall.generateCases seed nodes count attempts fuel revision transactions,
    NestedCall.replayCase, NestedCall.shrinkCases⟩,
  ⟨"stateful-keyed-storage", fun seed nodes count attempts fuel revision transactions =>
      KeyedStorage.generateCases seed nodes count attempts fuel revision transactions,
    KeyedStorage.replayCase, KeyedStorage.shrinkCases⟩,
  ⟨"stateful-dynamic-array", fun seed nodes count attempts fuel revision transactions =>
      DynamicArray.generateCases seed nodes count attempts fuel revision transactions,
    DynamicArray.replayCase, DynamicArray.shrinkCases⟩,
  ⟨"stateful-logs", fun seed nodes count attempts fuel revision transactions =>
      EventLog.generateCases seed nodes count attempts fuel revision transactions,
    EventLog.replayCase, EventLog.shrinkCases⟩,
  ⟨"stateful-call-value", fun seed nodes count attempts fuel revision transactions =>
      CallValue.generateCases seed nodes count attempts fuel revision transactions,
    CallValue.replayCase, CallValue.shrinkCases⟩,
  ⟨"stateful-bytes", fun seed nodes count attempts fuel revision transactions =>
      DynamicBytes.generateCases seed nodes count attempts fuel revision transactions,
    DynamicBytes.replayCase, DynamicBytes.shrinkCases⟩,
  ⟨"stateful-forwarded-value", fun seed nodes count attempts fuel revision transactions =>
      ForwardedCall.generateCases seed nodes count attempts fuel revision transactions,
    ForwardedCall.replayCase, ForwardedCall.shrinkCases⟩,
  ⟨"stateful-mapping", fun seed nodes count attempts fuel revision transactions =>
      StorageMapping.generateCases seed nodes count attempts fuel revision transactions,
    StorageMapping.replayCase, StorageMapping.shrinkCases⟩,
  ⟨"stateful-ledger", fun seed nodes count attempts fuel revision transactions =>
      StorageLedger.generateCases seed nodes count attempts fuel revision transactions,
    StorageLedger.replayCase, StorageLedger.shrinkCases⟩,
  ⟨"stateful-long-bytes", fun seed nodes count attempts fuel revision transactions =>
      LongBytes.generateCases seed nodes count attempts fuel revision transactions,
    LongBytes.replayCase, LongBytes.shrinkCases⟩,
  ⟨"stateful-nested-array", fun seed nodes count attempts fuel revision transactions =>
      NestedArray.generateCases seed nodes count attempts fuel revision transactions,
    NestedArray.replayCase, NestedArray.shrinkCases⟩]

private def fuel : Nat := 1000000

private def cases (corpus : Json) : IO (Array Json) :=
  get (corpus.getObjValAs? (Array Json) "cases")

private def firstCase (corpus : Json) (name : String) : IO Json := do
  let some case := (← cases corpus)[0]? | throw (IO.userError s!"{name}: generation produced no case")
  return case

private def transactions (case : Json) : IO (List Json) :=
  get (case.getObjValAs? (List Json) "transactions")

private def origin (case : Json) : IO Json := do
  get ((← get (case.getObjVal? "provenance")).getObjVal? "origin")

private def withOrigin (case : Json) (origin : Json) : IO Json := do
  let provenance ← get (case.getObjVal? "provenance")
  return case.setObjVal! "provenance" (provenance.setObjVal! "origin" origin)

private def ids (rows : List Json) : IO (List String) :=
  rows.mapM fun row => get (row.getObjValAs? String "id")

private def checkProfile (profile : Profile) : IO Unit := do
  let generate := fun (seed attempts count : Nat) => profile.generate (Seed.ofNat seed) 384 1 attempts fuel .v2 count
  let short ← firstCase (generate 11 64 3) profile.name
  ensure ((← origin short).getObjVal? "transactionCount" matches .error _)
    s!"{profile.name}: a three-transaction origin records its count"
  -- Longer and shorter sequences start at the short case's seed, so their
  -- first block is the short sequence.
  let some seed := (← get ((← origin short).getObjValAs? String "seed")).toNat?
    | throw (IO.userError s!"{profile.name}: invalid saved seed")
  let single ← firstCase (generate seed 1 1) profile.name
  ensure ((← transactions single) == (← transactions short).take 1) s!"{profile.name}: one transaction is not the first"
  let long ← firstCase (generate seed 1 maxTransactions) profile.name
  let rows ← transactions long
  ensure ((← ids rows) == (List.range maxTransactions).map (fun index => "tx-" ++ toString index))
    s!"{profile.name}: a long sequence has the wrong transaction IDs"
  ensure (rows.take 3 == (← transactions short)) s!"{profile.name}: a long sequence does not extend the short one"
  ensure (((← origin long).getObjValAs? Nat "transactionCount").toOption == some maxTransactions)
    s!"{profile.name}: a long origin does not record its count"
  ensure ((← cases (generate seed 1 (maxTransactions + 1))).isEmpty) s!"{profile.name}: an unbounded sequence was generated"
  ensure ((← get (profile.replay long fuel)) == long) s!"{profile.name}: a long case failed exact replay"
  for recorded in [3, maxTransactions - 1, maxTransactions + 1] do
    let changed ← withOrigin long ((← origin long).setObjVal! "transactionCount" (toJson recorded))
    ensure (profile.replay changed fuel matches .error _)
      s!"{profile.name}: a long case replayed with transaction count {recorded}"
  let reduced ← cases (← get (profile.shrink long 4 fuel))
  let some first := reduced[0]? | throw (IO.userError s!"{profile.name}: a long case has no reduction")
  ensure ((← transactions first) == rows.dropLast) s!"{profile.name}: reduction does not first remove the last transaction"
  for candidate in reduced do
    ensure ((← get (profile.replay candidate fuel)) == candidate) s!"{profile.name}: a long reduction failed exact replay"

/-- Generated values and amounts keep their totals; three transactions never
reach them. -/
private def checkValueBounds : IO Unit := do
  let large := Word.ofNatModulo (2 ^ 70)
  let sent := (List.range 8).map fun index =>
    ({id := "tx-" ++ toString index, flags := Word.zero, input := Word.zero, value := large} :
      Solcore.Synthesis.Stateful.CallValueExecution.Transaction)
  ensure ((CallValue.boundedValues (Word.ofNatModulo 5) sent).map (·.value.val) ==
      [2 ^ 70, 2 ^ 70, 2 ^ 70, 0, 0, 0, 0, 0]) "call values exceed the funded total"
  ensure (CallValue.boundedValues (Word.ofNatModulo 5) (sent.take 3) == sent.take 3) "three call values were bounded"
  let forwarded := (List.range 8).map fun index =>
    ({id := "tx-" ++ toString index, input := Word.zero, value := large, amount := large} :
      Solcore.Synthesis.Stateful.ForwardedCallExecution.Transaction)
  ensure ((ForwardedCall.boundedAmounts forwarded).map (·.amount.val) == [2 ^ 70, 2 ^ 70, 2 ^ 70, 2 ^ 70, 0, 0, 0, 0])
    "forwarded amounts exceed the endowment"
  ensure ((ForwardedCall.boundedAmounts forwarded).map (·.value.val) == List.replicate 8 (2 ^ 70))
    "bounding forwarded amounts changed a call value"

def testSourceStatefulSequenceCases : IO Unit := do
  ensure (profiles.length == 13) "a stateful profile is missing from the sequence checks"
  ensure ((blockSeeds (Seed.ofNat 7) 3).head? == some (Seed.ofNat 7)) "block zero no longer uses the scenario seed"
  ensure ((blockSeeds (Seed.ofNat 7) 3).eraseDups.length == 3) "block seeds repeat"
  checkValueBounds
  for profile in profiles do
    checkProfile profile

end Tests.SourceStatefulSequenceCases
end

section
-- leanmerge: from Solcore.Test.SourceSwarmMaskCases
/-! Revision-three cases of every G0-based profile record the swarm mask of
their case seed, replay it exactly and pass it to their reductions. Cases of
the other revisions record no mask. -/
set_option autoImplicit false

namespace Tests.SourceSwarmMaskCases

open Lean
open Solcore.Synthesis.Core
open Solcore.Synthesis.Source

private def get {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private structure Profile where
  name : String
  generate : Seed → Nat → Nat → Nat → Nat → GeneratorRevision → Json
  replay : Json → Nat → Except String Json
  shrink : Json → Nat → Nat → Except String Json
  nodes : Nat
  count : Nat
  /-- The provenance version fields of a revision. -/
  versions : GeneratorRevision → List (String × String)
  /-- Whether every recorded feature comes from G0 alone, without a template. -/
  scalar : Bool

private def g0Version (revision : GeneratorRevision) : List (String × String) :=
  [("generatorVersion", revision.version)]

private def profiles : List Profile := [
  ⟨"closed-g0", fun seed nodes count attempts fuel revision =>
      generateCases seed nodes count attempts fuel revision,
    replayCase, shrinkCases, 24, 2, g0Version, true⟩,
  ⟨"runtime-word", fun seed nodes count attempts fuel revision =>
      Input.generateCases seed nodes count attempts fuel revision,
    Input.replayCase, Input.shrinkCases, 32, 4, g0Version, true⟩,
  ⟨"runtime-primitives", fun seed nodes count attempts fuel revision =>
      Primitive.generateCases seed nodes count attempts fuel revision,
    Primitive.replayCase, Primitive.shrinkCases, 96, 8, fun revision =>
      [("generatorVersion", Primitive.generatorVersionFor revision),
       ("baseGeneratorVersion", revision.version)], true⟩,
  ⟨"runtime-functions", fun seed nodes count attempts fuel revision =>
      Function.generateCases seed nodes count attempts fuel revision,
    Function.replayCase, Function.shrinkCases, 64, 4, g0Version, false⟩,
  ⟨"runtime-mutation", fun seed nodes count attempts fuel revision =>
      Mutation.generateCases seed nodes count attempts fuel revision,
    Mutation.replayCase, Mutation.shrinkCases, 192, 4, g0Version, false⟩,
  ⟨"runtime-aggregates", fun seed nodes count attempts fuel revision =>
      Aggregate.generateCases seed nodes count attempts fuel revision,
    Aggregate.replayCase, Aggregate.shrinkCases, 256, 4, g0Version, false⟩,
  ⟨"runtime-loops", fun seed nodes count attempts fuel revision =>
      Loop.generateCases seed nodes count attempts fuel revision,
    Loop.replayCase, Loop.shrinkCases, 384, 6, g0Version, false⟩,
  ⟨"runtime-generics", fun seed nodes count attempts fuel revision =>
      Generic.generateCases seed nodes count attempts fuel revision,
    Generic.replayCase, Generic.shrinkCases, 384, 4, g0Version, false⟩,
  ⟨"runtime-closures", fun seed nodes count attempts fuel revision =>
      Closure.generateCases seed nodes count attempts fuel revision,
    Closure.replayCase, Closure.shrinkCases, 384, 4, g0Version, false⟩,
  ⟨"runtime-comptime", fun seed nodes count attempts fuel revision =>
      Comptime.generateCases seed nodes count attempts fuel revision,
    Comptime.replayCase, Comptime.shrinkCases, 384, 4, g0Version, false⟩,
  ⟨"runtime-modules", fun seed nodes count attempts fuel revision =>
      Modules.generateCases seed nodes count attempts fuel revision,
    Modules.replayCase, Modules.shrinkCases, 384, 4, g0Version, false⟩]

private def fuel : Nat := 100000

private def cases (corpus : Json) : IO (Array Json) :=
  get (corpus.getObjValAs? (Array Json) "cases")

private def provenance (case : Json) : IO Json := get (case.getObjVal? "provenance")

private def withProvenance (case : Json) (change : Json → Json) : IO Json := do
  return case.setObjVal! "provenance" (change (← provenance case))

private def withoutMask : Json → Json
  | .obj fields => .obj (fields.erase "swarmMask")
  | other => other

private def leaves : List String := ["wordLiteral", "local", "boolLiteral"]

private def checkProfile (profile : Profile) : IO Unit := do
  let generate := fun revision =>
    profile.generate (Seed.ofNat 11) profile.nodes profile.count 64 fuel revision
  let current ← cases (generate .v3)
  ensure (generate .v3 == generate .v3) s!"{profile.name}: revision three is not deterministic"
  ensure (current.size == profile.count) s!"{profile.name}: revision-three generation did not complete"
  for case in ← cases (generate .v2) do
    ensure ((← provenance case).getObjVal? "swarmMask" matches .error _)
      s!"{profile.name}: a revision-two case records a swarm mask"
  for case in current do
    let saved ← provenance case
    let seedText ← get ((← get (saved.getObjVal? "origin")).getObjValAs? String "seed")
    let some seed := seedText.toNat? | throw (IO.userError s!"{profile.name}: invalid seed")
    let mask := GeneratorRevision.v3.caseMask (Seed.ofNat seed)
    ensure ((← get (saved.getObjVal? "swarmMask")) == maskJson mask)
      s!"{profile.name}: a case does not record the mask of its seed"
    if profile.scalar then
      let allowed := leaves ++ mask.enabled.map featureName
      let features ← get (saved.getObjValAs? (List String) "features")
      ensure (features.all allowed.contains) s!"{profile.name}: a case uses a feature its mask disables"
    ensure ((← get (profile.replay case fuel)) == case) s!"{profile.name}: a masked case failed exact replay"
    ensure (profile.replay (← withProvenance case withoutMask) fuel matches .error _)
      s!"{profile.name}: a revision-three case replayed without its mask"
    let shrunk := toJson ((mask.enabled.drop 1).map featureName)
    ensure (profile.replay (← withProvenance case (·.setObjVal! "swarmMask" shrunk)) fuel matches .error _)
      s!"{profile.name}: a changed mask replayed"
    let downgraded ← withProvenance case fun saved =>
      (profile.versions .v2).foldl (fun json (name, version) => json.setObjVal! name (toJson version)) saved
    ensure (profile.replay downgraded fuel matches .error _)
      s!"{profile.name}: a mask replayed under revision two"
  let some first := current[0]? | throw (IO.userError s!"{profile.name}: no masked case")
  let parentMask ← get ((← provenance first).getObjVal? "swarmMask")
  let reduced ← cases (← get (profile.shrink first 3 fuel))
  ensure (!reduced.isEmpty) s!"{profile.name}: a masked case has no reduction candidate"
  for candidate in reduced do
    ensure ((← get ((← provenance candidate).getObjVal? "swarmMask")) == parentMask)
      s!"{profile.name}: a reduction lost its parent's mask"
    ensure ((← get (profile.replay candidate fuel)) == candidate)
      s!"{profile.name}: a reduction of a masked case failed exact replay"

def testSourceSwarmMaskCases : IO Unit := do
  ensure (profiles.length == 11) "a G0-based profile is missing from the swarm mask checks"
  for profile in profiles do
    checkProfile profile

end Tests.SourceSwarmMaskCases
end

section
-- leanmerge: from Solcore.Test.SourceSynthesisEmitter
/-! Source-emission regressions for the supported scalar subset. These tests
check representation and scope; Rust acceptance and differential execution
are separate checks, not consequences of these string assertions. -/
set_option autoImplicit false
namespace Tests.SourceSynthesisEmitter

open Solcore.Core
open Solcore.Synthesis.Core
open Solcore.Synthesis.Source

private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)

/-- A shared fixture carrier for the case runner and external Rust checks. -/
def fixtureProgram (body : Wire.Expr) : Wire.Program :=
  {resultType := .word, dataDefinitions := [], body}

private def comparison (operation : Wire.BinaryOp) (left right : Wire.Expr) : Wire.Expr :=
  .ifE (.binary operation left right) (word 1) (word 0)

/-- The true arm reads the outer binder; the false arm reads its own binder.
The final addition must still see the outer binder after either branch. -/
def scopedBranch (selected : Bool) : Wire.Expr :=
  .letE (word 7) (.binary .wordAdd
    (.ifE (.bool selected) (.letE (word 11) (.var 1)) (.letE (word 22) (.var 0))) (.var 0))

/-- Every initially supported primitive has a fixture, including modular and
unsigned boundaries. All fixtures pass the original G0 checker. -/
def fixtures : List (String × Wire.Expr) := [
  ("zero", word 0),
  ("maximum", .word Word.maximum),
  ("add-wrap", .binary .wordAdd (.word Word.maximum) (word 1)),
  ("sub-wrap", .binary .wordSub (word 0) (word 1)),
  ("mul-wrap", .binary .wordMul (word (2 ^ 255)) (word 2)),
  ("word-and", .binary .wordAnd (word 252) (word 10)),
  ("word-or", .binary .wordOr (word 252) (word 10)),
  ("word-xor", .binary .wordXor (word 252) (word 10)),
  ("word-not", .unary .wordNot (word 10)),
  ("word-equal", comparison .wordEq (.word Word.maximum) (.word Word.maximum)),
  ("word-greater-unsigned", comparison .wordGt (word (2 ^ 255)) (word 1)),
  ("bool-not", .ifE (.unary .boolNot (.bool false)) (word 55) (word 99)),
  ("nested-locals", .letE (word 7) (.letE (word 9) (.binary .wordSub (.var 1) (.var 0)))),
  ("branch-scope-true", scopedBranch true),
  ("branch-scope-false", scopedBranch false)]

private def unsupportedBinaries : List Wire.BinaryOp :=
  [.wordDiv, .wordMod, .wordSgt, .wordShl, .wordShr, .wordByte, .wordSar,
    .wordPow, .wordSignExtend, .wordSdiv, .wordSmod]

private def binaryWordBody (operation : Wire.BinaryOp) : Wire.Expr :=
  if operation == .wordSgt then comparison operation (word 2) (word 1)
  else .binary operation (word 2) (word 1)

private def unsupportedFixtures : List (Wire.Expr × EmitError) :=
  [(.unary .wordClz (word 1), .unsupportedUnary .wordClz)] ++
  unsupportedBinaries.map (fun operation => (binaryWordBody operation, .unsupportedBinary operation)) ++
  [(.ternary .wordAddMod (word 1) (word 2) (word 3), .unsupportedTernary .wordAddMod),
   (.ternary .wordMulMod (word 1) (word 2) (word 3), .unsupportedTernary .wordMulMod),
   (.ifE (.bool true) (word 1) (.binary .wordDiv (word 1) (word 0)), .unsupportedBinary .wordDiv)]

private def admit (body : Wire.Expr) : IO CheckedWordProgram := do
  match CheckedWordProgram.ofProgram? (fixtureProgram body) with
  | some checked => pure checked
  | none => throw (IO.userError "emitter fixture failed the original G0 checker")

private def emitted (body : Wire.Expr) : IO EmittedProgram := do
  match emit (← admit body) with
  | .ok result => pure result
  | .error error => throw (IO.userError s!"supported emitter fixture was rejected: {reprStr error}")

private def scopedExpected : String := String.intercalate "\n" [
  "pragma solcore;", "import * from std;",
  "import * from std.dispatch;",
  "",
  "contract SynthesizedG0 {",
  "    function run() public returns (uint256) {",
  "        let sc_v0: word = 7;",
  "        let sc_v1: word = sc_v0;",
  "        let sc_v2: bool = false;",
  "        let sc_v3: word = 0;",
  "        if (sc_v2) {",
  "            let sc_v4: word = 11;",
  "            let sc_v5: word = sc_v4;",
  "            sc_v3 = sc_v1;",
  "        } else {",
  "            let sc_v6: word = 22;",
  "            let sc_v7: word = sc_v6;",
  "            sc_v3 = sc_v7;",
  "        }",
  "        let sc_v8: word = (sc_v3 + sc_v1);",
  "        return uint256(sc_v8);",
  "    }",
  "}", ""]

private def nestedExpected : String := String.intercalate "\n" [
  "pragma solcore;", "import * from std;", "import * from std.dispatch;", "",
  "contract SynthesizedG0 {", "    function run() public returns (uint256) {",
  "        let sc_v0: word = 7;", "        let sc_v1: word = sc_v0;",
  "        let sc_v2: word = 9;", "        let sc_v3: word = sc_v2;",
  "        let sc_v4: word = (sc_v1 - sc_v3);", "        return uint256(sc_v4);",
  "    }", "}", ""]

def testSourceSynthesisEmitter : IO Unit := do
  for (label, body) in fixtures do
    unless supported body do
      throw (IO.userError s!"supported source fixture misclassified: {label}")
    let result ← emitted body
    unless result.contractName == contractName && result.methodName == methodName &&
        result.methodSignature == "run()" && result.deployPath == ["SynthesizedG0Deploy"] &&
        result.runtimePath == ["SynthesizedG0Deploy", "SynthesizedG0"] do
      throw (IO.userError s!"source wrapper metadata changed: {label}")
    unless result == (← emitted body) do
      throw (IO.userError s!"source emission is not deterministic: {label}")
  for (body, expected) in unsupportedFixtures do
    unless !supported body do
      throw (IO.userError "unsupported source fixture was marked supported")
    match emit (← admit body) with
    | .error actual =>
      unless actual == expected do
        throw (IO.userError s!"unsupported source operation returned the wrong error: {reprStr actual}")
    | .ok _ =>
      throw (IO.userError s!"unsupported source operation was not rejected explicitly: {reprStr expected}")
  unless (← emitted (scopedBranch false)).source == scopedExpected do
    throw (IO.userError "branch-local emission changed its scope, ordering or binding indices")
  unless (← emitted (.letE (word 7) (.letE (word 9) (.binary .wordSub (.var 1) (.var 0))))).source == nestedExpected do
    throw (IO.userError "nested Core bindings changed during source emission")
  let maximum ← emitted (.word Word.maximum)
  unless (maximum.source.splitOn (toString Word.maximum.val)).length == 2 do
    throw (IO.userError "source emission truncated a 256-bit Word literal")
  unless emitterVersion == "solcore-source-g0-v2" && wrapperVersion == "solcore-word-contract-v1" do
    throw (IO.userError "emitter provenance version changed")

end Tests.SourceSynthesisEmitter
end

section
-- leanmerge: from Solcore.Test.SourceSynthesisCases
/-! Replay, bounded generation and checked reduction regressions. Saved
observations are deliberately untrusted; these checks do not prove the printer
or either compiler preserves the original Core computation. -/
set_option autoImplicit false

namespace Tests.SourceSynthesisCases

open Lean
open Solcore.Core
open Solcore.Synthesis.Core
open Solcore.Synthesis.Source

private def get {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def rejected {α : Type} (result : Except String α)
    (expected : String) : IO Unit :=
  match result with
  | .ok _ => throw (IO.userError s!"tampered case accepted: {expected}")
  | .error error => ensure (error == expected) s!"unexpected rejection: {error}; expected {expected}"

private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)

private def checked (body : Wire.Expr) : IO CheckedWordProgram :=
  match CheckedWordProgram.ofProgram? (SourceSynthesisEmitter.fixtureProgram body) with
  | some value => pure value
  | none => throw (IO.userError "source case regression fixture did not typecheck")

private def imported (body : Wire.Expr) (fuel : Nat := 1000) : IO Json := do
  get ((emitCase (← checked body) (Json.mkObj [("kind", toJson "imported")]) fuel).mapError reprStr)

private def arrayField (value : Json) (field : String) : IO (Array Json) :=
  get (value.getObjValAs? (Array Json) field)

private def stringField (value : Json) (field : String) : IO String :=
  get (value.getObjValAs? String field)

private def natField (value : Json) (field : String) : IO Nat :=
  get (value.getObjValAs? Nat field)

private def field (value : Json) (name : String) : IO Json := get (value.getObjVal? name)

private def returned (value : Nat) : Json := Json.mkObj [
  ("stage", toJson "execution"), ("status", toJson "returned"),
  ("word", toJson (toString value))]

private def outOfFuel : Json := Json.mkObj [
  ("stage", toJson "execution"), ("status", toJson "out-of-fuel")]

private def generationChecks : IO Json := do
  let corpus := generateCases (Seed.ofNat 0) 24 12 64 1000
  ensure (corpus == generateCases (Seed.ofNat 0) 24 12 64 1000)
    "bounded source corpus generation is not deterministic"
  ensure ((← stringField corpus "schema") == corpusSchema) "incorrect corpus schema"
  ensure ((← stringField corpus "status") == "complete") "bounded corpus did not complete"
  let cases ← arrayField corpus "cases"
  let excluded ← arrayField corpus "excluded"
  let attempted ← natField corpus "attempted"
  ensure (cases.size == 12 && attempted ≤ 64 && attempted == cases.size + excluded.size)
    "generation exceeded its limits or lost an attempt"
  ensure (!excluded.isEmpty) "corpus no longer exercises explicit unsupported-operation exclusions"
  for saved in cases do
    let admitted ← get (caseProgram saved)
    ensure (admitted.program.check && Wire.programNodes admitted.program ≤ 24 &&
      supported admitted.program.body) "generated case escaped its checked supported node budget"
    ensure ((← get (replayCase saved 1000)) == saved) "generated case failed exact replay"
  for excludedCase in excluded do
    ensure ((← stringField excludedCase "stage") == "emission")
      "valid-budget exclusion was not an explicit emission failure"
    let seedText ← stringField excludedCase "seed"
    let some seed := seedText.toNat? | throw (IO.userError "excluded seed is not a natural number")
    let generated ← get ((generate {seed := Seed.ofNat seed, maxProgramNodes := 24}).mapError reprStr)
    match emit generated.checkedProgram with
    | .ok _ => throw (IO.userError "an emitter-supported generated case was excluded")
    | .error error =>
      ensure ((← stringField excludedCase "reason") == reprStr error)
        "an excluded case lost the explicit emitter error"
  let exhausted := generateCases (Seed.ofNat 0) 3 3 2 1000
  ensure ((← stringField exhausted "status") == "generation-exhausted" &&
    (← natField exhausted "attempted") == 2 && (← arrayField exhausted "cases").size == 2)
    "attempt exhaustion was silently reported as a complete corpus"
  let invalidBudget := generateCases (Seed.ofNat 0) 2 1 3 1000
  ensure ((← stringField invalidBudget "status") == "generation-exhausted" &&
    (← arrayField invalidBudget "cases").isEmpty &&
    (← natField invalidBudget "attempted") == 3) "invalid generation budgets escaped the attempt bound"
  for exclusion in ← arrayField invalidBudget "excluded" do
    ensure ((← stringField exclusion "stage") == "generation" &&
      (← stringField exclusion "reason") == reprStr GenerationError.budgetTooSmall)
      "generation failures were not recorded explicitly"
  let noAttempts := generateCases (Seed.ofNat 0) 24 1 0 1000
  ensure ((← stringField noAttempts "status") == "generation-exhausted" &&
    (← natField noAttempts "attempted") == 0) "zero attempt limit was ignored"
  let noCases := generateCases (Seed.ofNat 0) 24 0 64 1000
  ensure ((← stringField noCases "status") == "complete" &&
    (← natField noCases "attempted") == 0) "empty corpus unnecessarily consumed attempts"
  let unsupported ← checked (.binary .wordDiv (word 1) (word 0))
  match emitCase unsupported (Json.mkObj [("kind", toJson "imported")]) 1000 with
  | .error (.unsupportedBinary .wordDiv) => pure ()
  | _ => throw (IO.userError "case construction did not explicitly reject unsupported division")
  pure corpus

private def observationChecks : IO Unit := do
  for (body, expected) in [
      (.binary .wordAdd (.word Word.maximum) (word 1), 0),
      (.binary .wordSub (word 0) (word 1), Word.maximum.val),
      (.ifE (.binary .wordGt (word (2 ^ 255)) (word 1)) (word 17) (word 19), 17),
      (SourceSynthesisEmitter.scopedBranch true, 14),
      (SourceSynthesisEmitter.scopedBranch false, 29)] do
    let admitted ← checked body
    ensure (observe admitted 1000 == returned expected) "original Core observation changed"
    ensure (observe admitted 0 == outOfFuel) "zero fuel was confused with a result or language fault"
  let saved ← imported (word 7)
  let forged := saved.setObjVal! "directCore" (returned 999)
  let replayed ← get (replayCase forged 1000)
  ensure (replayed == saved) "replay trusted a forged stored direct Core observation"
  let suspended ← get (replayCase forged 0)
  ensure ((← field suspended "directCore") == outOfFuel &&
    (← natField suspended "executionFuel") == 0) "replay ignored its new fuel budget"

private def tamperingChecks (corpus : Json) : IO Unit := do
  let saved ← imported (SourceSynthesisEmitter.scopedBranch false)
  rejected (replayCase (saved.setObjVal! "schema" (toJson "unknown")) 1000)
    "unsupported semantic case schema"
  rejected (replayCase (saved.setObjVal! "source" (toJson "contract Forged {}")) 1000)
    "saved source differs from emission of the original Core program"
  let provenance ← field saved "provenance"
  for (version, expected) in [
      ("generatorVersion", "generator version changed"),
      ("emitterVersion", "emitter version changed"),
      ("wrapperVersion", "wrapper version changed")] do
    rejected (replayCase (saved.setObjVal! "provenance"
      (provenance.setObjVal! version (toJson "forged"))) 1000) expected
  rejected (replayCase (saved.setObjVal! "provenance"
    (provenance.setObjVal! "features" (toJson ([] : List String)))) 1000)
    "saved features differ from the original Core program"
  let contract ← field saved "contract"
  for (name, value) in [("name", toJson "Other"), ("method", toJson "other"),
      ("signature", toJson "other()"), ("calldata", toJson "0x00000000"),
      ("constructorCalldata", toJson "0x01"), ("deployPath", toJson ["OtherDeploy"]),
      ("runtimePath", toJson ["OtherDeploy", "Other"])] do
    rejected (replayCase (saved.setObjVal! "contract" (contract.setObjVal! name value)) 1000)
      "saved contract metadata differs from the fixed wrapper"
  let generatedCases ← arrayField corpus "cases"
  let some generated := generatedCases[0]? | throw (IO.userError "generated replay fixture missing")
  let generatedProvenance ← field generated "provenance"
  let origin ← field generatedProvenance "origin"
  let withOrigin := fun replacement => generated.setObjVal! "provenance"
    (generatedProvenance.setObjVal! "origin" replacement)
  rejected (replayCase (withOrigin (origin.setObjVal! "seed" (toJson "00"))) 1000)
    "noncanonical saved seed"
  rejected (replayCase (withOrigin (origin.setObjVal! "seed" (toJson (toString (2 ^ 64 : Nat))))) 1000)
    "noncanonical saved seed"
  rejected (replayCase (withOrigin (origin.setObjVal! "finalSeed" (toJson "forged"))) 1000)
    "saved final seed differs from generation"
  rejected (replayCase (withOrigin (origin.setObjVal! "maxProgramNodes" (toJson (513 : Nat)))) 1000)
    "saved generation budget exceeds limit"
  let originalProgram ← field generated "program"
  let mut checkedDifferentSeed := false
  for other in generatedCases do
    if !checkedDifferentSeed && (← field other "program") != originalProgram then
      let otherOrigin ← field (← field other "provenance") "origin"
      rejected (replayCase (withOrigin otherOrigin) 1000)
        "saved program differs from its generation seed"
      checkedDifferentSeed := true
  ensure checkedDifferentSeed "corpus has no distinct generated seed for provenance tampering"

private def shrinkChecks : IO Unit := do
  let original ← imported (SourceSynthesisEmitter.scopedBranch true)
  let admitted ← get (caseProgram original)
  let result ← get (shrinkCases original 100 1000)
  ensure (result == (← get (shrinkCases original 100 1000))) "source case shrinking is nondeterministic"
  let candidates ← arrayField result "cases"
  let checkedCandidates := shrink admitted
  ensure (!candidates.isEmpty && candidates.size == checkedCandidates.length)
    "source reducer lost checked Core shrink candidates"
  for candidate in candidates do
    let reduced ← get (caseProgram candidate)
    ensure (reduced.program.check && accepts .word reduced.program.body && supported reduced.program.body)
      "source reduction broke typing, closure or emitter support"
    ensure ((complexity reduced.program.body).isStrictlySmaller (complexity admitted.program.body))
      "source reduction did not strictly decrease the checked Core measure"
    let emitted ← get ((emit reduced).mapError reprStr)
    ensure ((← stringField candidate "source") == emitted.source)
      "source reduction reused stale source text"
    let origin ← field (← field candidate "provenance") "origin"
    ensure ((← stringField origin "kind") == "reduced" &&
      (← field origin "parentProgram") == Wire.encodeProgram admitted.program)
      "source reduction lost its parent provenance"
    ensure ((← get (replayCase candidate 1000)) == candidate) "reduced source case failed replay"
  let limited ← arrayField (← get (shrinkCases original 2 1000)) "cases"
  ensure (limited == candidates.extract 0 2) "source shrink limit changed candidate ordering"
  ensure ((← arrayField (← get (shrinkCases original 0 1000)) "cases").isEmpty)
    "zero shrink limit was ignored"
  rejected (shrinkCases (original.setObjVal! "source" (toJson "forged")) 10 1000)
    "saved source differs from emission of the original Core program"

def testSourceSynthesisCases : IO Unit := do
  let corpus ← generationChecks
  observationChecks
  tamperingChecks corpus
  shrinkChecks

end Tests.SourceSynthesisCases
end
