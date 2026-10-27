import Solcore.Synthesis.Core.Generator

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
