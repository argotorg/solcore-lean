import Solcore.Synthesis.Core.Fragment
import Solcore.Core.Primitive
import Solcore.Synthesis.Core.Seed
import Solcore.Core.Wire.Codec.Program
import Solcore.Core.Wire.Host

/-!
# The G0 generator

Deterministic, checker-sealed generation of the pure G0 fragment, its revisions and its swarm masks.
Main declarations: `GeneratorRevision`, `FeatureMask`, `GeneratedProgram`.
-/

section
-- leanmerge: from Solcore.Synthesis.Core.FeatureMask
/-! The G0 operators and forms a swarm mask can disable. Literal and local
leaves are always available, so every mask still admits a program. -/

set_option autoImplicit false

namespace Solcore.Synthesis.Core

open Solcore.Core.Wire

/-- The enabled maskable features, in `FeatureMask.catalog` order. -/
structure FeatureMask where
  private mk ::
  enabled : List Feature
  deriving Repr, BEq, DecidableEq

namespace FeatureMask

/-- Every operator and non-leaf form of the G0 grammar, in a fixed bit order. -/
def catalog : List Feature :=
  [.unary .boolNot, .unary .wordNot, .unary .wordClz] ++
    ([.wordAdd, .wordSub, .wordMul, .wordDiv, .wordMod, .wordAnd, .wordOr, .wordXor,
      .wordShl, .wordShr, .wordByte, .wordSar, .wordPow, .wordSignExtend, .wordSdiv, .wordSmod,
      .wordEq, .wordGt, .wordSgt] : List BinaryOp).map .binary ++
    [.ternary .wordAddMod, .ternary .wordMulMod, .letE, .ifE]

/-- The unrestricted mask of revisions one and two. -/
def all : FeatureMask := ⟨catalog⟩

/-- Bit `i` enables `catalog[i]`; higher bits are ignored. -/
def ofBits (bits : Nat) : FeatureMask :=
  ⟨catalog.zipIdx.filterMap fun (feature, index) =>
    if bits / 2 ^ index % 2 = 1 then some feature else none⟩

/-- Canonical order: any subset of the catalog, in catalog order. -/
def ofFeatures? (features : List Feature) : Option FeatureMask :=
  if features.all catalog.contains && features.eraseDups.length = features.length then
    let enabled := catalog.filter features.contains
    if enabled = features then some ⟨enabled⟩ else none
  else none

def allows (mask : FeatureMask) (feature : Feature) : Bool :=
  mask.enabled.contains feature

/-- The catalog features an emitter renders, from its own operator predicates.
Every G0 emitter renders `let` and `if`. -/
def supporting (unary : UnaryOp → Bool) (binary : BinaryOp → Bool) (ternary : TernaryOp → Bool) :
    FeatureMask :=
  ⟨catalog.filter fun
    | .unary operation => unary operation
    | .binary operation => binary operation
    | .ternary operation => ternary operation
    | _ => true⟩

/-- A unary, binary or ternary operator, rather than a `let` or `if` form. -/
def isOperator : Feature → Bool
  | .unary _ | .binary _ | .ternary _ => true
  | _ => false

def hasOperator (mask : FeatureMask) : Bool :=
  mask.enabled.any isOperator

/-- Whether every feature `mask` enables is in `support`. -/
def subset (mask support : FeatureMask) : Bool :=
  mask.enabled.all support.allows

/-- `mask` restricted to `support`. When that removes every operator `mask`
enables, the result is `support` itself, so that a restriction never leaves only
leaves and forms; a mask that enables no operator restricts plainly. -/
def within (mask support : FeatureMask) : FeatureMask :=
  let kept : FeatureMask := ⟨mask.enabled.filter support.allows⟩
  if kept.hasOperator || !mask.hasOperator then kept else support

end FeatureMask

end Solcore.Synthesis.Core
end

section
-- leanmerge: from Solcore.Synthesis.Core.GeneratorV2
/-!
Revisions two and three of the pure G0 generation choices.

The grammar, the budget split and the checker sealing are those of revision
one. Only the way lcg64-v1 draws become choices and Word literals differs, so
revision one stays bit-for-bit for the fixed corpora. Revision three restricts
revision two's grammar to a per-case swarm mask; with the full mask the
grammar is revision two itself.
-/

set_option autoImplicit false

namespace Solcore.Synthesis.Core.GeneratorV2

open Solcore.Core (Word)
open Solcore.Core.Wire

/--
SplitMix64's finalizer, a bijection on 64-bit values. Mixing each lcg64-v1
state removes the short low-bit periods within one stream and the fixed offset
between the streams of consecutive seeds.
-/
def mix (value : UInt64) : UInt64 :=
  let value := (value ^^^ (value >>> 30)) * 0xbf58476d1ce4e5b9
  let value := (value ^^^ (value >>> 27)) * 0x94d049bb133111eb
  value ^^^ (value >>> 31)

/-- Advance the lcg64-v1 state once and return the mixed new state. -/
def draw (seed : Seed) : UInt64 × Seed :=
  let (state, next) := seed.draw
  (mix state, next)

/--
Draw a choice in `[0, bound)` from the upper 32 bits of a mixed draw. A zero
bound still consumes exactly one draw and returns zero.
-/
def choose (seed : Seed) (bound : Nat) : Nat × Seed :=
  let (value, next) := draw seed
  if bound = 0 then (0, next) else ((value.toNat / 2 ^ 32) % bound, next)

/--
Boundary literals, uniformly weighted: shift counts and byte or sign-extension
indices, fixed-width masks and their successors, 64-bit limb boundaries, the
address mask, and the int256 limits with their neighbours.
-/
def edgeBank : Array Word :=
  (#[0, 1, 2, 3, 7, 8, 30, 31, 32, 63, 64, 127, 128, 255, 256, 257,
    2 ^ 16 - 1, 2 ^ 16, 2 ^ 32 - 1, 2 ^ 32, 2 ^ 64 - 1, 2 ^ 64, 2 ^ 128 - 1, 2 ^ 128,
    2 ^ 160 - 1, 2 ^ 192, 2 ^ 248, 2 ^ 255 - 1, 2 ^ 255, 2 ^ 255 + 1,
    2 ^ 256 - 2, 2 ^ 256 - 1] : Array Nat).map Word.ofNatModulo

/--
Every Word literal consumes six draws in a fixed order: edge versus random, a
bank index, then four high-to-low limbs. Half of the literals take the bank
entry and half the full 256-bit random Word, each decided by its own draw.
-/
def drawWord (seed : Seed) : Word × Seed :=
  let (kind, seed) := choose seed 2
  let (index, seed) := choose seed edgeBank.size
  let (high, seed) := draw seed
  let (next, seed) := draw seed
  let (nextLow, seed) := draw seed
  let (low, seed) := draw seed
  let value :=
    if kind = 0 then
      edgeBank[index]?.getD Word.zero
    else
      Word.ofNatModulo
        (high.toNat * 2 ^ 192 + next.toNat * 2 ^ 128 + nextLow.toNat * 2 ^ 64 + low.toNat)
  (value, seed)

def drawBool (seed : Seed) : Bool × Seed :=
  let (choice, seed) := choose seed 2
  (choice = 1, seed)

private def generateLeaf
    (target : Target)
    (localWordDepth : Nat)
    (seed : Seed) : Expr × Seed :=
  match target with
  | .bool =>
      let (value, seed) := drawBool seed
      (.bool value, seed)
  | .word =>
      if localWordDepth = 0 then
        let (value, seed) := drawWord seed
        (.word value, seed)
      else
        let (kind, seed) := choose seed 2
        if kind = 0 then
          let (value, seed) := drawWord seed
          (.word value, seed)
        else
          let (index, seed) := choose seed localWordDepth
          (.var index, seed)

/- Revision one's odd bounds only avoided low-bit correlation; these choices
are uniform over each operator list. A mask keeps the order of what it enables. -/
private def wordUnaryOps : Array UnaryOp := #[.wordNot, .wordClz]

private def wordBinaryOps : Array BinaryOp :=
  #[.wordAdd, .wordSub, .wordMul, .wordDiv, .wordMod, .wordAnd, .wordOr, .wordXor,
    .wordShl, .wordShr, .wordByte, .wordSar, .wordPow, .wordSignExtend, .wordSdiv, .wordSmod]

private def boolBinaryOps : Array BinaryOp := #[.wordEq, .wordGt, .wordSgt]

private def ternaryOps : Array TernaryOp := #[.wordAddMod, .wordMulMod]

private def splitTwo (total : Nat) (seed : Seed) : (Nat × Nat) × Seed :=
  let extras := total - 2
  let (leftExtra, seed) := choose seed (extras + 1)
  ((leftExtra + 1, extras - leftExtra + 1), seed)

private def splitThree
    (total : Nat)
    (seed : Seed) : (Nat × Nat × Nat) × Seed :=
  let extras := total - 3
  let (firstExtra, seed) := choose seed (extras + 1)
  let remaining := extras - firstExtra
  let (secondExtra, seed) := choose seed (remaining + 1)
  ((firstExtra + 1, secondExtra + 1, remaining - secondExtra + 1), seed)

/-- The grammar's forms, in revision two's choice order. -/
private inductive Form where
  | leaf | unary | binary | ternary | letE | ifE

/-- Revision two's Word forms for a budget. -/
private def wordForms (budget : Nat) : List Form :=
  if budget < 2 then [.leaf]
  else if budget < 3 then [.leaf, .unary]
  else if budget < 4 then [.leaf, .unary, .binary, .letE]
  else [.leaf, .unary, .binary, .ternary, .letE, .ifE]

/-- Revision two's Bool forms for a budget. -/
private def boolForms (budget : Nat) : List Form :=
  if budget < 2 then [.leaf]
  else if budget < 3 then [.leaf, .unary]
  else if budget < 4 then [.leaf, .unary, .binary, .letE]
  else [.leaf, .unary, .binary, .letE, .ifE]

/-- A form is enabled when the mask allows it or one of its operators. -/
private def enabled (mask : FeatureMask) (target : Target) : Form → Bool
  | .leaf => true
  | .unary => match target with
      | .word => wordUnaryOps.any fun op => mask.allows (.unary op)
      | .bool => mask.allows (.unary .boolNot)
  | .binary => match target with
      | .word => wordBinaryOps.any fun op => mask.allows (.binary op)
      | .bool => boolBinaryOps.any fun op => mask.allows (.binary op)
  | .ternary => ternaryOps.any fun op => mask.allows (.ternary op)
  | .letE => mask.allows .letE
  | .ifE => mask.allows .ifE

/--
Revision two's form choice. A disabled form is replaced by a second, uniform
choice among the enabled non-leaf forms, so a mask keeps revision two's leaf
probability, and therefore its program sizes, instead of ending programs early.
With the full mask no form is replaced.
-/
private def chooseForm (mask : FeatureMask) (target : Target) (budget : Nat) (seed : Seed) :
    Form × Seed :=
  let forms := match target with
    | .word => wordForms budget
    | .bool => boolForms budget
  let (formChoice, seed) := choose seed forms.length
  let form := forms[formChoice]?.getD .leaf
  if enabled mask target form then (form, seed)
  else
    let others := forms.filter fun form =>
      match form with
      | .leaf => false
      | form => enabled mask target form
    let (otherChoice, seed) := choose seed others.length
    (others[otherChoice]?.getD .leaf, seed)

/-- Revision one's forms and budget split, with this revision's choices. The
mask removes forms and operators; the full mask gives revision two itself. -/
private def generateExprWithFuel (mask : FeatureMask) :
    Nat → Target → Nat → Nat → Seed → Expr × Seed
  | 0, target, localWordDepth, _, seed =>
      generateLeaf target localWordDepth seed
  | fuel + 1, target, localWordDepth, budget, seed =>
      if budget ≤ 1 then
        generateLeaf target localWordDepth seed
      else
        let (form, seed) := chooseForm mask target budget seed
        match target, form with
        | _, .leaf => generateLeaf target localWordDepth seed
        | .word, .unary =>
            let ops := wordUnaryOps.filter fun op => mask.allows (.unary op)
            let (opChoice, seed) := choose seed ops.size
            let (operand, seed) :=
              generateExprWithFuel mask fuel .word localWordDepth (budget - 1) seed
            (.unary (ops[opChoice]?.getD .wordNot) operand, seed)
        | .word, .binary =>
            let ops := wordBinaryOps.filter fun op => mask.allows (.binary op)
            let (opChoice, seed) := choose seed ops.size
            let ((leftBudget, rightBudget), seed) := splitTwo (budget - 1) seed
            let (left, seed) :=
              generateExprWithFuel mask fuel .word localWordDepth leftBudget seed
            let (right, seed) :=
              generateExprWithFuel mask fuel .word localWordDepth rightBudget seed
            (.binary (ops[opChoice]?.getD .wordAdd) left right, seed)
        | .word, .ternary =>
            let ops := ternaryOps.filter fun op => mask.allows (.ternary op)
            let (opChoice, seed) := choose seed ops.size
            let ((firstBudget, secondBudget, thirdBudget), seed) :=
              splitThree (budget - 1) seed
            let (first, seed) :=
              generateExprWithFuel mask fuel .word localWordDepth firstBudget seed
            let (second, seed) :=
              generateExprWithFuel mask fuel .word localWordDepth secondBudget seed
            let (third, seed) :=
              generateExprWithFuel mask fuel .word localWordDepth thirdBudget seed
            (.ternary (ops[opChoice]?.getD .wordAddMod) first second third, seed)
        | target, .letE =>
            let ((valueBudget, bodyBudget), seed) := splitTwo (budget - 1) seed
            let (value, seed) :=
              generateExprWithFuel mask fuel .word localWordDepth valueBudget seed
            let (body, seed) :=
              generateExprWithFuel mask fuel target (localWordDepth + 1) bodyBudget seed
            (.letE value body, seed)
        | target, .ifE =>
            let ((conditionBudget, thenBudget, elseBudget), seed) :=
              splitThree (budget - 1) seed
            let (condition, seed) :=
              generateExprWithFuel mask fuel .bool localWordDepth conditionBudget seed
            let (thenBranch, seed) :=
              generateExprWithFuel mask fuel target localWordDepth thenBudget seed
            let (elseBranch, seed) :=
              generateExprWithFuel mask fuel target localWordDepth elseBudget seed
            (.ifE condition thenBranch elseBranch, seed)
        | .bool, .unary =>
            let (operand, seed) :=
              generateExprWithFuel mask fuel .bool localWordDepth (budget - 1) seed
            (.unary .boolNot operand, seed)
        | .bool, .binary =>
            let ops := boolBinaryOps.filter fun op => mask.allows (.binary op)
            let (opChoice, seed) := choose seed ops.size
            let ((leftBudget, rightBudget), seed) := splitTwo (budget - 1) seed
            let (left, seed) :=
              generateExprWithFuel mask fuel .word localWordDepth leftBudget seed
            let (right, seed) :=
              generateExprWithFuel mask fuel .word localWordDepth rightBudget seed
            (.binary (ops[opChoice]?.getD .wordEq) left right, seed)
        | .bool, .ternary => generateLeaf .bool localWordDepth seed

/-- Revision two generates with the full mask; revision three passes its swarm mask. -/
def generateExpr
    (target : Target)
    (localWordDepth budget : Nat)
    (seed : Seed)
    (mask : FeatureMask := FeatureMask.all) : Expr × Seed :=
  generateExprWithFuel mask budget target localWordDepth budget seed

private def swarmDomain : UInt64 := 0x737761726d6d736b

/--
Revision three's swarm mask of a case seed. Each catalog feature is enabled by
its own bit of one mixed, domain-separated draw, so about half are enabled.
Leaves stay available; a mask without any Word operator or form, of
probability 2^-22, generates single leaves.
-/
def swarmMask (seed : Seed) : FeatureMask :=
  FeatureMask.ofBits (mix ((seed.toUInt64 ^^^ swarmDomain) + 0x9e3779b97f4a7c15)).toNat

end Solcore.Synthesis.Core.GeneratorV2
end

section
-- leanmerge: from Solcore.Synthesis.Core.Generator
/-! Deterministic, checker-sealed generation for the pure G0 Core fragment. -/

set_option autoImplicit false

namespace Solcore.Synthesis.Core

open Solcore.Core.Wire

/--
The replay-visible G0 choice semantics. Fixed corpora pin `v1`; `v2` mixes
each draw, takes choices from its upper bits and widens the literal bank; `v3`
restricts `v2` to a swarm mask drawn once per case; `v4` restricts that mask
further to the features the profile's emitter renders.
-/
inductive GeneratorRevision where
  | v1
  | v2
  | v3
  | v4
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The complete replay input for one generated Program. -/
structure GenerationRequest where
  seed : Seed
  maxProgramNodes : Nat
  revision : GeneratorRevision := .v1
  /-- The swarm mask of revisions three and four; the others use the full grammar. -/
  mask : FeatureMask := FeatureMask.all
  deriving Repr, BEq, DecidableEq

/-- Configuration failure and the one impossible-by-design invariant failure. -/
inductive GenerationError where
  | budgetTooSmall
  | checkerInvariant
  deriving Repr, BEq, DecidableEq

/-- The minimum Program size: wrapper, Word result type, and one body node. -/
def minimumProgramNodes : Nat := 3

/-- Version of the generation choices layered on the versioned seed algorithm. -/
def generatorVersion : String := "core-g0-v1/" ++ Seed.algorithmId

namespace GeneratorRevision

def all : List GeneratorRevision := [.v1, .v2, .v3, .v4]

/-- Every revision layers its choices on the unchanged lcg64-v1 draws. -/
def version : GeneratorRevision → String
  | .v1 => generatorVersion
  | .v2 => "core-g0-v2/" ++ Seed.algorithmId
  | .v3 => "core-g0-v3/" ++ Seed.algorithmId
  | .v4 => "core-g0-v4/" ++ Seed.algorithmId

/-- The revisions every generator accepts. Revision four needs the features of
the profile's emitter, which only the pure profiles supply, so the stateful
tools parse with this and stop at revision three. -/
def ofVersion? (version : String) : Option GeneratorRevision :=
  [GeneratorRevision.v1, .v2, .v3].find? (·.version = version)

/-- Every revision, for the pure profiles, which pass their emitter's features
to `caseMask`. -/
def ofPureVersion? (version : String) : Option GeneratorRevision :=
  all.find? (·.version = version)

/-- Whether a revision draws, and records, a swarm mask per case. -/
def masked : GeneratorRevision → Bool
  | .v3 | .v4 => true
  | _ => false

/-- The mask of a case: drawn from the case seed for `v3`; for `v4` that mask
restricted to `support`, the features of the profile's emitter; otherwise
full. Every G0 program that one emitter renders, such as each helper of a case,
uses this one mask. -/
def caseMask (revision : GeneratorRevision) (seed : Seed) (support : FeatureMask := FeatureMask.all) :
    FeatureMask :=
  match revision with
  | .v3 => GeneratorV2.swarmMask seed
  | .v4 => (GeneratorV2.swarmMask seed).within support
  | _ => FeatureMask.all

end GeneratorRevision

/-- A checked Program together with the exact replay provenance that produced it. -/
structure GeneratedProgram where
  private mk ::
  initialSeed : Seed
  finalSeed : Seed
  maxProgramNodes : Nat
  revision : GeneratorRevision
  mask : FeatureMask
  checkedProgram : CheckedWordProgram

namespace GeneratedProgram

def program (generated : GeneratedProgram) : Program :=
  generated.checkedProgram.program

def nodeCount (generated : GeneratedProgram) : Nat :=
  programNodes generated.program

/-- Coverage is always classified from the generated AST, never sampled separately. -/
def features (generated : GeneratedProgram) : List Feature :=
  Solcore.Synthesis.Core.features generated.program.body

end GeneratedProgram

private def edgeWord : Nat → Solcore.Core.Word
  | 0 => Solcore.Core.Word.zero
  | 1 => Solcore.Core.Word.ofNatModulo 1
  | 2 => Solcore.Core.Word.ofNatModulo 2
  | 3 => Solcore.Core.Word.ofNatModulo 31
  | 4 => Solcore.Core.Word.ofNatModulo 32
  | 5 => Solcore.Core.Word.ofNatModulo 256
  | 6 => Solcore.Core.Word.ofNatModulo (2 ^ 255)
  | _ => Solcore.Core.Word.maximum

private def wordFromLimbs
    (high next nextLow low : UInt64) : Solcore.Core.Word :=
  Solcore.Core.Word.ofNatModulo
    (high.toNat * 2 ^ 192 + next.toNat * 2 ^ 128 +
      nextLow.toNat * 2 ^ 64 + low.toNat)

/--
Every Word literal consumes five draws in a fixed order: selector, then four
high-to-low limbs. Even an edge-bank result consumes all four limbs.
-/
private def drawWord (seed : Seed) : Solcore.Core.Word × Seed :=
  let (selector, seed) := seed.draw
  let (high, seed) := seed.draw
  let (next, seed) := seed.draw
  let (nextLow, seed) := seed.draw
  let (low, seed) := seed.draw
  let value :=
    if selector.toNat % 2 = 0 then
      edgeWord ((selector.toNat / 2) % 8)
    else
      wordFromLimbs high next nextLow low
  (value, seed)

private def drawBool (seed : Seed) : Bool × Seed :=
  let (choice, seed) := seed.choose 2
  (choice = 1, seed)

private def generateLeaf
    (target : Target)
    (localWordDepth : Nat)
    (seed : Seed) : Expr × Seed :=
  match target with
  | .bool =>
      let (value, seed) := drawBool seed
      (.bool value, seed)
  | .word =>
      if localWordDepth = 0 then
        let (value, seed) := drawWord seed
        (.word value, seed)
      else
        let (kind, seed) := seed.choose 2
        if kind = 0 then
          let (value, seed) := drawWord seed
          (.word value, seed)
        else
          let (index, seed) := seed.choose localWordDepth
          (.var index, seed)

private def wordUnaryOp (choice : Nat) : UnaryOp :=
  if choice % 2 = 0 then .wordNot else .wordClz

private def wordBinaryOp : Nat → BinaryOp
  | 0 => .wordAdd
  | 1 => .wordSub
  | 2 => .wordMul
  | 3 => .wordDiv
  | 4 => .wordMod
  | 5 => .wordAnd
  | 6 => .wordOr
  | 7 => .wordXor
  | 8 => .wordShl
  | 9 => .wordShr
  | 10 => .wordByte
  | 11 => .wordSar
  | 12 => .wordPow
  | 13 => .wordSignExtend
  | 14 => .wordSdiv
  | _ => .wordSmod

private def boolBinaryOp : Nat → BinaryOp
  | 0 => .wordEq
  | 1 => .wordGt
  | _ => .wordSgt

private def ternaryOp (choice : Nat) : TernaryOp :=
  if choice % 2 = 0 then .wordAddMod else .wordMulMod

private def splitTwo (total : Nat) (seed : Seed) : (Nat × Nat) × Seed :=
  let extras := total - 2
  let (leftExtra, seed) := seed.choose (extras + 1)
  ((leftExtra + 1, extras - leftExtra + 1), seed)

private def splitThree
    (total : Nat)
    (seed : Seed) : (Nat × Nat × Nat) × Seed :=
  let extras := total - 3
  let (firstExtra, seed) := seed.choose (extras + 1)
  let remaining := extras - firstExtra
  let (secondExtra, seed) := seed.choose (remaining + 1)
  ((firstExtra + 1, secondExtra + 1, remaining - secondExtra + 1), seed)

private def wordFormCount (budget : Nat) : Nat :=
  if budget < 2 then 1 else if budget < 3 then 2 else if budget < 4 then 4 else 6

private def boolFormCount (budget : Nat) : Nat :=
  if budget < 2 then 1 else if budget < 3 then 2 else if budget < 4 then 4 else 5

/-- Structural fuel makes termination independent of arithmetic budget proofs. -/
private def generateExprWithFuel :
    Nat → Target → Nat → Nat → Seed → Expr × Seed
  | 0, target, localWordDepth, _, seed =>
      generateLeaf target localWordDepth seed
  | fuel + 1, target, localWordDepth, budget, seed =>
      if budget ≤ 1 then
        generateLeaf target localWordDepth seed
      else
        let formCount :=
          match target with
          | .word => wordFormCount budget
          | .bool => boolFormCount budget
        let (form, seed) := seed.choose formCount
        match target, form with
        | .word, 0 => generateLeaf .word localWordDepth seed
        | .word, 1 =>
            /- The odd choice bound avoids low-bit correlation with form choice. -/
            let (opChoice, seed) := seed.choose 3
            let (operand, seed) :=
              generateExprWithFuel fuel .word localWordDepth (budget - 1) seed
            (.unary (wordUnaryOp opChoice) operand, seed)
        | .word, 2 =>
            let (opChoice, seed) := seed.choose 17
            let ((leftBudget, rightBudget), seed) := splitTwo (budget - 1) seed
            let (left, seed) :=
              generateExprWithFuel fuel .word localWordDepth leftBudget seed
            let (right, seed) :=
              generateExprWithFuel fuel .word localWordDepth rightBudget seed
            (.binary (wordBinaryOp (opChoice % 16)) left right, seed)
        | .word, 3 =>
            if budget < 4 then
              let ((valueBudget, bodyBudget), seed) := splitTwo (budget - 1) seed
              let (value, seed) :=
                generateExprWithFuel fuel .word localWordDepth valueBudget seed
              let (body, seed) :=
                generateExprWithFuel fuel .word (localWordDepth + 1) bodyBudget seed
              (.letE value body, seed)
            else
              let (opChoice, seed) := seed.choose 3
              let ((firstBudget, secondBudget, thirdBudget), seed) :=
                splitThree (budget - 1) seed
              let (first, seed) :=
                generateExprWithFuel fuel .word localWordDepth firstBudget seed
              let (second, seed) :=
                generateExprWithFuel fuel .word localWordDepth secondBudget seed
              let (third, seed) :=
                generateExprWithFuel fuel .word localWordDepth thirdBudget seed
              (.ternary (ternaryOp opChoice) first second third, seed)
        | .word, 4 =>
            let ((valueBudget, bodyBudget), seed) := splitTwo (budget - 1) seed
            let (value, seed) :=
              generateExprWithFuel fuel .word localWordDepth valueBudget seed
            let (body, seed) :=
              generateExprWithFuel fuel .word (localWordDepth + 1) bodyBudget seed
            (.letE value body, seed)
        | .word, _ =>
            let ((conditionBudget, thenBudget, elseBudget), seed) :=
              splitThree (budget - 1) seed
            let (condition, seed) :=
              generateExprWithFuel fuel .bool localWordDepth conditionBudget seed
            let (thenBranch, seed) :=
              generateExprWithFuel fuel .word localWordDepth thenBudget seed
            let (elseBranch, seed) :=
              generateExprWithFuel fuel .word localWordDepth elseBudget seed
            (.ifE condition thenBranch elseBranch, seed)
        | .bool, 0 => generateLeaf .bool localWordDepth seed
        | .bool, 1 =>
            let (operand, seed) :=
              generateExprWithFuel fuel .bool localWordDepth (budget - 1) seed
            (.unary .boolNot operand, seed)
        | .bool, 2 =>
            let (opChoice, seed) := seed.choose 3
            let ((leftBudget, rightBudget), seed) := splitTwo (budget - 1) seed
            let (left, seed) :=
              generateExprWithFuel fuel .word localWordDepth leftBudget seed
            let (right, seed) :=
              generateExprWithFuel fuel .word localWordDepth rightBudget seed
            (.binary (boolBinaryOp opChoice) left right, seed)
        | .bool, 3 =>
            let ((valueBudget, bodyBudget), seed) := splitTwo (budget - 1) seed
            let (value, seed) :=
              generateExprWithFuel fuel .word localWordDepth valueBudget seed
            let (body, seed) :=
              generateExprWithFuel fuel .bool (localWordDepth + 1) bodyBudget seed
            (.letE value body, seed)
        | .bool, _ =>
            let ((conditionBudget, thenBudget, elseBudget), seed) :=
              splitThree (budget - 1) seed
            let (condition, seed) :=
              generateExprWithFuel fuel .bool localWordDepth conditionBudget seed
            let (thenBranch, seed) :=
              generateExprWithFuel fuel .bool localWordDepth thenBudget seed
            let (elseBranch, seed) :=
              generateExprWithFuel fuel .bool localWordDepth elseBudget seed
            (.ifE condition thenBranch elseBranch, seed)

private def generateExpr
    (target : Target)
    (localWordDepth budget : Nat)
    (seed : Seed) : Expr × Seed :=
  generateExprWithFuel budget target localWordDepth budget seed

/-- Generate one bounded Word Program and seal it through the Wire checker. -/
def generate (request : GenerationRequest) : Except GenerationError GeneratedProgram :=
  if request.maxProgramNodes < minimumProgramNodes then
    .error .budgetTooSmall
  else
    let bodyBudget := request.maxProgramNodes - 2
    let mask := if request.revision.masked then request.mask else FeatureMask.all
    let (body, finalSeed) := match request.revision with
      | .v1 => generateExpr .word 0 bodyBudget request.seed
      | .v2 => GeneratorV2.generateExpr .word 0 bodyBudget request.seed
      | .v3 | .v4 => GeneratorV2.generateExpr .word 0 bodyBudget request.seed mask
    let program : Program := {
      resultType := .word
      dataDefinitions := []
      body
    }
    match CheckedWordProgram.ofProgram? program with
    | none => .error .checkerInvariant
    | some checkedProgram => .ok {
        initialSeed := request.seed
        finalSeed
        maxProgramNodes := request.maxProgramNodes
        revision := request.revision
        mask
        checkedProgram
      }

end Solcore.Synthesis.Core
end
