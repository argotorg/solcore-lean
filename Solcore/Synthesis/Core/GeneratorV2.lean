import Solcore.Core.Primitive
import Solcore.Synthesis.Core.FeatureMask
import Solcore.Synthesis.Core.Fragment
import Solcore.Synthesis.Core.Seed

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
