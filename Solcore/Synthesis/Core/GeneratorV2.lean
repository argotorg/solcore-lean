import Solcore.Core.Primitive
import Solcore.Synthesis.Core.Fragment
import Solcore.Synthesis.Core.Seed

/-!
Revision two of the pure G0 generation choices.

The grammar, the budget split and the checker sealing are those of revision
one. Only the way lcg64-v1 draws become choices and Word literals differs, so
revision one stays bit-for-bit for the fixed corpora.
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
are uniform over each operator list. -/
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

private def wordFormCount (budget : Nat) : Nat :=
  if budget < 2 then 1 else if budget < 3 then 2 else if budget < 4 then 4 else 6

private def boolFormCount (budget : Nat) : Nat :=
  if budget < 2 then 1 else if budget < 3 then 2 else if budget < 4 then 4 else 5

/-- Revision one's forms and budget split, with this revision's choices. -/
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
        let (form, seed) := choose seed formCount
        match target, form with
        | .word, 0 => generateLeaf .word localWordDepth seed
        | .word, 1 =>
            let (opChoice, seed) := choose seed wordUnaryOps.size
            let (operand, seed) :=
              generateExprWithFuel fuel .word localWordDepth (budget - 1) seed
            (.unary (wordUnaryOps[opChoice]?.getD .wordNot) operand, seed)
        | .word, 2 =>
            let (opChoice, seed) := choose seed wordBinaryOps.size
            let ((leftBudget, rightBudget), seed) := splitTwo (budget - 1) seed
            let (left, seed) :=
              generateExprWithFuel fuel .word localWordDepth leftBudget seed
            let (right, seed) :=
              generateExprWithFuel fuel .word localWordDepth rightBudget seed
            (.binary (wordBinaryOps[opChoice]?.getD .wordAdd) left right, seed)
        | .word, 3 =>
            if budget < 4 then
              let ((valueBudget, bodyBudget), seed) := splitTwo (budget - 1) seed
              let (value, seed) :=
                generateExprWithFuel fuel .word localWordDepth valueBudget seed
              let (body, seed) :=
                generateExprWithFuel fuel .word (localWordDepth + 1) bodyBudget seed
              (.letE value body, seed)
            else
              let (opChoice, seed) := choose seed ternaryOps.size
              let ((firstBudget, secondBudget, thirdBudget), seed) :=
                splitThree (budget - 1) seed
              let (first, seed) :=
                generateExprWithFuel fuel .word localWordDepth firstBudget seed
              let (second, seed) :=
                generateExprWithFuel fuel .word localWordDepth secondBudget seed
              let (third, seed) :=
                generateExprWithFuel fuel .word localWordDepth thirdBudget seed
              (.ternary (ternaryOps[opChoice]?.getD .wordAddMod) first second third, seed)
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
            let (opChoice, seed) := choose seed boolBinaryOps.size
            let ((leftBudget, rightBudget), seed) := splitTwo (budget - 1) seed
            let (left, seed) :=
              generateExprWithFuel fuel .word localWordDepth leftBudget seed
            let (right, seed) :=
              generateExprWithFuel fuel .word localWordDepth rightBudget seed
            (.binary (boolBinaryOps[opChoice]?.getD .wordEq) left right, seed)
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

def generateExpr
    (target : Target)
    (localWordDepth budget : Nat)
    (seed : Seed) : Expr × Seed :=
  generateExprWithFuel budget target localWordDepth budget seed

end Solcore.Synthesis.Core.GeneratorV2
