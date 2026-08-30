import Solcore.Core.Primitive
import Solcore.Core.Wire.V3.Codec.Program
import Solcore.Core.Wire.V3.Host
import Solcore.Synthesis.CoreV3.Fragment
import Solcore.Synthesis.CoreV3.Seed

/-! Deterministic, checker-sealed generation for the pure G0 Core v3 fragment. -/

set_option autoImplicit false

namespace Solcore.Synthesis.CoreV3

open Solcore.Core.Wire

/-- The complete replay input for one generated Program. -/
structure GenerationRequest where
  seed : Seed
  maxProgramNodes : Nat
  deriving Repr, BEq, DecidableEq

/-- Configuration failure and the one impossible-by-design invariant failure. -/
inductive GenerationError where
  | budgetTooSmall
  | checkerInvariant
  deriving Repr, BEq, DecidableEq

/-- The minimum v3 Program size: wrapper, Word result type, and one body node. -/
def minimumProgramNodes : Nat := 3

/-- Version of the generation choices layered on the versioned seed algorithm. -/
def generatorVersion : String := "core-v3-g0-v1/" ++ Seed.algorithmId

/-- A checked Program together with the exact replay provenance that produced it. -/
structure GeneratedProgram where
  private mk ::
  initialSeed : Seed
  finalSeed : Seed
  maxProgramNodes : Nat
  checkedProgram : CheckedWordProgram

namespace GeneratedProgram

def program (generated : GeneratedProgram) : V3.Program :=
  generated.checkedProgram.program

def nodeCount (generated : GeneratedProgram) : Nat :=
  V3.programNodes generated.program

/-- Coverage is always classified from the generated AST, never sampled separately. -/
def features (generated : GeneratedProgram) : List Feature :=
  CoreV3.features generated.program.body

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
    (seed : Seed) : V3.Expr × Seed :=
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

private def wordUnaryOp (choice : Nat) : V3.UnaryOp :=
  if choice % 2 = 0 then .wordNot else .wordClz

private def wordBinaryOp : Nat → V3.BinaryOp
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

private def boolBinaryOp : Nat → V3.BinaryOp
  | 0 => .wordEq
  | 1 => .wordGt
  | _ => .wordSgt

private def ternaryOp (choice : Nat) : V3.TernaryOp :=
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
    Nat → Target → Nat → Nat → Seed → V3.Expr × Seed
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
    (seed : Seed) : V3.Expr × Seed :=
  generateExprWithFuel budget target localWordDepth budget seed

/-- Generate one bounded Word Program and seal it through the frozen v3 checker. -/
def generate (request : GenerationRequest) : Except GenerationError GeneratedProgram :=
  if request.maxProgramNodes < minimumProgramNodes then
    .error .budgetTooSmall
  else
    let bodyBudget := request.maxProgramNodes - 2
    let (body, finalSeed) := generateExpr .word 0 bodyBudget request.seed
    let program : V3.Program := {
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
        checkedProgram
      }

end Solcore.Synthesis.CoreV3
