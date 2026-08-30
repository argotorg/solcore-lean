import Solcore.Core.Primitive
import Solcore.Core.Wire.V3.Codec.Program
import Solcore.Synthesis.CoreV3.Fragment

/-! Deterministic, checker-sealed shrinking for the pure G0 Core v3 fragment. -/

set_option autoImplicit false

namespace Solcore.Synthesis.CoreV3

open Solcore.Core.Wire

mutual

  /-- Sum of Word literal values, plus one for every true Boolean literal. -/
  def literalWeight : V3.Expr → Nat
    | .unit | .var _ => 0
    | .bool value => if value then 1 else 0
    | .word value => value.val
    | .pair left right | .apply left right | .storeCell left right |
        .binary _ left right | .letE left right =>
        literalWeight left + literalWeight right
    | .first operand | .second operand | .loadCell operand |
        .construct _ operand | .unary _ operand =>
        literalWeight operand
    | .lambda _ _ body => literalWeight body
    | .inLeft _ payload | .inRight _ payload | .newCell _ payload =>
        literalWeight payload
    | .caseE scrutinee leftBranch rightBranch |
        .ternary _ scrutinee leftBranch rightBranch |
        .ifE scrutinee leftBranch rightBranch =>
        literalWeight scrutinee + literalWeight leftBranch +
          literalWeight rightBranch
    | .matchData _ _ scrutinee branches =>
        literalWeight scrutinee + literalWeightList branches
  termination_by expression => sizeOf expression

  def literalWeightList : List V3.Expr → Nat
    | [] => 0
    | expression :: rest =>
        literalWeight expression + literalWeightList rest
  termination_by expressions => sizeOf expressions

end

/-- The fixed lexicographic G0 shrink measure. -/
structure Complexity where
  exprNodes : Nat
  literalWeight : Nat
  deriving Repr, BEq, DecidableEq

namespace Complexity

/-- Lexicographic order: nodes first, literal magnitude second. -/
def StrictlySmaller (candidate source : Complexity) : Prop :=
  candidate.exprNodes < source.exprNodes ∨
    (candidate.exprNodes = source.exprNodes ∧
      candidate.literalWeight < source.literalWeight)

instance (candidate source : Complexity) :
    Decidable (candidate.StrictlySmaller source) := by
  unfold StrictlySmaller
  infer_instance

def isStrictlySmaller (candidate source : Complexity) : Bool :=
  decide (candidate.StrictlySmaller source)

end Complexity

def complexity (expression : V3.Expr) : Complexity := {
  exprNodes := V3.exprNodes expression
  literalWeight := CoreV3.literalWeight expression
}

/-- One rechecked shrink result. The private constructor prevents callers from
forging the strict-decrease or node-bound evidence. -/
structure ShrinkCandidate where private mk ::
  checkedProgram : CheckedWordProgram
  sourceComplexity : Complexity
  candidateComplexity : Complexity
  strict : candidateComplexity.StrictlySmaller sourceComplexity
  nodesNonincreasing :
    candidateComplexity.exprNodes ≤ sourceComplexity.exprNodes

namespace ShrinkCandidate

def program (candidate : ShrinkCandidate) : V3.Program :=
  candidate.checkedProgram.program

def body (candidate : ShrinkCandidate) : V3.Expr :=
  candidate.program.body

end ShrinkCandidate

private def canonical : Target → V3.Expr
  | .word => .word Solcore.Core.Word.zero
  | .bool => .bool false

/-- Remove one surrounding Word binder without capturing another variable.

`cutoff` counts binders introduced inside the expression. A reference to the
removed binder fails; references beyond it are shifted down by one. -/
private def dropLocalAt (cutoff : Nat) : V3.Expr → Option V3.Expr
  | .word value => some (.word value)
  | .bool value => some (.bool value)
  | .var index =>
      if index < cutoff then some (.var index)
      else if index = cutoff then none
      else some (.var (index - 1))
  | .letE initializer body => do
      let initializer ← dropLocalAt cutoff initializer
      let body ← dropLocalAt (cutoff + 1) body
      pure (.letE initializer body)
  | .ifE condition thenBranch elseBranch => do
      let condition ← dropLocalAt cutoff condition
      let thenBranch ← dropLocalAt cutoff thenBranch
      let elseBranch ← dropLocalAt cutoff elseBranch
      pure (.ifE condition thenBranch elseBranch)
  | .unary op operand =>
      .unary op <$> dropLocalAt cutoff operand
  | .binary op left right => do
      let left ← dropLocalAt cutoff left
      let right ← dropLocalAt cutoff right
      pure (.binary op left right)
  | .ternary op first second third => do
      let first ← dropLocalAt cutoff first
      let second ← dropLocalAt cutoff second
      let third ← dropLocalAt cutoff third
      pure (.ternary op first second third)
  | _ => none

/-- Raw role-directed candidates. Invalid binder lifting is intentional here:
the sole public sealing pass rejects it through `CheckedWordProgram.ofProgram?`. -/
private def shrinkAt
    (localWordDepth : Nat)
    (target : Target)
    (expression : V3.Expr) : List V3.Expr :=
  let simplest := canonical target
  match expression with
  | .word _ | .bool _ | .var _ => [simplest]
  | .letE initializer body =>
      let liftedBody := (dropLocalAt 0 body).toList
      let direct :=
        match target with
        | .word => initializer :: liftedBody
        | .bool => liftedBody
      [simplest] ++ direct ++
        (shrinkAt localWordDepth .word initializer).map
          (fun candidate => .letE candidate body) ++
        (shrinkAt (localWordDepth + 1) target body).map
          (fun candidate => .letE initializer candidate)
  | .ifE condition thenBranch elseBranch =>
      let direct :=
        match target with
        | .word => [thenBranch, elseBranch]
        | .bool => [condition, thenBranch, elseBranch]
      [simplest] ++ direct ++
        (shrinkAt localWordDepth .bool condition).map
          (fun candidate => .ifE candidate thenBranch elseBranch) ++
        (shrinkAt localWordDepth target thenBranch).map
          (fun candidate => .ifE condition candidate elseBranch) ++
        (shrinkAt localWordDepth target elseBranch).map
          (fun candidate => .ifE condition thenBranch candidate)
  | .unary op operand =>
      let operandTarget := Target.unaryOperand op
      [simplest, operand] ++
        (shrinkAt localWordDepth operandTarget operand).map
          (fun candidate => .unary op candidate)
  | .binary op left right =>
      let direct :=
        match target with
        | .word => [left, right]
        | .bool => []
      [simplest] ++ direct ++
        (shrinkAt localWordDepth .word left).map
          (fun candidate => .binary op candidate right) ++
        (shrinkAt localWordDepth .word right).map
          (fun candidate => .binary op left candidate)
  | .ternary op first second third =>
      [simplest, first, second, third] ++
        (shrinkAt localWordDepth .word first).map
          (fun candidate => .ternary op candidate second third) ++
        (shrinkAt localWordDepth .word second).map
          (fun candidate => .ternary op first candidate third) ++
        (shrinkAt localWordDepth .word third).map
          (fun candidate => .ternary op first second candidate)
  | _ => [simplest]

private def bodyKey (expression : V3.Expr) : String :=
  (V3.encodeExpr expression).compress

private def stableDeduplicateFrom
    (seen : List String) : List V3.Expr → List V3.Expr
  | [] => []
  | expression :: rest =>
      let key := bodyKey expression
      if seen.contains key then
        stableDeduplicateFrom seen rest
      else
        expression :: stableDeduplicateFrom (key :: seen) rest

private def stableDeduplicate (expressions : List V3.Expr) : List V3.Expr :=
  stableDeduplicateFrom [] expressions

private def sealCandidates
    (source : CheckedWordProgram)
    (sourceComplexity : Complexity) :
    List V3.Expr → List ShrinkCandidate
  | [] => []
  | expression :: rest =>
      let remaining := sealCandidates source sourceComplexity rest
      let program : V3.Program := {
        resultType := source.program.resultType
        dataDefinitions := source.program.dataDefinitions
        body := expression
      }
      match CheckedWordProgram.ofProgram? program with
      | none => remaining
      | some checkedProgram =>
          let candidateComplexity := complexity expression
          if strict : candidateComplexity.StrictlySmaller sourceComplexity then
            if nodes : candidateComplexity.exprNodes ≤ sourceComplexity.exprNodes then
              ⟨checkedProgram, sourceComplexity, candidateComplexity,
                strict, nodes⟩ :: remaining
            else
              remaining
          else
            remaining

/-- Enumerate deterministic, distinct, rechecked strict shrink candidates. -/
def shrink (source : CheckedWordProgram) : List ShrinkCandidate :=
  let sourceComplexity := complexity source.program.body
  sealCandidates source sourceComplexity <|
    stableDeduplicate (shrinkAt 0 .word source.program.body)

end Solcore.Synthesis.CoreV3
