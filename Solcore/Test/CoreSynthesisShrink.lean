import Solcore.Synthesis.Core.Shrink

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
