import Solcore.Synthesis.CoreV3.Shrink

/-! Focused regressions for deterministic checked Core v3 shrinking. -/

set_option autoImplicit false

namespace Tests.CoreV3SynthesisShrink

open Solcore.Core
open Solcore.Core.Wire
open Solcore.Synthesis.CoreV3

private def word (value : Nat) : V3.Expr :=
  .word (Word.ofNatModulo value)

private def program (body : V3.Expr) : V3.Program := {
  resultType := .word
  dataDefinitions := []
  body
}

private def admitProgram (body : V3.Expr) : Option CheckedWordProgram :=
  CheckedWordProgram.ofProgram? (program body)

private def bodyKey (body : V3.Expr) : String :=
  (V3.encodeExpr body).compress

private def candidateKeys (candidates : List ShrinkCandidate) : List String :=
  candidates.map fun candidate => bodyKey candidate.body

private def allUnique : List String → Bool
  | [] => true
  | key :: rest => !rest.contains key && allUnique rest

private def hasBody
    (expected : V3.Expr)
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

private def compoundBody : V3.Expr :=
  .letE (word 7)
    (.ifE
      (.binary .wordEq (.var 0) (word 3))
      (.binary .wordAdd (.var 0) (word 9))
      (.unary .wordNot (word 2)))

private def isTopLet : V3.Expr → Bool
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

private def captureBody : V3.Expr :=
  .letE (word 1) (.var 0)

private def captureCandidateIsRejected : Bool :=
  match admitProgram captureBody with
  | none => false
  | some source =>
      let candidates := shrink source
      !(hasBody (.var 0) candidates) &&
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
    determinismOrderAndDedup &&
    literalWeightIsExact

private theorem allChecks_exact : allChecks = true := by
  native_decide

def testCoreV3SynthesisShrink : IO Unit := do
  unless allChecks do
    throw (IO.userError "Core v3 checked shrinker changed")

end Tests.CoreV3SynthesisShrink
