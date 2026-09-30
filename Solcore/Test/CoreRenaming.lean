import Solcore.Core.Renaming

/-! Focused static regressions for Core renaming and context insertion. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def one : Word :=
  Word.ofNatModulo 1

private def dataType : DataTypeId :=
  ⟨0⟩

private def freeVariableLet : Expr :=
  .letE (.word one) (.binary .wordAdd (.var 0) (.var 1))

private theorem freeVariableLetTyping :
    HasType [.word] freeVariableLet .word := by
  exact .letE .word
    (.binary
      (.var (by simp [BinaryOp.leftType]))
      (.var (by simp [BinaryOp.rightType, BinaryOp.leftType])))

private theorem branchesTyping :
    BranchesHaveType [.word] .word [.bool, .unit] [.var 1, .var 1] := by
  exact .cons (.var (by simp)) (.cons (.var (by simp)) .nil)

example :
    HasType (Context.insertAt [.word] 0 .bool)
      (freeVariableLet.rename (Renaming.insertion 0)) .word :=
  freeVariableLetTyping.rename
    (Renaming.insertion_respects_insertAt [.word] 0 .bool)

example :
    BranchesHaveType (Context.insertAt [.word] 0 .unit) .word [.bool, .unit]
      (Expr.renameList [.var 1, .var 1] (Renaming.insertion 0).lift) :=
  branchesTyping.rename
    (Renaming.insertion_respects_insertAt [.word] 0 .unit)

example :
    infer? (Context.insertAt [.word] 0 .bool)
      (freeVariableLet.rename (Renaming.insertion 0)) = some .word :=
  infer_rename (infer_complete freeVariableLetTyping)
    (Renaming.insertion_respects_insertAt [.word] 0 .bool)

private def testBinderLifting : IO Unit := do
  let lambda : Expr :=
    .lambda .word (.product .word .word) (.pair (.var 0) (.var 1))
  let expectedLambda : Expr :=
    .lambda .word (.product .word .word) (.pair (.var 0) (.var 2))
  assertTrue (lambda.weakenAt 0 == expectedLambda)
    "lambda renaming must preserve its binder and shift the free variable"

  let letExpression : Expr :=
    .letE (.var 0) (.pair (.var 0) (.var 1))
  let expectedLet : Expr :=
    .letE (.var 1) (.pair (.var 0) (.var 2))
  assertTrue (letExpression.weakenAt 0 == expectedLet)
    "let renaming must lift only beneath its body binder"

  let caseExpression : Expr :=
    .caseE (.var 0)
      (.pair (.var 0) (.var 1))
      (.pair (.var 1) (.var 0))
  let expectedCase : Expr :=
    .caseE (.var 1)
      (.pair (.var 0) (.var 2))
      (.pair (.var 2) (.var 0))
  assertTrue (caseExpression.weakenAt 0 == expectedCase)
    "case renaming must lift independently beneath both branch binders"

  let matchExpression : Expr :=
    .matchData dataType .word (.var 0) [
      .pair (.var 0) (.var 1),
      .pair (.var 1) (.var 0)
    ]
  let expectedMatch : Expr :=
    .matchData dataType .word (.var 1) [
      .pair (.var 0) (.var 2),
      .pair (.var 2) (.var 0)
    ]
  assertTrue (matchExpression.weakenAt 0 == expectedMatch)
    "matchData renaming must lift beneath every payload branch binder"

private def testIdentityAndComposition : IO Unit := do
  let expression : Expr :=
    .lambda .word .word
      (.letE (.var 1)
        (.matchData dataType .word (.var 2) [.var 0, .var 3]))
  let inner : Renaming := fun index => index + 2
  let outer : Renaming := fun index => index * 2
  assertTrue (expression.rename Renaming.id == expression)
    "identity renaming must preserve a nested expression"
  assertTrue
    ((expression.rename inner).rename outer ==
      expression.rename (outer.comp inner))
    "composition must apply the inner renaming before the outer renaming"

private def testInsertionBoundaries : IO Unit := do
  let context : Context := [.bool, .word]
  let insertedWithin := Context.insertAt context 1 .unit
  assertTrue (insertedWithin == [.bool, .unit, .word])
    "context insertion must place a type at an in-range cutoff"
  assertTrue
    ((Expr.var 0).rename (Renaming.insertion 1) == .var 0 &&
      (Expr.var 1).rename (Renaming.insertion 1) == .var 2)
    "insertion must preserve lower variables and shift variables at the cutoff"
  assertTrue
    (infer? insertedWithin (.var 0) == some .bool &&
      infer? insertedWithin (.var 1) == some .unit &&
      infer? insertedWithin (.var 2) == some .word)
    "context insertion and variable renaming must agree on lookup types"

  let insertedBeyond := Context.insertAt context 5 .unit
  let scopedExpression : Expr := .pair (.var 0) (.var 1)
  assertTrue (insertedBeyond == [.bool, .word, .unit])
    "an insertion beyond the context must saturate at its end"
  assertTrue
    (scopedExpression.rename (Renaming.insertion 5) == scopedExpression)
    "an insertion beyond a context must preserve its well-scoped variables"
  assertTrue
    ((Expr.var 7).rename (Renaming.insertion 5) == .var 8)
    "out-of-range syntax still follows the renaming even when it is untyped"

private def testFreeVariableNoncapture : IO Unit := do
  let expected : Expr :=
    .letE (.word one) (.binary .wordAdd (.var 0) (.var 2))
  let renamed := freeVariableLet.rename (Renaming.insertion 0)
  assertTrue (renamed == expected)
    "head insertion must not capture a free variable beneath a let binder"
  assertTrue
    (infer? (Context.insertAt [.word] 0 .bool) renamed == some .word)
    "the noncapturing renamed expression must retain its inferred type"

/-- Cover static binder lifting, renaming laws, insertion, noncapture, and the
typing-preservation theorem surface. -/
def testCoreRenaming : IO Unit := do
  testBinderLifting
  testIdentityAndComposition
  testInsertionBoundaries
  testFreeVariableNoncapture

end Tests
