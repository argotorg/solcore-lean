import Solcore.Core.Check
import Solcore.Core.Machine

/-! Executable regressions for internal binary sums and exhaustive case analysis. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def assertCheckError
    (name : String)
    (program : Program)
    (path : CheckPath)
    (data : CheckErrorData) : IO Unit := do
  match program.checkDetailed with
  | .ok type =>
      throw (IO.userError s!"{name} unexpectedly checked as {reprStr type}")
  | .error error =>
      assertTrue (error.code == data.code)
        s!"{name} returned {error.codeName}, expected {data.code.name}"
      assertTrue (error.path == path)
        s!"{name} returned path {reprStr error.path}, expected {reprStr path}"
      assertTrue (error.data == data)
        s!"{name} returned data {reprStr error.data}, expected {reprStr data}"

private def testInjectionsAndExactFuel : IO Unit := do
  let leftProgram : Program := {
    resultType := .sum .unit .bool
    body := .inLeft .bool .unit
  }
  assertTrue leftProgram.check
    "a left injection must infer the sum of its payload and annotated right type"
  assertTrue (leftProgram.run 2 == .outOfFuel)
    "two transitions must be insufficient for a left injection"
  assertTrue (leftProgram.run 3 == .done (.inLeft .bool .unit))
    "a left injection must finish exactly at three transitions"

  let rightProgram : Program := {
    resultType := .sum .unit .bool
    body := .inRight .unit (.bool true)
  }
  assertTrue rightProgram.check
    "a right injection must infer the sum of its annotated left type and payload"
  assertTrue (rightProgram.run 2 == .outOfFuel)
    "two transitions must be insufficient for a right injection"
  assertTrue (rightProgram.run 3 == .done (.inRight .unit (.bool true)))
    "a right injection must finish exactly at three transitions"

  let nestedProgram : Program := {
    resultType := .sum .unit (.sum .bool .word)
    body := .inRight .unit (.inLeft .word (.bool false))
  }
  assertTrue nestedProgram.check
    "sum types and injected values must nest recursively"
  assertTrue (nestedProgram.run 4 == .outOfFuel)
    "four transitions must be insufficient for a nested injection"
  assertTrue
    (nestedProgram.run 5 ==
      .done (.inRight .unit (.inLeft .word (.bool false))))
    "a nested injection must finish exactly at five transitions"

private def testCaseSelectionAndBinders : IO Unit := do
  let selectLeft : Program := {
    resultType := .unit
    body := .caseE (.inLeft .bool .unit) (.var 0) .unit
  }
  assertTrue selectLeft.check
    "a left case branch must receive the left payload at index zero"
  assertTrue (selectLeft.run 5 == .outOfFuel)
    "five transitions must be insufficient for a literal left case"
  assertTrue (selectLeft.run 6 == .done .unit)
    "a literal left case must finish exactly at six transitions"

  let selectRight : Program := {
    resultType := .bool
    body := .caseE (.inRight .unit (.bool true)) (.bool false) (.var 0)
  }
  assertTrue selectRight.check
    "a right case branch must receive the right payload at index zero"
  assertTrue (selectRight.run 5 == .outOfFuel)
    "five transitions must be insufficient for a literal right case"
  assertTrue (selectRight.run 6 == .done (.bool true))
    "a literal right case must finish exactly at six transitions"

  let payloadAndOuterBinding : Program := {
    resultType := .product .word .bool
    body :=
      .letE (.bool true)
        (.caseE
          (.inLeft .unit (.word Word.zero))
          (.pair (.var 0) (.var 1))
          (.pair (.word Word.zero) (.var 1)))
  }
  assertTrue payloadAndOuterBinding.check
    "case branches must type-check under payload followed by outer bindings"
  assertTrue
    (payloadAndOuterBinding.run 13 ==
      .done (.pair (.word Word.zero) (.bool true)))
    "index zero must denote the payload and index one the outer binding"

private def testCaseEvaluationOrder : IO Unit := do
  let invalidScrutineeAndBranches : Program := {
    resultType := .unit
    body := .caseE (.var 11) (.var 22) (.var 33)
  }
  assertTrue
    (invalidScrutineeAndBranches.run 1 == .fault (.unboundVariable 11))
    "case analysis must evaluate its scrutinee before either branch"

  let invalidPayloadAndBranch : Program := {
    resultType := .unit
    body := .caseE (.inLeft .unit (.var 12)) (.var 22) (.var 33)
  }
  assertTrue
    (invalidPayloadAndBranch.run 2 == .fault (.unboundVariable 12))
    "an injection payload must finish before case branch selection"

  let leftOnly : Program := {
    resultType := .unit
    body := .caseE (.inLeft .unit .unit) .unit (.var 99)
  }
  assertTrue (leftOnly.run 6 == .done .unit)
    "a left injection must not evaluate the right branch"

  let rightOnly : Program := {
    resultType := .unit
    body := .caseE (.inRight .unit .unit) (.var 98) .unit
  }
  assertTrue (rightOnly.run 6 == .done .unit)
    "a right injection must not evaluate the left branch"

  let selectedBranchFault : Program := {
    resultType := .unit
    body := .caseE (.inLeft .unit .unit) (.var 97) .unit
  }
  assertTrue
    (selectedBranchFault.run 5 == .fault (.unboundVariable 97))
    "the selected branch must run after scrutinee and payload completion"

  let nonSum : Program := {
    resultType := .unit
    body := .caseE (.bool true) .unit .unit
  }
  assertTrue
    (nonSum.run 2 == .fault (.expectedSum (.bool true)))
    "the unchecked machine must fault when a case scrutinee is not a sum"

private def testDetailedSumErrors : IO Unit := do
  let invalidLeftPayload : Program := {
    resultType := .sum .unit .unit
    body := .inLeft .unit (.var 11)
  }
  assertCheckError
    "invalid left payload"
    invalidLeftPayload
    [.inLeftPayload]
    (.unboundVariable 11 0)

  let invalidRightPayload : Program := {
    resultType := .sum .unit .unit
    body := .inRight .unit (.var 12)
  }
  assertCheckError
    "invalid right payload"
    invalidRightPayload
    [.inRightPayload]
    (.unboundVariable 12 0)

  let invalidScrutinee : Program := {
    resultType := .unit
    body := .caseE (.var 13) .unit .unit
  }
  assertCheckError
    "invalid case scrutinee"
    invalidScrutinee
    [.caseScrutinee]
    (.unboundVariable 13 0)

  let nonSum : Program := {
    resultType := .unit
    body := .caseE (.bool true) .unit .unit
  }
  assertCheckError
    "non-sum case scrutinee"
    nonSum
    [.caseScrutinee]
    (.expectedSum .bool)

  let invalidLeftBranch : Program := {
    resultType := .unit
    body := .caseE (.inLeft .unit .unit) (.var 2) .unit
  }
  assertCheckError
    "invalid left case branch"
    invalidLeftBranch
    [.caseLeftBranch]
    (.unboundVariable 2 1)

  let invalidRightBranch : Program := {
    resultType := .unit
    body := .caseE (.inLeft .unit .unit) .unit (.var 3)
  }
  assertCheckError
    "invalid right case branch"
    invalidRightBranch
    [.caseRightBranch]
    (.unboundVariable 3 1)

  let invalidBothBranches : Program := {
    resultType := .unit
    body := .caseE (.inLeft .unit .unit) (.var 21) (.var 22)
  }
  assertCheckError
    "invalid both case branches"
    invalidBothBranches
    [.caseLeftBranch]
    (.unboundVariable 21 1)

  let mismatchedBranches : Program := {
    resultType := .unit
    body := .caseE (.inLeft .unit .unit) .unit (.bool false)
  }
  assertCheckError
    "mismatched case branches"
    mismatchedBranches
    [.caseRightBranch]
    (.caseBranchTypeMismatch .unit .bool)

  let scrutineeHasPriority : Program := {
    resultType := .unit
    body := .caseE (.var 31) (.var 32) (.var 33)
  }
  assertCheckError
    "case scrutinee priority"
    scrutineeHasPriority
    [.caseScrutinee]
    (.unboundVariable 31 0)

  let prefixedBranchError : Program := {
    resultType := .product .unit .unit
    body :=
      .pair
        (.caseE
          (.inLeft .unit .unit)
          .unit
          (.first (.bool true)))
        .unit
  }
  assertCheckError
    "prefixed right branch error"
    prefixedBranchError
    [.pairLeft, .caseRightBranch, .firstOperand]
    (.expectedProduct .bool)

private def testSumInteractions : IO Unit := do
  let productPayload : Program := {
    resultType := .bool
    body :=
      .caseE
        (.inLeft .unit (.pair (.bool true) (.word Word.zero)))
        (.first (.var 0))
        (.bool false)
  }
  assertTrue productPayload.check
    "a sum payload may itself be a product"
  assertTrue (productPayload.run 12 == .done (.bool true))
    "case analysis must expose a product payload to the selected branch"

  let closurePayload : Program := {
    resultType := .unit
    body :=
      .caseE
        (.inLeft .unit (.lambda .unit .unit (.var 0)))
        (.apply (.var 0) .unit)
        .unit
  }
  assertTrue closurePayload.check
    "a sum payload may be a function closure"
  assertTrue (closurePayload.run 11 == .done .unit)
    "a closure extracted from a sum must remain applicable"

  let capturedSum : Program := {
    resultType := .bool
    body :=
      .letE
        (.inLeft .unit (.bool true))
        (.apply
          (.lambda .unit .bool
            (.caseE (.var 1) (.var 0) (.bool false)))
          .unit)
  }
  assertTrue capturedSum.check
    "a closure may capture a sum and eliminate it in its body"
  assertTrue (capturedSum.run 14 == .done (.bool true))
    "captured sums must retain their payload through closure application"

private def testCaseWeakening : IO Unit := do
  let expression : Expr :=
    .caseE
      (.var 0)
      (.pair (.var 0) (.var 1))
      (.pair (.var 0) (.var 1))
  let expected : Expr :=
    .caseE
      (.var 1)
      (.pair (.var 0) (.var 2))
      (.pair (.var 0) (.var 2))
  assertTrue (expression.weakenAt 0 == expected)
    "weakening must cross the scrutinee but preserve each branch payload binder"

/-- Cover injections, case binders, execution order, diagnostics, weakening,
interactions, exact fuel, and faults. -/
def testCoreSums : IO Unit := do
  testInjectionsAndExactFuel
  testCaseSelectionAndBinders
  testCaseEvaluationOrder
  testDetailedSumErrors
  testSumInteractions
  testCaseWeakening

end Tests
