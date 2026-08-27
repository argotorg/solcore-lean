import Solcore.Core.Check
import Solcore.Core.Machine
import Solcore.Core.Wire
import Solcore.Core.Wire.V2

/-! Executable regressions for non-recursive Core functions and lexical closures. -/

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

private def identity : Expr :=
  .lambda .unit .unit (.var 0)

private def testIdentityAndExactFuel : IO Unit := do
  let identityProgram : Program := {
    resultType := .function .unit .unit
    body := identity
  }
  let identityClosure : Value :=
    .closure .unit .unit (.var 0) []
  assertTrue identityProgram.check
    "a typed lambda must infer its declared function type"
  assertTrue (identityProgram.run 0 == .outOfFuel)
    "zero transitions must be insufficient to create a closure"
  assertTrue (identityProgram.run 1 == .done identityClosure)
    "a lambda must close over its environment in exactly one transition"

  let applicationProgram : Program := {
    resultType := .unit
    body := .apply identity .unit
  }
  assertTrue applicationProgram.check
    "identity applied to unit must check"
  assertTrue (applicationProgram.run 5 == .outOfFuel)
    "five transitions must be insufficient for identity application"
  assertTrue (applicationProgram.run 6 == .done .unit)
    "identity application must finish exactly at six transitions"

private def testLexicalCaptureAndShadowing : IO Unit := do
  let captureProgram : Program := {
    resultType := .bool
    body :=
      .letE (.bool true)
        (.apply
          (.lambda .unit .bool (.var 1))
          .unit)
  }
  assertTrue captureProgram.check
    "a closure body must type-check against its captured lexical context"
  assertTrue (captureProgram.run 8 == .outOfFuel)
    "eight transitions must be insufficient for the lexical-capture witness"
  assertTrue (captureProgram.run 9 == .done (.bool true))
    "a closure must read its captured outer binding"

  let shadowProgram : Program := {
    resultType := .bool
    body :=
      .letE (.bool false)
        (.apply
          (.lambda .bool .bool (.var 0))
          (.bool true))
  }
  assertTrue shadowProgram.check
    "a parameter may shadow a captured binding of the same type"
  assertTrue (shadowProgram.run 9 == .done (.bool true))
    "de Bruijn index zero in a function body must denote the parameter"

private def testNestedFunctionsAndClosures : IO Unit := do
  let nestedResultType : Ty :=
    .function .unit (.function .bool .unit)
  let nestedLambda : Expr :=
    .lambda .unit (.function .bool .unit)
      (.lambda .bool .unit .unit)
  let nestedClosure : Value :=
    .closure .unit (.function .bool .unit)
      (.lambda .bool .unit .unit)
      []
  let nestedProgram : Program := {
    resultType := nestedResultType
    body := nestedLambda
  }
  assertTrue nestedProgram.check
    "function types and lambda results must nest"
  assertTrue (nestedProgram.run 1 == .done nestedClosure)
    "the outer lambda must produce a closure containing the inner lambda"

  let invokeTwice : Program := {
    resultType := .unit
    body := .apply (.apply nestedLambda .unit) (.bool true)
  }
  assertTrue invokeTwice.check
    "a returned closure must remain applicable"
  assertTrue (invokeTwice.run 10 == .outOfFuel)
    "ten transitions must be insufficient for the nested application"
  assertTrue (invokeTwice.run 11 == .done .unit)
    "nested applications must finish exactly at eleven transitions"

private def testFunctionWeakening : IO Unit := do
  let parameterReference : Expr :=
    .lambda .unit .unit (.var 0)
  assertTrue (parameterReference.weakenAt 0 == parameterReference)
    "weakening outside a lambda must not shift its bound parameter"

  let capturedReference : Expr :=
    .lambda .unit .bool (.var 1)
  let weakenedCapture : Expr :=
    .lambda .unit .bool (.var 2)
  assertTrue (capturedReference.weakenAt 0 == weakenedCapture)
    "weakening outside a lambda must shift a captured outer binding"

  let application : Expr :=
    .apply (.var 0) (.var 1)
  assertTrue
    (application.weakenAt 1 == .apply (.var 0) (.var 2))
    "weakening must traverse both the callee and argument"

private def testDetailedFunctionErrors : IO Unit := do
  let nonFunction : Program := {
    resultType := .unit
    body := .apply (.bool true) .unit
  }
  assertTrue (!nonFunction.check)
    "application must reject a statically non-function callee"
  assertCheckError
    "non-function callee"
    nonFunction
    [.applyFunction]
    (.expectedFunction .bool)

  let wrongArgument : Program := {
    resultType := .unit
    body := .apply identity (.bool true)
  }
  assertCheckError
    "wrong function argument"
    wrongArgument
    [.applyArgument]
    (.functionArgumentTypeMismatch .unit .bool)

  let invalidArgumentBody : Program := {
    resultType := .unit
    body := .letE .unit (.apply identity (.var 22))
  }
  assertCheckError
    "invalid expression inside function argument"
    invalidArgumentBody
    [.letBody, .applyArgument]
    (.unboundVariable 22 1)

  let wrongLambdaResult : Program := {
    resultType := .function .unit .bool
    body := .lambda .unit .bool .unit
  }
  assertCheckError
    "wrong lambda result"
    wrongLambdaResult
    [.lambdaBody]
    (.lambdaResultTypeMismatch .bool .unit)

  let invalidLambdaBody : Program := {
    resultType := .function .unit .unit
    body := .lambda .unit .unit (.var 1)
  }
  assertCheckError
    "invalid lambda body"
    invalidLambdaBody
    [.lambdaBody]
    (.unboundVariable 1 1)

  let invalidCalleeAndArgument : Program := {
    resultType := .unit
    body := .apply (.var 11) (.var 22)
  }
  assertCheckError
    "invalid callee and argument"
    invalidCalleeAndArgument
    [.applyFunction]
    (.unboundVariable 11 0)

private def testApplicationFaultOrder : IO Unit := do
  let invalidCalleeAndArgument : Program := {
    resultType := .unit
    body := .apply (.var 11) (.var 22)
  }
  assertTrue
    (invalidCalleeAndArgument.run 1 == .fault (.unboundVariable 11))
    "application must evaluate the callee before the argument"

  let invalidArgumentAndBody : Program := {
    resultType := .unit
    body :=
      .apply
        (.lambda .unit .unit (.var 99))
        (.var 22)
  }
  assertTrue
    (invalidArgumentAndBody.run 3 == .fault (.unboundVariable 22))
    "application must evaluate the argument before entering the closure body"

  let invalidBody : Program := {
    resultType := .unit
    body := .apply (.lambda .unit .unit (.var 99)) .unit
  }
  assertTrue
    (invalidBody.run 5 == .fault (.unboundVariable 99))
    "the closure body must run only after a successful argument evaluation"

  let nonFunction : Program := {
    resultType := .unit
    body := .apply (.bool true) .unit
  }
  assertTrue
    (nonFunction.run 2 == .fault (.expectedFunction (.bool true)))
    "the unchecked machine must fault before evaluating a non-function argument"

private def testFrozenFunctionWireBoundary : IO Unit := do
  let functionType : Ty := .function .unit (.function .bool .unit)
  let lambdaExpr : Expr := .lambda .unit .unit (.var 0)
  let applyExpr : Expr := .apply lambdaExpr .unit
  let closureValue : Value := .closure .unit .unit (.var 0) []
  let nestedClosure : Value := .pair .unit closureValue

  assertTrue (Solcore.Core.Wire.V1.Ty.ofCore? functionType).isNone
    "Semantic Core v1 must reject function types"
  assertTrue (Solcore.Core.Wire.V2.Ty.ofCore? functionType).isNone
    "Semantic Core v2 must reject function types"
  assertTrue (Solcore.Core.Wire.V1.Value.ofCore? closureValue).isNone
    "Semantic Core v1 must reject closure values"
  assertTrue (Solcore.Core.Wire.V2.Value.ofCore? closureValue).isNone
    "Semantic Core v2 must reject closure values"
  assertTrue (Solcore.Core.Wire.V1.Value.ofCore? nestedClosure).isNone
    "Semantic Core v1 must reject closures nested in internal values"
  assertTrue (Solcore.Core.Wire.V2.Value.ofCore? nestedClosure).isNone
    "Semantic Core v2 must reject closures nested in internal values"

  for expression in [lambdaExpr, applyExpr] do
    assertTrue (Solcore.Core.Wire.V1.Expr.ofCore? expression).isNone
      s!"Semantic Core v1 encoded an internal function expression: {reprStr expression}"
    assertTrue (Solcore.Core.Wire.V2.Expr.ofCore? expression).isNone
      s!"Semantic Core v2 encoded an internal function expression: {reprStr expression}"

  let nestedInV1Shape : Expr := .letE .unit lambdaExpr
  let nestedInV2Shape : Expr := .unary .boolNot applyExpr
  assertTrue (Solcore.Core.Wire.V1.Expr.ofCore? nestedInV1Shape).isNone
    "Semantic Core v1 must reject a lambda nested under an old expression"
  assertTrue (Solcore.Core.Wire.V2.Expr.ofCore? nestedInV2Shape).isNone
    "Semantic Core v2 must reject an application nested under an old expression"

  let functionResultProgram : Program := {
    resultType := .function .unit .unit
    body := lambdaExpr
  }
  assertTrue (Solcore.Core.Wire.V1.Program.ofCore? functionResultProgram).isNone
    "Semantic Core v1 must reject programs with function result types"
  assertTrue (Solcore.Core.Wire.V2.Program.ofCore? functionResultProgram).isNone
    "Semantic Core v2 must reject programs with function result types"

  let oldResultProgram : Program := {
    resultType := .unit
    body := applyExpr
  }
  assertTrue (Solcore.Core.Wire.V1.Program.ofCore? oldResultProgram).isNone
    "Semantic Core v1 must reject function expressions under old result types"
  assertTrue (Solcore.Core.Wire.V2.Program.ofCore? oldResultProgram).isNone
    "Semantic Core v2 must reject function expressions under old result types"

/-- Cover function typing, lexical closures, evaluation order, diagnostics,
machine faults, exact fuel, and frozen-wire isolation. -/
def testCoreFunctions : IO Unit := do
  testIdentityAndExactFuel
  testLexicalCaptureAndShadowing
  testNestedFunctionsAndClosures
  testFunctionWeakening
  testDetailedFunctionErrors
  testApplicationFaultOrder
  testFrozenFunctionWireBoundary

end Tests
