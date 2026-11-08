import Solcore.Core.Internal.ConventionLaws
import Solcore.Core.Check
import Solcore.Core.Machine
import Solcore.Core.Safety
import Solcore.Core.Internal.Renaming
import Solcore.Core.Fuel
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.Heaps

/-!
# Core data and cell tests

Products, sums, named data, tagged functions, local cells in their general, optional and recursive
forms, Core mappings and function definitions.
-/

section
-- leanmerge: from Solcore.Test.CoreCallableContract
set_option autoImplicit false

namespace Tests.CoreCallableContract
open Solcore Core
open CallableContract

private def w (value : Nat) : Word := (Word.ofNat? value).getD Word.zero

private def function : Expr :=
  TaggedFunction.identified (w 7)
    (.lambda .unit (LanguageResult.resultType .word)
      (.letE (.newCell (.sum .unit .unit) (.inRight .unit .unit)) (LanguageResult.success (.word (w 9)))))

private def callee : Expr :=
  .letE (.storeCell (.var 0) (.word (w 1))) (LanguageResult.success (wrap (w 11) function))

private def arguments : Expr :=
  .letE (.storeCell (.var 0) (.word (w 2))) (LanguageResult.success .unit)

private def gates (before after : Option Word) : List Gate :=
  [⟨w 5, some (w 90), some (w 91)⟩, ⟨w 11, before, after⟩]

example (before after : Option Word) :
    HasType [.cell .word] (call (gates before after) (w 99) .word callee arguments)
      (LanguageResult.resultType .word) := by
  apply call_hasType _ _ .word
  · exact .letE (.storeCell (.var rfl) .word)
      (.inRight .word (.pair
        (.pair (.inRight .unit .word)
          (.lambda .unit (.sum .word .word)
            (.letE (.newCell (.inRight .unit .unit)) (.inRight .word .word)))) .word))
  · exact .letE (.storeCell (.var rfl) .word) (.inRight .word .unit)

example : decision (gates (some (w 21)) none) .beforeArguments (w 99) (w 11) = some (w 21) := by
  decide

example : decision (gates none (some (w 22))) .beforeApplication (w 99) (w 11) = some (w 22) := by
  decide

example : decision (gates none none) .beforeArguments (w 99) (w 12) = some (w 99) := by
  decide

example {environment : Environment} {store : Store} {left right : Value} :
    Evaluates (.pair (.pair (.inRight .unit (.word (w 7))) right) (.word (w 12)) ::
      .pair (.pair (.inRight .unit (.word (w 7))) left) (.word (w 11)) :: environment)
      store equalBody (.bool true) store :=
  by simpa using (equalBody_identified (leftIdentity := w 7) (rightIdentity := w 7))

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def check (before after : Option Word) (value : Value) (store : Store) : IO Unit := do
  let expression := call (gates before after) (w 99) .word callee arguments
  assertTrue (infer? [.cell .word] expression == some (LanguageResult.resultType .word))
    "callable contract code failed checker"
  let state := State.initial expression [.cellRef .word 0] [.word (w 0)]
  let verify := fun result => do
    match result with
    | .done actual actualStore =>
        assertTrue (actual == value && actualStore == store)
          s!"callable guard order/store changed: {reprStr result}"
    | other => throw (IO.userError s!"callable guard did not complete: {reprStr other}")
  verify (runStateful 1000 state)
  match runStateful 3 state with
  | .outOfFuel checkpoint => verify (runStateful 1000 checkpoint)
  | other => throw (IO.userError s!"callable guard did not retain checkpoint: {reprStr other}")

def run : IO Unit := do
  check (some (w 21)) none (.inLeft .word (.word (w 21))) [.word (w 1)]
  check none (some (w 22)) (.inLeft .word (.word (w 22))) [.word (w 2)]
  check none none (.inRight .word (.word (w 9))) [.word (w 2), .inRight .unit .unit]
  let unknown := call [] (w 99) .word callee arguments
  assertTrue (runStateful 1000 (State.initial unknown [.cellRef .word 0] [.word (w 0)]) ==
    .done (.inLeft .word (.word (w 99))) [.word (w 1)]) "unknown descriptor bypassed guard"
  let tagged := TaggedFunction.identified (w 7) (.lambda .unit (.sum .word .unit) (.inRight .word .unit))
  let namedEqual := equal (LanguageResult.success (wrap (w 11) tagged))
    (LanguageResult.success (wrap (w 12) tagged))
  assertTrue (runStateful 1000 (State.initial namedEqual [] []) ==
    .done (.inRight .word (.bool true)) []) "descriptor changed named identity"
  let anonymous := LanguageResult.success (wrap (w 11)
    (TaggedFunction.anonymous (.lambda .unit (.sum .word .unit) (.inRight .word .unit))))
  assertTrue (runStateful 1000 (State.initial (equal anonymous anonymous) [] []) ==
    .done (.inRight .word (.bool false)) []) "anonymous wrapper compared equal"
  IO.println "ordinary callable contract dispatch/order/equality GREEN"

end Tests.CoreCallableContract
end

section
-- leanmerge: from Solcore.Test.CoreCells
/-! Executable regressions for general local cells and explicit stores. -/

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

private def testAllocationAndExactFuel : IO Unit := do
  let program : Program := {
    resultType := .cell .bool
    body := .newCell .bool (.bool true)
  }
  assertTrue program.check
    "a boolean initializer must construct a boolean cell"
  assertTrue (program.run 2 == .outOfFuel)
    "two transitions must be insufficient to allocate a cell"
  assertTrue
    (program.runStateful 3 ==
      .done (.cellRef .bool 0) [.bool true])
    "the first allocation must finish in three transitions at location zero"
  assertTrue (program.run 3 == .done (.cellRef .bool 0))
    "the compatibility runner must erase only the final store"

  let nestedInitializer : Program := {
    resultType := .cell .bool
    body :=
      .newCell .bool
        (.letE (.newCell .unit .unit) (.bool true))
  }
  assertTrue nestedInitializer.check
    "an initializer may allocate a cell that is not returned"
  match nestedInitializer.runStateful 20 with
  | .done (.cellRef .bool location) store =>
      assertTrue (location == 1)
        "outer allocation must occur after all initializer effects"
      assertTrue (store == [.unit, .bool true])
        "initializer allocation must precede the outer cell in the store"
  | result =>
      throw (IO.userError
        s!"nested initializer returned an unexpected result: {reprStr result}")

private def testLoadStoreAndAliases : IO Unit := do
  let loadProgram : Program := {
    resultType := .bool
    body := .loadCell (.newCell .bool (.bool true))
  }
  assertTrue loadProgram.check
    "loading a freshly initialized boolean cell must check"
  assertTrue (loadProgram.run 4 == .outOfFuel)
    "four transitions must be insufficient for allocation followed by load"
  assertTrue
    (loadProgram.runStateful 5 == .done (.bool true) [.bool true])
    "load must read the store produced by its reference expression"

  let updateProgram : Program := {
    resultType := .bool
    body :=
      .letE (.newCell .bool (.bool false))
        (.letE
          (.storeCell (.var 0) (.bool true))
          (.loadCell (.var 1)))
  }
  assertTrue updateProgram.check
    "a write followed by a read through the same handle must check"
  assertTrue (updateProgram.run 14 == .outOfFuel)
    "fourteen transitions must be insufficient for the update witness"
  assertTrue
    (updateProgram.runStateful 15 == .done (.bool true) [.bool true])
    "storeCell must replace the selected entry and return unit to sequencing"

  let twoAllocations : Program := {
    resultType := .product (.cell .bool) (.cell .bool)
    body :=
      .letE (.newCell .bool (.bool false))
        (.letE (.newCell .bool (.bool true))
          (.pair (.var 1) (.var 0)))
  }
  match twoAllocations.runStateful 30 with
  | .done (.pair (.cellRef .bool left) (.cellRef .bool right)) store =>
      assertTrue (left == 0 && right == 1)
        "sequential allocations must receive distinct increasing locations"
      assertTrue (store == [.bool false, .bool true])
        "sequential allocations must preserve append order"
  | result =>
      throw (IO.userError
        s!"two-allocation witness returned an unexpected result: {reprStr result}")

private def testCompositePayloads : IO Unit := do
  let productProgram : Program := {
    resultType := .product .unit .bool
    body :=
      .letE
        (.newCell (.product .unit .bool) (.pair .unit (.bool false)))
        (.letE
          (.storeCell (.var 0) (.pair .unit (.bool true)))
          (.loadCell (.var 1)))
  }
  assertTrue productProgram.check
    "products of admissible payloads must remain admissible cell payloads"
  assertTrue
    (productProgram.runStateful 40 ==
      .done (.pair .unit (.bool true)) [.pair .unit (.bool true)])
    "a product cell must support allocation, replacement, and loading"

  let sumProgram : Program := {
    resultType := .sum .unit .bool
    body :=
      .letE
        (.newCell (.sum .unit .bool) (.inLeft .bool .unit))
        (.letE
          (.storeCell (.var 0) (.inRight .unit (.bool true)))
          (.loadCell (.var 1)))
  }
  assertTrue sumProgram.check
    "sums of admissible payloads must remain admissible cell payloads"
  assertTrue
    (sumProgram.runStateful 40 ==
      .done
        (.inRight .unit (.bool true))
        [.inRight .unit (.bool true)])
    "a sum cell must support allocation, constructor-changing replacement, and loading"

private theorem forgedCellAnnotationRejected :
    ¬ RuntimeValueHasType
      ([.unit] : StoreTyping)
      (.cellRef .bool 0)
      (.cell .bool) := by
  intro typing
  cases typing with
  | cellRef found => simp at found

private def testClosureSharedCell : IO Unit := do
  let program : Program := {
    resultType := .bool
    body :=
      .letE (.newCell .bool (.bool false))
        (.letE
          (.lambda .unit .unit
            (.storeCell (.var 1) (.bool true)))
          (.letE
            (.lambda .unit .bool
              (.loadCell (.var 2)))
            (.letE
              (.apply (.var 1) .unit)
              (.apply (.var 1) .unit))))
  }
  assertTrue program.check
    "writer and reader closures may capture the same first-order cell"
  match program.runStateful 80 with
  | .done (.bool true) store =>
      assertTrue (store == [.bool true])
        "a write through one closure must be visible through another"
  | result =>
      throw (IO.userError
        s!"closure-sharing witness returned an unexpected result: {reprStr result}")

private def testStoreEffectOrder : IO Unit := do
  let program : Program := {
    resultType := .unit
    body :=
      .letE (.newCell .bool (.bool false))
        (.storeCell
          (.letE (.newCell .unit .unit) (.var 1))
          (.letE
            (.newCell .word (.word Word.zero))
            (.bool true)))
  }
  assertTrue program.check
    "cell target and stored-value expressions may both allocate"
  match program.runStateful 40 with
  | .done .unit store =>
      assertTrue (store == [.bool true, .unit, .word Word.zero])
        "target effects must precede RHS effects, and the final write must preserve both"
  | result =>
      throw (IO.userError
        s!"store-order witness returned an unexpected result: {reprStr result}")

private def testFaultOrder : IO Unit := do
  let dangling : State :=
    State.initial
      (.storeCell
        (.var 0)
        (.letE (.newCell .unit .unit) (.bool true)))
      [.cellRef .bool 0]
      []
  match runStateful 10 dangling with
  | .fault (.invalidCellLocation 0) state =>
      assertTrue (state.store == [])
        "a dangling target must fault before RHS allocation can make it valid"
  | result =>
      throw (IO.userError
        s!"dangling write returned an unexpected result: {reprStr result}")

  let nonCell : State :=
    State.initial (.storeCell (.bool true) (.var 88))
  match runStateful 10 nonCell with
  | .fault (.expectedCell (.bool true)) state =>
      assertTrue (state.store == [])
        "a non-cell write target must fault without evaluating the value"
  | result =>
      throw (IO.userError
        s!"non-cell write returned an unexpected result: {reprStr result}")

  let danglingLoad : State :=
    State.initial (.loadCell (.var 0)) [.cellRef .unit 3] []
  match runStateful 10 danglingLoad with
  | .fault (.invalidCellLocation 3) _ => pure ()
  | result =>
      throw (IO.userError
        s!"dangling load returned an unexpected result: {reprStr result}")

private def testGeneralPayloads : IO Unit := do
  let functionPayload : Program := {
    resultType := .bool
    body :=
      .letE
        (.newCell (.function .unit .bool) (.lambda .unit .bool (.bool false)))
        (.letE
          (.storeCell (.var 0) (.lambda .unit .bool (.bool true)))
          (.apply (.loadCell (.var 1)) .unit))
  }
  assertTrue functionPayload.check
    "function cells must admit allocation, replacement, loading, and invocation"
  assertTrue (functionPayload.checkDetailed.toOption == some .bool)
    "detailed checking must admit the same function cell program"
  assertTrue (functionPayload.run 40 == .done (.bool true))
    "loading a replaced function cell must call its current closure"

  let nestedFunctionPayload : Program := {
    resultType := .unit
    body :=
      .apply
        (.second (.loadCell
          (.newCell (.product .unit (.function .unit .unit))
            (.pair .unit (.lambda .unit .unit (.var 0))))))
        .unit
  }
  assertTrue nestedFunctionPayload.check
    "products containing functions must be admitted as cell contents"
  assertTrue (nestedFunctionPayload.run 40 == .done .unit)
    "a function inside a stored product must retain its callable value"

  let nestedCellPayload : Program := {
    resultType := .bool
    body :=
      .letE (.newCell (.cell .bool) (.newCell .bool (.bool false)))
        (.letE
          (.storeCell (.loadCell (.var 0)) (.bool true))
          (.loadCell (.loadCell (.var 1))))
  }
  assertTrue nestedCellPayload.check
    "cells containing references must pass the general checker"
  assertTrue (nestedCellPayload.runStateful 40 ==
      .done (.bool true) [.bool true, .cellRef .bool 0])
    "loading a stored reference must preserve its original cell identity"

private def testDetailedCellErrors : IO Unit := do
  let wrongInitializer : Program := {
    resultType := .cell .bool
    body := .newCell .bool .unit
  }
  assertCheckError
    "wrong cell initializer"
    wrongInitializer
    [.newCellInitializer]
    (.cellInitializerTypeMismatch .bool .unit)

  let nonCellLoad : Program := {
    resultType := .bool
    body := .loadCell (.bool true)
  }
  assertCheckError
    "non-cell load"
    nonCellLoad
    [.loadCellReference]
    (.expectedCell .bool)

  let wrongStoredValue : Program := {
    resultType := .unit
    body :=
      .letE (.newCell .bool (.bool false))
        (.storeCell (.var 0) .unit)
  }
  assertCheckError
    "wrong stored value"
    wrongStoredValue
    [.letBody, .storeCellValue]
    (.cellValueTypeMismatch .bool .unit)

  let wrongFunctionValue : Program := {
    resultType := .unit
    body :=
      .letE (.newCell (.function .unit .unit) (.lambda .unit .unit (.var 0)))
        (.storeCell (.var 0) (.lambda .bool .bool (.var 0)))
  }
  assertCheckError
    "wrong function-valued cell write"
    wrongFunctionValue
    [.letBody, .storeCellValue]
    (.cellValueTypeMismatch (.function .unit .unit) (.function .bool .bool))

private def testCellWeakening : IO Unit := do
  let expression : Expr :=
    .storeCell
      (.loadCell (.var 0))
      (.newCell .unit (.var 1))
  let expected : Expr :=
    .storeCell
      (.loadCell (.var 1))
      (.newCell .unit (.var 2))
  assertTrue (expression.weakenAt 0 == expected)
    "weakening must traverse every cell-operation operand"

/-- Cover general typed cells, explicit-store order and identity, closure
sharing, detailed diagnostics, faults, and exact fuel. -/
def testCoreCells : IO Unit := do
  testAllocationAndExactFuel
  testLoadStoreAndAliases
  testCompositePayloads
  testGeneralPayloads
  testClosureSharedCell
  testStoreEffectOrder
  testFaultOrder
  testDetailedCellErrors
  testCellWeakening

end Tests
end

section
-- leanmerge: from Solcore.Test.CoreDefinitionExtension
set_option autoImplicit false
namespace Tests.CoreDefinitionExtension
open Solcore.Core
private def before : DataEnvironment := [⟨[.word]⟩]
private def after : DataEnvironment := before ++ [⟨[.function .word (.namedData ⟨0⟩)]⟩]
private def tag : ConstructorId := ⟨⟨0⟩, 0⟩
private def code : Expr := .lambda .word (.namedData ⟨0⟩) (.construct tag (.var 0))
private def value : Value := .closure .word (.namedData ⟨0⟩) (.construct tag (.var 0)) []

private theorem extended : before.Extends after := .append _ _
private theorem body : HasType [.word] (.construct tag (.var 0)) (.namedData ⟨0⟩) before :=
  .construct rfl (.var rfl)
private theorem closure : RuntimeValueHasType [] value (.function .word (.namedData ⟨0⟩)) before :=
  .closure .nil body

example : after.lookupConstructorPayloadType? tag = some .word := extended.constructor_lookup rfl
example : HasType [] code (.function .word (.namedData ⟨0⟩)) after :=
  (HasType.lambda .word (.namedData rfl) body).extend_definitions extended
example : RuntimeValueHasType [] value (.function .word (.namedData ⟨0⟩)) after :=
  closure.extend_definitions extended
example : RuntimeEnvironmentHasTypes [] [value] [.function .word (.namedData ⟨0⟩)] after :=
  (RuntimeEnvironmentHasTypes.cons closure .nil).extend_definitions extended
example (world : StoreTyping) (store : Store) (typed : RuntimeStoreHasTypes world store before) :
    RuntimeStoreHasTypes world store after := typed.extend_definitions extended

example : (.namedData ⟨1⟩ : Ty).WellFormed after := .namedData rfl
example : ¬ (.namedData ⟨1⟩ : Ty).WellFormed before := by
  intro typed
  cases typed with
  | namedData found => simp [before] at found

example : after.lookupConstructorPayloadType? ⟨⟨1⟩, 0⟩ = some (.function .word (.namedData ⟨0⟩)) := rfl
example : before.lookupConstructorPayloadType? ⟨⟨1⟩, 0⟩ = none := rfl
end Tests.CoreDefinitionExtension
end

section
-- leanmerge: from Solcore.Test.CoreFunctions
/-! Executable regressions for non-recursive Core functions and lexical closures. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core

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

/-- Cover function typing, lexical closures, evaluation order, diagnostics,
machine faults, and exact fuel. -/
def testCoreFunctions : IO Unit := do
  testIdentityAndExactFuel
  testLexicalCaptureAndShadowing
  testNestedFunctionsAndClosures
  testFunctionWeakening
  testDetailedFunctionErrors
  testApplicationFaultOrder

end Tests
end

section
-- leanmerge: from Solcore.Test.CoreGeneralCells
/-! A checked program installs a closure in the cell that it captures and
then calls it forever. General cells require finite safety, not normalization. -/

set_option autoImplicit false

namespace Tests.CoreGeneralCells

open Solcore.Core

private def functionType : Ty := .function .unit .unit

private def recursiveBody : Expr :=
  .apply (.loadCell (.var 1)) .unit

private def recursiveClosure : Value :=
  .closure .unit .unit recursiveBody [.cellRef functionType 0]

private def loopState : State :=
  .initial recursiveBody [.unit, .cellRef functionType 0] [recursiveClosure]

/-- Allocation and mutation construct the cycle from an empty initial store. -/
private def recursiveProgram : Program := {
  resultType := .unit
  body :=
    .letE (.newCell functionType (.lambda .unit .unit .unit))
      (.letE (.storeCell (.var 0) (.lambda .unit .unit recursiveBody))
        recursiveBody)
}

private theorem recursiveProgram_checked : recursiveProgram.check = true := by
  decide

/-- The loop is a genuine machine cycle, including the same captured reference,
store and empty continuation. -/
private theorem loop_cycle : runStateful 7 loopState = .outOfFuel loopState := by
  rfl

private theorem reaches_loop :
    runStateful 12 (.initial recursiveProgram.body) = .outOfFuel loopState := by
  rfl

private theorem loop_exhausts (fuel : Nat) :
    ∃ checkpoint, runStateful fuel loopState = .outOfFuel checkpoint := by
  induction fuel using Nat.strongRecOn with
  | ind fuel inductionHypothesis =>
      by_cases short : fuel < 7
      · have cases : fuel = 0 ∨ fuel = 1 ∨ fuel = 2 ∨ fuel = 3 ∨
            fuel = 4 ∨ fuel = 5 ∨ fuel = 6 := by omega
        rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          exact ⟨_, rfl⟩
      · obtain ⟨checkpoint, exhausted⟩ :=
          inductionHypothesis (fuel - 7) (by omega)
        refine ⟨checkpoint, ?_⟩
        have resumed := runStateful_resume loop_cycle (fuel - 7)
        have sum : 7 + (fuel - 7) = fuel := by omega
        rw [sum] at resumed
        exact resumed.symm.trans exhausted

/-- This checked program has no finite successful evaluation. The proof uses
the actual machine cycle and semantics correspondence, not a timeout sample. -/
private theorem recursiveProgram_no_evaluation
    {value : Value} {store : Store}
    (evaluation : Evaluates [] [] recursiveProgram.body value store) : False := by
  obtain ⟨required, completes⟩ :=
    evaluation_runStateful_complete_with_sufficient_fuel evaluation
  obtain ⟨checkpoint, exhausted⟩ := loop_exhausts required
  have resumed := runStateful_resume reaches_loop required
  rw [exhausted, completes (12 + required) (by omega)] at resumed
  cases resumed

/-- Every fuel budget suspends, with no internal fault and no forged completion. -/
private theorem recursiveProgram_exhausts (fuel : Nat) :
    ∃ checkpoint, recursiveProgram.runStateful fuel = .outOfFuel checkpoint := by
  cases outcome : recursiveProgram.runStateful fuel with
  | done value store =>
      exact False.elim (recursiveProgram_no_evaluation
        (runStateful_evaluation_sound outcome))
  | outOfFuel checkpoint => exact ⟨checkpoint, rfl⟩
  | fault error state =>
      exact False.elim (Program.checked_runStateful_never_faults
        recursiveProgram_checked outcome)

example (fuel : Nat) :
    ∃ checkpoint,
      recursiveProgram.runStateful fuel = .outOfFuel checkpoint ∧
      StateHasType checkpoint .unit := by
  obtain ⟨checkpoint, exhausted⟩ := recursiveProgram_exhausts fuel
  exact ⟨checkpoint, exhausted,
    well_typed_runStateful_preserves_checkpoint_type
      (initial_state_has_type
        (Program.check_full_sound recursiveProgram_checked).bodyHasType) exhausted⟩

example (fuel additional : Nat) (checkpoint : State)
    (exhausted : recursiveProgram.runStateful fuel = .outOfFuel checkpoint) :
    (runStateful additional checkpoint).HasType .unit ∧
      runStateful additional checkpoint = recursiveProgram.runStateful (fuel + additional) :=
  well_typed_runStateful_resume_has_type
    (initial_state_has_type
      (Program.check_full_sound recursiveProgram_checked).bodyHasType)
    exhausted additional

/-- A captured reference that has no matching world entry is still invalid. -/
example : ¬ RuntimeValueHasType []
    (.cellRef functionType 0) (.cell functionType) := by
  intro typing
  cases typing with
  | cellRef found => cases found

end Tests.CoreGeneralCells
end

section
-- leanmerge: from Solcore.Test.CoreNamedData
/-! Executable regressions for program-local named algebraic data. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core

private def assertProgramCheckAgreement
    (name : String)
    (program : Program) : IO Unit := do
  let detailedAccepted :=
    match program.checkDetailed with
    | .ok type => type == program.resultType
    | .error _ => false
  assertTrue (detailedAccepted == program.check)
    s!"{name} made Program.checkDetailed and Program.check disagree"

private def assertInferAgreement
    (name : String)
    (definitions : DataEnvironment)
    (context : Context)
    (expression : Expr) : IO Unit := do
  assertTrue
    ((inferDetailed context [] expression definitions).toOption ==
      infer? context expression definitions)
    s!"{name} made inferDetailed and infer? disagree"

private def dataType (index : Nat) : DataTypeId := ⟨index⟩

private def constructor (ownerIndex constructorIndex : Nat) : ConstructorId :=
  ⟨dataType ownerIndex, constructorIndex⟩

private def optionBoolDefinitions : DataEnvironment := [
  { constructorPayloadTypes := [.unit, .bool] }
]

private def testConstructionMatchingAndExactFuel : IO Unit := do
  let someTrue : Expr := .construct (constructor 0 1) (.bool true)
  let program : Program := {
    resultType := .bool
    body :=
      .matchData (dataType 0) .bool someTrue [
        .bool false,
        .var 0
      ]
    dataDefinitions := optionBoolDefinitions
  }
  assertTrue program.check
    "a constructor payload and every exhaustive branch must type-check"
  assertTrue (program.run 5 == .outOfFuel)
    "five transitions must be insufficient for construction followed by matching"
  assertTrue (program.run 6 == .done (.bool true))
    "matching must expose the selected constructor payload at index zero"

  let noneProgram : Program := {
    resultType := .bool
    body :=
      .matchData (dataType 0) .bool
        (.construct (constructor 0 0) .unit)
        [.bool true, .bool false]
    dataDefinitions := optionBoolDefinitions
  }
  assertTrue noneProgram.check
    "a nullary constructor must be represented by a unit payload"
  assertTrue (noneProgram.run 6 == .done (.bool true))
    "constructor index zero must select branch index zero"

private def testNominalIdentity : IO Unit := do
  let definitions : DataEnvironment := [
    { constructorPayloadTypes := [.bool] },
    { constructorPayloadTypes := [.bool] }
  ]
  let firstProgram : Program := {
    resultType := .namedData (dataType 0)
    body := .construct (constructor 0 0) (.bool true)
    dataDefinitions := definitions
  }
  let secondProgram : Program := {
    resultType := .namedData (dataType 1)
    body := .construct (constructor 1 0) (.bool true)
    dataDefinitions := definitions
  }
  let confusedProgram : Program := {
    resultType := .namedData (dataType 0)
    body := .construct (constructor 1 0) (.bool true)
    dataDefinitions := definitions
  }
  assertTrue (firstProgram.check && secondProgram.check)
    "each same-shaped declaration must accept its own constructor"
  assertTrue (!confusedProgram.check)
    "same-shaped declarations at different table indices must remain distinct"

private def testRecursiveMutualAndEmptyDefinitions : IO Unit := do
  let recursiveDefinitions : DataEnvironment := [
    {
      constructorPayloadTypes := [
        .unit,
        .product .word (.namedData (dataType 0))
      ]
    }
  ]
  assertTrue recursiveDefinitions.isWellFormed
    "a data declaration may refer to itself in a constructor payload"
  let recursiveProgram : Program := {
    resultType := .bool
    body :=
      .matchData (dataType 0) .bool
        (.construct (constructor 0 1)
          (.pair (.word Word.zero)
            (.construct (constructor 0 0) .unit)))
        [.bool false, .bool true]
    dataDefinitions := recursiveDefinitions
  }
  assertTrue recursiveProgram.check
    "finite values of recursive named types must type-check"
  assertTrue (recursiveProgram.run 20 == .done (.bool true))
    "recursive type identities must not force recursive evaluation"

  let mutualDefinitions : DataEnvironment := [
    { constructorPayloadTypes := [.namedData (dataType 1)] },
    { constructorPayloadTypes := [.unit, .namedData (dataType 0)] }
  ]
  assertTrue mutualDefinitions.isWellFormed
    "definition validation must permit forward and mutually recursive references"
  let mutualProgram : Program := {
    resultType := .namedData (dataType 0)
    body :=
      .construct (constructor 0 0)
        (.construct (constructor 1 0) .unit)
    dataDefinitions := mutualDefinitions
  }
  assertTrue mutualProgram.check
    "mutually recursive declarations must admit finite nested values"
  assertTrue
    (mutualProgram.run 5 ==
      .done
        (.constructed (constructor 0 0)
          (.constructed (constructor 1 0) .unit)))
    "nested named-data construction must preserve both nominal identities"

  let emptyDefinitions : DataEnvironment := [
    { constructorPayloadTypes := [] }
  ]
  let emptyEliminator : Expr :=
    .lambda (.namedData (dataType 0)) .bool
      (.matchData (dataType 0) .bool (.var 0) [])
  let emptyProgram : Program := {
    resultType := .function (.namedData (dataType 0)) .bool
    body := emptyEliminator
    dataDefinitions := emptyDefinitions
  }
  assertTrue emptyProgram.check
    "an empty data type must admit an eliminator with an empty branch list"
  assertTrue
    (emptyProgram.run 1 ==
      .done
        (.closure (.namedData (dataType 0)) .bool
          (.matchData (dataType 0) .bool (.var 0) []) []))
    "an empty-data eliminator must close without trying to fabricate an inhabitant"

private def testDefinitionAndAnnotationValidity : IO Unit := do
  let functionPayloadDefinitions : DataEnvironment := [
    { constructorPayloadTypes := [.function .unit .unit] }
  ]
  let unusedTable : Program := {
    resultType := .bool
    body := .bool true
    dataDefinitions := functionPayloadDefinitions
  }
  assertTrue functionPayloadDefinitions.isWellFormed
    "function-valued constructor payloads must use ordinary type well-formedness"
  assertTrue unusedTable.check
    "an unused function-valued definition must remain admissible"
  assertTrue (unusedTable.run 1 == .done (.bool true))
    "the raw compatibility runner must execute only the body and remain unchecked"

  let unknownAnnotation : Program := {
    resultType := .unit
    body :=
      .letE
        (.lambda (.namedData (dataType 9)) .unit .unit)
        .unit
  }
  assertTrue (!unknownAnnotation.check)
    "unknown named types in otherwise unused annotations must be rejected"

  let nestedFunctionDefinitions : DataEnvironment := [
    {
      constructorPayloadTypes := [
        .product .unit (.sum .bool (.function .unit .unit))
      ]
    }
  ]
  assertTrue nestedFunctionDefinitions.isWellFormed
    "well-formed functions nested below products and sums must be admitted"

  let unknownReferenceDefinitions : DataEnvironment := [
    { constructorPayloadTypes := [.namedData (dataType 4)] }
  ]
  assertTrue (!unknownReferenceDefinitions.isWellFormed)
    "every named type referenced by a constructor payload must exist in the table"

  let namedCellContentsDefinitions : DataEnvironment := [
    { constructorPayloadTypes := [.cell (.namedData (dataType 0))] }
  ]
  assertTrue namedCellContentsDefinitions.isWellFormed
    "constructor references may point to recursively named data values"

private def testDetailedCheckingAgreement : IO Unit := do
  let validExpression : Expr :=
    .matchData (dataType 0) .bool
      (.construct (constructor 0 1) (.bool true))
      [.bool false, .var 0]
  let invalidExpression : Expr :=
    .construct (constructor 0 1) .unit
  let recursiveDefinitions : DataEnvironment := [
    { constructorPayloadTypes := [.unit, .namedData (dataType 0)] }
  ]
  let recursiveExpression : Expr :=
    .construct (constructor 0 1)
      (.construct (constructor 0 0) .unit)

  assertInferAgreement
    "valid constructor match"
    optionBoolDefinitions [] validExpression
  assertInferAgreement
    "invalid constructor payload"
    optionBoolDefinitions [] invalidExpression
  assertInferAgreement
    "recursive named construction"
    recursiveDefinitions [] recursiveExpression
  assertInferAgreement
    "unknown named lambda annotation"
    [] [] (.lambda (.namedData (dataType 3)) .unit .unit)

  let validProgram : Program := {
    resultType := .bool
    body := validExpression
    dataDefinitions := optionBoolDefinitions
  }
  let invalidBodyProgram : Program := {
    resultType := .namedData (dataType 0)
    body := invalidExpression
    dataDefinitions := optionBoolDefinitions
  }
  let invalidResultProgram : Program := {
    resultType := .namedData (dataType 7)
    body := .var 99
    dataDefinitions := optionBoolDefinitions
  }
  let invalidTableProgram : Program := {
    resultType := .unit
    body := .unit
    dataDefinitions := [
      { constructorPayloadTypes := [.function (.namedData (dataType 9)) .unit] }
    ]
  }
  for (name, program) in [
      ("valid program", validProgram),
      ("invalid body program", invalidBodyProgram),
      ("invalid result program", invalidResultProgram),
      ("invalid table program", invalidTableProgram)
    ] do
    assertProgramCheckAgreement name program

private def testDetailedNamedDataErrors : IO Unit := do
  let invalidDefinitions : DataEnvironment := [
    { constructorPayloadTypes := [.function (.namedData (dataType 9)) .unit] }
  ]
  let invalidTable : Program := {
    resultType := .namedData (dataType 8)
    body := .var 99
    dataDefinitions := invalidDefinitions
  }
  assertCheckError
    "invalid definition table priority"
    invalidTable
    []
    (.invalidDefinitionPayload 0 0 (.function (.namedData (dataType 9)) .unit))

  let nestedInvalidType : Ty :=
    .product .unit (.sum .bool (.function (.namedData (dataType 9)) .unit))
  let multipleInvalidDefinitions : DataEnvironment := [
    { constructorPayloadTypes := [.unit] },
    { constructorPayloadTypes := [.bool, nestedInvalidType] },
    { constructorPayloadTypes := [.function .word (.namedData (dataType 9))] }
  ]
  let firstInvalidDefinition : Program := {
    resultType := .namedData (dataType 8)
    body := .var 99
    dataDefinitions := multipleInvalidDefinitions
  }
  assertCheckError
    "first invalid definition payload"
    firstInvalidDefinition
    []
    (.invalidDefinitionPayload 1 1 nestedInvalidType)

  let unknownDefinitionReference : Program := {
    resultType := .unit
    body := .unit
    dataDefinitions := [
      { constructorPayloadTypes := [.namedData (dataType 5)] }
    ]
  }
  assertCheckError
    "unknown named type in definition table"
    unknownDefinitionReference
    []
    (.invalidDefinitionPayload 0 0 (.namedData (dataType 5)))

  let invalidDeclaredResult : Program := {
    resultType := .namedData (dataType 8)
    body := .var 99
  }
  assertCheckError
    "unknown declared result type"
    invalidDeclaredResult
    []
    (.unknownNamedDataType (dataType 8))

  let invalidBodyAfterValidPreamble : Program := {
    resultType := .unit
    body := .var 7
    dataDefinitions := optionBoolDefinitions
  }
  assertCheckError
    "body checked after valid table and result"
    invalidBodyAfterValidPreamble
    []
    (.unboundVariable 7 0)

  let invalidAnnotation : Program := {
    resultType := .unit
    body :=
      .letE
        (.lambda (.namedData (dataType 9)) .unit .unit)
        .unit
  }
  assertCheckError
    "unknown nested type annotation"
    invalidAnnotation
    [.letValue]
    (.unknownNamedDataType (dataType 9))

  let unknownOwner : Program := {
    resultType := .unit
    body := .construct (constructor 4 0) .unit
    dataDefinitions := optionBoolDefinitions
  }
  assertCheckError
    "unknown constructor owner"
    unknownOwner
    []
    (.unknownDataType (dataType 4))

  let unknownConstructor : Program := {
    resultType := .namedData (dataType 0)
    body := .construct (constructor 0 7) .unit
    dataDefinitions := optionBoolDefinitions
  }
  assertCheckError
    "unknown constructor index"
    unknownConstructor
    []
    (.unknownConstructor (constructor 0 7))

  let unknownMatchDataType : Program := {
    resultType := .unit
    body := .matchData (dataType 6) .unit .unit []
    dataDefinitions := optionBoolDefinitions
  }
  assertCheckError
    "unknown match data type"
    unknownMatchDataType
    []
    (.unknownDataType (dataType 6))

  let wrongPayload : Program := {
    resultType := .namedData (dataType 0)
    body := .construct (constructor 0 1) .unit
    dataDefinitions := optionBoolDefinitions
  }
  assertCheckError
    "constructor payload mismatch"
    wrongPayload
    [.constructPayload]
    (.constructorPayloadTypeMismatch .bool .unit)

  let nonDataScrutinee : Program := {
    resultType := .unit
    body := .matchData (dataType 0) .unit (.bool true) [.unit, .unit]
    dataDefinitions := optionBoolDefinitions
  }
  assertCheckError
    "non-data match scrutinee"
    nonDataScrutinee
    [.matchScrutinee]
    (.expectedNamedData .bool)

  let twoDefinitions : DataEnvironment := [
    { constructorPayloadTypes := [.unit] },
    { constructorPayloadTypes := [.unit] }
  ]
  let wrongScrutineeType : Program := {
    resultType := .unit
    body :=
      .matchData (dataType 0) .unit
        (.construct (constructor 1 0) .unit)
        [.unit]
    dataDefinitions := twoDefinitions
  }
  assertCheckError
    "match nominal type mismatch"
    wrongScrutineeType
    [.matchScrutinee]
    (.matchDataTypeMismatch (dataType 0) (dataType 1))

  let wrongBranchCount : Program := {
    resultType := .unit
    body :=
      .matchData (dataType 0) .unit
        (.construct (constructor 0 0) .unit)
        [.unit]
    dataDefinitions := optionBoolDefinitions
  }
  assertCheckError
    "match branch count"
    wrongBranchCount
    []
    (.matchBranchCountMismatch 2 1)

  let invalidScrutineeAndCount : Program := {
    resultType := .unit
    body := .matchData (dataType 0) .unit (.var 8) []
    dataDefinitions := optionBoolDefinitions
  }
  assertCheckError
    "match scrutinee before branch count"
    invalidScrutineeAndCount
    [.matchScrutinee]
    (.unboundVariable 8 0)

  let invalidCountAndBranch : Program := {
    resultType := .unit
    body :=
      .matchData (dataType 0) .unit
        (.construct (constructor 0 0) .unit)
        [.var 8]
    dataDefinitions := optionBoolDefinitions
  }
  assertCheckError
    "match branch count before branch bodies"
    invalidCountAndBranch
    []
    (.matchBranchCountMismatch 2 1)

  let wrongBranchResult : Program := {
    resultType := .bool
    body :=
      .matchData (dataType 0) .bool
        (.construct (constructor 0 0) .unit)
        [.bool true, .unit]
    dataDefinitions := optionBoolDefinitions
  }
  assertCheckError
    "match branch result"
    wrongBranchResult
    [.matchBranch 1]
    (.matchBranchResultTypeMismatch 1 .bool .unit)

  let twoInvalidBranchResults : Program := {
    resultType := .unit
    body :=
      .matchData (dataType 0) .unit
        (.construct (constructor 0 0) .unit)
        [.bool true, .word Word.zero]
    dataDefinitions := optionBoolDefinitions
  }
  assertCheckError
    "first invalid match branch"
    twoInvalidBranchResults
    [.matchBranch 0]
    (.matchBranchResultTypeMismatch 0 .unit .bool)

  let invalidFirstBranchExpression : Program := {
    resultType := .unit
    body :=
      .matchData (dataType 0) .unit
        (.construct (constructor 0 0) .unit)
        [.var 4, .bool true]
    dataDefinitions := optionBoolDefinitions
  }
  assertCheckError
    "first ill-typed match branch expression"
    invalidFirstBranchExpression
    [.matchBranch 0]
    (.unboundVariable 4 1)

  let invalidMatchResult : Program := {
    resultType := .unit
    body :=
      .letE
        (.matchData (dataType 0) (.namedData (dataType 6))
          (.construct (constructor 0 0) .unit)
          [.unit, .unit])
        .unit
    dataDefinitions := optionBoolDefinitions
  }
  assertCheckError
    "unknown match result annotation"
    invalidMatchResult
    [.letValue]
    (.unknownNamedDataType (dataType 6))

private def testEffectsAndCellReferences : IO Unit := do
  let cellDefinitions : DataEnvironment := [
    { constructorPayloadTypes := [.cell .bool] }
  ]
  let carryAndLoad : Program := {
    resultType := .bool
    body :=
      .loadCell
        (.matchData (dataType 0) (.cell .bool)
          (.construct (constructor 0 0)
            (.newCell .bool (.bool true)))
          [.var 0])
    dataDefinitions := cellDefinitions
  }
  assertTrue carryAndLoad.check
    "named data may carry an admissible first-order cell reference"
  assertTrue
    (carryAndLoad.runStateful 20 == .done (.bool true) [.bool true])
    "a cell reference extracted from named data must retain its store identity"

  let storedNamedData : Program := {
    resultType := .cell (.namedData (dataType 0))
    body :=
      .newCell (.namedData (dataType 0))
        (.construct (constructor 0 0) (.newCell .bool (.bool true)))
    dataDefinitions := cellDefinitions
  }
  assertTrue storedNamedData.check
    "named-data values must be admitted as general cell contents"
  assertTrue (storedNamedData.runStateful 20 ==
      .done (.cellRef (.namedData (dataType 0)) 1)
        [.bool true, .constructed (constructor 0 0) (.cellRef .bool 0)])
    "storing named data must retain the constructor and captured cell identity"

  let orderedEffects : Program := {
    resultType := .cell .bool
    body :=
      .matchData (dataType 0) (.cell .bool)
        (.construct (constructor 0 1)
          (.letE (.newCell .unit .unit) (.bool true)))
        [
          .letE
            (.newCell .word (.word Word.zero))
            (.newCell .bool (.bool false)),
          .newCell .bool (.var 0)
        ]
    dataDefinitions := optionBoolDefinitions
  }
  assertTrue orderedEffects.check
    "scrutinee and every branch must type-check with their own payload binder"
  assertTrue
    (orderedEffects.runStateful 40 ==
      .done (.cellRef .bool 1) [.unit, .bool true])
    "scrutinee effects must precede the selected branch and unselected effects must not run"

private def testGeneralConstructorPayloads : IO Unit := do
  let functionProgram : Program := {
    resultType := .bool
    dataDefinitions := [{ constructorPayloadTypes := [.function .bool .bool] }]
    body :=
      .matchData (dataType 0) .bool
        (.construct (constructor 0 0)
          (.lambda .bool .bool (.unary .boolNot (.var 0))))
        [.apply (.var 0) (.bool false)]
  }
  assertTrue functionProgram.check
    "constructors must admit closures and expose them to a typed match branch"
  assertTrue (functionProgram.checkDetailed.toOption == some .bool)
    "detailed checking must admit a function-valued constructor payload"
  assertTrue (functionProgram.run 30 == .done (.bool true))
    "a closure extracted from named data must remain callable"

  let nestedCellProgram : Program := {
    resultType := .bool
    dataDefinitions := [{ constructorPayloadTypes := [.cell (.cell .bool)] }]
    body :=
      .matchData (dataType 0) .bool
        (.construct (constructor 0 0)
          (.newCell (.cell .bool) (.newCell .bool (.bool false))))
        [.letE
          (.storeCell (.loadCell (.var 0)) (.bool true))
          (.loadCell (.loadCell (.var 1)))]
  }
  assertTrue nestedCellProgram.check
    "constructor payloads must allow nested cell references"
  assertTrue (nestedCellProgram.runStateful 40 ==
      .done (.bool true) [.bool true, .cellRef .bool 0])
    "matching a stored reference must preserve the shared mutable target"

private def testUncheckedMachineFaults : IO Unit := do
  let nonData : State :=
    State.initial
      (.matchData (dataType 0) .unit (.bool true) [.unit])
  assertTrue
    (run 2 nonData == .fault (.expectedNamedData (.bool true)))
    "an unchecked match must fault when its scrutinee is not named data"

  let wrongOwner : State :=
    State.initial
      (.matchData (dataType 0) .unit (.var 0) [.unit])
      [.constructed (constructor 1 0) .unit]
  assertTrue
    (run 2 wrongOwner ==
      .fault (.namedDataTypeMismatch (dataType 0) (dataType 1)))
    "an unchecked match must reject a constructor owned by another data type"

  let missingBranch : State :=
    State.initial
      (.matchData (dataType 0) .unit (.var 0) [.unit])
      [.constructed (constructor 0 3) .unit]
  assertTrue
    (run 2 missingBranch ==
      .fault (.invalidConstructorBranch (constructor 0 3)))
    "an unchecked match must report a constructor index outside its branch list"

private def testNamedDataWeakening : IO Unit := do
  let expression : Expr :=
    .matchData (dataType 0) (.product .bool .bool)
      (.construct (constructor 0 1) (.var 0))
      [
        .pair (.bool false) (.var 1),
        .pair (.var 0) (.var 1)
      ]
  let expected : Expr :=
    .matchData (dataType 0) (.product .bool .bool)
      (.construct (constructor 0 1) (.var 1))
      [
        .pair (.bool false) (.var 2),
        .pair (.var 0) (.var 2)
      ]
  assertTrue (expression.weakenAt 0 == expected)
    "weakening must cross constructor payloads and preserve every match payload binder"

/-- Cover nominal identity, recursive and empty definitions, exhaustive matching,
effects, cells, unchecked faults, weakening, and exact fuel. -/
def testCoreNamedData : IO Unit := do
  testConstructionMatchingAndExactFuel
  testNominalIdentity
  testRecursiveMutualAndEmptyDefinitions
  testDefinitionAndAnnotationValidity
  testDetailedCheckingAgreement
  testDetailedNamedDataErrors
  testEffectsAndCellReferences
  testGeneralConstructorPayloads
  testUncheckedMachineFaults
  testNamedDataWeakening

end Tests
end

section
-- leanmerge: from Solcore.Test.CoreOptionalCells
/-! Optional cells return ordinary language failures for uninitialized reads.
The same representation handles aliases, closures and shared references. -/

set_option autoImplicit false

namespace Tests.CoreOptionalCells

open Solcore.Core

private def word (value : Nat) : Word := Word.ofNatModulo value
private def literal (value : Nat) : Expr := .word (word value)
private def scalar (value : Nat) : Value := .word (word value)
private def reason : Word := word 21

private def freshProgram : Program := {
  resultType := LanguageResult.resultType .word
  body := OptionalCell.read .word (OptionalCell.allocate .word) reason
}

private theorem fresh_checked : freshProgram.check = true := by decide

/-- The new cell contains a marker rather than an arbitrary Word. Its read
finishes with a language failure, and preserves that marker in the heap. -/
private theorem fresh_evaluates :
    Evaluates [] [] freshProgram.body (.inLeft .word (.word reason))
      [.inLeft .word .unit] :=
  OptionalCell.read_failure reason (OptionalCell.allocate_evaluates .word [] []) rfl

example : freshProgram.runStateful 12 =
    .done (.inLeft .word (.word reason)) [.inLeft .word .unit] := by rfl

example : ∃ checkpoint, freshProgram.runStateful 11 = .outOfFuel checkpoint :=
  ⟨_, rfl⟩

example (fuel : Nat) :
    (freshProgram.runStateful fuel).HasType (LanguageResult.resultType .word) :=
  Program.checked_runStateful_has_type fresh_checked fuel

private def initializedProgram : Program := {
  resultType := LanguageResult.resultType .word
  body := OptionalCell.read .word
    (OptionalCell.allocateInitialized .word (literal 9)) reason
}

example : initializedProgram.check = true := by decide

example : Evaluates [] [] initializedProgram.body (.inRight .word (scalar 9))
    [.inRight .unit (scalar 9)] :=
  OptionalCell.read_success reason (OptionalCell.allocateInitialized_evaluates .word) rfl

example : initializedProgram.runStateful 12 =
    .done (.inRight .word (scalar 9)) [.inRight .unit (scalar 9)] := by rfl

/-- Write through an alias, then read through the original handle. -/
private def aliasProgram : Program := {
  resultType := LanguageResult.resultType .word
  body := .letE (OptionalCell.allocate .word)
    (.letE (.var 0)
      (LanguageResult.bind .word (OptionalCell.write (.var 0) (literal 7))
        (OptionalCell.read .word (.var 2) reason)))
}

private theorem alias_checked : aliasProgram.check = true := by decide

private theorem alias_completed : aliasProgram.runStateful 64 =
    .done (.inRight .word (scalar 7)) [.inRight .unit (scalar 7)] := by rfl

example : ∃ world,
    RuntimeStoreHasTypes world [.inRight .unit (scalar 7)] ∧
    RuntimeValueHasType world (.inRight .word (scalar 7))
      (LanguageResult.resultType .word) :=
  Program.checked_runStateful_preserves_result_type alias_checked alias_completed

/-- If the read fails, the bind never evaluates its continuation's mutation. -/
private def shortCircuitProgram : Program := {
  resultType := LanguageResult.resultType .unit
  body := .letE (OptionalCell.allocate .word)
    (.letE (.newCell .word (literal 99))
      (LanguageResult.bind .unit (OptionalCell.read .word (.var 1) reason)
        (LanguageResult.success (.storeCell (.var 1) (literal 100)))))
}

private theorem shortCircuit_checked : shortCircuitProgram.check = true := by decide

private theorem shortCircuit_evaluates :
    Evaluates [] [] shortCircuitProgram.body (.inLeft .unit (.word reason))
      [.inLeft .word .unit, scalar 99] := by
  exact .letE (OptionalCell.allocate_evaluates .word [] [])
    (.letE (.newCell .word)
      (LanguageResult.bind_failure .unit
        (OptionalCell.read_failure reason (.var rfl) rfl)))

example : shortCircuitProgram.runStateful 64 =
    .done (.inLeft .unit (.word reason)) [.inLeft .word .unit, scalar 99] := by rfl

private def functionType : Ty := .function .word .word

/-- Captures are optional alias, original optional reference, and shared counter. -/
private def functionBody : Expr :=
  .letE (.storeCell (.var 3) (.var 0)) (.loadCell (.var 4))

/-- An uninitialized function binding requires no dummy closure. Installing a
closure preserves its two aliases and its shared mutable counter. -/
private def functionProgram : Program := {
  resultType := LanguageResult.resultType .word
  body := .letE (.newCell .word (literal 3))
    (.letE (OptionalCell.allocate functionType)
      (.letE (.var 0)
        (LanguageResult.bind .word
          (OptionalCell.write (.var 0) (.lambda .word .word functionBody))
          (LanguageResult.bind .word
            (OptionalCell.read functionType (.var 2) reason)
            (LanguageResult.success (.apply (.var 0) (literal 7)))))))
}

private def installedClosure : Value :=
  .closure .word .word functionBody
    [.cellRef (OptionalCell.cellType functionType) 1,
     .cellRef (OptionalCell.cellType functionType) 1, .cellRef .word 0]

private def functionStore : Store :=
  [scalar 7, .inRight .unit installedClosure]

private theorem function_checked : functionProgram.check = true := by decide

set_option maxRecDepth 2048 in
private theorem function_completed : functionProgram.runStateful 128 =
    .done (.inRight .word (scalar 7)) functionStore := by rfl

/-- The optional function's captures include its own cell, and remain valid
after the captured counter is mutated through that same shared store. -/
example : RuntimeStoreHasTypes [.word, OptionalCell.cellType functionType] functionStore := by
  obtain ⟨world, stored, _⟩ :=
    Program.checked_runStateful_preserves_result_type function_checked function_completed
  have exactWorld : world = [.word, OptionalCell.cellType functionType] := by
    simpa only [functionStore, List.map_cons, List.map_nil, Value.type,
      scalar, installedClosure, OptionalCell.cellType, functionType] using stored.world_eq
  change RuntimeStoreHasTypes world functionStore at stored
  simpa only [exactWorld] using stored

/-- The ordinary checked-machine guarantee applies to every suspension and
its resumed run, including the eventual language failure. -/
example (fuel additional : Nat) (checkpoint : State)
    (exhausted : shortCircuitProgram.runStateful fuel = .outOfFuel checkpoint) :
    StateHasType checkpoint (LanguageResult.resultType .unit) ∧
    (runStateful additional checkpoint).HasType (LanguageResult.resultType .unit) ∧
    runStateful additional checkpoint = shortCircuitProgram.runStateful (fuel + additional) := by
  have typed := initial_state_has_type
    (Program.check_full_sound shortCircuit_checked).bodyHasType
  have checkpointTyped := well_typed_runStateful_preserves_checkpoint_type typed exhausted
  exact ⟨checkpointTyped, well_typed_runStateful_resume_has_type typed exhausted additional⟩

example : ∃ required world,
    RuntimeStoreHasTypes world [.inLeft .word .unit, scalar 99] ∧
    RuntimeValueHasType world (.inLeft .unit (.word reason)) (LanguageResult.resultType .unit) ∧
    ∀ fuel, required ≤ fuel → shortCircuitProgram.runStateful fuel =
      .done (.inLeft .unit (.word reason)) [.inLeft .word .unit, scalar 99] := by
  obtain ⟨world, _, stored, typed⟩ := evaluation_preserves_type shortCircuit_evaluates
    (Program.check_full_sound shortCircuit_checked).bodyHasType .nil (.nil [])
  obtain ⟨required, completes⟩ :=
    evaluation_runStateful_complete_with_sufficient_fuel shortCircuit_evaluates
  exact ⟨required, world, stored, typed, completes⟩

/-- Nominal declarations are supported by the same allocation/read typing rule. -/
example {definitions : DataEnvironment} {context : Context} {type : Ty}
    (wellFormed : Ty.WellFormed definitions type) (reason : Word) :
    HasType context (OptionalCell.read type (OptionalCell.allocate type) reason)
      (LanguageResult.resultType type) definitions :=
  OptionalCell.read_hasType reason wellFormed (OptionalCell.allocate_hasType wellFormed)

end Tests.CoreOptionalCells
end

section
-- leanmerge: from Solcore.Test.CoreOrderedMapping
/-! Generic mapping helpers use nonzero catalog identities, caller comparison,
optional lookup results, and structural/function payloads through real Core. -/

set_option autoImplicit false

namespace Tests.CoreOrderedMapping

open Solcore.Core

private def w (value : Nat) : Word := Word.ofNatModulo value
private def layout : OrderedMapping.Layout := ⟨.integer, .product .bool .word, ⟨1⟩⟩
private def definitions : DataEnvironment := [{constructorPayloadTypes := [.unit]}, layout.definition]
private def comparison : Expr := .lambda (.product .integer .integer) .bool
  (.binary .integerEq (.first (.var 0)) (.second (.var 0)))
private def pairExpr (flag : Bool) (value : Nat) : Expr := .pair (.bool flag) (.word (w value))
private def pairValue (flag : Bool) (value : Nat) : Value := .pair (.bool flag) (.word (w value))
private def entries : OrderedMapping.Entries :=
  [(.integer (-4), pairValue true 7), (.integer 2, pairValue false 9), (.integer (-4), pairValue false 11)]
private def literal : Expr :=
  OrderedMapping.cons layout (.integer (-4)) (pairExpr true 7)
    (OrderedMapping.cons layout (.integer 2) (pairExpr false 9)
      (OrderedMapping.cons layout (.integer (-4)) (pairExpr false 11) (OrderedMapping.empty layout)))
private def program (resultType : Ty) (body : Expr) : Program := ⟨resultType, body, definitions⟩

example : layout.Registered definitions := ⟨.integer, .product .bool .word, rfl⟩

/-- Ordinary application supplies the equality proof for arbitrary store state. -/
example (left right : Int) (store : Store) :
    OrderedMapping.Compares layout
      (.closure (.product .integer .integer) .bool
        (.binary .integerEq (.first (.var 0)) (.second (.var 0))) [])
      (.integer left) (.integer right) (left == right) store :=
  ⟨_, [], rfl, .binary (.first (.var rfl)) (.second (.var rfl)) rfl⟩

private def integerRel (source : Solcore.SourceSemantics.Dynamic.Value) (target : Value) : Prop :=
  ∃ value : Int, source = .integer value ∧ target = .integer value
private def integerEqual : OrderedMapping.Predicate
  | .integer left, .integer right => left == right
  | _, _ => false
private def productRel (source : Solcore.SourceSemantics.Dynamic.Value) (target : Value) : Prop :=
  ∃ flag value, source = .product (.bool flag) (.word value) ∧ target = .pair (.bool flag) (.word value)

private theorem integerEqual_correct :
    Solcore.SourceSemantics.CoreLowering.OrderedMapping.KeyEqualityCorrect integerRel integerEqual where
  equivalent := by
    rintro sourceKey sourceStored key stored ⟨left, rfl, rfl⟩ ⟨right, rfl, rfl⟩
    constructor
    · intro equivalent
      have same : left = right := of_decide_eq_true (show decide (left = right) = true from equivalent)
      subst right
      exact ⟨rfl, .integer left⟩
    · intro equivalent
      have same := Solcore.SourceSemantics.Dynamic.Value.integer.inj equivalent.1
      subst right
      simp [integerEqual]

/-- Concrete independent source update, actual comparison execution, and full
Core installation combine into a finite run with the related product value. -/
example : ∃ output finalStore required,
    Solcore.SourceSemantics.CoreLowering.OrderedMapping.ValueRel layout integerRel productRel
      [(Solcore.SourceSemantics.Dynamic.Value.integer (-4), .product (.bool false) (.word (w 42)))] output ∧
    ∀ fuel, required ≤ fuel →
      runStateful fuel (State.initial (OrderedMapping.insert layout comparison
        (OrderedMapping.cons layout (.integer (-4)) (pairExpr true 7) (OrderedMapping.empty layout))
        (.integer (-4)) (pairExpr false 42))) = .done (.inRight .word output) finalStore := by
  apply Solcore.SourceSemantics.CoreLowering.OrderedMapping.insert_run_preserves
    integerEqual_correct layout (key := .integer (-4))
    (comparator := .closure (.product .integer .integer) .bool
      (.binary .integerEq (.first (.var 0)) (.second (.var 0))) [])
  · exact ⟨-4, rfl, rfl⟩
  · exact ⟨false, w 42, rfl, rfl⟩
  · exact .cons ⟨-4, rfl, rfl⟩ ⟨true, w 7, rfl, rfl⟩ .nil
  · exact .update (.head ⟨rfl, .integer (-4)⟩)
  · exact .construct (.pair (.pair .integer (.pair .bool .word)) (.construct .unit))
  · exact .integer
  · exact .pair .bool .word
  · exact .lambda
  · intro storedKey storedValue member
    have same := List.mem_singleton.mp member
    cases same
    exact ⟨_, [], rfl, .binary (.first (.var rfl)) (.second (.var rfl)) rfl⟩

private def latestProgram : Program := program (OptionalCell.cellType layout.type)
  (.letE (OptionalCell.allocateInitialized layout.type (OrderedMapping.empty layout))
    (.letE (OrderedMapping.assign layout comparison (.var 0)
      (LanguageResult.success (.integer (-4)))
      (.letE (.storeCell (.var 0) (.inRight .unit literal))
        (LanguageResult.success (pairExpr false 42))))
      (.loadCell (.var 1))))

private def failedRhsProgram : Program := program (LanguageResult.resultType .unit)
  (.letE (OptionalCell.allocateInitialized layout.type (OrderedMapping.empty layout))
    (OrderedMapping.assign layout comparison (.var 0)
      (LanguageResult.success (.integer (-4)))
      (.letE (.storeCell (.var 0) (.inRight .unit literal))
        (LanguageResult.failure layout.valueType (.word (w 18))))))

private def functionLayout : OrderedMapping.Layout := ⟨.integer, .function .integer .integer, ⟨1⟩⟩
private def capturedFunction : Expr := .lambda .integer .integer
  (.letE (.storeCell (.var 1) (.binary .integerAdd (.loadCell (.var 1)) (.var 0))) (.loadCell (.var 2)))
private def capturedProgram : Program := {
  resultType := LanguageResult.resultType .integer
  dataDefinitions := [{constructorPayloadTypes := [.unit]}, functionLayout.definition]
  body := .letE (.newCell .integer (.integer 4))
    (LanguageResult.bind .integer
      (OrderedMapping.lookup functionLayout comparison
        (OrderedMapping.cons functionLayout (.integer 1) capturedFunction (OrderedMapping.empty functionLayout))
        (.integer 1))
      (.caseE (.var 0) (LanguageResult.failure .integer (.word (w 19)))
        (.letE (.apply (.var 0) (.integer 3))
          (LanguageResult.success (.apply (.var 1) (.integer 5))))))
}

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)
private def completes (program : Program) (value : Value) : IO Store := do
  assertTrue program.check "generic mapping failed its registered checker"
  match program.runStateful 10000 with
  | .done result store =>
      assertTrue (result == value) s!"generic mapping result mismatch: {reprStr result}"
      return store
  | result => throw (IO.userError s!"generic mapping did not complete: {reprStr result}")

def run : IO Unit := do
  let lookupFound := program (LanguageResult.resultType layout.lookupResult)
    (OrderedMapping.lookup layout comparison literal (.integer (-4)))
  discard <| completes lookupFound (.inRight .word (.inRight .unit (pairValue true 7)))
  let lookupAbsent := program (LanguageResult.resultType layout.lookupResult)
    (OrderedMapping.lookup layout comparison literal (.integer 5))
  discard <| completes lookupAbsent (.inRight .word (.inLeft layout.valueType .unit))
  let defaulted := program (LanguageResult.resultType layout.valueType)
    (LanguageResult.bind layout.valueType lookupAbsent.body
      (.caseE (.var 0) (LanguageResult.success (pairExpr true 100)) (LanguageResult.success (.var 0))))
  discard <| completes defaulted (.inRight .word (pairValue true 100))
  let defaultFailed := program (LanguageResult.resultType layout.valueType)
    (LanguageResult.bind layout.valueType lookupAbsent.body
      (.caseE (.var 0) (LanguageResult.failure layout.valueType (.word (w 21)))
        (LanguageResult.success (.var 0))))
  discard <| completes defaultFailed (.inLeft layout.valueType (.word (w 21)))

  let updated : OrderedMapping.Entries :=
    [(.integer (-4), pairValue false 42), (.integer 2, pairValue false 9), (.integer (-4), pairValue false 11)]
  let insertion := program (LanguageResult.resultType layout.type)
    (OrderedMapping.insert layout comparison literal (.integer (-4)) (pairExpr false 42))
  let insertedStore ← completes insertion (.inRight .word (OrderedMapping.encode layout updated))
  assertTrue (insertedStore.length == 1) "recursion must share one installed self cell"
  discard <| completes (program (LanguageResult.resultType layout.type)
    (OrderedMapping.insert layout comparison literal (.integer 5) (pairExpr true 17)))
      (.inRight .word (OrderedMapping.encode layout (entries ++ [(.integer 5, pairValue true 17)])))
  let neverEqual : Expr := .lambda (.product .integer .integer) .bool (.bool false)
  discard <| completes (program (LanguageResult.resultType layout.type)
    (OrderedMapping.insert layout neverEqual literal (.integer (-4)) (pairExpr true 99)))
      (.inRight .word (OrderedMapping.encode layout (entries ++ [(.integer (-4), pairValue true 99)])))
  assertTrue (!( { lookupFound with dataDefinitions := [layout.definition] } : Program).check)
    "the actual mapping catalog identity must be checked"
  assertTrue (!(program (LanguageResult.resultType layout.lookupResult)
    (OrderedMapping.lookup layout (.lambda (.product .word .word) .bool (.bool true)) literal (.integer 0))).check)
    "the comparator must accept the precise key pair type"

  let latestStore ← completes latestProgram (.inRight .unit (OrderedMapping.encode layout updated))
  assertTrue (latestStore[0]? == some (.inRight .unit (OrderedMapping.encode layout updated)) && latestStore.length == 2)
    "generic writeback must use the root installed by the RHS"
  let failureStore ← completes failedRhsProgram (.inLeft .unit (.word (w 18)))
  assertTrue (failureStore == [.inRight .unit (OrderedMapping.encode layout entries)])
    "RHS failure must keep its root effects and skip helper allocation"
  let capturedStore ← completes capturedProgram (.inRight .word (.integer 12))
  assertTrue (capturedStore[0]? == some (.integer 12) && capturedStore.length == 2)
    "a function payload must retain the original mutable capture location"
  match latestProgram.runStateful 25 with
  | .outOfFuel checkpoint =>
      assertTrue (runStateful 10000 checkpoint == latestProgram.runStateful 10025)
        "generic mapping must resume from the actual store checkpoint"
  | result => throw (IO.userError s!"expected mapping suspension, got {reprStr result}")

end Tests.CoreOrderedMapping
end

section
-- leanmerge: from Solcore.Test.CoreProducts
/-! Executable regressions for the first internal Semantic Core vNext slice. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core

private def assertExpectedProduct
    (name : String)
    (program : Program)
    (path : CheckPath)
    (actual : Ty) : IO Unit := do
  match program.checkDetailed with
  | .ok type =>
      throw (IO.userError s!"{name} unexpectedly checked as {reprStr type}")
  | .error error =>
      assertTrue (error.code == .expectedProduct)
        s!"{name} returned {error.codeName}, expected core.check.expected-product"
      assertTrue (error.path == path)
        s!"{name} returned path {reprStr error.path}, expected {reprStr path}"
      assertTrue (error.data == .expectedProduct actual)
        s!"{name} reported the wrong non-product type: {reprStr error.data}"

private def assertUnboundVariable
    (name : String)
    (program : Program)
    (path : CheckPath)
    (index contextSize : Nat) : IO Unit := do
  match program.checkDetailed with
  | .ok type =>
      throw (IO.userError s!"{name} unexpectedly checked as {reprStr type}")
  | .error error =>
      assertTrue (error.code == .unboundVariable)
        s!"{name} returned {error.codeName}, expected core.check.unbound-variable"
      assertTrue (error.path == path)
        s!"{name} returned path {reprStr error.path}, expected {reprStr path}"
      assertTrue (error.data == .unboundVariable index contextSize)
        s!"{name} reported the wrong variable lookup: {reprStr error.data}"

private def testProductTypingAndExecution : IO Unit := do
  let pairProgram : Program := {
    resultType := .product .bool .word
    body := .pair (.bool true) (.word Word.zero)
  }
  assertTrue pairProgram.check
    "a pair expression must infer the product of its component types"
  assertTrue (pairProgram.run 4 == .outOfFuel)
    "four transitions must be insufficient for a pair of literals"
  assertTrue (pairProgram.run 5 == .done (.pair (.bool true) (.word Word.zero)))
    "a pair of literals must finish exactly at five transitions"

  let nestedProgram : Program := {
    resultType := .product .bool (.product .unit .word)
    body := .pair (.bool false) (.pair .unit (.word Word.zero))
  }
  assertTrue nestedProgram.check
    "product types and pair values must nest recursively"
  assertTrue (nestedProgram.run 8 == .outOfFuel)
    "eight transitions must be insufficient for the nested pair witness"
  assertTrue
    (nestedProgram.run 9 ==
      .done (.pair (.bool false) (.pair .unit (.word Word.zero))))
    "the nested pair witness must finish exactly at nine transitions"

  let firstProgram : Program := {
    resultType := .bool
    body := .first (.pair (.bool true) (.word Word.zero))
  }
  assertTrue firstProgram.check
    "first must infer the left component type of a product"
  assertTrue (firstProgram.run 6 == .outOfFuel)
    "six transitions must be insufficient for first over a literal pair"
  assertTrue (firstProgram.run 7 == .done (.bool true))
    "first must finish exactly at seven transitions and select the left value"

  let secondProgram : Program := {
    resultType := .word
    body := .second (.pair (.bool true) (.word Word.zero))
  }
  assertTrue secondProgram.check
    "second must infer the right component type of a product"
  assertTrue (secondProgram.run 6 == .outOfFuel)
    "six transitions must be insufficient for second over a literal pair"
  assertTrue (secondProgram.run 7 == .done (.word Word.zero))
    "second must finish exactly at seven transitions and select the right value"

private def testProductFaultsAndOrder : IO Unit := do
  let invalidPairLeft : Program := {
    resultType := .product .unit .unit
    body := .pair (.var 11) .unit
  }
  assertUnboundVariable
    "invalid pair left" invalidPairLeft [.pairLeft] 11 0

  let invalidPairRight : Program := {
    resultType := .product .unit .unit
    body := .pair .unit (.var 22)
  }
  assertUnboundVariable
    "invalid pair right" invalidPairRight [.pairRight] 22 0

  let invalidPairBoth : Program := {
    resultType := .product .unit .unit
    body := .pair (.var 11) (.var 22)
  }
  assertUnboundVariable
    "invalid pair both" invalidPairBoth [.pairLeft] 11 0

  let invalidFirst : Program := {
    resultType := .bool
    body := .first (.bool true)
  }
  assertTrue (!invalidFirst.check)
    "first must reject a statically non-product operand"
  assertExpectedProduct "first of bool" invalidFirst [.firstOperand] .bool
  assertTrue (invalidFirst.run 2 == .fault (.expectedProduct (.bool true)))
    "the unchecked machine must fault when first receives a bool"

  let invalidSecond : Program := {
    resultType := .word
    body := .second .unit
  }
  assertTrue (!invalidSecond.check)
    "second must reject a statically non-product operand"
  assertExpectedProduct "second of unit" invalidSecond [.secondOperand] .unit
  assertTrue (invalidSecond.run 2 == .fault (.expectedProduct .unit))
    "the unchecked machine must fault when second receives unit"

  let leftFaultsFirst : Program := {
    resultType := .product .unit .unit
    body := .pair (.var 11) (.var 22)
  }
  assertTrue
    (leftFaultsFirst.run 1 == .fault (.unboundVariable 11))
    "pair construction must evaluate its left component first"

  let rightAfterLeft : Program := {
    resultType := .product .unit .unit
    body := .pair .unit (.var 22)
  }
  assertTrue
    (rightAfterLeft.run 3 == .fault (.unboundVariable 22))
    "pair construction must evaluate the right component after the left finishes"

/-- Cover product typing, execution order, and projection faults as one focused
semantic-slice regression. -/
def testCoreProducts : IO Unit := do
  testProductTypingAndExecution
  testProductFaultsAndOrder

end Tests
end

section
-- leanmerge: from Solcore.Test.CoreRecursiveCells
/-! Terminating recursion through ordinary closure cells. The observations
include results, shared mutation counts, returned references, and exact stores. -/

set_option autoImplicit false

namespace Tests.CoreRecursiveCells

open Solcore.Core

private def word (value : Nat) : Word := Word.ofNatModulo value
private def literal (value : Nat) : Expr := .word (word value)
private def scalar (value : Nat) : Value := .word (word value)

private def sumFunctionType : Ty := .function .word .word

/-- Entry environment: argument, self reference, shared counter reference.
The sequencing let shifts all three positions before the recursive branch. -/
private def sumBody : Expr :=
  .letE
    (.storeCell (.var 2) (.binary .wordAdd (.loadCell (.var 2)) (literal 1)))
    (.ifE (.binary .wordEq (.var 1) (literal 0))
      (literal 0)
      (.binary .wordAdd (.var 1)
        (.apply (.loadCell (.var 2)) (.binary .wordSub (.var 1) (literal 1)))))

private def sumObservationType : Ty :=
  .product .word (.product .word
    (.product .word (.product (.cell sumFunctionType) (.cell .word))))

/-- Invoke the input function twice. Its two calls and all recursive calls
share the same captured cells. The client returns both cell handles as well. -/
private def callSumTwice : Expr :=
  .lambda sumFunctionType sumObservationType
    (.letE (.apply (.var 0) (literal 3))
      (.letE (.apply (.var 1) (literal 2))
        (.pair (.var 1)
          (.pair (.var 0)
            (.pair (.loadCell (.var 5)) (.pair (.var 4) (.var 5)))))))

private def sumProgram : Program := {
  resultType := sumObservationType
  body :=
    .letE (.newCell .word (literal 0))
      (.letE (.newCell sumFunctionType (.lambda .word .word (literal 0)))
        (.letE (.storeCell (.var 0) (.lambda .word .word sumBody))
          (.apply callSumTwice (.loadCell (.var 1)))))
}

private theorem sumProgram_checked : sumProgram.check = true := by decide

private def sumClosure : Value :=
  .closure .word .word sumBody [.cellRef sumFunctionType 1, .cellRef .word 0]

private def sumObservation : Value :=
  .pair (scalar 6) (.pair (scalar 3)
    (.pair (scalar 7) (.pair (.cellRef sumFunctionType 1) (.cellRef .word 0))))

private def sumStore : Store := [scalar 7, sumClosure]

private def parityFunctionType : Ty := .function .word .bool

/-- Entry environment: argument, odd reference, even reference, shared count. -/
private def evenBody : Expr :=
  .letE
    (.storeCell (.var 3) (.binary .wordAdd (.loadCell (.var 3)) (literal 1)))
    (.ifE (.binary .wordEq (.var 1) (literal 0))
      (.bool true)
      (.apply (.loadCell (.var 2)) (.binary .wordSub (.var 1) (literal 1))))

/-- The prior installation contributes a captured unit before both references. -/
private def oddBody : Expr :=
  .letE
    (.storeCell (.var 4) (.binary .wordAdd (.loadCell (.var 4)) (literal 1)))
    (.ifE (.binary .wordEq (.var 1) (literal 0))
      (.bool false)
      (.apply (.loadCell (.var 4)) (.binary .wordSub (.var 1) (literal 1))))

private def parityObservationType : Ty :=
  .product .bool (.product .bool (.product .word
    (.product (.cell parityFunctionType) (.product (.cell parityFunctionType) (.cell .word)))))

private def parityProgram : Program := {
  resultType := parityObservationType
  body :=
    .letE (.newCell .word (literal 0)) <|
    .letE (.newCell parityFunctionType (.lambda .word .bool (.bool false))) <|
    .letE (.newCell parityFunctionType (.lambda .word .bool (.bool false))) <|
    .letE (.storeCell (.var 1) (.lambda .word .bool evenBody)) <|
    .letE (.storeCell (.var 1) (.lambda .word .bool oddBody)) <|
    .letE (.apply (.loadCell (.var 3)) (literal 4)) <|
    .letE (.apply (.loadCell (.var 3)) (literal 3)) <|
    .pair (.var 1) (.pair (.var 0) (.pair (.loadCell (.var 6))
      (.pair (.var 5) (.pair (.var 4) (.var 6)))))
}

private theorem parityProgram_checked : parityProgram.check = true := by decide

private def evenClosure : Value :=
  .closure .word .bool evenBody
    [.cellRef parityFunctionType 2, .cellRef parityFunctionType 1, .cellRef .word 0]

private def oddClosure : Value :=
  .closure .word .bool oddBody
    [.unit, .cellRef parityFunctionType 2, .cellRef parityFunctionType 1, .cellRef .word 0]

private def parityObservation : Value :=
  .pair (.bool true) (.pair (.bool true) (.pair (scalar 9)
    (.pair (.cellRef parityFunctionType 1)
      (.pair (.cellRef parityFunctionType 2) (.cellRef .word 0)))))

private def parityStore : Store := [scalar 9, evenClosure, oddClosure]

/-! These bounds count actual machine transitions. In particular, admission is
checked separately from the finite execution evidence below. -/

set_option maxRecDepth 4096 in
private theorem sum_completed :
    sumProgram.runStateful 274 = .done sumObservation sumStore := by rfl

set_option maxRecDepth 4096 in
private theorem sum_predecessor_exhausted :
    ∃ checkpoint, sumProgram.runStateful 273 = .outOfFuel checkpoint := by
  exact ⟨_, rfl⟩

set_option maxRecDepth 4096 in
private theorem parity_completed :
    parityProgram.runStateful 329 = .done parityObservation parityStore := by rfl

set_option maxRecDepth 4096 in
private theorem parity_predecessor_exhausted :
    ∃ checkpoint, parityProgram.runStateful 328 = .outOfFuel checkpoint := by
  exact ⟨_, rfl⟩

private theorem exact_steps_of_boundary
    {start : State} {cost : Nat} {value : Value} {store : Store}
    (completed : runStateful (cost + 1) start = .done value store)
    (exhausted : ∃ checkpoint, runStateful cost start = .outOfFuel checkpoint) :
    Steps (cost + 1) start (State.final value store) := by
  obtain ⟨actual, enough, path⟩ := runStateful_sound completed
  have lower : cost < actual := path.runStateful_outOfFuel_iff.mp exhausted
  have exactCost : actual = cost + 1 := by omega
  simpa only [exactCost] using path

private theorem sum_steps :
    Steps 274 (State.initial sumProgram.body) (State.final sumObservation sumStore) :=
  exact_steps_of_boundary sum_completed sum_predecessor_exhausted

private theorem parity_steps :
    Steps 329 (State.initial parityProgram.body)
      (State.final parityObservation parityStore) :=
  exact_steps_of_boundary parity_completed parity_predecessor_exhausted

private theorem sum_exact_fuel (fuel : Nat) :
    sumProgram.runStateful fuel = .done sumObservation sumStore ↔ 274 ≤ fuel :=
  sum_steps.runStateful_done_iff

private theorem parity_exact_fuel (fuel : Nat) :
    parityProgram.runStateful fuel = .done parityObservation parityStore ↔ 329 ≤ fuel :=
  parity_steps.runStateful_done_iff

private theorem sum_evaluates :
    Evaluates [] [] sumProgram.body sumObservation sumStore :=
  runStateful_evaluation_sound sum_completed

private theorem parity_evaluates :
    Evaluates [] [] parityProgram.body parityObservation parityStore :=
  runStateful_evaluation_sound parity_completed

/-- The runtime world types both the self reference in the closure and the
returned handle without recursively unfolding the store. -/
private theorem sum_result_typed :
    RuntimeStoreHasTypes [.word, sumFunctionType] sumStore ∧
      RuntimeValueHasType [.word, sumFunctionType] sumObservation sumObservationType := by
  obtain ⟨world, stored, typed⟩ :=
    Program.checked_runStateful_preserves_result_type sumProgram_checked sum_completed
  have sameWorld : world = [.word, sumFunctionType] := stored.world_eq
  subst world
  exact ⟨stored, typed⟩

/-- Both closure cells contain references to the same two function locations
and the same counter, including references forming a cycle. -/
private theorem parity_result_typed :
    RuntimeStoreHasTypes [.word, parityFunctionType, parityFunctionType] parityStore ∧
      RuntimeValueHasType [.word, parityFunctionType, parityFunctionType]
        parityObservation parityObservationType := by
  obtain ⟨world, stored, typed⟩ :=
    Program.checked_runStateful_preserves_result_type parityProgram_checked parity_completed
  have sameWorld : world = [.word, parityFunctionType, parityFunctionType] := stored.world_eq
  subst world
  exact ⟨stored, typed⟩

/-- Resume the actual pre-completion checkpoint, retaining its cyclic heap. -/
private theorem sum_resume_typed :
    ∃ checkpoint,
      sumProgram.runStateful 273 = .outOfFuel checkpoint ∧
      StateHasType checkpoint sumObservationType ∧
      runStateful 1 checkpoint = .done sumObservation sumStore ∧
      (runStateful 1 checkpoint).HasType sumObservationType := by
  obtain ⟨checkpoint, exhausted⟩ := sum_predecessor_exhausted
  have initialTyped := initial_state_has_type
    (Program.check_full_sound sumProgram_checked).bodyHasType
  have checkpointTyped := well_typed_runStateful_preserves_checkpoint_type
    initialTyped exhausted
  obtain ⟨resumedTyped, resumed⟩ := well_typed_runStateful_resume_has_type
    initialTyped exhausted 1
  exact ⟨checkpoint, exhausted, checkpointTyped, resumed.trans sum_completed, resumedTyped⟩

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def checkExecution (label : String) (program : Program)
    (cost : Nat) (expected : Value) (expectedStore : Store) : IO Unit := do
  assertTrue program.check s!"{label}: the recursive program must pass the checker"
  assertTrue (program.runStateful cost == .done expected expectedStore)
    s!"{label}: results, mutation count, shared references, and closure captures must agree"
  match program.runStateful (cost - 1) with
  | .outOfFuel checkpoint =>
      assertTrue (runStateful 1 checkpoint == .done expected expectedStore)
        s!"{label}: one more transition must complete from the retained checkpoint"
  | _ => throw (IO.userError s!"{label}: the preceding fuel bound must exhaust")

/-- Cover self recursion passed as a function argument and called twice, mutual
recursion, shared mutation, cyclic stores, exact fuel, and resumption. -/
def run : IO Unit := do
  checkExecution "self recursion" sumProgram 274 sumObservation sumStore
  checkExecution "mutual recursion" parityProgram 329 parityObservation parityStore

end Tests.CoreRecursiveCells
end

section
-- leanmerge: from Solcore.Test.CoreSums
/-! Executable regressions for internal binary sums and exhaustive case analysis. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core

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
end

section
-- leanmerge: from Solcore.Test.CoreTaggedFunction
set_option autoImplicit false

namespace Tests.CoreTaggedFunction

open Solcore.Core

private def word (value : Nat) : Word := Word.ofNatModulo value
private def literal (value : Nat) : Expr := .word (word value)
private def scalar (value : Nat) : Value := .word (word value)
private def callableType : Ty := TaggedFunction.functionType .unit .word

/-- The closure captures a location and observes a write after creation. -/
private def capturedProgram : Program := {
  resultType := LanguageResult.resultType .word
  body := .letE (.newCell .word (literal 1))
    (.letE (TaggedFunction.anonymous (.lambda .unit (LanguageResult.resultType .word)
      (LanguageResult.success (.loadCell (.var 1)))))
      (.letE (.storeCell (.var 1) (literal 7))
        (TaggedFunction.call .word (LanguageResult.success (.var 1))
          (LanguageResult.success .unit))))
}

private def calleeFailure : Program := {
  resultType := LanguageResult.resultType .word
  body := .letE (.newCell .word (literal 1))
    (TaggedFunction.call .word (LanguageResult.failure callableType (literal 41))
      (.letE (.storeCell (.var 0) (literal 99)) (LanguageResult.success .unit)))
}

/-- The argument updates the store, then fails; the closure body is skipped. -/
private def argumentFailure : Program := {
  resultType := LanguageResult.resultType .word
  body := .letE (.newCell .word (literal 1))
    (TaggedFunction.call .word
      (LanguageResult.success (TaggedFunction.anonymous
        (.lambda .unit (LanguageResult.resultType .word)
          (.letE (.storeCell (.var 1) (literal 99)) (LanguageResult.success (literal 99))))))
      (.letE (.storeCell (.var 0) (literal 7)) (LanguageResult.failure .unit (literal 42))))
}

private def identityProgram (left right : Expr) : Program := {
  resultType := LanguageResult.resultType .bool
  body := TaggedFunction.equal (LanguageResult.success left) (LanguageResult.success right)
}

private def functionBody : Expr :=
  .lambda .unit (LanguageResult.resultType .word) (LanguageResult.success (literal 8))

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def expect (label : String) (program : Program) (value : Value) (store : Store := []) : IO Unit := do
  assertTrue program.check s!"{label}: checker rejected the function representation"
  assertTrue (program.runStateful 1000 == .done value store)
    s!"{label}: function result or shared store differs"

def run : IO Unit := do
  expect "mutable capture" capturedProgram (.inRight .word (scalar 7)) [scalar 7]
  expect "failed callee" calleeFailure (.inLeft .word (scalar 41)) [scalar 1]
  expect "failed argument" argumentFailure (.inLeft .word (scalar 42)) [scalar 7]
  let anonymous := TaggedFunction.anonymous functionBody
  let named := TaggedFunction.identified (word 1) functionBody
  expect "same anonymous closure" (identityProgram anonymous anonymous) (.inRight .word (.bool false))
  expect "same named identity" (identityProgram named named) (.inRight .word (.bool true))
  expect "different named identity"
    (identityProgram named (TaggedFunction.identified (word 2) functionBody)) (.inRight .word (.bool false))
  expect "anonymous left" (identityProgram anonymous named) (.inRight .word (.bool false))
  expect "anonymous right" (identityProgram named anonymous) (.inRight .word (.bool false))

end Tests.CoreTaggedFunction
end

section
-- leanmerge: from Solcore.Test.CoreWordMapping
/-! Fixed-catalog mapping helpers execute with the actual named-data definition,
including duplicate keys, shared mutable roots, and checkpoint resumption. -/

set_option autoImplicit false

namespace Tests.CoreWordMapping

open Solcore.Core

private def w (value : Nat) : Word := Word.ofNatModulo value
private def e (value : Nat) : Expr := .word (w value)
private def v (value : Nat) : Value := .word (w value)
private def entries : WordMapping.Entries := [(w 1, w 11), (w 2, w 22), (w 1, w 33)]

private def program (type : Ty) (body : Expr) : Program := {
  resultType := type
  body := body
  dataDefinitions := WordMapping.actualDefinitions
}

private def lookupProgram (key : Nat) : Program :=
  program (LanguageResult.resultType .word) (WordMapping.lookup (WordMapping.literal entries) (e key))

private def insertProgram (key value : Nat) : Program :=
  program (LanguageResult.resultType WordMapping.type)
    (WordMapping.insert (WordMapping.literal entries) (e key) (e value))

/-- Actual helper compilation produces the independent source insertion's
structural carrier and a finite runner result, for arbitrary finite lists. -/
example (words : WordMapping.Entries) (key value : Word) :
    ∃ output finalStore required,
      Solcore.SourceSemantics.CoreLowering.WordMapping.ValueRel
        (Solcore.SourceSemantics.CoreLowering.WordMapping.sourceEntries
          (WordMapping.insertEntries key value words)) output ∧
      ∀ fuel, required ≤ fuel →
        runStateful fuel (State.initial
          (WordMapping.insert (WordMapping.literal words) (.word key) (.word value))) =
          .done (.inRight .word output) finalStore :=
  Solcore.SourceSemantics.CoreLowering.WordMapping.insert_run_preserves
    (Solcore.SourceSemantics.CoreLowering.WordMapping.ValueRel.encode words)
    (Solcore.SourceSemantics.CoreLowering.WordMapping.insertEntries_source words key value)
    (WordMapping.literal_evaluates words [] []) .word .word

/-- The RHS replaces the root with two entries. Updating key 1 must preserve
its newly added key 2, which would disappear if an earlier root snapshot won. -/
private def latestRootProgram : Program := program (OptionalCell.cellType WordMapping.type)
  (.letE (OptionalCell.allocateInitialized WordMapping.type (WordMapping.literal [(w 1, w 10)]))
    (.letE (WordMapping.assign (.var 0) (LanguageResult.success (e 1))
      (.letE (.storeCell (.var 0) (.inRight .unit (WordMapping.literal [(w 1, w 20), (w 2, w 30)])))
        (LanguageResult.success (e 99))))
      (.loadCell (.var 1))))

/-- Reference, key, and RHS effects run in order: counter := 3; += 5; *= 2.
The key and value use the original environment after temporary binders. -/
private def orderProgram : Program :=
  program (.product (OptionalCell.cellType WordMapping.type) .word)
    (.letE (.newCell .word (e 0))
      (.letE (OptionalCell.allocateInitialized WordMapping.type (WordMapping.literal [(w 1, w 0)]))
        (.letE (WordMapping.assign
          (.letE (.storeCell (.var 1) (e 3)) (.var 1))
          (.letE (.storeCell (.var 1) (.binary .wordAdd (.loadCell (.var 1)) (e 5)))
            (LanguageResult.success (e 1)))
          (.letE (.storeCell (.var 1) (.binary .wordMul (.loadCell (.var 1)) (e 2)))
            (LanguageResult.success (.loadCell (.var 2)))))
          (.pair (.loadCell (.var 1)) (.loadCell (.var 2))))))

private def keyFailureProgram : Program := program (LanguageResult.resultType .unit)
  (.letE (OptionalCell.allocateInitialized WordMapping.type (WordMapping.literal [(w 1, w 10)]))
    (WordMapping.assign (.var 0) (LanguageResult.failure .word (e 17))
      (.letE (.storeCell (.var 0) (.inRight .unit WordMapping.empty))
        (LanguageResult.success (e 99)))))

private def rhsFailureProgram : Program := program (LanguageResult.resultType .unit)
  (.letE (OptionalCell.allocateInitialized WordMapping.type (WordMapping.literal [(w 1, w 10)]))
    (WordMapping.assign (.var 0) (LanguageResult.success (e 1))
      (.letE (.storeCell (.var 0) (.inRight .unit (WordMapping.literal [(w 2, w 30)])))
        (LanguageResult.failure .word (e 18)))))

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def completed (program : Program) (expected : Value) : IO Store := do
  assertTrue program.check "mapping prototype failed its registered Core checker"
  match program.runStateful 6000 with
  | .done actual store =>
      assertTrue (actual == expected) s!"mapping result mismatch: {reprStr actual}"
      return store
  | other => throw (IO.userError s!"mapping prototype did not complete: {reprStr other}")

def run : IO Unit := do
  assertTrue WordMapping.actualDefinitions.isWellFormed "mapping catalog must be valid"
  assertTrue (!( { (lookupProgram 1) with dataDefinitions := [] } : Program).check)
    "named mapping data must not type-check without its actual catalog"
  assertTrue (!( { (lookupProgram 1) with dataDefinitions := [{constructorPayloadTypes := [.unit]}] } : Program).check)
    "same nominal index with wrong payloads must be rejected"

  let lookupStore ← completed (lookupProgram 1) (.inRight .word (v 11))
  assertTrue (lookupStore == WordMapping.installedStore [] WordMapping.lookupParameter .word
    WordMapping.lookupBody (.pair (WordMapping.encode entries) (v 1)) [])
    "lookup must install exactly its own shared self cell"
  discard <| completed (lookupProgram 7) (.inRight .word (v 0))
  discard <| completed (program (LanguageResult.resultType .word)
    (WordMapping.lookup WordMapping.empty (e 1))) (.inRight .word (v 0))

  let updated := [(w 1, w 99), (w 2, w 22), (w 1, w 33)]
  let updatedStore ← completed (insertProgram 1 99) (.inRight .word (WordMapping.encode updated))
  assertTrue (updatedStore.length == 1) "one helper invocation allocates one self cell"
  discard <| completed (insertProgram 3 44)
    (.inRight .word (WordMapping.encode (entries ++ [(w 3, w 44)])))
  discard <| completed (program (LanguageResult.resultType WordMapping.type)
    (WordMapping.insert WordMapping.empty (e 7) (e 8)))
      (.inRight .word (WordMapping.encode [(w 7, w 8)]))
  let maxWord := Word.ofNatModulo (wordModulus - 1)
  discard <| completed (program (LanguageResult.resultType .word)
    (WordMapping.lookup (WordMapping.literal [(maxWord, w 42), (w 0, w 13)]) (.word maxWord)))
      (.inRight .word (v 42))

  let latest := WordMapping.encode [(w 1, w 99), (w 2, w 30)]
  let latestStore ← completed latestRootProgram (.inRight .unit latest)
  assertTrue (latestStore[0]? == some (.inRight .unit latest) && latestStore.length == 2)
    "writeback must preserve the RHS's key 2 and write through the original root reference"
  let ordered := WordMapping.encode [(w 1, w 16)]
  let orderedStore ← completed orderProgram (.pair (.inRight .unit ordered) (v 16))
  assertTrue (orderedStore[0]? == some (v 16) &&
    orderedStore[1]? == some (.inRight .unit ordered) && orderedStore.length == 3)
    "reference/key/RHS must run once, in order, through the shared store"

  let keyFailedStore ← completed keyFailureProgram (.inLeft .unit (v 17))
  assertTrue (keyFailedStore == [.inRight .unit (WordMapping.encode [(w 1, w 10)])])
    "key failure must skip the RHS and helper allocation"
  let rhsFailedStore ← completed rhsFailureProgram (.inLeft .unit (v 18))
  assertTrue (rhsFailedStore == [.inRight .unit (WordMapping.encode [(w 2, w 30)])])
    "RHS failure must preserve its effects and skip the pending mapping insertion"

  match orderProgram.runStateful 30 with
  | .outOfFuel checkpoint =>
      assertTrue (runStateful 6000 checkpoint == orderProgram.runStateful 6030)
        "resuming a mapping checkpoint must preserve shared references and final stores"
  | other => throw (IO.userError s!"expected actual mapping suspension, got {reprStr other}")

end Tests.CoreWordMapping
end
