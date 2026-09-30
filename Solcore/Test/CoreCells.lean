import Solcore.Core.Check
import Solcore.Core.Machine
import Solcore.Core.Safety

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
