import Solcore.Core.Check
import Solcore.Core.Machine

/-! Executable regressions for program-local named algebraic data. -/

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
  let unusedInvalidTable : Program := {
    resultType := .bool
    body := .bool true
    dataDefinitions := functionPayloadDefinitions
  }
  assertTrue (!functionPayloadDefinitions.isWellFormed)
    "function-valued constructor payloads must be rejected recursively"
  assertTrue (!unusedInvalidTable.check)
    "the complete definition table must be checked even when it is unused"
  assertTrue (unusedInvalidTable.run 1 == .done (.bool true))
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

  let nestedInvalidDefinitions : DataEnvironment := [
    {
      constructorPayloadTypes := [
        .product .unit (.sum .bool (.function .unit .unit))
      ]
    }
  ]
  assertTrue (!nestedInvalidDefinitions.isWellFormed)
    "function types nested below products and sums must invalidate the table"

  let unknownReferenceDefinitions : DataEnvironment := [
    { constructorPayloadTypes := [.namedData (dataType 4)] }
  ]
  assertTrue (!unknownReferenceDefinitions.isWellFormed)
    "every named type referenced by a constructor payload must exist in the table"

  let namedCellContentsDefinitions : DataEnvironment := [
    { constructorPayloadTypes := [.cell (.namedData (dataType 0))] }
  ]
  assertTrue (!namedCellContentsDefinitions.isWellFormed)
    "a constructor may carry a cell reference only when its element is a cell payload"

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
      { constructorPayloadTypes := [.function .unit .unit] }
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
    { constructorPayloadTypes := [.function .unit .unit] }
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
    (.invalidDefinitionPayload 0 0 (.function .unit .unit))

  let nestedInvalidType : Ty :=
    .product .unit (.sum .bool (.function .unit .unit))
  let multipleInvalidDefinitions : DataEnvironment := [
    { constructorPayloadTypes := [.unit] },
    { constructorPayloadTypes := [.bool, nestedInvalidType] },
    { constructorPayloadTypes := [.function .word .word] }
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
  assertTrue (!storedNamedData.check)
    "named-data values must remain inadmissible as cell contents"

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
  testUncheckedMachineFaults
  testNamedDataWeakening

end Tests
