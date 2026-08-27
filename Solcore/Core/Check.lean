import Solcore.Core.Typing

set_option autoImplicit false

namespace Solcore.Core

inductive CheckPathStep where
  | pairLeft
  | pairRight
  | firstOperand
  | secondOperand
  | lambdaBody
  | applyFunction
  | applyArgument
  | inLeftPayload
  | inRightPayload
  | caseScrutinee
  | caseLeftBranch
  | caseRightBranch
  | newCellInitializer
  | loadCellReference
  | storeCellReference
  | storeCellValue
  | unaryOperand
  | binaryLeft
  | binaryRight
  | letValue
  | letBody
  | ifCondition
  | ifThen
  | ifElse
  deriving Repr, BEq, DecidableEq

abbrev CheckPath := List CheckPathStep

def CheckPath.child (path : CheckPath) (step : CheckPathStep) : CheckPath :=
  path ++ [step]

inductive CheckErrorCode where
  | unboundVariable
  | expectedBool
  | expectedProduct
  | expectedFunction
  | functionArgumentTypeMismatch
  | lambdaResultTypeMismatch
  | expectedSum
  | caseBranchTypeMismatch
  | invalidCellPayload
  | cellInitializerTypeMismatch
  | expectedCell
  | cellValueTypeMismatch
  | primitiveOperandTypeMismatch
  | branchTypeMismatch
  | declaredResultTypeMismatch
  deriving Repr, BEq, DecidableEq

def CheckErrorCode.name : CheckErrorCode → String
  | .unboundVariable => "core.check.unbound-variable"
  | .expectedBool => "core.check.expected-bool"
  | .expectedProduct => "core.check.expected-product"
  | .expectedFunction => "core.check.expected-function"
  | .functionArgumentTypeMismatch =>
      "core.check.function-argument-type-mismatch"
  | .lambdaResultTypeMismatch => "core.check.lambda-result-type-mismatch"
  | .expectedSum => "core.check.expected-sum"
  | .caseBranchTypeMismatch => "core.check.case-branch-type-mismatch"
  | .invalidCellPayload => "core.check.invalid-cell-payload"
  | .cellInitializerTypeMismatch =>
      "core.check.cell-initializer-type-mismatch"
  | .expectedCell => "core.check.expected-cell"
  | .cellValueTypeMismatch => "core.check.cell-value-type-mismatch"
  | .primitiveOperandTypeMismatch =>
      "core.check.primitive-operand-type-mismatch"
  | .branchTypeMismatch => "core.check.branch-type-mismatch"
  | .declaredResultTypeMismatch => "core.check.declared-result-type-mismatch"

inductive CheckErrorData where
  | unboundVariable (index contextSize : Nat)
  | expectedBool (actual : Ty)
  | expectedProduct (actual : Ty)
  | expectedFunction (actual : Ty)
  | functionArgumentTypeMismatch (expected actual : Ty)
  | lambdaResultTypeMismatch (declared actual : Ty)
  | expectedSum (actual : Ty)
  | caseBranchTypeMismatch (leftType rightType : Ty)
  | invalidCellPayload (actual : Ty)
  | cellInitializerTypeMismatch (expected actual : Ty)
  | expectedCell (actual : Ty)
  | cellValueTypeMismatch (expected actual : Ty)
  | primitiveOperandTypeMismatch (expected actual : Ty)
  | branchTypeMismatch (thenType elseType : Ty)
  | declaredResultTypeMismatch (declaredType inferredType : Ty)
  deriving Repr, BEq, DecidableEq

def CheckErrorData.code : CheckErrorData → CheckErrorCode
  | .unboundVariable .. => .unboundVariable
  | .expectedBool .. => .expectedBool
  | .expectedProduct .. => .expectedProduct
  | .expectedFunction .. => .expectedFunction
  | .functionArgumentTypeMismatch .. => .functionArgumentTypeMismatch
  | .lambdaResultTypeMismatch .. => .lambdaResultTypeMismatch
  | .expectedSum .. => .expectedSum
  | .caseBranchTypeMismatch .. => .caseBranchTypeMismatch
  | .invalidCellPayload .. => .invalidCellPayload
  | .cellInitializerTypeMismatch .. => .cellInitializerTypeMismatch
  | .expectedCell .. => .expectedCell
  | .cellValueTypeMismatch .. => .cellValueTypeMismatch
  | .primitiveOperandTypeMismatch .. => .primitiveOperandTypeMismatch
  | .branchTypeMismatch .. => .branchTypeMismatch
  | .declaredResultTypeMismatch .. => .declaredResultTypeMismatch

structure CheckError where
  path : CheckPath
  data : CheckErrorData
  deriving Repr, BEq, DecidableEq

def CheckError.code (error : CheckError) : CheckErrorCode :=
  error.data.code

def CheckError.codeName (error : CheckError) : String :=
  error.code.name

def inferDetailed (context : Context) (path : CheckPath := []) : Expr → Except CheckError Ty
  | .unit => .ok .unit
  | .bool _ => .ok .bool
  | .word _ => .ok .word
  | .var index =>
      match context[index]? with
      | some type => .ok type
      | none =>
          .error {
            path
            data := .unboundVariable index context.length
          }
  | .pair left right =>
      match inferDetailed context (path.child .pairLeft) left with
      | .error error => .error error
      | .ok leftType =>
          match inferDetailed context (path.child .pairRight) right with
          | .error error => .error error
          | .ok rightType => .ok (.product leftType rightType)
  | .first operand =>
      let operandPath := path.child .firstOperand
      match inferDetailed context operandPath operand with
      | .error error => .error error
      | .ok (.product leftType _) => .ok leftType
      | .ok actualType =>
          .error {
            path := operandPath
            data := .expectedProduct actualType
          }
  | .second operand =>
      let operandPath := path.child .secondOperand
      match inferDetailed context operandPath operand with
      | .error error => .error error
      | .ok (.product _ rightType) => .ok rightType
      | .ok actualType =>
          .error {
            path := operandPath
            data := .expectedProduct actualType
          }
  | .lambda parameterType resultType body =>
      let bodyPath := path.child .lambdaBody
      match inferDetailed (parameterType :: context) bodyPath body with
      | .error error => .error error
      | .ok actualType =>
          if actualType = resultType then
            .ok (.function parameterType resultType)
          else
            .error {
              path := bodyPath
              data := .lambdaResultTypeMismatch resultType actualType
            }
  | .apply function argument =>
      let functionPath := path.child .applyFunction
      match inferDetailed context functionPath function with
      | .error error => .error error
      | .ok (.function parameterType resultType) =>
          let argumentPath := path.child .applyArgument
          match inferDetailed context argumentPath argument with
          | .error error => .error error
          | .ok actualType =>
              if actualType = parameterType then
                .ok resultType
              else
                .error {
                  path := argumentPath
                  data := .functionArgumentTypeMismatch parameterType actualType
                }
      | .ok actualType =>
          .error {
            path := functionPath
            data := .expectedFunction actualType
          }
  | .inLeft rightType payload =>
      match inferDetailed context (path.child .inLeftPayload) payload with
      | .error error => .error error
      | .ok leftType => .ok (.sum leftType rightType)
  | .inRight leftType payload =>
      match inferDetailed context (path.child .inRightPayload) payload with
      | .error error => .error error
      | .ok rightType => .ok (.sum leftType rightType)
  | .caseE scrutinee leftBranch rightBranch =>
      let scrutineePath := path.child .caseScrutinee
      match inferDetailed context scrutineePath scrutinee with
      | .error error => .error error
      | .ok (.sum leftType rightType) =>
          match
              inferDetailed
                (leftType :: context)
                (path.child .caseLeftBranch)
                leftBranch with
          | .error error => .error error
          | .ok leftResultType =>
              match
                  inferDetailed
                    (rightType :: context)
                    (path.child .caseRightBranch)
                    rightBranch with
              | .error error => .error error
              | .ok rightResultType =>
                  if leftResultType = rightResultType then
                    .ok leftResultType
                  else
                    .error {
                      path := path.child .caseRightBranch
                      data := .caseBranchTypeMismatch
                        leftResultType
                        rightResultType
                    }
      | .ok actualType =>
          .error {
            path := scrutineePath
            data := .expectedSum actualType
          }
  | .newCell elementType initializer =>
      let initializerPath := path.child .newCellInitializer
      match inferDetailed context initializerPath initializer with
      | .error error => .error error
      | .ok actualType =>
          if actualType = elementType then
            if elementType.isCellPayload then
              .ok (.cell elementType)
            else
              .error {
                path
                data := .invalidCellPayload elementType
              }
          else
            .error {
              path := initializerPath
              data := .cellInitializerTypeMismatch elementType actualType
            }
  | .loadCell reference =>
      let referencePath := path.child .loadCellReference
      match inferDetailed context referencePath reference with
      | .error error => .error error
      | .ok (.cell elementType) =>
          if elementType.isCellPayload then
            .ok elementType
          else
            .error {
              path := referencePath
              data := .invalidCellPayload elementType
            }
      | .ok actualType =>
          .error {
            path := referencePath
            data := .expectedCell actualType
          }
  | .storeCell reference value =>
      let referencePath := path.child .storeCellReference
      match inferDetailed context referencePath reference with
      | .error error => .error error
      | .ok (.cell elementType) =>
          if elementType.isCellPayload then
            let valuePath := path.child .storeCellValue
            match inferDetailed context valuePath value with
            | .error error => .error error
            | .ok actualType =>
                if actualType = elementType then
                  .ok .unit
                else
                  .error {
                    path := valuePath
                    data := .cellValueTypeMismatch elementType actualType
                  }
          else
            .error {
              path := referencePath
              data := .invalidCellPayload elementType
            }
      | .ok actualType =>
          .error {
            path := referencePath
            data := .expectedCell actualType
          }
  | .unary op operand =>
      let operandPath := path.child .unaryOperand
      match inferDetailed context operandPath operand with
      | .error error => .error error
      | .ok operandType =>
          if operandType = op.operandType then
            .ok op.resultType
          else
            .error {
              path := operandPath
              data := .primitiveOperandTypeMismatch op.operandType operandType
            }
  | .binary op left right =>
      let leftPath := path.child .binaryLeft
      match inferDetailed context leftPath left with
      | .error error => .error error
      | .ok leftType =>
          if leftType = op.leftType then
            let rightPath := path.child .binaryRight
            match inferDetailed context rightPath right with
            | .error error => .error error
            | .ok rightType =>
                if rightType = op.rightType then
                  .ok op.resultType
                else
                  .error {
                    path := rightPath
                    data := .primitiveOperandTypeMismatch op.rightType rightType
                  }
          else
            .error {
              path := leftPath
              data := .primitiveOperandTypeMismatch op.leftType leftType
            }
  | .letE value body =>
      match inferDetailed context (path.child .letValue) value with
      | .error error => .error error
      | .ok valueType =>
          inferDetailed (valueType :: context) (path.child .letBody) body
  | .ifE condition thenBranch elseBranch =>
      match inferDetailed context (path.child .ifCondition) condition with
      | .error error => .error error
      | .ok conditionType =>
          if conditionType = .bool then
            match inferDetailed context (path.child .ifThen) thenBranch with
            | .error error => .error error
            | .ok thenType =>
                match inferDetailed context (path.child .ifElse) elseBranch with
                | .error error => .error error
                | .ok elseType =>
                    if thenType = elseType then
                      .ok thenType
                    else
                      .error {
                        path := path.child .ifElse
                        data := .branchTypeMismatch thenType elseType
                      }
          else
            .error {
              path := path.child .ifCondition
              data := .expectedBool conditionType
            }

theorem inferDetailed_toOption
    (context : Context) (path : CheckPath) (expr : Expr) :
    (inferDetailed context path expr).toOption = infer? context expr := by
  induction expr generalizing context path with
  | unit | bool | word => rfl
  | var index =>
      cases lookup : context[index]? <;>
        simp [inferDetailed, infer?, Except.toOption, lookup]
  | pair left right leftIH rightIH =>
      cases leftDetailed :
          inferDetailed context (path.child .pairLeft) left with
      | error error =>
          have leftNotInferred : infer? context left = none := by
            simpa [leftDetailed, Except.toOption] using
              (leftIH context (path.child .pairLeft)).symm
          simp [
            inferDetailed,
            infer?,
            Except.toOption,
            leftDetailed,
            leftNotInferred
          ]
      | ok leftType =>
          have leftInferred : infer? context left = some leftType := by
            simpa [leftDetailed, Except.toOption] using
              (leftIH context (path.child .pairLeft)).symm
          cases rightDetailed :
              inferDetailed context (path.child .pairRight) right with
          | error error =>
              have rightNotInferred : infer? context right = none := by
                simpa [rightDetailed, Except.toOption] using
                  (rightIH context (path.child .pairRight)).symm
              simp [
                inferDetailed,
                infer?,
                Except.toOption,
                leftDetailed,
                leftInferred,
                rightDetailed,
                rightNotInferred
              ]
          | ok rightType =>
              have rightInferred : infer? context right = some rightType := by
                simpa [rightDetailed, Except.toOption] using
                  (rightIH context (path.child .pairRight)).symm
              simp [
                inferDetailed,
                infer?,
                Except.toOption,
                leftDetailed,
                leftInferred,
                rightDetailed,
                rightInferred
              ]
  | first operand operandIH =>
      cases operandDetailed :
          inferDetailed context (path.child .firstOperand) operand with
      | error error =>
          have operandNotInferred : infer? context operand = none := by
            simpa [operandDetailed, Except.toOption] using
              (operandIH context (path.child .firstOperand)).symm
          simp [
            inferDetailed,
            infer?,
            Except.toOption,
            operandDetailed,
            operandNotInferred
          ]
      | ok operandType =>
          have operandInferred : infer? context operand = some operandType := by
            simpa [operandDetailed, Except.toOption] using
              (operandIH context (path.child .firstOperand)).symm
          cases operandType <;>
            simp [
              inferDetailed,
              infer?,
              Except.toOption,
              operandDetailed,
              operandInferred
            ]
  | second operand operandIH =>
      cases operandDetailed :
          inferDetailed context (path.child .secondOperand) operand with
      | error error =>
          have operandNotInferred : infer? context operand = none := by
            simpa [operandDetailed, Except.toOption] using
              (operandIH context (path.child .secondOperand)).symm
          simp [
            inferDetailed,
            infer?,
            Except.toOption,
            operandDetailed,
            operandNotInferred
          ]
      | ok operandType =>
          have operandInferred : infer? context operand = some operandType := by
            simpa [operandDetailed, Except.toOption] using
              (operandIH context (path.child .secondOperand)).symm
          cases operandType <;>
            simp [
              inferDetailed,
              infer?,
              Except.toOption,
              operandDetailed,
              operandInferred
            ]
  | lambda parameterType resultType body bodyIH =>
      cases bodyDetailed :
          inferDetailed
            (parameterType :: context)
            (path.child .lambdaBody)
            body with
      | error error =>
          have bodyNotInferred :
              infer? (parameterType :: context) body = none := by
            simpa [bodyDetailed, Except.toOption] using
              (bodyIH (parameterType :: context) (path.child .lambdaBody)).symm
          simp [
            inferDetailed,
            infer?,
            Except.toOption,
            bodyDetailed,
            bodyNotInferred
          ]
      | ok bodyType =>
          have bodyInferred :
              infer? (parameterType :: context) body = some bodyType := by
            simpa [bodyDetailed, Except.toOption] using
              (bodyIH (parameterType :: context) (path.child .lambdaBody)).symm
          by_cases matchingResult : bodyType = resultType
          · subst bodyType
            simp [
              inferDetailed,
              infer?,
              Except.toOption,
              bodyDetailed,
              bodyInferred
            ]
          · simp [
              inferDetailed,
              infer?,
              Except.toOption,
              bodyDetailed,
              bodyInferred,
              matchingResult
            ]
  | apply function argument functionIH argumentIH =>
      cases functionDetailed :
          inferDetailed context (path.child .applyFunction) function with
      | error error =>
          have functionNotInferred : infer? context function = none := by
            simpa [functionDetailed, Except.toOption] using
              (functionIH context (path.child .applyFunction)).symm
          simp [
            inferDetailed,
            infer?,
            Except.toOption,
            functionDetailed,
            functionNotInferred
          ]
      | ok functionType =>
          have functionInferred : infer? context function = some functionType := by
            simpa [functionDetailed, Except.toOption] using
              (functionIH context (path.child .applyFunction)).symm
          cases functionType with
          | unit =>
              simp [
                inferDetailed,
                infer?,
                Except.toOption,
                functionDetailed,
                functionInferred
              ]
          | bool =>
              simp [
                inferDetailed,
                infer?,
                Except.toOption,
                functionDetailed,
                functionInferred
              ]
          | word =>
              simp [
                inferDetailed,
                infer?,
                Except.toOption,
                functionDetailed,
                functionInferred
              ]
          | product leftType rightType =>
              simp [
                inferDetailed,
                infer?,
                Except.toOption,
                functionDetailed,
                functionInferred
              ]
          | function parameterType resultType =>
              cases argumentDetailed :
                  inferDetailed context (path.child .applyArgument) argument with
              | error error =>
                  have argumentNotInferred : infer? context argument = none := by
                    simpa [argumentDetailed, Except.toOption] using
                      (argumentIH context (path.child .applyArgument)).symm
                  simp [
                    inferDetailed,
                    infer?,
                    Except.toOption,
                    functionDetailed,
                    functionInferred,
                    argumentDetailed,
                    argumentNotInferred
                  ]
              | ok argumentType =>
                  have argumentInferred :
                      infer? context argument = some argumentType := by
                    simpa [argumentDetailed, Except.toOption] using
                      (argumentIH context (path.child .applyArgument)).symm
                  by_cases matchingArgument : argumentType = parameterType
                  · subst argumentType
                    simp [
                      inferDetailed,
                      infer?,
                      Except.toOption,
                      functionDetailed,
                      functionInferred,
                      argumentDetailed,
                      argumentInferred
                    ]
                  · simp [
                      inferDetailed,
                      infer?,
                      Except.toOption,
                      functionDetailed,
                      functionInferred,
                      argumentDetailed,
                      argumentInferred,
                      matchingArgument
                    ]
          | sum leftType rightType =>
              simp [
                inferDetailed,
                infer?,
                Except.toOption,
                functionDetailed,
                functionInferred
              ]
          | cell elementType =>
              simp [
                inferDetailed,
                infer?,
                Except.toOption,
                functionDetailed,
                functionInferred
              ]
  | inLeft rightType payload payloadIH =>
      cases payloadDetailed :
          inferDetailed context (path.child .inLeftPayload) payload with
      | error error =>
          have payloadNotInferred : infer? context payload = none := by
            simpa [payloadDetailed, Except.toOption] using
              (payloadIH context (path.child .inLeftPayload)).symm
          simp [
            inferDetailed,
            infer?,
            Except.toOption,
            payloadDetailed,
            payloadNotInferred
          ]
      | ok leftType =>
          have payloadInferred : infer? context payload = some leftType := by
            simpa [payloadDetailed, Except.toOption] using
              (payloadIH context (path.child .inLeftPayload)).symm
          simp [
            inferDetailed,
            infer?,
            Except.toOption,
            payloadDetailed,
            payloadInferred
          ]
  | inRight leftType payload payloadIH =>
      cases payloadDetailed :
          inferDetailed context (path.child .inRightPayload) payload with
      | error error =>
          have payloadNotInferred : infer? context payload = none := by
            simpa [payloadDetailed, Except.toOption] using
              (payloadIH context (path.child .inRightPayload)).symm
          simp [
            inferDetailed,
            infer?,
            Except.toOption,
            payloadDetailed,
            payloadNotInferred
          ]
      | ok rightType =>
          have payloadInferred : infer? context payload = some rightType := by
            simpa [payloadDetailed, Except.toOption] using
              (payloadIH context (path.child .inRightPayload)).symm
          simp [
            inferDetailed,
            infer?,
            Except.toOption,
            payloadDetailed,
            payloadInferred
          ]
  | caseE scrutinee leftBranch rightBranch scrutineeIH leftIH rightIH =>
      cases scrutineeDetailed :
          inferDetailed context (path.child .caseScrutinee) scrutinee with
      | error error =>
          have scrutineeNotInferred : infer? context scrutinee = none := by
            simpa [scrutineeDetailed, Except.toOption] using
              (scrutineeIH context (path.child .caseScrutinee)).symm
          simp [
            inferDetailed,
            infer?,
            Except.toOption,
            scrutineeDetailed,
            scrutineeNotInferred
          ]
      | ok scrutineeType =>
          have scrutineeInferred :
              infer? context scrutinee = some scrutineeType := by
            simpa [scrutineeDetailed, Except.toOption] using
              (scrutineeIH context (path.child .caseScrutinee)).symm
          cases scrutineeType with
          | unit =>
              simp [
                inferDetailed,
                infer?,
                Except.toOption,
                scrutineeDetailed,
                scrutineeInferred
              ]
          | bool =>
              simp [
                inferDetailed,
                infer?,
                Except.toOption,
                scrutineeDetailed,
                scrutineeInferred
              ]
          | word =>
              simp [
                inferDetailed,
                infer?,
                Except.toOption,
                scrutineeDetailed,
                scrutineeInferred
              ]
          | product firstType secondType =>
              simp [
                inferDetailed,
                infer?,
                Except.toOption,
                scrutineeDetailed,
                scrutineeInferred
              ]
          | function parameterType resultType =>
              simp [
                inferDetailed,
                infer?,
                Except.toOption,
                scrutineeDetailed,
                scrutineeInferred
              ]
          | sum leftType rightType =>
              cases leftDetailed :
                  inferDetailed
                    (leftType :: context)
                    (path.child .caseLeftBranch)
                    leftBranch with
              | error error =>
                  have leftNotInferred :
                      infer? (leftType :: context) leftBranch = none := by
                    simpa [leftDetailed, Except.toOption] using
                      (leftIH
                        (leftType :: context)
                        (path.child .caseLeftBranch)).symm
                  simp [
                    inferDetailed,
                    infer?,
                    Except.toOption,
                    scrutineeDetailed,
                    scrutineeInferred,
                    leftDetailed,
                    leftNotInferred
                  ]
              | ok leftResultType =>
                  have leftInferred :
                      infer? (leftType :: context) leftBranch =
                        some leftResultType := by
                    simpa [leftDetailed, Except.toOption] using
                      (leftIH
                        (leftType :: context)
                        (path.child .caseLeftBranch)).symm
                  cases rightDetailed :
                      inferDetailed
                        (rightType :: context)
                        (path.child .caseRightBranch)
                        rightBranch with
                  | error error =>
                      have rightNotInferred :
                          infer? (rightType :: context) rightBranch = none := by
                        simpa [rightDetailed, Except.toOption] using
                          (rightIH
                            (rightType :: context)
                            (path.child .caseRightBranch)).symm
                      simp [
                        inferDetailed,
                        infer?,
                        Except.toOption,
                        scrutineeDetailed,
                        scrutineeInferred,
                        leftDetailed,
                        leftInferred,
                        rightDetailed,
                        rightNotInferred
                      ]
                  | ok rightResultType =>
                      have rightInferred :
                          infer? (rightType :: context) rightBranch =
                            some rightResultType := by
                        simpa [rightDetailed, Except.toOption] using
                          (rightIH
                            (rightType :: context)
                            (path.child .caseRightBranch)).symm
                      by_cases equalTypes : leftResultType = rightResultType
                      · subst rightResultType
                        simp [
                          inferDetailed,
                          infer?,
                          Except.toOption,
                          scrutineeDetailed,
                          scrutineeInferred,
                          leftDetailed,
                          leftInferred,
                          rightDetailed,
                          rightInferred
                        ]
                      · simp [
                          inferDetailed,
                          infer?,
                          Except.toOption,
                          scrutineeDetailed,
                          scrutineeInferred,
                          leftDetailed,
                          leftInferred,
                          rightDetailed,
                          rightInferred,
                          equalTypes
                        ]
          | cell elementType =>
              simp [
                inferDetailed,
                infer?,
                Except.toOption,
                scrutineeDetailed,
                scrutineeInferred
              ]
  | newCell elementType initializer initializerIH =>
      cases initializerDetailed :
          inferDetailed context (path.child .newCellInitializer) initializer with
      | error error =>
          have initializerNotInferred : infer? context initializer = none := by
            simpa [initializerDetailed, Except.toOption] using
              (initializerIH context (path.child .newCellInitializer)).symm
          simp [
            inferDetailed,
            infer?,
            Except.toOption,
            initializerDetailed,
            initializerNotInferred
          ]
      | ok initializerType =>
          have initializerInferred :
              infer? context initializer = some initializerType := by
            simpa [initializerDetailed, Except.toOption] using
              (initializerIH context (path.child .newCellInitializer)).symm
          by_cases matchingType : initializerType = elementType
          · subst initializerType
            by_cases payloadAccepted : elementType.isCellPayload = true
            · simp [
                inferDetailed,
                infer?,
                Except.toOption,
                initializerDetailed,
                initializerInferred,
                payloadAccepted
              ]
            · simp [
                inferDetailed,
                infer?,
                Except.toOption,
                initializerDetailed,
                initializerInferred,
                payloadAccepted
              ]
          · simp [
              inferDetailed,
              infer?,
              Except.toOption,
              initializerDetailed,
              initializerInferred,
              matchingType
            ]
  | loadCell reference referenceIH =>
      cases referenceDetailed :
          inferDetailed context (path.child .loadCellReference) reference with
      | error error =>
          have referenceNotInferred : infer? context reference = none := by
            simpa [referenceDetailed, Except.toOption] using
              (referenceIH context (path.child .loadCellReference)).symm
          simp [
            inferDetailed,
            infer?,
            Except.toOption,
            referenceDetailed,
            referenceNotInferred
          ]
      | ok referenceType =>
          have referenceInferred : infer? context reference = some referenceType := by
            simpa [referenceDetailed, Except.toOption] using
              (referenceIH context (path.child .loadCellReference)).symm
          cases referenceType with
          | unit | bool | word | product | function | sum =>
              simp [
                inferDetailed,
                infer?,
                Except.toOption,
                referenceDetailed,
                referenceInferred
              ]
          | cell elementType =>
              by_cases payloadAccepted : elementType.isCellPayload = true
              · simp [
                  inferDetailed,
                  infer?,
                  Except.toOption,
                  referenceDetailed,
                  referenceInferred,
                  payloadAccepted
                ]
              · simp [
                  inferDetailed,
                  infer?,
                  Except.toOption,
                  referenceDetailed,
                  referenceInferred,
                  payloadAccepted
                ]
  | storeCell reference value referenceIH valueIH =>
      cases referenceDetailed :
          inferDetailed context (path.child .storeCellReference) reference with
      | error error =>
          have referenceNotInferred : infer? context reference = none := by
            simpa [referenceDetailed, Except.toOption] using
              (referenceIH context (path.child .storeCellReference)).symm
          simp [
            inferDetailed,
            infer?,
            Except.toOption,
            referenceDetailed,
            referenceNotInferred
          ]
      | ok referenceType =>
          have referenceInferred : infer? context reference = some referenceType := by
            simpa [referenceDetailed, Except.toOption] using
              (referenceIH context (path.child .storeCellReference)).symm
          cases referenceType with
          | unit | bool | word | product | function | sum =>
              simp [
                inferDetailed,
                infer?,
                Except.toOption,
                referenceDetailed,
                referenceInferred
              ]
          | cell elementType =>
              by_cases payloadAccepted : elementType.isCellPayload = true
              · cases valueDetailed :
                    inferDetailed context (path.child .storeCellValue) value with
                | error error =>
                    have valueNotInferred : infer? context value = none := by
                      simpa [valueDetailed, Except.toOption] using
                        (valueIH context (path.child .storeCellValue)).symm
                    simp [
                      inferDetailed,
                      infer?,
                      Except.toOption,
                      referenceDetailed,
                      referenceInferred,
                      payloadAccepted,
                      valueDetailed,
                      valueNotInferred
                    ]
                | ok valueType =>
                    have valueInferred : infer? context value = some valueType := by
                      simpa [valueDetailed, Except.toOption] using
                        (valueIH context (path.child .storeCellValue)).symm
                    by_cases matchingType : valueType = elementType
                    · subst valueType
                      simp [
                        inferDetailed,
                        infer?,
                        Except.toOption,
                        referenceDetailed,
                        referenceInferred,
                        payloadAccepted,
                        valueDetailed,
                        valueInferred
                      ]
                    · simp [
                        inferDetailed,
                        infer?,
                        Except.toOption,
                        referenceDetailed,
                        referenceInferred,
                        payloadAccepted,
                        valueDetailed,
                        valueInferred,
                        matchingType
                      ]
              · simp [
                  inferDetailed,
                  infer?,
                  Except.toOption,
                  referenceDetailed,
                  referenceInferred,
                  payloadAccepted
                ]
  | unary op operand operandIH =>
      cases operandDetailed :
          inferDetailed context (path.child .unaryOperand) operand with
      | error error =>
          have operandNotInferred : infer? context operand = none := by
            simpa [operandDetailed, Except.toOption] using
              (operandIH context (path.child .unaryOperand)).symm
          simp [
            inferDetailed,
            infer?,
            Except.toOption,
            operandDetailed,
            operandNotInferred
          ]
      | ok operandType =>
          have operandInferred : infer? context operand = some operandType := by
            simpa [operandDetailed, Except.toOption] using
              (operandIH context (path.child .unaryOperand)).symm
          by_cases matchingType : operandType = op.operandType
          · subst operandType
            simp [
              inferDetailed,
              infer?,
              Except.toOption,
              operandDetailed,
              operandInferred
            ]
          · simp [
              inferDetailed,
              infer?,
              Except.toOption,
              operandDetailed,
              operandInferred,
              matchingType
            ]
  | binary op left right leftIH rightIH =>
      cases leftDetailed :
          inferDetailed context (path.child .binaryLeft) left with
      | error error =>
          have leftNotInferred : infer? context left = none := by
            simpa [leftDetailed, Except.toOption] using
              (leftIH context (path.child .binaryLeft)).symm
          simp [
            inferDetailed,
            infer?,
            Except.toOption,
            leftDetailed,
            leftNotInferred
          ]
      | ok leftType =>
          have leftInferred : infer? context left = some leftType := by
            simpa [leftDetailed, Except.toOption] using
              (leftIH context (path.child .binaryLeft)).symm
          by_cases matchingLeft : leftType = op.leftType
          · subst leftType
            cases rightDetailed :
                inferDetailed context (path.child .binaryRight) right with
            | error error =>
                have rightNotInferred : infer? context right = none := by
                  simpa [rightDetailed, Except.toOption] using
                    (rightIH context (path.child .binaryRight)).symm
                simp [
                  inferDetailed,
                  infer?,
                  Except.toOption,
                  leftDetailed,
                  leftInferred,
                  rightDetailed,
                  rightNotInferred
                ]
            | ok rightType =>
                have rightInferred : infer? context right = some rightType := by
                  simpa [rightDetailed, Except.toOption] using
                    (rightIH context (path.child .binaryRight)).symm
                by_cases matchingRight : rightType = op.rightType
                · subst rightType
                  simp [
                    inferDetailed,
                    infer?,
                    Except.toOption,
                    leftDetailed,
                    leftInferred,
                    rightDetailed,
                    rightInferred
                  ]
                · simp [
                    inferDetailed,
                    infer?,
                    Except.toOption,
                    leftDetailed,
                    leftInferred,
                    rightDetailed,
                    rightInferred,
                    matchingRight
                  ]
          · simp [
              inferDetailed,
              infer?,
              Except.toOption,
              leftDetailed,
              leftInferred,
              matchingLeft
            ]
  | letE value body valueIH bodyIH =>
      cases valueDetailed :
          inferDetailed context (path.child .letValue) value with
      | error error =>
          have valueNotInferred : infer? context value = none := by
            simpa [valueDetailed, Except.toOption] using
              (valueIH context (path.child .letValue)).symm
          simp [
            inferDetailed,
            infer?,
            Except.toOption,
            valueDetailed,
            valueNotInferred
          ]
      | ok valueType =>
          have valueInferred : infer? context value = some valueType := by
            simpa [valueDetailed, Except.toOption] using
              (valueIH context (path.child .letValue)).symm
          simpa [inferDetailed, infer?, valueDetailed, valueInferred] using
            bodyIH (valueType :: context) (path.child .letBody)
  | ifE condition thenBranch elseBranch conditionIH thenIH elseIH =>
      cases conditionDetailed :
          inferDetailed context (path.child .ifCondition) condition with
      | error error =>
          have conditionNotInferred : infer? context condition = none := by
            simpa [conditionDetailed, Except.toOption] using
              (conditionIH context (path.child .ifCondition)).symm
          simp [
            inferDetailed,
            infer?,
            Except.toOption,
            conditionDetailed,
            conditionNotInferred
          ]
      | ok conditionType =>
          have conditionInferred : infer? context condition = some conditionType := by
            simpa [conditionDetailed, Except.toOption] using
              (conditionIH context (path.child .ifCondition)).symm
          cases conditionType with
          | unit =>
              simp [
                inferDetailed,
                infer?,
                Except.toOption,
                conditionDetailed,
                conditionInferred
              ]
          | word =>
              simp [
                inferDetailed,
                infer?,
                Except.toOption,
                conditionDetailed,
                conditionInferred
              ]
          | product leftType rightType =>
              simp [
                inferDetailed,
                infer?,
                Except.toOption,
                conditionDetailed,
                conditionInferred
              ]
          | function parameterType resultType =>
              simp [
                inferDetailed,
                infer?,
                Except.toOption,
                conditionDetailed,
                conditionInferred
              ]
          | sum leftType rightType =>
              simp [
                inferDetailed,
                infer?,
                Except.toOption,
                conditionDetailed,
                conditionInferred
              ]
          | cell elementType =>
              simp [
                inferDetailed,
                infer?,
                Except.toOption,
                conditionDetailed,
                conditionInferred
              ]
          | bool =>
              cases thenDetailed :
                  inferDetailed context (path.child .ifThen) thenBranch with
              | error error =>
                  have thenNotInferred : infer? context thenBranch = none := by
                    simpa [thenDetailed, Except.toOption] using
                      (thenIH context (path.child .ifThen)).symm
                  simp [
                    inferDetailed,
                    infer?,
                    Except.toOption,
                    conditionDetailed,
                    conditionInferred,
                    thenDetailed,
                    thenNotInferred
                  ]
              | ok thenType =>
                  have thenInferred : infer? context thenBranch = some thenType := by
                    simpa [thenDetailed, Except.toOption] using
                      (thenIH context (path.child .ifThen)).symm
                  cases elseDetailed :
                      inferDetailed context (path.child .ifElse) elseBranch with
                  | error error =>
                      have elseNotInferred : infer? context elseBranch = none := by
                        simpa [elseDetailed, Except.toOption] using
                          (elseIH context (path.child .ifElse)).symm
                      simp [
                        inferDetailed,
                        infer?,
                        Except.toOption,
                        conditionDetailed,
                        conditionInferred,
                        thenDetailed,
                        thenInferred,
                        elseDetailed,
                        elseNotInferred
                      ]
                  | ok elseType =>
                      have elseInferred : infer? context elseBranch = some elseType := by
                        simpa [elseDetailed, Except.toOption] using
                          (elseIH context (path.child .ifElse)).symm
                      by_cases equalTypes : thenType = elseType
                      · subst elseType
                        simp [
                          inferDetailed,
                          infer?,
                          Except.toOption,
                          conditionDetailed,
                          conditionInferred,
                          thenDetailed,
                          thenInferred,
                          elseDetailed,
                          elseInferred
                        ]
                      · simp [
                          inferDetailed,
                          infer?,
                          Except.toOption,
                          conditionDetailed,
                          conditionInferred,
                          thenDetailed,
                          thenInferred,
                          elseDetailed,
                          elseInferred,
                          equalTypes
                        ]

theorem inferDetailed_iff_infer
    {context : Context} {path : CheckPath} {expr : Expr} {type : Ty} :
    inferDetailed context path expr = .ok type ↔ infer? context expr = some type := by
  rw [← inferDetailed_toOption context path expr]
  cases inferDetailed context path expr <;> simp [Except.toOption]

theorem inferDetailed_iff_typing
    {context : Context} {path : CheckPath} {expr : Expr} {type : Ty} :
    inferDetailed context path expr = .ok type ↔ HasType context expr type := by
  rw [inferDetailed_iff_infer, typing_iff_infer]

def Program.checkDetailed (program : Program) : Except CheckError Ty :=
  match inferDetailed [] [] program.body with
  | .error error => .error error
  | .ok inferredType =>
      if inferredType = program.resultType then
        .ok inferredType
      else
        .error {
          path := []
          data := .declaredResultTypeMismatch program.resultType inferredType
        }

theorem Program.checkDetailed_iff_typing {program : Program} :
    program.checkDetailed = .ok program.resultType ↔
      HasType [] program.body program.resultType := by
  constructor
  · intro checked
    cases detailed : inferDetailed [] [] program.body with
    | error error =>
        simp [Program.checkDetailed, detailed] at checked
    | ok inferredType =>
        by_cases equalTypes : inferredType = program.resultType
        · subst inferredType
          exact inferDetailed_iff_typing.mp detailed
        · simp [Program.checkDetailed, detailed, equalTypes] at checked
  · intro typing
    have detailed :
        inferDetailed [] [] program.body = .ok program.resultType :=
      inferDetailed_iff_typing.mpr typing
    simp [Program.checkDetailed, detailed]

theorem Program.checkDetailed_iff_check {program : Program} :
    program.checkDetailed = .ok program.resultType ↔ program.check = true := by
  rw [Program.checkDetailed_iff_typing]
  exact ⟨Program.check_complete, Program.check_sound⟩

theorem Program.checkDetailed_sound
    {program : Program}
    (checked : program.checkDetailed = .ok program.resultType) :
    HasType [] program.body program.resultType :=
  Program.checkDetailed_iff_typing.mp checked

theorem Program.checkDetailed_complete
    {program : Program}
    (typing : HasType [] program.body program.resultType) :
    program.checkDetailed = .ok program.resultType :=
  Program.checkDetailed_iff_typing.mpr typing

end Solcore.Core
