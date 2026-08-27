import Solcore.Core.Typing

set_option autoImplicit false

namespace Solcore.Core

inductive CheckPathStep where
  | pairLeft
  | pairRight
  | firstOperand
  | secondOperand
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
  | primitiveOperandTypeMismatch
  | branchTypeMismatch
  | declaredResultTypeMismatch
  deriving Repr, BEq, DecidableEq

def CheckErrorCode.name : CheckErrorCode → String
  | .unboundVariable => "core.check.unbound-variable"
  | .expectedBool => "core.check.expected-bool"
  | .expectedProduct => "core.check.expected-product"
  | .primitiveOperandTypeMismatch =>
      "core.check.primitive-operand-type-mismatch"
  | .branchTypeMismatch => "core.check.branch-type-mismatch"
  | .declaredResultTypeMismatch => "core.check.declared-result-type-mismatch"

inductive CheckErrorData where
  | unboundVariable (index contextSize : Nat)
  | expectedBool (actual : Ty)
  | expectedProduct (actual : Ty)
  | primitiveOperandTypeMismatch (expected actual : Ty)
  | branchTypeMismatch (thenType elseType : Ty)
  | declaredResultTypeMismatch (declaredType inferredType : Ty)
  deriving Repr, BEq, DecidableEq

def CheckErrorData.code : CheckErrorData → CheckErrorCode
  | .unboundVariable .. => .unboundVariable
  | .expectedBool .. => .expectedBool
  | .expectedProduct .. => .expectedProduct
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
