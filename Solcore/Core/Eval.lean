import Solcore.Core.Typing

set_option autoImplicit false

namespace Solcore.Core

inductive Evaluates : Environment → Expr → Value → Prop where
  | unit {environment : Environment} :
      Evaluates environment .unit .unit
  | bool {environment : Environment} {value : Bool} :
      Evaluates environment (.bool value) (.bool value)
  | word {environment : Environment} {value : Word} :
      Evaluates environment (.word value) (.word value)
  | pair
      {environment : Environment} {left right : Expr}
      {leftValue rightValue : Value} :
      Evaluates environment left leftValue →
      Evaluates environment right rightValue →
      Evaluates environment (.pair left right) (.pair leftValue rightValue)
  | first
      {environment : Environment} {operand : Expr}
      {leftValue rightValue : Value} :
      Evaluates environment operand (.pair leftValue rightValue) →
      Evaluates environment (.first operand) leftValue
  | second
      {environment : Environment} {operand : Expr}
      {leftValue rightValue : Value} :
      Evaluates environment operand (.pair leftValue rightValue) →
      Evaluates environment (.second operand) rightValue
  | inLeft
      {environment : Environment} {rightType : Ty} {payload : Expr}
      {payloadValue : Value} :
      Evaluates environment payload payloadValue →
      Evaluates environment (.inLeft rightType payload)
        (.inLeft rightType payloadValue)
  | inRight
      {environment : Environment} {leftType : Ty} {payload : Expr}
      {payloadValue : Value} :
      Evaluates environment payload payloadValue →
      Evaluates environment (.inRight leftType payload)
        (.inRight leftType payloadValue)
  | caseLeft
      {environment : Environment} {scrutinee leftBranch rightBranch : Expr}
      {rightType : Ty} {payload result : Value} :
      Evaluates environment scrutinee (.inLeft rightType payload) →
      Evaluates (payload :: environment) leftBranch result →
      Evaluates environment (.caseE scrutinee leftBranch rightBranch) result
  | caseRight
      {environment : Environment} {scrutinee leftBranch rightBranch : Expr}
      {leftType : Ty} {payload result : Value} :
      Evaluates environment scrutinee (.inRight leftType payload) →
      Evaluates (payload :: environment) rightBranch result →
      Evaluates environment (.caseE scrutinee leftBranch rightBranch) result
  | lambda
      {environment : Environment} {parameterType resultType : Ty}
      {body : Expr} :
      Evaluates environment (.lambda parameterType resultType body)
        (.closure parameterType resultType body environment)
  | apply
      {environment capturedEnvironment : Environment}
      {function argument body : Expr}
      {parameterType resultType : Ty}
      {argumentValue result : Value} :
      Evaluates environment function
        (.closure parameterType resultType body capturedEnvironment) →
      Evaluates environment argument argumentValue →
      Evaluates (argumentValue :: capturedEnvironment) body result →
      Evaluates environment (.apply function argument) result
  | var {environment : Environment} {index : Nat} {value : Value} :
      environment[index]? = some value →
      Evaluates environment (.var index) value
  | unary
      {environment : Environment} {op : UnaryOp} {operand : Expr}
      {operandValue result : Value} :
      Evaluates environment operand operandValue →
      op.apply operandValue = some result →
      Evaluates environment (.unary op operand) result
  | binary
      {environment : Environment} {op : BinaryOp} {left right : Expr}
      {leftValue rightValue result : Value} :
      Evaluates environment left leftValue →
      Evaluates environment right rightValue →
      op.apply leftValue rightValue = some result →
      Evaluates environment (.binary op left right) result
  | letE
      {environment : Environment} {value body : Expr}
      {boundValue result : Value} :
      Evaluates environment value boundValue →
      Evaluates (boundValue :: environment) body result →
      Evaluates environment (.letE value body) result
  | ifTrue
      {environment : Environment} {condition thenBranch elseBranch : Expr}
      {result : Value} :
      Evaluates environment condition (.bool true) →
      Evaluates environment thenBranch result →
      Evaluates environment (.ifE condition thenBranch elseBranch) result
  | ifFalse
      {environment : Environment} {condition thenBranch elseBranch : Expr}
      {result : Value} :
      Evaluates environment condition (.bool false) →
      Evaluates environment elseBranch result →
      Evaluates environment (.ifE condition thenBranch elseBranch) result

theorem evaluation_deterministic
    {environment : Environment} {expr : Expr} {left right : Value}
    (leftEvaluation : Evaluates environment expr left)
    (rightEvaluation : Evaluates environment expr right) :
    left = right := by
  induction leftEvaluation generalizing right with
  | unit =>
      cases rightEvaluation
      rfl
  | bool =>
      cases rightEvaluation
      rfl
  | word =>
      cases rightEvaluation
      rfl
  | pair _ _ leftIH rightIH =>
      cases rightEvaluation with
      | pair otherLeft otherRight =>
          cases leftIH otherLeft
          cases rightIH otherRight
          rfl
  | first _ operandIH =>
      cases rightEvaluation with
      | first otherOperand =>
          have pairEquality := operandIH otherOperand
          cases pairEquality
          rfl
  | second _ operandIH =>
      cases rightEvaluation with
      | second otherOperand =>
          have pairEquality := operandIH otherOperand
          cases pairEquality
          rfl
  | inLeft _ payloadIH =>
      cases rightEvaluation with
      | inLeft otherPayload =>
          cases payloadIH otherPayload
          rfl
  | inRight _ payloadIH =>
      cases rightEvaluation with
      | inRight otherPayload =>
          cases payloadIH otherPayload
          rfl
  | caseLeft _ _ scrutineeIH branchIH =>
      cases rightEvaluation with
      | caseLeft otherScrutinee otherBranch =>
          have scrutineeEquality := scrutineeIH otherScrutinee
          cases scrutineeEquality
          exact branchIH otherBranch
      | caseRight otherScrutinee _ =>
          have impossible := scrutineeIH otherScrutinee
          cases impossible
  | caseRight _ _ scrutineeIH branchIH =>
      cases rightEvaluation with
      | caseLeft otherScrutinee _ =>
          have impossible := scrutineeIH otherScrutinee
          cases impossible
      | caseRight otherScrutinee otherBranch =>
          have scrutineeEquality := scrutineeIH otherScrutinee
          cases scrutineeEquality
          exact branchIH otherBranch
  | lambda =>
      cases rightEvaluation
      rfl
  | apply _ _ _ functionIH argumentIH bodyIH =>
      cases rightEvaluation with
      | apply otherFunction otherArgument otherBody =>
          have functionEquality := functionIH otherFunction
          cases functionEquality
          have argumentEquality := argumentIH otherArgument
          cases argumentEquality
          exact bodyIH otherBody
  | var leftLookup =>
      cases rightEvaluation with
      | var rightLookup =>
          rw [leftLookup] at rightLookup
          cases rightLookup
          rfl
  | unary _ leftApplied operandIH =>
      cases rightEvaluation with
      | unary rightOperand rightApplied =>
          cases operandIH rightOperand
          rw [leftApplied] at rightApplied
          cases rightApplied
          rfl
  | binary _ _ leftApplied leftIH rightIH =>
      cases rightEvaluation with
      | binary otherLeft otherRight rightApplied =>
          cases leftIH otherLeft
          cases rightIH otherRight
          rw [leftApplied] at rightApplied
          cases rightApplied
          rfl
  | letE _ _ boundIH bodyIH =>
      cases rightEvaluation with
      | letE rightBound rightBody =>
          have boundEquality := boundIH rightBound
          cases boundEquality
          exact bodyIH rightBody
  | ifTrue _ _ conditionIH branchIH =>
      cases rightEvaluation with
      | ifTrue rightCondition rightBranch =>
          exact branchIH rightBranch
      | ifFalse rightCondition _ =>
          have impossible := conditionIH rightCondition
          cases impossible
  | ifFalse _ _ conditionIH branchIH =>
      cases rightEvaluation with
      | ifTrue rightCondition _ =>
          have impossible := conditionIH rightCondition
          cases impossible
      | ifFalse rightCondition rightBranch =>
          exact branchIH rightBranch

end Solcore.Core
