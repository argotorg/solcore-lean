import Solcore.Core.Primitive

set_option autoImplicit false

namespace Solcore.Core

inductive HasType : Context → Expr → Ty → Prop where
  | unit {context : Context} : HasType context .unit .unit
  | bool {context : Context} {value : Bool} : HasType context (.bool value) .bool
  | word {context : Context} {value : Word} : HasType context (.word value) .word
  | var {context : Context} {index : Nat} {type : Ty} :
      context[index]? = some type →
      HasType context (.var index) type
  | pair
      {context : Context} {left right : Expr} {leftType rightType : Ty} :
      HasType context left leftType →
      HasType context right rightType →
      HasType context (.pair left right) (.product leftType rightType)
  | first
      {context : Context} {operand : Expr} {leftType rightType : Ty} :
      HasType context operand (.product leftType rightType) →
      HasType context (.first operand) leftType
  | second
      {context : Context} {operand : Expr} {leftType rightType : Ty} :
      HasType context operand (.product leftType rightType) →
      HasType context (.second operand) rightType
  | lambda
      {context : Context} {parameterType resultType : Ty} {body : Expr} :
      HasType (parameterType :: context) body resultType →
      HasType context
        (.lambda parameterType resultType body)
        (.function parameterType resultType)
  | apply
      {context : Context} {function argument : Expr}
      {parameterType resultType : Ty} :
      HasType context function (.function parameterType resultType) →
      HasType context argument parameterType →
      HasType context (.apply function argument) resultType
  | inLeft
      {context : Context} {rightType leftType : Ty} {payload : Expr} :
      HasType context payload leftType →
      HasType context (.inLeft rightType payload) (.sum leftType rightType)
  | inRight
      {context : Context} {leftType rightType : Ty} {payload : Expr} :
      HasType context payload rightType →
      HasType context (.inRight leftType payload) (.sum leftType rightType)
  | caseE
      {context : Context} {scrutinee leftBranch rightBranch : Expr}
      {leftType rightType resultType : Ty} :
      HasType context scrutinee (.sum leftType rightType) →
      HasType (leftType :: context) leftBranch resultType →
      HasType (rightType :: context) rightBranch resultType →
      HasType context (.caseE scrutinee leftBranch rightBranch) resultType
  | unary
      {context : Context} {op : UnaryOp} {operand : Expr} :
      HasType context operand op.operandType →
      HasType context (.unary op operand) op.resultType
  | binary
      {context : Context} {op : BinaryOp} {left right : Expr} :
      HasType context left op.leftType →
      HasType context right op.rightType →
      HasType context (.binary op left right) op.resultType
  | letE :
      {context : Context} → {value body : Expr} → {valueType bodyType : Ty} →
      HasType context value valueType →
      HasType (valueType :: context) body bodyType →
      HasType context (.letE value body) bodyType
  | ifE :
      {context : Context} → {condition thenBranch elseBranch : Expr} → {resultType : Ty} →
      HasType context condition .bool →
      HasType context thenBranch resultType →
      HasType context elseBranch resultType →
      HasType context (.ifE condition thenBranch elseBranch) resultType

def infer? (context : Context) : Expr → Option Ty
  | .unit => some .unit
  | .bool _ => some .bool
  | .word _ => some .word
  | .var index => context[index]?
  | .pair left right =>
      match infer? context left, infer? context right with
      | some leftType, some rightType => some (.product leftType rightType)
      | _, _ => none
  | .first operand =>
      match infer? context operand with
      | some (.product leftType _) => some leftType
      | _ => none
  | .second operand =>
      match infer? context operand with
      | some (.product _ rightType) => some rightType
      | _ => none
  | .lambda parameterType resultType body =>
      if infer? (parameterType :: context) body = some resultType then
        some (.function parameterType resultType)
      else
        none
  | .apply function argument =>
      match infer? context function with
      | some (.function parameterType resultType) =>
          if infer? context argument = some parameterType then
            some resultType
          else
            none
      | _ => none
  | .inLeft rightType payload =>
      match infer? context payload with
      | some leftType => some (.sum leftType rightType)
      | none => none
  | .inRight leftType payload =>
      match infer? context payload with
      | some rightType => some (.sum leftType rightType)
      | none => none
  | .caseE scrutinee leftBranch rightBranch =>
      match infer? context scrutinee with
      | some (.sum leftType rightType) =>
          match
              infer? (leftType :: context) leftBranch,
              infer? (rightType :: context) rightBranch with
          | some leftResultType, some rightResultType =>
              if leftResultType = rightResultType then
                some leftResultType
              else
                none
          | _, _ => none
      | _ => none
  | .unary op operand =>
      if infer? context operand = some op.operandType then
        some op.resultType
      else
        none
  | .binary op left right =>
      if infer? context left = some op.leftType then
        if infer? context right = some op.rightType then
          some op.resultType
        else
          none
      else
        none
  | .letE value body =>
      match infer? context value with
      | some valueType => infer? (valueType :: context) body
      | none => none
  | .ifE condition thenBranch elseBranch =>
      match infer? context condition, infer? context thenBranch, infer? context elseBranch with
      | some .bool, some thenType, some elseType =>
          if thenType = elseType then some thenType else none
      | _, _, _ => none

theorem infer_complete
    {context : Context} {expr : Expr} {type : Ty}
    (typing : HasType context expr type) :
    infer? context expr = some type := by
  induction typing with
  | unit | bool | word | var => simp_all [infer?]
  | pair _ _ leftIH rightIH => simp [infer?, leftIH, rightIH]
  | first _ operandIH => simp [infer?, operandIH]
  | second _ operandIH => simp [infer?, operandIH]
  | lambda bodyTyping bodyIH => simp [infer?, bodyIH]
  | apply _ _ functionIH argumentIH => simp [infer?, functionIH, argumentIH]
  | inLeft _ payloadIH => simp [infer?, payloadIH]
  | inRight _ payloadIH => simp [infer?, payloadIH]
  | caseE _ _ _ scrutineeIH leftIH rightIH =>
      simp [infer?, scrutineeIH, leftIH, rightIH]
  | unary _ operandIH => simp [infer?, operandIH]
  | binary _ _ leftIH rightIH => simp [infer?, leftIH, rightIH]
  | letE _ _ valueIH bodyIH => simp_all [infer?]
  | ifE _ _ _ conditionIH thenIH elseIH => simp_all [infer?]

theorem infer_sound
    {context : Context} {expr : Expr} {type : Ty}
    (inferred : infer? context expr = some type) :
    HasType context expr type := by
  induction expr generalizing context type with
  | unit =>
      simp [infer?] at inferred
      cases inferred
      exact .unit
  | bool =>
      simp [infer?] at inferred
      cases inferred
      exact .bool
  | word =>
      simp [infer?] at inferred
      cases inferred
      exact .word
  | var index =>
      exact .var inferred
  | pair left right leftIH rightIH =>
      cases leftInferred : infer? context left with
      | none => simp [infer?, leftInferred] at inferred
      | some leftType =>
          cases rightInferred : infer? context right with
          | none => simp [infer?, leftInferred, rightInferred] at inferred
          | some rightType =>
              have resultType : Ty.product leftType rightType = type := by
                exact Option.some.inj (by
                  simpa [infer?, leftInferred, rightInferred] using inferred)
              subst type
              exact .pair
                (leftIH leftInferred)
                (rightIH rightInferred)
  | first operand operandIH =>
      cases operandInferred : infer? context operand with
      | none => simp [infer?, operandInferred] at inferred
      | some operandType =>
          cases operandType with
          | unit => simp [infer?, operandInferred] at inferred
          | bool => simp [infer?, operandInferred] at inferred
          | word => simp [infer?, operandInferred] at inferred
          | product leftType rightType =>
              have resultType : leftType = type := by
                exact Option.some.inj (by
                  simpa [infer?, operandInferred] using inferred)
              subst type
              exact .first (operandIH operandInferred)
          | function parameterType resultType =>
              simp [infer?, operandInferred] at inferred
          | sum leftType rightType =>
              simp [infer?, operandInferred] at inferred
  | second operand operandIH =>
      cases operandInferred : infer? context operand with
      | none => simp [infer?, operandInferred] at inferred
      | some operandType =>
          cases operandType with
          | unit => simp [infer?, operandInferred] at inferred
          | bool => simp [infer?, operandInferred] at inferred
          | word => simp [infer?, operandInferred] at inferred
          | product leftType rightType =>
              have resultType : rightType = type := by
                exact Option.some.inj (by
                  simpa [infer?, operandInferred] using inferred)
              subst type
              exact .second (operandIH operandInferred)
          | function parameterType resultType =>
              simp [infer?, operandInferred] at inferred
          | sum leftType rightType =>
              simp [infer?, operandInferred] at inferred
  | lambda parameterType resultType body bodyIH =>
      by_cases bodyInferred :
          infer? (parameterType :: context) body = some resultType
      · have functionType : Ty.function parameterType resultType = type := by
          exact Option.some.inj (by
            simpa [infer?, bodyInferred] using inferred)
        subst type
        exact .lambda (bodyIH bodyInferred)
      · simp [infer?, bodyInferred] at inferred
  | apply function argument functionIH argumentIH =>
      cases functionInferred : infer? context function with
      | none => simp [infer?, functionInferred] at inferred
      | some functionType =>
          cases functionType with
          | unit => simp [infer?, functionInferred] at inferred
          | bool => simp [infer?, functionInferred] at inferred
          | word => simp [infer?, functionInferred] at inferred
          | product leftType rightType =>
              simp [infer?, functionInferred] at inferred
          | function parameterType resultType =>
              by_cases argumentInferred :
                  infer? context argument = some parameterType
              · have inferredResult : resultType = type := by
                  exact Option.some.inj (by
                    simpa [infer?, functionInferred, argumentInferred] using inferred)
                subst type
                exact .apply
                  (functionIH functionInferred)
                  (argumentIH argumentInferred)
              · simp [infer?, functionInferred, argumentInferred] at inferred
          | sum leftType rightType =>
              simp [infer?, functionInferred] at inferred
  | inLeft rightType payload payloadIH =>
      cases payloadInferred : infer? context payload with
      | none => simp [infer?, payloadInferred] at inferred
      | some leftType =>
          have sumType : Ty.sum leftType rightType = type := by
            exact Option.some.inj (by
              simpa [infer?, payloadInferred] using inferred)
          subst type
          exact .inLeft (payloadIH payloadInferred)
  | inRight leftType payload payloadIH =>
      cases payloadInferred : infer? context payload with
      | none => simp [infer?, payloadInferred] at inferred
      | some rightType =>
          have sumType : Ty.sum leftType rightType = type := by
            exact Option.some.inj (by
              simpa [infer?, payloadInferred] using inferred)
          subst type
          exact .inRight (payloadIH payloadInferred)
  | caseE scrutinee leftBranch rightBranch scrutineeIH leftIH rightIH =>
      cases scrutineeInferred : infer? context scrutinee with
      | none => simp [infer?, scrutineeInferred] at inferred
      | some scrutineeType =>
          cases scrutineeType with
          | unit => simp [infer?, scrutineeInferred] at inferred
          | bool => simp [infer?, scrutineeInferred] at inferred
          | word => simp [infer?, scrutineeInferred] at inferred
          | product firstType secondType =>
              simp [infer?, scrutineeInferred] at inferred
          | function parameterType resultType =>
              simp [infer?, scrutineeInferred] at inferred
          | sum leftType rightType =>
              cases leftInferred : infer? (leftType :: context) leftBranch with
              | none => simp [infer?, scrutineeInferred, leftInferred] at inferred
              | some leftResultType =>
                  cases rightInferred : infer? (rightType :: context) rightBranch with
                  | none =>
                      simp [infer?, scrutineeInferred, leftInferred, rightInferred]
                        at inferred
                  | some rightResultType =>
                      by_cases equalTypes : leftResultType = rightResultType
                      · subst rightResultType
                        have inferredResult : leftResultType = type := by
                          exact Option.some.inj (by
                            simpa [infer?, scrutineeInferred, leftInferred, rightInferred]
                              using inferred)
                        subst type
                        exact .caseE
                          (scrutineeIH scrutineeInferred)
                          (leftIH leftInferred)
                          (rightIH rightInferred)
                      · simp [
                          infer?,
                          scrutineeInferred,
                          leftInferred,
                          rightInferred,
                          equalTypes
                        ] at inferred
  | unary op operand operandIH =>
      by_cases operandInferred :
          infer? context operand = some op.operandType
      · have resultType : op.resultType = type := by
          exact Option.some.inj (by
            simpa [infer?, operandInferred] using inferred)
        subst type
        exact .unary (operandIH operandInferred)
      · simp [infer?, operandInferred] at inferred
  | binary op left right leftIH rightIH =>
      by_cases leftInferred :
          infer? context left = some op.leftType
      · by_cases rightInferred :
            infer? context right = some op.rightType
        · have resultType : op.resultType = type := by
            exact Option.some.inj (by
              simpa [infer?, leftInferred, rightInferred] using inferred)
          subst type
          exact .binary
            (leftIH leftInferred)
            (rightIH rightInferred)
        · simp [infer?, leftInferred, rightInferred] at inferred
      · simp [infer?, leftInferred] at inferred
  | letE value body valueIH bodyIH =>
      cases valueInferred : infer? context value with
      | none => simp [infer?, valueInferred] at inferred
      | some valueType =>
          exact .letE
            (valueIH valueInferred)
            (bodyIH (by simpa [infer?, valueInferred] using inferred))
  | ifE condition thenBranch elseBranch conditionIH thenIH elseIH =>
      cases conditionInferred : infer? context condition with
      | none => simp [infer?, conditionInferred] at inferred
      | some conditionType =>
          cases conditionType with
          | unit => simp [infer?, conditionInferred] at inferred
          | word => simp [infer?, conditionInferred] at inferred
          | product leftType rightType =>
              simp [infer?, conditionInferred] at inferred
          | function parameterType resultType =>
              simp [infer?, conditionInferred] at inferred
          | sum leftType rightType =>
              simp [infer?, conditionInferred] at inferred
          | bool =>
              cases thenInferred : infer? context thenBranch with
              | none => simp [infer?, conditionInferred, thenInferred] at inferred
              | some thenType =>
                  cases elseInferred : infer? context elseBranch with
                  | none =>
                      simp [infer?, conditionInferred, thenInferred, elseInferred] at inferred
                  | some elseType =>
                      by_cases equalTypes : thenType = elseType
                      · subst elseType
                        have resultType : thenType = type := by
                          exact Option.some.inj (by
                            simpa [infer?, conditionInferred, thenInferred, elseInferred]
                              using inferred)
                        subst type
                        exact .ifE
                          (conditionIH conditionInferred)
                          (thenIH thenInferred)
                          (elseIH elseInferred)
                      · simp [infer?, conditionInferred, thenInferred, elseInferred, equalTypes]
                          at inferred

theorem typing_iff_infer :
    {context : Context} → {expr : Expr} → {type : Ty} →
    HasType context expr type ↔ infer? context expr = some type :=
  ⟨infer_complete, infer_sound⟩

theorem typing_deterministic
    {context : Context} {expr : Expr} {leftType rightType : Ty}
    (left : HasType context expr leftType)
    (right : HasType context expr rightType) :
    leftType = rightType := by
  rw [typing_iff_infer] at left right
  rw [left] at right
  cases right
  rfl

def Program.check (program : Program) : Bool :=
  match infer? [] program.body with
  | some inferredType => decide (inferredType = program.resultType)
  | none => false

theorem Program.check_sound {program : Program} (checked : program.check = true) :
    HasType [] program.body program.resultType := by
  cases inferred : infer? [] program.body with
  | none => simp [Program.check, inferred] at checked
  | some inferredType =>
      have typeEquality : inferredType = program.resultType := by
        simpa [Program.check, inferred] using checked
      subst inferredType
      exact infer_sound inferred

theorem Program.check_complete
    {program : Program}
    (typing : HasType [] program.body program.resultType) :
    program.check = true := by
  simp [Program.check, infer_complete typing]

end Solcore.Core
