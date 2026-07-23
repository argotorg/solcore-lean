import Solcore.Core.Typing

set_option autoImplicit false

namespace Solcore.Core

inductive CheckPathStep where
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
  | branchTypeMismatch
  | declaredResultTypeMismatch
  deriving Repr, BEq, DecidableEq

def CheckErrorCode.name : CheckErrorCode → String
  | .unboundVariable => "core.check.unbound-variable"
  | .expectedBool => "core.check.expected-bool"
  | .branchTypeMismatch => "core.check.branch-type-mismatch"
  | .declaredResultTypeMismatch => "core.check.declared-result-type-mismatch"

inductive CheckErrorData where
  | unboundVariable (index contextSize : Nat)
  | expectedBool (actual : Ty)
  | branchTypeMismatch (thenType elseType : Ty)
  | declaredResultTypeMismatch (declaredType inferredType : Ty)
  deriving Repr, BEq, DecidableEq

def CheckErrorData.code : CheckErrorData → CheckErrorCode
  | .unboundVariable .. => .unboundVariable
  | .expectedBool .. => .expectedBool
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
