import Solcore.Core.Syntax

set_option autoImplicit false

namespace Solcore.Core

inductive HasType : Context → Expr → Ty → Prop where
  | unit {context : Context} : HasType context .unit .unit
  | bool {context : Context} {value : Bool} : HasType context (.bool value) .bool
  | word {context : Context} {value : Word} : HasType context (.word value) .word
  | var {context : Context} {index : Nat} {type : Ty} :
      context[index]? = some type →
      HasType context (.var index) type
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
