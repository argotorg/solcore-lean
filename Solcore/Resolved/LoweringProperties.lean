import Solcore.Resolved.Expr
import Solcore.Resolved.LocalScopeProperties

set_option autoImplicit false

namespace Solcore.Resolved

theorem Lowers.complete {scope : List LocalId} {expr : Expr} {core : Core.Expr}
    (lowered : Lowers scope expr core) : expr.lower? scope = some core := by
  induction lowered with
  | unit => rfl
  | bool => rfl
  | word => rfl
  | var found => simp [Expr.lower?, LocalScope.index?_iff.mpr found]
  | unary _ ih => simp [Expr.lower?, ih]
  | binary _ _ leftIH rightIH => simp [Expr.lower?, leftIH, rightIH]
  | wordLt _ _ leftIH rightIH => simp [Expr.lower?, leftIH, rightIH]
  | letE _ _ valueIH bodyIH => simp [Expr.lower?, valueIH, bodyIH]
  | ifE _ _ _ conditionIH thenIH elseIH =>
      simp [Expr.lower?, conditionIH, thenIH, elseIH]

theorem Expr.lower?_sound {scope : List LocalId} {expr : Expr} {core : Core.Expr}
    (lowered : expr.lower? scope = some core) : Lowers scope expr core := by
  induction expr generalizing scope core with
  | unit => cases lowered; exact .unit
  | bool value => cases lowered; exact .bool
  | word value => cases lowered; exact .word
  | var id =>
      simp only [Expr.lower?, Option.map_eq_some_iff] at lowered
      obtain ⟨index, found, rfl⟩ := lowered
      exact .var (LocalScope.index?_iff.mp found)
  | unary op operand ih =>
      simp only [Expr.lower?, bind, Option.bind_eq_some_iff, pure] at lowered
      obtain ⟨coreOperand, operandLowered, result⟩ := lowered
      cases result
      exact .unary (ih operandLowered)
  | binary op left right leftIH rightIH =>
      simp only [Expr.lower?, bind, Option.bind_eq_some_iff, pure] at lowered
      obtain ⟨coreLeft, leftLowered, coreRight, rightLowered, result⟩ := lowered
      cases result
      exact .binary (leftIH leftLowered) (rightIH rightLowered)
  | wordLt left right leftIH rightIH =>
      simp only [Expr.lower?, bind, Option.bind_eq_some_iff, pure] at lowered
      obtain ⟨coreLeft, leftLowered, coreRight, rightLowered, result⟩ := lowered
      cases result
      exact .wordLt (leftIH leftLowered) (rightIH rightLowered)
  | letE binder value body valueIH bodyIH =>
      simp only [Expr.lower?, bind, Option.bind_eq_some_iff, pure] at lowered
      obtain ⟨coreValue, valueLowered, coreBody, bodyLowered, result⟩ := lowered
      cases result
      exact .letE (valueIH valueLowered) (bodyIH bodyLowered)
  | ifE condition thenBranch elseBranch conditionIH thenIH elseIH =>
      simp only [Expr.lower?, bind, Option.bind_eq_some_iff, pure] at lowered
      obtain ⟨coreCondition, conditionLowered, coreThen, thenLowered,
        coreElse, elseLowered, result⟩ := lowered
      cases result
      exact .ifE (conditionIH conditionLowered) (thenIH thenLowered) (elseIH elseLowered)

theorem Expr.lower?_iff {scope : List LocalId} {expr : Expr} {core : Core.Expr} :
    expr.lower? scope = some core ↔ Lowers scope expr core :=
  ⟨Expr.lower?_sound, Lowers.complete⟩

theorem Lowers.deterministic {scope : List LocalId} {expr : Expr} {left right : Core.Expr}
    (first : Lowers scope expr left) (second : Lowers scope expr right) : left = right :=
  Option.some.inj (first.complete.symm.trans second.complete)

/-- Elaboration fails precisely when no declarative elaboration exists. -/
theorem Expr.lower?_eq_none_iff {scope : List LocalId} {expr : Expr} :
    expr.lower? scope = none ↔ ¬ ∃ core, Lowers scope expr core := by
  constructor
  · intro missing ⟨core, lowered⟩
    have result := lowered.complete
    rw [missing] at result
    contradiction
  · intro missing
    cases result : expr.lower? scope with
    | none => rfl
    | some core => exact False.elim (missing ⟨core, Expr.lower?_sound result⟩)

end Solcore.Resolved
