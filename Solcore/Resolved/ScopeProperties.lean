import Solcore.Resolved.Scope
import Solcore.Resolved.LoweringProperties
import Solcore.Resolved.Typing

/-! Local scope validity exactly characterizes successful structural lowering.
This boundary is independent of operand types and requires no identity freshness. -/

set_option autoImplicit false

namespace Solcore.Resolved

theorem Lowers.wellScoped {scope : List LocalId} {expr : Expr} {core : Core.Expr}
    (lowered : Lowers scope expr core) : WellScoped scope expr := by
  induction lowered with
  | unit => exact .unit
  | bool => exact .bool
  | word => exact .word
  | var indexed =>
      apply WellScoped.var
      induction indexed with
      | head => exact List.mem_cons_self
      | tail _ _ ih => exact List.mem_cons_of_mem _ ih
  | unary _ ih => exact .unary ih
  | binary _ _ leftIH rightIH => exact .binary leftIH rightIH
  | letE _ _ valueIH bodyIH => exact .letE valueIH bodyIH
  | ifE _ _ _ conditionIH thenIH elseIH => exact .ifE conditionIH thenIH elseIH

/-- In-scope references always have an exact first-match positional lowering. -/
theorem WellScoped.lowers {scope : List LocalId} {expr : Expr}
    (scopeValid : WellScoped scope expr) : ∃ core, Lowers scope expr core := by
  induction scopeValid with
  | unit => exact ⟨_, .unit⟩
  | bool => exact ⟨_, .bool⟩
  | word => exact ⟨_, .word⟩
  | @var scope id member =>
      cases result : LocalScope.index? scope id with
      | none => exact False.elim ((LocalScope.index?_eq_none_iff.mp result) member)
      | some index => exact ⟨_, .var (LocalScope.index?_iff.mp result)⟩
  | unary _ ih =>
      obtain ⟨core, lowered⟩ := ih
      exact ⟨_, .unary lowered⟩
  | binary _ _ leftIH rightIH =>
      obtain ⟨left, leftLowered⟩ := leftIH
      obtain ⟨right, rightLowered⟩ := rightIH
      exact ⟨_, .binary leftLowered rightLowered⟩
  | letE _ _ valueIH bodyIH =>
      obtain ⟨value, valueLowered⟩ := valueIH
      obtain ⟨body, bodyLowered⟩ := bodyIH
      exact ⟨_, .letE valueLowered bodyLowered⟩
  | ifE _ _ _ conditionIH thenIH elseIH =>
      obtain ⟨condition, conditionLowered⟩ := conditionIH
      obtain ⟨thenBranch, thenLowered⟩ := thenIH
      obtain ⟨elseBranch, elseLowered⟩ := elseIH
      exact ⟨_, .ifE conditionLowered thenLowered elseLowered⟩

theorem wellScoped_iff_lowers {scope : List LocalId} {expr : Expr} :
    WellScoped scope expr ↔ ∃ core, Lowers scope expr core :=
  ⟨WellScoped.lowers, fun ⟨_, lowered⟩ => lowered.wellScoped⟩

/-- No out-of-scope reference can be hidden by structural elaboration. -/
theorem Expr.lower?_eq_none_iff_not_wellScoped {scope : List LocalId} {expr : Expr} :
    expr.lower? scope = none ↔ ¬ WellScoped scope expr := by
  rw [Expr.lower?_eq_none_iff, wellScoped_iff_lowers]

theorem Expr.lower?_isSome_iff_wellScoped {scope : List LocalId} {expr : Expr} :
    (expr.lower? scope).isSome = true ↔ WellScoped scope expr := by
  cases result : expr.lower? scope with
  | none =>
      simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
      exact Expr.lower?_eq_none_iff_not_wellScoped.mp result
  | some core =>
      simp only [Option.isSome_some, true_iff]
      exact (Expr.lower?_sound result).wellScoped

/-- Independent typing checks scope in all branches, including unselected ones. -/
theorem HasType.wellScoped {context : Context} {expr : Expr} {type : Core.Ty}
    (typing : HasType context expr type) : WellScoped (LocalScope.ids context) expr := by
  induction typing with
  | unit => exact .unit
  | bool => exact .bool
  | word => exact .word
  | var found => exact .var (List.mem_map.mpr ⟨_, found.mem, rfl⟩)
  | unary _ ih => exact .unary ih
  | binary _ _ leftIH rightIH => exact .binary leftIH rightIH
  | letE _ _ valueIH bodyIH => exact .letE valueIH bodyIH
  | ifE _ _ _ conditionIH thenIH elseIH => exact .ifE conditionIH thenIH elseIH

/-- A missing local variable is rejected instead of receiving a default index. -/
theorem Expr.lower?_var_eq_none_iff {scope : List LocalId} {id : LocalId} :
    (Expr.var id).lower? scope = none ↔ id ∉ scope := by
  rw [Expr.lower?_eq_none_iff_not_wellScoped]
  constructor
  · intro rejected member
    exact rejected (.var member)
  · intro missing scopeValid
    cases scopeValid with
    | var member => exact missing member

end Solcore.Resolved
