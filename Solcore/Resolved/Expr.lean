import Solcore.Resolved.LocalScope
import Solcore.Core.Primitive
import Solcore.Core.Internal.LocalFragment

/-!
# Resolved expressions

`Resolved.Expr` is an expression whose locals are identities, and `Resolved.Expr.lower?` lowers it
to Core. The laws of lowering follow, including that it produces only the local Core fragment.
-/

section
-- leanmerge: from Solcore.Resolved.Expr
set_option autoImplicit false

namespace Solcore.Resolved

/--
A monomorphic local-expression fragment after name and primitive selection.
Literals are semantic values, not source spellings. Source operator resolution,
mutable declarations, functions, imports, and staging are outside this fragment.
-/
inductive Expr where
  | unit
  | bool (value : Bool)
  | word (value : Core.Word)
  | var (id : LocalId)
  | pair (left right : Expr)
  | unary (op : Core.UnaryOp) (operand : Expr)
  | binary (op : Core.BinaryOp) (left right : Expr)
  | wordLt (left right : Expr)
  | letE (binder : LocalId) (value body : Expr)
  | ifE (condition thenBranch elseBranch : Expr)
  deriving Repr, DecidableEq

/-- Exact structural elaboration; no missing reference receives a default index. -/
def Expr.lower? (scope : List LocalId) : Expr → Option Core.Expr
  | .unit => some .unit
  | .bool value => some (.bool value)
  | .word value => some (.word value)
  | .var id => (LocalScope.index? scope id).map Core.Expr.var
  | .pair left right => do
      return .pair (← left.lower? scope) (← right.lower? scope)
  | .unary op operand => do
      return .unary op (← operand.lower? scope)
  | .binary op left right => do
      return .binary op (← left.lower? scope) (← right.lower? scope)
  | .wordLt left right => do
      return .wordLt (← left.lower? scope) (← right.lower? scope)
  | .letE binder value body => do
      return .letE (← value.lower? scope) (← body.lower? (binder :: scope))
  | .ifE condition thenBranch elseBranch => do
      return .ifE (← condition.lower? scope) (← thenBranch.lower? scope)
        (← elseBranch.lower? scope)

/-- Declarative elaboration with explicit lexical references and binder extent. -/
inductive Lowers : List LocalId → Expr → Core.Expr → Prop where
  | unit {scope} : Lowers scope .unit .unit
  | bool {scope value} : Lowers scope (.bool value) (.bool value)
  | word {scope value} : Lowers scope (.word value) (.word value)
  | var {scope id index} :
      LocalScope.IndexOf scope id index → Lowers scope (.var id) (.var index)
  | pair {scope left right coreLeft coreRight} :
      Lowers scope left coreLeft → Lowers scope right coreRight →
      Lowers scope (.pair left right) (.pair coreLeft coreRight)
  | unary {scope op operand coreOperand} :
      Lowers scope operand coreOperand →
      Lowers scope (.unary op operand) (.unary op coreOperand)
  | binary {scope op left right coreLeft coreRight} :
      Lowers scope left coreLeft → Lowers scope right coreRight →
      Lowers scope (.binary op left right) (.binary op coreLeft coreRight)
  | wordLt {scope left right coreLeft coreRight} :
      Lowers scope left coreLeft → Lowers scope right coreRight →
      Lowers scope (.wordLt left right) (coreLeft.wordLt coreRight)
  | letE {scope binder value body coreValue coreBody} :
      Lowers scope value coreValue → Lowers (binder :: scope) body coreBody →
      Lowers scope (.letE binder value body) (.letE coreValue coreBody)
  | ifE {scope condition thenBranch elseBranch coreCondition coreThen coreElse} :
      Lowers scope condition coreCondition → Lowers scope thenBranch coreThen →
      Lowers scope elseBranch coreElse →
      Lowers scope (.ifE condition thenBranch elseBranch)
        (.ifE coreCondition coreThen coreElse)

end Solcore.Resolved
end

section
-- leanmerge: from Solcore.Resolved.LoweringProperties
set_option autoImplicit false

namespace Solcore.Resolved

theorem Lowers.complete {scope : List LocalId} {expr : Expr} {core : Core.Expr}
    (lowered : Lowers scope expr core) : expr.lower? scope = some core := by
  induction lowered with
  | unit => rfl
  | bool => rfl
  | word => rfl
  | var found => simp [Expr.lower?, LocalScope.index?_iff.mpr found]
  | pair _ _ leftIH rightIH => simp [Expr.lower?, leftIH, rightIH]
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
  | pair left right leftIH rightIH =>
      simp only [Expr.lower?, bind, Option.bind_eq_some_iff, pure] at lowered
      obtain ⟨coreLeft, leftLowered, coreRight, rightLowered, result⟩ := lowered
      cases result
      exact .pair (leftIH leftLowered) (rightIH rightLowered)
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
end

section
-- leanmerge: from Solcore.Resolved.LocalFragmentProperties
/-! Existing resolved lowering produces only the independent local Core
fragment. This structural bridge does not use either language's evaluation
correspondence and introduces no dependency from Core back to Resolved. -/

set_option autoImplicit false

namespace Solcore.Resolved

theorem Lowers.localFragment {scope : List LocalId} {expr : Expr} {core : Core.Expr}
    (lowered : Lowers scope expr core) : Core.Expr.LocalFragment core := by
  induction lowered with
  | unit => exact .unit
  | bool => exact .bool
  | word => exact .word
  | var => exact .var
  | pair _ _ leftIH rightIH => exact .pair leftIH rightIH
  | unary _ ih => exact .unary ih
  | binary _ _ leftIH rightIH => exact .binary leftIH rightIH
  | wordLt _ _ leftIH rightIH => exact leftIH.wordLt rightIH
  | letE _ _ valueIH bodyIH => exact .letE valueIH bodyIH
  | ifE _ _ _ conditionIH thenIH elseIH => exact .ifE conditionIH thenIH elseIH

end Solcore.Resolved
end
