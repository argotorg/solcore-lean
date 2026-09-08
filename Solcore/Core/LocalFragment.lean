import Solcore.Core.Primitive

/-! A syntax-only boundary for the local expression fragment. It neither
requires typing or valid indices nor asserts that an expression evaluates.
All children are checked, including branches that execution may not select.
Variables may return arbitrary runtime values, but no form creates or calls
a closure or reads or writes a cell. -/

set_option autoImplicit false

namespace Solcore.Core

inductive Expr.LocalFragment : Expr → Prop where
  | unit : LocalFragment .unit
  | bool {value : Bool} : LocalFragment (.bool value)
  | word {value : Word} : LocalFragment (.word value)
  | var {index : Nat} : LocalFragment (.var index)
  | unary {op : UnaryOp} {operand : Expr} :
      LocalFragment operand → LocalFragment (.unary op operand)
  | binary {op : BinaryOp} {left right : Expr} :
      LocalFragment left → LocalFragment right → LocalFragment (.binary op left right)
  | letE {value body : Expr} :
      LocalFragment value → LocalFragment body → LocalFragment (.letE value body)
  | ifE {condition thenBranch elseBranch : Expr} :
      LocalFragment condition → LocalFragment thenBranch → LocalFragment elseBranch →
      LocalFragment (.ifE condition thenBranch elseBranch)

/-- Positional insertion stays within the fragment at every cutoff, including
under lets. This structural fact imposes no bound on the inserted position. -/
theorem Expr.LocalFragment.weakenAt {expr : Expr}
    (fragment : Expr.LocalFragment expr) (cutoff : Nat) :
    Expr.LocalFragment (expr.weakenAt cutoff) := by
  induction fragment generalizing cutoff with
  | unit => simp only [Expr.weakenAt]; exact .unit
  | bool => simp only [Expr.weakenAt]; exact .bool
  | word => simp only [Expr.weakenAt]; exact .word
  | var =>
      simp only [Expr.weakenAt]
      split <;> exact .var
  | unary _ ih => simp only [Expr.weakenAt]; exact .unary (ih cutoff)
  | binary _ _ leftIH rightIH =>
      simp only [Expr.weakenAt]
      exact .binary (leftIH cutoff) (rightIH cutoff)
  | letE _ _ valueIH bodyIH =>
      simp only [Expr.weakenAt]
      exact .letE (valueIH cutoff) (bodyIH (cutoff + 1))
  | ifE _ _ _ conditionIH thenIH elseIH =>
      simp only [Expr.weakenAt]
      exact .ifE (conditionIH cutoff) (thenIH cutoff) (elseIH cutoff)

end Solcore.Core
