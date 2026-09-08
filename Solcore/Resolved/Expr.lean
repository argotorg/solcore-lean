import Solcore.Resolved.LocalScope
import Solcore.Core.Primitive

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
