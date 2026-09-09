import Solcore.Core.Syntax

/-! Whole caller bodies close an arbitrary child predicate under unit, lets,
conditionals and generated Word tests. Membership imposes no runtime contract. -/

set_option autoImplicit false

namespace Solcore.Frontend

inductive ComputationBodyFragment (F : Core.Expr → Prop) : Core.Expr → Prop where
  | unit : ComputationBodyFragment F .unit
  | leaf {expr : Core.Expr} (child : F expr) : ComputationBodyFragment F expr
  | letE {initializer body : Core.Expr}
      (head : ComputationBodyFragment F initializer) (tail : ComputationBodyFragment F body) :
      ComputationBodyFragment F (.letE initializer body)
  | ifE {condition thenBranch elseBranch : Core.Expr}
      (guard : ComputationBodyFragment F condition)
      (yes : ComputationBodyFragment F thenBranch) (no : ComputationBodyFragment F elseBranch) :
      ComputationBodyFragment F (.ifE condition thenBranch elseBranch)
  | wordTest {index : Nat} {word : Core.Word} :
      ComputationBodyFragment F (.binary .wordEq (.var index) (.word word))

end Solcore.Frontend
