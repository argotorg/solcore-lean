import Solcore.Resolved.Expr
import Solcore.Core.Eval

set_option autoImplicit false

namespace Solcore.Resolved

abbrev Environment := LocalScope Core.Value

/--
Independent named-environment evaluation. Primitive operations have already
been selected; this relation does not give meanings to unresolved source names.
-/
inductive Evaluates : Environment → Core.Store → Expr → Core.Value → Core.Store → Prop where
  | unit {environment store} : Evaluates environment store .unit .unit store
  | bool {environment store value} :
      Evaluates environment store (.bool value) (.bool value) store
  | word {environment store value} :
      Evaluates environment store (.word value) (.word value) store
  | var {environment store id value} :
      LocalScope.Lookup environment id value →
      Evaluates environment store (.var id) value store
  | unary {environment initialStore finalStore op operand operandValue result} :
      Evaluates environment initialStore operand operandValue finalStore →
      op.apply operandValue = some result →
      Evaluates environment initialStore (.unary op operand) result finalStore
  | binary {environment initialStore middleStore finalStore op left right
      leftValue rightValue result} :
      Evaluates environment initialStore left leftValue middleStore →
      Evaluates environment middleStore right rightValue finalStore →
      op.apply leftValue rightValue = some result →
      Evaluates environment initialStore (.binary op left right) result finalStore
  | wordLt {environment initialStore middleStore finalStore left right leftWord rightWord} :
      Evaluates environment initialStore left (.word leftWord) middleStore →
      Evaluates environment middleStore right (.word rightWord) finalStore →
      Evaluates environment initialStore (.wordLt left right)
        (.bool (decide (leftWord < rightWord))) finalStore
  | letE {environment initialStore middleStore finalStore binder value body boundValue result} :
      Evaluates environment initialStore value boundValue middleStore →
      Evaluates ((binder, boundValue) :: environment) middleStore body result finalStore →
      Evaluates environment initialStore (.letE binder value body) result finalStore
  | ifTrue {environment initialStore middleStore finalStore condition thenBranch elseBranch result} :
      Evaluates environment initialStore condition (.bool true) middleStore →
      Evaluates environment middleStore thenBranch result finalStore →
      Evaluates environment initialStore (.ifE condition thenBranch elseBranch) result finalStore
  | ifFalse {environment initialStore middleStore finalStore condition thenBranch elseBranch result} :
      Evaluates environment initialStore condition (.bool false) middleStore →
      Evaluates environment middleStore elseBranch result finalStore →
      Evaluates environment initialStore (.ifE condition thenBranch elseBranch) result finalStore

end Solcore.Resolved
