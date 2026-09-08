import Solcore.Resolved.Expr
import Solcore.Core.Typing

set_option autoImplicit false

namespace Solcore.Resolved

abbrev Context := LocalScope Core.Ty

/-- Source-independent typing over resolved local identities. -/
inductive HasType : Context → Expr → Core.Ty → Prop where
  | unit {context} : HasType context .unit .unit
  | bool {context value} : HasType context (.bool value) .bool
  | word {context value} : HasType context (.word value) .word
  | var {context id type} :
      LocalScope.Lookup context id type → HasType context (.var id) type
  | unary {context op operand} :
      HasType context operand op.operandType →
      HasType context (.unary op operand) op.resultType
  | binary {context op left right} :
      HasType context left op.leftType → HasType context right op.rightType →
      HasType context (.binary op left right) op.resultType
  | letE {context binder value body valueType bodyType} :
      HasType context value valueType →
      HasType ((binder, valueType) :: context) body bodyType →
      HasType context (.letE binder value body) bodyType
  | ifE {context condition thenBranch elseBranch type} :
      HasType context condition .bool → HasType context thenBranch type →
      HasType context elseBranch type →
      HasType context (.ifE condition thenBranch elseBranch) type

/-- A total checker for this fragment, reusing only the existing Core checker. -/
def infer? (context : Context) (expr : Expr) : Option Core.Ty := do
  let core ← expr.lower? (LocalScope.ids context)
  Core.infer? (LocalScope.values context) core

end Solcore.Resolved
