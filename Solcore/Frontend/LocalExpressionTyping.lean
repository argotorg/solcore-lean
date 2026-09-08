import Solcore.Frontend.LocalExpression
import Solcore.Resolved.Typing

/-! Independent typing for the supported canonical local-expression fragment.
Conditionals require a Boolean condition and equally typed branches. Names and
local identities come from explicit caller tables; no literal meaning,
coercion, or typing rule for other canonical constructors is introduced. -/

set_option autoImplicit false

namespace Solcore.Frontend

inductive LocalExpressionHasType (table : LocalNameTable) (context : Resolved.Context) :
    Syntax.Expr → Core.Ty → Prop where
  | identifier {span : Syntax.SourceSpan} {name : Syntax.Identifier}
      {id : Resolved.LocalId} {type : Core.Ty}
      (named : LocalNameTable.Lookup table name.value id)
      (found : Resolved.LocalScope.Lookup context id type) :
      LocalExpressionHasType table context { span, value := .identifier name } type
  | group {span : Syntax.SourceSpan} {inner : Syntax.Expr} {type : Core.Ty}
      (typing : LocalExpressionHasType table context inner type) :
      LocalExpressionHasType table context { span, value := .group inner } type
  | conditional {span question colon : Syntax.SourceSpan}
      {condition thenBranch elseBranch : Syntax.Expr} {type : Core.Ty}
      (conditionTyped : LocalExpressionHasType table context condition .bool)
      (thenTyped : LocalExpressionHasType table context thenBranch type)
      (elseTyped : LocalExpressionHasType table context elseBranch type) :
      LocalExpressionHasType table context
        { span, value := .conditional condition question thenBranch colon elseBranch } type

/-- Resolve supported syntax, lower all references, and check the resulting
Core expression. Failure is adapter failure, not whole-language rejection. -/
def elaborateLocalExpression? (table : LocalNameTable) (context : Resolved.Context)
    (source : Syntax.Expr) : Option (Core.Expr × Core.Ty) := do
  let resolved ← resolveLocalExpression? table source
  let core ← resolved.lower? (Resolved.LocalScope.ids context)
  let type ← Core.infer? (Resolved.LocalScope.values context) core
  return (core, type)

end Solcore.Frontend
