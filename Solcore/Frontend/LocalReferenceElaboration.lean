import Solcore.Frontend.LocalReference
import Solcore.Resolved.Typing

set_option autoImplicit false

namespace Solcore.Frontend

/-- Resolve a supported canonical reference, locate its identity in the supplied
context, and return its Core variable and type. `none` is adapter failure, not a
source-language rejection. No identity receives a default index or type. -/
def elaborateLocalReference? (table : LocalNameTable) (context : Resolved.Context)
    (source : Syntax.Expr) : Option (Core.Expr × Core.Ty) := do
  let resolved ← resolveLocalReference? table source
  let core ← resolved.lower? (Resolved.LocalScope.ids context)
  let type ← Core.infer? (Resolved.LocalScope.values context) core
  return (core, type)

/-- Independent typing of the supported canonical reference fragment against
two explicit first-match tables. No lexical validity or source shadowing policy
is assumed, and no typing rule for unsupported expression forms is introduced. -/
inductive LocalReferenceHasType (table : LocalNameTable) (context : Resolved.Context) :
    Syntax.Expr → Core.Ty → Prop where
  | resolved {source : Syntax.Expr} {id : Resolved.LocalId} {type : Core.Ty}
      (reference : ResolvesLocalReference table source id)
      (found : Resolved.LocalScope.Lookup context id type) :
      LocalReferenceHasType table context source type

end Solcore.Frontend
