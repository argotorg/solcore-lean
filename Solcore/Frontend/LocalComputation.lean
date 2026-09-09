import Solcore.Frontend.LocalFunctionApplication

/-! A nonrecursive union of the existing pure expression and root application
profiles. Original children are not reinterpreted recursively by this adapter. -/

set_option autoImplicit false

namespace Solcore.Frontend

def elaborateLocalComputation? (table : LocalNameTable) (context : Resolved.Context)
    (source : Syntax.Expr) : Option (Core.Expr × Core.Ty) :=
  match source.value with
  | .call _ _ => elaborateLocalFunctionApplication? table context source
  | _ => elaborateLocalExpression? table context source

inductive LocalComputationHasType (table : LocalNameTable) (context : Resolved.Context) :
    Syntax.Expr → Core.Ty → Prop where
  | pure {source : Syntax.Expr} {type : Core.Ty}
      (child : LocalExpressionHasType table context source type) :
      LocalComputationHasType table context source type
  | application {source : Syntax.Expr} {type : Core.Ty}
      (child : LocalFunctionApplicationHasType table context source type) :
      LocalComputationHasType table context source type

inductive LocalComputationElaborates (table : LocalNameTable) (context : Resolved.Context) :
    Syntax.Expr → Core.Expr → Core.Ty → Prop where
  | pure {source : Syntax.Expr} {resolved : Resolved.Expr} {core : Core.Expr} {type : Core.Ty}
      (resolution : ResolvesLocalExpression table source resolved)
      (lowered : Resolved.Lowers context.ids resolved core)
      (typing : Resolved.HasType context resolved type) :
      LocalComputationElaborates table context source core type
  | application {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
      (child : LocalFunctionApplicationElaborates table context source core type) :
      LocalComputationElaborates table context source core type

end Solcore.Frontend
