import Solcore.Frontend.LocalComputationReturnTree
import Solcore.Frontend.TypedLetReturnTree

/-! Old pure provenance embeds with exactly the same syntax, scope, Core and
type. This one-way proof changes no old checker and uses no old runtime law. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem TypedLetReturnTreeElaborates.toLocalComputationReturnTree
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : TypedLetReturnTreeElaborates types owner inputs body core type) :
    LocalComputationReturnTreeElaborates types owner inputs body core type := by
  induction elaboration with
  | single child =>
      cases child with
      | bare => exact .bare
      | expression resolution lowered typing => exact .expression (.pure resolution lowered typing)
  | block _ ih => exact .block ih
  | binding meaning unused resolution lowered typing _ ih =>
      exact .binding meaning unused
        (.pure resolution (by simpa only [LocalTypeInputs.context_ids] using lowered) typing) ih
  | inferred unused resolution lowered typing _ ih =>
      exact .inferred unused
        (.pure resolution (by simpa only [LocalTypeInputs.context_ids] using lowered) typing) ih
  | discard resolution lowered typing _ ih =>
      exact .discard
        (.pure resolution (by simpa only [LocalTypeInputs.context_ids] using lowered) typing) ih
  | conditional resolution lowered typing _ _ thenIH elseIH =>
      exact .conditional
        (.pure resolution (by simpa only [LocalTypeInputs.context_ids] using lowered) typing) thenIH elseIH

end Solcore.Frontend
