import Solcore.Frontend.LocalInputsRenaming
import Solcore.Frontend.LocalInputsExecution
import Solcore.Frontend.LocalExpressionRenamingSemantics

/-! Identity relabeling leaves checked Core and runtime value lists unchanged.
The runner agrees at identical fuel, including its entire suspended state. -/

set_option autoImplicit false

namespace Solcore.Frontend.LocalInputs

theorem check?_mapIds (inputs : LocalInputs) (mapping : Resolved.LocalId → Resolved.LocalId)
    (injective : Function.Injective mapping) (source : Syntax.Expr) :
    (inputs.mapIds mapping injective).check? source = inputs.check? source := by
  simp only [check?, mapIds_names, mapIds_context, elaborateLocalExpression?_mapIds mapping injective]

/-- No successful checking or sufficient fuel premise: both absent and all
present results, including exact out-of-fuel states, are unchanged. -/
theorem run?_mapIds (inputs : LocalInputs) (mapping : Resolved.LocalId → Resolved.LocalId)
    (injective : Function.Injective mapping) (fuel : Nat) (source : Syntax.Expr) (store : Core.Store) :
    (inputs.mapIds mapping injective).run? fuel source store = inputs.run? fuel source store := by
  simp only [run?, check?_mapIds, mapIds_environment, Resolved.LocalScope.values_mapIds]

theorem hasType_mapIds_iff (inputs : LocalInputs) (mapping : Resolved.LocalId → Resolved.LocalId)
    (injective : Function.Injective mapping) {source : Syntax.Expr} {type : Core.Ty} :
    LocalExpressionHasType (inputs.mapIds mapping injective).names
        (inputs.mapIds mapping injective).context source type ↔
      LocalExpressionHasType inputs.names inputs.context source type := by
  simp only [mapIds_names, mapIds_context, localExpressionHasType_mapIds_iff mapping injective]

theorem evaluates_mapIds_iff (inputs : LocalInputs) (mapping : Resolved.LocalId → Resolved.LocalId)
    (injective : Function.Injective mapping) {source : Syntax.Expr} {value : Core.Value}
    {initialStore finalStore : Core.Store} :
    LocalExpressionEvaluates (inputs.mapIds mapping injective).names
        (inputs.mapIds mapping injective).environment initialStore source value finalStore ↔
      LocalExpressionEvaluates inputs.names inputs.environment initialStore source value finalStore := by
  simp only [mapIds_names, mapIds_environment, localExpressionEvaluates_mapIds_iff mapping injective]

end Solcore.Frontend.LocalInputs
