import Solcore.Frontend.RecursiveLocalComputation
import Solcore.Frontend.RecursiveLocalComputationEvaluation
import Solcore.Frontend.LocalComputation
import Solcore.Frontend.LocalComputationEvaluation

/-! Old successes embed on the same original syntax and actual values, stores
and costs. No old endpoint or stronger pure runtime contract is changed. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem LocalComputationElaborates.toRecursiveLocalComputation
    {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalComputationElaborates table context source core type) :
    RecursiveLocalComputationElaborates table context source core type := by
  cases elaboration with
  | pure resolution lowered typing => exact .pure resolution lowered typing
  | application child =>
      cases child with
      | call functionResolution functionLowered functionTyped argumentResolution argumentLowered argumentTyped =>
          exact .application (.pure functionResolution functionLowered functionTyped)
            (.pure argumentResolution argumentLowered argumentTyped)

theorem LocalComputationEvaluatesWithCost.toRecursiveLocalComputation
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {source : Syntax.Expr} {value : Core.Value} {cost : Nat}
    (evaluation : LocalComputationEvaluatesWithCost table environment initialStore source value finalStore cost) :
    RecursiveLocalComputationEvaluatesWithCost table environment initialStore source value finalStore cost := by
  cases evaluation with
  | pure child => exact .pure child
  | application child =>
      cases child with
      | call functionEvaluation argumentEvaluation bodyPath =>
          exact .application (.pure functionEvaluation) (.pure argumentEvaluation) bodyPath

end Solcore.Frontend
