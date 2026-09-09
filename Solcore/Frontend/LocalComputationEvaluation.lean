import Solcore.Frontend.LocalFunctionApplicationEvaluation

/-! Raw successful computation and its exact child cost. The two original
profiles are disjoint at the root; these wrappers add no machine transitions. -/

set_option autoImplicit false

namespace Solcore.Frontend

inductive LocalComputationEvaluates
    (table : LocalNameTable) (environment : Resolved.Environment) :
    Core.Store → Syntax.Expr → Core.Value → Core.Store → Prop where
  | pure {initialStore finalStore : Core.Store} {source : Syntax.Expr} {value : Core.Value}
      (child : LocalExpressionEvaluates table environment initialStore source value finalStore) :
      LocalComputationEvaluates table environment initialStore source value finalStore
  | application {initialStore finalStore : Core.Store} {source : Syntax.Expr} {value : Core.Value}
      (child : LocalFunctionApplicationEvaluates table environment initialStore source value finalStore) :
      LocalComputationEvaluates table environment initialStore source value finalStore

inductive LocalComputationEvaluatesWithCost
    (table : LocalNameTable) (environment : Resolved.Environment) :
    Core.Store → Syntax.Expr → Core.Value → Core.Store → Nat → Prop where
  | pure {initialStore finalStore : Core.Store} {source : Syntax.Expr}
      {value : Core.Value} {cost : Nat}
      (child : LocalExpressionEvaluatesWithCost table environment initialStore source value finalStore cost) :
      LocalComputationEvaluatesWithCost table environment initialStore source value finalStore cost
  | application {initialStore finalStore : Core.Store} {source : Syntax.Expr}
      {value : Core.Value} {cost : Nat}
      (child : LocalFunctionApplicationEvaluatesWithCost table environment initialStore source value finalStore cost) :
      LocalComputationEvaluatesWithCost table environment initialStore source value finalStore cost

end Solcore.Frontend
