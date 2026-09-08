import Solcore.Frontend.ConditionalReturnBodyEvaluationProperties

/-! A nonrecursive union of existing raw return-body semantics. The wrapper
adds no source control operation, value conversion, store effect or cost. -/

set_option autoImplicit false

namespace Solcore.Frontend

inductive TerminalReturnBodyEvaluates (table : LocalNameTable) (environment : Resolved.Environment) :
    Core.Store → Syntax.Block → Core.Value → Core.Store → Prop where
  | single {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value}
      (child : ReturnBodyEvaluates table environment initialStore body value finalStore) :
      TerminalReturnBodyEvaluates table environment initialStore body value finalStore
  | conditional {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value}
      (child : ConditionalReturnBodyEvaluates table environment initialStore body value finalStore) :
      TerminalReturnBodyEvaluates table environment initialStore body value finalStore

inductive TerminalReturnBodyEvaluatesWithCost (table : LocalNameTable) (environment : Resolved.Environment) :
    Core.Store → Syntax.Block → Core.Value → Core.Store → Nat → Prop where
  | single {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
      (child : ReturnBodyEvaluatesWithCost table environment initialStore body value finalStore cost) :
      TerminalReturnBodyEvaluatesWithCost table environment initialStore body value finalStore cost
  | conditional {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
      (child : ConditionalReturnBodyEvaluatesWithCost table environment initialStore body value finalStore cost) :
      TerminalReturnBodyEvaluatesWithCost table environment initialStore body value finalStore cost

end Solcore.Frontend
