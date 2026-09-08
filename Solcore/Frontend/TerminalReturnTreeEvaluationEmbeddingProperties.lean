import Solcore.Frontend.TerminalReturnTreeEvaluation
import Solcore.Frontend.TerminalReturnBodyEvaluation

/-! Every old selected-path derivation embeds with the original value, stores
and cost. Whole checking and evaluation of an unselected arm are not required. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem ReturnBodyEvaluates.returnTree
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value}
    (evaluation : ReturnBodyEvaluates table environment initialStore body value finalStore) :
    TerminalReturnTreeEvaluates table environment initialStore body value finalStore := .single evaluation

theorem ReturnBodyEvaluatesWithCost.returnTree
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : ReturnBodyEvaluatesWithCost table environment initialStore body value finalStore cost) :
    TerminalReturnTreeEvaluatesWithCost table environment initialStore body value finalStore cost := .single evaluation

theorem ConditionalReturnBodyEvaluates.returnTree
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value}
    (evaluation : ConditionalReturnBodyEvaluates table environment initialStore body value finalStore) :
    TerminalReturnTreeEvaluates table environment initialStore body value finalStore := by
  cases evaluation with
  | ifTrue condition branch => exact .ifTrue condition branch.returnTree
  | ifFalse condition branch => exact .ifFalse condition branch.returnTree

theorem ConditionalReturnBodyEvaluatesWithCost.returnTree
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : ConditionalReturnBodyEvaluatesWithCost table environment initialStore body value finalStore cost) :
    TerminalReturnTreeEvaluatesWithCost table environment initialStore body value finalStore cost := by
  cases evaluation with
  | ifTrue condition branch => exact .ifTrue condition branch.returnTree
  | ifFalse condition branch => exact .ifFalse condition branch.returnTree

theorem TerminalReturnBodyEvaluates.returnTree
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value}
    (evaluation : TerminalReturnBodyEvaluates table environment initialStore body value finalStore) :
    TerminalReturnTreeEvaluates table environment initialStore body value finalStore := by
  cases evaluation with
  | single child => exact child.returnTree
  | conditional child => exact child.returnTree

theorem TerminalReturnBodyEvaluatesWithCost.returnTree
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : TerminalReturnBodyEvaluatesWithCost table environment initialStore body value finalStore cost) :
    TerminalReturnTreeEvaluatesWithCost table environment initialStore body value finalStore cost := by
  cases evaluation with
  | single child => exact child.returnTree
  | conditional child => exact child.returnTree

end Solcore.Frontend
