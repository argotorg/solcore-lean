import Solcore.Frontend.TypedLetReturnTreeEvaluation
import Solcore.Frontend.TypedLetReturnBodyEvaluation

/-! Old selected paths embed with their exact value, stores and cost.
No annotation meaning, runtime typing or whole-source acceptance is added. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem TerminalReturnTreeEvaluates.typedLetReturnTree
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value}
    (evaluation : TerminalReturnTreeEvaluates table environment initialStore body value finalStore)
    (owner : Resolved.DeclarationId) :
    TypedLetReturnTreeEvaluates owner table environment initialStore body value finalStore := by
  induction evaluation with
  | single child => exact .single child
  | ifTrue condition _ ih => exact .ifTrue condition ih
  | ifFalse condition _ ih => exact .ifFalse condition ih

theorem TerminalReturnTreeEvaluatesWithCost.typedLetReturnTree
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : TerminalReturnTreeEvaluatesWithCost table environment initialStore body value finalStore cost)
    (owner : Resolved.DeclarationId) :
    TypedLetReturnTreeEvaluatesWithCost owner table environment initialStore body value finalStore cost := by
  induction evaluation with
  | single child => exact .single child
  | ifTrue condition _ ih => exact .ifTrue condition ih
  | ifFalse condition _ ih => exact .ifFalse condition ih

theorem TypedLetReturnBodyEvaluates.returnTree
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value}
    (evaluation : TypedLetReturnBodyEvaluates owner table environment initialStore body value finalStore) :
    TypedLetReturnTreeEvaluates owner table environment initialStore body value finalStore := by
  induction evaluation with
  | terminal child => exact child.typedLetReturnTree owner
  | binding initializer _ ih => exact .binding initializer ih

theorem TypedLetReturnBodyEvaluatesWithCost.returnTree
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : TypedLetReturnBodyEvaluatesWithCost owner table environment initialStore body value finalStore cost) :
    TypedLetReturnTreeEvaluatesWithCost owner table environment initialStore body value finalStore cost := by
  induction evaluation with
  | terminal child => exact child.typedLetReturnTree owner
  | binding initializer _ ih => exact .binding initializer ih

end Solcore.Frontend
