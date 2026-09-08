import Solcore.Frontend.TypedLetReturnBodyEvaluation

/-! Existing tree paths embed without changing their stores, values or costs.
Neither acceptance nor evaluation of unselected source is required. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem TerminalReturnTreeEvaluates.typedLetReturnBody
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value}
    (evaluation : TerminalReturnTreeEvaluates table environment initialStore body value finalStore)
    (owner : Resolved.DeclarationId) :
    TypedLetReturnBodyEvaluates owner table environment initialStore body value finalStore := .terminal evaluation

theorem TerminalReturnTreeEvaluatesWithCost.typedLetReturnBody
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : TerminalReturnTreeEvaluatesWithCost table environment initialStore body value finalStore cost)
    (owner : Resolved.DeclarationId) :
    TypedLetReturnBodyEvaluatesWithCost owner table environment initialStore body value finalStore cost := .terminal evaluation

end Solcore.Frontend
