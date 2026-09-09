import Solcore.Frontend.RecursiveComputationReturnTree
import Solcore.Frontend.RecursiveLocalComputationEmbeddingProperties
import Solcore.Frontend.LocalComputationReturnTree
import Solcore.Frontend.LocalComputationReturnTreeEvaluation

/-! The old mixed-body evidence embeds one way on identical source and Core.
Actual bound values, stores and costs are retained, not inferred from types. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem LocalComputationReturnTreeElaborates.toRecursiveComputationReturnTree
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalComputationReturnTreeElaborates types owner inputs body core type) :
    RecursiveComputationReturnTreeElaborates types owner inputs body core type := by
  induction elaboration with
  | bare => exact .bare
  | expression child => exact .expression child.toRecursiveLocalComputation
  | block _ ih => exact .block ih
  | binding meaning unused child _ ih => exact .binding meaning unused child.toRecursiveLocalComputation ih
  | inferred unused child _ ih => exact .inferred unused child.toRecursiveLocalComputation ih
  | discard child _ ih => exact .discard child.toRecursiveLocalComputation ih
  | conditional guard _ _ yesIH noIH => exact .conditional guard.toRecursiveLocalComputation yesIH noIH

theorem LocalComputationReturnTreeEvaluatesWithCost.toRecursiveComputationReturnTree
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : LocalComputationReturnTreeEvaluatesWithCost owner table environment
      initialStore body value finalStore cost) :
    RecursiveComputationReturnTreeEvaluatesWithCost owner table environment
      initialStore body value finalStore cost := by
  induction evaluation with
  | bare => exact .bare
  | expression child => exact .expression child.toRecursiveLocalComputation
  | block _ ih => exact .block ih
  | binding child _ ih => exact .binding child.toRecursiveLocalComputation ih
  | inferred child _ ih => exact .inferred child.toRecursiveLocalComputation ih
  | discard child _ ih => exact .discard child.toRecursiveLocalComputation ih
  | ifTrue guard _ ih => exact .ifTrue guard.toRecursiveLocalComputation ih
  | ifFalse guard _ ih => exact .ifFalse guard.toRecursiveLocalComputation ih

end Solcore.Frontend
