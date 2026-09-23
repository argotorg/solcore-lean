import Solcore.Frontend.Computation
import Solcore.Frontend.RecursiveLocalComputation
import Solcore.Frontend.LocalComputation

/-! Concrete recursive-expression bodies instantiate the shared engine.
Their five operations and relations do not introduce parallel proof aliases. -/

set_option autoImplicit false

namespace Solcore.Frontend

abbrev elaborateRecursiveComputationReturnTree? :=
  elaborateComputationReturnTree? elaborateRecursiveLocalComputation?

abbrev RecursiveComputationReturnTreeHasType :=
  ComputationReturnTreeHasType RecursiveLocalComputationHasType

abbrev RecursiveComputationReturnTreeElaborates :=
  ComputationReturnTreeElaborates RecursiveLocalComputationElaborates

abbrev RecursiveComputationReturnTreeEvaluates :=
  ComputationReturnTreeEvaluates RecursiveLocalComputationEvaluates

abbrev RecursiveComputationReturnTreeEvaluatesWithCost :=
  ComputationReturnTreeEvaluatesWithCost RecursiveLocalComputationEvaluatesWithCost

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.RecursiveComputationReturnTreeEmbeddingProperties`
-/

/-! The old mixed-body evidence embeds one way on identical source and Core.
Actual bound values, stores and costs are retained, not inferred from types. -/

set_option autoImplicit false

namespace Solcore.Frontend

private theorem old_names_protected
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalComputationReturnTreeElaborates types owner inputs body core type)
    {names : List String} (included : names ⊆ inputs.names.map Prod.fst) :
    ComputationNamesProtected names body := by
  apply ComputationNamesProtected.subset (large := inputs.names.map Prod.fst) ?_ included
  clear included names
  induction elaboration with
  | bare | expression _ | block _ _ =>
      intro name exposed
      cases exposed with | tail impossible => cases impossible
  | binding meaning unused child tail ih | inferred unused child tail ih =>
      intro name exposed member
      cases exposed with
      | binding spelling => exact unused (spelling ▸ member)
      | tail exposed =>
          apply ih name exposed
          exact List.mem_cons_of_mem _ member
  | discard child tail ih =>
      intro name exposed
      cases exposed with | tail exposed => exact ih name exposed
  | conditional guard yes no yesIH noIH =>
      intro name exposed
      cases exposed with
      | tail impossible => cases impossible
      | thenBranch exposed => exact yesIH name exposed
      | elseBranch exposed => exact noIH name exposed

theorem LocalComputationReturnTreeElaborates.toRecursiveComputationReturnTree
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalComputationReturnTreeElaborates types owner inputs body core type) :
    RecursiveComputationReturnTreeElaborates types owner inputs body core type := by
  induction elaboration with
  | bare => exact .bare
  | expression child => exact .expression child.toRecursiveLocalComputation
  | block _ ih => exact .block ih
  | binding meaning unused child _ ih => exact .binding meaning child.toRecursiveLocalComputation ih
  | inferred unused child _ ih => exact .inferred child.toRecursiveLocalComputation ih
  | discard child _ ih => exact .discard child.toRecursiveLocalComputation ih
  | conditional guard yes _ yesIH noIH =>
      exact .conditional guard.toRecursiveLocalComputation
        (old_names_protected yes (by intro name member; exact member)) yesIH noIH

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
