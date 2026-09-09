import Solcore.Frontend.LocalComputation
import Solcore.Frontend.LocalFunctionApplicationInsertionProperties
import Solcore.Frontend.LocalFunctionApplicationInsertionPaths

/-! The two computation branches share exact caller-insertion kernels.
These are leaf facts; enclosing body scopes still require their own induction. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem LocalComputationElaborates.core_hasType_insert_iff
    {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalComputationElaborates table context source core type)
    (leading suffix : Core.Context) (inserted : Core.Ty)
    {requestedType : Core.Ty} {definitions : Core.DataEnvironment} :
    Core.HasType (leading ++ inserted :: suffix) (core.weakenAt leading.length)
      requestedType definitions ↔
    Core.HasType (leading ++ suffix) core requestedType definitions := by
  cases elaboration with
  | pure _ lowered _ => exact lowered.localFragment.hasType_insert_iff leading suffix inserted
  | application child => exact child.core_hasType_insert_iff leading suffix inserted

theorem LocalComputationElaborates.core_evaluates_insert_iff
    {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalComputationElaborates table context source core type)
    (leading suffix : Core.Environment) (inserted : Core.Value)
    {initialStore finalStore : Core.Store} {value : Core.Value} :
    Core.Evaluates (leading ++ inserted :: suffix) initialStore
      (core.weakenAt leading.length) value finalStore ↔
    Core.Evaluates (leading ++ suffix) initialStore core value finalStore := by
  cases elaboration with
  | pure _ lowered _ => exact lowered.localFragment.evaluates_insert_iff leading suffix inserted
  | application child => exact child.core_evaluates_insert_iff leading suffix inserted

theorem LocalComputationElaborates.core_insertion_paths
    {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalComputationElaborates table context source core type)
    (leading suffix : Core.Environment) (inserted : Core.Value)
    {initialStore finalStore : Core.Store} {value : Core.Value}
    (evaluation : Core.Evaluates (leading ++ suffix) initialStore core value finalStore) :
    ∃ cost, ∀ continuation,
      Core.Steps cost
        ⟨.eval core (leading ++ suffix), continuation, initialStore⟩
        ⟨.ret value, continuation, finalStore⟩ ∧
      Core.Steps cost
        ⟨.eval (core.weakenAt leading.length) (leading ++ inserted :: suffix),
          continuation, initialStore⟩
        ⟨.ret value, continuation, finalStore⟩ := by
  cases elaboration with
  | pure _ lowered _ => exact lowered.localFragment.insertion_paths leading suffix inserted evaluation
  | application child => exact child.core_insertion_paths leading suffix inserted evaluation

end Solcore.Frontend
