import Solcore.Frontend.LocalFunctionApplication
import Solcore.Resolved.LocalFragmentProperties
import Solcore.Core.LocalFragment

/-! Exact application provenance supplies its two local child fragments.
Insertion changes only caller positions, not actual closure bodies or captures.
The arbitrary runtime environment and typing context need not match the source. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem LocalFunctionApplicationElaborates.core_evaluates_insert_iff
    {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalFunctionApplicationElaborates table context source core type)
    (leading suffix : Core.Environment) (inserted : Core.Value)
    {initialStore finalStore : Core.Store} {value : Core.Value} :
    Core.Evaluates (leading ++ inserted :: suffix) initialStore
      (core.weakenAt leading.length) value finalStore ↔
      Core.Evaluates (leading ++ suffix) initialStore core value finalStore := by
  cases elaboration with
  | call _ functionLowered _ _ argumentLowered _ =>
      simp only [Core.Expr.weakenAt]
      constructor
      · intro evaluation
        cases evaluation with
        | apply functionEvaluation argumentEvaluation bodyEvaluation =>
            exact .apply
              ((functionLowered.localFragment.evaluates_insert_iff leading suffix inserted).mp functionEvaluation)
              ((argumentLowered.localFragment.evaluates_insert_iff leading suffix inserted).mp argumentEvaluation)
              bodyEvaluation
      · intro evaluation
        cases evaluation with
        | apply functionEvaluation argumentEvaluation bodyEvaluation =>
            exact .apply
              ((functionLowered.localFragment.evaluates_insert_iff leading suffix inserted).mpr functionEvaluation)
              ((argumentLowered.localFragment.evaluates_insert_iff leading suffix inserted).mpr argumentEvaluation)
              bodyEvaluation

theorem LocalFunctionApplicationElaborates.core_hasType_insert_iff
    {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalFunctionApplicationElaborates table context source core type)
    (leading suffix : Core.Context) (inserted : Core.Ty)
    {requestedType : Core.Ty} {definitions : Core.DataEnvironment} :
    Core.HasType (leading ++ inserted :: suffix) (core.weakenAt leading.length) requestedType definitions ↔
      Core.HasType (leading ++ suffix) core requestedType definitions := by
  cases elaboration with
  | call _ functionLowered _ _ argumentLowered _ =>
      simp only [Core.Expr.weakenAt]
      constructor
      · intro typing
        cases typing with
        | apply functionTyping argumentTyping =>
            exact .apply
              ((functionLowered.localFragment.hasType_insert_iff leading suffix inserted).mp functionTyping)
              ((argumentLowered.localFragment.hasType_insert_iff leading suffix inserted).mp argumentTyping)
      · intro typing
        cases typing with
        | apply functionTyping argumentTyping =>
            exact .apply
              ((functionLowered.localFragment.hasType_insert_iff leading suffix inserted).mpr functionTyping)
              ((argumentLowered.localFragment.hasType_insert_iff leading suffix inserted).mpr argumentTyping)

end Solcore.Frontend
