import Solcore.Frontend.LocalFunctionApplication
import Solcore.Resolved.LocalFragmentProperties
import Solcore.Core.LocalFragmentInsertionPaths
import Solcore.Frontend.LocalFunctionApplicationStepComposition

/-! One caller insertion preserves the literal closure and argument returned
by the two local children. Both applications then invoke the same actual body
path and captures, choosing a common cost before the outer continuation. -/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Source provenance supplies child fragments, not a runtime context premise.
Each side retains its own caller frames; only the resulting value, store and
successful cost agree. The actual closure body need not be pure or typed. -/
theorem LocalFunctionApplicationElaborates.core_insertion_paths
    {table : LocalNameTable} {context : Resolved.Context} {source : Syntax.Expr}
    {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalFunctionApplicationElaborates table context source core type)
    (leading suffix : Core.Environment) (inserted : Core.Value)
    {initialStore finalStore : Core.Store} {value : Core.Value}
    (evaluation : Core.Evaluates (leading ++ suffix) initialStore core value finalStore) :
    ∃ cost, ∀ continuation,
      Core.Steps cost
        ⟨.eval core (leading ++ suffix), continuation, initialStore⟩
        ⟨.ret value, continuation, finalStore⟩ ∧
      Core.Steps cost
        ⟨.eval (core.weakenAt leading.length) (leading ++ inserted :: suffix), continuation, initialStore⟩
        ⟨.ret value, continuation, finalStore⟩ := by
  cases elaboration with
  | call _ functionLowered _ _ argumentLowered _ =>
      cases evaluation with
      | apply functionEvaluation argumentEvaluation bodyEvaluation =>
          obtain ⟨functionCost, functionPaths⟩ :=
            functionLowered.localFragment.insertion_paths leading suffix inserted functionEvaluation
          obtain ⟨argumentCost, argumentPaths⟩ :=
            argumentLowered.localFragment.insertion_paths leading suffix inserted argumentEvaluation
          obtain ⟨bodyCost, bodyPath⟩ := bodyEvaluation.toSteps
          refine ⟨functionCost + argumentCost + bodyCost + 3, fun continuation => ?_⟩
          constructor
          · exact CostStepComposition.apply (functionPaths _).1 (argumentPaths _).1 bodyPath
          · simp only [Core.Expr.weakenAt]
            exact CostStepComposition.apply (functionPaths _).2 (argumentPaths _).2 bodyPath

end Solcore.Frontend
