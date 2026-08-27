import Solcore.Core.RenamingEval
import Solcore.Core.RenamingSafety

set_option autoImplicit false

namespace Solcore.Core

/--
Weakening a typed expression at the outermost context position is exact for
cell-payload result types. The inserted runtime value is completely arbitrary:
the original free variables are shifted past it, so no typing assumption on the
new head is required.
-/
theorem Evaluates.weakenAt_zero_cellPayload
    {definitions : DataEnvironment}
    {environment : Environment} {context : Context}
    {initialStore finalStore : Store} {world : StoreTyping}
    {expr : Expr} {result : Value} {type : Ty}
    (evaluation :
      Evaluates environment initialStore expr result finalStore)
    (typing : HasType context expr type definitions)
    (payload : CellPayload type)
    (environmentTyping :
      RuntimeEnvironmentHasTypes world environment context definitions)
    (storeTyping : StoreHasTypes world initialStore)
    (inserted : Value) :
    Evaluates (inserted :: environment) initialStore
      (expr.weakenAt 0) result finalStore := by
  obtain ⟨finalWorld, _, finalStoreTyping, resultTyping⟩ :=
    evaluation_preserves_type evaluation typing environmentTyping storeTyping
  obtain ⟨targetResult, targetFinalStore, targetEvaluation,
      resultRelated, finalStoresRelated⟩ :=
    evaluation.rename
      (EnvironmentsRelated.headInsertion inserted environment)
      (StoresRelated.refl initialStore)
  have resultEquality : result = targetResult :=
    resultRelated.eq_of_cellPayload payload resultTyping.erase
  have storeEquality : finalStore = targetFinalStore :=
    finalStoresRelated.eq_of_hasTypes finalStoreTyping
  subst targetResult
  subst targetFinalStore
  simpa using targetEvaluation

theorem Evaluates.weakenAt_zero_word
    {definitions : DataEnvironment}
    {environment : Environment} {context : Context}
    {initialStore finalStore : Store} {world : StoreTyping}
    {expr : Expr} {result : Word}
    (evaluation :
      Evaluates environment initialStore expr (.word result) finalStore)
    (typing : HasType context expr .word definitions)
    (environmentTyping :
      RuntimeEnvironmentHasTypes world environment context definitions)
    (storeTyping : StoreHasTypes world initialStore)
    (inserted : Value) :
    Evaluates (inserted :: environment) initialStore
      (expr.weakenAt 0) (.word result) finalStore :=
  evaluation.weakenAt_zero_cellPayload typing .word
    environmentTyping storeTyping inserted

end Solcore.Core
