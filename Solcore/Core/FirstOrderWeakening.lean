import Solcore.Core.Renaming

/-! Exact environment insertion for finite evaluations with first-order results
and actual first-order final stores. General closure heaps still use relational
renaming: this lemma deliberately retains its final-store premise. -/

set_option autoImplicit false

namespace Solcore.Core

namespace Environment

def insertAt : Environment → Nat → Value → Environment
  | environment, 0, value => value :: environment
  | [], _ + 1, value => [value]
  | head :: tail, cutoff + 1, value => head :: insertAt tail cutoff value

end Environment

theorem EnvironmentsRelated.insertion (environment : Environment) (cutoff : Nat)
    (inserted : Value) :
    EnvironmentsRelated (Renaming.insertion cutoff) environment
      (Environment.insertAt environment cutoff inserted) := by
  induction environment generalizing cutoff with
  | nil => exact .empty _ _
  | cons head tail inductionHypothesis =>
      cases cutoff with
      | zero => exact .headInsertion inserted (head :: tail)
      | succ cutoff =>
          simpa [Environment.insertAt] using
            (inductionHypothesis cutoff).extend (ValuesRelated.refl head)

theorem Evaluates.weakenAt_cellPayload
    {definitions : DataEnvironment} {environment : Environment} {context : Context}
    {initialStore finalStore : Store} {world : StoreTyping}
    {expression : Expr} {result : Value} {type : Ty}
    (evaluation : Evaluates environment initialStore expression result finalStore)
    (typing : HasType context expression type definitions)
    (payload : CellPayload type)
    (environmentTyping : RuntimeEnvironmentHasTypes world environment context definitions)
    (storeTyping : RuntimeStoreHasTypes world initialStore definitions)
    {finalWorld : StoreTyping} (finalStoreTyping : StoreHasTypes finalWorld finalStore)
    (cutoff : Nat) (inserted : Value) :
    Evaluates (Environment.insertAt environment cutoff inserted) initialStore
      (expression.weakenAt cutoff) result finalStore := by
  obtain ⟨_, _, _, resultTyping⟩ :=
    evaluation_preserves_type evaluation typing environmentTyping storeTyping
  obtain ⟨targetResult, targetFinalStore, targetEvaluation,
      resultRelated, finalStoresRelated⟩ :=
    evaluation.rename (EnvironmentsRelated.insertion environment cutoff inserted)
      (StoresRelated.refl initialStore)
  have resultEquality : result = targetResult :=
    resultRelated.eq_of_cellPayload payload resultTyping.erase
  have storeEquality : finalStore = targetFinalStore :=
    finalStoresRelated.eq_of_hasTypes finalStoreTyping
  subst targetResult
  subst targetFinalStore
  simpa using targetEvaluation

end Solcore.Core
