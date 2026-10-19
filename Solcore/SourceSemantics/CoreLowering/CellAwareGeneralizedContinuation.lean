import Solcore.SourceSemantics.CoreLowering.CompatibleStatementInitializedTree
import Solcore.SourceSemantics.CoreLowering.CoreHelperInversion

/-! The real emitted initializer and allocation expose a strictly smaller
native continuation, independently of the later Source grade. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareGeneralizedContinuation
open Core Frontend SourceInference ReadOnly CoreProof
open CompatibleStatementInitialized (sequence)

theorem smaller {actual : Environment} {store nextStore : Store}
    {embedding : Renaming} {initializer allocation body : Expr} {output : Ty}
    {value reference : Value}
    (initialized : Evaluates actual store (initializer.rename embedding) (.inRight .word value) store)
    (allocated : Evaluates (value :: actual) store (allocation.rename embedding.lift) reference nextStore)
    {size : Nat} {result : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store
      ((sequence output initializer allocation body).rename embedding) result finalStore) :
    ∃ tailSize, tailSize < size ∧
      EvaluationSize tailSize (reference :: value :: actual) nextStore
        (body.rename (Renaming.comp (Renaming.insertion 0) embedding).lift) result finalStore := by
  have bodyEq : (body.weakenAt 1).rename embedding.lift.lift =
      body.rename (Renaming.comp (Renaming.insertion 0) embedding).lift := by
    rw [← Expr.rename_insertion, Expr.rename_comp]
    congr 1
    funext index
    cases index <;> rfl
  have combined : EvaluationSize size actual store
      (LanguageResult.bind (LocalLoop.controlType output) (initializer.rename embedding)
        (.letE (allocation.rename embedding.lift) ((body.weakenAt 1).rename embedding.lift.lift)))
      result finalStore := by
    simpa only [sequence, LanguageResult.bind,
      Expr.rename, Renaming.lift] using completed
  obtain ⟨branchSize, branchSmaller, branch⟩ := combined.bind_success initialized
  obtain ⟨tailSize, tailSmaller, tail⟩ := branch.let_body allocated
  exact ⟨tailSize, Nat.lt_trans tailSmaller branchSmaller, bodyEq ▸ tail⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareGeneralizedContinuation
