import Solcore.SourceSemantics.CoreLowering.TypedLexicalControlAllocation
import Solcore.SourceSemantics.CoreLowering.CoreHelperInversion

/-! An ordinary initializer may change the store before allocation. Both
continuation directions retain that reached store; failure skips allocation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareOrdinaryContinuation
open Core Frontend SourceInference ReadOnly CoreProof
open CompatibleStatementInitialized (sequence)

private theorem body_rename (body : Expr) (embedding : Renaming) :
    (body.weakenAt 1).rename embedding.lift.lift =
      body.rename (Renaming.comp (Renaming.insertion 0) embedding).lift := by
  rw [← Expr.rename_insertion, Expr.rename_comp]
  congr 1
  funext index
  cases index <;> rfl

theorem agreement {actual : Environment} {store middleStore nextStore : Store}
    {embedding : Renaming} {initializer allocation body : Expr} {output : Ty}
    {value reference : Value}
    (initialized : Evaluates actual store (initializer.rename embedding) (.inRight .word value) middleStore)
    (allocated : Evaluates (value :: actual) middleStore (allocation.rename embedding.lift) reference nextStore) :
    ContinuationAgreement actual store ((sequence output initializer allocation body).rename embedding)
      (reference :: value :: actual) nextStore
      (body.rename (Renaming.comp (Renaming.insertion 0) embedding).lift) := by
  have combined := (ContinuationAgreement.bind (type := LocalLoop.controlType output)
    (body := .letE (allocation.rename embedding.lift) ((body.weakenAt 1).rename embedding.lift.lift)) initialized).trans
    (ContinuationAgreement.letE allocated)
  simpa only [sequence, LanguageResult.bind, Expr.rename, body_rename, Renaming.lift] using combined

theorem smaller {actual : Environment} {store middleStore nextStore : Store}
    {embedding : Renaming} {initializer allocation body : Expr} {output : Ty}
    {value reference : Value}
    (initialized : Evaluates actual store (initializer.rename embedding) (.inRight .word value) middleStore)
    (allocated : Evaluates (value :: actual) middleStore (allocation.rename embedding.lift) reference nextStore)
    {size : Nat} {result : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store
      ((sequence output initializer allocation body).rename embedding) result finalStore) :
    ∃ tailSize, tailSize < size ∧ EvaluationSize tailSize (reference :: value :: actual) nextStore
      (body.rename (Renaming.comp (Renaming.insertion 0) embedding).lift) result finalStore := by
  have combined : EvaluationSize size actual store
      (LanguageResult.bind (LocalLoop.controlType output) (initializer.rename embedding)
        (.letE (allocation.rename embedding.lift) ((body.weakenAt 1).rename embedding.lift.lift)))
      result finalStore := by
    simpa only [sequence, LanguageResult.bind, Expr.rename, Renaming.lift] using completed
  obtain ⟨branchSize, branchSmaller, branch⟩ := combined.bind_success initialized
  obtain ⟨tailSize, tailSmaller, tail⟩ := branch.let_body allocated
  exact ⟨tailSize, Nat.lt_trans tailSmaller branchSmaller, body_rename body embedding ▸ tail⟩

theorem failure {actual : Environment} {store finalStore : Store}
    {embedding : Renaming} {initializer allocation body : Expr} {output payload : Ty} {reason : Word}
    (failed : Evaluates actual store (initializer.rename embedding) (.inLeft payload (.word reason)) finalStore) :
    Evaluates actual store ((sequence output initializer allocation body).rename embedding)
      (.inLeft (LocalLoop.controlType output) (.word reason)) finalStore := by
  rw [TypedLexicalControl.sequence_rename]
  exact LanguageResult.bind_failure _ failed

end Solcore.SourceSemantics.CoreLowering.CellAwareOrdinaryContinuation
