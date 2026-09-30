import Solcore.SourceSemantics.CoreLowering.CoreHelperInversion
import Solcore.SourceSemantics.CoreLowering.LoopExecution

/-! Finite invocation and recursive-edge inversion for the actual generated
while helper. The installed closure is supplied as an exact store lookup;
source simulation will obtain that lookup from the administrative frame. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.CoreProof

open Core Core.LocalLoop Core.LoopExecution

private theorem advance_weaken (type : Ty) (computation next : Expr) :
    (LocalLoop.advance type computation next).weakenAt 0 = LocalLoop.advance type (computation.weakenAt 0) (next.weakenAt 0) := by
  simpa only [Expr.rename_insertion] using LoopRenaming.advance type computation next (Renaming.insertion 0)

private theorem fallthrough_weaken (type : Ty) :
    (fallthrough type).weakenAt 0 = fallthrough type := by
  simp [fallthrough, LanguageResult.success, Expr.weakenAt]

private theorem invoke_weaken (type : Ty) (reference : Expr) (reason : Word) :
    (invoke type reference reason).weakenAt 0 = invoke type (reference.weakenAt 0) reason := by
  simpa only [Expr.rename_insertion] using LoopRenaming.invoke type reference reason (Renaming.insertion 0)

theorem EvaluationSize.loop_true_branch
    {size : Nat} {environment : Environment} {before middle after : Store} {type : Ty}
    {condition body post : Expr} {reason : Word} {result : Value}
    (evaluation : EvaluationSize size environment before (loopBody type condition body post reason) result after)
    (conditionEvaluation : Evaluates environment before (conditionCode condition) (.inRight .word (.bool true)) middle) :
    ∃ smaller, smaller < size ∧ EvaluationSize smaller (.bool true :: environment) middle
      (advance type (bodyCode body)
        ((advance type ((post.weakenAt 0).weakenAt 0) (invoke type (.var 1) reason)).weakenAt 0)) result after := by
  obtain ⟨smaller, decreased, branch⟩ := evaluation.choose_true conditionEvaluation
  exact ⟨smaller, decreased, by simpa only [advance_weaken, bodyCode] using branch⟩

private theorem post_fallthrough_next
    {size : Nat} {environment : Environment} {before after : Store} {type : Ty} {location : Location}
    {condition body : Expr} {reason : Word} {result : Value}
    (added : List Value)
    (installed : before.read? location = some (.inRight .unit
      (installedClosure type condition body (fallthrough type) reason location environment)))
    (evaluation : EvaluationSize size (added ++ entryEnvironment type location environment) before
      ((advance type ((fallthrough type).weakenAt 0 |>.weakenAt 0)
        (invoke type (.var 1) reason)).rename (fun index => index + added.length)) result after) :
    ∃ smaller, smaller < size ∧ EvaluationSize smaller (entryEnvironment type location environment) before
      (loopBody type condition body (fallthrough type) reason) result after := by
  rw [LoopRenaming.advance, fallthrough_weaken, fallthrough_weaken, LoopRenaming.fallthrough] at evaluation
  obtain ⟨next, decreased, invocation⟩ := evaluation.advance_fallthrough (fallthrough_evaluates _ _ _)
  simp [LoopRenaming.invoke, Expr.rename, invoke_weaken, Expr.weakenAt] at invocation
  obtain ⟨last, decreasedAgain, bodyEvaluation⟩ := invocation.invoke_body
    (body := loopBody type condition body (fallthrough type) reason)
    (captured := .cellRef (OptionalCell.cellType (functionType type)) location :: environment)
    (.var (by
      simpa [entryEnvironment, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        (List.getElem?_append_right (l₁ := added) (l₂ := entryEnvironment type location environment)
          (i := added.length + 1) (by omega)))) installed
  exact ⟨last, Nat.lt_trans decreasedAgain decreased, bodyEvaluation⟩

/-- After a body falls through, the only finite continuation invokes the exact
retained self closure with Unit. Its derivation is strictly smaller. -/
theorem EvaluationSize.loop_next_fallthrough
    {size : Nat} {environment : Environment} {before middle after : Store} {type : Ty} {location : Location}
    {condition body : Expr} {reason : Word} {result : Value}
    (evaluation : EvaluationSize size (bodyEnvironment type location environment) before
      (advance type (bodyCode body)
        ((advance type (((fallthrough type).weakenAt 0).weakenAt 0) (invoke type (.var 1) reason)).weakenAt 0)) result after)
    (bodyEvaluation : Evaluates (bodyEnvironment type location environment) before (bodyCode body) (fallthroughValue type) middle)
    (installed : middle.read? location = some (.inRight .unit
      (installedClosure type condition body (fallthrough type) reason location environment))) :
    ∃ smaller, smaller < size ∧ EvaluationSize smaller (entryEnvironment type location environment) middle
      (loopBody type condition body (fallthrough type) reason) result after := by
  obtain ⟨next, decreased, postEvaluation⟩ := evaluation.advance_fallthrough bodyEvaluation
  have renamed : EvaluationSize next
      ([.unit, .inLeft type .unit, .inLeft transferType (.inLeft type .unit), .bool true] ++ entryEnvironment type location environment)
      middle ((advance type ((fallthrough type).weakenAt 0 |>.weakenAt 0)
        (invoke type (.var 1) reason)).rename (fun index => index + 4)) result after := by
    simpa [← Expr.rename_insertion, Expr.rename_comp, Renaming.comp, Renaming.insertion, bodyEnvironment, Expr.rename] using postEvaluation
  obtain ⟨last, decreasedAgain, nextEvaluation⟩ := post_fallthrough_next
    [.unit, .inLeft type .unit, .inLeft transferType (.inLeft type .unit), .bool true] installed renamed
  exact ⟨last, Nat.lt_trans decreasedAgain decreased, nextEvaluation⟩

theorem EvaluationSize.loop_next_continuing
    {size : Nat} {environment : Environment} {before middle after : Store} {type : Ty} {location : Location}
    {condition body : Expr} {reason : Word} {result : Value}
    (evaluation : EvaluationSize size (bodyEnvironment type location environment) before
      (advance type (bodyCode body)
        ((advance type (((fallthrough type).weakenAt 0).weakenAt 0) (invoke type (.var 1) reason)).weakenAt 0)) result after)
    (bodyEvaluation : Evaluates (bodyEnvironment type location environment) before (bodyCode body) (continuingValue type) middle)
    (installed : middle.read? location = some (.inRight .unit
      (installedClosure type condition body (fallthrough type) reason location environment))) :
    ∃ smaller, smaller < size ∧ EvaluationSize smaller (entryEnvironment type location environment) middle
      (loopBody type condition body (fallthrough type) reason) result after := by
  obtain ⟨next, decreased, postEvaluation⟩ := evaluation.advance_continuing bodyEvaluation
  have renamed : EvaluationSize next
      ([.unit, .inRight .unit .unit, .inRight (LocalControl.controlType type) (.inRight .unit .unit), .bool true] ++ entryEnvironment type location environment)
      middle ((advance type ((fallthrough type).weakenAt 0 |>.weakenAt 0)
        (invoke type (.var 1) reason)).rename (fun index => index + 4)) result after := by
    simpa [← Expr.rename_insertion, Expr.rename_comp, Renaming.comp, Renaming.insertion, bodyEnvironment, Expr.rename] using postEvaluation
  obtain ⟨last, decreasedAgain, nextEvaluation⟩ := post_fallthrough_next
    [.unit, .inRight .unit .unit, .inRight (LocalControl.controlType type) (.inRight .unit .unit), .bool true] installed renamed
  exact ⟨last, Nat.lt_trans decreasedAgain decreased, nextEvaluation⟩

end Solcore.SourceSemantics.CoreLowering.CoreProof
