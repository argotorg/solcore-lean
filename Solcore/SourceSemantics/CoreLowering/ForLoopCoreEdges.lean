import Solcore.SourceSemantics.CoreLowering.LoopCoreInversion

/-! Concrete execution and strictly decreasing inversion at the post edge of
an installed for closure. The supplied post execution is evaluated after the
body and before the exact retained self closure is invoked. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.CoreProof

open Core Core.LocalLoop Core.LoopExecution

namespace ForLoop

private theorem insertion_zero : Renaming.insertion 0 = (fun index => index + 1) := by
  funext index
  simp [Renaming.insertion]

private theorem shift_comp (left right : Nat) :
    Renaming.comp (fun index => index + left) (fun index => index + right) =
      (fun index => index + (right + left)) := by
  funext index
  simp [Renaming.comp, Nat.add_assoc]

def fallthroughPrefix (type : Ty) : List Value :=
  [.unit, .inLeft type .unit, .inLeft transferType (.inLeft type .unit), .bool true]

def continuingPrefix (type : Ty) : List Value :=
  [.unit, .inRight .unit .unit, .inRight (LocalControl.controlType type) (.inRight .unit .unit), .bool true]

def postCode (post : Expr) : Expr :=
  (conditionCode post).rename (fun index => index + 4)

theorem postCode_eq (post : Expr) :
    postCode post = ((((((post.weakenAt 0).weakenAt 0).weakenAt 0).weakenAt 0).weakenAt 0).weakenAt 0) := by
  simp only [postCode, conditionCode, ← Expr.rename_insertion, Expr.rename_comp]
  congr 1

private theorem advance_weaken (type : Ty) (computation next : Expr) :
    (LocalLoop.advance type computation next).weakenAt 0 =
      LocalLoop.advance type (computation.weakenAt 0) (next.weakenAt 0) := by
  simpa only [Expr.rename_insertion] using LoopRenaming.advance type computation next (Renaming.insertion 0)

private theorem invoke_weaken (type : Ty) (reference : Expr) (reason : Word) :
    (invoke type reference reason).weakenAt 0 = invoke type (reference.weakenAt 0) reason := by
  simpa only [Expr.rename_insertion] using LoopRenaming.invoke type reference reason (Renaming.insertion 0)

/-- A successful post reaches the exact installed closure, with its captured
lexical environment restored rather than any post-local bindings. -/
theorem post_invokes
    {environment : Environment} {before middle after : Store} {type : Ty} {location : Location}
    {condition body post : Expr} {reason : Word} {result : Value}
    (added : List Value)
    (postEvaluation : Evaluates (added ++ entryEnvironment type location environment) before
      ((conditionCode post).rename (fun index => index + added.length)) (fallthroughValue type) middle)
    (installed : middle.read? location = some (.inRight .unit
      (installedClosure type condition body post reason location environment)))
    (next : Evaluates (entryEnvironment type location environment) middle
      (loopBody type condition body post reason) result after) :
    Evaluates (added ++ entryEnvironment type location environment) before
      ((advance type (conditionCode post) (invoke type (.var 1) reason)).rename
        (fun index => index + added.length)) result after := by
  rw [LoopRenaming.advance]
  apply advance_fallthrough _ postEvaluation
  simp [LoopRenaming.invoke, Expr.rename, invoke_weaken, Expr.weakenAt]
  apply invoke_success _ _ (.var ?_) installed next
  simpa [entryEnvironment, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    (List.getElem?_append_right (l₁ := added) (l₂ := entryEnvironment type location environment)
      (i := added.length + 1) (by omega))

/-- The recursive body derivation after a successful post is strictly smaller
than the enclosing post/advance derivation. -/
theorem post_next
    {size : Nat} {environment : Environment} {before middle after : Store} {type : Ty} {location : Location}
    {condition body post : Expr} {reason : Word} {result : Value}
    (added : List Value)
    (postEvaluation : Evaluates (added ++ entryEnvironment type location environment) before
      ((conditionCode post).rename (fun index => index + added.length)) (fallthroughValue type) middle)
    (installed : middle.read? location = some (.inRight .unit
      (installedClosure type condition body post reason location environment)))
    (evaluation : EvaluationSize size (added ++ entryEnvironment type location environment) before
      ((advance type (conditionCode post) (invoke type (.var 1) reason)).rename
        (fun index => index + added.length)) result after) :
    ∃ smaller, smaller < size ∧ EvaluationSize smaller (entryEnvironment type location environment) middle
      (loopBody type condition body post reason) result after := by
  rw [LoopRenaming.advance] at evaluation
  obtain ⟨next, decreased, invocation⟩ := evaluation.advance_fallthrough postEvaluation
  simp [LoopRenaming.invoke, Expr.rename, invoke_weaken, Expr.weakenAt] at invocation
  obtain ⟨last, decreasedAgain, bodyEvaluation⟩ := invocation.invoke_body
    (body := loopBody type condition body post reason)
    (captured := .cellRef (OptionalCell.cellType (functionType type)) location :: environment)
    (.var (by
      simpa [entryEnvironment, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        (List.getElem?_append_right (l₁ := added) (l₂ := entryEnvironment type location environment)
          (i := added.length + 1) (by omega)))) installed
  exact ⟨last, Nat.lt_trans decreasedAgain decreased, bodyEvaluation⟩

theorem body_fallthrough
    {environment : Environment} {before middle bodyStore postStore after : Store} {type : Ty} {location : Location}
    {condition body post : Expr} {reason : Word} {result : Value}
    (conditionEvaluation : Evaluates (entryEnvironment type location environment) before (conditionCode condition)
      (.inRight .word (.bool true)) middle)
    (bodyEvaluation : Evaluates (bodyEnvironment type location environment) middle (bodyCode body)
      (fallthroughValue type) bodyStore)
    (postEvaluation : Evaluates (fallthroughPrefix type ++ entryEnvironment type location environment) bodyStore
      (postCode post) (fallthroughValue type) postStore)
    (installed : postStore.read? location = some (.inRight .unit
      (installedClosure type condition body post reason location environment)))
    (next : Evaluates (entryEnvironment type location environment) postStore
      (loopBody type condition body post reason) result after) :
    Evaluates (entryEnvironment type location environment) before
      (loopBody type condition body post reason) result after := by
  apply LocalControl.choose_true _ conditionEvaluation
  rw [advance_weaken]
  apply advance_fallthrough _ bodyEvaluation
  have composed := post_invokes (fallthroughPrefix type) postEvaluation installed next
  simp [← Expr.rename_insertion, Expr.rename_comp, bodyEnvironment, Expr.rename, fallthroughPrefix, conditionCode] at composed ⊢
  simpa only [insertion_zero, shift_comp, Nat.reduceAdd] using composed

theorem body_fallthrough_post_fault
    {environment : Environment} {before middle bodyStore after : Store} {type : Ty} {location : Location}
    {condition body post : Expr} {selfReason reason : Word}
    (conditionEvaluation : Evaluates (entryEnvironment type location environment) before (conditionCode condition)
      (.inRight .word (.bool true)) middle)
    (bodyEvaluation : Evaluates (bodyEnvironment type location environment) middle (bodyCode body)
      (fallthroughValue type) bodyStore)
    (postEvaluation : Evaluates (fallthroughPrefix type ++ entryEnvironment type location environment) bodyStore
      (postCode post) (.inLeft (controlType type) (.word reason)) after) :
    Evaluates (entryEnvironment type location environment) before
      (loopBody type condition body post selfReason) (.inLeft (controlType type) (.word reason)) after := by
  apply LocalControl.choose_true _ conditionEvaluation
  rw [advance_weaken]
  apply advance_fallthrough _ bodyEvaluation
  have failed := advance_failure
    (next := (invoke type (.var 1) selfReason).rename (fun index => index + 4)) type postEvaluation
  simp only [postCode] at failed
  rw [← LoopRenaming.advance] at failed
  simp [← Expr.rename_insertion, Expr.rename_comp, bodyEnvironment, Expr.rename, fallthroughPrefix, conditionCode] at failed ⊢
  simpa only [insertion_zero, shift_comp, Nat.reduceAdd] using failed

theorem next_fallthrough
    {size : Nat} {environment : Environment} {before bodyStore postStore after : Store} {type : Ty} {location : Location}
    {condition body post : Expr} {reason : Word} {result : Value}
    (evaluation : EvaluationSize size (bodyEnvironment type location environment) before
      (advance type (bodyCode body)
        ((advance type (conditionCode post) (invoke type (.var 1) reason)).weakenAt 0)) result after)
    (bodyEvaluation : Evaluates (bodyEnvironment type location environment) before
      (bodyCode body) (fallthroughValue type) bodyStore)
    (postEvaluation : Evaluates (fallthroughPrefix type ++ entryEnvironment type location environment) bodyStore
      (postCode post) (fallthroughValue type) postStore)
    (installed : postStore.read? location = some (.inRight .unit
      (installedClosure type condition body post reason location environment))) :
    ∃ smaller, smaller < size ∧ EvaluationSize smaller (entryEnvironment type location environment) postStore
      (loopBody type condition body post reason) result after := by
  obtain ⟨next, decreased, postAdvance⟩ := evaluation.advance_fallthrough bodyEvaluation
  have renamed : EvaluationSize next
      (fallthroughPrefix type ++ entryEnvironment type location environment) bodyStore
      ((advance type (conditionCode post) (invoke type (.var 1) reason)).rename
        (fun index => index + 4)) result after := by
    simp [← Expr.rename_insertion, Expr.rename_comp, bodyEnvironment, Expr.rename, fallthroughPrefix] at postAdvance ⊢
    simpa only [insertion_zero, shift_comp, Nat.reduceAdd] using postAdvance
  obtain ⟨last, decreasedAgain, nextEvaluation⟩ := post_next (fallthroughPrefix type) postEvaluation installed renamed
  exact ⟨last, Nat.lt_trans decreasedAgain decreased, nextEvaluation⟩

theorem body_continuing
    {environment : Environment} {before middle bodyStore postStore after : Store} {type : Ty} {location : Location}
    {condition body post : Expr} {reason : Word} {result : Value}
    (conditionEvaluation : Evaluates (entryEnvironment type location environment) before (conditionCode condition)
      (.inRight .word (.bool true)) middle)
    (bodyEvaluation : Evaluates (bodyEnvironment type location environment) middle (bodyCode body)
      (continuingValue type) bodyStore)
    (postEvaluation : Evaluates (continuingPrefix type ++ entryEnvironment type location environment) bodyStore
      (postCode post) (fallthroughValue type) postStore)
    (installed : postStore.read? location = some (.inRight .unit
      (installedClosure type condition body post reason location environment)))
    (next : Evaluates (entryEnvironment type location environment) postStore
      (loopBody type condition body post reason) result after) :
    Evaluates (entryEnvironment type location environment) before
      (loopBody type condition body post reason) result after := by
  apply LocalControl.choose_true _ conditionEvaluation
  rw [advance_weaken]
  apply advance_continuing _ bodyEvaluation
  have composed := post_invokes (continuingPrefix type) postEvaluation installed next
  simp [← Expr.rename_insertion, Expr.rename_comp, bodyEnvironment, Expr.rename, continuingPrefix, conditionCode] at composed ⊢
  simpa only [insertion_zero, shift_comp, Nat.reduceAdd] using composed

theorem body_continuing_post_fault
    {environment : Environment} {before middle bodyStore after : Store} {type : Ty} {location : Location}
    {condition body post : Expr} {selfReason reason : Word}
    (conditionEvaluation : Evaluates (entryEnvironment type location environment) before (conditionCode condition)
      (.inRight .word (.bool true)) middle)
    (bodyEvaluation : Evaluates (bodyEnvironment type location environment) middle (bodyCode body)
      (continuingValue type) bodyStore)
    (postEvaluation : Evaluates (continuingPrefix type ++ entryEnvironment type location environment) bodyStore
      (postCode post) (.inLeft (controlType type) (.word reason)) after) :
    Evaluates (entryEnvironment type location environment) before
      (loopBody type condition body post selfReason) (.inLeft (controlType type) (.word reason)) after := by
  apply LocalControl.choose_true _ conditionEvaluation
  rw [advance_weaken]
  apply advance_continuing _ bodyEvaluation
  have failed := advance_failure
    (next := (invoke type (.var 1) selfReason).rename (fun index => index + 4)) type postEvaluation
  simp only [postCode] at failed
  rw [← LoopRenaming.advance] at failed
  simp [← Expr.rename_insertion, Expr.rename_comp, bodyEnvironment, Expr.rename, continuingPrefix, conditionCode] at failed ⊢
  simpa only [insertion_zero, shift_comp, Nat.reduceAdd] using failed

theorem next_continuing
    {size : Nat} {environment : Environment} {before bodyStore postStore after : Store} {type : Ty} {location : Location}
    {condition body post : Expr} {reason : Word} {result : Value}
    (evaluation : EvaluationSize size (bodyEnvironment type location environment) before
      (advance type (bodyCode body)
        ((advance type (conditionCode post) (invoke type (.var 1) reason)).weakenAt 0)) result after)
    (bodyEvaluation : Evaluates (bodyEnvironment type location environment) before
      (bodyCode body) (continuingValue type) bodyStore)
    (postEvaluation : Evaluates (continuingPrefix type ++ entryEnvironment type location environment) bodyStore
      (postCode post) (fallthroughValue type) postStore)
    (installed : postStore.read? location = some (.inRight .unit
      (installedClosure type condition body post reason location environment))) :
    ∃ smaller, smaller < size ∧ EvaluationSize smaller (entryEnvironment type location environment) postStore
      (loopBody type condition body post reason) result after := by
  obtain ⟨next, decreased, postAdvance⟩ := evaluation.advance_continuing bodyEvaluation
  have renamed : EvaluationSize next
      (continuingPrefix type ++ entryEnvironment type location environment) bodyStore
      ((advance type (conditionCode post) (invoke type (.var 1) reason)).rename
        (fun index => index + 4)) result after := by
    simp [← Expr.rename_insertion, Expr.rename_comp, bodyEnvironment, Expr.rename, continuingPrefix] at postAdvance ⊢
    simpa only [insertion_zero, shift_comp, Nat.reduceAdd] using postAdvance
  obtain ⟨last, decreasedAgain, nextEvaluation⟩ := post_next (continuingPrefix type) postEvaluation installed renamed
  exact ⟨last, Nat.lt_trans decreasedAgain decreased, nextEvaluation⟩

end ForLoop

end Solcore.SourceSemantics.CoreLowering.CoreProof
