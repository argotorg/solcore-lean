import Solcore.Core.LocalLoop
import Solcore.SourceSemantics.CoreLowering.ReadOnlyRenaming
import Solcore.SourceSemantics.CoreLowering.CoreHelperInversion
import Solcore.SourceSemantics.Dynamic
import Solcore.SourceSemantics.CoreLowering.ScalarStatementViews

/-!
# Loop renaming and execution

Loop renaming, execution and Core inversion, the post edge of `for` loops, and `for` Source views.

This file stays below `Statements/LoopLayouts`, because the `@[simp]` lemmas there loop in the proofs at the post edge, which rewrite renamings of inserted binders backwards.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.LoopRenaming
/-! Syntactic renaming laws for generated control and loop helpers. These laws
change the actual generated closure body together with its lexical layout;
they do not assert equality of closures or final stores across insertions. -/

set_option autoImplicit false

namespace Solcore.Core.LoopRenaming

@[simp] theorem weakenZero (expression : Expr) (mapping : Renaming) :
    (expression.weakenAt 0).rename mapping.lift = (expression.rename mapping).weakenAt 0 := by
  rw [← Expr.rename_insertion, Expr.rename_comp, Renaming.lift_comp_insertion_zero,
    ← Expr.rename_comp, Expr.rename_insertion]

@[simp] theorem weakenOne (expression : Expr) (mapping : Renaming) :
    (expression.weakenAt 1).rename mapping.lift.lift = (expression.rename mapping.lift).weakenAt 1 := by
  have commute : Renaming.comp mapping.lift.lift (Renaming.insertion 1) =
      Renaming.comp (Renaming.insertion 1) mapping.lift := by
    simpa only [Renaming.lift_comp, Renaming.lift_insertion] using
      congrArg Renaming.lift (Renaming.lift_comp_insertion_zero mapping)
  rw [← Expr.rename_insertion, Expr.rename_comp, commute, ← Expr.rename_comp, Expr.rename_insertion]

@[simp] theorem discard (type : Ty) (computation next : Expr) (mapping : Renaming) :
    (LocalSequence.discard type computation next).rename mapping =
      LocalSequence.discard type (computation.rename mapping) (next.rename mapping) := by
  simp [LocalSequence.discard, LanguageResult.bind, Expr.rename, Renaming.lift]

@[simp] theorem letUninitialized (type : Ty) (body : Expr) (mapping : Renaming) :
    (LocalSequence.letUninitialized type body).rename mapping =
      LocalSequence.letUninitialized type (body.rename mapping.lift) := by
  rfl

@[simp] theorem letInitialized (type payload : Ty) (initializer body : Expr) (mapping : Renaming) :
    (LocalSequence.letInitialized type payload initializer body).rename mapping =
      LocalSequence.letInitialized type payload (initializer.rename mapping) (body.rename mapping.lift) := by
  simp [LocalSequence.letInitialized, OptionalCell.allocateInitialized, LanguageResult.bind, Expr.rename, Renaming.lift]

@[simp] theorem assign (type : Ty) (reference rhs next : Expr) (mapping : Renaming) :
    (LocalSequence.assign type reference rhs next).rename mapping =
      LocalSequence.assign type (reference.rename mapping) (rhs.rename mapping) (next.rename mapping) := by
  simp [LocalSequence.assign, LanguageResult.bind, Expr.rename, Renaming.lift]

@[simp] theorem fallthrough (type : Ty) (mapping : Renaming) :
    (LocalLoop.fallthrough type).rename mapping = LocalLoop.fallthrough type := rfl

@[simp] theorem returned (value : Expr) (mapping : Renaming) :
    (LocalLoop.returned value).rename mapping = LocalLoop.returned (value.rename mapping) := rfl

@[simp] theorem breaking (type : Ty) (mapping : Renaming) :
    (LocalLoop.breaking type).rename mapping = LocalLoop.breaking type := rfl

@[simp] theorem continuing (type : Ty) (mapping : Renaming) :
    (LocalLoop.continuing type).rename mapping = LocalLoop.continuing type := rfl

@[simp] theorem returnValue (type : Ty) (computation : Expr) (mapping : Renaming) :
    (LocalLoop.returnValue type computation).rename mapping = LocalLoop.returnValue type (computation.rename mapping) := by
  simp [LocalLoop.returnValue, LanguageResult.bind, LocalLoop.returned, LanguageResult.success, Expr.rename, Renaming.lift]

@[simp] theorem conditional (type : Ty) (condition thenBranch elseBranch : Expr) (mapping : Renaming) :
    (LocalLoop.conditional type condition thenBranch elseBranch).rename mapping =
      LocalLoop.conditional type (condition.rename mapping) (thenBranch.rename mapping) (elseBranch.rename mapping) := by
  simp [LocalLoop.conditional, LocalControl.choose, LanguageResult.bind, Expr.rename, Renaming.lift]

@[simp] theorem sequence (type : Ty) (computation next : Expr) (mapping : Renaming) :
    (LocalLoop.sequence type computation next).rename mapping =
      LocalLoop.sequence type (computation.rename mapping) (next.rename mapping) := by
  simp [LocalLoop.sequence, LanguageResult.bind, LocalLoop.returned, LanguageResult.success, Expr.rename, Renaming.lift]

@[simp] theorem advance (type : Ty) (computation next : Expr) (mapping : Renaming) :
    (LocalLoop.advance type computation next).rename mapping =
      LocalLoop.advance type (computation.rename mapping) (next.rename mapping) := by
  simp [LocalLoop.advance, LanguageResult.bind, LocalLoop.returned, LocalLoop.fallthrough,
    LanguageResult.success, Expr.rename, Renaming.lift]

@[simp] theorem invoke (type : Ty) (reference : Expr) (reason : Word) (mapping : Renaming) :
    (LocalLoop.invoke type reference reason).rename mapping =
      LocalLoop.invoke type (reference.rename mapping) reason := by
  simp [LocalLoop.invoke, OptionalCell.read, LanguageResult.bind, LanguageResult.success, LanguageResult.failure,
    Expr.rename, Renaming.lift]

@[simp] theorem loopBody (type : Ty) (condition body post : Expr) (reason : Word) (mapping : Renaming) :
    (LocalLoop.loopBody type condition body post reason).rename mapping.lift.lift =
      LocalLoop.loopBody type (condition.rename mapping) (body.rename mapping) (post.rename mapping) reason := by
  simp [LocalLoop.loopBody, Expr.rename, Renaming.lift]

@[simp] theorem iterate (type : Ty) (condition body post : Expr) (reason : Word) (mapping : Renaming) :
    (LocalLoop.iterate type condition body post reason).rename mapping =
      LocalLoop.iterate type (condition.rename mapping) (body.rename mapping) (post.rename mapping) reason := by
  simp [LocalLoop.iterate, OptionalCell.allocate, Expr.rename, Renaming.lift]

@[simp] theorem whileLoop (type : Ty) (condition body : Expr) (reason : Word) (mapping : Renaming) :
    (LocalLoop.whileLoop type condition body reason).rename mapping =
      LocalLoop.whileLoop type (condition.rename mapping) (body.rename mapping) reason := by
  simp [LocalLoop.whileLoop]

end Solcore.Core.LoopRenaming
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.LoopExecution
/-! Finite execution rules for the concrete generated while closure. These
rules compose actual Core derivations; they are not source compilation
certificates and do not assume that inserted closure captures remain equal. -/

set_option autoImplicit false

namespace Solcore.Core.LoopExecution

open LocalLoop

private theorem advance_weaken (type : Ty) (computation next : Expr) :
    (LocalLoop.advance type computation next).weakenAt 0 = LocalLoop.advance type (computation.weakenAt 0) (next.weakenAt 0) := by
  simpa only [Expr.rename_insertion] using LoopRenaming.advance type computation next (Renaming.insertion 0)

private theorem fallthrough_weaken (type : Ty) :
    (fallthrough type).weakenAt 0 = fallthrough type := by
  simp [fallthrough, LanguageResult.success, Expr.weakenAt]

private theorem invoke_weaken (type : Ty) (reference : Expr) (reason : Word) :
    (invoke type reference reason).weakenAt 0 = invoke type (reference.weakenAt 0) reason := by
  simpa only [Expr.rename_insertion] using LoopRenaming.invoke type reference reason (Renaming.insertion 0)

def entryEnvironment (type : Ty) (location : Location) (environment : Environment) : Environment :=
  .unit :: .cellRef (OptionalCell.cellType (functionType type)) location :: environment

def bodyEnvironment (type : Ty) (location : Location) (environment : Environment) : Environment :=
  .bool true :: entryEnvironment type location environment

def conditionCode (condition : Expr) : Expr := (condition.weakenAt 0).weakenAt 0

def bodyCode (body : Expr) : Expr := ((body.weakenAt 0).weakenAt 0).weakenAt 0

/-- A loop condition fault stops before its body and keeps the condition's
actual post-prefix store. -/
theorem condition_failure
    {environment : Environment} {before after : Store} {type : Ty}
    {condition body post : Expr} {selfReason reason : Word}
    (conditionEvaluation : Evaluates environment before (conditionCode condition)
      (.inLeft .bool (.word reason)) after) :
    Evaluates environment before (loopBody type condition body post selfReason)
      (.inLeft (controlType type) (.word reason)) after :=
  LocalControl.choose_failure _ conditionEvaluation

theorem condition_false
    {environment : Environment} {before after : Store} {type : Ty}
    {condition body post : Expr} {selfReason : Word}
    (conditionEvaluation : Evaluates environment before (conditionCode condition)
      (.inRight .word (.bool false)) after) :
    Evaluates environment before (loopBody type condition body post selfReason)
      (fallthroughValue type) after :=
  LocalControl.choose_false _ conditionEvaluation (by
    rw [fallthrough_weaken]
    exact fallthrough_evaluates _ _ _)

theorem body_failure
    {environment : Environment} {before middle after : Store} {type : Ty}
    {condition body post : Expr} {selfReason reason : Word}
    (conditionEvaluation : Evaluates environment before (conditionCode condition)
      (.inRight .word (.bool true)) middle)
    (bodyEvaluation : Evaluates (.bool true :: environment) middle (bodyCode body)
      (.inLeft (controlType type) (.word reason)) after) :
    Evaluates environment before (loopBody type condition body post selfReason)
      (.inLeft (controlType type) (.word reason)) after := by
  apply LocalControl.choose_true _ conditionEvaluation
  rw [advance_weaken]
  exact advance_failure _ bodyEvaluation

theorem body_returned
    {environment : Environment} {before middle after : Store} {type : Ty}
    {condition body post : Expr} {selfReason : Word} {value : Value}
    (conditionEvaluation : Evaluates environment before (conditionCode condition)
      (.inRight .word (.bool true)) middle)
    (bodyEvaluation : Evaluates (.bool true :: environment) middle (bodyCode body)
      (returnedValue value) after) :
    Evaluates environment before (loopBody type condition body post selfReason)
      (returnedValue value) after := by
  apply LocalControl.choose_true _ conditionEvaluation
  rw [advance_weaken]
  exact advance_returned _ bodyEvaluation

theorem body_breaking
    {environment : Environment} {before middle after : Store} {type : Ty}
    {condition body post : Expr} {selfReason : Word}
    (conditionEvaluation : Evaluates environment before (conditionCode condition)
      (.inRight .word (.bool true)) middle)
    (bodyEvaluation : Evaluates (.bool true :: environment) middle (bodyCode body)
      (breakingValue type) after) :
    Evaluates environment before (loopBody type condition body post selfReason)
      (fallthroughValue type) after := by
  apply LocalControl.choose_true _ conditionEvaluation
  rw [advance_weaken]
  exact advance_breaking _ bodyEvaluation

private theorem post_fallthrough_invokes
    {environment : Environment} {before after : Store} {type : Ty} {location : Location}
    {condition body : Expr} {selfReason : Word} {result : Value}
    (added : List Value)
    (installed : before.read? location = some (.inRight .unit
      (installedClosure type condition body (fallthrough type) selfReason location environment)))
    (next : Evaluates (entryEnvironment type location environment) before
      (loopBody type condition body (fallthrough type) selfReason) result after) :
    Evaluates (added ++ entryEnvironment type location environment) before
      ((LocalLoop.advance type ((fallthrough type).weakenAt 0 |>.weakenAt 0)
        (invoke type (.var 1) selfReason)).rename (fun index => index + added.length)) result after := by
  rw [LoopRenaming.advance, fallthrough_weaken, fallthrough_weaken, LoopRenaming.fallthrough]
  apply advance_fallthrough _ (fallthrough_evaluates _ _ _)
  simp [LoopRenaming.invoke, Expr.rename, invoke_weaken, Expr.weakenAt]
  apply invoke_success _ _ (.var ?_) installed next
  simpa [entryEnvironment, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    (List.getElem?_append_right (l₁ := added) (l₂ := entryEnvironment type location environment)
      (i := added.length + 1) (by omega))

theorem body_fallthrough
    {environment : Environment} {before middle nextStore after : Store} {type : Ty} {location : Location}
    {condition body : Expr} {selfReason : Word} {result : Value}
    (conditionEvaluation : Evaluates (entryEnvironment type location environment) before (conditionCode condition)
      (.inRight .word (.bool true)) middle)
    (bodyEvaluation : Evaluates (bodyEnvironment type location environment) middle (bodyCode body)
      (fallthroughValue type) nextStore)
    (installed : nextStore.read? location = some (.inRight .unit
      (installedClosure type condition body (fallthrough type) selfReason location environment)))
    (next : Evaluates (entryEnvironment type location environment) nextStore
      (loopBody type condition body (fallthrough type) selfReason) result after) :
    Evaluates (entryEnvironment type location environment) before
      (loopBody type condition body (fallthrough type) selfReason) result after := by
  apply LocalControl.choose_true _ conditionEvaluation
  rw [advance_weaken]
  apply advance_fallthrough _ bodyEvaluation
  have composed := post_fallthrough_invokes
    [.unit, .inLeft type .unit, .inLeft transferType (.inLeft type .unit), .bool true] installed next
  simpa [← Expr.rename_insertion, Expr.rename_comp, Renaming.comp, Renaming.insertion, bodyEnvironment, Expr.rename] using composed
theorem body_continuing
    {environment : Environment} {before middle nextStore after : Store} {type : Ty} {location : Location}
    {condition body : Expr} {selfReason : Word} {result : Value}
    (conditionEvaluation : Evaluates (entryEnvironment type location environment) before (conditionCode condition)
      (.inRight .word (.bool true)) middle)
    (bodyEvaluation : Evaluates (bodyEnvironment type location environment) middle (bodyCode body)
      (continuingValue type) nextStore)
    (installed : nextStore.read? location = some (.inRight .unit
      (installedClosure type condition body (fallthrough type) selfReason location environment)))
    (next : Evaluates (entryEnvironment type location environment) nextStore
      (loopBody type condition body (fallthrough type) selfReason) result after) :
    Evaluates (entryEnvironment type location environment) before
      (loopBody type condition body (fallthrough type) selfReason) result after := by
  apply LocalControl.choose_true _ conditionEvaluation
  rw [advance_weaken]
  apply advance_continuing _ bodyEvaluation
  have composed := post_fallthrough_invokes
    [.unit, .inRight .unit .unit, .inRight (LocalControl.controlType type) (.inRight .unit .unit), .bool true] installed next
  simpa [← Expr.rename_insertion, Expr.rename_comp, Renaming.comp, Renaming.insertion, bodyEnvironment, Expr.rename] using composed

/-- A finite trace of the actual generated loop closure. Each recursive edge
records the still-installed self closure after the body effects. This is an
execution witness used below static source certificates, not a replacement
for the independent source semantics. -/
inductive WhileTrace (type : Ty) (condition body : Expr) (selfReason : Word)
    (location : Location) (environment : Environment) : Store → Value → Store → Prop where
  | done {before after}
      (conditionEvaluation : Evaluates (entryEnvironment type location environment) before (conditionCode condition)
        (.inRight .word (.bool false)) after) :
      WhileTrace type condition body selfReason location environment before (fallthroughValue type) after
  | conditionFault {before after reason}
      (conditionEvaluation : Evaluates (entryEnvironment type location environment) before (conditionCode condition)
        (.inLeft .bool (.word reason)) after) :
      WhileTrace type condition body selfReason location environment before (.inLeft (controlType type) (.word reason)) after
  | returns {before middle after value}
      (conditionEvaluation : Evaluates (entryEnvironment type location environment) before (conditionCode condition)
        (.inRight .word (.bool true)) middle)
      (bodyEvaluation : Evaluates (bodyEnvironment type location environment) middle (bodyCode body) (returnedValue value) after) :
      WhileTrace type condition body selfReason location environment before (returnedValue value) after
  | breaks {before middle after}
      (conditionEvaluation : Evaluates (entryEnvironment type location environment) before (conditionCode condition)
        (.inRight .word (.bool true)) middle)
      (bodyEvaluation : Evaluates (bodyEnvironment type location environment) middle (bodyCode body) (breakingValue type) after) :
      WhileTrace type condition body selfReason location environment before (fallthroughValue type) after
  | bodyFault {before middle after reason}
      (conditionEvaluation : Evaluates (entryEnvironment type location environment) before (conditionCode condition)
        (.inRight .word (.bool true)) middle)
      (bodyEvaluation : Evaluates (bodyEnvironment type location environment) middle (bodyCode body)
        (.inLeft (controlType type) (.word reason)) after) :
      WhileTrace type condition body selfReason location environment before (.inLeft (controlType type) (.word reason)) after
  | nextFallthrough {before middle nextStore after result}
      (conditionEvaluation : Evaluates (entryEnvironment type location environment) before (conditionCode condition)
        (.inRight .word (.bool true)) middle)
      (bodyEvaluation : Evaluates (bodyEnvironment type location environment) middle (bodyCode body)
        (fallthroughValue type) nextStore)
      (installed : nextStore.read? location = some (.inRight .unit
        (installedClosure type condition body (fallthrough type) selfReason location environment)))
      (next : WhileTrace type condition body selfReason location environment nextStore result after) :
      WhileTrace type condition body selfReason location environment before result after
  | nextContinue {before middle nextStore after result}
      (conditionEvaluation : Evaluates (entryEnvironment type location environment) before (conditionCode condition)
        (.inRight .word (.bool true)) middle)
      (bodyEvaluation : Evaluates (bodyEnvironment type location environment) middle (bodyCode body)
        (continuingValue type) nextStore)
      (installed : nextStore.read? location = some (.inRight .unit
        (installedClosure type condition body (fallthrough type) selfReason location environment)))
      (next : WhileTrace type condition body selfReason location environment nextStore result after) :
      WhileTrace type condition body selfReason location environment before result after

theorem WhileTrace.evaluates
    {environment : Environment} {before after : Store} {type : Ty} {location : Location}
    {condition body : Expr} {selfReason : Word} {result : Value}
    (trace : WhileTrace type condition body selfReason location environment before result after) :
    Evaluates (entryEnvironment type location environment) before
      (loopBody type condition body (fallthrough type) selfReason) result after := by
  induction trace with
  | done condition => exact condition_false condition
  | conditionFault condition => exact condition_failure condition
  | returns condition body => exact body_returned condition body
  | breaks condition body => exact body_breaking condition body
  | bodyFault condition body => exact body_failure condition body
  | nextFallthrough condition body installed _ ih => exact body_fallthrough condition body installed ih
  | nextContinue condition body installed _ ih => exact body_continuing condition body installed ih

/-- Allocation and self installation are included in the generated program's
execution. A trace starts only after that concrete administrative cell exists. -/
theorem WhileTrace.whileLoop_evaluates
    {environment : Environment} {before after : Store} {type : Ty}
    {condition body : Expr} {selfReason : Word} {result : Value}
    (trace : WhileTrace type condition body selfReason before.length environment
      (before ++ [.inRight .unit (installedClosure type condition body (fallthrough type) selfReason before.length environment)])
      result after) :
    Evaluates environment before (whileLoop type condition body selfReason) result after := by
  apply iterate_evaluates
  apply invoke_success _ _ (.var rfl) _ trace.evaluates
  simp [Store.read?, installedClosure]

end Solcore.Core.LoopExecution
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.LoopCoreInversion
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ForSourceInduction
/-! A focused induction principle derived from the independent, mutually
inductive source semantics. The source judgments and their constructors are
unchanged; unrelated expression/call premises receive the trivial motive. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.LoopStatements

open Frontend Frontend.SourceInference Solcore.SourceSemantics.Dynamic

/-- Induction on finite source for derivations, retaining the successful
body derivations and the induction hypothesis for each next iteration. -/
theorem for_induction {program : Program}
    (motive : Context → EvidenceEnvironment → TypedSource → Environment → Heap →
      ExpressionId → List ForItemForm → List StatementId → Context → ControlOutcome → Heap → Prop)
    (done : ∀ {context evidence source environment before after condition post body},
      ExpressionEvaluates program context evidence source environment before condition (.bool false) after →
      motive context evidence source environment before condition post body context (.fallthrough environment) after)
    (nextFallthrough : ∀ {context evidence source environment before conditionHeap bodyHeap postHeap after
        condition post body bodyFinalContext postFinalContext bodyEnvironment postEnvironment outcome},
      ExpressionEvaluates program context evidence source environment before condition (.bool true) conditionHeap →
      StatementsExecute program context evidence source environment conditionHeap body bodyFinalContext
        (.fallthrough bodyEnvironment) bodyHeap →
      ForItemsExecute program context evidence source environment bodyHeap post postFinalContext postEnvironment postHeap →
      ForLoopExecutes program context evidence source environment postHeap condition post body context outcome after →
      motive context evidence source environment postHeap condition post body context outcome after →
      motive context evidence source environment before condition post body context outcome after)
    (nextContinue : ∀ {context evidence source environment before conditionHeap bodyHeap postHeap after
        condition post body bodyFinalContext postFinalContext bodyEnvironment postEnvironment outcome},
      ExpressionEvaluates program context evidence source environment before condition (.bool true) conditionHeap →
      StatementsExecute program context evidence source environment conditionHeap body bodyFinalContext
        (.continuing bodyEnvironment) bodyHeap →
      ForItemsExecute program context evidence source environment bodyHeap post postFinalContext postEnvironment postHeap →
      ForLoopExecutes program context evidence source environment postHeap condition post body context outcome after →
      motive context evidence source environment postHeap condition post body context outcome after →
      motive context evidence source environment before condition post body context outcome after)
    (breaks : ∀ {context evidence source environment before conditionHeap after condition post body bodyFinalContext bodyEnvironment},
      ExpressionEvaluates program context evidence source environment before condition (.bool true) conditionHeap →
      StatementsExecute program context evidence source environment conditionHeap body bodyFinalContext
        (.breaking bodyEnvironment) after →
      motive context evidence source environment before condition post body context (.fallthrough environment) after)
    (returns : ∀ {context evidence source environment before conditionHeap after condition post body bodyFinalContext result},
      ExpressionEvaluates program context evidence source environment before condition (.bool true) conditionHeap →
      StatementsExecute program context evidence source environment conditionHeap body bodyFinalContext (.returned result) after →
      motive context evidence source environment before condition post body context (.returned result) after)
    {context evidence source environment before condition post body finalContext outcome after}
    (execution : ForLoopExecutes program context evidence source environment before condition post body finalContext outcome after) :
    motive context evidence source environment before condition post body finalContext outcome after := by
  apply ForLoopExecutes.rec
    (motive_1 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ _ _ _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_6 := fun _ _ _ _ _ _ _ _ _ _ _ => True)
    (motive_7 := fun _ _ _ _ _ _ _ _ _ _ => True)
    (motive_8 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_9 := fun _ _ _ _ _ _ _ _ _ _ => True)
    (motive_10 := fun _ _ _ _ _ _ _ _ => True)
    (motive_11 := fun _ _ _ _ _ _ _ _ => True)
    (motive_12 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_13 := fun _ _ _ _ _ _ _ => True)
    (motive_14 := fun _ _ _ _ _ _ _ _ _ _ => True)
    (motive_15 := fun _ _ _ _ _ _ _ _ _ _ => True)
    (motive_16 := fun _ _ _ _ _ _ _ _ _ _ => True)
    (motive_17 := fun _ _ _ _ _ _ _ _ _ _ => True)
    (motive_18 := fun _ _ _ _ _ _ _ _ _ _ => True)
    (motive_19 := fun _ _ _ _ _ _ _ _ _ _ _ => True)
    (motive_20 := fun context evidence source environment before condition post body finalContext outcome after _ =>
      motive context evidence source environment before condition post body finalContext outcome after)
    (t := execution)
  all_goals intros
  all_goals first
    | exact True.intro
    | solve | apply done; assumption
    | solve | apply nextFallthrough <;> assumption
    | solve | apply nextContinue <;> assumption
    | solve | apply breaks <;> assumption
    | solve | apply returns <;> assumption

/-- Fault induction retains successful prefixes and follows only the first
faulting iteration. -/
theorem for_fault_induction {program : Program}
    (motive : Context → EvidenceEnvironment → TypedSource → Environment → Heap →
      ExpressionId → List ForItemForm → List StatementId → SemanticFault → Heap → Prop)
    (conditionFault : ∀ {context evidence source environment before after condition post body reason},
      ExpressionFaults program context evidence source environment before condition reason after →
      motive context evidence source environment before condition post body reason after)
    (conditionType : ∀ {context evidence source environment before after condition post body value actual},
      ExpressionEvaluates program context evidence source environment before condition value after →
      (¬ BooleanValue value) → ValueRuntimeType value actual →
      motive context evidence source environment before condition post body (.typeMismatch .bool actual) after)
    (bodyFault : ∀ {context evidence source environment before conditionHeap after condition post body finalContext reason},
      ExpressionEvaluates program context evidence source environment before condition (.bool true) conditionHeap →
      StatementsFault program context evidence source environment conditionHeap body finalContext reason after →
      motive context evidence source environment before condition post body reason after)
    (postFallthrough : ∀ {context evidence source environment before conditionHeap bodyHeap after
        condition post body bodyFinalContext bodyEnvironment finalContext reason},
      ExpressionEvaluates program context evidence source environment before condition (.bool true) conditionHeap →
      StatementsExecute program context evidence source environment conditionHeap body bodyFinalContext
        (.fallthrough bodyEnvironment) bodyHeap →
      ForItemsFault program context evidence source environment bodyHeap post finalContext reason after →
      motive context evidence source environment before condition post body reason after)
    (postContinue : ∀ {context evidence source environment before conditionHeap bodyHeap after
        condition post body bodyFinalContext bodyEnvironment finalContext reason},
      ExpressionEvaluates program context evidence source environment before condition (.bool true) conditionHeap →
      StatementsExecute program context evidence source environment conditionHeap body bodyFinalContext
        (.continuing bodyEnvironment) bodyHeap →
      ForItemsFault program context evidence source environment bodyHeap post finalContext reason after →
      motive context evidence source environment before condition post body reason after)
    (nextFallthrough : ∀ {context evidence source environment before conditionHeap bodyHeap postHeap after
        condition post body bodyFinalContext postFinalContext bodyEnvironment postEnvironment reason},
      ExpressionEvaluates program context evidence source environment before condition (.bool true) conditionHeap →
      StatementsExecute program context evidence source environment conditionHeap body bodyFinalContext
        (.fallthrough bodyEnvironment) bodyHeap →
      ForItemsExecute program context evidence source environment bodyHeap post postFinalContext postEnvironment postHeap →
      ForLoopFaults program context evidence source environment postHeap condition post body reason after →
      motive context evidence source environment postHeap condition post body reason after →
      motive context evidence source environment before condition post body reason after)
    (nextContinue : ∀ {context evidence source environment before conditionHeap bodyHeap postHeap after
        condition post body bodyFinalContext postFinalContext bodyEnvironment postEnvironment reason},
      ExpressionEvaluates program context evidence source environment before condition (.bool true) conditionHeap →
      StatementsExecute program context evidence source environment conditionHeap body bodyFinalContext
        (.continuing bodyEnvironment) bodyHeap →
      ForItemsExecute program context evidence source environment bodyHeap post postFinalContext postEnvironment postHeap →
      ForLoopFaults program context evidence source environment postHeap condition post body reason after →
      motive context evidence source environment postHeap condition post body reason after →
      motive context evidence source environment before condition post body reason after)
    {context evidence source environment before condition post body reason after}
    (execution : ForLoopFaults program context evidence source environment before condition post body reason after) :
    motive context evidence source environment before condition post body reason after := by
  apply ForLoopFaults.rec
    (motive_1 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ _ _ _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ _ _ _ _ _ _ => True)
    (motive_6 := fun _ _ _ _ _ _ _ _ => True)
    (motive_7 := fun _ _ _ _ _ _ _ _ => True)
    (motive_8 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_9 := fun _ _ _ _ _ _ _ => True)
    (motive_10 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_11 := fun _ _ _ _ _ _ _ _ _ _ => True)
    (motive_12 := fun _ _ _ _ _ _ _ _ _ _ => True)
    (motive_13 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_14 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_15 := fun _ _ _ _ _ _ _ _ _ _ _ => True)
    (motive_16 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_17 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_18 := fun _ _ _ _ _ _ _ _ _ _ => True)
    (motive_19 := fun _ _ _ _ _ _ _ _ _ _ => True)
    (motive_20 := fun context evidence source environment before condition post body reason after _ =>
      motive context evidence source environment before condition post body reason after)
    (t := execution)
  all_goals intros
  all_goals first
    | exact True.intro
    | solve | apply conditionFault; assumption
    | solve | apply conditionType <;> assumption
    | solve | apply bodyFault <;> assumption
    | solve | apply postFallthrough <;> assumption
    | solve | apply postContinue <;> assumption
    | solve | apply nextFallthrough <;> assumption
    | solve | apply nextContinue <;> assumption

end Solcore.SourceSemantics.CoreLowering.LoopStatements
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ForSourceViews
/-! Unique-occurrence inversion for independent source for statements. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.ForSourceViews

open Frontend Frontend.SourceInference

private theorem shape {source : TypedSource} {id : StatementId} {node : StatementNode}
    {form : StatementForm} (unique : NodeOccurrencesUnique source)
    (contains : ContainsStatement source id node) (sameForm : node.form = form) :
    ∀ other, ContainsStatement source id other → other.form = form := by
  intro other otherContains
  have same : other = node := Option.some.inj
    ((lookupStatement?_complete unique otherContains).symm.trans (lookupStatement?_complete unique contains))
  exact same ▸ sameForm

theorem success
    {program : Program} {context finalContext : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : StatementId} {node : StatementNode} {outcome : Dynamic.ControlOutcome}
    {items post : List ForItemForm} {condition : ExpressionId} {statements : List StatementId}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (form : node.form = .forLoop items condition post statements)
    (executed : Dynamic.StatementExecutes program context evidence source environment before id finalContext outcome after) :
    finalContext = context ∧ ∃ loopContext loopFinalContext loopEnvironment initialized loopOutcome,
      outcome = Dynamic.restoreControl environment loopOutcome ∧
      Dynamic.ForItemsExecute program context evidence source environment before items loopContext loopEnvironment initialized ∧
      Dynamic.ForLoopExecutes program loopContext evidence source loopEnvironment initialized condition post statements loopFinalContext loopOutcome after := by
  have formShape := shape unique contains form
  clear contains form
  cases executed <;> have actualForm := formShape _ (by assumption) <;> simp_all
  exact ⟨_, _, _, _, _, rfl, by assumption, by assumption⟩

theorem fault
    {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : StatementId} {node : StatementNode} {reason : Dynamic.SemanticFault}
    {items post : List ForItemForm} {condition : ExpressionId} {statements : List StatementId}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (form : node.form = .forLoop items condition post statements)
    (fault : Dynamic.StatementFaults program context evidence source environment before id reason after) :
    (∃ finalContext, Dynamic.ForItemsFault program context evidence source environment before items finalContext reason after) ∨
    (∃ loopContext loopEnvironment initialized,
      Dynamic.ForItemsExecute program context evidence source environment before items loopContext loopEnvironment initialized ∧
      Dynamic.ForLoopFaults program loopContext evidence source loopEnvironment initialized condition post statements reason after) := by
  have formShape := shape unique contains form
  have present : ¬ Dynamic.StatementMissing source id := fun absent => Dynamic.StatementAbsentIn.excludes_contains absent contains
  clear contains form
  cases fault
  all_goals first
    | exact False.elim (present (by assumption))
    | have actualForm := formShape _ (by assumption); simp_all
  · exact .inl ⟨_, by assumption⟩
  · exact .inr ⟨_, _, _, by assumption, by assumption⟩

end Solcore.SourceSemantics.CoreLowering.ForSourceViews
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ForLoopCoreEdges
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
end
