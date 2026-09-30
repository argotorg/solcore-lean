import Solcore.SourceSemantics.CoreLowering.LoopRenaming

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
