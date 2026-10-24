import Solcore.Core.LocalLoop

/-! Evaluation bridges for the ordinary Core loop implementation. Each stage
uses its actual administrative binders and store; recursive iterations reuse
the installed self cell instead of allocating another loop closure. -/
set_option autoImplicit false
namespace Solcore.Core.LocalLoop

def shift (count : Nat) : Renaming := fun index => count + index

@[simp] theorem rename_shift (expression : Expr) (first second : Nat) :
    (expression.rename (shift first)).rename (shift second) = expression.rename (shift (second + first)) := by
  rw [Expr.rename_comp]
  congr 1
  funext index
  simp [Renaming.comp, shift, Nat.add_assoc]

theorem weaken_zero (expression : Expr) : expression.weakenAt 0 = expression.rename (shift 1) := by
  rw [← Expr.rename_insertion]
  congr 1
  funext index
  simp [Renaming.insertion, shift, Nat.add_comm]

theorem rename_weaken_zero (expression : Expr) (mapping : Renaming) :
    (expression.weakenAt 0).rename mapping.lift = (expression.rename mapping).weakenAt 0 := by
  simp only [← Expr.rename_insertion, Expr.rename_comp, Renaming.lift_comp_insertion_zero]

theorem conditional_rename (type : Ty) (condition yes no : Expr) (mapping : Renaming) :
    (conditional type condition yes no).rename mapping =
      conditional type (condition.rename mapping) (yes.rename mapping) (no.rename mapping) := by
  simp only [conditional, LocalControl.choose, LanguageResult.bind, Expr.rename,
    rename_weaken_zero, Renaming.lift]

@[simp] theorem fallthrough_rename (type : Ty) (mapping : Renaming) :
    (fallthrough type).rename mapping = fallthrough type := rfl

@[simp] theorem breaking_rename (type : Ty) (mapping : Renaming) :
    (breaking type).rename mapping = breaking type := rfl

@[simp] theorem continuing_rename (type : Ty) (mapping : Renaming) :
    (continuing type).rename mapping = continuing type := rfl

@[simp] theorem returned_rename (value : Expr) (mapping : Renaming) :
    (returned value).rename mapping = returned (value.rename mapping) := rfl

theorem advance_rename (type : Ty) (computation next : Expr) (mapping : Renaming) :
    (advance type computation next).rename mapping =
      advance type (computation.rename mapping) (next.rename mapping) := by
  simp only [advance, returned, fallthrough, LanguageResult.bind, LanguageResult.success,
    Expr.rename, rename_weaken_zero, Renaming.lift]

theorem invoke_rename (type : Ty) (reference : Expr) (reason : Word) (mapping : Renaming) :
    (invoke type reference reason).rename mapping = invoke type (reference.rename mapping) reason := by
  simp [invoke, OptionalCell.read, LanguageResult.bind, LanguageResult.success,
    LanguageResult.failure, Expr.rename, Renaming.lift]

theorem loopBody_rename (type : Ty) (condition body post : Expr) (reason : Word) (mapping : Renaming) :
    (loopBody type condition body post reason).rename mapping.lift.lift =
      loopBody type (condition.rename mapping) (body.rename mapping) (post.rename mapping) reason := by
  simp only [loopBody, conditional_rename, advance_rename, invoke_rename,
    rename_weaken_zero, fallthrough_rename, Expr.rename, Renaming.lift]

theorem iterate_rename (type : Ty) (condition body post : Expr) (reason : Word) (mapping : Renaming) :
    (iterate type condition body post reason).rename mapping =
      iterate type (condition.rename mapping) (body.rename mapping) (post.rename mapping) reason := by
  simp only [iterate, Expr.rename, OptionalCell.allocate, loopBody_rename, invoke_rename,
    Renaming.lift]

def selfReference (type : Ty) (location : Location) : Value :=
  .cellRef (OptionalCell.cellType (functionType type)) location

def conditionPrefix (type : Ty) (location : Location) : Environment :=
  [.unit, selfReference type location]

def bodyPrefix (type : Ty) (location : Location) : Environment :=
  .bool true :: conditionPrefix type location

def advancePrefix (type : Ty) (continues : Bool) : Environment :=
  if continues then
    [.unit, .inRight .unit .unit, .inRight (LocalControl.controlType type) (.inRight .unit .unit)]
  else [.unit, .inLeft type .unit, .inLeft transferType (.inLeft type .unit)]

def advanceValue (type : Ty) (continues : Bool) : Value :=
  if continues then continuingValue type else fallthroughValue type

def postPrefix (type : Ty) (location : Location) (bodyContinues : Bool) : Environment :=
  advancePrefix type bodyContinues ++ bodyPrefix type location

def restartPrefix (type : Ty) (location : Location) (bodyContinues postContinues : Bool) : Environment :=
  advancePrefix type postContinues ++ postPrefix type location bodyContinues

@[simp] theorem conditionPrefix_length (type : Ty) (location : Location) :
    (conditionPrefix type location).length = 2 := rfl

@[simp] theorem bodyPrefix_length (type : Ty) (location : Location) :
    (bodyPrefix type location).length = 3 := rfl

@[simp] theorem advancePrefix_length (type : Ty) (continues : Bool) :
    (advancePrefix type continues).length = 3 := by cases continues <;> rfl

@[simp] theorem postPrefix_length (type : Ty) (location : Location) (continues : Bool) :
    (postPrefix type location continues).length = 6 := by simp [postPrefix]

@[simp] theorem restartPrefix_length (type : Ty) (location : Location) (bodyContinues postContinues : Bool) :
    (restartPrefix type location bodyContinues postContinues).length = 9 := by simp [restartPrefix]

theorem advance_progress {environment : Environment} {initial middle final : Store}
    {computation next : Expr} {result : Value} (type : Ty) (continues : Bool)
    (evaluated : Evaluates environment initial computation (advanceValue type continues) middle)
    (continued : Evaluates (advancePrefix type continues ++ environment) middle
      (next.rename (shift 3)) result final) :
    Evaluates environment initial (advance type computation next) result final := by
  have shifted : ((next.weakenAt 0).weakenAt 0).weakenAt 0 = next.rename (shift 3) := by
    simp only [weaken_zero, rename_shift]
  cases continues with
  | false => exact advance_fallthrough type evaluated (by simpa [shifted, advancePrefix] using continued)
  | true => exact advance_continuing type evaluated (by simpa [shifted, advancePrefix] using continued)

theorem loopBody_done {environment : Environment} {initial final : Store}
    {condition body post : Expr} (type : Ty) (reason : Word) (location : Location)
    (tested : Evaluates (conditionPrefix type location ++ environment) initial
      (condition.rename (shift 2)) (.inRight .word (.bool false)) final) :
    Evaluates (conditionPrefix type location ++ environment) initial
      (loopBody type condition body post reason) (fallthroughValue type) final := by
  apply LocalControl.choose_false (controlType type)
  · simpa only [weaken_zero, rename_shift] using tested
  · simpa only [weaken_zero, fallthrough_rename] using fallthrough_evaluates type
      (.bool false :: (conditionPrefix type location ++ environment)) final

theorem loopBody_conditionFailure {environment : Environment} {initial final : Store}
    {condition body post : Expr} {failure : Word} (type : Ty) (reason : Word) (location : Location)
    (tested : Evaluates (conditionPrefix type location ++ environment) initial
      (condition.rename (shift 2)) (.inLeft .bool (.word failure)) final) :
    Evaluates (conditionPrefix type location ++ environment) initial
      (loopBody type condition body post reason) (.inLeft (controlType type) (.word failure)) final := by
  apply LocalControl.choose_failure (controlType type)
  simpa only [weaken_zero, rename_shift] using tested

/-- The condition's true branch contains precisely the body and post advances
and a reference to the same self cell. -/
theorem loopBody_true {environment : Environment} {initial testedStore final : Store}
    {condition body post : Expr} {result : Value} (type : Ty) (reason : Word) (location : Location)
    (tested : Evaluates (conditionPrefix type location ++ environment) initial
      (condition.rename (shift 2)) (.inRight .word (.bool true)) testedStore)
    (advanced : Evaluates (bodyPrefix type location ++ environment) testedStore
      (advance type (body.rename (shift 3))
        (advance type (post.rename (shift 3)) (invoke type (.var 2) reason))) result final) :
    Evaluates (conditionPrefix type location ++ environment) initial
      (loopBody type condition body post reason) result final := by
  apply LocalControl.choose_true (controlType type)
  · simpa only [weaken_zero, rename_shift] using tested
  · simpa only [weaken_zero, advance_rename, invoke_rename, rename_shift, Expr.rename,
      shift, bodyPrefix, List.cons_append] using advanced

theorem loopBody_bodyBreak {environment : Environment} {initial testedStore final : Store}
    {condition body post : Expr} (type : Ty) (reason : Word) (location : Location)
    (tested : Evaluates (conditionPrefix type location ++ environment) initial
      (condition.rename (shift 2)) (.inRight .word (.bool true)) testedStore)
    (bodyEvaluated : Evaluates (bodyPrefix type location ++ environment) testedStore
      (body.rename (shift 3)) (breakingValue type) final) :
    Evaluates (conditionPrefix type location ++ environment) initial
      (loopBody type condition body post reason) (fallthroughValue type) final :=
  loopBody_true type reason location tested (advance_breaking type bodyEvaluated)

theorem loopBody_bodyReturn {environment : Environment} {initial testedStore final : Store}
    {condition body post : Expr} {value : Value} (type : Ty) (reason : Word) (location : Location)
    (tested : Evaluates (conditionPrefix type location ++ environment) initial
      (condition.rename (shift 2)) (.inRight .word (.bool true)) testedStore)
    (bodyEvaluated : Evaluates (bodyPrefix type location ++ environment) testedStore
      (body.rename (shift 3)) (returnedValue value) final) :
    Evaluates (conditionPrefix type location ++ environment) initial
      (loopBody type condition body post reason) (returnedValue value) final :=
  loopBody_true type reason location tested (advance_returned type bodyEvaluated)

theorem loopBody_bodyFailure {environment : Environment} {initial testedStore final : Store}
    {condition body post : Expr} {failure : Word} (type : Ty) (reason : Word) (location : Location)
    (tested : Evaluates (conditionPrefix type location ++ environment) initial
      (condition.rename (shift 2)) (.inRight .word (.bool true)) testedStore)
    (bodyEvaluated : Evaluates (bodyPrefix type location ++ environment) testedStore
      (body.rename (shift 3)) (.inLeft (controlType type) (.word failure)) final) :
    Evaluates (conditionPrefix type location ++ environment) initial
      (loopBody type condition body post reason) (.inLeft (controlType type) (.word failure)) final :=
  loopBody_true type reason location tested (advance_failure type bodyEvaluated)

theorem loopBody_progress {environment : Environment} {initial testedStore bodyStore final : Store}
    {condition body post : Expr} {result : Value} (type : Ty) (reason : Word) (location : Location)
    (bodyContinues : Bool)
    (tested : Evaluates (conditionPrefix type location ++ environment) initial
      (condition.rename (shift 2)) (.inRight .word (.bool true)) testedStore)
    (bodyEvaluated : Evaluates (bodyPrefix type location ++ environment) testedStore
      (body.rename (shift 3)) (advanceValue type bodyContinues) bodyStore)
    (postAdvanced : Evaluates (postPrefix type location bodyContinues ++ environment) bodyStore
      (advance type (post.rename (shift 6)) (invoke type (.var 5) reason)) result final) :
    Evaluates (conditionPrefix type location ++ environment) initial
      (loopBody type condition body post reason) result final := by
  apply loopBody_true type reason location tested
  apply advance_progress type bodyContinues bodyEvaluated
  simpa only [advance_rename, invoke_rename, rename_shift, Expr.rename, shift,
    postPrefix, List.append_assoc] using postAdvanced

theorem loopBody_postBreak {environment : Environment} {initial testedStore bodyStore final : Store}
    {condition body post : Expr} (type : Ty) (reason : Word) (location : Location)
    (bodyContinues : Bool)
    (tested : Evaluates (conditionPrefix type location ++ environment) initial
      (condition.rename (shift 2)) (.inRight .word (.bool true)) testedStore)
    (bodyEvaluated : Evaluates (bodyPrefix type location ++ environment) testedStore
      (body.rename (shift 3)) (advanceValue type bodyContinues) bodyStore)
    (postEvaluated : Evaluates (postPrefix type location bodyContinues ++ environment) bodyStore
      (post.rename (shift 6)) (breakingValue type) final) :
    Evaluates (conditionPrefix type location ++ environment) initial
      (loopBody type condition body post reason) (fallthroughValue type) final :=
  loopBody_progress type reason location bodyContinues tested bodyEvaluated (advance_breaking type postEvaluated)

theorem loopBody_postReturn {environment : Environment} {initial testedStore bodyStore final : Store}
    {condition body post : Expr} {value : Value} (type : Ty) (reason : Word) (location : Location)
    (bodyContinues : Bool)
    (tested : Evaluates (conditionPrefix type location ++ environment) initial
      (condition.rename (shift 2)) (.inRight .word (.bool true)) testedStore)
    (bodyEvaluated : Evaluates (bodyPrefix type location ++ environment) testedStore
      (body.rename (shift 3)) (advanceValue type bodyContinues) bodyStore)
    (postEvaluated : Evaluates (postPrefix type location bodyContinues ++ environment) bodyStore
      (post.rename (shift 6)) (returnedValue value) final) :
    Evaluates (conditionPrefix type location ++ environment) initial
      (loopBody type condition body post reason) (returnedValue value) final :=
  loopBody_progress type reason location bodyContinues tested bodyEvaluated (advance_returned type postEvaluated)

theorem loopBody_postFailure {environment : Environment} {initial testedStore bodyStore final : Store}
    {condition body post : Expr} {failure : Word} (type : Ty) (reason : Word) (location : Location)
    (bodyContinues : Bool)
    (tested : Evaluates (conditionPrefix type location ++ environment) initial
      (condition.rename (shift 2)) (.inRight .word (.bool true)) testedStore)
    (bodyEvaluated : Evaluates (bodyPrefix type location ++ environment) testedStore
      (body.rename (shift 3)) (advanceValue type bodyContinues) bodyStore)
    (postEvaluated : Evaluates (postPrefix type location bodyContinues ++ environment) bodyStore
      (post.rename (shift 6)) (.inLeft (controlType type) (.word failure)) final) :
    Evaluates (conditionPrefix type location ++ environment) initial
      (loopBody type condition body post reason) (.inLeft (controlType type) (.word failure)) final :=
  loopBody_progress type reason location bodyContinues tested bodyEvaluated (advance_failure type postEvaluated)

/-- Reenter an installed loop closure from any caller expression and caller
environment. Its captured lexical environment is the original one. -/
theorem invoke_existing {environment caller : Environment} {initial referenceStore final : Store}
    {condition body post reference : Expr} {result : Value} (type : Ty) (reason : Word) (location : Location)
    (referenceEvaluated : Evaluates caller initial reference (selfReference type location) referenceStore)
    (installed : referenceStore.read? location =
      some (.inRight .unit (installedClosure type condition body post reason location environment)))
    (continued : Evaluates (conditionPrefix type location ++ environment) referenceStore
      (loopBody type condition body post reason) result final) :
    Evaluates caller initial (invoke type reference reason) result final :=
  invoke_success type reason referenceEvaluated installed continued

theorem restartPrefix_reference (type : Ty) (location : Location) (bodyContinues postContinues : Bool)
    (environment : Environment) :
    (restartPrefix type location bodyContinues postContinues ++ environment)[8]? =
      some (selfReference type location) := by
  cases bodyContinues <;> cases postContinues <;> rfl

/-- Both normal fallthrough and continue run post and reenter the existing
closure. The caller supplies the self-cell lookup after all intervening
effects, so preservation of that cell is never assumed implicitly. -/
theorem loopBody_step {environment : Environment} {initial testedStore bodyStore postStore final : Store}
    {condition body post : Expr} {result : Value} (type : Ty) (reason : Word) (location : Location)
    (bodyContinues postContinues : Bool)
    (tested : Evaluates (conditionPrefix type location ++ environment) initial
      (condition.rename (shift 2)) (.inRight .word (.bool true)) testedStore)
    (bodyEvaluated : Evaluates (bodyPrefix type location ++ environment) testedStore
      (body.rename (shift 3)) (advanceValue type bodyContinues) bodyStore)
    (postEvaluated : Evaluates (postPrefix type location bodyContinues ++ environment) bodyStore
      (post.rename (shift 6)) (advanceValue type postContinues) postStore)
    (installed : postStore.read? location =
      some (.inRight .unit (installedClosure type condition body post reason location environment)))
    (continued : Evaluates (conditionPrefix type location ++ environment) postStore
      (loopBody type condition body post reason) result final) :
    Evaluates (conditionPrefix type location ++ environment) initial
      (loopBody type condition body post reason) result final := by
  apply loopBody_progress type reason location bodyContinues tested bodyEvaluated
  apply advance_progress type postContinues postEvaluated
  have invoked := invoke_existing type reason location
    (Evaluates.var (restartPrefix_reference type location bodyContinues postContinues environment)) installed continued
  simpa only [invoke_rename, Expr.rename, shift, restartPrefix, List.append_assoc] using invoked

/-- Actual allocation and installation produce the self-cell condition needed
by the first invocation. The supplied loop-body execution starts from exactly
that initialized store. -/
theorem iterate_start {environment : Environment} {initial final : Store}
    {condition body post : Expr} {result : Value} (type : Ty) (reason : Word)
    (continued : Evaluates (conditionPrefix type initial.length ++ environment)
      (initial ++ [.inRight .unit (installedClosure type condition body post reason initial.length environment)])
      (loopBody type condition body post reason) result final) :
    Evaluates environment initial (iterate type condition body post reason) result final := by
  apply iterate_evaluates type reason
  exact invoke_existing type reason initial.length (.var rfl) (by simp [Store.read?]) continued

end Solcore.Core.LocalLoop
