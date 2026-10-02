import Solcore.SourceSemantics.CoreLowering.CoreHelperInversion
import Solcore.SourceSemantics.CoreLowering.TypedImperativeForReflection
import Solcore.Frontend.SourceCoreCompatibleDataPlaces

/-! Bounds obtained from the original emitted Core derivation. Known phase
executions align values and stores by determinism; every remaining size comes
from an actual child derivation. No continuation equivalence is assigned a
cost, and renaming beneath the six post values keeps the original size. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ForHeaderNativeBounds
open Core Frontend CoreProof
open SourceCoreCompatibleDataPlaces
open DataPlaceExecution (referenceEnvironment keysEnvironment snapshotEnvironment rhsEnvironment modifiedEnvironment writtenEnvironment)

/-- A marked allocation is a real let node, so its remaining body is smaller. -/
theorem allocation_body {size : Nat} {environment : Environment} {before middle after : Store}
    {allocation body : Expr} {reference value : Value}
    (completed : EvaluationSize size environment before (.letE allocation body) value after)
    (allocated : Evaluates environment before allocation reference middle) :
    ∃ remainingSize, remainingSize < size ∧
      EvaluationSize remainingSize (reference :: environment) middle body value after :=
  completed.let_body allocated

/-- Initialized headers retain both inserted values and both real boundaries. -/
theorem initialized_body {size : Nat} {environment : Environment} {before middle written after : Store}
    {output : Ty} {initializer allocation body : Expr} {input reference value : Value}
    (completed : EvaluationSize size environment before
      (LanguageResult.bind output initializer (.letE allocation body)) value after)
    (initialized : Evaluates environment before initializer (.inRight .word input) middle)
    (allocated : Evaluates (input :: environment) middle allocation reference written) :
    ∃ remainingSize, remainingSize < size ∧
      EvaluationSize remainingSize (reference :: input :: environment) written body value after := by
  obtain ⟨initialSize, first, initial⟩ := completed.bind_success initialized
  obtain ⟨remainingSize, second, remaining⟩ := initial.let_body allocated
  exact ⟨remainingSize, Nat.lt_trans second first, remaining⟩

/-- The discarded payload is an actual temporary slot, not a capture cast. -/
theorem discard_body {size : Nat} {environment : Environment} {before middle after : Store}
    {output : Ty} {computation body : Expr} {input value : Value}
    (completed : EvaluationSize size environment before (LocalSequence.discard output computation body) value after)
    (computed : Evaluates environment before computation (.inRight .word input) middle) :
    ∃ remainingSize, remainingSize < size ∧
      EvaluationSize remainingSize (input :: environment) middle (body.weakenAt 0) value after :=
  completed.bind_success computed

/-- Success through the seven actual assignment slots exposes a strict native
continuation. The premises are the same phase executions as execute_success,
with the actual compatible getter and setter. No child source meaning is used. -/
theorem execute_continuation {size : Nat} {prepared : Prepared} {reference rhs next : Expr} {keys : SourceCoreBasic.LoweredExpr}
    {outputType : Ty} {operator : Option BinaryOp} {bitNot : Bool} {invalidOperand : Word}
    {environment : Environment} {before keyStore snapshotStore rhsStore modifiedStore setterStore written finalStore : Store}
    {location : Location} {keyValue snapshot right changed updated old result : Value}
    (referenceSelected : DataEquality.Selects environment reference (.cellRef (OptionalCell.cellType prepared.route.rootType) location))
    (keysEvaluated : Evaluates (referenceEnvironment prepared.route.rootType location environment) before
      (shift 1 keys.expression) (.inRight .word keyValue) keyStore)
    (snapshotEvaluated : Evaluates (keysEnvironment prepared.route.rootType location keyValue environment) keyStore
      (.apply (getter prepared keys.type) (.pair (.loadCell (.var 1)) (.var 0))) (.inRight .word snapshot) snapshotStore)
    (rhsEvaluated : Evaluates (snapshotEnvironment prepared.route.rootType location keyValue snapshot environment) snapshotStore
      (shift 3 rhs) (.inRight .word right) rhsStore)
    (modifiedEvaluated : Evaluates (rhsEnvironment prepared.route.rootType location keyValue snapshot right environment) rhsStore
      (modified prepared.route.leafType operator bitNot (.var 1) (.var 0) invalidOperand) (.inRight .word changed) modifiedStore)
    (setterEvaluated : Evaluates (modifiedEnvironment prepared.route.rootType location keyValue snapshot right changed environment) modifiedStore
      (.apply (setter prepared keys.type) (.pair (.loadCell (.var 4)) (.pair (.var 3) (.var 0)))) (.inRight .word updated) setterStore)
    (read : setterStore.read? location = some old)
    (write : setterStore.write? location (.inRight .unit updated) = some written)
    (completed : EvaluationSize size environment before
      (execute prepared reference keys rhs next outputType operator bitNot invalidOperand) result finalStore) :
    ∃ remainingSize, remainingSize < size ∧
      EvaluationSize remainingSize
        (writtenEnvironment prepared.route.rootType location keyValue snapshot right changed updated environment)
        written (shift 7 next) result finalStore := by
  obtain ⟨referenceSize, first, referenceRest⟩ := completed.let_body (referenceSelected.evaluates before)
  obtain ⟨keysSize, second, keysRest⟩ := referenceRest.bind_success keysEvaluated
  obtain ⟨snapshotSize, third, snapshotRest⟩ := keysRest.bind_success snapshotEvaluated
  obtain ⟨rhsSize, fourth, rhsRest⟩ := snapshotRest.bind_success rhsEvaluated
  obtain ⟨modifiedSize, fifth, modifiedRest⟩ := rhsRest.bind_success modifiedEvaluated
  obtain ⟨setterSize, sixth, setterRest⟩ := modifiedRest.bind_success setterEvaluated
  obtain ⟨remainingSize, seventh, remaining⟩ := setterRest.let_body
    (.storeCell (.var rfl) read (.inRight (.var rfl)) write)
  exact ⟨remainingSize, by omega, remaining⟩

/-- Moving into the actual six-value post environment changes syntax only.
It does not change or regenerate the supplied Core size. -/
theorem post_rename_size {size : Nat} {actual : Environment} {before after : Store}
    {type : Ty} {location : Location} {continued : Bool} {code : Expr} {ξ : Renaming} {value : Value} :
    EvaluationSize size (TypedImperativeFor.postValues type location continued ++ actual) before
      (ForLoop.postCode (code.rename ξ)) value after ↔
    EvaluationSize size (TypedImperativeFor.postValues type location continued ++ actual) before
      (code.rename ((fun index => index + 6).comp ξ)) value after := by
  rw [TypedImperativeFor.post_rename]

open TypedImperativeFor (postValues)

private theorem insertion_zero : Renaming.insertion 0 = (fun index => index + 1) := by
  funext index
  simp [Renaming.insertion]

private theorem shift_comp (left right : Nat) :
    Renaming.comp (fun index => index + left) (fun index => index + right) =
      (fun index => index + (right + left)) := by
  funext index
  simp [Renaming.comp, Nat.add_assoc]

set_option maxRecDepth 3000 in
/-- Inversion of the actual body envelope exposes the actual post computation.
The four branch temporaries and Unit/self slots retain their concrete values. -/
theorem post_computation_sized {size : Nat} {actual : Environment} {before bodyStore after : Store}
    {type : Ty} {location : Location} {body post : Expr} {reason : Word} {value : Value}
    (continued : Bool)
    (evaluation : EvaluationSize size (Core.LoopExecution.bodyEnvironment type location actual) before
      (LocalLoop.advance type (Core.LoopExecution.bodyCode body)
        ((LocalLoop.advance type (Core.LoopExecution.conditionCode post) (LocalLoop.invoke type (.var 1) reason)).weakenAt 0)) value after)
    (bodyEval : Evaluates (Core.LoopExecution.bodyEnvironment type location actual) before
      (Core.LoopExecution.bodyCode body) (if continued then LocalLoop.continuingValue type else LocalLoop.fallthroughValue type) bodyStore) :
    ∃ postSize postStore postValue, postSize < size ∧
      EvaluationSize postSize (postValues type location continued ++ actual) bodyStore (ForLoop.postCode post) postValue postStore := by
  cases continued
  · obtain ⟨next, nextSmaller, postAdvance⟩ := evaluation.advance_fallthrough bodyEval
    have renamed : EvaluationSize next
        (ForLoop.fallthroughPrefix type ++ Core.LoopExecution.entryEnvironment type location actual) bodyStore
        ((LocalLoop.advance type (Core.LoopExecution.conditionCode post) (LocalLoop.invoke type (.var 1) reason)).rename
          (fun index => index + 4)) value after := by
      simpa only [← Expr.rename_insertion, Expr.rename_comp, insertion_zero, shift_comp, Nat.reduceAdd, Core.LoopExecution.bodyEnvironment, Core.LoopExecution.entryEnvironment, ForLoop.fallthroughPrefix, ForLoop.continuingPrefix, List.cons_append, List.nil_append] using postAdvance
    rw [LoopRenaming.advance] at renamed
    obtain ⟨postSize, store, result, postSmaller, evaluated⟩ := renamed.bind_computation
    exact ⟨postSize, store, result, Nat.lt_trans postSmaller nextSmaller, evaluated⟩
  · obtain ⟨next, nextSmaller, postAdvance⟩ := evaluation.advance_continuing bodyEval
    have renamed : EvaluationSize next
        (ForLoop.continuingPrefix type ++ Core.LoopExecution.entryEnvironment type location actual) bodyStore
        ((LocalLoop.advance type (Core.LoopExecution.conditionCode post) (LocalLoop.invoke type (.var 1) reason)).rename
          (fun index => index + 4)) value after := by
      simpa only [← Expr.rename_insertion, Expr.rename_comp, insertion_zero, shift_comp, Nat.reduceAdd, Core.LoopExecution.bodyEnvironment, Core.LoopExecution.entryEnvironment, ForLoop.fallthroughPrefix, ForLoop.continuingPrefix, List.cons_append, List.nil_append] using postAdvance
    rw [LoopRenaming.advance] at renamed
    obtain ⟨postSize, store, result, postSmaller, evaluated⟩ := renamed.bind_computation
    exact ⟨postSize, store, result, Nat.lt_trans postSmaller nextSmaller, evaluated⟩

end Solcore.SourceSemantics.CoreLowering.ForHeaderNativeBounds
