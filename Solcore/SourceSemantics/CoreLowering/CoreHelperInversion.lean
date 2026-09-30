import Solcore.SourceSemantics.CoreLowering.CoreEvaluationSize
import Solcore.Core.LocalLoop

/-! Invert finite evaluations of actual Core helpers while retaining a strict
bound on the continuation derivation. Known firstEvaluation evaluations are compared
using Core determinism; no source execution is assumed by these lemmas. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.CoreProof

open Core

theorem EvaluationSize.case_left
    {size : Nat} {environment : Environment} {before middle after : Store}
    {scrutinee left right : Expr} {rightType : Ty} {payload result : Value}
    (evaluation : EvaluationSize size environment before (.caseE scrutinee left right) result after)
    (firstEvaluation : Evaluates environment before scrutinee (.inLeft rightType payload) middle) :
    ∃ smaller, smaller < size ∧ EvaluationSize smaller (payload :: environment) middle left result after := by
  cases evaluation with
  | caseLeft other branch =>
    obtain ⟨same, rfl⟩ := evaluation_deterministic other.sound firstEvaluation
    cases same
    exact ⟨_, by omega, branch⟩
  | caseRight other _ =>
    obtain ⟨impossible, _⟩ := evaluation_deterministic other.sound firstEvaluation
    cases impossible

theorem EvaluationSize.case_right
    {size : Nat} {environment : Environment} {before middle after : Store}
    {scrutinee left right : Expr} {leftType : Ty} {payload result : Value}
    (evaluation : EvaluationSize size environment before (.caseE scrutinee left right) result after)
    (firstEvaluation : Evaluates environment before scrutinee (.inRight leftType payload) middle) :
    ∃ smaller, smaller < size ∧ EvaluationSize smaller (payload :: environment) middle right result after := by
  cases evaluation with
  | caseRight other branch =>
    obtain ⟨same, rfl⟩ := evaluation_deterministic other.sound firstEvaluation
    cases same
    exact ⟨_, by omega, branch⟩
  | caseLeft other _ =>
    obtain ⟨impossible, _⟩ := evaluation_deterministic other.sound firstEvaluation
    cases impossible

theorem EvaluationSize.let_body
    {size : Nat} {environment : Environment} {before middle after : Store}
    {initializer body : Expr} {bound result : Value}
    (evaluation : EvaluationSize size environment before (.letE initializer body) result after)
    (firstEvaluation : Evaluates environment before initializer bound middle) :
    ∃ smaller, smaller < size ∧ EvaluationSize smaller (bound :: environment) middle body result after := by
  cases evaluation with
  | letE other branch =>
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic other.sound firstEvaluation
    exact ⟨_, by omega, branch⟩

theorem EvaluationSize.if_true
    {size : Nat} {environment : Environment} {before middle after : Store}
    {condition left right : Expr} {result : Value}
    (evaluation : EvaluationSize size environment before (.ifE condition left right) result after)
    (firstEvaluation : Evaluates environment before condition (.bool true) middle) :
    ∃ smaller, smaller < size ∧ EvaluationSize smaller environment middle left result after := by
  cases evaluation with
  | ifTrue other branch =>
    obtain ⟨_, rfl⟩ := evaluation_deterministic other.sound firstEvaluation
    exact ⟨_, by omega, branch⟩
  | ifFalse other _ =>
    obtain ⟨impossible, _⟩ := evaluation_deterministic other.sound firstEvaluation
    cases impossible

theorem EvaluationSize.if_false
    {size : Nat} {environment : Environment} {before middle after : Store}
    {condition left right : Expr} {result : Value}
    (evaluation : EvaluationSize size environment before (.ifE condition left right) result after)
    (firstEvaluation : Evaluates environment before condition (.bool false) middle) :
    ∃ smaller, smaller < size ∧ EvaluationSize smaller environment middle right result after := by
  cases evaluation with
  | ifFalse other branch =>
    obtain ⟨_, rfl⟩ := evaluation_deterministic other.sound firstEvaluation
    exact ⟨_, by omega, branch⟩
  | ifTrue other _ =>
    obtain ⟨impossible, _⟩ := evaluation_deterministic other.sound firstEvaluation
    cases impossible

theorem EvaluationSize.apply_body
    {size : Nat} {environment captured : Environment} {before argumentStore bodyStore after : Store}
    {function argument body : Expr} {parameterType resultType : Ty} {input result : Value}
    (evaluation : EvaluationSize size environment before (.apply function argument) result after)
    (callee : Evaluates environment before function (.closure parameterType resultType body captured) argumentStore)
    (argumentEvaluation : Evaluates environment argumentStore argument input bodyStore) :
    ∃ smaller, smaller < size ∧ EvaluationSize smaller (input :: captured) bodyStore body result after := by
  cases evaluation with
  | apply otherFunction otherArgument bodyEvaluation =>
    obtain ⟨same, rfl⟩ := evaluation_deterministic otherFunction.sound callee
    cases same
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic otherArgument.sound argumentEvaluation
    exact ⟨_, by omega, bodyEvaluation⟩

theorem EvaluationSize.bind_success
    {size : Nat} {environment : Environment} {before middle after : Store}
    {type : Ty} {computation body : Expr} {payload result : Value}
    (evaluation : EvaluationSize size environment before (LanguageResult.bind type computation body) result after)
    (firstEvaluation : Evaluates environment before computation (.inRight .word payload) middle) :
    ∃ smaller, smaller < size ∧ EvaluationSize smaller (payload :: environment) middle body result after :=
  evaluation.case_right firstEvaluation

theorem EvaluationSize.choose_true
    {size : Nat} {environment : Environment} {before middle after : Store}
    {type : Ty} {condition left right : Expr} {result : Value}
    (evaluation : EvaluationSize size environment before (LocalControl.choose type condition left right) result after)
    (firstEvaluation : Evaluates environment before condition (.inRight .word (.bool true)) middle) :
    ∃ smaller, smaller < size ∧ EvaluationSize smaller (.bool true :: environment) middle (left.weakenAt 0) result after := by
  obtain ⟨next, smaller, continuation⟩ := evaluation.bind_success firstEvaluation
  obtain ⟨last, smallerAgain, branch⟩ := continuation.if_true (.var rfl)
  exact ⟨last, Nat.lt_trans smallerAgain smaller, branch⟩

theorem EvaluationSize.choose_false
    {size : Nat} {environment : Environment} {before middle after : Store}
    {type : Ty} {condition left right : Expr} {result : Value}
    (evaluation : EvaluationSize size environment before (LocalControl.choose type condition left right) result after)
    (firstEvaluation : Evaluates environment before condition (.inRight .word (.bool false)) middle) :
    ∃ smaller, smaller < size ∧ EvaluationSize smaller (.bool false :: environment) middle (right.weakenAt 0) result after := by
  obtain ⟨next, smaller, continuation⟩ := evaluation.bind_success firstEvaluation
  obtain ⟨last, smallerAgain, branch⟩ := continuation.if_false (.var rfl)
  exact ⟨last, Nat.lt_trans smallerAgain smaller, branch⟩

theorem EvaluationSize.sequence_fallthrough
    {size : Nat} {environment : Environment} {before middle after : Store}
    {type : Ty} {computation next : Expr} {result : Value}
    (evaluation : EvaluationSize size environment before (LocalLoop.sequence type computation next) result after)
    (firstEvaluation : Evaluates environment before computation (LocalLoop.fallthroughValue type) middle) :
    ∃ smaller, smaller < size ∧ EvaluationSize smaller
      (.unit :: .inLeft type .unit :: .inLeft LocalLoop.transferType (.inLeft type .unit) :: environment)
      middle (((next.weakenAt 0).weakenAt 0).weakenAt 0) result after := by
  obtain ⟨first, smaller, branch⟩ := evaluation.bind_success firstEvaluation
  obtain ⟨second, smallerAgain, branch⟩ := branch.case_left (.var rfl)
  obtain ⟨third, smallerLast, branch⟩ := branch.case_left (.var rfl)
  exact ⟨third, Nat.lt_trans smallerLast (Nat.lt_trans smallerAgain smaller), branch⟩

theorem EvaluationSize.invoke_body
    {size : Nat} {environment captured : Environment} {before middle after : Store}
    {type : Ty} {reason : Word} {reference body : Expr} {location : Location} {result : Value}
    (evaluation : EvaluationSize size environment before (LocalLoop.invoke type reference reason) result after)
    (referenceEvaluation : Evaluates environment before reference
      (.cellRef (OptionalCell.cellType (LocalLoop.functionType type)) location) middle)
    (installed : middle.read? location = some (.inRight .unit (.closure .unit (LocalLoop.resultType type) body captured))) :
    ∃ smaller, smaller < size ∧ EvaluationSize smaller (.unit :: captured) middle body result after := by
  obtain ⟨first, smaller, application⟩ := evaluation.bind_success (OptionalCell.read_success reason referenceEvaluation installed)
  obtain ⟨second, smallerAgain, body⟩ := application.apply_body (.var rfl) .unit
  exact ⟨second, Nat.lt_trans smallerAgain smaller, body⟩

/-- The exact installed closure and store are forced by the generated prelude.
Its finite entry-body derivation is strictly smaller than the whole loop. -/
theorem EvaluationSize.iterate_entry
    {size : Nat} {environment : Environment} {before after : Store}
    {type : Ty} {reason : Word} {condition body post : Expr} {result : Value}
    (evaluation : EvaluationSize size environment before (LocalLoop.iterate type condition body post reason) result after) :
    ∃ smaller, smaller < size ∧ EvaluationSize smaller
      (.unit :: .cellRef (OptionalCell.cellType (LocalLoop.functionType type)) before.length :: environment)
      (before ++ [.inRight .unit (LocalLoop.installedClosure type condition body post reason before.length environment)])
      (LocalLoop.loopBody type condition body post reason) result after := by
  obtain ⟨first, smaller, storeSelf⟩ := evaluation.let_body (OptionalCell.allocate_evaluates _ _ _)
  have write : Evaluates
      (.cellRef (OptionalCell.cellType (LocalLoop.functionType type)) before.length :: environment)
      (before ++ [.inLeft (LocalLoop.functionType type) .unit])
      (.storeCell (.var 0) (.inRight .unit (.lambda .unit (LocalLoop.resultType type)
        (LocalLoop.loopBody type condition body post reason)))) .unit
      (before ++ [.inRight .unit (LocalLoop.installedClosure type condition body post reason before.length environment)]) := by
    apply Evaluates.storeCell (oldValue := .inLeft (LocalLoop.functionType type) .unit) (.var rfl)
    · simp [Store.read?]
    · exact .inRight .lambda
    · simp [Store.write?, LocalLoop.installedClosure]
  obtain ⟨second, smallerAgain, invoke⟩ := storeSelf.let_body write
  obtain ⟨third, smallerLast, bodyEval⟩ := invoke.invoke_body
    (body := LocalLoop.loopBody type condition body post reason)
    (captured := .cellRef (OptionalCell.cellType (LocalLoop.functionType type)) before.length :: environment)
    (.var rfl) (by simp [Store.read?, LocalLoop.installedClosure])
  exact ⟨third, Nat.lt_trans smallerLast (Nat.lt_trans smallerAgain smaller), bodyEval⟩


/-- Inspect the computation of a bind without assuming either language-result
branch, then use its smaller certificate to reconstruct its source meaning. -/
theorem EvaluationSize.bind_computation
    {size : Nat} {environment : Environment} {before after : Store}
    {type : Ty} {computation body : Expr} {result : Value}
    (evaluation : EvaluationSize size environment before (LanguageResult.bind type computation body) result after) :
    ∃ smaller middle value, smaller < size ∧ EvaluationSize smaller environment before computation value middle := by
  cases evaluation with
  | caseLeft computation _ => exact ⟨_, _, _, by omega, computation⟩
  | caseRight computation _ => exact ⟨_, _, _, by omega, computation⟩

theorem EvaluationSize.advance_fallthrough
    {size : Nat} {environment : Environment} {before middle after : Store}
    {type : Ty} {computation next : Expr} {result : Value}
    (evaluation : EvaluationSize size environment before (LocalLoop.advance type computation next) result after)
    (firstEvaluation : Evaluates environment before computation (LocalLoop.fallthroughValue type) middle) :
    ∃ smaller, smaller < size ∧ EvaluationSize smaller
      (.unit :: .inLeft type .unit :: .inLeft LocalLoop.transferType (.inLeft type .unit) :: environment)
      middle (((next.weakenAt 0).weakenAt 0).weakenAt 0) result after := by
  obtain ⟨first, smaller, branch⟩ := evaluation.bind_success firstEvaluation
  obtain ⟨second, smallerAgain, branch⟩ := branch.case_left (.var rfl)
  obtain ⟨third, smallerLast, branch⟩ := branch.case_left (.var rfl)
  exact ⟨third, Nat.lt_trans smallerLast (Nat.lt_trans smallerAgain smaller), branch⟩

theorem EvaluationSize.advance_continuing
    {size : Nat} {environment : Environment} {before middle after : Store}
    {type : Ty} {computation next : Expr} {result : Value}
    (evaluation : EvaluationSize size environment before (LocalLoop.advance type computation next) result after)
    (firstEvaluation : Evaluates environment before computation (LocalLoop.continuingValue type) middle) :
    ∃ smaller, smaller < size ∧ EvaluationSize smaller
      (.unit :: .inRight .unit .unit :: .inRight (LocalControl.controlType type) (.inRight .unit .unit) :: environment)
      middle (((next.weakenAt 0).weakenAt 0).weakenAt 0) result after := by
  obtain ⟨first, smaller, branch⟩ := evaluation.bind_success firstEvaluation
  obtain ⟨second, smallerAgain, branch⟩ := branch.case_right (.var rfl)
  obtain ⟨third, smallerLast, branch⟩ := branch.case_right (.var rfl)
  exact ⟨third, Nat.lt_trans smallerLast (Nat.lt_trans smallerAgain smaller), branch⟩

end Solcore.SourceSemantics.CoreLowering.CoreProof
