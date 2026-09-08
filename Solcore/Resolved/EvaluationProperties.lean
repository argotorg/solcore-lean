import Solcore.Resolved.Eval
import Solcore.Resolved.LocalScopeProperties
import Solcore.Resolved.LocalFragmentProperties
import Solcore.Core.LocalRightWordLessEvaluationProperties

/-! Exact named-to-positional evaluation correspondence for the resolved local
fragment. The independent relation preserves the store and is deterministic
even when a skipped branch prevents whole-expression lowering. -/

set_option autoImplicit false

namespace Solcore.Resolved

theorem Evaluates.toCore
    {environment : Environment} {initialStore finalStore : Core.Store}
    {expr : Expr} {value : Core.Value}
    (evaluation : Evaluates environment initialStore expr value finalStore)
    {core : Core.Expr} (lowered : Lowers (LocalScope.ids environment) expr core) :
    Core.Evaluates (LocalScope.values environment) initialStore core value finalStore := by
  induction evaluation generalizing core with
  | unit => cases lowered; exact .unit
  | bool => cases lowered; exact .bool
  | word => cases lowered; exact .word
  | pair _ _ leftIH rightIH =>
      cases lowered with
      | pair left right => exact .pair (leftIH left) (rightIH right)
  | var found =>
      cases lowered with
      | var indexed =>
          exact .var ((LocalScope.lookup_iff_getElem? indexed).mp found)
  | unary _ applied ih =>
      cases lowered with
      | unary child => exact .unary (ih child) applied
  | binary _ _ applied leftIH rightIH =>
      cases lowered with
      | binary left right => exact .binary (leftIH left) (rightIH right) applied
  | wordLt _ _ leftIH rightIH =>
      cases lowered with
      | wordLt left right =>
          exact (leftIH left).wordLt_local_right (rightIH right) right.localFragment
  | letE _ _ valueIH bodyIH =>
      cases lowered with
      | letE value body => exact .letE (valueIH value) (bodyIH body)
  | ifTrue _ _ conditionIH branchIH =>
      cases lowered with
      | ifE condition thenBranch _ => exact .ifTrue (conditionIH condition) (branchIH thenBranch)
  | ifFalse _ _ conditionIH branchIH =>
      cases lowered with
      | ifE condition _ elseBranch => exact .ifFalse (conditionIH condition) (branchIH elseBranch)

private theorem evaluation_of_core_scope
    {scope : List LocalId} {expr : Expr} {core : Core.Expr}
    (lowered : Lowers scope expr core) :
    ∀ {environment : Environment} {initialStore finalStore : Core.Store} {value : Core.Value},
      LocalScope.ids environment = scope →
      Core.Evaluates (LocalScope.values environment) initialStore core value finalStore →
      Evaluates environment initialStore expr value finalStore := by
  induction lowered with
  | unit => intro environment initialStore finalStore value scopeEq evaluation; cases evaluation; exact .unit
  | bool => intro environment initialStore finalStore value scopeEq evaluation; cases evaluation; exact .bool
  | word => intro environment initialStore finalStore value scopeEq evaluation; cases evaluation; exact .word
  | pair left right leftIH rightIH =>
      intro environment initialStore finalStore value scopeEq evaluation
      cases evaluation with
      | pair leftEvaluation rightEvaluation =>
          exact .pair (leftIH scopeEq leftEvaluation) (rightIH scopeEq rightEvaluation)
  | var indexed =>
      intro environment initialStore finalStore value scopeEq evaluation
      cases evaluation with
      | var atValue => exact .var (LocalScope.lookup_of_indexed (scopeEq ▸ indexed) atValue)
  | unary child ih =>
      intro environment initialStore finalStore value scopeEq evaluation
      cases evaluation with
      | unary childEvaluation applied => exact .unary (ih scopeEq childEvaluation) applied
  | binary left right leftIH rightIH =>
      intro environment initialStore finalStore value scopeEq evaluation
      cases evaluation with
      | binary leftEvaluation rightEvaluation applied =>
          exact .binary (leftIH scopeEq leftEvaluation) (rightIH scopeEq rightEvaluation) applied
  | wordLt left right leftIH rightIH =>
      intro environment initialStore finalStore value scopeEq evaluation
      obtain ⟨leftWord, rightWord, middleStore, leftEvaluation, rightEvaluation, rfl⟩ :=
        evaluation.wordLt_inv_local_right right.localFragment
      exact .wordLt (leftIH scopeEq leftEvaluation) (rightIH scopeEq rightEvaluation)
  | letE lowerValue lowerBody valueIH bodyIH =>
      intro environment initialStore finalStore value scopeEq evaluation
      cases evaluation with
      | letE valueEvaluation bodyEvaluation =>
          exact .letE (valueIH scopeEq valueEvaluation)
            (bodyIH (by exact congrArg (List.cons _) scopeEq) bodyEvaluation)
  | ifE condition thenBranch elseBranch conditionIH thenIH elseIH =>
      intro environment initialStore finalStore value scopeEq evaluation
      cases evaluation with
      | ifTrue conditionEvaluation branchEvaluation =>
          exact .ifTrue (conditionIH scopeEq conditionEvaluation) (thenIH scopeEq branchEvaluation)
      | ifFalse conditionEvaluation branchEvaluation =>
          exact .ifFalse (conditionIH scopeEq conditionEvaluation) (elseIH scopeEq branchEvaluation)

theorem Evaluates.ofCore
    {environment : Environment} {initialStore finalStore : Core.Store}
    {expr : Expr} {core : Core.Expr} {value : Core.Value}
    (lowered : Lowers (LocalScope.ids environment) expr core)
    (evaluation : Core.Evaluates (LocalScope.values environment) initialStore core value finalStore) :
    Evaluates environment initialStore expr value finalStore :=
  evaluation_of_core_scope lowered rfl evaluation

theorem Lowers.evaluates_iff
    {environment : Environment} {initialStore finalStore : Core.Store}
    {expr : Expr} {core : Core.Expr} {value : Core.Value}
    (lowered : Lowers (LocalScope.ids environment) expr core) :
    Evaluates environment initialStore expr value finalStore ↔
      Core.Evaluates (LocalScope.values environment) initialStore core value finalStore :=
  ⟨fun evaluation => evaluation.toCore lowered, Evaluates.ofCore lowered⟩

/-- This fragment has no store-mutating constructor. The conclusion does not
require typing, closedness, or lowering of unselected conditional branches. -/
theorem Evaluates.store_eq
    {environment : Environment} {initialStore finalStore : Core.Store}
    {expr : Expr} {value : Core.Value}
    (evaluation : Evaluates environment initialStore expr value finalStore) :
    finalStore = initialStore := by
  induction evaluation with
  | unit | bool | word | var => rfl
  | unary _ _ ih => exact ih
  | pair _ _ leftIH rightIH => exact rightIH.trans leftIH
  | binary _ _ _ leftIH rightIH => exact rightIH.trans leftIH
  | wordLt _ _ leftIH rightIH => exact rightIH.trans leftIH
  | letE _ _ valueIH bodyIH => exact bodyIH.trans valueIH
  | ifTrue _ _ conditionIH branchIH | ifFalse _ _ conditionIH branchIH =>
      exact branchIH.trans conditionIH

/-- First-match local lookup and selected-branch evaluation are deterministic
without any separate successful elaboration premise. -/
theorem evaluation_deterministic
    {environment : Environment} {initialStore : Core.Store} {expr : Expr}
    {left right : Core.Value} {leftStore rightStore : Core.Store}
    (leftEvaluation : Evaluates environment initialStore expr left leftStore)
    (rightEvaluation : Evaluates environment initialStore expr right rightStore) :
    left = right ∧ leftStore = rightStore := by
  induction leftEvaluation generalizing right rightStore with
  | unit => cases rightEvaluation; exact ⟨rfl, rfl⟩
  | bool => cases rightEvaluation; exact ⟨rfl, rfl⟩
  | word => cases rightEvaluation; exact ⟨rfl, rfl⟩
  | pair _ _ leftIH rightIH =>
      cases rightEvaluation with
      | pair otherLeft otherRight =>
          obtain ⟨rfl, rfl⟩ := leftIH otherLeft
          obtain ⟨rfl, storeEquality⟩ := rightIH otherRight
          exact ⟨rfl, storeEquality⟩
  | var leftLookup =>
      cases rightEvaluation with
      | var rightLookup => exact ⟨leftLookup.value_unique rightLookup, rfl⟩
  | unary _ leftApplied operandIH =>
      cases rightEvaluation with
      | unary rightOperand rightApplied =>
          obtain ⟨rfl, storeEquality⟩ := operandIH rightOperand
          rw [leftApplied] at rightApplied
          cases rightApplied
          exact ⟨rfl, storeEquality⟩
  | binary _ _ leftApplied leftIH rightIH =>
      cases rightEvaluation with
      | binary otherLeft otherRight rightApplied =>
          obtain ⟨rfl, rfl⟩ := leftIH otherLeft
          obtain ⟨rfl, storeEquality⟩ := rightIH otherRight
          rw [leftApplied] at rightApplied
          cases rightApplied
          exact ⟨rfl, storeEquality⟩
  | letE _ _ valueIH bodyIH =>
      cases rightEvaluation with
      | letE rightValue rightBody =>
          obtain ⟨rfl, rfl⟩ := valueIH rightValue
          exact bodyIH rightBody
  | wordLt _ _ leftIH rightIH =>
      cases rightEvaluation with
      | wordLt otherLeft otherRight =>
          obtain ⟨sameLeft, rfl⟩ := leftIH otherLeft
          cases Core.Value.word.inj sameLeft
          obtain ⟨sameRight, sameStore⟩ := rightIH otherRight
          cases Core.Value.word.inj sameRight
          exact ⟨rfl, sameStore⟩
  | ifTrue _ _ conditionIH branchIH =>
      cases rightEvaluation with
      | ifTrue rightCondition rightBranch =>
          obtain ⟨_, rfl⟩ := conditionIH rightCondition
          exact branchIH rightBranch
      | ifFalse rightCondition _ =>
          obtain ⟨impossible, _⟩ := conditionIH rightCondition
          cases impossible
  | ifFalse _ _ conditionIH branchIH =>
      cases rightEvaluation with
      | ifTrue rightCondition _ =>
          obtain ⟨impossible, _⟩ := conditionIH rightCondition
          cases impossible
      | ifFalse rightCondition rightBranch =>
          obtain ⟨_, rfl⟩ := conditionIH rightCondition
          exact branchIH rightBranch

end Solcore.Resolved
