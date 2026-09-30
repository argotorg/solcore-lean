import Solcore.Core.LocalFragment.Basic
import Solcore.Core.Safety

/-!
# Structural termination of the local Core fragment

Local expressions can return closures and cell references supplied by their
environment, but cannot call them or inspect the store. Their termination
therefore needs neither store typing nor termination of those closures.
-/

set_option autoImplicit false

namespace Solcore.Core

/-- A typed local expression evaluates with the original store and world.
The store is arbitrary: local evaluation does not read or change it. -/
theorem Expr.LocalFragment.runtime_evaluates
    {definitions : DataEnvironment} {world : StoreTyping} {expr : Expr}
    (fragment : expr.LocalFragment)
    {context : Context} {type : Ty}
    (typing : HasType context expr type definitions)
    {environment : Environment}
    (environmentTyping : RuntimeEnvironmentHasTypes world environment context definitions)
    (store : Store) :
    ∃ value, Evaluates environment store expr value store ∧
      RuntimeValueHasType world value type definitions := by
  induction fragment generalizing context type environment with
  | unit => cases typing; exact ⟨.unit, .unit, .unit⟩
  | bool => cases typing; exact ⟨_, .bool, .bool⟩
  | word => cases typing; exact ⟨_, .word, .word⟩
  | var =>
      cases typing with
      | var found =>
          obtain ⟨value, lookup, valueTyping⟩ := environmentTyping.lookup found
          exact ⟨value, .var lookup, valueTyping⟩
  | pair _ _ leftIH rightIH =>
      cases typing with
      | pair leftTyping rightTyping =>
          obtain ⟨left, leftEvaluation, leftValueTyping⟩ := leftIH leftTyping environmentTyping
          obtain ⟨right, rightEvaluation, rightValueTyping⟩ := rightIH rightTyping environmentTyping
          exact ⟨.pair left right, .pair leftEvaluation rightEvaluation,
            .pair leftValueTyping rightValueTyping⟩
  | unary _ operandIH =>
      cases typing with
      | unary operandTyping =>
          obtain ⟨operand, operandEvaluation, operandValueTyping⟩ :=
            operandIH operandTyping environmentTyping
          obtain ⟨result, applied, _⟩ :=
            UnaryOp.apply_total_of_type _ operand operandValueTyping.type_eq
          exact ⟨result, .unary operandEvaluation applied,
            unary_apply_result_has_runtime_type applied definitions⟩
  | binary _ _ leftIH rightIH =>
      cases typing with
      | binary leftTyping rightTyping =>
          obtain ⟨left, leftEvaluation, leftValueTyping⟩ := leftIH leftTyping environmentTyping
          obtain ⟨right, rightEvaluation, rightValueTyping⟩ := rightIH rightTyping environmentTyping
          obtain ⟨result, applied, _⟩ :=
            BinaryOp.apply_total_of_types _ left right leftValueTyping.type_eq rightValueTyping.type_eq
          exact ⟨result, .binary leftEvaluation rightEvaluation applied,
            binary_apply_result_has_runtime_type applied definitions⟩
  | letE _ _ initializerIH bodyIH =>
      cases typing with
      | letE initializerTyping bodyTyping =>
          obtain ⟨bound, initializerEvaluation, boundTyping⟩ :=
            initializerIH initializerTyping environmentTyping
          obtain ⟨value, bodyEvaluation, valueTyping⟩ :=
            bodyIH bodyTyping (.cons boundTyping environmentTyping)
          exact ⟨value, .letE initializerEvaluation bodyEvaluation, valueTyping⟩
  | ifE _ _ _ conditionIH thenIH elseIH =>
      cases typing with
      | ifE conditionTyping thenTyping elseTyping =>
          obtain ⟨condition, conditionEvaluation, conditionValueTyping⟩ :=
            conditionIH conditionTyping environmentTyping
          obtain ⟨decision, rfl⟩ := conditionValueTyping.bool_shape
          cases decision with
          | false =>
              obtain ⟨value, branchEvaluation, valueTyping⟩ := elseIH elseTyping environmentTyping
              exact ⟨value, .ifFalse conditionEvaluation branchEvaluation, valueTyping⟩
          | true =>
              obtain ⟨value, branchEvaluation, valueTyping⟩ := thenIH thenTyping environmentTyping
              exact ⟨value, .ifTrue conditionEvaluation branchEvaluation, valueTyping⟩

end Solcore.Core
