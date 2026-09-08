import Solcore.Frontend.LocalExpressionCostRenamingProperties
import Solcore.Frontend.LocalInputsExtensionSemantics

/-! Structural preservation of independent source costs under identity
relabeling and unused-name insertion. Erased evaluation is used only at
identifier leaves to recover existing lookup laws, not to equate costs. -/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Avoidance covers every written child, including unselected branches and
arbitrary literal payloads. Freshness alone does not prevent spelling shadowing.
This is an exact raw-cost law, not equality of suspended machine states. -/
theorem AvoidsLocalName.bindFresh_cost_iff {name : String} {source : Syntax.Expr}
    (avoids : AvoidsLocalName name source) (inputs : LocalInputs)
    (owner : Resolved.DeclarationId) (newType : Core.Ty) (newValue : Core.Value)
    (valueTyped : Core.ValueHasType newValue newType)
    {initialStore finalStore : Core.Store} {result : Core.Value} {cost : Nat} :
    LocalExpressionEvaluatesWithCost (inputs.bindFresh owner name newType newValue valueTyped).names
        (inputs.bindFresh owner name newType newValue valueTyped).environment
        initialStore source result finalStore cost ↔
      LocalExpressionEvaluatesWithCost inputs.names inputs.environment
        initialStore source result finalStore cost := by
  induction avoids generalizing initialStore finalStore result cost with
  | identifier different =>
      constructor
      · intro evaluation
        have ordinary := ((AvoidsLocalName.identifier different).bindFresh_evaluates_iff
          inputs owner newType newValue valueTyped).mp evaluation.erase
        cases evaluation with
        | identifier _ _ =>
            cases ordinary with
            | identifier named found => exact .identifier named found
      · intro evaluation
        have ordinary := ((AvoidsLocalName.identifier different).bindFresh_evaluates_iff
          inputs owner newType newValue valueTyped).mpr evaluation.erase
        cases evaluation with
        | identifier _ _ =>
            cases ordinary with
            | identifier named found => exact .identifier named found
  | literal =>
      constructor
      · intro evaluation
        cases evaluation with
        | wordLiteral meaning => exact .wordLiteral meaning
      · intro evaluation
        cases evaluation with
        | wordLiteral meaning => exact .wordLiteral meaning
  | unit => constructor <;> intro evaluation <;> cases evaluation <;> exact .unit
  | group _ ih =>
      constructor
      · intro evaluation
        cases evaluation with
        | group child => exact .group (ih.mp child)
      · intro evaluation
        cases evaluation with
        | group child => exact .group (ih.mpr child)
  | pair _ _ leftIH rightIH =>
      constructor
      · intro evaluation
        cases evaluation with
        | pair left right => exact .pair (leftIH.mp left) (rightIH.mp right)
      · intro evaluation
        cases evaluation with
        | pair left right => exact .pair (leftIH.mpr left) (rightIH.mpr right)
  | logicalNot _ ih =>
      constructor
      · intro evaluation
        cases evaluation with
        | logicalNot child => exact .logicalNot (ih.mp child)
      · intro evaluation
        cases evaluation with
        | logicalNot child => exact .logicalNot (ih.mpr child)
  | bitNot _ ih =>
      constructor
      · intro evaluation
        cases evaluation with
        | bitNot child => exact .bitNot (ih.mp child)
      · intro evaluation
        cases evaluation with
        | bitNot child => exact .bitNot (ih.mpr child)
  | add _ _ leftIH rightIH =>
      constructor
      · intro evaluation
        cases evaluation with
        | add left right => exact .add (leftIH.mp left) (rightIH.mp right)
      · intro evaluation
        cases evaluation with
        | add left right => exact .add (leftIH.mpr left) (rightIH.mpr right)
  | subtract _ _ leftIH rightIH =>
      constructor
      · intro evaluation
        cases evaluation with
        | subtract left right => exact .subtract (leftIH.mp left) (rightIH.mp right)
      · intro evaluation
        cases evaluation with
        | subtract left right => exact .subtract (leftIH.mpr left) (rightIH.mpr right)
  | multiply _ _ leftIH rightIH =>
      constructor
      · intro evaluation
        cases evaluation with
        | multiply left right => exact .multiply (leftIH.mp left) (rightIH.mp right)
      · intro evaluation
        cases evaluation with
        | multiply left right => exact .multiply (leftIH.mpr left) (rightIH.mpr right)
  | divide _ _ leftIH rightIH =>
      constructor
      · intro evaluation
        cases evaluation with
        | divide left right => exact .divide (leftIH.mp left) (rightIH.mp right)
      · intro evaluation
        cases evaluation with
        | divide left right => exact .divide (leftIH.mpr left) (rightIH.mpr right)
  | modulo _ _ leftIH rightIH =>
      constructor
      · intro evaluation
        cases evaluation with
        | modulo left right => exact .modulo (leftIH.mp left) (rightIH.mp right)
      · intro evaluation
        cases evaluation with
        | modulo left right => exact .modulo (leftIH.mpr left) (rightIH.mpr right)
  | greater _ _ leftIH rightIH =>
      constructor
      · intro evaluation
        cases evaluation with
        | greater left right => exact .greater (leftIH.mp left) (rightIH.mp right)
      · intro evaluation
        cases evaluation with
        | greater left right => exact .greater (leftIH.mpr left) (rightIH.mpr right)
  | less _ _ leftIH rightIH =>
      constructor
      · intro evaluation
        cases evaluation with
        | less left right => exact .less (leftIH.mp left) (rightIH.mp right)
      · intro evaluation
        cases evaluation with
        | less left right => exact .less (leftIH.mpr left) (rightIH.mpr right)
  | equal _ _ leftIH rightIH =>
      constructor
      · intro evaluation
        cases evaluation with
        | equal left right => exact .equal (leftIH.mp left) (rightIH.mp right)
      · intro evaluation
        cases evaluation with
        | equal left right => exact .equal (leftIH.mpr left) (rightIH.mpr right)
  | notEqual _ _ leftIH rightIH =>
      constructor
      · intro evaluation
        cases evaluation with
        | notEqual left right => exact .notEqual (leftIH.mp left) (rightIH.mp right)
      · intro evaluation
        cases evaluation with
        | notEqual left right => exact .notEqual (leftIH.mpr left) (rightIH.mpr right)
  | lessEqual _ _ leftIH rightIH =>
      constructor
      · intro evaluation
        cases evaluation with
        | lessEqual left right => exact .lessEqual (leftIH.mp left) (rightIH.mp right)
      · intro evaluation
        cases evaluation with
        | lessEqual left right => exact .lessEqual (leftIH.mpr left) (rightIH.mpr right)
  | greaterEqual _ _ leftIH rightIH =>
      constructor
      · intro evaluation
        cases evaluation with
        | greaterEqual left right => exact .greaterEqual (leftIH.mp left) (rightIH.mp right)
      · intro evaluation
        cases evaluation with
        | greaterEqual left right => exact .greaterEqual (leftIH.mpr left) (rightIH.mpr right)
  | bitAnd _ _ leftIH rightIH =>
      constructor
      · intro evaluation
        cases evaluation with
        | bitAnd left right => exact .bitAnd (leftIH.mp left) (rightIH.mp right)
      · intro evaluation
        cases evaluation with
        | bitAnd left right => exact .bitAnd (leftIH.mpr left) (rightIH.mpr right)
  | bitOr _ _ leftIH rightIH =>
      constructor
      · intro evaluation
        cases evaluation with
        | bitOr left right => exact .bitOr (leftIH.mp left) (rightIH.mp right)
      · intro evaluation
        cases evaluation with
        | bitOr left right => exact .bitOr (leftIH.mpr left) (rightIH.mpr right)
  | bitXor _ _ leftIH rightIH =>
      constructor
      · intro evaluation
        cases evaluation with
        | bitXor left right => exact .bitXor (leftIH.mp left) (rightIH.mp right)
      · intro evaluation
        cases evaluation with
        | bitXor left right => exact .bitXor (leftIH.mpr left) (rightIH.mpr right)
  | logicalAnd _ _ leftIH rightIH =>
      constructor
      · intro evaluation
        cases evaluation with
        | andTrue left right => exact .andTrue (leftIH.mp left) (rightIH.mp right)
        | andFalse left => exact .andFalse (leftIH.mp left)
      · intro evaluation
        cases evaluation with
        | andTrue left right => exact .andTrue (leftIH.mpr left) (rightIH.mpr right)
        | andFalse left => exact .andFalse (leftIH.mpr left)
  | logicalOr _ _ leftIH rightIH =>
      constructor
      · intro evaluation
        cases evaluation with
        | orTrue left => exact .orTrue (leftIH.mp left)
        | orFalse left right => exact .orFalse (leftIH.mp left) (rightIH.mp right)
      · intro evaluation
        cases evaluation with
        | orTrue left => exact .orTrue (leftIH.mpr left)
        | orFalse left right => exact .orFalse (leftIH.mpr left) (rightIH.mpr right)
  | conditional _ _ _ conditionIH thenIH elseIH =>
      constructor
      · intro evaluation
        cases evaluation with
        | ifTrue condition branch => exact .ifTrue (conditionIH.mp condition) (thenIH.mp branch)
        | ifFalse condition branch => exact .ifFalse (conditionIH.mp condition) (elseIH.mp branch)
      · intro evaluation
        cases evaluation with
        | ifTrue condition branch => exact .ifTrue (conditionIH.mpr condition) (thenIH.mpr branch)
        | ifFalse condition branch => exact .ifFalse (conditionIH.mpr condition) (elseIH.mpr branch)

end Solcore.Frontend
