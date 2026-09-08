import Solcore.Frontend.LocalExpressionCostProperties
import Solcore.Frontend.LocalExpressionRenamingSemantics
import Solcore.Frontend.LocalInputsExtensionSemantics

/-! Structural preservation of independent source costs under identity
relabeling and unused-name insertion. Erased evaluation is used only at
identifier leaves to recover existing lookup laws, not to equate costs. -/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Simultaneous injective ID relabeling preserves raw value, both stores, and
cost. Whole resolution and typing are not required, even for skipped syntax. -/
theorem localExpressionEvaluatesWithCost_mapIds_iff
    (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping)
    {table : LocalNameTable} {environment : Resolved.Environment} {source : Syntax.Expr}
    {initialStore finalStore : Core.Store} {value : Core.Value} {cost : Nat} :
    LocalExpressionEvaluatesWithCost (LocalNameTable.mapIds mapping table)
        (Resolved.LocalScope.mapIds mapping environment) initialStore source value finalStore cost ↔
      LocalExpressionEvaluatesWithCost table environment initialStore source value finalStore cost := by
  constructor
  · intro evaluation
    induction evaluation with
    | @identifier store span name id value named found =>
        have ordinary := (localExpressionEvaluates_mapIds_iff mapping injective).mp
          (LocalExpressionEvaluatesWithCost.identifier (store := store) (span := span) named found).erase
        cases ordinary with
        | identifier oldNamed oldFound => exact .identifier oldNamed oldFound
    | wordLiteral meaning => exact .wordLiteral meaning
    | group _ ih => exact .group ih
    | logicalNot _ ih => exact .logicalNot ih
    | bitNot _ ih => exact .bitNot ih
    | add _ _ leftIH rightIH => exact .add leftIH rightIH
    | subtract _ _ leftIH rightIH => exact .subtract leftIH rightIH
    | multiply _ _ leftIH rightIH => exact .multiply leftIH rightIH
    | greater _ _ leftIH rightIH => exact .greater leftIH rightIH
    | bitAnd _ _ leftIH rightIH => exact .bitAnd leftIH rightIH
    | bitOr _ _ leftIH rightIH => exact .bitOr leftIH rightIH
    | bitXor _ _ leftIH rightIH => exact .bitXor leftIH rightIH
    | andTrue _ _ leftIH rightIH => exact .andTrue leftIH rightIH
    | andFalse _ ih => exact .andFalse ih
    | orTrue _ ih => exact .orTrue ih
    | orFalse _ _ leftIH rightIH => exact .orFalse leftIH rightIH
    | ifTrue _ _ conditionIH branchIH => exact .ifTrue conditionIH branchIH
    | ifFalse _ _ conditionIH branchIH => exact .ifFalse conditionIH branchIH
  · intro evaluation
    induction evaluation with
    | @identifier store span name id value named found =>
        have ordinary := (localExpressionEvaluates_mapIds_iff mapping injective).mpr
          (LocalExpressionEvaluatesWithCost.identifier (store := store) (span := span) named found).erase
        cases ordinary with
        | identifier newNamed newFound => exact .identifier newNamed newFound
    | wordLiteral meaning => exact .wordLiteral meaning
    | group _ ih => exact .group ih
    | logicalNot _ ih => exact .logicalNot ih
    | bitNot _ ih => exact .bitNot ih
    | add _ _ leftIH rightIH => exact .add leftIH rightIH
    | subtract _ _ leftIH rightIH => exact .subtract leftIH rightIH
    | multiply _ _ leftIH rightIH => exact .multiply leftIH rightIH
    | greater _ _ leftIH rightIH => exact .greater leftIH rightIH
    | bitAnd _ _ leftIH rightIH => exact .bitAnd leftIH rightIH
    | bitOr _ _ leftIH rightIH => exact .bitOr leftIH rightIH
    | bitXor _ _ leftIH rightIH => exact .bitXor leftIH rightIH
    | andTrue _ _ leftIH rightIH => exact .andTrue leftIH rightIH
    | andFalse _ ih => exact .andFalse ih
    | orTrue _ ih => exact .orTrue ih
    | orFalse _ _ leftIH rightIH => exact .orFalse leftIH rightIH
    | ifTrue _ _ conditionIH branchIH => exact .ifTrue conditionIH branchIH
    | ifFalse _ _ conditionIH branchIH => exact .ifFalse conditionIH branchIH

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
  | group _ ih =>
      constructor
      · intro evaluation
        cases evaluation with
        | group child => exact .group (ih.mp child)
      · intro evaluation
        cases evaluation with
        | group child => exact .group (ih.mpr child)
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
  | greater _ _ leftIH rightIH =>
      constructor
      · intro evaluation
        cases evaluation with
        | greater left right => exact .greater (leftIH.mp left) (rightIH.mp right)
      · intro evaluation
        cases evaluation with
        | greater left right => exact .greater (leftIH.mpr left) (rightIH.mpr right)
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
