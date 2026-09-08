import Solcore.Frontend.LocalExpressionCost
import Solcore.Frontend.LocalExpressionCostStepComposition

/-! Independent source costs are exact Core path lengths. Whole structural
resolution and runtime identity-order lowering are explicit; no typing or
runtime store assumptions are needed once a cost derivation is supplied. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem LocalExpressionEvaluatesWithCost.toStepsWithContinuation
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {source : Syntax.Expr}
    {value : Core.Value} {cost : Nat}
    (evaluation : LocalExpressionEvaluatesWithCost table environment
      initialStore source value finalStore cost)
    {resolved : Resolved.Expr} {core : Core.Expr}
    (resolution : ResolvesLocalExpression table source resolved)
    (lowered : Resolved.Lowers (Resolved.LocalScope.ids environment) resolved core)
    (continuation : List Core.Frame) :
    Core.Steps cost
      ⟨.eval core (Resolved.LocalScope.values environment), continuation, initialStore⟩
      ⟨.ret value, continuation, finalStore⟩ := by
  induction evaluation generalizing resolved core continuation with
  | identifier named found =>
      cases resolution with
      | identifier otherNamed =>
          cases named.id_unique otherNamed
          cases lowered with
          | var indexed =>
              exact .cons (.var ((Resolved.LocalScope.lookup_iff_getElem? indexed).mp found)) .refl
  | wordLiteral meaning =>
      cases resolution with
      | wordLiteral otherMeaning =>
          cases meaning.value_unique otherMeaning
          cases lowered
          exact .cons .word .refl
  | group _ ih =>
      cases resolution with
      | group child => exact ih child lowered continuation
  | logicalNot _ ih =>
      cases resolution with
      | logicalNot child =>
          cases lowered with
          | unary lowerChild => exact CostStepComposition.unary (ih child lowerChild _) rfl
  | bitNot _ ih =>
      cases resolution with
      | bitNot child =>
          cases lowered with
          | unary lowerChild => exact CostStepComposition.unary (ih child lowerChild _) rfl
  | add _ _ leftIH rightIH =>
      cases resolution with
      | add leftChild rightChild =>
          cases lowered with
          | binary lowerLeft lowerRight =>
              exact CostStepComposition.binary
                (leftIH leftChild lowerLeft _) (rightIH rightChild lowerRight _) rfl
  | bitAnd _ _ leftIH rightIH =>
      cases resolution with
      | bitAnd leftChild rightChild =>
          cases lowered with
          | binary lowerLeft lowerRight =>
              exact CostStepComposition.binary
                (leftIH leftChild lowerLeft _) (rightIH rightChild lowerRight _) rfl
  | bitOr _ _ leftIH rightIH =>
      cases resolution with
      | bitOr leftChild rightChild =>
          cases lowered with
          | binary lowerLeft lowerRight =>
              exact CostStepComposition.binary
                (leftIH leftChild lowerLeft _) (rightIH rightChild lowerRight _) rfl
  | bitXor _ _ leftIH rightIH =>
      cases resolution with
      | bitXor leftChild rightChild =>
          cases lowered with
          | binary lowerLeft lowerRight =>
              exact CostStepComposition.binary
                (leftIH leftChild lowerLeft _) (rightIH rightChild lowerRight _) rfl
  | andTrue _ _ leftIH rightIH =>
      cases resolution with
      | logicalAnd leftChild rightChild =>
          cases lowered with
          | ifE lowerLeft lowerRight _ =>
              exact CostStepComposition.ifTrue
                (leftIH leftChild lowerLeft _) (rightIH rightChild lowerRight _)
  | andFalse _ leftIH =>
      cases resolution with
      | logicalAnd leftChild _ =>
          cases lowered with
          | ifE lowerLeft _ lowerConstant =>
              cases lowerConstant
              simpa only [Nat.add_assoc] using CostStepComposition.ifFalse
                (leftIH leftChild lowerLeft _) (.cons .bool .refl)
  | orTrue _ leftIH =>
      cases resolution with
      | logicalOr leftChild _ =>
          cases lowered with
          | ifE lowerLeft lowerConstant _ =>
              cases lowerConstant
              simpa only [Nat.add_assoc] using CostStepComposition.ifTrue
                (leftIH leftChild lowerLeft _) (.cons .bool .refl)
  | orFalse _ _ leftIH rightIH =>
      cases resolution with
      | logicalOr leftChild rightChild =>
          cases lowered with
          | ifE lowerLeft _ lowerRight =>
              exact CostStepComposition.ifFalse
                (leftIH leftChild lowerLeft _) (rightIH rightChild lowerRight _)
  | ifTrue _ _ conditionIH branchIH =>
      cases resolution with
      | conditional conditionChild branchChild _ =>
          cases lowered with
          | ifE lowerCondition lowerBranch _ =>
              exact CostStepComposition.ifTrue
                (conditionIH conditionChild lowerCondition _) (branchIH branchChild lowerBranch _)
  | ifFalse _ _ conditionIH branchIH =>
      cases resolution with
      | conditional conditionChild _ branchChild =>
          cases lowered with
          | ifE lowerCondition _ lowerBranch =>
              exact CostStepComposition.ifFalse
                (conditionIH conditionChild lowerCondition _) (branchIH branchChild lowerBranch _)

theorem LocalExpressionEvaluatesWithCost.toSteps
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {source : Syntax.Expr}
    {value : Core.Value} {cost : Nat}
    (evaluation : LocalExpressionEvaluatesWithCost table environment
      initialStore source value finalStore cost)
    {resolved : Resolved.Expr} {core : Core.Expr}
    (resolution : ResolvesLocalExpression table source resolved)
    (lowered : Resolved.Lowers (Resolved.LocalScope.ids environment) resolved core) :
    Core.Steps cost
      (Core.State.initial core (Resolved.LocalScope.values environment) initialStore)
      (Core.State.final value finalStore) :=
  evaluation.toStepsWithContinuation resolution lowered []

end Solcore.Frontend
