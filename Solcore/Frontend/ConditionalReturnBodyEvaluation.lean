import Solcore.Frontend.ReturnBodyProperties

/-! Independent selected-arm semantics for a terminal conditional statement.
An unselected arm need not evaluate; whole checking is a separate judgment. -/

set_option autoImplicit false

namespace Solcore.Frontend

inductive ConditionalReturnBodyEvaluates
    (table : LocalNameTable) (environment : Resolved.Environment) :
    Core.Store → Syntax.Block → Core.Value → Core.Store → Prop where
  | ifTrue {blockSpan statementSpan : Syntax.SourceSpan} {condition : Syntax.Expr}
      {thenBody elseBody : Syntax.Block} {initialStore middleStore finalStore : Core.Store}
      {value : Core.Value}
      (conditionEvaluation : LocalExpressionEvaluates table environment
        initialStore condition (.bool true) middleStore)
      (branchEvaluation : ReturnBodyEvaluates table environment middleStore thenBody value finalStore) :
      ConditionalReturnBodyEvaluates table environment initialStore
        ⟨blockSpan, [⟨statementSpan, .ifThen condition thenBody (some elseBody)⟩]⟩ value finalStore
  | ifFalse {blockSpan statementSpan : Syntax.SourceSpan} {condition : Syntax.Expr}
      {thenBody elseBody : Syntax.Block} {initialStore middleStore finalStore : Core.Store}
      {value : Core.Value}
      (conditionEvaluation : LocalExpressionEvaluates table environment
        initialStore condition (.bool false) middleStore)
      (branchEvaluation : ReturnBodyEvaluates table environment middleStore elseBody value finalStore) :
      ConditionalReturnBodyEvaluates table environment initialStore
        ⟨blockSpan, [⟨statementSpan, .ifThen condition thenBody (some elseBody)⟩]⟩ value finalStore

/-- Costs include condition evaluation, the selected arm and the two Core
conditional transitions. Bare return arms retain their one Unit transition. -/
inductive ConditionalReturnBodyEvaluatesWithCost
    (table : LocalNameTable) (environment : Resolved.Environment) :
    Core.Store → Syntax.Block → Core.Value → Core.Store → Nat → Prop where
  | ifTrue {blockSpan statementSpan : Syntax.SourceSpan} {condition : Syntax.Expr}
      {thenBody elseBody : Syntax.Block} {initialStore middleStore finalStore : Core.Store}
      {value : Core.Value} {conditionCost branchCost : Nat}
      (conditionEvaluation : LocalExpressionEvaluatesWithCost table environment
        initialStore condition (.bool true) middleStore conditionCost)
      (branchEvaluation : ReturnBodyEvaluatesWithCost table environment
        middleStore thenBody value finalStore branchCost) :
      ConditionalReturnBodyEvaluatesWithCost table environment initialStore
        ⟨blockSpan, [⟨statementSpan, .ifThen condition thenBody (some elseBody)⟩]⟩
        value finalStore (conditionCost + branchCost + 2)
  | ifFalse {blockSpan statementSpan : Syntax.SourceSpan} {condition : Syntax.Expr}
      {thenBody elseBody : Syntax.Block} {initialStore middleStore finalStore : Core.Store}
      {value : Core.Value} {conditionCost branchCost : Nat}
      (conditionEvaluation : LocalExpressionEvaluatesWithCost table environment
        initialStore condition (.bool false) middleStore conditionCost)
      (branchEvaluation : ReturnBodyEvaluatesWithCost table environment
        middleStore elseBody value finalStore branchCost) :
      ConditionalReturnBodyEvaluatesWithCost table environment initialStore
        ⟨blockSpan, [⟨statementSpan, .ifThen condition thenBody (some elseBody)⟩]⟩
        value finalStore (conditionCost + branchCost + 2)

end Solcore.Frontend
