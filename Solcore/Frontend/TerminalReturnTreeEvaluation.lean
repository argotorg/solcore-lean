import Solcore.Frontend.ReturnBodyProperties

/-! Independent recursive selected-path semantics. Unselected subtrees need
neither evaluation nor whole acceptance; both stores remain explicit. -/

set_option autoImplicit false

namespace Solcore.Frontend

inductive TerminalReturnTreeEvaluates
    (table : LocalNameTable) (environment : Resolved.Environment) :
    Core.Store → Syntax.Block → Core.Value → Core.Store → Prop where
  | single {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value}
      (child : ReturnBodyEvaluates table environment initialStore body value finalStore) :
      TerminalReturnTreeEvaluates table environment initialStore body value finalStore
  | ifTrue {blockSpan statementSpan : Syntax.SourceSpan} {condition : Syntax.Expr}
      {thenBody elseBody : Syntax.Block} {initialStore middleStore finalStore : Core.Store}
      {value : Core.Value}
      (conditionEvaluation : LocalExpressionEvaluates table environment
        initialStore condition (.bool true) middleStore)
      (branchEvaluation : TerminalReturnTreeEvaluates table environment middleStore thenBody value finalStore) :
      TerminalReturnTreeEvaluates table environment initialStore
        ⟨blockSpan, [⟨statementSpan, .ifThen condition thenBody (some elseBody)⟩]⟩ value finalStore
  | ifFalse {blockSpan statementSpan : Syntax.SourceSpan} {condition : Syntax.Expr}
      {thenBody elseBody : Syntax.Block} {initialStore middleStore finalStore : Core.Store}
      {value : Core.Value}
      (conditionEvaluation : LocalExpressionEvaluates table environment
        initialStore condition (.bool false) middleStore)
      (branchEvaluation : TerminalReturnTreeEvaluates table environment middleStore elseBody value finalStore) :
      TerminalReturnTreeEvaluates table environment initialStore
        ⟨blockSpan, [⟨statementSpan, .ifThen condition thenBody (some elseBody)⟩]⟩ value finalStore

/-- Only selected conditions and leaves contribute cost. Each conditional
adds the two existing Core transitions; the leaf wrapper adds nothing. -/
inductive TerminalReturnTreeEvaluatesWithCost
    (table : LocalNameTable) (environment : Resolved.Environment) :
    Core.Store → Syntax.Block → Core.Value → Core.Store → Nat → Prop where
  | single {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
      (child : ReturnBodyEvaluatesWithCost table environment initialStore body value finalStore cost) :
      TerminalReturnTreeEvaluatesWithCost table environment initialStore body value finalStore cost
  | ifTrue {blockSpan statementSpan : Syntax.SourceSpan} {condition : Syntax.Expr}
      {thenBody elseBody : Syntax.Block} {initialStore middleStore finalStore : Core.Store}
      {value : Core.Value} {conditionCost branchCost : Nat}
      (conditionEvaluation : LocalExpressionEvaluatesWithCost table environment
        initialStore condition (.bool true) middleStore conditionCost)
      (branchEvaluation : TerminalReturnTreeEvaluatesWithCost table environment
        middleStore thenBody value finalStore branchCost) :
      TerminalReturnTreeEvaluatesWithCost table environment initialStore
        ⟨blockSpan, [⟨statementSpan, .ifThen condition thenBody (some elseBody)⟩]⟩
        value finalStore (conditionCost + branchCost + 2)
  | ifFalse {blockSpan statementSpan : Syntax.SourceSpan} {condition : Syntax.Expr}
      {thenBody elseBody : Syntax.Block} {initialStore middleStore finalStore : Core.Store}
      {value : Core.Value} {conditionCost branchCost : Nat}
      (conditionEvaluation : LocalExpressionEvaluatesWithCost table environment
        initialStore condition (.bool false) middleStore conditionCost)
      (branchEvaluation : TerminalReturnTreeEvaluatesWithCost table environment
        middleStore elseBody value finalStore branchCost) :
      TerminalReturnTreeEvaluatesWithCost table environment initialStore
        ⟨blockSpan, [⟨statementSpan, .ifThen condition thenBody (some elseBody)⟩]⟩
        value finalStore (conditionCost + branchCost + 2)

end Solcore.Frontend
