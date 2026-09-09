import Solcore.Frontend.LocalReference
import Solcore.Resolved.Eval
import Solcore.Resolved.FreshIdentity

/-! Shared raw body rules depend only on the supplied raw child relation;
cost rules depend only on the supplied cost relation. Neither checks syntax. -/

set_option autoImplicit false

namespace Solcore.Frontend

inductive ComputationReturnTreeEvaluates
    (ChildEval : LocalNameTable → Resolved.Environment → Core.Store → Syntax.Expr → Core.Value → Core.Store → Prop)
    (owner : Resolved.DeclarationId) :
    LocalNameTable → Resolved.Environment → Core.Store → Syntax.Block → Core.Value → Core.Store → Prop where
  | bare {table : LocalNameTable} {environment : Resolved.Environment}
      {blockSpan returnSpan : Syntax.SourceSpan} {store : Core.Store} :
      ComputationReturnTreeEvaluates ChildEval owner table environment store
        ⟨blockSpan, [⟨returnSpan, .returnStmt none⟩]⟩ .unit store
  | expression {table : LocalNameTable} {environment : Resolved.Environment}
      {blockSpan returnSpan : Syntax.SourceSpan} {source : Syntax.Expr}
      {initialStore finalStore : Core.Store} {value : Core.Value}
      (child : ChildEval table environment initialStore source value finalStore) :
      ComputationReturnTreeEvaluates ChildEval owner table environment initialStore
        ⟨blockSpan, [⟨returnSpan, .returnStmt (some source)⟩]⟩ value finalStore
  | block {table : LocalNameTable} {environment : Resolved.Environment}
      {outerSpan innerSpan : Syntax.SourceSpan} {statements : List Syntax.Statement}
      {initialStore finalStore : Core.Store} {value : Core.Value}
      (child : ComputationReturnTreeEvaluates ChildEval owner table environment initialStore
        ⟨innerSpan, statements⟩ value finalStore) :
      ComputationReturnTreeEvaluates ChildEval owner table environment initialStore
        ⟨outerSpan, [⟨innerSpan, .block statements⟩]⟩ value finalStore
  | binding {table : LocalNameTable} {environment : Resolved.Environment}
      {blockSpan letSpan : Syntax.SourceSpan} {name : Syntax.Identifier}
      {annotation : Syntax.TypeExpr} {initializer : Syntax.Expr} {rest : List Syntax.Statement}
      {initialStore middleStore finalStore : Core.Store} {boundValue value : Core.Value}
      (initializerEvaluation : ChildEval table environment initialStore initializer boundValue middleStore)
      (tailEvaluation : ComputationReturnTreeEvaluates ChildEval owner
        ((name.value, Resolved.freshLocalId owner (table.map Prod.snd)) :: table)
        ((Resolved.freshLocalId owner (table.map Prod.snd), boundValue) :: environment)
        middleStore ⟨blockSpan, rest⟩ value finalStore) :
      ComputationReturnTreeEvaluates ChildEval owner table environment initialStore
        ⟨blockSpan, ⟨letSpan, .letDecl name (some annotation) (some initializer)⟩ :: rest⟩ value finalStore
  | inferred {table : LocalNameTable} {environment : Resolved.Environment}
      {blockSpan letSpan : Syntax.SourceSpan} {name : Syntax.Identifier}
      {initializer : Syntax.Expr} {rest : List Syntax.Statement}
      {initialStore middleStore finalStore : Core.Store} {boundValue value : Core.Value}
      (initializerEvaluation : ChildEval table environment initialStore initializer boundValue middleStore)
      (tailEvaluation : ComputationReturnTreeEvaluates ChildEval owner
        ((name.value, Resolved.freshLocalId owner (table.map Prod.snd)) :: table)
        ((Resolved.freshLocalId owner (table.map Prod.snd), boundValue) :: environment)
        middleStore ⟨blockSpan, rest⟩ value finalStore) :
      ComputationReturnTreeEvaluates ChildEval owner table environment initialStore
        ⟨blockSpan, ⟨letSpan, .letDecl name none (some initializer)⟩ :: rest⟩ value finalStore
  | discard {table : LocalNameTable} {environment : Resolved.Environment}
      {blockSpan statementSpan : Syntax.SourceSpan} {expression : Syntax.Expr} {rest : List Syntax.Statement}
      {initialStore middleStore finalStore : Core.Store} {discardedValue value : Core.Value}
      (expressionEvaluation : ChildEval table environment initialStore expression discardedValue middleStore)
      (tailEvaluation : ComputationReturnTreeEvaluates ChildEval owner table environment middleStore
        ⟨blockSpan, rest⟩ value finalStore) :
      ComputationReturnTreeEvaluates ChildEval owner table environment initialStore
        ⟨blockSpan, ⟨statementSpan, .expression expression true⟩ :: rest⟩ value finalStore
  | ifTrue {table : LocalNameTable} {environment : Resolved.Environment}
      {blockSpan ifSpan : Syntax.SourceSpan} {condition : Syntax.Expr}
      {thenBody elseBody : Syntax.Block} {initialStore middleStore finalStore : Core.Store} {value : Core.Value}
      (conditionEvaluation : ChildEval table environment initialStore condition (.bool true) middleStore)
      (branchEvaluation : ComputationReturnTreeEvaluates ChildEval owner table environment middleStore thenBody value finalStore) :
      ComputationReturnTreeEvaluates ChildEval owner table environment initialStore
        ⟨blockSpan, [⟨ifSpan, .ifThen condition thenBody (some elseBody)⟩]⟩ value finalStore
  | ifFalse {table : LocalNameTable} {environment : Resolved.Environment}
      {blockSpan ifSpan : Syntax.SourceSpan} {condition : Syntax.Expr}
      {thenBody elseBody : Syntax.Block} {initialStore middleStore finalStore : Core.Store} {value : Core.Value}
      (conditionEvaluation : ChildEval table environment initialStore condition (.bool false) middleStore)
      (branchEvaluation : ComputationReturnTreeEvaluates ChildEval owner table environment middleStore elseBody value finalStore) :
      ComputationReturnTreeEvaluates ChildEval owner table environment initialStore
        ⟨blockSpan, [⟨ifSpan, .ifThen condition thenBody (some elseBody)⟩]⟩ value finalStore

/-- Selected lets, discards and conditionals each add two existing Core transitions.
An unused initializer or discarded expression still contributes its complete cost.
Bare return costs one; expression return and terminal blocks keep child costs.
These paths do not impose store independence on an actual called body. -/
inductive ComputationReturnTreeEvaluatesWithCost
    (ChildCost : LocalNameTable → Resolved.Environment → Core.Store → Syntax.Expr → Core.Value → Core.Store → Nat → Prop)
    (owner : Resolved.DeclarationId) :
    LocalNameTable → Resolved.Environment → Core.Store → Syntax.Block → Core.Value → Core.Store → Nat → Prop where
  | bare {table : LocalNameTable} {environment : Resolved.Environment}
      {blockSpan returnSpan : Syntax.SourceSpan} {store : Core.Store} :
      ComputationReturnTreeEvaluatesWithCost ChildCost owner table environment store
        ⟨blockSpan, [⟨returnSpan, .returnStmt none⟩]⟩ .unit store 1
  | expression {table : LocalNameTable} {environment : Resolved.Environment}
      {blockSpan returnSpan : Syntax.SourceSpan} {source : Syntax.Expr}
      {initialStore finalStore : Core.Store} {value : Core.Value} {cost : Nat}
      (child : ChildCost table environment initialStore source value finalStore cost) :
      ComputationReturnTreeEvaluatesWithCost ChildCost owner table environment initialStore
        ⟨blockSpan, [⟨returnSpan, .returnStmt (some source)⟩]⟩ value finalStore cost
  | block {table : LocalNameTable} {environment : Resolved.Environment}
      {outerSpan innerSpan : Syntax.SourceSpan} {statements : List Syntax.Statement}
      {initialStore finalStore : Core.Store} {value : Core.Value} {cost : Nat}
      (child : ComputationReturnTreeEvaluatesWithCost ChildCost owner table environment initialStore
        ⟨innerSpan, statements⟩ value finalStore cost) :
      ComputationReturnTreeEvaluatesWithCost ChildCost owner table environment initialStore
        ⟨outerSpan, [⟨innerSpan, .block statements⟩]⟩ value finalStore cost
  | binding {table : LocalNameTable} {environment : Resolved.Environment}
      {blockSpan letSpan : Syntax.SourceSpan} {name : Syntax.Identifier}
      {annotation : Syntax.TypeExpr} {initializer : Syntax.Expr} {rest : List Syntax.Statement}
      {initialStore middleStore finalStore : Core.Store} {boundValue value : Core.Value}
      {initializerCost tailCost : Nat}
      (initializerEvaluation : ChildCost table environment
        initialStore initializer boundValue middleStore initializerCost)
      (tailEvaluation : ComputationReturnTreeEvaluatesWithCost ChildCost owner
        ((name.value, Resolved.freshLocalId owner (table.map Prod.snd)) :: table)
        ((Resolved.freshLocalId owner (table.map Prod.snd), boundValue) :: environment)
        middleStore ⟨blockSpan, rest⟩ value finalStore tailCost) :
      ComputationReturnTreeEvaluatesWithCost ChildCost owner table environment initialStore
        ⟨blockSpan, ⟨letSpan, .letDecl name (some annotation) (some initializer)⟩ :: rest⟩
        value finalStore (initializerCost + tailCost + 2)
  | inferred {table : LocalNameTable} {environment : Resolved.Environment}
      {blockSpan letSpan : Syntax.SourceSpan} {name : Syntax.Identifier}
      {initializer : Syntax.Expr} {rest : List Syntax.Statement}
      {initialStore middleStore finalStore : Core.Store} {boundValue value : Core.Value}
      {initializerCost tailCost : Nat}
      (initializerEvaluation : ChildCost table environment
        initialStore initializer boundValue middleStore initializerCost)
      (tailEvaluation : ComputationReturnTreeEvaluatesWithCost ChildCost owner
        ((name.value, Resolved.freshLocalId owner (table.map Prod.snd)) :: table)
        ((Resolved.freshLocalId owner (table.map Prod.snd), boundValue) :: environment)
        middleStore ⟨blockSpan, rest⟩ value finalStore tailCost) :
      ComputationReturnTreeEvaluatesWithCost ChildCost owner table environment initialStore
        ⟨blockSpan, ⟨letSpan, .letDecl name none (some initializer)⟩ :: rest⟩
        value finalStore (initializerCost + tailCost + 2)
  | discard {table : LocalNameTable} {environment : Resolved.Environment}
      {blockSpan statementSpan : Syntax.SourceSpan} {expression : Syntax.Expr} {rest : List Syntax.Statement}
      {initialStore middleStore finalStore : Core.Store} {discardedValue value : Core.Value}
      {expressionCost tailCost : Nat}
      (expressionEvaluation : ChildCost table environment
        initialStore expression discardedValue middleStore expressionCost)
      (tailEvaluation : ComputationReturnTreeEvaluatesWithCost ChildCost owner table environment
        middleStore ⟨blockSpan, rest⟩ value finalStore tailCost) :
      ComputationReturnTreeEvaluatesWithCost ChildCost owner table environment initialStore
        ⟨blockSpan, ⟨statementSpan, .expression expression true⟩ :: rest⟩
        value finalStore (expressionCost + tailCost + 2)
  | ifTrue {table : LocalNameTable} {environment : Resolved.Environment}
      {blockSpan ifSpan : Syntax.SourceSpan} {condition : Syntax.Expr}
      {thenBody elseBody : Syntax.Block} {initialStore middleStore finalStore : Core.Store}
      {value : Core.Value} {conditionCost branchCost : Nat}
      (conditionEvaluation : ChildCost table environment
        initialStore condition (.bool true) middleStore conditionCost)
      (branchEvaluation : ComputationReturnTreeEvaluatesWithCost ChildCost owner table environment
        middleStore thenBody value finalStore branchCost) :
      ComputationReturnTreeEvaluatesWithCost ChildCost owner table environment initialStore
        ⟨blockSpan, [⟨ifSpan, .ifThen condition thenBody (some elseBody)⟩]⟩
        value finalStore (conditionCost + branchCost + 2)
  | ifFalse {table : LocalNameTable} {environment : Resolved.Environment}
      {blockSpan ifSpan : Syntax.SourceSpan} {condition : Syntax.Expr}
      {thenBody elseBody : Syntax.Block} {initialStore middleStore finalStore : Core.Store}
      {value : Core.Value} {conditionCost branchCost : Nat}
      (conditionEvaluation : ChildCost table environment
        initialStore condition (.bool false) middleStore conditionCost)
      (branchEvaluation : ComputationReturnTreeEvaluatesWithCost ChildCost owner table environment
        middleStore elseBody value finalStore branchCost) :
      ComputationReturnTreeEvaluatesWithCost ChildCost owner table environment initialStore
        ⟨blockSpan, [⟨ifSpan, .ifThen condition thenBody (some elseBody)⟩]⟩
        value finalStore (conditionCost + branchCost + 2)

end Solcore.Frontend
