import Solcore.Frontend.LocalComputationEvaluation
import Solcore.Resolved.FreshIdentity

/-! Independent mixed-body paths thread actual stores through strict children.
Named initializers use the old scope before allocating from the name table;
discards retain the same source scope and selected guards retain their effects.
No checking, annotation meaning, unused-name or runtime typing is required. -/

set_option autoImplicit false

namespace Solcore.Frontend

inductive LocalComputationReturnTreeEvaluates (owner : Resolved.DeclarationId) :
    LocalNameTable → Resolved.Environment → Core.Store → Syntax.Block → Core.Value → Core.Store → Prop where
  | bare {table : LocalNameTable} {environment : Resolved.Environment}
      {blockSpan returnSpan : Syntax.SourceSpan} {store : Core.Store} :
      LocalComputationReturnTreeEvaluates owner table environment store
        ⟨blockSpan, [⟨returnSpan, .returnStmt none⟩]⟩ .unit store
  | expression {table : LocalNameTable} {environment : Resolved.Environment}
      {blockSpan returnSpan : Syntax.SourceSpan} {source : Syntax.Expr}
      {initialStore finalStore : Core.Store} {value : Core.Value}
      (child : LocalComputationEvaluates table environment initialStore source value finalStore) :
      LocalComputationReturnTreeEvaluates owner table environment initialStore
        ⟨blockSpan, [⟨returnSpan, .returnStmt (some source)⟩]⟩ value finalStore
  | block {table : LocalNameTable} {environment : Resolved.Environment}
      {outerSpan innerSpan : Syntax.SourceSpan} {statements : List Syntax.Statement}
      {initialStore finalStore : Core.Store} {value : Core.Value}
      (child : LocalComputationReturnTreeEvaluates owner table environment initialStore
        ⟨innerSpan, statements⟩ value finalStore) :
      LocalComputationReturnTreeEvaluates owner table environment initialStore
        ⟨outerSpan, [⟨innerSpan, .block statements⟩]⟩ value finalStore
  | binding {table : LocalNameTable} {environment : Resolved.Environment}
      {blockSpan letSpan : Syntax.SourceSpan} {name : Syntax.Identifier}
      {annotation : Syntax.TypeExpr} {initializer : Syntax.Expr} {rest : List Syntax.Statement}
      {initialStore middleStore finalStore : Core.Store} {boundValue value : Core.Value}
      (initializerEvaluation : LocalComputationEvaluates table environment initialStore initializer boundValue middleStore)
      (tailEvaluation : LocalComputationReturnTreeEvaluates owner
        ((name.value, Resolved.freshLocalId owner (table.map Prod.snd)) :: table)
        ((Resolved.freshLocalId owner (table.map Prod.snd), boundValue) :: environment)
        middleStore ⟨blockSpan, rest⟩ value finalStore) :
      LocalComputationReturnTreeEvaluates owner table environment initialStore
        ⟨blockSpan, ⟨letSpan, .letDecl name (some annotation) (some initializer)⟩ :: rest⟩ value finalStore
  | inferred {table : LocalNameTable} {environment : Resolved.Environment}
      {blockSpan letSpan : Syntax.SourceSpan} {name : Syntax.Identifier}
      {initializer : Syntax.Expr} {rest : List Syntax.Statement}
      {initialStore middleStore finalStore : Core.Store} {boundValue value : Core.Value}
      (initializerEvaluation : LocalComputationEvaluates table environment initialStore initializer boundValue middleStore)
      (tailEvaluation : LocalComputationReturnTreeEvaluates owner
        ((name.value, Resolved.freshLocalId owner (table.map Prod.snd)) :: table)
        ((Resolved.freshLocalId owner (table.map Prod.snd), boundValue) :: environment)
        middleStore ⟨blockSpan, rest⟩ value finalStore) :
      LocalComputationReturnTreeEvaluates owner table environment initialStore
        ⟨blockSpan, ⟨letSpan, .letDecl name none (some initializer)⟩ :: rest⟩ value finalStore
  | discard {table : LocalNameTable} {environment : Resolved.Environment}
      {blockSpan statementSpan : Syntax.SourceSpan} {expression : Syntax.Expr} {rest : List Syntax.Statement}
      {initialStore middleStore finalStore : Core.Store} {discardedValue value : Core.Value}
      (expressionEvaluation : LocalComputationEvaluates table environment initialStore expression discardedValue middleStore)
      (tailEvaluation : LocalComputationReturnTreeEvaluates owner table environment middleStore
        ⟨blockSpan, rest⟩ value finalStore) :
      LocalComputationReturnTreeEvaluates owner table environment initialStore
        ⟨blockSpan, ⟨statementSpan, .expression expression true⟩ :: rest⟩ value finalStore
  | ifTrue {table : LocalNameTable} {environment : Resolved.Environment}
      {blockSpan ifSpan : Syntax.SourceSpan} {condition : Syntax.Expr}
      {thenBody elseBody : Syntax.Block} {initialStore middleStore finalStore : Core.Store} {value : Core.Value}
      (conditionEvaluation : LocalComputationEvaluates table environment initialStore condition (.bool true) middleStore)
      (branchEvaluation : LocalComputationReturnTreeEvaluates owner table environment middleStore thenBody value finalStore) :
      LocalComputationReturnTreeEvaluates owner table environment initialStore
        ⟨blockSpan, [⟨ifSpan, .ifThen condition thenBody (some elseBody)⟩]⟩ value finalStore
  | ifFalse {table : LocalNameTable} {environment : Resolved.Environment}
      {blockSpan ifSpan : Syntax.SourceSpan} {condition : Syntax.Expr}
      {thenBody elseBody : Syntax.Block} {initialStore middleStore finalStore : Core.Store} {value : Core.Value}
      (conditionEvaluation : LocalComputationEvaluates table environment initialStore condition (.bool false) middleStore)
      (branchEvaluation : LocalComputationReturnTreeEvaluates owner table environment middleStore elseBody value finalStore) :
      LocalComputationReturnTreeEvaluates owner table environment initialStore
        ⟨blockSpan, [⟨ifSpan, .ifThen condition thenBody (some elseBody)⟩]⟩ value finalStore

/-- Selected lets, discards and conditionals each add two existing Core transitions.
An unused initializer or discarded expression still contributes its complete cost.
Bare return costs one; expression return and terminal blocks keep child costs.
These paths do not impose store independence on an actual called body. -/
inductive LocalComputationReturnTreeEvaluatesWithCost (owner : Resolved.DeclarationId) :
    LocalNameTable → Resolved.Environment → Core.Store → Syntax.Block → Core.Value → Core.Store → Nat → Prop where
  | bare {table : LocalNameTable} {environment : Resolved.Environment}
      {blockSpan returnSpan : Syntax.SourceSpan} {store : Core.Store} :
      LocalComputationReturnTreeEvaluatesWithCost owner table environment store
        ⟨blockSpan, [⟨returnSpan, .returnStmt none⟩]⟩ .unit store 1
  | expression {table : LocalNameTable} {environment : Resolved.Environment}
      {blockSpan returnSpan : Syntax.SourceSpan} {source : Syntax.Expr}
      {initialStore finalStore : Core.Store} {value : Core.Value} {cost : Nat}
      (child : LocalComputationEvaluatesWithCost table environment initialStore source value finalStore cost) :
      LocalComputationReturnTreeEvaluatesWithCost owner table environment initialStore
        ⟨blockSpan, [⟨returnSpan, .returnStmt (some source)⟩]⟩ value finalStore cost
  | block {table : LocalNameTable} {environment : Resolved.Environment}
      {outerSpan innerSpan : Syntax.SourceSpan} {statements : List Syntax.Statement}
      {initialStore finalStore : Core.Store} {value : Core.Value} {cost : Nat}
      (child : LocalComputationReturnTreeEvaluatesWithCost owner table environment initialStore
        ⟨innerSpan, statements⟩ value finalStore cost) :
      LocalComputationReturnTreeEvaluatesWithCost owner table environment initialStore
        ⟨outerSpan, [⟨innerSpan, .block statements⟩]⟩ value finalStore cost
  | binding {table : LocalNameTable} {environment : Resolved.Environment}
      {blockSpan letSpan : Syntax.SourceSpan} {name : Syntax.Identifier}
      {annotation : Syntax.TypeExpr} {initializer : Syntax.Expr} {rest : List Syntax.Statement}
      {initialStore middleStore finalStore : Core.Store} {boundValue value : Core.Value}
      {initializerCost tailCost : Nat}
      (initializerEvaluation : LocalComputationEvaluatesWithCost table environment
        initialStore initializer boundValue middleStore initializerCost)
      (tailEvaluation : LocalComputationReturnTreeEvaluatesWithCost owner
        ((name.value, Resolved.freshLocalId owner (table.map Prod.snd)) :: table)
        ((Resolved.freshLocalId owner (table.map Prod.snd), boundValue) :: environment)
        middleStore ⟨blockSpan, rest⟩ value finalStore tailCost) :
      LocalComputationReturnTreeEvaluatesWithCost owner table environment initialStore
        ⟨blockSpan, ⟨letSpan, .letDecl name (some annotation) (some initializer)⟩ :: rest⟩
        value finalStore (initializerCost + tailCost + 2)
  | inferred {table : LocalNameTable} {environment : Resolved.Environment}
      {blockSpan letSpan : Syntax.SourceSpan} {name : Syntax.Identifier}
      {initializer : Syntax.Expr} {rest : List Syntax.Statement}
      {initialStore middleStore finalStore : Core.Store} {boundValue value : Core.Value}
      {initializerCost tailCost : Nat}
      (initializerEvaluation : LocalComputationEvaluatesWithCost table environment
        initialStore initializer boundValue middleStore initializerCost)
      (tailEvaluation : LocalComputationReturnTreeEvaluatesWithCost owner
        ((name.value, Resolved.freshLocalId owner (table.map Prod.snd)) :: table)
        ((Resolved.freshLocalId owner (table.map Prod.snd), boundValue) :: environment)
        middleStore ⟨blockSpan, rest⟩ value finalStore tailCost) :
      LocalComputationReturnTreeEvaluatesWithCost owner table environment initialStore
        ⟨blockSpan, ⟨letSpan, .letDecl name none (some initializer)⟩ :: rest⟩
        value finalStore (initializerCost + tailCost + 2)
  | discard {table : LocalNameTable} {environment : Resolved.Environment}
      {blockSpan statementSpan : Syntax.SourceSpan} {expression : Syntax.Expr} {rest : List Syntax.Statement}
      {initialStore middleStore finalStore : Core.Store} {discardedValue value : Core.Value}
      {expressionCost tailCost : Nat}
      (expressionEvaluation : LocalComputationEvaluatesWithCost table environment
        initialStore expression discardedValue middleStore expressionCost)
      (tailEvaluation : LocalComputationReturnTreeEvaluatesWithCost owner table environment
        middleStore ⟨blockSpan, rest⟩ value finalStore tailCost) :
      LocalComputationReturnTreeEvaluatesWithCost owner table environment initialStore
        ⟨blockSpan, ⟨statementSpan, .expression expression true⟩ :: rest⟩
        value finalStore (expressionCost + tailCost + 2)
  | ifTrue {table : LocalNameTable} {environment : Resolved.Environment}
      {blockSpan ifSpan : Syntax.SourceSpan} {condition : Syntax.Expr}
      {thenBody elseBody : Syntax.Block} {initialStore middleStore finalStore : Core.Store}
      {value : Core.Value} {conditionCost branchCost : Nat}
      (conditionEvaluation : LocalComputationEvaluatesWithCost table environment
        initialStore condition (.bool true) middleStore conditionCost)
      (branchEvaluation : LocalComputationReturnTreeEvaluatesWithCost owner table environment
        middleStore thenBody value finalStore branchCost) :
      LocalComputationReturnTreeEvaluatesWithCost owner table environment initialStore
        ⟨blockSpan, [⟨ifSpan, .ifThen condition thenBody (some elseBody)⟩]⟩
        value finalStore (conditionCost + branchCost + 2)
  | ifFalse {table : LocalNameTable} {environment : Resolved.Environment}
      {blockSpan ifSpan : Syntax.SourceSpan} {condition : Syntax.Expr}
      {thenBody elseBody : Syntax.Block} {initialStore middleStore finalStore : Core.Store}
      {value : Core.Value} {conditionCost branchCost : Nat}
      (conditionEvaluation : LocalComputationEvaluatesWithCost table environment
        initialStore condition (.bool false) middleStore conditionCost)
      (branchEvaluation : LocalComputationReturnTreeEvaluatesWithCost owner table environment
        middleStore elseBody value finalStore branchCost) :
      LocalComputationReturnTreeEvaluatesWithCost owner table environment initialStore
        ⟨blockSpan, [⟨ifSpan, .ifThen condition thenBody (some elseBody)⟩]⟩
        value finalStore (conditionCost + branchCost + 2)

end Solcore.Frontend
