import Solcore.Frontend.RuntimeWordMatch
import Solcore.Resolved.FreshIdentity

/-! Nine original raw body forms over mixed values with explicit-owner child
evaluation. Annotations and unselected branches are unchecked; no scope guard,
heap snapshot, closed evaluator, execution cost or failure classification is added. -/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Original successful body rules with actual mixed stores and ordered rows.
Initializers precede binding; branches use current stores without static guards. -/
inductive SourceComputationBodyEvaluates
    (ChildEval : Resolved.DeclarationId → List (String × Resolved.LocalId) →
      List (Resolved.LocalId × RuntimeValue) → List RuntimeValue → Syntax.Expr →
      RuntimeValue → List RuntimeValue → Prop)
    (owner : Resolved.DeclarationId) :
    List (String × Resolved.LocalId) → List (Resolved.LocalId × RuntimeValue) →
    List RuntimeValue → Syntax.Block → RuntimeValue → List RuntimeValue → Prop where
  | bare {table : List (String × Resolved.LocalId)} {environment : List (Resolved.LocalId × RuntimeValue)}
      {blockSpan returnSpan : Syntax.SourceSpan} {store : List RuntimeValue} :
      SourceComputationBodyEvaluates ChildEval owner table environment store
        ⟨blockSpan, [⟨returnSpan, .returnStmt none⟩]⟩ .unit store
  | expression {table : List (String × Resolved.LocalId)} {environment : List (Resolved.LocalId × RuntimeValue)}
      {blockSpan returnSpan : Syntax.SourceSpan} {source : Syntax.Expr}
      {initialStore finalStore : List RuntimeValue} {value : RuntimeValue}
      (child : ChildEval owner table environment initialStore source value finalStore) :
      SourceComputationBodyEvaluates ChildEval owner table environment initialStore
        ⟨blockSpan, [⟨returnSpan, .returnStmt (some source)⟩]⟩ value finalStore
  | block {table : List (String × Resolved.LocalId)} {environment : List (Resolved.LocalId × RuntimeValue)}
      {outerSpan innerSpan : Syntax.SourceSpan} {statements : List Syntax.Statement}
      {initialStore finalStore : List RuntimeValue} {value : RuntimeValue}
      (child : SourceComputationBodyEvaluates ChildEval owner table environment initialStore
        ⟨innerSpan, statements⟩ value finalStore) :
      SourceComputationBodyEvaluates ChildEval owner table environment initialStore
        ⟨outerSpan, [⟨innerSpan, .block statements⟩]⟩ value finalStore
  | binding {table : List (String × Resolved.LocalId)} {environment : List (Resolved.LocalId × RuntimeValue)}
      {blockSpan letSpan : Syntax.SourceSpan} {name : Syntax.Identifier}
      {annotation : Syntax.TypeExpr} {initializer : Syntax.Expr} {rest : List Syntax.Statement}
      {initialStore middleStore finalStore : List RuntimeValue} {boundValue value : RuntimeValue}
      (initializerEvaluation : ChildEval owner table environment initialStore initializer boundValue middleStore)
      (tailEvaluation : SourceComputationBodyEvaluates ChildEval owner
        ((name.value, Resolved.freshLocalId owner (table.map Prod.snd)) :: table)
        ((Resolved.freshLocalId owner (table.map Prod.snd), boundValue) :: environment)
        middleStore ⟨blockSpan, rest⟩ value finalStore) :
      SourceComputationBodyEvaluates ChildEval owner table environment initialStore
        ⟨blockSpan, ⟨letSpan, .letDecl name (some annotation) (some initializer)⟩ :: rest⟩ value finalStore
  | inferred {table : List (String × Resolved.LocalId)} {environment : List (Resolved.LocalId × RuntimeValue)}
      {blockSpan letSpan : Syntax.SourceSpan} {name : Syntax.Identifier}
      {initializer : Syntax.Expr} {rest : List Syntax.Statement}
      {initialStore middleStore finalStore : List RuntimeValue} {boundValue value : RuntimeValue}
      (initializerEvaluation : ChildEval owner table environment initialStore initializer boundValue middleStore)
      (tailEvaluation : SourceComputationBodyEvaluates ChildEval owner
        ((name.value, Resolved.freshLocalId owner (table.map Prod.snd)) :: table)
        ((Resolved.freshLocalId owner (table.map Prod.snd), boundValue) :: environment)
        middleStore ⟨blockSpan, rest⟩ value finalStore) :
      SourceComputationBodyEvaluates ChildEval owner table environment initialStore
        ⟨blockSpan, ⟨letSpan, .letDecl name none (some initializer)⟩ :: rest⟩ value finalStore
  | discard {table : List (String × Resolved.LocalId)} {environment : List (Resolved.LocalId × RuntimeValue)}
      {blockSpan statementSpan : Syntax.SourceSpan} {expression : Syntax.Expr} {rest : List Syntax.Statement}
      {initialStore middleStore finalStore : List RuntimeValue} {discardedValue value : RuntimeValue}
      (expressionEvaluation : ChildEval owner table environment initialStore expression discardedValue middleStore)
      (tailEvaluation : SourceComputationBodyEvaluates ChildEval owner table environment middleStore
        ⟨blockSpan, rest⟩ value finalStore) :
      SourceComputationBodyEvaluates ChildEval owner table environment initialStore
        ⟨blockSpan, ⟨statementSpan, .expression expression true⟩ :: rest⟩ value finalStore
  | ifTrue {table : List (String × Resolved.LocalId)} {environment : List (Resolved.LocalId × RuntimeValue)}
      {blockSpan ifSpan : Syntax.SourceSpan} {condition : Syntax.Expr}
      {thenBody elseBody : Syntax.Block} {initialStore middleStore finalStore : List RuntimeValue} {value : RuntimeValue}
      (conditionEvaluation : ChildEval owner table environment initialStore condition (.bool true) middleStore)
      (branchEvaluation : SourceComputationBodyEvaluates ChildEval owner table environment middleStore thenBody value finalStore) :
      SourceComputationBodyEvaluates ChildEval owner table environment initialStore
        ⟨blockSpan, [⟨ifSpan, .ifThen condition thenBody (some elseBody)⟩]⟩ value finalStore
  | ifFalse {table : List (String × Resolved.LocalId)} {environment : List (Resolved.LocalId × RuntimeValue)}
      {blockSpan ifSpan : Syntax.SourceSpan} {condition : Syntax.Expr}
      {thenBody elseBody : Syntax.Block} {initialStore middleStore finalStore : List RuntimeValue} {value : RuntimeValue}
      (conditionEvaluation : ChildEval owner table environment initialStore condition (.bool false) middleStore)
      (branchEvaluation : SourceComputationBodyEvaluates ChildEval owner table environment middleStore elseBody value finalStore) :
      SourceComputationBodyEvaluates ChildEval owner table environment initialStore
        ⟨blockSpan, [⟨ifSpan, .ifThen condition thenBody (some elseBody)⟩]⟩ value finalStore

  | wordMatch {table : List (String × Resolved.LocalId)} {environment : List (Resolved.LocalId × RuntimeValue)}
      {blockSpan matchSpan scrutineeSpan armsSpan : Syntax.SourceSpan}
      {scrutinee : Syntax.Expr} {cases : List Syntax.MatchCase}
      {defaultBody : Option Syntax.Block} {selected : Syntax.Block}
      {initialStore middleStore finalStore : List RuntimeValue} {scrutineeValue value : RuntimeValue} {tests : Nat}
      (scrutineeEvaluation : ChildEval owner table environment initialStore scrutinee scrutineeValue middleStore)
      (choice : RuntimeWordMatchChooses scrutineeValue cases defaultBody selected tests)
      (branchEvaluation : SourceComputationBodyEvaluates ChildEval owner table environment
        middleStore selected value finalStore) :
      SourceComputationBodyEvaluates ChildEval owner table environment initialStore
        ⟨blockSpan, [⟨matchSpan, .matchWith ⟨scrutineeSpan, ⟨scrutinee, []⟩⟩
          ⟨armsSpan, ⟨cases, defaultBody⟩⟩⟩]⟩ value finalStore

end Solcore.Frontend
