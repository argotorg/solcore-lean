import Solcore.Frontend.SourceLambdaEvaluation
import Solcore.Frontend.SourceComputationBodyEvaluation
import Solcore.Frontend.LocalReference

/-! Callback-free successful evaluation of original expressions and bodies.
Closed refers to recursive judgments, not empty lexical inputs. Original syntax,
ordered captures and actual mixed stores remain literal. Core/host values are
inert data; no typing, store mutation, staging or termination claim is added. -/

set_option autoImplicit false
namespace Solcore.Frontend

mutual

/-- Twelve original expression forms, recursively closed with original body evaluation.
Owner is an index so calls can switch to the closure's saved lexical scope. -/
inductive ClosedSourceExpressionEvaluates :
    Resolved.DeclarationId → List (String × Resolved.LocalId) →
    List (Resolved.LocalId × RuntimeValue) → List RuntimeValue →
    Syntax.Expr → RuntimeValue → List RuntimeValue → Prop where
  | reference {owner names captured store span name id value}
      (named : LocalNameTable.Lookup names name.value id)
      (found : Resolved.LocalScope.Lookup captured id value) :
      ClosedSourceExpressionEvaluates owner names captured store
        ⟨span, .identifier name⟩ value store
  | unit {owner names captured store span tupleSpan} :
      ClosedSourceExpressionEvaluates owner names captured store
        ⟨span, .tuple ⟨tupleSpan, []⟩⟩ .unit store
  | wordLiteral {owner names captured store span literal word}
      (meaning : WordLiteralDenotes literal word) :
      ClosedSourceExpressionEvaluates owner names captured store
        ⟨span, .literal literal⟩ (.word word) store
  | group {owner names captured initialStore finalStore span inner value}
      (child : ClosedSourceExpressionEvaluates owner names captured
        initialStore inner value finalStore) :
      ClosedSourceExpressionEvaluates owner names captured initialStore
        ⟨span, .group inner⟩ value finalStore
  | pair {owner names captured initialStore middleStore finalStore}
      {span tupleSpan left right leftValue rightValue}
      (leftEvaluation : ClosedSourceExpressionEvaluates owner names captured
        initialStore left leftValue middleStore)
      (rightEvaluation : ClosedSourceExpressionEvaluates owner names captured
        middleStore right rightValue finalStore) :
      ClosedSourceExpressionEvaluates owner names captured initialStore
        ⟨span, .tuple ⟨tupleSpan, [left, right]⟩⟩ (.pair leftValue rightValue) finalStore
  | many {owner names captured initialStore middleStore finalStore}
      {span tupleSpan first second third rest headValue tailValue}
      (headEvaluation : ClosedSourceExpressionEvaluates owner names captured
        initialStore first headValue middleStore)
      (tailEvaluation : ClosedSourceExpressionEvaluates owner names captured middleStore
        ⟨span, .tuple ⟨tupleSpan, second :: third :: rest⟩⟩ tailValue finalStore) :
      ClosedSourceExpressionEvaluates owner names captured initialStore
        ⟨span, .tuple ⟨tupleSpan, first :: second :: third :: rest⟩⟩
        (.pair headValue tailValue) finalStore
  | creation {owner names captured store source name body}
      (shape : SourceUnaryLambdaShape source name body) :
      ClosedSourceExpressionEvaluates owner names captured store source
        (.sourceClosure source owner names captured) store
  | call {owner names captured initialStore calleeStore argumentStore finalStore}
      {span argumentsSpan callee argument source savedOwner savedNames savedCaptured name body argumentValue result}
      (shape : SourceUnaryLambdaShape source name body)
      (calleeEvaluation : ClosedSourceExpressionEvaluates owner names captured initialStore callee
        (.sourceClosure source savedOwner savedNames savedCaptured) calleeStore)
      (argumentEvaluation : ClosedSourceExpressionEvaluates owner names captured calleeStore
        argument argumentValue argumentStore)
      (bodyEvaluation : ClosedSourceBodyEvaluates savedOwner
        ((name.value, Resolved.freshLocalId savedOwner (savedNames.map Prod.snd)) :: savedNames)
        ((Resolved.freshLocalId savedOwner (savedNames.map Prod.snd), argumentValue) :: savedCaptured)
        argumentStore body result finalStore) :
      ClosedSourceExpressionEvaluates owner names captured initialStore
        ⟨span, .call callee ⟨argumentsSpan, [argument]⟩⟩ result finalStore

  | conditionalTrue {owner names captured initialStore middleStore finalStore}
      {span question colon condition thenBranch elseBranch value}
      (conditionEvaluation : ClosedSourceExpressionEvaluates owner names captured
        initialStore condition (.bool true) middleStore)
      (branchEvaluation : ClosedSourceExpressionEvaluates owner names captured
        middleStore thenBranch value finalStore) :
      ClosedSourceExpressionEvaluates owner names captured initialStore
        ⟨span, .conditional condition question thenBranch colon elseBranch⟩ value finalStore
  | conditionalFalse {owner names captured initialStore middleStore finalStore}
      {span question colon condition thenBranch elseBranch value}
      (conditionEvaluation : ClosedSourceExpressionEvaluates owner names captured
        initialStore condition (.bool false) middleStore)
      (branchEvaluation : ClosedSourceExpressionEvaluates owner names captured
        middleStore elseBranch value finalStore) :
      ClosedSourceExpressionEvaluates owner names captured initialStore
        ⟨span, .conditional condition question thenBranch colon elseBranch⟩ value finalStore

  | logicalNot {owner names captured initialStore finalStore}
      {span operatorSpan : Syntax.SourceSpan} {operand : Syntax.Expr} {value : Bool}
      (child : ClosedSourceExpressionEvaluates owner names captured
        initialStore operand (.bool value) finalStore) :
      ClosedSourceExpressionEvaluates owner names captured initialStore
        ⟨span, .unary ⟨operatorSpan, .logicalNot⟩ operand⟩ (.bool (!value)) finalStore
  | bitNot {owner names captured initialStore finalStore}
      {span operatorSpan : Syntax.SourceSpan} {operand : Syntax.Expr} {value : Core.Word}
      (child : ClosedSourceExpressionEvaluates owner names captured
        initialStore operand (.word value) finalStore) :
      ClosedSourceExpressionEvaluates owner names captured initialStore
        ⟨span, .unary ⟨operatorSpan, .bitNot⟩ operand⟩ (.word value.bitNot) finalStore

/-- The nine original body forms with recursively closed expression children.
Initializers precede fresh binding; annotations and unselected branches are inert. -/
inductive ClosedSourceBodyEvaluates :
    Resolved.DeclarationId → List (String × Resolved.LocalId) →
    List (Resolved.LocalId × RuntimeValue) → List RuntimeValue →
    Syntax.Block → RuntimeValue → List RuntimeValue → Prop where
  | bare {owner : Resolved.DeclarationId} {table : List (String × Resolved.LocalId)}
      {environment : List (Resolved.LocalId × RuntimeValue)}
      {blockSpan returnSpan : Syntax.SourceSpan} {store : List RuntimeValue} :
      ClosedSourceBodyEvaluates owner table environment store
        ⟨blockSpan, [⟨returnSpan, .returnStmt none⟩]⟩ .unit store
  | expression {owner : Resolved.DeclarationId} {table : List (String × Resolved.LocalId)}
      {environment : List (Resolved.LocalId × RuntimeValue)}
      {blockSpan returnSpan : Syntax.SourceSpan} {source : Syntax.Expr}
      {initialStore finalStore : List RuntimeValue} {value : RuntimeValue}
      (child : ClosedSourceExpressionEvaluates owner table environment initialStore source value finalStore) :
      ClosedSourceBodyEvaluates owner table environment initialStore
        ⟨blockSpan, [⟨returnSpan, .returnStmt (some source)⟩]⟩ value finalStore
  | block {owner : Resolved.DeclarationId} {table : List (String × Resolved.LocalId)}
      {environment : List (Resolved.LocalId × RuntimeValue)}
      {outerSpan innerSpan : Syntax.SourceSpan} {statements : List Syntax.Statement}
      {initialStore finalStore : List RuntimeValue} {value : RuntimeValue}
      (child : ClosedSourceBodyEvaluates owner table environment initialStore
        ⟨innerSpan, statements⟩ value finalStore) :
      ClosedSourceBodyEvaluates owner table environment initialStore
        ⟨outerSpan, [⟨innerSpan, .block statements⟩]⟩ value finalStore
  | binding {owner : Resolved.DeclarationId} {table : List (String × Resolved.LocalId)}
      {environment : List (Resolved.LocalId × RuntimeValue)}
      {blockSpan letSpan : Syntax.SourceSpan} {name : Syntax.Identifier}
      {annotation : Syntax.TypeExpr} {initializer : Syntax.Expr} {rest : List Syntax.Statement}
      {initialStore middleStore finalStore : List RuntimeValue} {boundValue value : RuntimeValue}
      (initializerEvaluation : ClosedSourceExpressionEvaluates owner table environment initialStore initializer boundValue middleStore)
      (tailEvaluation : ClosedSourceBodyEvaluates owner
        ((name.value, Resolved.freshLocalId owner (table.map Prod.snd)) :: table)
        ((Resolved.freshLocalId owner (table.map Prod.snd), boundValue) :: environment)
        middleStore ⟨blockSpan, rest⟩ value finalStore) :
      ClosedSourceBodyEvaluates owner table environment initialStore
        ⟨blockSpan, ⟨letSpan, .letDecl name (some annotation) (some initializer)⟩ :: rest⟩ value finalStore
  | inferred {owner : Resolved.DeclarationId} {table : List (String × Resolved.LocalId)}
      {environment : List (Resolved.LocalId × RuntimeValue)}
      {blockSpan letSpan : Syntax.SourceSpan} {name : Syntax.Identifier}
      {initializer : Syntax.Expr} {rest : List Syntax.Statement}
      {initialStore middleStore finalStore : List RuntimeValue} {boundValue value : RuntimeValue}
      (initializerEvaluation : ClosedSourceExpressionEvaluates owner table environment initialStore initializer boundValue middleStore)
      (tailEvaluation : ClosedSourceBodyEvaluates owner
        ((name.value, Resolved.freshLocalId owner (table.map Prod.snd)) :: table)
        ((Resolved.freshLocalId owner (table.map Prod.snd), boundValue) :: environment)
        middleStore ⟨blockSpan, rest⟩ value finalStore) :
      ClosedSourceBodyEvaluates owner table environment initialStore
        ⟨blockSpan, ⟨letSpan, .letDecl name none (some initializer)⟩ :: rest⟩ value finalStore
  | discard {owner : Resolved.DeclarationId} {table : List (String × Resolved.LocalId)}
      {environment : List (Resolved.LocalId × RuntimeValue)}
      {blockSpan statementSpan : Syntax.SourceSpan} {expression : Syntax.Expr} {rest : List Syntax.Statement}
      {initialStore middleStore finalStore : List RuntimeValue} {discardedValue value : RuntimeValue}
      (expressionEvaluation : ClosedSourceExpressionEvaluates owner table environment initialStore expression discardedValue middleStore)
      (tailEvaluation : ClosedSourceBodyEvaluates owner table environment middleStore
        ⟨blockSpan, rest⟩ value finalStore) :
      ClosedSourceBodyEvaluates owner table environment initialStore
        ⟨blockSpan, ⟨statementSpan, .expression expression true⟩ :: rest⟩ value finalStore
  | ifTrue {owner : Resolved.DeclarationId} {table : List (String × Resolved.LocalId)}
      {environment : List (Resolved.LocalId × RuntimeValue)}
      {blockSpan ifSpan : Syntax.SourceSpan} {condition : Syntax.Expr}
      {thenBody elseBody : Syntax.Block} {initialStore middleStore finalStore : List RuntimeValue} {value : RuntimeValue}
      (conditionEvaluation : ClosedSourceExpressionEvaluates owner table environment initialStore condition (.bool true) middleStore)
      (branchEvaluation : ClosedSourceBodyEvaluates owner table environment middleStore thenBody value finalStore) :
      ClosedSourceBodyEvaluates owner table environment initialStore
        ⟨blockSpan, [⟨ifSpan, .ifThen condition thenBody (some elseBody)⟩]⟩ value finalStore
  | ifFalse {owner : Resolved.DeclarationId} {table : List (String × Resolved.LocalId)}
      {environment : List (Resolved.LocalId × RuntimeValue)}
      {blockSpan ifSpan : Syntax.SourceSpan} {condition : Syntax.Expr}
      {thenBody elseBody : Syntax.Block} {initialStore middleStore finalStore : List RuntimeValue} {value : RuntimeValue}
      (conditionEvaluation : ClosedSourceExpressionEvaluates owner table environment initialStore condition (.bool false) middleStore)
      (branchEvaluation : ClosedSourceBodyEvaluates owner table environment middleStore elseBody value finalStore) :
      ClosedSourceBodyEvaluates owner table environment initialStore
        ⟨blockSpan, [⟨ifSpan, .ifThen condition thenBody (some elseBody)⟩]⟩ value finalStore

  | wordMatch {owner : Resolved.DeclarationId} {table : List (String × Resolved.LocalId)}
      {environment : List (Resolved.LocalId × RuntimeValue)}
      {blockSpan matchSpan scrutineeSpan armsSpan : Syntax.SourceSpan}
      {scrutinee : Syntax.Expr} {cases : List Syntax.MatchCase}
      {defaultBody : Option Syntax.Block} {selected : Syntax.Block}
      {initialStore middleStore finalStore : List RuntimeValue} {scrutineeValue value : RuntimeValue} {tests : Nat}
      (scrutineeEvaluation : ClosedSourceExpressionEvaluates owner table environment initialStore scrutinee scrutineeValue middleStore)
      (choice : RuntimeWordMatchChooses scrutineeValue cases defaultBody selected tests)
      (branchEvaluation : ClosedSourceBodyEvaluates owner table environment
        middleStore selected value finalStore) :
      ClosedSourceBodyEvaluates owner table environment initialStore
        ⟨blockSpan, [⟨matchSpan, .matchWith ⟨scrutineeSpan, ⟨scrutinee, []⟩⟩
          ⟨armsSpan, ⟨cases, defaultBody⟩⟩⟩]⟩ value finalStore

end

end Solcore.Frontend
