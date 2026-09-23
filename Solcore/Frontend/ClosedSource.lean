import Solcore.Syntax.Term
import Solcore.Frontend.StrictWordBinary
import Solcore.Frontend.SourceLambdaEvaluation
import Solcore.Frontend.SourceComputationBody
import Solcore.Frontend.LocalReference
import Solcore.Frontend.LocalExpressionEvaluation
import Solcore.Frontend.RuntimeValue
import Solcore.Frontend.Computation
import Solcore.Frontend.LocalExpressionExecutionProperties
import Solcore.Frontend.TypedLetReturnTree
import Solcore.Core.LocalFragment
import Solcore.Resolved.LocalScope
import Solcore.Frontend.RuntimeWordMatch
import Solcore.Frontend.WordLiteral
import Solcore.Frontend.RuntimeCapturedOwnerProperties
import Solcore.Frontend.LocalExpressionRenaming

/-! Closed-source syntax, evaluation, executable checking, and proof support. -/

/-!
## Consolidated module: `Solcore.Frontend.ClosedSourceDataDepthBound`
-/

/- A source-only upper depth for the recursive data-expression gate.
It is not Core transition cost or a search bound for source closures/calls.
Unsupported shapes receive zero; the syntax gate is a separate premise. -/
set_option autoImplicit false
namespace Solcore.Frontend

/-- Pays one recursive source-search level per written data node, including
groups and each right-associated tuple tail. Both potential branches are counted
through a maximum, independently of runtime inputs, lexical rows or stores. -/
def closedSourceDataDepthBound (source : Syntax.Expr) : Nat :=
  match source with
  | ⟨_,.identifier _⟩ => 1
  | ⟨_,.literal _⟩ => 1
  | ⟨_,.group inner⟩ => closedSourceDataDepthBound inner + 1
  | ⟨_,.tuple ⟨_,[]⟩⟩ => 1
  | ⟨_,.tuple ⟨_,[left,right]⟩⟩ =>
      max (closedSourceDataDepthBound left) (closedSourceDataDepthBound right) + 1
  | ⟨span,.tuple ⟨tupleSpan,first::second::third::rest⟩⟩ =>
      max (closedSourceDataDepthBound first)
        (closedSourceDataDepthBound ⟨span,.tuple ⟨tupleSpan,second::third::rest⟩⟩) + 1
  | ⟨_,.unary _ child⟩ => closedSourceDataDepthBound child + 1
  | ⟨_,.binary left _ right⟩ =>
      max (closedSourceDataDepthBound left) (closedSourceDataDepthBound right) + 1
  | ⟨_,.conditional condition _ thenBranch _ elseBranch⟩ =>
      max (closedSourceDataDepthBound condition)
        (max (closedSourceDataDepthBound thenBranch) (closedSourceDataDepthBound elseBranch)) + 1
  | _ => 0
termination_by sizeOf source

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.ClosedSourceDataBodyDepthBound`
-/

/- Source-search upper depths for gated original bodies and all written match
branches. This is independent of match comparison counts and Core step costs.
Unhandled root forms receive zero; the separate syntax gate remains essential. -/
set_option autoImplicit false
namespace Solcore.Frontend

mutual

/-- Counts every body-search level, retaining the original reconstructed tails
and considering both conditional branches and every written match body. -/
def closedSourceDataBodyDepthBound (body : Syntax.Block) : Nat :=
  match body with
  | ⟨_, [⟨_, .returnStmt none⟩]⟩ => 1
  | ⟨_, [⟨_, .returnStmt (some child)⟩]⟩ => closedSourceDataDepthBound child + 1
  | ⟨_, [⟨innerSpan, .block statements⟩]⟩ =>
      closedSourceDataBodyDepthBound ⟨innerSpan, statements⟩ + 1
  | ⟨blockSpan, ⟨_, .letDecl _ _ (some initializer)⟩ :: rest⟩ =>
      max (closedSourceDataDepthBound initializer)
        (closedSourceDataBodyDepthBound ⟨blockSpan, rest⟩) + 1
  | ⟨blockSpan, ⟨_, .expression child true⟩ :: rest⟩ =>
      max (closedSourceDataDepthBound child)
        (closedSourceDataBodyDepthBound ⟨blockSpan, rest⟩) + 1
  | ⟨_, [⟨_, .ifThen condition thenBody (some elseBody)⟩]⟩ =>
      max (closedSourceDataDepthBound condition)
        (max (closedSourceDataBodyDepthBound thenBody) (closedSourceDataBodyDepthBound elseBody)) + 1
  | ⟨_, [⟨_, .matchWith ⟨_, ⟨scrutinee, []⟩⟩ ⟨_, ⟨cases, defaultBody⟩⟩⟩]⟩ =>
      max (closedSourceDataDepthBound scrutinee)
        (closedSourceDataMatchDepthBound cases defaultBody) + 1
  | _ => 0
termination_by sizeOf body

/-- Maximum body depth of every written arm and optional fallback. Traversing
the arm list itself consumes no recursive evaluator depth. -/
def closedSourceDataMatchDepthBound (cases : List Syntax.MatchCase)
    (defaultBody : Option Syntax.Block) : Nat :=
  match cases with
  | [] => match defaultBody with
      | none => 0
      | some body => closedSourceDataBodyDepthBound body
  | first :: rest =>
      have bodySmaller : sizeOf first.value.body < sizeOf first := by
        rcases first with ⟨_,⟨_,_⟩⟩
        simp only [Syntax.Located.mk.sizeOf_spec, Syntax.MatchCaseValue.mk.sizeOf_spec]
        omega
      max (closedSourceDataBodyDepthBound first.value.body)
        (closedSourceDataMatchDepthBound rest defaultBody)
termination_by sizeOf cases + sizeOf defaultBody

end

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.ClosedSourceDataExpression`
-/

/- Pure syntax admission for the exact closed/local data bridge.
It establishes neither successful execution nor whole structural resolution. -/
set_option autoImplicit false
namespace Solcore.Frontend

inductive ClosedSourceDataExpression : Syntax.Expr → Prop where
  | reference {span : Syntax.SourceSpan} {name : Syntax.Identifier} :
      ClosedSourceDataExpression ⟨span, .identifier name⟩
  | literal {span : Syntax.SourceSpan} {literal : Syntax.CoreLiteral} :
      ClosedSourceDataExpression ⟨span, .literal literal⟩
  | group {span : Syntax.SourceSpan} {inner : Syntax.Expr}
      (child : ClosedSourceDataExpression inner) :
      ClosedSourceDataExpression ⟨span, .group inner⟩
  | unit {span tupleSpan : Syntax.SourceSpan} :
      ClosedSourceDataExpression ⟨span, .tuple ⟨tupleSpan, []⟩⟩
  | pair {span tupleSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      (leftSyntax : ClosedSourceDataExpression left)
      (rightSyntax : ClosedSourceDataExpression right) :
      ClosedSourceDataExpression ⟨span, .tuple ⟨tupleSpan, [left, right]⟩⟩
  | many {span tupleSpan : Syntax.SourceSpan} {first second third : Syntax.Expr}
      {rest : List Syntax.Expr}
      (headSyntax : ClosedSourceDataExpression first)
      (tailSyntax : ClosedSourceDataExpression
        ⟨span, .tuple ⟨tupleSpan, second :: third :: rest⟩⟩) :
      ClosedSourceDataExpression ⟨span, .tuple ⟨tupleSpan, first :: second :: third :: rest⟩⟩
  | conditional {span question colon : Syntax.SourceSpan}
      {condition thenBranch elseBranch : Syntax.Expr}
      (conditionSyntax : ClosedSourceDataExpression condition)
      (thenSyntax : ClosedSourceDataExpression thenBranch)
      (elseSyntax : ClosedSourceDataExpression elseBranch) :
      ClosedSourceDataExpression
        ⟨span, .conditional condition question thenBranch colon elseBranch⟩

  | logicalNot {span operatorSpan : Syntax.SourceSpan} {operand : Syntax.Expr}
      (child : ClosedSourceDataExpression operand) :
      ClosedSourceDataExpression ⟨span, .unary ⟨operatorSpan, .logicalNot⟩ operand⟩
  | bitNot {span operatorSpan : Syntax.SourceSpan} {operand : Syntax.Expr}
      (child : ClosedSourceDataExpression operand) :
      ClosedSourceDataExpression ⟨span, .unary ⟨operatorSpan, .bitNot⟩ operand⟩

  | logicalAnd {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      (leftSyntax : ClosedSourceDataExpression left)
      (rightSyntax : ClosedSourceDataExpression right) :
      ClosedSourceDataExpression ⟨span, .binary left ⟨operatorSpan, .logicalAnd⟩ right⟩
  | logicalOr {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      (leftSyntax : ClosedSourceDataExpression left)
      (rightSyntax : ClosedSourceDataExpression right) :
      ClosedSourceDataExpression ⟨span, .binary left ⟨operatorSpan, .logicalOr⟩ right⟩

  | strictWordBinary {span operatorSpan : Syntax.SourceSpan} {operator : Syntax.BinaryOp}
      {left right : Syntax.Expr}
      (leftSyntax : ClosedSourceDataExpression left)
      (rightSyntax : ClosedSourceDataExpression right)
      (notAnd : operator ≠ .logicalAnd) (notOr : operator ≠ .logicalOr) :
      ClosedSourceDataExpression ⟨span, .binary left ⟨operatorSpan, operator⟩ right⟩

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.ClosedSourceDataBody`
-/

namespace Solcore.Frontend

/-- Original terminal bodies whose written expression children are closed data. -/
inductive ClosedSourceDataBody : Syntax.Block → Prop where
  | bare {blockSpan returnSpan : Syntax.SourceSpan} :
      ClosedSourceDataBody ⟨blockSpan, [⟨returnSpan, .returnStmt none⟩]⟩
  | expression {blockSpan returnSpan : Syntax.SourceSpan} {source : Syntax.Expr}
      (child : ClosedSourceDataExpression source) :
      ClosedSourceDataBody ⟨blockSpan, [⟨returnSpan, .returnStmt (some source)⟩]⟩
  | block {outerSpan innerSpan : Syntax.SourceSpan} {statements : List Syntax.Statement}
      (child : ClosedSourceDataBody ⟨innerSpan, statements⟩) :
      ClosedSourceDataBody ⟨outerSpan, [⟨innerSpan, .block statements⟩]⟩
  | binding {blockSpan letSpan : Syntax.SourceSpan} {name : Syntax.Identifier}
      {annotation : Option Syntax.TypeExpr} {initializer : Syntax.Expr}
      {rest : List Syntax.Statement}
      (initializerSyntax : ClosedSourceDataExpression initializer)
      (tailSyntax : ClosedSourceDataBody ⟨blockSpan, rest⟩) :
      ClosedSourceDataBody
        ⟨blockSpan, ⟨letSpan, .letDecl name annotation (some initializer)⟩ :: rest⟩
  | discard {blockSpan statementSpan : Syntax.SourceSpan} {source : Syntax.Expr}
      {rest : List Syntax.Statement}
      (child : ClosedSourceDataExpression source)
      (tailSyntax : ClosedSourceDataBody ⟨blockSpan, rest⟩) :
      ClosedSourceDataBody
        ⟨blockSpan, ⟨statementSpan, .expression source true⟩ :: rest⟩
  | conditional {blockSpan ifSpan : Syntax.SourceSpan} {condition : Syntax.Expr}
      {thenBody elseBody : Syntax.Block}
      (conditionSyntax : ClosedSourceDataExpression condition)
      (thenSyntax : ClosedSourceDataBody thenBody)
      (elseSyntax : ClosedSourceDataBody elseBody) :
      ClosedSourceDataBody
        ⟨blockSpan, [⟨ifSpan, .ifThen condition thenBody (some elseBody)⟩]⟩
  | wordMatch {blockSpan matchSpan scrutineeSpan armsSpan : Syntax.SourceSpan}
      {scrutinee : Syntax.Expr} {cases : List Syntax.MatchCase}
      {defaultBody : Option Syntax.Block}
      (scrutineeSyntax : ClosedSourceDataExpression scrutinee)
      (branches : ∀ arm ∈ cases, ClosedSourceDataBody arm.value.body)
      (fallback : ∀ source ∈ defaultBody.toList, ClosedSourceDataBody source) :
      ClosedSourceDataBody
        ⟨blockSpan, [⟨matchSpan, .matchWith ⟨scrutineeSpan, ⟨scrutinee, []⟩⟩
          ⟨armsSpan, ⟨cases, defaultBody⟩⟩⟩]⟩

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.ClosedSourceEvaluation`
-/

/-! Callback-free successful evaluation of original expressions and bodies.
Closed refers to recursive judgments, not empty lexical inputs. Original syntax,
ordered captures and actual mixed stores remain literal. Core/host values are
inert data; no typing, store mutation, staging or termination claim is added. -/

set_option autoImplicit false
namespace Solcore.Frontend

mutual

/-- Seventeen original expression evaluation rules, recursively closed with original body evaluation.
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

  | andTrue {owner names captured initialStore middleStore finalStore}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr} {value : RuntimeValue}
      (leftEvaluation : ClosedSourceExpressionEvaluates owner names captured
        initialStore left (.bool true) middleStore)
      (rightEvaluation : ClosedSourceExpressionEvaluates owner names captured
        middleStore right value finalStore) :
      ClosedSourceExpressionEvaluates owner names captured initialStore
        ⟨span, .binary left ⟨operatorSpan, .logicalAnd⟩ right⟩ value finalStore
  | andFalse {owner names captured initialStore finalStore}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      (leftEvaluation : ClosedSourceExpressionEvaluates owner names captured
        initialStore left (.bool false) finalStore) :
      ClosedSourceExpressionEvaluates owner names captured initialStore
        ⟨span, .binary left ⟨operatorSpan, .logicalAnd⟩ right⟩ (.bool false) finalStore
  | orTrue {owner names captured initialStore finalStore}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      (leftEvaluation : ClosedSourceExpressionEvaluates owner names captured
        initialStore left (.bool true) finalStore) :
      ClosedSourceExpressionEvaluates owner names captured initialStore
        ⟨span, .binary left ⟨operatorSpan, .logicalOr⟩ right⟩ (.bool true) finalStore
  | orFalse {owner names captured initialStore middleStore finalStore}
      {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr} {value : RuntimeValue}
      (leftEvaluation : ClosedSourceExpressionEvaluates owner names captured
        initialStore left (.bool false) middleStore)
      (rightEvaluation : ClosedSourceExpressionEvaluates owner names captured
        middleStore right value finalStore) :
      ClosedSourceExpressionEvaluates owner names captured initialStore
        ⟨span, .binary left ⟨operatorSpan, .logicalOr⟩ right⟩ value finalStore

  | strictWordBinary {owner names captured initialStore middleStore finalStore}
      {span operatorSpan : Syntax.SourceSpan} {operator : Syntax.BinaryOp}
      {left right : Syntax.Expr} {leftWord rightWord : Core.Word} {result : Core.Value}
      (leftEvaluation : ClosedSourceExpressionEvaluates owner names captured
        initialStore left (.word leftWord) middleStore)
      (rightEvaluation : ClosedSourceExpressionEvaluates owner names captured
        middleStore right (.word rightWord) finalStore)
      (meaning : StrictWordBinaryDenotes operator leftWord rightWord result) :
      ClosedSourceExpressionEvaluates owner names captured initialStore
        ⟨span, .binary left ⟨operatorSpan, operator⟩ right⟩
        (RuntimeValue.ofCore result) finalStore

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

/-!
## Consolidated module: `Solcore.Frontend.ClosedSourceDataExpressionProperties`
-/

/- Exact actual-output reflection for the common syntax; no evaluator or typing premise. -/
set_option autoImplicit false
namespace Solcore.Frontend

private theorem lookup_embed {environment : Resolved.Environment} {id : Resolved.LocalId}
    {value : Core.Value} (found : Resolved.LocalScope.Lookup environment id value) :
    Resolved.LocalScope.Lookup
      (environment.map (fun entry => (entry.1, RuntimeValue.ofCore entry.2)))
      id (RuntimeValue.ofCore value) := by
  induction found with
  | head => exact .head
  | tail different _ ih => exact .tail different ih

private theorem lookup_reflect (environment : Resolved.Environment) {id : Resolved.LocalId}
    {actual : RuntimeValue}
    (found : Resolved.LocalScope.Lookup
      (environment.map (fun entry => (entry.1, RuntimeValue.ofCore entry.2))) id actual) :
    ∃ value, actual = RuntimeValue.ofCore value ∧ Resolved.LocalScope.Lookup environment id value := by
  induction environment generalizing actual with
  | nil => cases found
  | cons entry environment ih =>
      obtain ⟨key, value⟩ := entry
      cases found with
      | head => exact ⟨value, rfl, .head⟩
      | tail different found =>
          obtain ⟨value, same, previous⟩ := ih found
          exact ⟨value, same, .tail different previous⟩

private theorem reflect {source : Syntax.Expr} (fragment : ClosedSourceDataExpression source)
    {owner : Resolved.DeclarationId} {names : LocalNameTable}
    {environment : Resolved.Environment} {initialStore : Core.Store}
    {actualValue : RuntimeValue} {actualFinal : List RuntimeValue}
    (evaluated : ClosedSourceExpressionEvaluates owner names
      (environment.map (fun entry => (entry.1, RuntimeValue.ofCore entry.2)))
      (initialStore.map RuntimeValue.ofCore) source actualValue actualFinal) :
    ∃ value finalStore, actualValue = RuntimeValue.ofCore value ∧
      actualFinal = finalStore.map RuntimeValue.ofCore ∧
      LocalExpressionEvaluates names environment initialStore source value finalStore := by
  induction fragment generalizing initialStore actualValue actualFinal with
  | reference =>
      cases evaluated with
      | reference named found =>
          obtain ⟨value, same, previous⟩ := lookup_reflect environment found
          exact ⟨value, initialStore, same, rfl, .identifier named previous⟩
      | creation shape => cases shape
  | literal =>
      cases evaluated with
      | wordLiteral meaning => exact ⟨.word _, initialStore,
          by simp only [RuntimeValue.ofCore], rfl, .wordLiteral meaning⟩
      | creation shape => cases shape
  | unit =>
      cases evaluated with
      | unit => exact ⟨.unit, initialStore, by simp only [RuntimeValue.ofCore], rfl, .unit⟩
      | creation shape => cases shape
  | group _ ih =>
      cases evaluated with
      | group child =>
          obtain ⟨value, finalStore, same, finalSame, previous⟩ := ih child
          exact ⟨value, finalStore, same, finalSame, .group previous⟩
      | creation shape => cases shape
  | pair _ _ leftIH rightIH =>
      cases evaluated with
      | pair left right =>
          obtain ⟨leftValue, middleStore, leftSame, middleSame, oldLeft⟩ := leftIH left
          rw [middleSame] at right
          obtain ⟨rightValue, finalStore, rightSame, finalSame, oldRight⟩ := rightIH right
          exact ⟨.pair leftValue rightValue, finalStore,
            by simp only [RuntimeValue.ofCore, leftSame, rightSame], finalSame, .pair oldLeft oldRight⟩
      | creation shape => cases shape
  | many _ _ headIH tailIH =>
      cases evaluated with
      | many head tail =>
          obtain ⟨headValue, middleStore, headSame, middleSame, oldHead⟩ := headIH head
          rw [middleSame] at tail
          obtain ⟨tailValue, finalStore, tailSame, finalSame, oldTail⟩ := tailIH tail
          exact ⟨.pair headValue tailValue, finalStore,
            by simp only [RuntimeValue.ofCore, headSame, tailSame], finalSame, .many oldHead oldTail⟩
      | creation shape => cases shape
  | conditional _ _ _ conditionIH thenIH elseIH =>
      cases evaluated with
      | conditionalTrue condition branch =>
          obtain ⟨decision, middleStore, decisionSame, middleSame, oldCondition⟩ := conditionIH condition
          have actualBool : Core.Value.bool true = decision := RuntimeValue.ofCore_injective
            (by simpa only [RuntimeValue.ofCore] using decisionSame)
          cases actualBool
          rw [middleSame] at branch
          obtain ⟨value, finalStore, same, finalSame, oldBranch⟩ := thenIH branch
          exact ⟨value, finalStore, same, finalSame, .ifTrue oldCondition oldBranch⟩
      | conditionalFalse condition branch =>
          obtain ⟨decision, middleStore, decisionSame, middleSame, oldCondition⟩ := conditionIH condition
          have actualBool : Core.Value.bool false = decision := RuntimeValue.ofCore_injective
            (by simpa only [RuntimeValue.ofCore] using decisionSame)
          cases actualBool
          rw [middleSame] at branch
          obtain ⟨value, finalStore, same, finalSame, oldBranch⟩ := elseIH branch
          exact ⟨value, finalStore, same, finalSame, .ifFalse oldCondition oldBranch⟩
      | creation shape => cases shape

  | logicalNot _ ih =>
      cases evaluated with
      | @logicalNot _ _ _ _ _ _ _ _ operandBool child =>
          obtain ⟨value, finalStore, same, finalSame, previous⟩ := ih child
          have actualBool : Core.Value.bool operandBool = value := RuntimeValue.ofCore_injective
            (by simpa only [RuntimeValue.ofCore] using same)
          cases actualBool
          exact ⟨.bool (!operandBool), finalStore,
            by simp only [RuntimeValue.ofCore], finalSame, .logicalNot previous⟩
      | creation shape => cases shape
  | bitNot _ ih =>
      cases evaluated with
      | @bitNot _ _ _ _ _ _ _ _ operandWord child =>
          obtain ⟨value, finalStore, same, finalSame, previous⟩ := ih child
          have actualWord : Core.Value.word operandWord = value := RuntimeValue.ofCore_injective
            (by simpa only [RuntimeValue.ofCore] using same)
          cases actualWord
          exact ⟨.word operandWord.bitNot, finalStore,
            by simp only [RuntimeValue.ofCore], finalSame, .bitNot previous⟩
      | creation shape => cases shape

  | logicalAnd _ _ leftIH rightIH =>
      cases evaluated with
      | andTrue left right =>
          obtain ⟨decision, middleStore, decisionSame, middleSame, oldLeft⟩ := leftIH left
          have actualBool : Core.Value.bool true = decision := RuntimeValue.ofCore_injective
            (by simpa only [RuntimeValue.ofCore] using decisionSame)
          cases actualBool
          rw [middleSame] at right
          obtain ⟨value, finalStore, same, finalSame, oldRight⟩ := rightIH right
          exact ⟨value, finalStore, same, finalSame, .andTrue oldLeft oldRight⟩
      | andFalse left =>
          obtain ⟨decision, finalStore, decisionSame, finalSame, oldLeft⟩ := leftIH left
          have actualBool : Core.Value.bool false = decision := RuntimeValue.ofCore_injective
            (by simpa only [RuntimeValue.ofCore] using decisionSame)
          cases actualBool
          exact ⟨.bool false, finalStore,
            by simp only [RuntimeValue.ofCore], finalSame, .andFalse oldLeft⟩
      | creation shape => cases shape
      | strictWordBinary _ _ meaning => cases meaning
  | logicalOr _ _ leftIH rightIH =>
      cases evaluated with
      | orTrue left =>
          obtain ⟨decision, finalStore, decisionSame, finalSame, oldLeft⟩ := leftIH left
          have actualBool : Core.Value.bool true = decision := RuntimeValue.ofCore_injective
            (by simpa only [RuntimeValue.ofCore] using decisionSame)
          cases actualBool
          exact ⟨.bool true, finalStore,
            by simp only [RuntimeValue.ofCore], finalSame, .orTrue oldLeft⟩
      | orFalse left right =>
          obtain ⟨decision, middleStore, decisionSame, middleSame, oldLeft⟩ := leftIH left
          have actualBool : Core.Value.bool false = decision := RuntimeValue.ofCore_injective
            (by simpa only [RuntimeValue.ofCore] using decisionSame)
          cases actualBool
          rw [middleSame] at right
          obtain ⟨value, finalStore, same, finalSame, oldRight⟩ := rightIH right
          exact ⟨value, finalStore, same, finalSame, .orFalse oldLeft oldRight⟩
      | creation shape => cases shape
      | strictWordBinary _ _ meaning => cases meaning

  | strictWordBinary _ _ notAnd notOr leftIH rightIH =>
      cases evaluated with
      | creation shape => cases shape
      | andTrue _ _ => exact False.elim (notAnd rfl)
      | andFalse _ => exact False.elim (notAnd rfl)
      | orTrue _ => exact False.elim (notOr rfl)
      | orFalse _ _ => exact False.elim (notOr rfl)
      | @strictWordBinary _ _ _ _ _ _ _ _ _ _ _ leftWord rightWord result left right meaning =>
          obtain ⟨leftValue, middleStore, leftSame, middleSame, oldLeft⟩ := leftIH left
          have actualLeft : Core.Value.word leftWord = leftValue := RuntimeValue.ofCore_injective
            (by simpa only [RuntimeValue.ofCore] using leftSame)
          cases actualLeft
          rw [middleSame] at right
          obtain ⟨rightValue, finalStore, rightSame, finalSame, oldRight⟩ := rightIH right
          have actualRight : Core.Value.word rightWord = rightValue := RuntimeValue.ofCore_injective
            (by simpa only [RuntimeValue.ofCore] using rightSame)
          cases actualRight
          cases meaning <;> refine ⟨_, finalStore, rfl, finalSame, ?_⟩ <;> constructor <;> assumption

private theorem embed {source : Syntax.Expr} (fragment : ClosedSourceDataExpression source)
    {owner : Resolved.DeclarationId} {names : LocalNameTable}
    {environment : Resolved.Environment} {initialStore finalStore : Core.Store} {value : Core.Value}
    (evaluated : LocalExpressionEvaluates names environment initialStore source value finalStore) :
    ClosedSourceExpressionEvaluates owner names
      (environment.map (fun entry => (entry.1, RuntimeValue.ofCore entry.2)))
      (initialStore.map RuntimeValue.ofCore) source (RuntimeValue.ofCore value)
      (finalStore.map RuntimeValue.ofCore) := by
  induction fragment generalizing initialStore finalStore value with
  | reference =>
      cases evaluated with
      | identifier named found => exact .reference named (lookup_embed found)
  | literal =>
      cases evaluated with
      | wordLiteral meaning => simp only [RuntimeValue.ofCore]; exact .wordLiteral meaning
  | unit => cases evaluated; simp only [RuntimeValue.ofCore]; exact .unit
  | group _ ih =>
      cases evaluated with
      | group child => exact .group (ih child)
  | pair _ _ leftIH rightIH =>
      cases evaluated with
      | pair left right => simp only [RuntimeValue.ofCore]; exact .pair (leftIH left) (rightIH right)
  | many _ _ headIH tailIH =>
      cases evaluated with
      | many head tail => simp only [RuntimeValue.ofCore]; exact .many (headIH head) (tailIH tail)
  | conditional _ _ _ conditionIH thenIH elseIH =>
      cases evaluated with
      | ifTrue condition branch =>
          exact .conditionalTrue (by simpa only [RuntimeValue.ofCore] using conditionIH condition)
            (thenIH branch)
      | ifFalse condition branch =>
          exact .conditionalFalse (by simpa only [RuntimeValue.ofCore] using conditionIH condition)
            (elseIH branch)

  | logicalNot _ ih =>
      cases evaluated with
      | logicalNot child =>
          simp only [RuntimeValue.ofCore]
          exact .logicalNot (by simpa only [RuntimeValue.ofCore] using ih child)
  | bitNot _ ih =>
      cases evaluated with
      | bitNot child =>
          simp only [RuntimeValue.ofCore]
          exact .bitNot (by simpa only [RuntimeValue.ofCore] using ih child)

  | logicalAnd _ _ leftIH rightIH =>
      cases evaluated with
      | andTrue left right =>
          exact .andTrue (by simpa only [RuntimeValue.ofCore] using leftIH left) (rightIH right)
      | andFalse left =>
          simp only [RuntimeValue.ofCore]
          exact .andFalse (by simpa only [RuntimeValue.ofCore] using leftIH left)
  | logicalOr _ _ leftIH rightIH =>
      cases evaluated with
      | orTrue left =>
          simp only [RuntimeValue.ofCore]
          exact .orTrue (by simpa only [RuntimeValue.ofCore] using leftIH left)
      | orFalse left right =>
          exact .orFalse (by simpa only [RuntimeValue.ofCore] using leftIH left) (rightIH right)

  | strictWordBinary _ _ notAnd notOr leftIH rightIH =>
      cases evaluated <;> first
      | exact False.elim (notAnd rfl)
      | exact False.elim (notOr rfl)
      | rename_i middle leftWord rightWord left right
        have l := leftIH left
        have r := rightIH right
        simp only [RuntimeValue.ofCore] at l r
        exact .strictWordBinary l r (by constructor)

/-- Every actual mixed result and whole final store is exactly an old local result's image. -/
theorem ClosedSourceDataExpression.local_evaluates_iff
    {owner : Resolved.DeclarationId} {names : LocalNameTable}
    {environment : Resolved.Environment} {initialStore : Core.Store}
    {source : Syntax.Expr} {actualValue : RuntimeValue} {actualFinal : List RuntimeValue}
    (fragment : ClosedSourceDataExpression source) :
    ClosedSourceExpressionEvaluates owner names
      (environment.map (fun entry => (entry.1, RuntimeValue.ofCore entry.2)))
      (initialStore.map RuntimeValue.ofCore) source actualValue actualFinal ↔
    ∃ value finalStore,
      actualValue = RuntimeValue.ofCore value ∧
      actualFinal = finalStore.map RuntimeValue.ofCore ∧
      LocalExpressionEvaluates names environment initialStore source value finalStore := by
  constructor
  · exact reflect fragment
  · rintro ⟨value, finalStore, rfl, rfl, evaluated⟩
    exact embed fragment evaluated

/-- Whole resolution and the exact runtime identity order compose the independent raw bridge. -/
theorem ClosedSourceDataExpression.core_evaluates_iff
    {owner : Resolved.DeclarationId} {names : LocalNameTable}
    {environment : Resolved.Environment} {initialStore : Core.Store}
    {source : Syntax.Expr} {actualValue : RuntimeValue} {actualFinal : List RuntimeValue}
    (fragment : ClosedSourceDataExpression source)
    {resolved : Resolved.Expr} {core : Core.Expr}
    (resolution : ResolvesLocalExpression names source resolved)
    (lowered : Resolved.Lowers (Resolved.LocalScope.ids environment) resolved core) :
    ClosedSourceExpressionEvaluates owner names
      (environment.map (fun entry => (entry.1, RuntimeValue.ofCore entry.2)))
      (initialStore.map RuntimeValue.ofCore) source actualValue actualFinal ↔
    ∃ value finalStore,
      actualValue = RuntimeValue.ofCore value ∧
      actualFinal = finalStore.map RuntimeValue.ofCore ∧
      Core.Evaluates (Resolved.LocalScope.values environment) initialStore core value finalStore := by
  rw [fragment.local_evaluates_iff]
  constructor
  · rintro ⟨value, finalStore, same, finalSame, evaluated⟩
    exact ⟨value, finalStore, same, finalSame, (resolution.core_evaluates_iff lowered).mp evaluated⟩
  · rintro ⟨value, finalStore, same, finalSame, evaluated⟩
    exact ⟨value, finalStore, same, finalSame, (resolution.core_evaluates_iff lowered).mpr evaluated⟩

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.ClosedSourceEvaluationCompatibility`
-/

/- Exact original-body and unary-call correspondence, with no child callback
hypothesis or old-value image restriction. -/
set_option autoImplicit false
namespace Solcore.Frontend

private theorem body_forward {owner names captured initialStore body value finalStore}
    (evaluated : ClosedSourceBodyEvaluates owner names captured initialStore body value finalStore) :
    SourceComputationBodyEvaluates ClosedSourceExpressionEvaluates owner names captured
      initialStore body value finalStore := by
  induction evaluated using ClosedSourceBodyEvaluates.rec
    (motive_1 := fun _ _ _ _ _ _ _ _ => True) with
  | reference => trivial
  | unit => trivial
  | wordLiteral => trivial
  | group => trivial
  | pair => trivial
  | many => trivial
  | creation => trivial
  | call => trivial
  | conditionalTrue => trivial
  | conditionalFalse => trivial
  | logicalNot => trivial
  | bitNot => trivial
  | andTrue => trivial
  | andFalse => trivial
  | orTrue => trivial
  | orFalse => trivial
  | strictWordBinary => trivial
  | bare => exact .bare
  | expression child _ => exact .expression child
  | block _ ih => exact .block ih
  | binding initializer _ _ ih => exact .binding initializer ih
  | inferred initializer _ _ ih => exact .inferred initializer ih
  | discard expression _ _ ih => exact .discard expression ih
  | ifTrue condition _ _ ih => exact .ifTrue condition ih
  | ifFalse condition _ _ ih => exact .ifFalse condition ih
  | wordMatch scrutinee choice _ _ ih => exact .wordMatch scrutinee choice ih

/-- Exact original-body correspondence at every actual mixed input and endpoint. -/
theorem closedSourceBodyEvaluates_iff {owner names captured initialStore body value finalStore} :
    ClosedSourceBodyEvaluates owner names captured initialStore body value finalStore ↔
    SourceComputationBodyEvaluates ClosedSourceExpressionEvaluates owner names captured
      initialStore body value finalStore := by
  constructor
  · exact body_forward
  · intro evaluated
    induction evaluated with
    | bare => exact .bare
    | expression child => exact .expression child
    | block _ ih => exact .block ih
    | binding initializer _ ih => exact .binding initializer ih
    | inferred initializer _ ih => exact .inferred initializer ih
    | discard expression _ ih => exact .discard expression ih
    | ifTrue condition _ ih => exact .ifTrue condition ih
    | ifFalse condition _ ih => exact .ifFalse condition ih
    | wordMatch scrutinee choice _ ih => exact .wordMatch scrutinee choice ih

/-- Exact compatibility only for original unary calls, retaining caller children,
saved lexical fields and actual intermediate stores without callback premises. -/
theorem closedSourceExpressionEvaluates_call_iff
    {owner names captured initialStore finalStore span argumentsSpan callee argument result} :
    ClosedSourceExpressionEvaluates owner names captured initialStore
      ⟨span, .call callee ⟨argumentsSpan, [argument]⟩⟩ result finalStore ↔
    SourceLambdaEvaluates ClosedSourceExpressionEvaluates
      (SourceComputationBodyEvaluates ClosedSourceExpressionEvaluates) owner names captured
      initialStore ⟨span, .call callee ⟨argumentsSpan, [argument]⟩⟩ result finalStore := by
  constructor
  · intro evaluated
    cases evaluated with
    | creation shape => cases shape
    | call shape calleeEvaluation argumentEvaluation bodyEvaluation =>
        exact .call shape calleeEvaluation argumentEvaluation
          (closedSourceBodyEvaluates_iff.mp bodyEvaluation)
  · intro evaluated
    cases evaluated with
    | creation shape => cases shape
    | call shape calleeEvaluation argumentEvaluation bodyEvaluation =>
        exact .call shape calleeEvaluation argumentEvaluation
          (closedSourceBodyEvaluates_iff.mpr bodyEvaluation)

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.ClosedSourceDataBodyProperties`
-/

/- Restrict only private child predicates, then reuse the full actual-image body bridge. -/
set_option autoImplicit false
namespace Solcore.Frontend

private def oldChild (names : LocalNameTable) (environment : Resolved.Environment)
    (initialStore : Core.Store) (source : Syntax.Expr) (value : Core.Value) (finalStore : Core.Store) : Prop :=
  ClosedSourceDataExpression source ∧
    LocalExpressionEvaluates names environment initialStore source value finalStore
private def mixedChild (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (environment : List (Resolved.LocalId × RuntimeValue)) (initialStore : List RuntimeValue)
    (source : Syntax.Expr) (value : RuntimeValue) (finalStore : List RuntimeValue) : Prop :=
  ClosedSourceDataExpression source ∧
    ClosedSourceExpressionEvaluates owner names environment initialStore source value finalStore

private theorem selected_body_property {actual : RuntimeValue} {cases : List Syntax.MatchCase}
    {defaultBody : Option Syntax.Block} {selected : Syntax.Block} {tests : Nat}
    (choice : RuntimeWordMatchChooses actual cases defaultBody selected tests)
    {P : Syntax.Block → Prop} (branches : ∀ arm ∈ cases, P arm.value.body)
    (fallback : ∀ source ∈ defaultBody.toList, P source) : P selected := by
  induction choice with
  | fallback => exact fallback _ (by simp)
  | wildcard _ => exact branches _ List.mem_cons_self
  | hit _ => exact branches _ List.mem_cons_self
  | miss _ _ _ ih => exact ih (fun arm member => branches arm (List.mem_cons_of_mem _ member)) fallback

private theorem mixed_add {owner names environment initialStore body value finalStore}
    (evaluated : SourceComputationBodyEvaluates ClosedSourceExpressionEvaluates owner names
      environment initialStore body value finalStore) :
    ClosedSourceDataBody body →
      SourceComputationBodyEvaluates mixedChild owner names environment initialStore body value finalStore := by
  induction evaluated with
  | bare => intro _; exact .bare
  | expression child =>
      intro gate; cases gate with
      | expression admitted => exact .expression ⟨admitted, child⟩
  | block _ ih =>
      intro gate; cases gate with
      | block admitted => exact .block (ih admitted)
  | binding initializer _ ih =>
      intro gate; cases gate with
      | binding admitted tail => exact .binding ⟨admitted, initializer⟩ (ih tail)
  | inferred initializer _ ih =>
      intro gate; cases gate with
      | binding admitted tail => exact .inferred ⟨admitted, initializer⟩ (ih tail)
  | discard child _ ih =>
      intro gate; cases gate with
      | discard admitted tail => exact .discard ⟨admitted, child⟩ (ih tail)
  | ifTrue condition _ ih =>
      intro gate; cases gate with
      | conditional admitted yes _ => exact .ifTrue ⟨admitted, condition⟩ (ih yes)
  | ifFalse condition _ ih =>
      intro gate; cases gate with
      | conditional admitted _ no => exact .ifFalse ⟨admitted, condition⟩ (ih no)
  | wordMatch scrutinee choice _ ih =>
      intro gate; cases gate with
      | wordMatch admitted branches fallback =>
          exact .wordMatch ⟨admitted, scrutinee⟩ choice (ih (selected_body_property choice branches fallback))

private theorem mixed_remove {owner names environment initialStore body value finalStore}
    (evaluated : SourceComputationBodyEvaluates mixedChild owner names environment
      initialStore body value finalStore) :
    SourceComputationBodyEvaluates ClosedSourceExpressionEvaluates owner names environment
      initialStore body value finalStore := by
  induction evaluated with
  | bare => exact .bare
  | expression child => exact .expression child.2
  | block _ ih => exact .block ih
  | binding initializer _ ih => exact .binding initializer.2 ih
  | inferred initializer _ ih => exact .inferred initializer.2 ih
  | discard child _ ih => exact .discard child.2 ih
  | ifTrue condition _ ih => exact .ifTrue condition.2 ih
  | ifFalse condition _ ih => exact .ifFalse condition.2 ih
  | wordMatch scrutinee choice _ ih => exact .wordMatch scrutinee.2 choice ih

private theorem old_add {owner names environment initialStore body value finalStore}
    (evaluated : ComputationReturnTreeEvaluates LocalExpressionEvaluates owner names
      environment initialStore body value finalStore) :
    ClosedSourceDataBody body →
      ComputationReturnTreeEvaluates oldChild owner names environment initialStore body value finalStore := by
  induction evaluated with
  | bare => intro _; exact .bare
  | expression child =>
      intro gate; cases gate with
      | expression admitted => exact .expression ⟨admitted, child⟩
  | block _ ih =>
      intro gate; cases gate with
      | block admitted => exact .block (ih admitted)
  | binding initializer _ ih =>
      intro gate; cases gate with
      | binding admitted tail => exact .binding ⟨admitted, initializer⟩ (ih tail)
  | inferred initializer _ ih =>
      intro gate; cases gate with
      | binding admitted tail => exact .inferred ⟨admitted, initializer⟩ (ih tail)
  | discard child _ ih =>
      intro gate; cases gate with
      | discard admitted tail => exact .discard ⟨admitted, child⟩ (ih tail)
  | ifTrue condition _ ih =>
      intro gate; cases gate with
      | conditional admitted yes _ => exact .ifTrue ⟨admitted, condition⟩ (ih yes)
  | ifFalse condition _ ih =>
      intro gate; cases gate with
      | conditional admitted _ no => exact .ifFalse ⟨admitted, condition⟩ (ih no)
  | wordMatch scrutinee choice _ ih =>
      intro gate; cases gate with
      | wordMatch admitted branches fallback =>
          exact .wordMatch ⟨admitted, scrutinee⟩ choice
            (ih (selected_body_property (runtimeWordMatchChooses_ofCore_iff.mpr choice) branches fallback))

private theorem old_remove {owner names environment initialStore body value finalStore}
    (evaluated : ComputationReturnTreeEvaluates oldChild owner names environment
      initialStore body value finalStore) :
    ComputationReturnTreeEvaluates LocalExpressionEvaluates owner names environment
      initialStore body value finalStore := by
  induction evaluated with
  | bare => exact .bare
  | expression child => exact .expression child.2
  | block _ ih => exact .block ih
  | binding initializer _ ih => exact .binding initializer.2 ih
  | inferred initializer _ ih => exact .inferred initializer.2 ih
  | discard child _ ih => exact .discard child.2 ih
  | ifTrue condition _ ih => exact .ifTrue condition.2 ih
  | ifFalse condition _ ih => exact .ifFalse condition.2 ih
  | wordMatch scrutinee choice _ ih => exact .wordMatch scrutinee.2 choice ih

private theorem child_exact {owner names environment initialStore source actualValue actualFinal} :
    mixedChild owner names (environment.map (fun entry => (entry.1, RuntimeValue.ofCore entry.2)))
      (initialStore.map RuntimeValue.ofCore) source actualValue actualFinal ↔
    ∃ value finalStore, actualValue = RuntimeValue.ofCore value ∧
      actualFinal = finalStore.map RuntimeValue.ofCore ∧
      oldChild names environment initialStore source value finalStore := by
  constructor
  · rintro ⟨gate, evaluated⟩
    obtain ⟨value, finalStore, same, finalSame, old⟩ := gate.local_evaluates_iff.mp evaluated
    exact ⟨value, finalStore, same, finalSame, gate, old⟩
  · rintro ⟨value, finalStore, same, finalSame, gate, evaluated⟩
    exact ⟨gate, gate.local_evaluates_iff.mpr ⟨value, finalStore, same, finalSame, evaluated⟩⟩

/-- Original gated bodies have exactly the old generic-local actual image. -/
theorem ClosedSourceDataBody.local_evaluates_iff
    {owner : Resolved.DeclarationId} {names : LocalNameTable}
    {environment : Resolved.Environment} {initialStore : Core.Store}
    {body : Syntax.Block} {actualValue : RuntimeValue} {actualFinal : List RuntimeValue}
    (fragment : ClosedSourceDataBody body) :
    ClosedSourceBodyEvaluates owner names
      (environment.map (fun entry => (entry.1, RuntimeValue.ofCore entry.2)))
      (initialStore.map RuntimeValue.ofCore) body actualValue actualFinal ↔
    ∃ value finalStore,
      actualValue = RuntimeValue.ofCore value ∧
      actualFinal = finalStore.map RuntimeValue.ofCore ∧
      ComputationReturnTreeEvaluates LocalExpressionEvaluates owner names environment
        initialStore body value finalStore := by
  rw [closedSourceBodyEvaluates_iff]
  constructor
  · intro evaluated
    obtain ⟨value, finalStore, same, finalSame, old⟩ :=
      (sourceComputationBodyEvaluates_ofCore_inputs_iff child_exact).mp (mixed_add evaluated fragment)
    exact ⟨value, finalStore, same, finalSame, old_remove old⟩
  · rintro ⟨value, finalStore, same, finalSame, old⟩
    exact mixed_remove ((sourceComputationBodyEvaluates_ofCore_inputs_iff child_exact).mpr
      ⟨value, finalStore, same, finalSame, old_add old fragment⟩)

/-- Whole shared checking and exact ID alignment supply the stronger Core boundary. -/
theorem ClosedSourceDataBody.core_evaluates_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {environment : Resolved.Environment} {initialStore : Core.Store}
    {body : Syntax.Block} {actualValue : RuntimeValue} {actualFinal : List RuntimeValue}
    (fragment : ClosedSourceDataBody body)
    {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateComputationReturnTree? elaborateLocalExpression?
      types owner inputs body = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids inputs.context) :
    ClosedSourceBodyEvaluates owner inputs.names
      (environment.map (fun entry => (entry.1, RuntimeValue.ofCore entry.2)))
      (initialStore.map RuntimeValue.ofCore) body actualValue actualFinal ↔
    ∃ value finalStore,
      actualValue = RuntimeValue.ofCore value ∧
      actualFinal = finalStore.map RuntimeValue.ofCore ∧
      Core.Evaluates (Resolved.LocalScope.values environment) initialStore core value finalStore := by
  have elaboration := (elaborateComputationReturnTree?_iff
    (ChildElab := fun names context source core type =>
      elaborateLocalExpression? names context source = some (core, type)) (fun {_ _ _ _ _} => Iff.rfl)).mp accepted
  have correspondence {value finalStore} :
      ComputationReturnTreeEvaluates LocalExpressionEvaluates owner inputs.names environment
        initialStore body value finalStore ↔
      Core.Evaluates environment.values initialStore core value finalStore :=
    ComputationReturnTreeElaborates.evaluates_iff (ChildEval := LocalExpressionEvaluates)
      (F := Core.Expr.LocalFragment)
      elaborateLocalExpression?_localFragment Core.Expr.LocalFragment.weakenAt
      Core.Expr.LocalFragment.evaluates_insert_iff
      (fun checked aligned => elaborateLocalExpression?_evaluates_iff checked aligned) elaboration sameIds
  rw [fragment.local_evaluates_iff]
  constructor
  · rintro ⟨value, finalStore, same, finalSame, evaluated⟩
    exact ⟨value, finalStore, same, finalSame, correspondence.mp evaluated⟩
  · rintro ⟨value, finalStore, same, finalSame, evaluated⟩
    exact ⟨value, finalStore, same, finalSame, correspondence.mpr evaluated⟩

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.ClosedSourceEvaluationProperties`
-/

/- One joint induction closes expression determinism without opaque callback
laws. Body determinism is subsequently derived through exact compatibility. -/
set_option autoImplicit false
namespace Solcore.Frontend

/-- Successful expression value/store uniqueness by joint expression/body induction,
without an external child law, typing or termination assumption. -/
theorem ClosedSourceExpressionEvaluates.deterministic
    {owner names captured initialStore source left right leftStore rightStore}
    (first : ClosedSourceExpressionEvaluates owner names captured initialStore source left leftStore)
    (second : ClosedSourceExpressionEvaluates owner names captured initialStore source right rightStore) :
    left = right ∧ leftStore = rightStore := by
  induction first using ClosedSourceExpressionEvaluates.rec
    (motive_2 := fun owner names captured store source value finalStore _ =>
      ∀ {right rightStore}, ClosedSourceBodyEvaluates owner names captured store source right rightStore →
        value = right ∧ finalStore = rightStore) generalizing right rightStore with
  | reference named found =>
      cases second with
      | reference otherNamed otherFound =>
          cases named.id_unique otherNamed
          exact ⟨found.value_unique otherFound, rfl⟩
      | creation shape => cases shape
  | unit =>
      cases second with
      | unit => exact ⟨rfl, rfl⟩
      | creation shape => cases shape
  | wordLiteral meaning =>
      cases second with
      | wordLiteral otherMeaning =>
          cases meaning.value_unique otherMeaning
          exact ⟨rfl, rfl⟩
      | creation shape => cases shape
  | group _ ih =>
      cases second with
      | group child => exact ih child
      | creation shape => cases shape
  | pair _ _ leftIH rightIH =>
      cases second with
      | pair otherLeft otherRight =>
          obtain ⟨rfl, rfl⟩ := leftIH otherLeft
          obtain ⟨rfl, rfl⟩ := rightIH otherRight
          exact ⟨rfl, rfl⟩
      | creation shape => cases shape
  | many _ _ headIH tailIH =>
      cases second with
      | many otherHead otherTail =>
          obtain ⟨rfl, rfl⟩ := headIH otherHead
          obtain ⟨rfl, rfl⟩ := tailIH otherTail
          exact ⟨rfl, rfl⟩
      | creation shape => cases shape
  | creation shape =>
      cases shape <;> cases second with
      | creation _ => exact ⟨rfl, rfl⟩
  | call shape _ _ _ calleeIH argumentIH bodyIH =>
      cases second with
      | creation shape => cases shape
      | call otherShape otherCallee otherArgument otherBody =>
          obtain ⟨sameCallee, sameStore⟩ := calleeIH otherCallee
          cases sameCallee
          cases sameStore
          obtain ⟨rfl, rfl⟩ := argumentIH otherArgument
          have sameShape := Prod.mk.inj (Option.some.inj
            ((sourceUnaryLambdaShape?_iff.mpr shape).symm.trans
              (sourceUnaryLambdaShape?_iff.mpr otherShape)))
          obtain ⟨rfl, rfl⟩ := sameShape
          exact bodyIH otherBody
  | conditionalTrue _ _ conditionIH branchIH =>
      cases second with
      | creation shape => cases shape
      | conditionalTrue otherCondition otherBranch =>
          obtain ⟨_, rfl⟩ := conditionIH otherCondition
          exact branchIH otherBranch
      | conditionalFalse otherCondition _ => cases (conditionIH otherCondition).1
  | conditionalFalse _ _ conditionIH branchIH =>
      cases second with
      | creation shape => cases shape
      | conditionalTrue otherCondition _ => cases (conditionIH otherCondition).1
      | conditionalFalse otherCondition otherBranch =>
          obtain ⟨_, rfl⟩ := conditionIH otherCondition
          exact branchIH otherBranch
  | logicalNot _ ih =>
      cases second with
      | creation shape => cases shape
      | logicalNot child =>
          obtain ⟨same, sameStore⟩ := ih child
          cases RuntimeValue.bool.inj same
          cases sameStore
          exact ⟨rfl, rfl⟩
  | bitNot _ ih =>
      cases second with
      | creation shape => cases shape
      | bitNot child =>
          obtain ⟨same, sameStore⟩ := ih child
          cases RuntimeValue.word.inj same
          cases sameStore
          exact ⟨rfl, rfl⟩
  | andTrue _ _ leftIH rightIH =>
      cases second with
      | creation shape => cases shape
      | andTrue otherLeft otherRight =>
          obtain ⟨_, rfl⟩ := leftIH otherLeft
          exact rightIH otherRight
      | andFalse otherLeft => cases (leftIH otherLeft).1
      | strictWordBinary otherLeft _ _ => cases (leftIH otherLeft).1
  | andFalse _ leftIH =>
      cases second with
      | creation shape => cases shape
      | andTrue otherLeft _ => cases (leftIH otherLeft).1
      | andFalse otherLeft => exact leftIH otherLeft
      | strictWordBinary otherLeft _ _ => cases (leftIH otherLeft).1
  | orTrue _ leftIH =>
      cases second with
      | creation shape => cases shape
      | orTrue otherLeft => exact leftIH otherLeft
      | orFalse otherLeft _ => cases (leftIH otherLeft).1
      | strictWordBinary otherLeft _ _ => cases (leftIH otherLeft).1
  | orFalse _ _ leftIH rightIH =>
      cases second with
      | creation shape => cases shape
      | orTrue otherLeft => cases (leftIH otherLeft).1
      | orFalse otherLeft otherRight =>
          obtain ⟨_, rfl⟩ := leftIH otherLeft
          exact rightIH otherRight
      | strictWordBinary otherLeft _ _ => cases (leftIH otherLeft).1
  | strictWordBinary _ _ meaning leftIH rightIH =>
      cases second with
      | creation shape => cases shape
      | andTrue otherLeft _ => cases (leftIH otherLeft).1
      | andFalse otherLeft => cases (leftIH otherLeft).1
      | orTrue otherLeft => cases (leftIH otherLeft).1
      | orFalse otherLeft _ => cases (leftIH otherLeft).1
      | strictWordBinary otherLeft otherRight otherMeaning =>
          obtain ⟨sameLeft, rfl⟩ := leftIH otherLeft
          cases RuntimeValue.word.inj sameLeft
          obtain ⟨sameRight, rfl⟩ := rightIH otherRight
          cases RuntimeValue.word.inj sameRight
          cases meaning.value_unique otherMeaning
          exact ⟨rfl, rfl⟩
  | bare =>
      rename_i right rightStore other
      cases other
      exact ⟨rfl, rfl⟩
  | expression _ ih =>
      rename_i right rightStore other
      cases other with
      | expression otherChild => exact ih otherChild
  | block _ ih =>
      rename_i right rightStore other
      cases other with
      | block otherBody => exact ih otherBody
  | binding _ _ initializerIH tailIH =>
      rename_i right rightStore other
      cases other with
      | binding otherInitializer otherTail =>
          obtain ⟨rfl, rfl⟩ := initializerIH otherInitializer
          exact tailIH otherTail
  | inferred _ _ initializerIH tailIH =>
      rename_i right rightStore other
      cases other with
      | inferred otherInitializer otherTail =>
          obtain ⟨rfl, rfl⟩ := initializerIH otherInitializer
          exact tailIH otherTail
  | discard _ _ expressionIH tailIH =>
      rename_i right rightStore other
      cases other with
      | discard otherExpression otherTail =>
          obtain ⟨_, rfl⟩ := expressionIH otherExpression
          exact tailIH otherTail
  | ifTrue _ _ conditionIH branchIH =>
      rename_i right rightStore other
      cases other with
      | ifTrue otherCondition otherBranch =>
          obtain ⟨_, rfl⟩ := conditionIH otherCondition
          exact branchIH otherBranch
      | ifFalse otherCondition _ => cases (conditionIH otherCondition).1
  | ifFalse _ _ conditionIH branchIH =>
      rename_i right rightStore other
      cases other with
      | ifTrue otherCondition _ => cases (conditionIH otherCondition).1
      | ifFalse otherCondition otherBranch =>
          obtain ⟨_, rfl⟩ := conditionIH otherCondition
          exact branchIH otherBranch
  | wordMatch _ choice _ scrutineeIH branchIH =>
      rename_i right rightStore other
      cases other with
      | wordMatch otherScrutinee otherChoice otherBranch =>
          obtain ⟨rfl, rfl⟩ := scrutineeIH otherScrutinee
          obtain ⟨rfl, rfl⟩ := choice.deterministic otherChoice
          exact branchIH otherBranch

/-- Body uniqueness derived from exact compatibility and closed child determinism. -/
theorem ClosedSourceBodyEvaluates.deterministic
    {owner names captured initialStore source left right leftStore rightStore}
    (first : ClosedSourceBodyEvaluates owner names captured initialStore source left leftStore)
    (second : ClosedSourceBodyEvaluates owner names captured initialStore source right rightStore) :
    left = right ∧ leftStore = rightStore :=
  SourceComputationBodyEvaluates.deterministic ClosedSourceExpressionEvaluates.deterministic
    (closedSourceBodyEvaluates_iff.mp first) (closedSourceBodyEvaluates_iff.mp second)

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.ClosedSourceEvaluator`
-/

/- Depth-bounded closed original fragment. Zero rejects even leaves; each child
gets the same predecessor. None does not distinguish unsupported paths, missing
values or exhausted depth. Stores and saved lexical fields remain literal. -/

set_option autoImplicit false
namespace Solcore.Frontend

mutual

/-- Search the closed original expression fragment up to a derivation-depth bound. -/
def evaluateClosedSourceExpression? (budget : Nat) (owner : Resolved.DeclarationId)
    (names : LocalNameTable) (captured : Resolved.LocalScope RuntimeValue)
    (store : List RuntimeValue) (source : Syntax.Expr) :
    Option (RuntimeValue × List RuntimeValue) :=
  match budget with
  | 0 => none
  | n + 1 =>
      match source with
      | ⟨_, .identifier name⟩ => do
          let id ← names.lookup? name.value
          let value ← captured.lookup? id
          return (value, store)
      | ⟨_, .literal literal⟩ => do
          return (.word (← interpretWordLiteral? literal), store)
      | ⟨_, .group inner⟩ => evaluateClosedSourceExpression? n owner names captured store inner
      | ⟨_, .tuple ⟨_, []⟩⟩ => some (.unit, store)
      | ⟨_, .tuple ⟨_, [left, right]⟩⟩ => do
          let (leftValue, middleStore) ← evaluateClosedSourceExpression? n owner names captured store left
          let (rightValue, finalStore) ← evaluateClosedSourceExpression? n owner names captured middleStore right
          return (.pair leftValue rightValue, finalStore)
      | ⟨span, .tuple ⟨tupleSpan, first :: second :: third :: rest⟩⟩ => do
          let (headValue, middleStore) ← evaluateClosedSourceExpression? n owner names captured store first
          let (tailValue, finalStore) ← evaluateClosedSourceExpression? n owner names captured middleStore
            ⟨span, .tuple ⟨tupleSpan, second :: third :: rest⟩⟩
          return (.pair headValue tailValue, finalStore)
      | ⟨_, .conditional condition _ thenBranch _ elseBranch⟩ => do
          let (.bool choice, middleStore) ← evaluateClosedSourceExpression? n owner names captured store condition | none
          evaluateClosedSourceExpression? n owner names captured middleStore
            (if choice then thenBranch else elseBranch)
      | ⟨_, .call callee ⟨_, [argument]⟩⟩ => do
          let (function, calleeStore) ← evaluateClosedSourceExpression? n owner names captured store callee
          let (argumentValue, argumentStore) ← evaluateClosedSourceExpression? n owner names captured calleeStore argument
          let .sourceClosure saved savedOwner savedNames savedCaptured := function | none
          let (name, body) ← sourceUnaryLambdaShape? saved
          let id := Resolved.freshLocalId savedOwner (savedNames.map Prod.snd)
          evaluateClosedSourceBody? n savedOwner ((name.value, id) :: savedNames)
            ((id, argumentValue) :: savedCaptured) argumentStore body
      | ⟨_, .unary ⟨_, .logicalNot⟩ operand⟩ => do
          let (.bool value, finalStore) ←
            evaluateClosedSourceExpression? n owner names captured store operand | none
          return (.bool (!value), finalStore)
      | ⟨_, .unary ⟨_, .bitNot⟩ operand⟩ => do
          let (.word value, finalStore) ←
            evaluateClosedSourceExpression? n owner names captured store operand | none
          return (.word value.bitNot, finalStore)
      | ⟨_, .binary left ⟨_, .logicalAnd⟩ right⟩ => do
          let (.bool choice, middleStore) ← evaluateClosedSourceExpression? n owner names captured store left | none
          if choice then evaluateClosedSourceExpression? n owner names captured middleStore right
          else return (.bool false, middleStore)
      | ⟨_, .binary left ⟨_, .logicalOr⟩ right⟩ => do
          let (.bool choice, middleStore) ← evaluateClosedSourceExpression? n owner names captured store left | none
          if choice then return (.bool true, middleStore)
          else evaluateClosedSourceExpression? n owner names captured middleStore right
      | ⟨_, .binary left ⟨_, operator⟩ right⟩ => do
          let (.word leftWord, middleStore) ←
            evaluateClosedSourceExpression? n owner names captured store left | none
          let (.word rightWord, finalStore) ←
            evaluateClosedSourceExpression? n owner names captured middleStore right | none
          let result ← evaluateStrictWordBinary? operator leftWord rightWord
          return (RuntimeValue.ofCore result, finalStore)
      | _ => do
          let _ ← sourceUnaryLambdaShape? source
          return (.sourceClosure source owner names captured, store)
termination_by budget

/-- Search original body rules with the same predecessor bound for every child. -/
def evaluateClosedSourceBody? (budget : Nat) (owner : Resolved.DeclarationId)
    (names : LocalNameTable) (captured : Resolved.LocalScope RuntimeValue)
    (store : List RuntimeValue) (source : Syntax.Block) :
    Option (RuntimeValue × List RuntimeValue) :=
  match budget with
  | 0 => none
  | n + 1 =>
      match source with
      | ⟨_, [⟨_, .returnStmt none⟩]⟩ => some (.unit, store)
      | ⟨_, [⟨_, .returnStmt (some child)⟩]⟩ =>
          evaluateClosedSourceExpression? n owner names captured store child
      | ⟨_, [⟨innerSpan, .block statements⟩]⟩ =>
          evaluateClosedSourceBody? n owner names captured store ⟨innerSpan, statements⟩
      | ⟨blockSpan, ⟨_, .letDecl name _ (some initializer)⟩ :: rest⟩ => do
          let (boundValue, middleStore) ← evaluateClosedSourceExpression? n owner names captured store initializer
          let id := Resolved.freshLocalId owner (names.map Prod.snd)
          evaluateClosedSourceBody? n owner ((name.value, id) :: names)
            ((id, boundValue) :: captured) middleStore ⟨blockSpan, rest⟩
      | ⟨blockSpan, ⟨_, .expression child true⟩ :: rest⟩ => do
          let (_, middleStore) ← evaluateClosedSourceExpression? n owner names captured store child
          evaluateClosedSourceBody? n owner names captured middleStore ⟨blockSpan, rest⟩
      | ⟨_, [⟨_, .ifThen condition thenBody (some elseBody)⟩]⟩ => do
          let (.bool choice, middleStore) ← evaluateClosedSourceExpression? n owner names captured store condition | none
          if choice then evaluateClosedSourceBody? n owner names captured middleStore thenBody
          else evaluateClosedSourceBody? n owner names captured middleStore elseBody
      | ⟨_, [⟨_, .matchWith ⟨_, ⟨scrutinee, []⟩⟩ ⟨_, ⟨cases, defaultBody⟩⟩⟩]⟩ => do
          let (actual, middleStore) ← evaluateClosedSourceExpression? n owner names captured store scrutinee
          let (selected, _) ← chooseRuntimeWordMatch? actual cases defaultBody
          evaluateClosedSourceBody? n owner names captured middleStore selected
      | _ => none
termination_by budget

end

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.ClosedSourceConditionalProperties`
-/

/- Exact original conditional decomposition and successor-depth computation.
Only the selected original branch is evaluated, under the unchanged lexical rows. -/
set_option autoImplicit false
namespace Solcore.Frontend

/-- An original conditional evaluates exactly its actual Bool-selected branch. -/
theorem closedSourceExpressionEvaluates_conditional_iff
    {owner : Resolved.DeclarationId} {names : LocalNameTable}
    {captured : Resolved.LocalScope RuntimeValue}
    {initialStore finalStore : List RuntimeValue}
    {span question colon : Syntax.SourceSpan}
    {condition thenBranch elseBranch : Syntax.Expr} {value : RuntimeValue} :
    ClosedSourceExpressionEvaluates owner names captured initialStore
      ⟨span, .conditional condition question thenBranch colon elseBranch⟩ value finalStore ↔
    ∃ (choice : Bool) (middleStore : List RuntimeValue),
      ClosedSourceExpressionEvaluates owner names captured initialStore
        condition (.bool choice) middleStore ∧
      ClosedSourceExpressionEvaluates owner names captured middleStore
        (if choice then thenBranch else elseBranch) value finalStore := by
  constructor
  · intro evaluated
    cases evaluated with
    | creation shape => cases shape
    | conditionalTrue condition branch => exact ⟨true, _, condition, branch⟩
    | conditionalFalse condition branch => exact ⟨false, _, condition, branch⟩
  · rintro ⟨choice, middleStore, condition, branch⟩
    cases choice
    · exact .conditionalFalse condition branch
    · exact .conditionalTrue condition branch

/-- The guard and selected original branch share the same predecessor depth. -/
theorem evaluateClosedSourceExpression?_conditional
    (budget : Nat) (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (initialStore : List RuntimeValue)
    (span question colon : Syntax.SourceSpan)
    (condition thenBranch elseBranch : Syntax.Expr) :
    evaluateClosedSourceExpression? (budget + 1) owner names captured initialStore
      ⟨span, .conditional condition question thenBranch colon elseBranch⟩ =
    (do
      let (.bool choice, middleStore) ←
        evaluateClosedSourceExpression? budget owner names captured initialStore condition | none
      evaluateClosedSourceExpression? budget owner names captured middleStore
        (if choice then thenBranch else elseBranch)) := by
  rw [evaluateClosedSourceExpression?]

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.ClosedSourceDataDepthBoundProperties`
-/

/- Syntax induction bounds every original data derivation directly.
No resolution, runtime typing, successful lookup or embedded-input premise is added.
Every original intermediate store and actual returned mixed value stays literal. -/
set_option autoImplicit false
namespace Solcore.Frontend

/-- The syntax-only data bound finds every original successful derivation,
including its actual value and complete final store, at every larger budget. -/
theorem ClosedSourceDataExpression.evaluates_at_depthBound
    {source : Syntax.Expr} (fragment : ClosedSourceDataExpression source)
    {owner : Resolved.DeclarationId} {names : LocalNameTable}
    {captured : Resolved.LocalScope RuntimeValue}
    {initialStore finalStore : List RuntimeValue} {value : RuntimeValue}
    (evaluated : ClosedSourceExpressionEvaluates owner names captured
      initialStore source value finalStore)
    {budget : Nat} (enough : closedSourceDataDepthBound source ≤ budget) :
    evaluateClosedSourceExpression? budget owner names captured initialStore source =
      some (value, finalStore) := by
  induction fragment generalizing initialStore finalStore value budget with
  | reference =>
      rw [closedSourceDataDepthBound] at enough
      cases budget with
      | zero => omega
      | succ n =>
          cases evaluated with
          | reference named found =>
              simp only [evaluateClosedSourceExpression?, LocalNameTable.lookup?_iff.mpr named,
                Resolved.LocalScope.lookup?_iff.mpr found, bind, Option.bind_some, pure]
          | creation shape => cases shape
  | literal =>
      rw [closedSourceDataDepthBound] at enough
      cases budget with
      | zero => omega
      | succ n =>
          cases evaluated with
          | wordLiteral meaning =>
              simp only [evaluateClosedSourceExpression?, interpretWordLiteral?_complete meaning,
                bind, Option.bind_some, pure]
          | creation shape => cases shape
  | unit =>
      rw [closedSourceDataDepthBound] at enough
      cases budget with
      | zero => omega
      | succ n =>
          cases evaluated with
          | unit => simp only [evaluateClosedSourceExpression?]
          | creation shape => cases shape
  | group _ ih =>
      rw [closedSourceDataDepthBound] at enough
      cases budget with
      | zero => omega
      | succ n =>
          cases evaluated with
          | group child =>
              simpa only [evaluateClosedSourceExpression?] using ih child (by omega : _ ≤ n)
          | creation shape => cases shape
  | pair _ _ leftIH rightIH =>
      rw [closedSourceDataDepthBound] at enough
      cases budget with
      | zero => omega
      | succ n =>
          cases evaluated with
          | pair left right =>
              have leftResult := leftIH left (by omega : _ ≤ n)
              have rightResult := rightIH right (by omega : _ ≤ n)
              simp only [evaluateClosedSourceExpression?, leftResult, rightResult,
                bind, Option.bind_some, pure]
          | creation shape => cases shape
  | many _ _ headIH tailIH =>
      rw [closedSourceDataDepthBound] at enough
      cases budget with
      | zero => omega
      | succ n =>
          cases evaluated with
          | many head tail =>
              have headResult := headIH head (by omega : _ ≤ n)
              have tailResult := tailIH tail (by omega : _ ≤ n)
              simp only [evaluateClosedSourceExpression?, headResult, tailResult,
                bind, Option.bind_some, pure]
          | creation shape => cases shape
  | conditional _ _ _ conditionIH thenIH elseIH =>
      rw [closedSourceDataDepthBound] at enough
      cases budget with
      | zero => omega
      | succ n =>
          cases evaluated with
          | conditionalTrue condition branch =>
              have conditionResult := conditionIH condition (by omega : _ ≤ n)
              simpa only [evaluateClosedSourceExpression?, conditionResult,
                bind, Option.bind_some, ↓reduceIte] using thenIH branch (by omega : _ ≤ n)
          | conditionalFalse condition branch =>
              have conditionResult := conditionIH condition (by omega : _ ≤ n)
              simpa only [evaluateClosedSourceExpression?, conditionResult, bind,
                Option.bind_some, Bool.false_eq_true, ↓reduceIte] using elseIH branch (by omega : _ ≤ n)
          | creation shape => cases shape
  | logicalNot _ ih =>
      rw [closedSourceDataDepthBound] at enough
      cases budget with
      | zero => omega
      | succ n =>
          cases evaluated with
          | logicalNot child =>
              simp only [evaluateClosedSourceExpression?, ih child (by omega : _ ≤ n),
                bind, Option.bind_some, pure]
          | creation shape => cases shape
  | bitNot _ ih =>
      rw [closedSourceDataDepthBound] at enough
      cases budget with
      | zero => omega
      | succ n =>
          cases evaluated with
          | bitNot child =>
              simp only [evaluateClosedSourceExpression?, ih child (by omega : _ ≤ n),
                bind, Option.bind_some, pure]
          | creation shape => cases shape
  | logicalAnd _ _ leftIH rightIH =>
      rw [closedSourceDataDepthBound] at enough
      cases budget with
      | zero => omega
      | succ n =>
          cases evaluated with
          | andTrue left right =>
              have leftResult := leftIH left (by omega : _ ≤ n)
              simpa only [evaluateClosedSourceExpression?, leftResult,
                bind, Option.bind_some, ↓reduceIte] using rightIH right (by omega : _ ≤ n)
          | andFalse left =>
              simp only [evaluateClosedSourceExpression?, leftIH left (by omega : _ ≤ n),
                bind, Option.bind_some, Bool.false_eq_true, ↓reduceIte, pure]
          | strictWordBinary _ _ meaning => cases meaning
          | creation shape => cases shape
  | logicalOr _ _ leftIH rightIH =>
      rw [closedSourceDataDepthBound] at enough
      cases budget with
      | zero => omega
      | succ n =>
          cases evaluated with
          | orTrue left =>
              simp only [evaluateClosedSourceExpression?, leftIH left (by omega : _ ≤ n),
                bind, Option.bind_some, ↓reduceIte, pure]
          | orFalse left right =>
              have leftResult := leftIH left (by omega : _ ≤ n)
              simpa only [evaluateClosedSourceExpression?, leftResult, bind,
                Option.bind_some, Bool.false_eq_true, ↓reduceIte] using rightIH right (by omega : _ ≤ n)
          | strictWordBinary _ _ meaning => cases meaning
          | creation shape => cases shape
  | strictWordBinary _ _ notAnd notOr leftIH rightIH =>
      rw [closedSourceDataDepthBound] at enough
      cases budget with
      | zero => omega
      | succ n =>
          cases evaluated with
          | strictWordBinary left right meaning =>
              have leftResult := leftIH left (by omega : _ ≤ n)
              have rightResult := rightIH right (by omega : _ ≤ n)
              cases meaning <;>
                simp only [evaluateClosedSourceExpression?, leftResult, rightResult,
                  evaluateStrictWordBinary?, bind, Option.bind_some, pure]
          | andTrue _ _ => exact False.elim (notAnd rfl)
          | andFalse _ => exact False.elim (notAnd rfl)
          | orTrue _ => exact False.elim (notOr rfl)
          | orFalse _ _ => exact False.elim (notOr rfl)
          | creation shape => cases shape

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.ClosedSourceDataBodyDepthProperties`
-/

/- Direct syntax induction retains original body derivations and all mixed
lexical/store endpoints. Fresh binding changes the induction inputs literally.
Written-arm maxima bound selection, not the number of visited comparisons. -/
set_option autoImplicit false
namespace Solcore.Frontend

private theorem selected_depth_property {actual : RuntimeValue} {cases : List Syntax.MatchCase}
    {defaultBody : Option Syntax.Block} {selected : Syntax.Block} {tests : Nat}
    (choice : RuntimeWordMatchChooses actual cases defaultBody selected tests)
    {P : Syntax.Block → Prop} (branches : ∀ arm ∈ cases, P arm.value.body)
    (fallback : ∀ source ∈ defaultBody.toList, P source) : P selected := by
  induction choice with
  | fallback => exact fallback _ (by simp)
  | wildcard _ => exact branches _ List.mem_cons_self
  | hit _ => exact branches _ List.mem_cons_self
  | miss _ _ _ ih => exact ih (fun arm member => branches arm (List.mem_cons_of_mem _ member)) fallback

private theorem selected_depth_le {actual : RuntimeValue} {cases : List Syntax.MatchCase}
    {defaultBody : Option Syntax.Block} {selected : Syntax.Block} {tests : Nat}
    (choice : RuntimeWordMatchChooses actual cases defaultBody selected tests) :
    closedSourceDataBodyDepthBound selected ≤ closedSourceDataMatchDepthBound cases defaultBody := by
  induction choice with
  | fallback => rw [closedSourceDataMatchDepthBound]; exact Nat.le_refl _
  | wildcard _ => rw [closedSourceDataMatchDepthBound]; exact Nat.le_max_left _ _
  | hit _ => rw [closedSourceDataMatchDepthBound]; exact Nat.le_max_left _ _
  | miss _ _ _ ih =>
      rw [closedSourceDataMatchDepthBound]
      exact Nat.le_trans ih (Nat.le_max_right _ _)

/-- Every original successful gated body derivation is found at its syntax-only
upper depth and every larger budget, with the complete actual result and store. -/
theorem ClosedSourceDataBody.evaluates_at_depthBound
    {body : Syntax.Block} (fragment : ClosedSourceDataBody body)
    {owner : Resolved.DeclarationId} {names : LocalNameTable}
    {captured : Resolved.LocalScope RuntimeValue}
    {initialStore finalStore : List RuntimeValue} {value : RuntimeValue}
    (evaluated : ClosedSourceBodyEvaluates owner names captured
      initialStore body value finalStore)
    {budget : Nat} (enough : closedSourceDataBodyDepthBound body ≤ budget) :
    evaluateClosedSourceBody? budget owner names captured initialStore body =
      some (value, finalStore) := by
  induction fragment generalizing owner names captured initialStore finalStore value budget with
  | bare =>
      rw [closedSourceDataBodyDepthBound] at enough
      cases budget with
      | zero => omega
      | succ n =>
          cases evaluated with
          | bare => simp only [evaluateClosedSourceBody?]
  | expression admitted =>
      rw [closedSourceDataBodyDepthBound] at enough
      cases budget with
      | zero => omega
      | succ n =>
          cases evaluated with
          | expression child =>
              simpa only [evaluateClosedSourceBody?] using
                admitted.evaluates_at_depthBound child (by omega : _ ≤ n)
  | block _ ih =>
      rw [closedSourceDataBodyDepthBound] at enough
      cases budget with
      | zero => omega
      | succ n =>
          cases evaluated with
          | block child =>
              simpa only [evaluateClosedSourceBody?] using ih child (by omega : _ ≤ n)
  | binding admitted _ ih =>
      rw [closedSourceDataBodyDepthBound] at enough
      cases budget with
      | zero => omega
      | succ n =>
          cases evaluated with
          | binding initializer tail =>
              have initialized := admitted.evaluates_at_depthBound initializer (by omega : _ ≤ n)
              simpa only [evaluateClosedSourceBody?, initialized, bind, Option.bind_some] using
                ih tail (by omega : _ ≤ n)
          | inferred initializer tail =>
              have initialized := admitted.evaluates_at_depthBound initializer (by omega : _ ≤ n)
              simpa only [evaluateClosedSourceBody?, initialized, bind, Option.bind_some] using
                ih tail (by omega : _ ≤ n)
  | discard admitted _ ih =>
      rw [closedSourceDataBodyDepthBound] at enough
      cases budget with
      | zero => omega
      | succ n =>
          cases evaluated with
          | discard child tail =>
              have discarded := admitted.evaluates_at_depthBound child (by omega : _ ≤ n)
              simpa only [evaluateClosedSourceBody?, discarded, bind, Option.bind_some] using
                ih tail (by omega : _ ≤ n)
  | conditional admitted _ _ thenIH elseIH =>
      rw [closedSourceDataBodyDepthBound] at enough
      cases budget with
      | zero => omega
      | succ n =>
          cases evaluated with
          | ifTrue condition branch =>
              have tested := admitted.evaluates_at_depthBound condition (by omega : _ ≤ n)
              simpa only [evaluateClosedSourceBody?, tested, bind, Option.bind_some, ↓reduceIte] using
                thenIH branch (by omega : _ ≤ n)
          | ifFalse condition branch =>
              have tested := admitted.evaluates_at_depthBound condition (by omega : _ ≤ n)
              simpa only [evaluateClosedSourceBody?, tested, bind, Option.bind_some,
                Bool.false_eq_true, ↓reduceIte] using elseIH branch (by omega : _ ≤ n)
  | wordMatch admitted _ _ branchesIH fallbackIH =>
      rw [closedSourceDataBodyDepthBound] at enough
      cases budget with
      | zero => omega
      | succ n =>
          cases evaluated with
          | wordMatch scrutinee choice branch =>
              have tested := admitted.evaluates_at_depthBound scrutinee (by omega : _ ≤ n)
              have selectedBound := selected_depth_le choice
              have returned := selected_depth_property choice
                (P := fun body => ∀ {scopeOwner : Resolved.DeclarationId} {scopeNames : LocalNameTable}
                  {scopeCaptured : Resolved.LocalScope RuntimeValue}
                  {initial final : List RuntimeValue} {actual : RuntimeValue},
                  ClosedSourceBodyEvaluates scopeOwner scopeNames scopeCaptured initial body actual final →
                  ∀ {depth : Nat}, closedSourceDataBodyDepthBound body ≤ depth →
                  evaluateClosedSourceBody? depth scopeOwner scopeNames scopeCaptured initial body =
                    some (actual, final))
                (fun arm member => @branchesIH arm member)
                (fun source member => @fallbackIH source member) branch (by omega : _ ≤ n)
              simpa only [evaluateClosedSourceBody?, tested, chooseRuntimeWordMatch?_iff.mpr choice,
                bind, Option.bind_some] using returned

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.ClosedSourceEvaluatorCompletenessProperties`
-/

/- Every finite derivation is found at all sufficiently large depths. The bound
depends on the derivation, not source size; no termination or step-cost claim. -/

set_option autoImplicit false
namespace Solcore.Frontend

private theorem eventually_step {P : Nat → Prop} (threshold : Nat)
    (step : ∀ n, threshold ≤ n → P (n + 1)) :
    ∃ required, ∀ budget, required ≤ budget → P budget := by
  refine ⟨threshold + 1, ?_⟩
  intro budget large
  cases budget with
  | zero => omega
  | succ n => exact step n (by omega)

/-- Every finite expression derivation is found at all sufficiently large depths. -/
theorem evaluateClosedSourceExpression?_eventually_complete
    {owner names captured initialStore source value finalStore}
    (evaluated : ClosedSourceExpressionEvaluates owner names captured initialStore source value finalStore) :
    ∃ required, ∀ budget, required ≤ budget →
      evaluateClosedSourceExpression? budget owner names captured initialStore source = some (value, finalStore) := by
  induction evaluated using ClosedSourceExpressionEvaluates.rec
    (motive_2 := fun owner names captured store source value finalStore _ =>
      ∃ required, ∀ budget, required ≤ budget →
        evaluateClosedSourceBody? budget owner names captured store source = some (value, finalStore)) with
  | reference named found =>
      apply eventually_step 0
      intro n _
      simp only [evaluateClosedSourceExpression?, LocalNameTable.lookup?_iff.mpr named,
        Resolved.LocalScope.lookup?_iff.mpr found, bind, Option.bind_some, pure]
  | unit =>
      apply eventually_step 0
      intro n _
      simp only [evaluateClosedSourceExpression?]
  | wordLiteral meaning =>
      apply eventually_step 0
      intro n _
      simp only [evaluateClosedSourceExpression?, interpretWordLiteral?_complete meaning,
        bind, Option.bind_some, pure]
  | group _ ih =>
      obtain ⟨k, ih⟩ := ih
      apply eventually_step k
      intro n large
      simpa only [evaluateClosedSourceExpression?] using ih n large
  | pair _ _ leftIH rightIH | many _ _ leftIH rightIH =>
      obtain ⟨l, leftIH⟩ := leftIH
      obtain ⟨r, rightIH⟩ := rightIH
      apply eventually_step (max l r)
      intro n large
      have left := leftIH n (by omega)
      have right := rightIH n (by omega)
      simp only [evaluateClosedSourceExpression?, left, right, bind, Option.bind_some, pure]
  | creation shape =>
      cases shape <;> apply eventually_step 0 <;> intro n _ <;>
        simp only [evaluateClosedSourceExpression?, sourceUnaryLambdaShape?, bind, Option.bind_some, pure]
  | call shape _ _ _ calleeIH argumentIH bodyIH =>
      obtain ⟨f, calleeIH⟩ := calleeIH
      obtain ⟨a, argumentIH⟩ := argumentIH
      obtain ⟨b, bodyIH⟩ := bodyIH
      apply eventually_step (max f (max a b))
      intro n large
      have callee := calleeIH n (by omega)
      have argument := argumentIH n (by omega)
      have body := bodyIH n (by omega)
      simpa only [evaluateClosedSourceExpression?, callee, argument,
        sourceUnaryLambdaShape?_iff.mpr shape, bind, Option.bind_some] using body
  | conditionalTrue _ _ conditionIH branchIH | conditionalFalse _ _ conditionIH branchIH =>
      obtain ⟨c, conditionIH⟩ := conditionIH
      obtain ⟨b, branchIH⟩ := branchIH
      apply eventually_step (max c b)
      intro n large
      have condition := conditionIH n (by omega)
      have branch := branchIH n (by omega)
      simpa only [evaluateClosedSourceExpression?, condition, bind, Option.bind_some,
        Bool.false_eq_true, ↓reduceIte] using branch
  | logicalNot _ ih | bitNot _ ih =>
      obtain ⟨k, ih⟩ := ih
      apply eventually_step k
      intro n large
      simp only [evaluateClosedSourceExpression?, ih n large, bind, Option.bind_some, pure]
  | andTrue _ _ leftIH rightIH | orFalse _ _ leftIH rightIH =>
      obtain ⟨l, leftIH⟩ := leftIH
      obtain ⟨r, rightIH⟩ := rightIH
      apply eventually_step (max l r)
      intro n large
      have left := leftIH n (by omega)
      have right := rightIH n (by omega)
      simpa only [evaluateClosedSourceExpression?, left, bind, Option.bind_some,
        Bool.false_eq_true, ↓reduceIte] using right
  | andFalse _ leftIH | orTrue _ leftIH =>
      obtain ⟨l, leftIH⟩ := leftIH
      apply eventually_step l
      intro n large
      simp only [evaluateClosedSourceExpression?, leftIH n large, bind, Option.bind_some,
        Bool.false_eq_true, ↓reduceIte, pure]
  | strictWordBinary _ _ meaning leftIH rightIH =>
      obtain ⟨l, leftIH⟩ := leftIH
      obtain ⟨r, rightIH⟩ := rightIH
      apply eventually_step (max l r)
      intro n large
      have left := leftIH n (by omega)
      have right := rightIH n (by omega)
      cases meaning <;>
        simp only [evaluateClosedSourceExpression?, left, right, evaluateStrictWordBinary?,
          bind, Option.bind_some, pure]
  | bare =>
      apply eventually_step 0
      intro n _
      simp only [evaluateClosedSourceBody?]
  | expression _ ih =>
      obtain ⟨k, ih⟩ := ih
      apply eventually_step k
      intro n large
      simpa only [evaluateClosedSourceBody?] using ih n large
  | block _ ih =>
      obtain ⟨k, ih⟩ := ih
      apply eventually_step k
      intro n large
      simpa only [evaluateClosedSourceBody?] using ih n large
  | binding _ _ initializerIH tailIH | inferred _ _ initializerIH tailIH
  | discard _ _ initializerIH tailIH | ifTrue _ _ initializerIH tailIH | ifFalse _ _ initializerIH tailIH =>
      obtain ⟨i, initializerIH⟩ := initializerIH
      obtain ⟨t, tailIH⟩ := tailIH
      apply eventually_step (max i t)
      intro n large
      have initializer := initializerIH n (by omega)
      have tail := tailIH n (by omega)
      simpa only [evaluateClosedSourceBody?, initializer, bind, Option.bind_some, Bool.false_eq_true,
        ↓reduceIte] using tail
  | wordMatch _ choice _ scrutineeIH branchIH =>
      obtain ⟨s, scrutineeIH⟩ := scrutineeIH
      obtain ⟨b, branchIH⟩ := branchIH
      apply eventually_step (max s b)
      intro n large
      have scrutinee := scrutineeIH n (by omega)
      have branch := branchIH n (by omega)
      simpa only [evaluateClosedSourceBody?, scrutinee, chooseRuntimeWordMatch?_iff.mpr choice,
        bind, Option.bind_some] using branch

/-- Every finite body derivation is found at all sufficiently large depths. -/
theorem evaluateClosedSourceBody?_eventually_complete
    {owner names captured initialStore source value finalStore}
    (evaluated : ClosedSourceBodyEvaluates owner names captured initialStore source value finalStore) :
    ∃ required, ∀ budget, required ≤ budget →
      evaluateClosedSourceBody? budget owner names captured initialStore source = some (value, finalStore) := by
  have original := closedSourceBodyEvaluates_iff.mp evaluated
  clear evaluated
  induction original with
  | bare =>
      apply eventually_step 0
      intro n _
      simp only [evaluateClosedSourceBody?]
  | expression child =>
      obtain ⟨k, child⟩ := evaluateClosedSourceExpression?_eventually_complete child
      apply eventually_step k
      intro n large
      simpa only [evaluateClosedSourceBody?] using child n large
  | block _ ih =>
      obtain ⟨k, ih⟩ := ih
      apply eventually_step k
      intro n large
      simpa only [evaluateClosedSourceBody?] using ih n large
  | binding initializer _ tailIH | inferred initializer _ tailIH
  | discard initializer _ tailIH | ifTrue initializer _ tailIH | ifFalse initializer _ tailIH =>
      obtain ⟨i, initializerIH⟩ := evaluateClosedSourceExpression?_eventually_complete initializer
      obtain ⟨t, tailIH⟩ := tailIH
      apply eventually_step (max i t)
      intro n large
      have head := initializerIH n (by omega)
      have tail := tailIH n (by omega)
      simpa only [evaluateClosedSourceBody?, head, bind, Option.bind_some, Bool.false_eq_true,
        ↓reduceIte] using tail
  | wordMatch scrutinee choice _ branchIH =>
      obtain ⟨s, scrutineeIH⟩ := evaluateClosedSourceExpression?_eventually_complete scrutinee
      obtain ⟨b, branchIH⟩ := branchIH
      apply eventually_step (max s b)
      intro n large
      have scrutinee := scrutineeIH n (by omega)
      have branch := branchIH n (by omega)
      simpa only [evaluateClosedSourceBody?, scrutinee, chooseRuntimeWordMatch?_iff.mpr choice,
        bind, Option.bind_some] using branch

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.ClosedSourceEvaluatorMonotonicityProperties`
-/

/- Successful depth growth keeps every actual mixed value and store literal.
One private simultaneous induction covers all caller and saved lexical inputs. -/
set_option autoImplicit false
namespace Solcore.Frontend

private theorem simultaneous_step (budget : Nat) :
    (∀ owner names captured store source value finalStore,
      evaluateClosedSourceExpression? budget owner names captured store source = some (value, finalStore) →
      evaluateClosedSourceExpression? (budget + 1) owner names captured store source = some (value, finalStore)) ∧
    (∀ owner names captured store source value finalStore,
      evaluateClosedSourceBody? budget owner names captured store source = some (value, finalStore) →
      evaluateClosedSourceBody? (budget + 1) owner names captured store source = some (value, finalStore)) := by
  induction budget with
  | zero =>
      constructor <;> intro owner names captured store source value finalStore accepted
      · simp only [evaluateClosedSourceExpression?, reduceCtorEq] at accepted
      · simp only [evaluateClosedSourceBody?, reduceCtorEq] at accepted
  | succ n ih =>
      constructor
      · intro owner names captured store source value finalStore accepted
        rcases source with ⟨span, payload⟩
        cases payload <;> try (solve | simpa only [evaluateClosedSourceExpression?] using accepted)
        case group inner =>
          rw [evaluateClosedSourceExpression?] at accepted ⊢
          exact ih.1 _ _ _ _ _ _ _ accepted
        case tuple elements =>
          rcases elements with ⟨tupleSpan, children⟩
          cases children with
          | nil => simpa only [evaluateClosedSourceExpression?] using accepted
          | cons left remaining =>
              cases remaining with
              | nil => simpa only [evaluateClosedSourceExpression?] using accepted
              | cons right tail =>
                  cases tail with
                  | nil =>
                      simp only [evaluateClosedSourceExpression?, bind, Option.bind_eq_some_iff,
                        pure, Option.some.injEq, Prod.mk.injEq] at accepted
                      obtain ⟨⟨lv, middleStore⟩, leftResult, ⟨rv, finalStore⟩, rightResult, rfl, rfl⟩ := accepted
                      rw [evaluateClosedSourceExpression?]
                      simp only [ih.1 _ _ _ _ _ _ _ leftResult, ih.1 _ _ _ _ _ _ _ rightResult,
                        bind, Option.bind_some, pure]
                  | cons third rest =>
                      simp only [evaluateClosedSourceExpression?, bind, Option.bind_eq_some_iff,
                        pure, Option.some.injEq, Prod.mk.injEq] at accepted
                      obtain ⟨⟨head, middleStore⟩, headResult, ⟨tail, finalStore⟩, tailResult, rfl, rfl⟩ := accepted
                      rw [evaluateClosedSourceExpression?]
                      simp only [ih.1 _ _ _ _ _ _ _ headResult, ih.1 _ _ _ _ _ _ _ tailResult,
                        bind, Option.bind_some, pure]
        case conditional condition question thenBranch colon elseBranch =>
          simp only [evaluateClosedSourceExpression?, bind, Option.bind_eq_some_iff] at accepted
          obtain ⟨⟨actual, middleStore⟩, conditionResult, selectedResult⟩ := accepted
          cases actual <;> simp only [reduceCtorEq] at selectedResult
          rename_i choice
          rw [evaluateClosedSourceExpression?]
          simp only [ih.1 _ _ _ _ _ _ _ conditionResult, bind, Option.bind_some]
          exact ih.1 _ _ _ _ _ _ _ selectedResult
        case unary operator operand =>
          rcases operator with ⟨operatorSpan, operator⟩
          cases operator with
          | logicalNot =>
              simp only [evaluateClosedSourceExpression?, bind, Option.bind_eq_some_iff] at accepted
              obtain ⟨⟨actual, finalStore⟩, child, result⟩ := accepted
              cases actual <;>
                simp only [reduceCtorEq, pure, Option.some.injEq, Prod.mk.injEq] at result
              obtain ⟨rfl, rfl⟩ := result
              rw [evaluateClosedSourceExpression?]
              simp only [ih.1 _ _ _ _ _ _ _ child, bind, Option.bind_some, pure]
          | bitNot =>
              simp only [evaluateClosedSourceExpression?, bind, Option.bind_eq_some_iff] at accepted
              obtain ⟨⟨actual, finalStore⟩, child, result⟩ := accepted
              cases actual <;>
                simp only [reduceCtorEq, pure, Option.some.injEq, Prod.mk.injEq] at result
              obtain ⟨rfl, rfl⟩ := result
              rw [evaluateClosedSourceExpression?]
              simp only [ih.1 _ _ _ _ _ _ _ child, bind, Option.bind_some, pure]
        case binary left operator right =>
          rcases operator with ⟨operatorSpan, operator⟩
          cases operator
          case logicalAnd =>
            simp only [evaluateClosedSourceExpression?, bind, Option.bind_eq_some_iff] at accepted
            obtain ⟨⟨actual, middleStore⟩, leftResult, result⟩ := accepted
            cases actual <;> simp only [reduceCtorEq] at result
            rename_i choice
            rw [evaluateClosedSourceExpression?]
            simp only [ih.1 _ _ _ _ _ _ _ leftResult, bind, Option.bind_some]
            cases choice <;> simp only [Bool.false_eq_true, ↓reduceIte] at result ⊢
            · exact result
            · exact ih.1 _ _ _ _ _ _ _ result
          case logicalOr =>
            simp only [evaluateClosedSourceExpression?, bind, Option.bind_eq_some_iff] at accepted
            obtain ⟨⟨actual, middleStore⟩, leftResult, result⟩ := accepted
            cases actual <;> simp only [reduceCtorEq] at result
            rename_i choice
            rw [evaluateClosedSourceExpression?]
            simp only [ih.1 _ _ _ _ _ _ _ leftResult, bind, Option.bind_some]
            cases choice <;> simp only [Bool.false_eq_true, ↓reduceIte] at result ⊢
            · exact ih.1 _ _ _ _ _ _ _ result
            · exact result
          all_goals
            simp only [evaluateClosedSourceExpression?, bind, Option.bind_eq_some_iff] at accepted
            obtain ⟨⟨leftActual, middleStore⟩, leftResult, result⟩ := accepted
            cases leftActual <;> simp only [reduceCtorEq, Option.bind_eq_some_iff] at result
            obtain ⟨⟨rightActual, finalStore⟩, rightResult, result⟩ := result
            cases rightActual <;>
              simp only [reduceCtorEq, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at result
            obtain ⟨coreValue, meaning, rfl, rfl⟩ := result
            simp only [evaluateClosedSourceExpression?,
              ih.1 _ _ _ _ _ _ _ leftResult, ih.1 _ _ _ _ _ _ _ rightResult,
              meaning, bind, Option.bind_some, pure]
        case call callee arguments =>
          rcases arguments with ⟨argumentsSpan, arguments⟩
          cases arguments with
          | nil => simpa only [evaluateClosedSourceExpression?] using accepted
          | cons argument rest =>
              cases rest with
              | cons _ _ => simpa only [evaluateClosedSourceExpression?] using accepted
              | nil =>
                  simp only [evaluateClosedSourceExpression?, bind, Option.bind_eq_some_iff] at accepted
                  obtain ⟨⟨function, calleeStore⟩, calleeResult,
                    ⟨argumentValue, argumentStore⟩, argumentResult, result⟩ := accepted
                  cases function <;> simp only [reduceCtorEq, Option.bind_eq_some_iff] at result
                  obtain ⟨⟨name, body⟩, shape, bodyResult⟩ := result
                  rw [evaluateClosedSourceExpression?]
                  simp only [ih.1 _ _ _ _ _ _ _ calleeResult, ih.1 _ _ _ _ _ _ _ argumentResult,
                    shape, bind, Option.bind_some]
                  exact ih.2 _ _ _ _ _ _ _ bodyResult
      · intro owner names captured store source value finalStore accepted
        rcases source with ⟨blockSpan, statements⟩
        cases statements with
        | nil => simpa only [evaluateClosedSourceBody?] using accepted
        | cons statement rest =>
            rcases statement with ⟨statementSpan, payload⟩
            cases payload <;> try (solve | simpa only [evaluateClosedSourceBody?] using accepted)
            case returnStmt returned =>
                cases rest with
                | cons _ _ => simpa only [evaluateClosedSourceBody?] using accepted
                | nil =>
                    cases returned with
                    | none => simpa only [evaluateClosedSourceBody?] using accepted
                    | some child =>
                        rw [evaluateClosedSourceBody?] at accepted ⊢
                        exact ih.1 _ _ _ _ _ _ _ accepted
            case block inner =>
                cases rest with
                | cons _ _ => simpa only [evaluateClosedSourceBody?] using accepted
                | nil =>
                    rw [evaluateClosedSourceBody?] at accepted ⊢
                    exact ih.2 _ _ _ _ _ _ _ accepted
            case letDecl name annotation initializer =>
                cases initializer with
                | none => simpa only [evaluateClosedSourceBody?] using accepted
                | some initializer =>
                    simp only [evaluateClosedSourceBody?, bind, Option.bind_eq_some_iff] at accepted
                    obtain ⟨⟨boundValue, middleStore⟩, head, tail⟩ := accepted
                    rw [evaluateClosedSourceBody?]
                    simp only [ih.1 _ _ _ _ _ _ _ head, bind, Option.bind_some]
                    exact ih.2 _ _ _ _ _ _ _ tail
            case expression child terminated =>
                cases terminated with
                | false => simpa only [evaluateClosedSourceBody?] using accepted
                | true =>
                    simp only [evaluateClosedSourceBody?, bind, Option.bind_eq_some_iff] at accepted
                    obtain ⟨⟨discarded, middleStore⟩, head, tail⟩ := accepted
                    rw [evaluateClosedSourceBody?]
                    simp only [ih.1 _ _ _ _ _ _ _ head, bind, Option.bind_some]
                    exact ih.2 _ _ _ _ _ _ _ tail
            case ifThen condition thenBody elseBody =>
                cases rest with
                | cons _ _ => simpa only [evaluateClosedSourceBody?] using accepted
                | nil =>
                    cases elseBody with
                    | none => simpa only [evaluateClosedSourceBody?] using accepted
                    | some elseBody =>
                        simp only [evaluateClosedSourceBody?, bind, Option.bind_eq_some_iff] at accepted
                        obtain ⟨⟨actual, middleStore⟩, conditionResult, selectedResult⟩ := accepted
                        cases actual <;> simp only [reduceCtorEq] at selectedResult
                        rename_i choice
                        rw [evaluateClosedSourceBody?]
                        simp only [ih.1 _ _ _ _ _ _ _ conditionResult, bind, Option.bind_some]
                        cases choice <;> simp only [Bool.false_eq_true, ↓reduceIte] at selectedResult ⊢
                        · exact ih.2 _ _ _ _ _ _ _ selectedResult
                        · exact ih.2 _ _ _ _ _ _ _ selectedResult
            case matchWith scrutinees arms =>
                cases rest with
                | cons _ _ => simpa only [evaluateClosedSourceBody?] using accepted
                | nil =>
                    rcases scrutinees with ⟨scrutineeSpan, ⟨scrutinee, additional⟩⟩
                    rcases arms with ⟨armsSpan, ⟨cases, defaultBody⟩⟩
                    cases additional with
                    | cons _ _ => simpa only [evaluateClosedSourceBody?] using accepted
                    | nil =>
                        simp only [evaluateClosedSourceBody?, bind, Option.bind_eq_some_iff] at accepted
                        obtain ⟨⟨actual, middleStore⟩, scrutineeResult,
                          ⟨selected, tests⟩, choice, selectedResult⟩ := accepted
                        rw [evaluateClosedSourceBody?]
                        simp only [ih.1 _ _ _ _ _ _ _ scrutineeResult, choice, bind, Option.bind_some]
                        exact ih.2 _ _ _ _ _ _ _ selectedResult

/-- Increasing depth retains the entire actual successful expression endpoint. -/
theorem evaluateClosedSourceExpression?_monotone
    {small large : Nat} {owner : Resolved.DeclarationId} {names : LocalNameTable}
    {captured : Resolved.LocalScope RuntimeValue} {initialStore : List RuntimeValue}
    {source : Syntax.Expr} {value : RuntimeValue} {finalStore : List RuntimeValue}
    (order : small ≤ large)
    (accepted : evaluateClosedSourceExpression? small owner names captured initialStore source =
      some (value, finalStore)) :
    evaluateClosedSourceExpression? large owner names captured initialStore source = some (value, finalStore) := by
  induction order with
  | refl => exact accepted
  | @step large _ ih => exact (simultaneous_step large).1 _ _ _ _ _ _ _ ih

/-- A larger-depth None excludes successes at every smaller depth. -/
theorem evaluateClosedSourceExpression?_none_of_le
    {small large : Nat} {owner : Resolved.DeclarationId} {names : LocalNameTable}
    {captured : Resolved.LocalScope RuntimeValue} {initialStore : List RuntimeValue}
    {source : Syntax.Expr}
    (order : small ≤ large)
    (rejected : evaluateClosedSourceExpression? large owner names captured initialStore source = none) :
    evaluateClosedSourceExpression? small owner names captured initialStore source = none := by
  cases result : evaluateClosedSourceExpression? small owner names captured initialStore source with
  | none => rfl
  | some endpoint =>
      have retained := evaluateClosedSourceExpression?_monotone order result
      rw [rejected] at retained
      cases retained

/-- Increasing depth retains the entire actual successful original-body endpoint. -/
theorem evaluateClosedSourceBody?_monotone
    {small large : Nat} {owner : Resolved.DeclarationId} {names : LocalNameTable}
    {captured : Resolved.LocalScope RuntimeValue} {initialStore : List RuntimeValue}
    {source : Syntax.Block} {value : RuntimeValue} {finalStore : List RuntimeValue}
    (order : small ≤ large)
    (accepted : evaluateClosedSourceBody? small owner names captured initialStore source =
      some (value, finalStore)) :
    evaluateClosedSourceBody? large owner names captured initialStore source = some (value, finalStore) := by
  induction order with
  | refl => exact accepted
  | @step large _ ih => exact (simultaneous_step large).2 _ _ _ _ _ _ _ ih

/-- Original bodies satisfy the same None-downward direction. -/
theorem evaluateClosedSourceBody?_none_of_le
    {small large : Nat} {owner : Resolved.DeclarationId} {names : LocalNameTable}
    {captured : Resolved.LocalScope RuntimeValue} {initialStore : List RuntimeValue}
    {source : Syntax.Block}
    (order : small ≤ large)
    (rejected : evaluateClosedSourceBody? large owner names captured initialStore source = none) :
    evaluateClosedSourceBody? small owner names captured initialStore source = none := by
  cases result : evaluateClosedSourceBody? small owner names captured initialStore source with
  | none => rfl
  | some endpoint =>
      have retained := evaluateClosedSourceBody?_monotone order result
      rw [rejected] at retained
      cases retained

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.ClosedSourceEvaluatorOwnerStepProperties`
-/

/- One executable body layer preserves complete Option endpoints. The supplied
predecessor equations include failure, arbitrary captures and complete stores;
no original-success, typing, scope uniqueness or depth-existence premise is used. -/
set_option autoImplicit false
namespace Solcore.Frontend

/-- Full predecessor covariance suffices for the next body budget, including absence. -/
theorem evaluateClosedSourceBody?_mapOwners_step
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (injective : Function.Injective mapping)
    (n : Nat)
    (expressionIH : ∀ owner names captured store source,
      evaluateClosedSourceExpression? n (mapping owner) (LocalNameTable.mapIds (ownerLocalIdMap mapping) names)
        (mapRuntimeCapturedOwners mapping captured) (store.map (RuntimeValue.mapOwners mapping)) source =
      (evaluateClosedSourceExpression? n owner names captured store source).map
        (fun result => (result.1.mapOwners mapping,result.2.map (RuntimeValue.mapOwners mapping))))
    (bodyIH : ∀ owner names captured store source,
      evaluateClosedSourceBody? n (mapping owner) (LocalNameTable.mapIds (ownerLocalIdMap mapping) names)
        (mapRuntimeCapturedOwners mapping captured) (store.map (RuntimeValue.mapOwners mapping)) source =
      (evaluateClosedSourceBody? n owner names captured store source).map
        (fun result => (result.1.mapOwners mapping,result.2.map (RuntimeValue.mapOwners mapping))))
    (owner : Resolved.DeclarationId) (names : LocalNameTable) (captured : Resolved.LocalScope RuntimeValue)
    (store : List RuntimeValue) (source : Syntax.Block) :
    evaluateClosedSourceBody? (n+1) (mapping owner) (LocalNameTable.mapIds (ownerLocalIdMap mapping) names)
      (mapRuntimeCapturedOwners mapping captured) (store.map (RuntimeValue.mapOwners mapping)) source =
    (evaluateClosedSourceBody? (n+1) owner names captured store source).map
      (fun result => (result.1.mapOwners mapping,result.2.map (RuntimeValue.mapOwners mapping))) := by
  rcases source with ⟨blockSpan,statements⟩
  cases statements with
  | nil => simp only [evaluateClosedSourceBody?,Option.map_none]
  | cons statement rest =>
    rcases statement with ⟨statementSpan,payload⟩
    cases payload <;> try (solve | simp only [evaluateClosedSourceBody?,Option.map_none])
    case returnStmt child =>
      cases rest <;> cases child <;>
        simp only [evaluateClosedSourceBody?,expressionIH,Option.map_some,Option.map_none,RuntimeValue.mapOwners]
    case block statements =>
      cases rest <;> simp only [evaluateClosedSourceBody?,bodyIH,Option.map_none]
    case letDecl name annotation initializer =>
      cases initializer with
      | none => simp only [evaluateClosedSourceBody?,Option.map_none]
      | some initializer =>
        simp only [evaluateClosedSourceBody?,expressionIH]
        cases first : evaluateClosedSourceExpression? n owner names captured store initializer with
        | none => simp only [Option.map_none,bind,Option.bind_none]
        | some result =>
          rcases result with ⟨value,middle⟩
          simp only [Option.map_some,bind,Option.bind_some]
          rw [freshLocalId_mapRuntimeNamesOwners mapping injective]
          simpa only [LocalNameTable.mapIds,mapRuntimeCapturedOwners,List.map_cons] using
            bodyIH owner ((name.value,Resolved.freshLocalId owner (names.map Prod.snd))::names)
              ((Resolved.freshLocalId owner (names.map Prod.snd),value)::captured) middle ⟨blockSpan,rest⟩
    case expression child semicolon =>
      cases semicolon with
      | false => simp only [evaluateClosedSourceBody?,Option.map_none]
      | true =>
        simp only [evaluateClosedSourceBody?,expressionIH]
        cases first : evaluateClosedSourceExpression? n owner names captured store child with
        | none => simp only [Option.map_none,bind,Option.bind_none]
        | some result =>
          rcases result with ⟨value,middle⟩
          simpa only [first,Option.map_some,bind,Option.bind_some] using
            bodyIH owner names captured middle ⟨blockSpan,rest⟩
    case ifThen condition thenBody elseBody =>
      cases rest with
      | cons _ _ => simp only [evaluateClosedSourceBody?,Option.map_none]
      | nil =>
        cases elseBody with
        | none => simp only [evaluateClosedSourceBody?,Option.map_none]
        | some elseBody =>
          simp only [evaluateClosedSourceBody?,expressionIH]
          cases first : evaluateClosedSourceExpression? n owner names captured store condition with
          | none => simp only [Option.map_none,bind,Option.bind_none]
          | some result =>
            rcases result with ⟨value,middle⟩
            cases value <;> simp only [Option.map_some,bind,Option.bind_some,
              RuntimeValue.mapOwners,bodyIH,Option.map_none]
            case bool choice => cases choice <;> rfl
    case matchWith scrutinees arms =>
      cases rest with
      | cons _ _ => simp only [evaluateClosedSourceBody?,Option.map_none]
      | nil =>
        rcases scrutinees with ⟨scrutineesSpan,⟨scrutinee,additional⟩⟩
        cases additional with
        | cons _ _ => simp only [evaluateClosedSourceBody?,Option.map_none]
        | nil =>
          rcases arms with ⟨armsSpan,⟨cases,defaultBody⟩⟩
          simp only [evaluateClosedSourceBody?,expressionIH]
          cases first : evaluateClosedSourceExpression? n owner names captured store scrutinee with
          | none => simp only [Option.map_none,bind,Option.bind_none]
          | some result =>
            rcases result with ⟨value,middle⟩
            simp only [Option.map_some,bind,Option.bind_some,chooseRuntimeWordMatch?_mapOwners]
            cases selected : chooseRuntimeWordMatch? value cases defaultBody with
            | none => simp only [Option.bind_none,Option.map_none]
            | some result =>
              rcases result with ⟨chosen,tests⟩
              simpa only [selected,Option.bind_some] using bodyIH owner names captured middle chosen

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.ClosedSourceEvaluatorOwnerProperties`
-/

/- Direct joint budget induction keeps complete successes and failures.
All stored owners and payloads are relabeled; source syntax and depth are literal. -/
set_option autoImplicit false
namespace Solcore.Frontend

private def endpoint (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (result : RuntimeValue × List RuntimeValue) : RuntimeValue × List RuntimeValue :=
  (result.1.mapOwners mapping,result.2.map (RuntimeValue.mapOwners mapping))

private theorem creation (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue) (source : Syntax.Expr) :
    (do let _ ← sourceUnaryLambdaShape? source
        pure (RuntimeValue.sourceClosure source (mapping owner)
          (LocalNameTable.mapIds (ownerLocalIdMap mapping) names) (mapRuntimeCapturedOwners mapping captured),
          store.map (RuntimeValue.mapOwners mapping))) =
      (do let _ ← sourceUnaryLambdaShape? source
          pure (RuntimeValue.sourceClosure source owner names captured,store)).map (endpoint mapping) := by
  cases shape : sourceUnaryLambdaShape? source <;>
    simp only [bind,Option.bind_none,Option.bind_some,pure,Option.map_none,Option.map_some,
      endpoint,RuntimeValue.mapOwners_sourceClosure]

private theorem pair_tail (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (left : RuntimeValue) (tail : Option (RuntimeValue × List RuntimeValue)) :
    ((tail.map (endpoint mapping)).bind fun result => pure (.pair (left.mapOwners mapping) result.1,result.2)) =
      (tail.bind fun result => pure (RuntimeValue.pair left result.1,result.2)).map (endpoint mapping) := by
  cases tail with
  | none => rfl
  | some result =>
    rcases result with ⟨right,store⟩
    simp only [Option.map_some,Option.bind_some,pure,endpoint,RuntimeValue.mapOwners]

private theorem strict_tail (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (operator : Syntax.BinaryOp) (left : Core.Word) (tail : Option (RuntimeValue × List RuntimeValue)) :
    ((tail.map (endpoint mapping)).bind fun result => match result with
      | (.word right,store) => (evaluateStrictWordBinary? operator left right).bind fun value =>
          pure (RuntimeValue.ofCore value,store)
      | _ => none) =
    (tail.bind fun result => match result with
      | (.word right,store) => (evaluateStrictWordBinary? operator left right).bind fun value =>
          pure (RuntimeValue.ofCore value,store)
      | _ => none).map (endpoint mapping) := by
  cases tail with
  | none => rfl
  | some result =>
    rcases result with ⟨value,store⟩
    cases value <;> simp only [Option.map_some,Option.bind_some,endpoint,RuntimeValue.mapOwners,Option.map_none]
    rename_i right
    cases meaning : evaluateStrictWordBinary? operator left right <;>
      simp only [Option.bind_none,Option.bind_some,pure,Option.map_none,Option.map_some,endpoint,
        RuntimeValue.mapOwners_ofCore]

section
variable (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
variable (injective : Function.Injective mapping)
include injective

private theorem simultaneous (budget : Nat) :
    (∀ owner names captured store source,
      evaluateClosedSourceExpression? budget (mapping owner) (LocalNameTable.mapIds (ownerLocalIdMap mapping) names)
        (mapRuntimeCapturedOwners mapping captured) (store.map (RuntimeValue.mapOwners mapping)) source =
      (evaluateClosedSourceExpression? budget owner names captured store source).map (endpoint mapping)) ∧
    (∀ owner names captured store source,
      evaluateClosedSourceBody? budget (mapping owner) (LocalNameTable.mapIds (ownerLocalIdMap mapping) names)
        (mapRuntimeCapturedOwners mapping captured) (store.map (RuntimeValue.mapOwners mapping)) source =
      (evaluateClosedSourceBody? budget owner names captured store source).map (endpoint mapping)) := by
  induction budget with
  | zero =>
    constructor <;> intro owner names captured store source
    · simp only [evaluateClosedSourceExpression?,Option.map_none]
    · simp only [evaluateClosedSourceBody?,Option.map_none]
  | succ n ih =>
    constructor
    · intro owner names captured store source
      rcases source with ⟨span,payload⟩
      cases payload <;> try (solve |
        simpa only [evaluateClosedSourceExpression?] using creation mapping owner names captured store _)
      case identifier name =>
        simp only [evaluateClosedSourceExpression?,LocalNameTable.lookup?_mapIds]
        cases named : names.lookup? name.value with
        | none => simp only [Option.map_none,bind,Option.bind_none]
        | some id =>
          simp only [Option.map_some,bind,Option.bind_some,
            lookup?_mapRuntimeCapturedOwners mapping injective]
          cases found : captured.lookup? id <;>
            simp only [Option.map_none,Option.map_some,Option.bind_none,Option.bind_some,pure,endpoint]
      case literal literal =>
        simp only [evaluateClosedSourceExpression?]
        cases interpreted : interpretWordLiteral? literal <;>
          simp only [bind,Option.bind_none,Option.bind_some,pure,
            Option.map_none,Option.map_some,endpoint,RuntimeValue.mapOwners]
      case group inner =>
        simpa only [evaluateClosedSourceExpression?] using ih.1 owner names captured store inner
      case tuple elements =>
        rcases elements with ⟨tupleSpan,children⟩
        cases children with
        | nil => simp only [evaluateClosedSourceExpression?,Option.map_some,endpoint,RuntimeValue.mapOwners]
        | cons left remaining =>
          cases remaining with
          | nil => simpa only [evaluateClosedSourceExpression?] using creation mapping owner names captured store _
          | cons right tail =>
            cases tail <;>
              simp only [evaluateClosedSourceExpression?,ih.1]
            all_goals
              cases first : evaluateClosedSourceExpression? n owner names captured store left with
              | none => simp only [Option.map_none,bind,Option.bind_none]
              | some result =>
                rcases result with ⟨value,middle⟩
                simp only [Option.map_some,bind,Option.bind_some,endpoint,ih.1]
                exact pair_tail mapping value _
      case conditional condition question thenBranch colon elseBranch =>
        simp only [evaluateClosedSourceExpression?,ih.1]
        cases first : evaluateClosedSourceExpression? n owner names captured store condition with
        | none => simp only [Option.map_none,bind,Option.bind_none]
        | some result =>
          rcases result with ⟨value,middle⟩
          cases value <;> simp only [Option.map_some,bind,Option.bind_some,endpoint,RuntimeValue.mapOwners,ih.1,
            Option.map_none]
      case unary operator operand =>
        rcases operator with ⟨operatorSpan,operator⟩
        cases operator <;> simp only [evaluateClosedSourceExpression?,ih.1]
        all_goals
          cases first : evaluateClosedSourceExpression? n owner names captured store operand with
          | none => simp only [Option.map_none,bind,Option.bind_none]
          | some result =>
            rcases result with ⟨value,final⟩
            cases value <;> simp only [Option.map_some,bind,Option.bind_some,endpoint,
              RuntimeValue.mapOwners,pure,Option.map_none]
      case binary left operator right =>
        rcases operator with ⟨operatorSpan,operator⟩
        cases operator <;> simp only [evaluateClosedSourceExpression?,ih.1]
        all_goals
          cases first : evaluateClosedSourceExpression? n owner names captured store left with
          | none => simp only [Option.map_none,bind,Option.bind_none]
          | some result =>
            rcases result with ⟨value,middle⟩
            cases value <;> simp only [Option.map_some,bind,Option.bind_some,endpoint,
              RuntimeValue.mapOwners,Option.map_none,ih.1]
            all_goals first
              | exact strict_tail mapping _ _ _
              | rename_i choice
                cases choice <;> simp only [Bool.false_eq_true,↓reduceIte,pure,Option.map_some,endpoint,
                  RuntimeValue.mapOwners]
      case call callee arguments =>
        rcases arguments with ⟨argumentsSpan,arguments⟩
        cases arguments with
        | nil => simpa only [evaluateClosedSourceExpression?] using creation mapping owner names captured store _
        | cons argument rest =>
          cases rest with
          | cons _ _ => simpa only [evaluateClosedSourceExpression?] using creation mapping owner names captured store _
          | nil =>
            simp only [evaluateClosedSourceExpression?,ih.1]
            cases first : evaluateClosedSourceExpression? n owner names captured store callee with
            | none => simp only [Option.map_none,bind,Option.bind_none]
            | some result =>
              rcases result with ⟨function,middle⟩
              simp only [Option.map_some,bind,Option.bind_some,endpoint,ih.1]
              cases second : evaluateClosedSourceExpression? n owner names captured middle argument with
              | none => simp only [Option.map_none,Option.bind_none]
              | some result =>
                rcases result with ⟨value,final⟩
                cases function <;> try (solve |
                  simp only [Option.map_some,Option.bind_some,endpoint,RuntimeValue.mapOwners,Option.map_none])
                case sourceClosure saved savedOwner savedNames savedCaptured =>
                  simp only [Option.map_some,Option.bind_some,endpoint,RuntimeValue.mapOwners_sourceClosure]
                  cases shape : sourceUnaryLambdaShape? saved with
                  | none => simp only [Option.bind_none,Option.map_none]
                  | some bodyInfo =>
                    rcases bodyInfo with ⟨name,body⟩
                    simp only [Option.bind_some]
                    rw [freshLocalId_mapRuntimeNamesOwners mapping injective]
                    simpa only [LocalNameTable.mapIds,mapRuntimeCapturedOwners,List.map_cons] using
                      ih.2 savedOwner ((name.value,Resolved.freshLocalId savedOwner (savedNames.map Prod.snd))::savedNames)
                        ((Resolved.freshLocalId savedOwner (savedNames.map Prod.snd),value)::savedCaptured) final body
    · intro owner names captured store source
      exact evaluateClosedSourceBody?_mapOwners_step mapping injective n
        ih.1 ih.2
        owner names captured store source

/-- Exact owner covariance of every finite expression outcome, including absence. -/
theorem evaluateClosedSourceExpression?_mapOwners
    (budget : Nat) (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue) (source : Syntax.Expr) :
    evaluateClosedSourceExpression? budget (mapping owner) (LocalNameTable.mapIds (ownerLocalIdMap mapping) names)
      (mapRuntimeCapturedOwners mapping captured) (store.map (RuntimeValue.mapOwners mapping)) source =
    (evaluateClosedSourceExpression? budget owner names captured store source).map
      (fun result => (result.1.mapOwners mapping,result.2.map (RuntimeValue.mapOwners mapping))) :=
  (simultaneous mapping injective budget).1 owner names captured store source

/-- Exact body covariance retains the same budget, selected syntax and complete endpoint. -/
theorem evaluateClosedSourceBody?_mapOwners
    (budget : Nat) (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue) (source : Syntax.Block) :
    evaluateClosedSourceBody? budget (mapping owner) (LocalNameTable.mapIds (ownerLocalIdMap mapping) names)
      (mapRuntimeCapturedOwners mapping captured) (store.map (RuntimeValue.mapOwners mapping)) source =
    (evaluateClosedSourceBody? budget owner names captured store source).map
      (fun result => (result.1.mapOwners mapping,result.2.map (RuntimeValue.mapOwners mapping))) :=
  (simultaneous mapping injective budget).2 owner names captured store source

end
end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.ClosedSourceEvaluatorSoundnessProperties`
-/

/- One private simultaneous budget induction constructs the independent source
judgments at exact actual endpoints, without callback or checking premises. -/

set_option autoImplicit false
namespace Solcore.Frontend

private theorem simultaneous_sound (budget : Nat) :
    (∀ owner names captured store source value finalStore,
      evaluateClosedSourceExpression? budget owner names captured store source = some (value, finalStore) →
      ClosedSourceExpressionEvaluates owner names captured store source value finalStore) ∧
    (∀ owner names captured store source value finalStore,
      evaluateClosedSourceBody? budget owner names captured store source = some (value, finalStore) →
      ClosedSourceBodyEvaluates owner names captured store source value finalStore) := by
  induction budget with
  | zero =>
      constructor <;> intro owner names captured store source value finalStore accepted
      · simp only [evaluateClosedSourceExpression?, reduceCtorEq] at accepted
      · simp only [evaluateClosedSourceBody?, reduceCtorEq] at accepted
  | succ n ih =>
      constructor
      · intro owner names captured store source value finalStore accepted
        rcases source with ⟨span, payload⟩
        cases payload <;> try (solve |
          simp only [evaluateClosedSourceExpression?, sourceUnaryLambdaShape?,
            bind, Option.bind_none, reduceCtorEq] at accepted)
        case identifier name =>
          simp only [evaluateClosedSourceExpression?, bind, Option.bind_eq_some_iff,
            pure, Option.some.injEq, Prod.mk.injEq] at accepted
          obtain ⟨id, named, actual, found, rfl, rfl⟩ := accepted
          exact .reference (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found)
        case literal literal =>
          simp only [evaluateClosedSourceExpression?, bind, Option.bind_eq_some_iff,
            pure, Option.some.injEq, Prod.mk.injEq] at accepted
          obtain ⟨word, meaning, rfl, rfl⟩ := accepted
          exact .wordLiteral (interpretWordLiteral?_sound meaning)
        case group inner =>
          rw [evaluateClosedSourceExpression?] at accepted
          exact .group (ih.1 _ _ _ _ _ _ _ accepted)
        case tuple elements =>
          rcases elements with ⟨tupleSpan, children⟩
          cases children with
          | nil =>
              simp only [evaluateClosedSourceExpression?, Option.some.injEq, Prod.mk.injEq] at accepted
              obtain ⟨rfl, rfl⟩ := accepted
              exact .unit
          | cons left remaining =>
              cases remaining with
              | nil =>
                  simp only [evaluateClosedSourceExpression?, sourceUnaryLambdaShape?,
                    bind, Option.bind_none, reduceCtorEq] at accepted
              | cons right tail =>
                  cases tail with
                  | nil =>
                      simp only [evaluateClosedSourceExpression?, bind, Option.bind_eq_some_iff,
                        pure, Option.some.injEq, Prod.mk.injEq] at accepted
                      obtain ⟨⟨leftValue, middleStore⟩, leftResult,
                        ⟨rightValue, finalStore⟩, rightResult, rfl, rfl⟩ := accepted
                      exact .pair (ih.1 _ _ _ _ _ _ _ leftResult) (ih.1 _ _ _ _ _ _ _ rightResult)
                  | cons third rest =>
                      simp only [evaluateClosedSourceExpression?, bind, Option.bind_eq_some_iff,
                        pure, Option.some.injEq, Prod.mk.injEq] at accepted
                      obtain ⟨⟨headValue, middleStore⟩, headResult,
                        ⟨tailValue, finalStore⟩, tailResult, rfl, rfl⟩ := accepted
                      exact .many (ih.1 _ _ _ _ _ _ _ headResult) (ih.1 _ _ _ _ _ _ _ tailResult)
        case call callee arguments =>
          rcases arguments with ⟨argumentsSpan, arguments⟩
          cases arguments with
          | nil =>
              simp only [evaluateClosedSourceExpression?, sourceUnaryLambdaShape?,
                bind, Option.bind_none, reduceCtorEq] at accepted
          | cons argument rest =>
              cases rest with
              | cons _ _ =>
                  simp only [evaluateClosedSourceExpression?, sourceUnaryLambdaShape?,
                    bind, Option.bind_none, reduceCtorEq] at accepted
              | nil =>
                  simp only [evaluateClosedSourceExpression?, bind, Option.bind_eq_some_iff] at accepted
                  obtain ⟨⟨function, calleeStore⟩, calleeResult,
                    ⟨argumentValue, argumentStore⟩, argumentResult, result⟩ := accepted
                  cases function <;> simp only [reduceCtorEq, Option.bind_eq_some_iff] at result
                  obtain ⟨⟨name, body⟩, shape, bodyResult⟩ := result
                  exact .call (sourceUnaryLambdaShape?_iff.mp shape)
                    (ih.1 _ _ _ _ _ _ _ calleeResult) (ih.1 _ _ _ _ _ _ _ argumentResult)
                    (ih.2 _ _ _ _ _ _ _ bodyResult)
        case conditional condition question thenBranch colon elseBranch =>
          simp only [evaluateClosedSourceExpression?, bind, Option.bind_eq_some_iff] at accepted
          obtain ⟨⟨actual, middleStore⟩, conditionResult, result⟩ := accepted
          cases actual <;> simp only [reduceCtorEq] at result
          rename_i choice
          cases choice <;> simp only [Bool.false_eq_true, ↓reduceIte] at result
          · exact .conditionalFalse (ih.1 _ _ _ _ _ _ _ conditionResult) (ih.1 _ _ _ _ _ _ _ result)
          · exact .conditionalTrue (ih.1 _ _ _ _ _ _ _ conditionResult) (ih.1 _ _ _ _ _ _ _ result)
        case unary operator operand =>
          rcases operator with ⟨operatorSpan, operator⟩
          cases operator with
          | logicalNot =>
              simp only [evaluateClosedSourceExpression?, bind, Option.bind_eq_some_iff] at accepted
              obtain ⟨⟨actual, finalStore⟩, child, result⟩ := accepted
              cases actual <;>
                simp only [reduceCtorEq, pure, Option.some.injEq, Prod.mk.injEq] at result
              obtain ⟨rfl, rfl⟩ := result
              exact .logicalNot (ih.1 _ _ _ _ _ _ _ child)
          | bitNot =>
              simp only [evaluateClosedSourceExpression?, bind, Option.bind_eq_some_iff] at accepted
              obtain ⟨⟨actual, finalStore⟩, child, result⟩ := accepted
              cases actual <;>
                simp only [reduceCtorEq, pure, Option.some.injEq, Prod.mk.injEq] at result
              obtain ⟨rfl, rfl⟩ := result
              exact .bitNot (ih.1 _ _ _ _ _ _ _ child)
        case binary left operator right =>
          rcases operator with ⟨operatorSpan, operator⟩
          cases operator
          case logicalAnd =>
            simp only [evaluateClosedSourceExpression?, bind, Option.bind_eq_some_iff] at accepted
            obtain ⟨⟨actual, middleStore⟩, leftResult, result⟩ := accepted
            cases actual <;> simp only [reduceCtorEq] at result
            rename_i choice
            cases choice <;> simp only [Bool.false_eq_true, ↓reduceIte] at result
            · simp only [pure, Option.some.injEq, Prod.mk.injEq] at result
              obtain ⟨rfl, rfl⟩ := result
              exact .andFalse (ih.1 _ _ _ _ _ _ _ leftResult)
            · exact .andTrue (ih.1 _ _ _ _ _ _ _ leftResult) (ih.1 _ _ _ _ _ _ _ result)
          case logicalOr =>
            simp only [evaluateClosedSourceExpression?, bind, Option.bind_eq_some_iff] at accepted
            obtain ⟨⟨actual, middleStore⟩, leftResult, result⟩ := accepted
            cases actual <;> simp only [reduceCtorEq] at result
            rename_i choice
            cases choice <;> simp only [Bool.false_eq_true, ↓reduceIte] at result
            · exact .orFalse (ih.1 _ _ _ _ _ _ _ leftResult) (ih.1 _ _ _ _ _ _ _ result)
            · simp only [pure, Option.some.injEq, Prod.mk.injEq] at result
              obtain ⟨rfl, rfl⟩ := result
              exact .orTrue (ih.1 _ _ _ _ _ _ _ leftResult)
          all_goals
            simp only [evaluateClosedSourceExpression?, bind, Option.bind_eq_some_iff] at accepted
            obtain ⟨⟨leftActual, middleStore⟩, leftResult, result⟩ := accepted
            cases leftActual <;> simp only [reduceCtorEq, Option.bind_eq_some_iff] at result
            obtain ⟨⟨rightActual, finalStore⟩, rightResult, result⟩ := result
            cases rightActual <;>
              simp only [reduceCtorEq, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at result
            obtain ⟨coreValue, meaning, rfl, rfl⟩ := result
            exact .strictWordBinary (ih.1 _ _ _ _ _ _ _ leftResult)
              (ih.1 _ _ _ _ _ _ _ rightResult) (evaluateStrictWordBinary?_iff.mp meaning)
        case lambda keyword parameters returns body =>
          simp only [evaluateClosedSourceExpression?, bind, Option.bind_eq_some_iff,
            pure, Option.some.injEq, Prod.mk.injEq] at accepted
          obtain ⟨⟨name, body⟩, shape, rfl, rfl⟩ := accepted
          exact .creation (sourceUnaryLambdaShape?_iff.mp shape)
      · intro owner names captured store source value finalStore accepted
        rcases source with ⟨blockSpan, statements⟩
        cases statements with
        | nil => simp only [evaluateClosedSourceBody?, reduceCtorEq] at accepted
        | cons statement rest =>
            rcases statement with ⟨statementSpan, payload⟩
            cases payload <;> try (solve | simp only [evaluateClosedSourceBody?, reduceCtorEq] at accepted)
            case returnStmt returned =>
                cases rest with
                | cons _ _ => simp only [evaluateClosedSourceBody?, reduceCtorEq] at accepted
                | nil =>
                    cases returned with
                    | none =>
                        simp only [evaluateClosedSourceBody?, Option.some.injEq, Prod.mk.injEq] at accepted
                        obtain ⟨rfl, rfl⟩ := accepted
                        exact .bare
                    | some child =>
                        rw [evaluateClosedSourceBody?] at accepted
                        exact .expression (ih.1 _ _ _ _ _ _ _ accepted)
            case block inner =>
                cases rest with
                | cons _ _ => simp only [evaluateClosedSourceBody?, reduceCtorEq] at accepted
                | nil =>
                    rw [evaluateClosedSourceBody?] at accepted
                    exact .block (ih.2 _ _ _ _ _ _ _ accepted)
            case letDecl name annotation initializer =>
                cases initializer with
                | none => simp only [evaluateClosedSourceBody?, reduceCtorEq] at accepted
                | some initializer =>
                    simp only [evaluateClosedSourceBody?, bind, Option.bind_eq_some_iff] at accepted
                    obtain ⟨⟨boundValue, middleStore⟩, head, tail⟩ := accepted
                    cases annotation with
                    | none => exact .inferred (ih.1 _ _ _ _ _ _ _ head) (ih.2 _ _ _ _ _ _ _ tail)
                    | some annotation => exact .binding (ih.1 _ _ _ _ _ _ _ head) (ih.2 _ _ _ _ _ _ _ tail)
            case expression child terminated =>
                cases terminated with
                | false => simp only [evaluateClosedSourceBody?, reduceCtorEq] at accepted
                | true =>
                    simp only [evaluateClosedSourceBody?, bind, Option.bind_eq_some_iff] at accepted
                    obtain ⟨⟨discarded, middleStore⟩, head, tail⟩ := accepted
                    exact .discard (ih.1 _ _ _ _ _ _ _ head) (ih.2 _ _ _ _ _ _ _ tail)
            case ifThen condition thenBody elseBody =>
                cases rest with
                | cons _ _ => simp only [evaluateClosedSourceBody?, reduceCtorEq] at accepted
                | nil =>
                    cases elseBody with
                    | none => simp only [evaluateClosedSourceBody?, reduceCtorEq] at accepted
                    | some elseBody =>
                        simp only [evaluateClosedSourceBody?, bind, Option.bind_eq_some_iff] at accepted
                        obtain ⟨⟨actual, middleStore⟩, conditionResult, result⟩ := accepted
                        cases actual <;> simp only [reduceCtorEq] at result
                        rename_i choice
                        cases choice <;> simp only [Bool.false_eq_true, ↓reduceIte] at result
                        · exact .ifFalse (ih.1 _ _ _ _ _ _ _ conditionResult) (ih.2 _ _ _ _ _ _ _ result)
                        · exact .ifTrue (ih.1 _ _ _ _ _ _ _ conditionResult) (ih.2 _ _ _ _ _ _ _ result)
            case matchWith scrutinees arms =>
                cases rest with
                | cons _ _ => simp only [evaluateClosedSourceBody?, reduceCtorEq] at accepted
                | nil =>
                    rcases scrutinees with ⟨scrutineeSpan, ⟨scrutinee, additional⟩⟩
                    rcases arms with ⟨armsSpan, ⟨cases, defaultBody⟩⟩
                    cases additional with
                    | cons _ _ => simp only [evaluateClosedSourceBody?, reduceCtorEq] at accepted
                    | nil =>
                        simp only [evaluateClosedSourceBody?, bind, Option.bind_eq_some_iff] at accepted
                        obtain ⟨⟨actual, middleStore⟩, scrutineeResult,
                          ⟨selected, tests⟩, choice, branch⟩ := accepted
                        exact .wordMatch (ih.1 _ _ _ _ _ _ _ scrutineeResult)
                          (chooseRuntimeWordMatch?_iff.mp choice) (ih.2 _ _ _ _ _ _ _ branch)

/-- Every computed expression endpoint has an independent closed derivation. -/
theorem evaluateClosedSourceExpression?_sound
    {budget owner names captured initialStore source value finalStore}
    (accepted : evaluateClosedSourceExpression? budget owner names captured initialStore source =
      some (value, finalStore)) :
    ClosedSourceExpressionEvaluates owner names captured initialStore source value finalStore :=
  (simultaneous_sound budget).1 _ _ _ _ _ _ _ accepted

/-- Every computed body endpoint has an independent closed derivation. -/
theorem evaluateClosedSourceBody?_sound
    {budget owner names captured initialStore source value finalStore}
    (accepted : evaluateClosedSourceBody? budget owner names captured initialStore source =
      some (value, finalStore)) :
    ClosedSourceBodyEvaluates owner names captured initialStore source value finalStore :=
  (simultaneous_sound budget).2 _ _ _ _ _ _ _ accepted

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.ClosedSourceDataBodyDepthDecisionProperties`
-/

/- Exact finite search on the independently admitted data-body syntax.
No lookup, literal validity or runtime typing premise guarantees success.
All absence claims concern this existing successful-evaluation judgment only. -/
set_option autoImplicit false
namespace Solcore.Frontend

/-- At every sufficient source depth, the actual result and entire final store
agree exactly with the original judgment over arbitrary mixed runtime inputs. -/
theorem ClosedSourceDataBody.evaluate_at_depthBound_iff
    {source : Syntax.Block} (fragment : ClosedSourceDataBody source)
    {owner : Resolved.DeclarationId} {names : LocalNameTable}
    {captured : Resolved.LocalScope RuntimeValue} {initialStore finalStore : List RuntimeValue}
    {value : RuntimeValue} {budget : Nat}
    (enough : closedSourceDataBodyDepthBound source ≤ budget) :
    evaluateClosedSourceBody? budget owner names captured initialStore source =
      some (value,finalStore) ↔
    ClosedSourceBodyEvaluates owner names captured initialStore source value finalStore :=
  ⟨evaluateClosedSourceBody?_sound,fun original => fragment.evaluates_at_depthBound original enough⟩

/-- Whole Option stability includes semantic failure, not only successful values.
The bound is sufficient; a selected short-circuit path may need much less depth. -/
theorem ClosedSourceDataBody.evaluate_depth_stable
    {source : Syntax.Block} (fragment : ClosedSourceDataBody source)
    (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (initialStore : List RuntimeValue)
    {budget : Nat} (enough : closedSourceDataBodyDepthBound source ≤ budget) :
    evaluateClosedSourceBody? budget owner names captured initialStore source =
      evaluateClosedSourceBody? (closedSourceDataBodyDepthBound source)
        owner names captured initialStore source := by
  cases low : evaluateClosedSourceBody? (closedSourceDataBodyDepthBound source)
      owner names captured initialStore source with
  | none =>
      cases high : evaluateClosedSourceBody? budget owner names captured initialStore source with
      | none => rfl
      | some endpoint =>
          obtain ⟨value,finalStore⟩ := endpoint
          have atBound := fragment.evaluates_at_depthBound
            (evaluateClosedSourceBody?_sound high) (Nat.le_refl _)
          rw [low] at atBound
          cases atBound
  | some endpoint =>
      obtain ⟨value,finalStore⟩ := endpoint
      exact evaluateClosedSourceBody?_monotone enough low

/-- Failure at a sufficient depth excludes every original successful endpoint.
It does not classify missing values, wrong payloads or invalid literal spellings. -/
theorem ClosedSourceDataBody.evaluate_depth_none_iff
    {source : Syntax.Block} (fragment : ClosedSourceDataBody source)
    (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (initialStore : List RuntimeValue)
    {budget : Nat} (enough : closedSourceDataBodyDepthBound source ≤ budget) :
    evaluateClosedSourceBody? budget owner names captured initialStore source = none ↔
      ∀ value finalStore, ¬ ClosedSourceBodyEvaluates owner names captured
        initialStore source value finalStore := by
  constructor
  · intro absent value finalStore original
    have accepted := fragment.evaluates_at_depthBound original enough
    rw [absent] at accepted
    cases accepted
  · intro impossible
    cases actual : evaluateClosedSourceBody? budget owner names captured initialStore source with
    | none => rfl
    | some endpoint =>
        obtain ⟨value,finalStore⟩ := endpoint
        exact False.elim (impossible value finalStore (evaluateClosedSourceBody?_sound actual))

/-- A single sufficient search decides whether any budget could succeed on this
gated syntax; no analogous conclusion is claimed for arbitrary source bodies or calls. -/
theorem ClosedSourceDataBody.evaluate_depth_none_iff_all_budgets
    {source : Syntax.Block} (fragment : ClosedSourceDataBody source)
    (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (initialStore : List RuntimeValue) :
    evaluateClosedSourceBody? (closedSourceDataBodyDepthBound source)
        owner names captured initialStore source = none ↔
      ∀ budget, evaluateClosedSourceBody? budget owner names captured initialStore source = none := by
  constructor
  · intro absent budget
    have impossible := (fragment.evaluate_depth_none_iff owner names captured initialStore (Nat.le_refl _)).mp absent
    cases actual : evaluateClosedSourceBody? budget owner names captured initialStore source with
    | none => rfl
    | some endpoint =>
        obtain ⟨value,finalStore⟩ := endpoint
        exact False.elim (impossible value finalStore (evaluateClosedSourceBody?_sound actual))
  · intro absent
    exact absent _

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.ClosedSourceDataDepthDecisionProperties`
-/

/- Exact finite search on the independently admitted data-expression syntax.
No lookup, literal validity or runtime typing premise guarantees success.
All absence claims concern this existing successful-evaluation judgment only. -/
set_option autoImplicit false
namespace Solcore.Frontend

/-- At every sufficient source depth, the actual result and entire final store
agree exactly with the original judgment over arbitrary mixed runtime inputs. -/
theorem ClosedSourceDataExpression.evaluate_at_depthBound_iff
    {source : Syntax.Expr} (fragment : ClosedSourceDataExpression source)
    {owner : Resolved.DeclarationId} {names : LocalNameTable}
    {captured : Resolved.LocalScope RuntimeValue} {initialStore finalStore : List RuntimeValue}
    {value : RuntimeValue} {budget : Nat}
    (enough : closedSourceDataDepthBound source ≤ budget) :
    evaluateClosedSourceExpression? budget owner names captured initialStore source =
      some (value,finalStore) ↔
    ClosedSourceExpressionEvaluates owner names captured initialStore source value finalStore :=
  ⟨evaluateClosedSourceExpression?_sound,fun original => fragment.evaluates_at_depthBound original enough⟩

/-- Whole Option stability includes semantic failure, not only successful values.
The bound is sufficient; a selected short-circuit path may need much less depth. -/
theorem ClosedSourceDataExpression.evaluate_depth_stable
    {source : Syntax.Expr} (fragment : ClosedSourceDataExpression source)
    (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (initialStore : List RuntimeValue)
    {budget : Nat} (enough : closedSourceDataDepthBound source ≤ budget) :
    evaluateClosedSourceExpression? budget owner names captured initialStore source =
      evaluateClosedSourceExpression? (closedSourceDataDepthBound source)
        owner names captured initialStore source := by
  cases low : evaluateClosedSourceExpression? (closedSourceDataDepthBound source)
      owner names captured initialStore source with
  | none =>
      cases high : evaluateClosedSourceExpression? budget owner names captured initialStore source with
      | none => rfl
      | some endpoint =>
          obtain ⟨value,finalStore⟩ := endpoint
          have atBound := fragment.evaluates_at_depthBound
            (evaluateClosedSourceExpression?_sound high) (Nat.le_refl _)
          rw [low] at atBound
          cases atBound
  | some endpoint =>
      obtain ⟨value,finalStore⟩ := endpoint
      exact evaluateClosedSourceExpression?_monotone enough low

/-- Failure at a sufficient depth excludes every original successful endpoint.
It does not classify missing values, wrong payloads or invalid literal spellings. -/
theorem ClosedSourceDataExpression.evaluate_depth_none_iff
    {source : Syntax.Expr} (fragment : ClosedSourceDataExpression source)
    (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (initialStore : List RuntimeValue)
    {budget : Nat} (enough : closedSourceDataDepthBound source ≤ budget) :
    evaluateClosedSourceExpression? budget owner names captured initialStore source = none ↔
      ∀ value finalStore, ¬ ClosedSourceExpressionEvaluates owner names captured
        initialStore source value finalStore := by
  constructor
  · intro absent value finalStore original
    have accepted := fragment.evaluates_at_depthBound original enough
    rw [absent] at accepted
    cases accepted
  · intro impossible
    cases actual : evaluateClosedSourceExpression? budget owner names captured initialStore source with
    | none => rfl
    | some endpoint =>
        obtain ⟨value,finalStore⟩ := endpoint
        exact False.elim (impossible value finalStore (evaluateClosedSourceExpression?_sound actual))

/-- A single sufficient search decides whether any budget could succeed on this
gated syntax; no analogous conclusion is claimed for arbitrary source calls. -/
theorem ClosedSourceDataExpression.evaluate_depth_none_iff_all_budgets
    {source : Syntax.Expr} (fragment : ClosedSourceDataExpression source)
    (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (initialStore : List RuntimeValue) :
    evaluateClosedSourceExpression? (closedSourceDataDepthBound source)
        owner names captured initialStore source = none ↔
      ∀ budget, evaluateClosedSourceExpression? budget owner names captured initialStore source = none := by
  constructor
  · intro absent budget
    have impossible := (fragment.evaluate_depth_none_iff owner names captured initialStore (Nat.le_refl _)).mp absent
    cases actual : evaluateClosedSourceExpression? budget owner names captured initialStore source with
    | none => rfl
    | some endpoint =>
        obtain ⟨value,finalStore⟩ := endpoint
        exact False.elim (impossible value finalStore (evaluateClosedSourceExpression?_sound actual))
  · intro absent
    exact absent _

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.ClosedSourceEvaluatorStoreProperties`
-/

/- Exact store replay at the same finite budget. The private proof transports
success directly through the joint evaluator recursion; reversing that transport
retains None. Captures, saved lexical fields and opaque values are unchanged. -/
set_option autoImplicit false
namespace Solcore.Frontend

private theorem simultaneous_replay (budget : Nat) :
    (∀ owner names captured store source value finalStore replacement,
      evaluateClosedSourceExpression? budget owner names captured store source = some (value, finalStore) →
      evaluateClosedSourceExpression? budget owner names captured replacement source = some (value, replacement)) ∧
    (∀ owner names captured store source value finalStore replacement,
      evaluateClosedSourceBody? budget owner names captured store source = some (value, finalStore) →
      evaluateClosedSourceBody? budget owner names captured replacement source = some (value, replacement)) := by
  induction budget with
  | zero =>
      constructor <;> intro owner names captured store source value finalStore replacement accepted
      · simp only [evaluateClosedSourceExpression?, reduceCtorEq] at accepted
      · simp only [evaluateClosedSourceBody?, reduceCtorEq] at accepted
  | succ n ih =>
      constructor
      · intro owner names captured store source value finalStore replacement accepted
        rcases source with ⟨span, payload⟩
        cases payload <;> try (solve |
          simp only [evaluateClosedSourceExpression?, bind, Option.bind_eq_some_iff,
            pure, Option.some.injEq, Prod.mk.injEq] at accepted ⊢
          obtain ⟨actual, computed, rfl, rfl⟩ := accepted
          exact ⟨actual, computed, rfl, True.intro⟩)
        case identifier name =>
          simp only [evaluateClosedSourceExpression?, bind, Option.bind_eq_some_iff,
            pure, Option.some.injEq, Prod.mk.injEq] at accepted ⊢
          obtain ⟨id, named, actual, found, rfl, rfl⟩ := accepted
          exact ⟨id, named, actual, found, rfl, True.intro⟩
        case group inner =>
          rw [evaluateClosedSourceExpression?] at accepted ⊢
          exact ih.1 _ _ _ _ _ _ _ replacement accepted
        case tuple elements =>
          rcases elements with ⟨tupleSpan, children⟩
          cases children with
          | nil =>
              simp only [evaluateClosedSourceExpression?, Option.some.injEq, Prod.mk.injEq] at accepted
              obtain ⟨rfl, rfl⟩ := accepted
              simp only [evaluateClosedSourceExpression?]
          | cons left remaining =>
              cases remaining with
              | nil => simp only [evaluateClosedSourceExpression?, sourceUnaryLambdaShape?, bind, Option.bind_none, reduceCtorEq] at accepted
              | cons right tail =>
                  cases tail with
                  | nil =>
                      simp only [evaluateClosedSourceExpression?, bind, Option.bind_eq_some_iff,
                        pure, Option.some.injEq, Prod.mk.injEq] at accepted
                      obtain ⟨⟨lv, middleStore⟩, leftResult, ⟨rv, finalStore⟩, rightResult, rfl, rfl⟩ := accepted
                      rw [evaluateClosedSourceExpression?]
                      simp only [ih.1 _ _ _ _ _ _ _ replacement leftResult, ih.1 _ _ _ _ _ _ _ replacement rightResult,
                        bind, Option.bind_some, pure]
                  | cons third rest =>
                      simp only [evaluateClosedSourceExpression?, bind, Option.bind_eq_some_iff,
                        pure, Option.some.injEq, Prod.mk.injEq] at accepted
                      obtain ⟨⟨head, middleStore⟩, headResult, ⟨tail, finalStore⟩, tailResult, rfl, rfl⟩ := accepted
                      rw [evaluateClosedSourceExpression?]
                      simp only [ih.1 _ _ _ _ _ _ _ replacement headResult, ih.1 _ _ _ _ _ _ _ replacement tailResult,
                        bind, Option.bind_some, pure]
        case conditional condition question thenBranch colon elseBranch =>
          simp only [evaluateClosedSourceExpression?, bind, Option.bind_eq_some_iff] at accepted
          obtain ⟨⟨actual, middleStore⟩, conditionResult, selectedResult⟩ := accepted
          cases actual <;> simp only [reduceCtorEq] at selectedResult
          rename_i choice
          rw [evaluateClosedSourceExpression?]
          simp only [ih.1 _ _ _ _ _ _ _ replacement conditionResult, bind, Option.bind_some]
          exact ih.1 _ _ _ _ _ _ _ replacement selectedResult
        case unary operator operand =>
          rcases operator with ⟨operatorSpan, operator⟩
          cases operator with
          | logicalNot =>
              simp only [evaluateClosedSourceExpression?, bind, Option.bind_eq_some_iff] at accepted
              obtain ⟨⟨actual, finalStore⟩, child, result⟩ := accepted
              cases actual <;>
                simp only [reduceCtorEq, pure, Option.some.injEq, Prod.mk.injEq] at result
              obtain ⟨rfl, rfl⟩ := result
              rw [evaluateClosedSourceExpression?]
              simp only [ih.1 _ _ _ _ _ _ _ replacement child, bind, Option.bind_some, pure]
          | bitNot =>
              simp only [evaluateClosedSourceExpression?, bind, Option.bind_eq_some_iff] at accepted
              obtain ⟨⟨actual, finalStore⟩, child, result⟩ := accepted
              cases actual <;>
                simp only [reduceCtorEq, pure, Option.some.injEq, Prod.mk.injEq] at result
              obtain ⟨rfl, rfl⟩ := result
              rw [evaluateClosedSourceExpression?]
              simp only [ih.1 _ _ _ _ _ _ _ replacement child, bind, Option.bind_some, pure]
        case binary left operator right =>
          rcases operator with ⟨operatorSpan, operator⟩
          cases operator
          case logicalAnd =>
            simp only [evaluateClosedSourceExpression?, bind, Option.bind_eq_some_iff] at accepted
            obtain ⟨⟨actual, middleStore⟩, leftResult, result⟩ := accepted
            cases actual <;> simp only [reduceCtorEq] at result
            rename_i choice
            rw [evaluateClosedSourceExpression?]
            simp only [ih.1 _ _ _ _ _ _ _ replacement leftResult, bind, Option.bind_some]
            cases choice <;> simp only [Bool.false_eq_true, ↓reduceIte] at result ⊢
            · simp only [pure, Option.some.injEq, Prod.mk.injEq] at result
              obtain ⟨rfl, rfl⟩ := result
              rfl
            · exact ih.1 _ _ _ _ _ _ _ replacement result
          case logicalOr =>
            simp only [evaluateClosedSourceExpression?, bind, Option.bind_eq_some_iff] at accepted
            obtain ⟨⟨actual, middleStore⟩, leftResult, result⟩ := accepted
            cases actual <;> simp only [reduceCtorEq] at result
            rename_i choice
            rw [evaluateClosedSourceExpression?]
            simp only [ih.1 _ _ _ _ _ _ _ replacement leftResult, bind, Option.bind_some]
            cases choice <;> simp only [Bool.false_eq_true, ↓reduceIte] at result ⊢
            · exact ih.1 _ _ _ _ _ _ _ replacement result
            · simp only [pure, Option.some.injEq, Prod.mk.injEq] at result
              obtain ⟨rfl, rfl⟩ := result
              rfl
          all_goals
            simp only [evaluateClosedSourceExpression?, bind, Option.bind_eq_some_iff] at accepted
            obtain ⟨⟨leftActual, middleStore⟩, leftResult, result⟩ := accepted
            cases leftActual <;> simp only [reduceCtorEq, Option.bind_eq_some_iff] at result
            obtain ⟨⟨rightActual, finalStore⟩, rightResult, result⟩ := result
            cases rightActual <;>
              simp only [reduceCtorEq, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at result
            obtain ⟨coreValue, meaning, rfl, rfl⟩ := result
            simp only [evaluateClosedSourceExpression?,
              ih.1 _ _ _ _ _ _ _ replacement leftResult, ih.1 _ _ _ _ _ _ _ replacement rightResult,
              meaning, bind, Option.bind_some, pure]
        case call callee arguments =>
          rcases arguments with ⟨argumentsSpan, arguments⟩
          cases arguments with
          | nil => simp only [evaluateClosedSourceExpression?, sourceUnaryLambdaShape?, bind, Option.bind_none, reduceCtorEq] at accepted
          | cons argument rest =>
              cases rest with
              | cons _ _ => simp only [evaluateClosedSourceExpression?, sourceUnaryLambdaShape?, bind, Option.bind_none, reduceCtorEq] at accepted
              | nil =>
                  simp only [evaluateClosedSourceExpression?, bind, Option.bind_eq_some_iff] at accepted
                  obtain ⟨⟨function, calleeStore⟩, calleeResult,
                    ⟨argumentValue, argumentStore⟩, argumentResult, result⟩ := accepted
                  cases function <;> simp only [reduceCtorEq, Option.bind_eq_some_iff] at result
                  obtain ⟨⟨name, body⟩, shape, bodyResult⟩ := result
                  rw [evaluateClosedSourceExpression?]
                  simp only [ih.1 _ _ _ _ _ _ _ replacement calleeResult, ih.1 _ _ _ _ _ _ _ replacement argumentResult,
                    shape, bind, Option.bind_some]
                  exact ih.2 _ _ _ _ _ _ _ replacement bodyResult
      · intro owner names captured store source value finalStore replacement accepted
        rcases source with ⟨blockSpan, statements⟩
        cases statements with
        | nil => simp only [evaluateClosedSourceBody?, reduceCtorEq] at accepted
        | cons statement rest =>
            rcases statement with ⟨statementSpan, payload⟩
            cases payload <;> try (solve | simp only [evaluateClosedSourceBody?, reduceCtorEq] at accepted)
            case returnStmt returned =>
                cases rest with
                | cons _ _ => simp only [evaluateClosedSourceBody?, reduceCtorEq] at accepted
                | nil =>
                    cases returned with
                    | none =>
                        simp only [evaluateClosedSourceBody?, Option.some.injEq, Prod.mk.injEq] at accepted
                        obtain ⟨rfl, rfl⟩ := accepted
                        simp only [evaluateClosedSourceBody?]
                    | some child =>
                        rw [evaluateClosedSourceBody?] at accepted ⊢
                        exact ih.1 _ _ _ _ _ _ _ replacement accepted
            case block inner =>
                cases rest with
                | cons _ _ => simp only [evaluateClosedSourceBody?, reduceCtorEq] at accepted
                | nil =>
                    rw [evaluateClosedSourceBody?] at accepted ⊢
                    exact ih.2 _ _ _ _ _ _ _ replacement accepted
            case letDecl name annotation initializer =>
                cases initializer with
                | none => simp only [evaluateClosedSourceBody?, reduceCtorEq] at accepted
                | some initializer =>
                    simp only [evaluateClosedSourceBody?, bind, Option.bind_eq_some_iff] at accepted
                    obtain ⟨⟨boundValue, middleStore⟩, head, tail⟩ := accepted
                    rw [evaluateClosedSourceBody?]
                    simp only [ih.1 _ _ _ _ _ _ _ replacement head, bind, Option.bind_some]
                    exact ih.2 _ _ _ _ _ _ _ replacement tail
            case expression child terminated =>
                cases terminated with
                | false => simp only [evaluateClosedSourceBody?, reduceCtorEq] at accepted
                | true =>
                    simp only [evaluateClosedSourceBody?, bind, Option.bind_eq_some_iff] at accepted
                    obtain ⟨⟨discarded, middleStore⟩, head, tail⟩ := accepted
                    rw [evaluateClosedSourceBody?]
                    simp only [ih.1 _ _ _ _ _ _ _ replacement head, bind, Option.bind_some]
                    exact ih.2 _ _ _ _ _ _ _ replacement tail
            case ifThen condition thenBody elseBody =>
                cases rest with
                | cons _ _ => simp only [evaluateClosedSourceBody?, reduceCtorEq] at accepted
                | nil =>
                    cases elseBody with
                    | none => simp only [evaluateClosedSourceBody?, reduceCtorEq] at accepted
                    | some elseBody =>
                        simp only [evaluateClosedSourceBody?, bind, Option.bind_eq_some_iff] at accepted
                        obtain ⟨⟨actual, middleStore⟩, conditionResult, selectedResult⟩ := accepted
                        cases actual <;> simp only [reduceCtorEq] at selectedResult
                        rename_i choice
                        rw [evaluateClosedSourceBody?]
                        simp only [ih.1 _ _ _ _ _ _ _ replacement conditionResult, bind, Option.bind_some]
                        cases choice <;> simp only [Bool.false_eq_true, ↓reduceIte] at selectedResult ⊢
                        · exact ih.2 _ _ _ _ _ _ _ replacement selectedResult
                        · exact ih.2 _ _ _ _ _ _ _ replacement selectedResult
            case matchWith scrutinees arms =>
                cases rest with
                | cons _ _ => simp only [evaluateClosedSourceBody?, reduceCtorEq] at accepted
                | nil =>
                    rcases scrutinees with ⟨scrutineeSpan, ⟨scrutinee, additional⟩⟩
                    rcases arms with ⟨armsSpan, ⟨cases, defaultBody⟩⟩
                    cases additional with
                    | cons _ _ => simp only [evaluateClosedSourceBody?, reduceCtorEq] at accepted
                    | nil =>
                        simp only [evaluateClosedSourceBody?, bind, Option.bind_eq_some_iff] at accepted
                        obtain ⟨⟨actual, middleStore⟩, scrutineeResult,
                          ⟨selected, tests⟩, choice, selectedResult⟩ := accepted
                        rw [evaluateClosedSourceBody?]
                        simp only [ih.1 _ _ _ _ _ _ _ replacement scrutineeResult, choice, bind, Option.bind_some]
                        exact ih.2 _ _ _ _ _ _ _ replacement selectedResult

/-- Replacing only the store preserves the complete finite expression outcome. -/
theorem evaluateClosedSourceExpression?_replay_store
    (budget : Nat) (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue)
    (initialStore replacement : List RuntimeValue) (source : Syntax.Expr) :
    evaluateClosedSourceExpression? budget owner names captured replacement source =
      (evaluateClosedSourceExpression? budget owner names captured initialStore source).map
        (fun endpoint => (endpoint.1, replacement)) := by
  cases original : evaluateClosedSourceExpression? budget owner names captured initialStore source with
  | some endpoint =>
      exact (simultaneous_replay budget).1 _ _ _ _ _ _ _ replacement original
  | none =>
      cases replayed : evaluateClosedSourceExpression? budget owner names captured replacement source with
      | none => rfl
      | some endpoint =>
          have back := (simultaneous_replay budget).1 _ _ _ _ _ _ _ initialStore replayed
          rw [original] at back
          cases back

/-- Body replay also retains None, with exactly the original finite budget. -/
theorem evaluateClosedSourceBody?_replay_store
    (budget : Nat) (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue)
    (initialStore replacement : List RuntimeValue) (source : Syntax.Block) :
    evaluateClosedSourceBody? budget owner names captured replacement source =
      (evaluateClosedSourceBody? budget owner names captured initialStore source).map
        (fun endpoint => (endpoint.1, replacement)) := by
  cases original : evaluateClosedSourceBody? budget owner names captured initialStore source with
  | some endpoint =>
      exact (simultaneous_replay budget).2 _ _ _ _ _ _ _ replacement original
  | none =>
      cases replayed : evaluateClosedSourceBody? budget owner names captured replacement source with
      | none => rfl
      | some endpoint =>
          have back := (simultaneous_replay budget).2 _ _ _ _ _ _ _ initialStore replayed
          rw [original] at back
          cases back

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.ClosedSourceEvaluatorThresholdProperties`
-/

/- Finite original derivations have a positive exact depth cutoff, not a total search bound. -/
set_option autoImplicit false
namespace Solcore.Frontend

private theorem exact_threshold_of_success {α : Type} (f : Nat → Option α)
    (zero : f 0 = none)
    (monotone : ∀ {small large value}, small ≤ large →
      f small = some value → f large = some value)
    {budget : Nat} {value : α} (accepted : f budget = some value) :
    ∃ required : Nat, 0 < required ∧ ∀ n,
      f n = if required ≤ n then some value else none := by
  induction budget with
  | zero => rw [zero] at accepted; cases accepted
  | succ budget ih =>
      cases previous : f budget with
      | none =>
          refine ⟨budget + 1, Nat.zero_lt_succ _, ?_⟩
          intro n
          by_cases order : budget + 1 ≤ n
          · simp only [if_pos order]
            exact monotone order accepted
          · simp only [if_neg order]
            cases actual : f n with
            | none => rfl
            | some result =>
                have impossible := monotone (show n ≤ budget by omega) actual
                rw [previous] at impossible
                cases impossible
      | some result =>
          have same : result = value :=
            Option.some.inj ((monotone (Nat.le_succ budget) previous).symm.trans accepted)
          subst result
          exact ih previous

/-- A finite original expression derivation has a positive, hole-free successful-depth range. -/
theorem ClosedSourceExpressionEvaluates.exact_depth_threshold
    {owner : Resolved.DeclarationId} {names : LocalNameTable}
    {captured : Resolved.LocalScope RuntimeValue} {initialStore finalStore : List RuntimeValue}
    {source : Syntax.Expr} {value : RuntimeValue}
    (evaluated : ClosedSourceExpressionEvaluates owner names captured initialStore source value finalStore) :
    ∃ required : Nat, 0 < required ∧ ∀ budget,
      evaluateClosedSourceExpression? budget owner names captured initialStore source =
        if required ≤ budget then some (value, finalStore) else none := by
  obtain ⟨budget, accepted⟩ := evaluateClosedSourceExpression?_eventually_complete evaluated
  apply exact_threshold_of_success
    (fun n => evaluateClosedSourceExpression? n owner names captured initialStore source)
    (by simp only [evaluateClosedSourceExpression?]) ?_ (accepted budget (Nat.le_refl _))
  intro small large endpoint order result
  obtain ⟨actual, actualStore⟩ := endpoint
  exact evaluateClosedSourceExpression?_monotone order result

/-- A finite original body derivation has a positive, hole-free successful-depth range. -/
theorem ClosedSourceBodyEvaluates.exact_depth_threshold
    {owner : Resolved.DeclarationId} {names : LocalNameTable}
    {captured : Resolved.LocalScope RuntimeValue} {initialStore finalStore : List RuntimeValue}
    {source : Syntax.Block} {value : RuntimeValue}
    (evaluated : ClosedSourceBodyEvaluates owner names captured initialStore source value finalStore) :
    ∃ required : Nat, 0 < required ∧ ∀ budget,
      evaluateClosedSourceBody? budget owner names captured initialStore source =
        if required ≤ budget then some (value, finalStore) else none := by
  obtain ⟨budget, accepted⟩ := evaluateClosedSourceBody?_eventually_complete evaluated
  apply exact_threshold_of_success
    (fun n => evaluateClosedSourceBody? n owner names captured initialStore source)
    (by simp only [evaluateClosedSourceBody?]) ?_ (accepted budget (Nat.le_refl _))
  intro small large endpoint order result
  obtain ⟨actual, actualStore⟩ := endpoint
  exact evaluateClosedSourceBody?_monotone order result

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.ClosedSourceOwnerBudgetProperties`
-/

/- Full finite observations reflect actual endpoints, not assumed endpoint images.
Successful originals retain one positive cutoff for both complete runners. -/
set_option autoImplicit false
namespace Solcore.Frontend
section
variable (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
variable (injective : Function.Injective mapping)
include injective

/-- Every actual mapped expression success has a complete preimage at the same budget. -/
theorem evaluateClosedSourceExpression?_mapOwners_some_iff_exists
    {budget owner names captured store source value final} :
    evaluateClosedSourceExpression? budget (mapping owner) (LocalNameTable.mapIds (ownerLocalIdMap mapping) names)
      (mapRuntimeCapturedOwners mapping captured) (store.map (RuntimeValue.mapOwners mapping)) source = some (value,final) ↔
    ∃ before beforeStore, evaluateClosedSourceExpression? budget owner names captured store source = some (before,beforeStore) ∧
      value = before.mapOwners mapping ∧ final = beforeStore.map (RuntimeValue.mapOwners mapping) := by
  rw [evaluateClosedSourceExpression?_mapOwners mapping injective,Option.map_eq_some_iff]
  constructor
  · rintro ⟨⟨before,beforeStore⟩,ran,same⟩
    exact ⟨before,beforeStore,ran,(congrArg Prod.fst same).symm,(congrArg Prod.snd same).symm⟩
  · rintro ⟨before,beforeStore,ran,rfl,rfl⟩
    exact ⟨(before,beforeStore),ran,rfl⟩

/-- Every actual mapped body success has a complete preimage at the same budget. -/
theorem evaluateClosedSourceBody?_mapOwners_some_iff_exists
    {budget owner names captured store source value final} :
    evaluateClosedSourceBody? budget (mapping owner) (LocalNameTable.mapIds (ownerLocalIdMap mapping) names)
      (mapRuntimeCapturedOwners mapping captured) (store.map (RuntimeValue.mapOwners mapping)) source = some (value,final) ↔
    ∃ before beforeStore, evaluateClosedSourceBody? budget owner names captured store source = some (before,beforeStore) ∧
      value = before.mapOwners mapping ∧ final = beforeStore.map (RuntimeValue.mapOwners mapping) := by
  rw [evaluateClosedSourceBody?_mapOwners mapping injective,Option.map_eq_some_iff]
  constructor
  · rintro ⟨⟨before,beforeStore⟩,ran,same⟩
    exact ⟨before,beforeStore,ran,(congrArg Prod.fst same).symm,(congrArg Prod.snd same).symm⟩
  · rintro ⟨before,beforeStore,ran,rfl,rfl⟩
    exact ⟨(before,beforeStore),ran,rfl⟩

/-- Finite expression absence is equivalent at the same budget, without classifying its cause. -/
theorem evaluateClosedSourceExpression?_mapOwners_none_iff
    (budget : Nat) (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue) (source : Syntax.Expr) :
    evaluateClosedSourceExpression? budget (mapping owner) (LocalNameTable.mapIds (ownerLocalIdMap mapping) names)
      (mapRuntimeCapturedOwners mapping captured) (store.map (RuntimeValue.mapOwners mapping)) source = none ↔
    evaluateClosedSourceExpression? budget owner names captured store source = none := by
  rw [evaluateClosedSourceExpression?_mapOwners mapping injective,Option.map_eq_none_iff]

/-- Finite body absence is equivalent at the same budget, with no success or cutoff premise. -/
theorem evaluateClosedSourceBody?_mapOwners_none_iff
    (budget : Nat) (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue) (source : Syntax.Block) :
    evaluateClosedSourceBody? budget (mapping owner) (LocalNameTable.mapIds (ownerLocalIdMap mapping) names)
      (mapRuntimeCapturedOwners mapping captured) (store.map (RuntimeValue.mapOwners mapping)) source = none ↔
    evaluateClosedSourceBody? budget owner names captured store source = none := by
  rw [evaluateClosedSourceBody?_mapOwners mapping injective,Option.map_eq_none_iff]

/-- A successful original expression has one positive exact cutoff shared by both complete runners. -/
theorem ClosedSourceExpressionEvaluates.mapOwners_exact_depth_threshold
    {owner names captured store source value final}
    (original : ClosedSourceExpressionEvaluates owner names captured store source value final) :
    ∃ required : Nat, 0 < required ∧ ∀ budget,
      (evaluateClosedSourceExpression? budget owner names captured store source =
        if required ≤ budget then some (value,final) else none) ∧
      (evaluateClosedSourceExpression? budget (mapping owner) (LocalNameTable.mapIds (ownerLocalIdMap mapping) names)
        (mapRuntimeCapturedOwners mapping captured) (store.map (RuntimeValue.mapOwners mapping)) source =
        if required ≤ budget then some (value.mapOwners mapping,final.map (RuntimeValue.mapOwners mapping)) else none) := by
  obtain ⟨required,positive,cutoff⟩ := original.exact_depth_threshold
  refine ⟨required,positive,fun budget => ⟨cutoff budget,?_⟩⟩
  rw [evaluateClosedSourceExpression?_mapOwners mapping injective,cutoff budget]
  split <;> rfl

/-- A successful original body has the same exact positive cutoff after owner relabeling. -/
theorem ClosedSourceBodyEvaluates.mapOwners_exact_depth_threshold
    {owner names captured store source value final}
    (original : ClosedSourceBodyEvaluates owner names captured store source value final) :
    ∃ required : Nat, 0 < required ∧ ∀ budget,
      (evaluateClosedSourceBody? budget owner names captured store source =
        if required ≤ budget then some (value,final) else none) ∧
      (evaluateClosedSourceBody? budget (mapping owner) (LocalNameTable.mapIds (ownerLocalIdMap mapping) names)
        (mapRuntimeCapturedOwners mapping captured) (store.map (RuntimeValue.mapOwners mapping)) source =
        if required ≤ budget then some (value.mapOwners mapping,final.map (RuntimeValue.mapOwners mapping)) else none) := by
  obtain ⟨required,positive,cutoff⟩ := original.exact_depth_threshold
  refine ⟨required,positive,fun budget => ⟨cutoff budget,?_⟩⟩
  rw [evaluateClosedSourceBody?_mapOwners mapping injective,cutoff budget]
  split <;> rfl

end
end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.ClosedSourceOwnerProperties`
-/

/- Transport actual original successes, including every saved closure field.
Only owner injectivity is required: no lexical uniqueness, typing or world premise. -/
set_option autoImplicit false
namespace Solcore.Frontend

private theorem mapOwners_unit (mapping : Resolved.DeclarationId → Resolved.DeclarationId) :
    RuntimeValue.mapOwners mapping .unit = .unit := by simp only [RuntimeValue.mapOwners]

private theorem mapOwners_bool (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (value : Bool) :
    RuntimeValue.mapOwners mapping (.bool value) = .bool value := by simp only [RuntimeValue.mapOwners]

private theorem mapOwners_word (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (value : Core.Word) :
    RuntimeValue.mapOwners mapping (.word value) = .word value := by simp only [RuntimeValue.mapOwners]

private theorem mapOwners_pair (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (left right : RuntimeValue) :
    RuntimeValue.mapOwners mapping (.pair left right) = .pair (left.mapOwners mapping) (right.mapOwners mapping) := by
  simp only [RuntimeValue.mapOwners]

section
variable (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
variable (injective : Function.Injective mapping)
include injective

/-- Every original expression success transports its complete value and store. -/
theorem ClosedSourceExpressionEvaluates.mapOwners
    {owner names captured initialStore source value finalStore}
    (original : ClosedSourceExpressionEvaluates owner names captured initialStore source value finalStore) :
    ClosedSourceExpressionEvaluates (mapping owner) (LocalNameTable.mapIds (ownerLocalIdMap mapping) names)
      (mapRuntimeCapturedOwners mapping captured) (initialStore.map (RuntimeValue.mapOwners mapping)) source
      (value.mapOwners mapping) (finalStore.map (RuntimeValue.mapOwners mapping)) := by
  induction original using ClosedSourceExpressionEvaluates.rec
    (motive_2 := fun owner names captured store source value final _ =>
      ClosedSourceBodyEvaluates (mapping owner) (LocalNameTable.mapIds (ownerLocalIdMap mapping) names)
        (mapRuntimeCapturedOwners mapping captured) (store.map (RuntimeValue.mapOwners mapping)) source
        (value.mapOwners mapping) (final.map (RuntimeValue.mapOwners mapping))) with
  | reference named found =>
    exact .reference ((LocalNameTable.lookup_mapIds_iff (ownerLocalIdMap mapping)
      (ownerLocalIdMap_injective mapping injective)).mpr named) (mapRuntimeCapturedOwners_lookup mapping injective found)
  | unit =>
    rw [mapOwners_unit]
    exact .unit
  | wordLiteral meaning =>
    rw [mapOwners_word]
    exact .wordLiteral meaning
  | group _ ih => exact .group ih
  | pair _ _ leftIH rightIH =>
    rw [mapOwners_pair]
    exact .pair leftIH rightIH
  | many _ _ headIH tailIH =>
    rw [mapOwners_pair]
    exact .many headIH tailIH
  | creation shape =>
    simp only [RuntimeValue.mapOwners_sourceClosure]
    exact .creation shape
  | call shape _ _ _ calleeIH argumentIH bodyIH =>
    simp only [RuntimeValue.mapOwners_sourceClosure] at calleeIH
    apply ClosedSourceExpressionEvaluates.call shape calleeIH argumentIH
    rw [freshLocalId_mapRuntimeNamesOwners mapping injective]
    simpa only [LocalNameTable.mapIds,
      mapRuntimeCapturedOwners,List.map_cons] using bodyIH
  | conditionalTrue _ _ conditionIH branchIH =>
    simp only [mapOwners_bool] at conditionIH
    exact .conditionalTrue conditionIH branchIH
  | conditionalFalse _ _ conditionIH branchIH =>
    simp only [mapOwners_bool] at conditionIH
    exact .conditionalFalse conditionIH branchIH
  | logicalNot _ ih =>
    simp only [mapOwners_bool] at ih ⊢
    exact .logicalNot ih
  | bitNot _ ih =>
    simp only [mapOwners_word] at ih ⊢
    exact .bitNot ih
  | andTrue _ _ leftIH rightIH =>
    simp only [mapOwners_bool] at leftIH
    exact .andTrue leftIH rightIH
  | andFalse _ ih =>
    simp only [mapOwners_bool] at ih ⊢
    exact .andFalse ih
  | orTrue _ ih =>
    simp only [mapOwners_bool] at ih ⊢
    exact .orTrue ih
  | orFalse _ _ leftIH rightIH =>
    simp only [mapOwners_bool] at leftIH
    exact .orFalse leftIH rightIH
  | strictWordBinary _ _ meaning leftIH rightIH =>
    simp only [mapOwners_word] at leftIH rightIH
    rw [RuntimeValue.mapOwners_ofCore]
    exact .strictWordBinary leftIH rightIH meaning
  | bare =>
    rw [mapOwners_unit]
    exact .bare
  | expression _ ih => exact .expression ih
  | block _ ih => exact .block ih
  | binding _ _ initializerIH tailIH =>
    apply ClosedSourceBodyEvaluates.binding initializerIH
    rw [freshLocalId_mapRuntimeNamesOwners mapping injective]
    simpa only [LocalNameTable.mapIds,
      mapRuntimeCapturedOwners,List.map_cons] using tailIH
  | inferred _ _ initializerIH tailIH =>
    apply ClosedSourceBodyEvaluates.inferred initializerIH
    rw [freshLocalId_mapRuntimeNamesOwners mapping injective]
    simpa only [LocalNameTable.mapIds,
      mapRuntimeCapturedOwners,List.map_cons] using tailIH
  | discard _ _ expressionIH tailIH => exact .discard expressionIH tailIH
  | ifTrue _ _ conditionIH branchIH =>
    simp only [mapOwners_bool] at conditionIH
    exact .ifTrue conditionIH branchIH
  | ifFalse _ _ conditionIH branchIH =>
    simp only [mapOwners_bool] at conditionIH
    exact .ifFalse conditionIH branchIH
  | wordMatch _ choice _ scrutineeIH branchIH =>
    exact .wordMatch scrutineeIH ((runtimeWordMatchChooses_mapOwners_iff mapping).mpr choice) branchIH

/-- Every original body success transports fresh binding, selected branch and full endpoint. -/
theorem ClosedSourceBodyEvaluates.mapOwners
    {owner names captured initialStore source value finalStore}
    (original : ClosedSourceBodyEvaluates owner names captured initialStore source value finalStore) :
    ClosedSourceBodyEvaluates (mapping owner) (LocalNameTable.mapIds (ownerLocalIdMap mapping) names)
      (mapRuntimeCapturedOwners mapping captured) (initialStore.map (RuntimeValue.mapOwners mapping)) source
      (value.mapOwners mapping) (finalStore.map (RuntimeValue.mapOwners mapping)) := by
  have independent := closedSourceBodyEvaluates_iff.mp original
  clear original
  induction independent with
  | bare =>
    rw [mapOwners_unit]
    exact .bare
  | expression child => exact .expression (child.mapOwners mapping injective)
  | block _ ih => exact .block ih
  | binding initializer _ tailIH =>
    apply ClosedSourceBodyEvaluates.binding (initializer.mapOwners mapping injective)
    rw [freshLocalId_mapRuntimeNamesOwners mapping injective]
    simpa only [LocalNameTable.mapIds,
      mapRuntimeCapturedOwners,List.map_cons] using tailIH
  | inferred initializer _ tailIH =>
    apply ClosedSourceBodyEvaluates.inferred (initializer.mapOwners mapping injective)
    rw [freshLocalId_mapRuntimeNamesOwners mapping injective]
    simpa only [LocalNameTable.mapIds,
      mapRuntimeCapturedOwners,List.map_cons] using tailIH
  | discard child _ tailIH => exact .discard (child.mapOwners mapping injective) tailIH
  | ifTrue child _ branchIH =>
    have condition := child.mapOwners mapping injective
    simp only [mapOwners_bool] at condition
    exact .ifTrue condition branchIH
  | ifFalse child _ branchIH =>
    have condition := child.mapOwners mapping injective
    simp only [mapOwners_bool] at condition
    exact .ifFalse condition branchIH
  | wordMatch child choice _ branchIH =>
    exact .wordMatch (child.mapOwners mapping injective) ((runtimeWordMatchChooses_mapOwners_iff mapping).mpr choice) branchIH

end
end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.ClosedSourceOwnerReflectionProperties`
-/

/- Actual successful mapped endpoints have original preimages. No inverse owner
map, surjectivity or preselected endpoint-image premise is used to reflect them. -/
set_option autoImplicit false
namespace Solcore.Frontend
section
variable (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
variable (injective : Function.Injective mapping)
include injective

/-- Every actual original expression endpoint in the mapped environment has an original preimage. -/
theorem ClosedSourceExpressionEvaluates.mapOwners_iff_exists
    {owner names captured store source value final} :
    ClosedSourceExpressionEvaluates (mapping owner) (LocalNameTable.mapIds (ownerLocalIdMap mapping) names)
      (mapRuntimeCapturedOwners mapping captured) (store.map (RuntimeValue.mapOwners mapping)) source value final ↔
    ∃ before beforeStore, ClosedSourceExpressionEvaluates owner names captured store source before beforeStore ∧
      value = before.mapOwners mapping ∧ final = beforeStore.map (RuntimeValue.mapOwners mapping) := by
  constructor
  · intro original
    obtain ⟨budget,eventual⟩ := evaluateClosedSourceExpression?_eventually_complete original
    have actual := eventual budget (Nat.le_refl _)
    rw [evaluateClosedSourceExpression?_mapOwners mapping injective,Option.map_eq_some_iff] at actual
    obtain ⟨⟨before,beforeStore⟩,evaluated,same⟩ := actual
    exact ⟨before,beforeStore,evaluateClosedSourceExpression?_sound evaluated,
      (congrArg Prod.fst same).symm,(congrArg Prod.snd same).symm⟩
  · rintro ⟨before,beforeStore,original,rfl,rfl⟩
    exact original.mapOwners mapping injective

/-- Actual mapped body successes reflect complete values and final stores without an endpoint assumption. -/
theorem ClosedSourceBodyEvaluates.mapOwners_iff_exists
    {owner names captured store source value final} :
    ClosedSourceBodyEvaluates (mapping owner) (LocalNameTable.mapIds (ownerLocalIdMap mapping) names)
      (mapRuntimeCapturedOwners mapping captured) (store.map (RuntimeValue.mapOwners mapping)) source value final ↔
    ∃ before beforeStore, ClosedSourceBodyEvaluates owner names captured store source before beforeStore ∧
      value = before.mapOwners mapping ∧ final = beforeStore.map (RuntimeValue.mapOwners mapping) := by
  constructor
  · intro original
    obtain ⟨budget,eventual⟩ := evaluateClosedSourceBody?_eventually_complete original
    have actual := eventual budget (Nat.le_refl _)
    rw [evaluateClosedSourceBody?_mapOwners mapping injective,Option.map_eq_some_iff] at actual
    obtain ⟨⟨before,beforeStore⟩,evaluated,same⟩ := actual
    exact ⟨before,beforeStore,evaluateClosedSourceBody?_sound evaluated,
      (congrArg Prod.fst same).symm,(congrArg Prod.snd same).symm⟩
  · rintro ⟨before,beforeStore,original,rfl,rfl⟩
    exact original.mapOwners mapping injective

/-- Explicit mapped expression endpoints are equivalent to their original endpoints. -/
theorem ClosedSourceExpressionEvaluates.mapOwners_iff
    {owner names captured store source value final} :
    ClosedSourceExpressionEvaluates (mapping owner) (LocalNameTable.mapIds (ownerLocalIdMap mapping) names)
      (mapRuntimeCapturedOwners mapping captured) (store.map (RuntimeValue.mapOwners mapping)) source
      (value.mapOwners mapping) (final.map (RuntimeValue.mapOwners mapping)) ↔
    ClosedSourceExpressionEvaluates owner names captured store source value final := by
  rw [ClosedSourceExpressionEvaluates.mapOwners_iff_exists mapping injective]
  constructor
  · rintro ⟨before,beforeStore,original,values,stores⟩
    have valueSame := RuntimeValue.mapOwners_injective mapping injective values
    have storeSame := (List.map_inj_right (f := RuntimeValue.mapOwners mapping)
      (fun _ _ same => RuntimeValue.mapOwners_injective mapping injective same)).mp stores
    simpa only [valueSame,storeSame] using original
  · intro original
    exact ⟨value,final,original,rfl,rfl⟩

/-- Explicit mapped body endpoints are equivalent without requiring an onto owner map. -/
theorem ClosedSourceBodyEvaluates.mapOwners_iff
    {owner names captured store source value final} :
    ClosedSourceBodyEvaluates (mapping owner) (LocalNameTable.mapIds (ownerLocalIdMap mapping) names)
      (mapRuntimeCapturedOwners mapping captured) (store.map (RuntimeValue.mapOwners mapping)) source
      (value.mapOwners mapping) (final.map (RuntimeValue.mapOwners mapping)) ↔
    ClosedSourceBodyEvaluates owner names captured store source value final := by
  rw [ClosedSourceBodyEvaluates.mapOwners_iff_exists mapping injective]
  constructor
  · rintro ⟨before,beforeStore,original,values,stores⟩
    have valueSame := RuntimeValue.mapOwners_injective mapping injective values
    have storeSame := (List.map_inj_right (f := RuntimeValue.mapOwners mapping)
      (fun _ _ same => RuntimeValue.mapOwners_injective mapping injective same)).mp stores
    simpa only [valueSame,storeSame] using original
  · intro original
    exact ⟨value,final,original,rfl,rfl⟩

end
end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.ClosedSourceOwnerCoreExpressionProperties`
-/

/- Owner relabeling keeps embedded Core values literal. The whole old resolution
and lowering boundary remains explicit when reflecting arbitrary raw endpoints. -/
set_option autoImplicit false
namespace Solcore.Frontend

/-- Relabeling an embedded ordered environment changes keys but no Core payload. -/
theorem mapRuntimeCapturedOwners_ofCore
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (environment : Resolved.Environment) :
    mapRuntimeCapturedOwners mapping (environment.map (fun row => (row.1,RuntimeValue.ofCore row.2))) =
      (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) environment).map
        (fun row => (row.1,RuntimeValue.ofCore row.2)) := by
  simp only [mapRuntimeCapturedOwners,Resolved.LocalScope.mapIds,List.map_map,Function.comp_def,
    RuntimeValue.mapOwners_ofCore]

/-- Every element of an embedded Core store is fixed by owner relabeling. -/
theorem mapRuntimeStoreOwners_ofCore
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (store : Core.Store) :
    (store.map RuntimeValue.ofCore).map (RuntimeValue.mapOwners mapping) = store.map RuntimeValue.ofCore := by
  simp only [List.map_map,Function.comp_def,RuntimeValue.mapOwners_ofCore]

/-- Mapped resolution lowers to the literal old Core term and reflects every actual raw endpoint. -/
theorem ClosedSourceDataExpression.mapOwners_core_evaluates_iff
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (injective : Function.Injective mapping)
    {owner : Resolved.DeclarationId} {names : LocalNameTable} {environment : Resolved.Environment}
    {initialStore : Core.Store} {source : Syntax.Expr} {actualValue : RuntimeValue}
    {actualFinal : List RuntimeValue} (fragment : ClosedSourceDataExpression source)
    {resolved : Resolved.Expr} {core : Core.Expr} (resolution : ResolvesLocalExpression names source resolved)
    (lowered : Resolved.Lowers (Resolved.LocalScope.ids environment) resolved core) :
    ResolvesLocalExpression (LocalNameTable.mapIds (ownerLocalIdMap mapping) names) source
      (resolved.renameIds (ownerLocalIdMap mapping)) ∧
    Resolved.Lowers (Resolved.LocalScope.ids (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) environment))
      (resolved.renameIds (ownerLocalIdMap mapping)) core ∧
    (ClosedSourceExpressionEvaluates (mapping owner) (LocalNameTable.mapIds (ownerLocalIdMap mapping) names)
      ((Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) environment).map (fun row => (row.1,RuntimeValue.ofCore row.2)))
      (initialStore.map RuntimeValue.ofCore) source actualValue actualFinal ↔
    ∃ value finalStore, actualValue=RuntimeValue.ofCore value ∧ actualFinal=finalStore.map RuntimeValue.ofCore ∧
      Core.Evaluates (Resolved.LocalScope.values environment) initialStore core value finalStore) := by
  refine ⟨resolution.mapIds _,?_,?_⟩
  · rw [Resolved.LocalScope.ids_mapIds]
    exact (Resolved.lowers_renameIds_iff (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective)).mpr lowered
  · constructor
    · intro actual
      have mapped : ClosedSourceExpressionEvaluates (mapping owner) (LocalNameTable.mapIds (ownerLocalIdMap mapping) names)
          (mapRuntimeCapturedOwners mapping (environment.map (fun row => (row.1,RuntimeValue.ofCore row.2))))
          ((initialStore.map RuntimeValue.ofCore).map (RuntimeValue.mapOwners mapping)) source actualValue actualFinal := by
        simpa only [mapRuntimeCapturedOwners_ofCore,mapRuntimeStoreOwners_ofCore] using actual
      obtain ⟨before,beforeStore,original,values,stores⟩ :=
        (ClosedSourceExpressionEvaluates.mapOwners_iff_exists mapping injective).mp mapped
      obtain ⟨value,finalStore,beforeEq,beforeStoreEq,evaluated⟩ :=
        (fragment.core_evaluates_iff resolution lowered).mp original
      refine ⟨value,finalStore,?_,?_,evaluated⟩
      · simpa only [beforeEq,RuntimeValue.mapOwners_ofCore] using values
      · simpa only [beforeStoreEq,mapRuntimeStoreOwners_ofCore] using stores
    · rintro ⟨value,finalStore,rfl,rfl,evaluated⟩
      have original := (fragment.core_evaluates_iff (owner:=owner) resolution lowered).mpr
        ⟨value,finalStore,rfl,rfl,evaluated⟩
      simpa only [mapRuntimeCapturedOwners_ofCore,mapRuntimeStoreOwners_ofCore,RuntimeValue.mapOwners_ofCore] using
        original.mapOwners mapping injective

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.ClosedSourceOwnerCoreBodyProperties`
-/

/- Preserve the old complete shared-checker and exact runtime-ID premises.
An actual mapped result becomes a Core image only through the old gated bridge. -/
set_option autoImplicit false
namespace Solcore.Frontend

/-- Mapped body checking retains the same Core/type pair and complete actual-output image. -/
theorem ClosedSourceDataBody.mapOwners_core_evaluates_iff
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (injective : Function.Injective mapping)
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {environment : Resolved.Environment} {initialStore : Core.Store} {body : Syntax.Block}
    {actualValue : RuntimeValue} {actualFinal : List RuntimeValue} (fragment : ClosedSourceDataBody body)
    {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateComputationReturnTree? elaborateLocalExpression? types owner inputs body = some (core,type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids inputs.context) :
    elaborateComputationReturnTree? elaborateLocalExpression? types (mapping owner)
      (inputs.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective)) body = some (core,type) ∧
    Resolved.LocalScope.ids (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) environment) =
      Resolved.LocalScope.ids (inputs.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective)).context ∧
    (ClosedSourceBodyEvaluates (mapping owner)
      (inputs.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective)).names
      ((Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) environment).map (fun row => (row.1,RuntimeValue.ofCore row.2)))
      (initialStore.map RuntimeValue.ofCore) body actualValue actualFinal ↔
    ∃ value finalStore, actualValue=RuntimeValue.ofCore value ∧ actualFinal=finalStore.map RuntimeValue.ofCore ∧
      Core.Evaluates (Resolved.LocalScope.values environment) initialStore core value finalStore) := by
  refine ⟨?_,?_,?_⟩
  · rw [elaborateComputationReturnTree?_mapOwner mapping injective elaborateLocalExpression?
      (elaborateLocalExpression?_mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective))]
    exact accepted
  · simpa only [LocalTypeInputs.mapIds_context,Resolved.LocalScope.ids_mapIds] using
      congrArg (List.map (ownerLocalIdMap mapping)) sameIds
  · constructor
    · intro actual
      have mapped : ClosedSourceBodyEvaluates (mapping owner) (LocalNameTable.mapIds (ownerLocalIdMap mapping) inputs.names)
          (mapRuntimeCapturedOwners mapping (environment.map (fun row => (row.1,RuntimeValue.ofCore row.2))))
          ((initialStore.map RuntimeValue.ofCore).map (RuntimeValue.mapOwners mapping)) body actualValue actualFinal := by
        simpa only [LocalTypeInputs.mapIds_names,mapRuntimeCapturedOwners_ofCore,mapRuntimeStoreOwners_ofCore] using actual
      obtain ⟨before,beforeStore,original,values,stores⟩ :=
        (ClosedSourceBodyEvaluates.mapOwners_iff_exists mapping injective).mp mapped
      obtain ⟨value,finalStore,beforeEq,beforeStoreEq,evaluated⟩ :=
        (fragment.core_evaluates_iff accepted sameIds).mp original
      refine ⟨value,finalStore,?_,?_,evaluated⟩
      · simpa only [beforeEq,RuntimeValue.mapOwners_ofCore] using values
      · simpa only [beforeStoreEq,mapRuntimeStoreOwners_ofCore] using stores
    · rintro ⟨value,finalStore,rfl,rfl,evaluated⟩
      have original := (fragment.core_evaluates_iff accepted sameIds).mpr
        ⟨value,finalStore,rfl,rfl,evaluated⟩
      simpa only [LocalTypeInputs.mapIds_names,mapRuntimeCapturedOwners_ofCore,
        mapRuntimeStoreOwners_ofCore,RuntimeValue.mapOwners_ofCore] using original.mapOwners mapping injective

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.ClosedSourceShortCircuitProperties`
-/

/- Exact short-circuit decomposition; actual right values and stores
remain unrestricted, and skipped operands have no evaluation premise. -/
set_option autoImplicit false
namespace Solcore.Frontend

theorem closedSourceExpressionEvaluates_logicalAnd_iff
    {owner : Resolved.DeclarationId} {names : LocalNameTable}
    {captured : Resolved.LocalScope RuntimeValue}
    {initialStore finalStore : List RuntimeValue}
    {span operatorSpan : Syntax.SourceSpan}
    {left right : Syntax.Expr} {value : RuntimeValue} :
    ClosedSourceExpressionEvaluates owner names captured initialStore
      ⟨span, .binary left ⟨operatorSpan, .logicalAnd⟩ right⟩ value finalStore ↔
    (value = .bool false ∧
      ClosedSourceExpressionEvaluates owner names captured initialStore
        left (.bool false) finalStore) ∨
    (∃ middleStore,
      ClosedSourceExpressionEvaluates owner names captured initialStore
        left (.bool true) middleStore ∧
      ClosedSourceExpressionEvaluates owner names captured middleStore
        right value finalStore) := by
  constructor
  · intro evaluated
    cases evaluated with
    | creation shape => cases shape
    | strictWordBinary _ _ meaning => cases meaning
    | andTrue leftEvaluation rightEvaluation => exact .inr ⟨_, leftEvaluation, rightEvaluation⟩
    | andFalse leftEvaluation => exact .inl ⟨rfl, leftEvaluation⟩
  · rintro (⟨rfl, leftEvaluation⟩ | ⟨middleStore, leftEvaluation, rightEvaluation⟩)
    · exact .andFalse leftEvaluation
    · exact .andTrue leftEvaluation rightEvaluation

theorem closedSourceExpressionEvaluates_logicalOr_iff
    {owner : Resolved.DeclarationId} {names : LocalNameTable}
    {captured : Resolved.LocalScope RuntimeValue}
    {initialStore finalStore : List RuntimeValue}
    {span operatorSpan : Syntax.SourceSpan}
    {left right : Syntax.Expr} {value : RuntimeValue} :
    ClosedSourceExpressionEvaluates owner names captured initialStore
      ⟨span, .binary left ⟨operatorSpan, .logicalOr⟩ right⟩ value finalStore ↔
    (value = .bool true ∧
      ClosedSourceExpressionEvaluates owner names captured initialStore
        left (.bool true) finalStore) ∨
    (∃ middleStore,
      ClosedSourceExpressionEvaluates owner names captured initialStore
        left (.bool false) middleStore ∧
      ClosedSourceExpressionEvaluates owner names captured middleStore
        right value finalStore) := by
  constructor
  · intro evaluated
    cases evaluated with
    | creation shape => cases shape
    | strictWordBinary _ _ meaning => cases meaning
    | orTrue leftEvaluation => exact .inl ⟨rfl, leftEvaluation⟩
    | orFalse leftEvaluation rightEvaluation => exact .inr ⟨_, leftEvaluation, rightEvaluation⟩
  · rintro (⟨rfl, leftEvaluation⟩ | ⟨middleStore, leftEvaluation, rightEvaluation⟩)
    · exact .orTrue leftEvaluation
    · exact .orFalse leftEvaluation rightEvaluation

theorem evaluateClosedSourceExpression?_logicalAnd
    (budget : Nat) (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (initialStore : List RuntimeValue)
    (span operatorSpan : Syntax.SourceSpan) (left right : Syntax.Expr) :
    evaluateClosedSourceExpression? (budget + 1) owner names captured initialStore
      ⟨span, .binary left ⟨operatorSpan, .logicalAnd⟩ right⟩ =
    (do
      let (.bool choice, middleStore) ←
        evaluateClosedSourceExpression? budget owner names captured initialStore left | none
      if choice then evaluateClosedSourceExpression? budget owner names captured middleStore right
      else return (.bool false, middleStore)) := by
  rw [evaluateClosedSourceExpression?]

theorem evaluateClosedSourceExpression?_logicalOr
    (budget : Nat) (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (initialStore : List RuntimeValue)
    (span operatorSpan : Syntax.SourceSpan) (left right : Syntax.Expr) :
    evaluateClosedSourceExpression? (budget + 1) owner names captured initialStore
      ⟨span, .binary left ⟨operatorSpan, .logicalOr⟩ right⟩ =
    (do
      let (.bool choice, middleStore) ←
        evaluateClosedSourceExpression? budget owner names captured initialStore left | none
      if choice then return (.bool true, middleStore)
      else evaluateClosedSourceExpression? budget owner names captured middleStore right) := by
  rw [evaluateClosedSourceExpression?]

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.ClosedSourceStoreProperties`
-/

/- Original closed source rules neither inspect nor mutate stores. Replaying a
value keeps source, lexical rows and opaque captured values literal; replacing
the store does not establish validity of any cell reference inside those values. -/
set_option autoImplicit false
namespace Solcore.Frontend

/-- Every successful original expression returns its actual initial store unchanged. -/
theorem ClosedSourceExpressionEvaluates.store_eq
    {owner names captured initialStore source value finalStore}
    (original : ClosedSourceExpressionEvaluates owner names captured initialStore source value finalStore) :
    finalStore = initialStore := by
  induction original using ClosedSourceExpressionEvaluates.rec
    (motive_2 := fun _ _ _ store _ _ final _ => final = store) <;> simp_all

/-- Every successful original body returns its actual initial store unchanged. -/
theorem ClosedSourceBodyEvaluates.store_eq
    {owner names captured initialStore source value finalStore}
    (original : ClosedSourceBodyEvaluates owner names captured initialStore source value finalStore) :
    finalStore = initialStore := by
  induction original using ClosedSourceBodyEvaluates.rec
    (motive_1 := fun _ _ _ store _ _ final _ => final = store) <;> simp_all

/-- Original expression success replays the same complete value from any store.
No lexical, typing, scope or runtime-world premise is added. -/
theorem ClosedSourceExpressionEvaluates.replay_store
    {owner names captured initialStore source value finalStore}
    (original : ClosedSourceExpressionEvaluates owner names captured initialStore source value finalStore)
    (replacement : List RuntimeValue) :
    ClosedSourceExpressionEvaluates owner names captured replacement source value replacement := by
  induction original using ClosedSourceExpressionEvaluates.rec
    (motive_2 := fun owner names captured _ source value _ _ =>
      ∀ replacement, ClosedSourceBodyEvaluates owner names captured replacement source value replacement) generalizing replacement with
  | reference named found => exact .reference named found
  | unit => exact .unit
  | wordLiteral meaning => exact .wordLiteral meaning
  | group _ ih => exact .group (ih replacement)
  | pair _ _ leftIH rightIH => exact .pair (leftIH replacement) (rightIH replacement)
  | many _ _ headIH tailIH => exact .many (headIH replacement) (tailIH replacement)
  | creation shape => exact .creation shape
  | call shape _ _ _ calleeIH argumentIH bodyIH =>
    exact .call shape (calleeIH replacement) (argumentIH replacement) (bodyIH replacement)
  | conditionalTrue _ _ conditionIH branchIH => exact .conditionalTrue (conditionIH replacement) (branchIH replacement)
  | conditionalFalse _ _ conditionIH branchIH => exact .conditionalFalse (conditionIH replacement) (branchIH replacement)
  | logicalNot _ ih => exact .logicalNot (ih replacement)
  | bitNot _ ih => exact .bitNot (ih replacement)
  | andTrue _ _ leftIH rightIH => exact .andTrue (leftIH replacement) (rightIH replacement)
  | andFalse _ ih => exact .andFalse (ih replacement)
  | orTrue _ ih => exact .orTrue (ih replacement)
  | orFalse _ _ leftIH rightIH => exact .orFalse (leftIH replacement) (rightIH replacement)
  | strictWordBinary _ _ meaning leftIH rightIH => exact .strictWordBinary (leftIH replacement) (rightIH replacement) meaning
  | bare => exact .bare
  | expression _ ih => rename_i replacement; exact .expression (ih replacement)
  | block _ ih => rename_i replacement; exact .block (ih replacement)
  | binding _ _ initializerIH tailIH => rename_i replacement; exact .binding (initializerIH replacement) (tailIH replacement)
  | inferred _ _ initializerIH tailIH => rename_i replacement; exact .inferred (initializerIH replacement) (tailIH replacement)
  | discard _ _ expressionIH tailIH => rename_i replacement; exact .discard (expressionIH replacement) (tailIH replacement)
  | ifTrue _ _ conditionIH branchIH => rename_i replacement; exact .ifTrue (conditionIH replacement) (branchIH replacement)
  | ifFalse _ _ conditionIH branchIH => rename_i replacement; exact .ifFalse (conditionIH replacement) (branchIH replacement)
  | wordMatch _ choice _ scrutineeIH branchIH =>
    rename_i replacement; exact .wordMatch (scrutineeIH replacement) choice (branchIH replacement)

/-- Original body replay preserves all actual values and fresh saved lexical inputs. -/
theorem ClosedSourceBodyEvaluates.replay_store
    {owner names captured initialStore source value finalStore}
    (original : ClosedSourceBodyEvaluates owner names captured initialStore source value finalStore)
    (replacement : List RuntimeValue) :
    ClosedSourceBodyEvaluates owner names captured replacement source value replacement := by
  have compatible := closedSourceBodyEvaluates_iff.mp original
  clear original
  apply closedSourceBodyEvaluates_iff.mpr
  induction compatible with
  | bare => exact .bare
  | expression child => exact .expression (child.replay_store replacement)
  | block _ ih => exact .block ih
  | binding initializer _ ih => exact .binding (initializer.replay_store replacement) ih
  | inferred initializer _ ih => exact .inferred (initializer.replay_store replacement) ih
  | discard expression _ ih => exact .discard (expression.replay_store replacement) ih
  | ifTrue condition _ ih => exact .ifTrue (condition.replay_store replacement) ih
  | ifFalse condition _ ih => exact .ifFalse (condition.replay_store replacement) ih
  | wordMatch scrutinee choice _ ih => exact .wordMatch (scrutinee.replay_store replacement) choice ih

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.ClosedSourceStrictWordBinaryProperties`
-/

/- Ordered strict binary decomposition keeps actual Words and full stores.
Operator exclusions separate this family from the two short-circuit rules. -/
set_option autoImplicit false
namespace Solcore.Frontend

theorem closedSourceExpressionEvaluates_strictWordBinary_iff
    {owner : Resolved.DeclarationId} {names : LocalNameTable}
    {captured : Resolved.LocalScope RuntimeValue}
    {initialStore finalStore : List RuntimeValue}
    {span operatorSpan : Syntax.SourceSpan} {operator : Syntax.BinaryOp}
    (notAnd : operator ≠ .logicalAnd) (notOr : operator ≠ .logicalOr)
    {left right : Syntax.Expr} {value : RuntimeValue} :
    ClosedSourceExpressionEvaluates owner names captured initialStore
      ⟨span, .binary left ⟨operatorSpan, operator⟩ right⟩ value finalStore ↔
    ∃ leftWord rightWord result middleStore,
      value = RuntimeValue.ofCore result ∧
      ClosedSourceExpressionEvaluates owner names captured initialStore
        left (.word leftWord) middleStore ∧
      ClosedSourceExpressionEvaluates owner names captured middleStore
        right (.word rightWord) finalStore ∧
      StrictWordBinaryDenotes operator leftWord rightWord result := by
  constructor
  · intro evaluated
    cases evaluated with
    | creation shape => cases shape
    | andTrue _ _ => exact False.elim (notAnd rfl)
    | andFalse _ => exact False.elim (notAnd rfl)
    | orTrue _ => exact False.elim (notOr rfl)
    | orFalse _ _ => exact False.elim (notOr rfl)
    | strictWordBinary leftEvaluation rightEvaluation meaning =>
        exact ⟨_, _, _, _, rfl, leftEvaluation, rightEvaluation, meaning⟩
  · rintro ⟨leftWord, rightWord, result, middleStore, rfl, leftEvaluation,
      rightEvaluation, meaning⟩
    exact .strictWordBinary leftEvaluation rightEvaluation meaning

theorem evaluateClosedSourceExpression?_strictWordBinary
    (budget : Nat) (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (initialStore : List RuntimeValue)
    (span operatorSpan : Syntax.SourceSpan) (operator : Syntax.BinaryOp)
    (notAnd : operator ≠ .logicalAnd) (notOr : operator ≠ .logicalOr)
    (left right : Syntax.Expr) :
    evaluateClosedSourceExpression? (budget + 1) owner names captured initialStore
      ⟨span, .binary left ⟨operatorSpan, operator⟩ right⟩ =
    (do
      let (.word leftWord, middleStore) ←
        evaluateClosedSourceExpression? budget owner names captured initialStore left | none
      let (.word rightWord, finalStore) ←
        evaluateClosedSourceExpression? budget owner names captured middleStore right | none
      let result ← evaluateStrictWordBinary? operator leftWord rightWord
      return (RuntimeValue.ofCore result, finalStore)) := by
  rw [evaluateClosedSourceExpression?] <;> first | rfl | assumption

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.ClosedSourceUnaryProperties`
-/

/- Exact original unary decomposition and predecessor-depth computation. -/
set_option autoImplicit false
namespace Solcore.Frontend

theorem closedSourceExpressionEvaluates_logicalNot_iff
    {owner : Resolved.DeclarationId} {names : LocalNameTable}
    {captured : Resolved.LocalScope RuntimeValue}
    {initialStore finalStore : List RuntimeValue}
    {span operatorSpan : Syntax.SourceSpan}
    {operand : Syntax.Expr} {value : RuntimeValue} :
    ClosedSourceExpressionEvaluates owner names captured initialStore
      ⟨span, .unary ⟨operatorSpan, .logicalNot⟩ operand⟩ value finalStore ↔
    ∃ operandValue : Bool,
      ClosedSourceExpressionEvaluates owner names captured initialStore
        operand (.bool operandValue) finalStore ∧
      value = .bool (!operandValue) := by
  constructor
  · intro evaluated
    cases evaluated with
    | creation shape => cases shape
    | logicalNot child => exact ⟨_, child, rfl⟩
  · rintro ⟨operandValue, child, rfl⟩
    exact .logicalNot child

theorem closedSourceExpressionEvaluates_bitNot_iff
    {owner : Resolved.DeclarationId} {names : LocalNameTable}
    {captured : Resolved.LocalScope RuntimeValue}
    {initialStore finalStore : List RuntimeValue}
    {span operatorSpan : Syntax.SourceSpan}
    {operand : Syntax.Expr} {value : RuntimeValue} :
    ClosedSourceExpressionEvaluates owner names captured initialStore
      ⟨span, .unary ⟨operatorSpan, .bitNot⟩ operand⟩ value finalStore ↔
    ∃ operandValue : Core.Word,
      ClosedSourceExpressionEvaluates owner names captured initialStore
        operand (.word operandValue) finalStore ∧
      value = .word operandValue.bitNot := by
  constructor
  · intro evaluated
    cases evaluated with
    | creation shape => cases shape
    | bitNot child => exact ⟨_, child, rfl⟩
  · rintro ⟨operandValue, child, rfl⟩
    exact .bitNot child

theorem evaluateClosedSourceExpression?_logicalNot
    (budget : Nat) (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (initialStore : List RuntimeValue)
    (span operatorSpan : Syntax.SourceSpan) (operand : Syntax.Expr) :
    evaluateClosedSourceExpression? (budget + 1) owner names captured initialStore
      ⟨span, .unary ⟨operatorSpan, .logicalNot⟩ operand⟩ =
    (do
      let (.bool value, finalStore) ←
        evaluateClosedSourceExpression? budget owner names captured initialStore operand | none
      return (.bool (!value), finalStore)) := by
  rw [evaluateClosedSourceExpression?]

theorem evaluateClosedSourceExpression?_bitNot
    (budget : Nat) (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (initialStore : List RuntimeValue)
    (span operatorSpan : Syntax.SourceSpan) (operand : Syntax.Expr) :
    evaluateClosedSourceExpression? (budget + 1) owner names captured initialStore
      ⟨span, .unary ⟨operatorSpan, .bitNot⟩ operand⟩ =
    (do
      let (.word value, finalStore) ←
        evaluateClosedSourceExpression? budget owner names captured initialStore operand | none
      return (.word value.bitNot, finalStore)) := by
  rw [evaluateClosedSourceExpression?]

end Solcore.Frontend
