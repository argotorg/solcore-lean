import Solcore.Frontend.ClosedSourceDataExpression

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
