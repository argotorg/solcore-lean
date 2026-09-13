import Solcore.Syntax.Term

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

end Solcore.Frontend
