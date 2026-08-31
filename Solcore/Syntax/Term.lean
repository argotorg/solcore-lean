import Solcore.Syntax.Literal
import Solcore.Syntax.Operator
import Solcore.Syntax.Yul

set_option autoImplicit false

namespace Solcore.Syntax

mutual

/-- Source-preserving canonical Core expression payload. -/
inductive ExprValue where
  | literal (literal : CoreLiteral)
  | identifier (name : Identifier)
  | dotConstructor
      (dot : SourceSpan)
      (name : Identifier)
      (arguments : Option (DelimitedList (Located ExprValue)))
  | proxy
      (marker : SourceSpan)
      (type : TypeExpr)
  | lambda
      (keyword : SourceSpan)
      (parameters : DelimitedList LambdaParameter)
      (returnType : Option TypeExpr)
      (body : Located (List (Located StatementValue)))
  | unary
      (operator : Located UnaryOp)
      (operand : Located ExprValue)
  | binary
      (left : Located ExprValue)
      (operator : Located BinaryOp)
      (right : Located ExprValue)
  | index
      (base : Located ExprValue)
      (brackets : SourceSpan)
      (index : Located ExprValue)
  | call
      (callee : Located ExprValue)
      (arguments : DelimitedList (Located ExprValue))
  | field
      (base : Located ExprValue)
      (dot : SourceSpan)
      (name : Identifier)
  | conditional
      (condition : Located ExprValue)
      (question : SourceSpan)
      (thenBranch : Located ExprValue)
      (colon : SourceSpan)
      (elseBranch : Located ExprValue)
  | group (inner : Located ExprValue)
  | tuple (elements : DelimitedList (Located ExprValue))
  | array (elements : DelimitedList (Located ExprValue))
  | error
  deriving Repr, BEq

/-- Source-preserving canonical pattern payload. -/
inductive PatternValue where
  | wildcard (marker : SourceSpan)
  | literal (literal : CoreLiteral)
  | binder (name : Identifier)
  | constructor
      (leadingDot : Option SourceSpan)
      (qualifiers : List Identifier)
      (name : Identifier)
      (arguments : Option (NonemptyDelimitedList (Located PatternValue)))
  | comptime
      (keyword : SourceSpan)
      (expression : Located ExprValue)
  | group (inner : Located PatternValue)
  | tuple (elements : DelimitedList (Located PatternValue))
  | error
  deriving Repr, BEq

/-- One explicit non-default Core match arm. -/
inductive MatchCaseValue where
  | arm
      (patterns : NonemptyList (Located PatternValue))
      (body : Located (List (Located StatementValue)))
  deriving Repr, BEq

/-- Nonempty match-arm collection with `default`, when present, fixed last. -/
inductive MatchArmsValue where
  | cases
      (cases : NonemptyList (Located MatchCaseValue))
      (defaultBody : Option (Located (List (Located StatementValue))))
  | defaultOnly (body : Located (List (Located StatementValue)))
  deriving Repr, BEq

/-- Restricted item accepted in a canonical `for` header. -/
inductive ForItemValue where
  | letDecl
      (name : Identifier)
      (type : Option TypeExpr)
      (initializer : Option (Located ExprValue))
  | expression (expression : Located ExprValue)
  | assignValue
      (target : Located ExprValue)
      (operator : Located ValueAssignOp)
      (value : Located ExprValue)
  | assignBitNot
      (target : Located ExprValue)
      (operator : SourceSpan)
  deriving Repr, BEq

/-- Source-preserving canonical Core statement payload. -/
inductive StatementValue where
  | letDecl
      (name : Identifier)
      (type : Option TypeExpr)
      (initializer : Option (Located ExprValue))
  | returnStmt (value : Option (Located ExprValue))
  | expression
      (expression : Located ExprValue)
      (trailingSemicolon : Bool)
  | assignValue
      (target : Located ExprValue)
      (operator : Located ValueAssignOp)
      (value : Located ExprValue)
  | assignBitNot
      (target : Located ExprValue)
      (operator : SourceSpan)
  | matchWith
      (scrutinees : NonemptyDelimitedList (Located ExprValue))
      (arms : Located MatchArmsValue)
  | forLoop
      (headerSpan : SourceSpan)
      (initializer : List (Located ForItemValue))
      (condition : Located ExprValue)
      (post : List (Located ForItemValue))
      (body : Located (List (Located StatementValue)))
  | whileLoop
      (condition : Located ExprValue)
      (body : Located (List (Located StatementValue)))
  | ifThen
      (condition : Located ExprValue)
      (thenBody : Located (List (Located StatementValue)))
      (elseBody : Option (Located (List (Located StatementValue))))
  | block (body : List (Located StatementValue))
  | assembly (body : List YulStmt)
  | breakStmt
  | continueStmt
  | error
  deriving Repr, BEq

end

abbrev Expr := Located ExprValue
abbrev Pattern := Located PatternValue
abbrev MatchCase := Located MatchCaseValue
abbrev MatchArms := Located MatchArmsValue
abbrev ForItem := Located ForItemValue
abbrev Statement := Located StatementValue
abbrev Block := Located (List Statement)

end Solcore.Syntax
