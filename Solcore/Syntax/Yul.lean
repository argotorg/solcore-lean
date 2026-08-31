import Solcore.Syntax.Literal

set_option autoImplicit false

namespace Solcore.Syntax

/-- Identifier accepted specifically by the inline-Yul identifier grammar. -/
abbrev YulIdentifier := SpannedText

/-- Source-preserving inline-Yul expression payload. -/
inductive YulExprValue where
  | literal (literal : YulLiteral)
  | identifier (name : YulIdentifier)
  | call
      (callee : YulIdentifier)
      (arguments : DelimitedList (Located YulExprValue))
  | error
  deriving Repr, BEq

abbrev YulExpr := Located YulExprValue

/-- Explicit inline-Yul return-name clause introduced by `->`. -/
structure YulReturnClauseValue where
  arrow : SourceSpan
  names : NonemptyList YulIdentifier
  deriving Repr, BEq

abbrev YulReturnClause := Located YulReturnClauseValue

mutual

/-- Source-preserving inline-Yul statement payload. -/
inductive YulStmtValue where
  | block (body : List (Located YulStmtValue))
  | letDecl
      (names : NonemptyList YulIdentifier)
      (initializer : Option YulExpr)
  | assign
      (names : NonemptyList YulIdentifier)
      (value : YulExpr)
  | expression (expression : YulExpr)
  | ifThen
      (condition : YulExpr)
      (body : List (Located YulStmtValue))
  | forLoop
      (initializer : List (Located YulStmtValue))
      (condition : YulExpr)
      (post : List (Located YulStmtValue))
      (body : List (Located YulStmtValue))
  | switch
      (scrutinee : YulExpr)
      (cases : NonemptyList (Located YulCaseValue))
      (defaultBody : Option (List (Located YulStmtValue)))
  | functionDef
      (name : YulIdentifier)
      (parameters : DelimitedList YulIdentifier)
      (returns : Option YulReturnClause)
      (body : List (Located YulStmtValue))
  | leave
  | break
  | continue
  | error
  deriving Repr, BEq

/-- One non-default Yul switch arm. -/
inductive YulCaseValue where
  | arm
      (literal : YulLiteral)
      (body : List (Located YulStmtValue))
  deriving Repr, BEq

end

abbrev YulStmt := Located YulStmtValue
abbrev YulCase := Located YulCaseValue

end Solcore.Syntax
