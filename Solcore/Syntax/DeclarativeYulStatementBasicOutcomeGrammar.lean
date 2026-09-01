import Solcore.Syntax.DeclarativeCoreYulStatementBasicGrammar
import Solcore.Syntax.DeclarativeDelimitedOutcomeGrammar
import Solcore.Syntax.DeclarativeYulExpressionFuelGrammar
import Solcore.Syntax.DeclarativeYulStatementBasicGrammar

/-!
Parser-independent ordinary successes and exact rejection traces for the
nonrecursive expression, source-level `return(...)`, and keyword-only Yul
statement primaries.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary expression-statement success uses the public ordinary expression
relation and preserves the expression AST and span exactly. -/
abbrev YulExpressionStatementOrdinaryParses :=
  YulExpressionStatementParses YulExpressionOrdinaryParses

/-- Exact rejection of an inline-Yul expression statement. -/
inductive YulExpressionStatementRejects : Remainder → Remainder → Prop where
  | expressionRejected {input rejected : Remainder}
      (expressionRejected : YulExpressionRejects input rejected) :
      YulExpressionStatementRejects input rejected

/-- Ordinary source-level `return(...)` success reuses the exact synthesized
call grammar with public ordinary expressions. -/
abbrev YulReturnBuiltinOrdinaryParses :=
  YulReturnBuiltinParses YulExpressionOrdinaryParses

/-- Exact rejection stage of one source-level `return(...)` attempt. -/
inductive YulReturnBuiltinRejects : Remainder → Remainder → Prop where
  | markerMissing {input : Remainder}
      (markerAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .returnKw)) :
      YulReturnBuiltinRejects input input
  | argumentsRejected {input afterMarker rejected : Remainder}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .returnKw) input markerSpan
        afterMarker)
      (argumentsRejected : DelimitedListRejects .leftParen .rightParen true true
        YulExpressionOrdinaryParses YulExpressionRejects afterMarker rejected) :
      YulReturnBuiltinRejects input rejected

/-- Ordinary keyword-only control success is already exact token parsing. -/
abbrev YulControlTokenOrdinaryParses
    (keyword : HardKeyword) (statementValue : Syntax.YulStmtValue) :=
  YulControlTokenParses keyword statementValue

/-- Exact nonconsuming rejection of one keyword-only Yul control token. -/
inductive YulControlTokenRejects (keyword : HardKeyword) :
    Remainder → Remainder → Prop where
  | keywordMissing {input : Remainder}
      (keywordAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword keyword)) :
      YulControlTokenRejects keyword input input

end Solcore.Syntax.DeclarativeGrammar
