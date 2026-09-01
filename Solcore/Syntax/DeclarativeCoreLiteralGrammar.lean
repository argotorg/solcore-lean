import Solcore.Syntax.DeclarativeGrammar

/-!
Parser-independent leaf grammar for Core literals and expression names.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact grammar of one literal admitted by Core expressions and patterns. -/
inductive CoreLiteralParses :
    Remainder → Syntax.CoreLiteral → Remainder → Prop where
  | decimal {input : Remainder} {span : SourceSpan} {spelling : String}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span
        value := .decimalLiteral spelling
      }) :
      CoreLiteralParses input {
        span
        value := .decimal spelling
      } { input with cursor := input.cursor + 1 }
  | hexadecimal {input : Remainder} {span : SourceSpan} {spelling : String}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span
        value := .hexadecimalLiteral spelling
      }) :
      CoreLiteralParses input {
        span
        value := .hexadecimal spelling
      } { input with cursor := input.cursor + 1 }
  | string {input : Remainder} {span : SourceSpan} {spelling : String}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span
        value := .stringLiteral spelling
      }) :
      CoreLiteralParses input {
        span
        value := .string spelling
      } { input with cursor := input.cursor + 1 }

/-- Exact grammar of the identifier-shaped Boolean builtin values. -/
inductive BooleanIdentifierParses :
    Remainder → Syntax.Identifier → Remainder → Prop where
  | trueKeyword {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span
        value := .keyword .trueKw
      }) :
      BooleanIdentifierParses input {
        span
        value := "true"
      } { input with cursor := input.cursor + 1 }
  | falseKeyword {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span
        value := .keyword .falseKw
      }) :
      BooleanIdentifierParses input {
        span
        value := "false"
      } { input with cursor := input.cursor + 1 }

/--
Exact ordered grammar of an expression name.

Boolean keywords have priority.  The ordinary-identifier branch therefore
records that neither Boolean keyword occurs at the input cursor.
-/
inductive ExpressionNameParses :
    Remainder → Syntax.Identifier → Remainder → Prop where
  | boolean {input output : Remainder} {name : Syntax.Identifier}
      (parsed : BooleanIdentifierParses input name output) :
      ExpressionNameParses input name output
  | identifier {input output : Remainder} {name : Syntax.Identifier}
      (trueAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .trueKw))
      (falseAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .falseKw))
      (parsed : IdentifierParses input name output) :
      ExpressionNameParses input name output

end Solcore.Syntax.DeclarativeGrammar
