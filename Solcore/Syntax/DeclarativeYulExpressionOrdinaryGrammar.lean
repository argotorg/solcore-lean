import Solcore.Syntax.DeclarativeDelimitedFallbackProperties
import Solcore.Syntax.DeclarativeYulExpressionRejectionGrammar
import Solcore.Syntax.DeclarativeYulNameOutcomeGrammar

/-!
Parser-independent ordinary-success grammar for inline-Yul expressions.

Unlike the diagnostic-free grammar, this layer retains diagnosed Yul names,
forbidden source meta syntax, and recovered error expressions.  Transactional
call-argument rejection is recorded before the parser rewinds to `none`.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary outcomes of optional transactional Yul call arguments. -/
inductive OptionalYulCallArgumentsOrdinaryParses
    (ordinaryParses : Remainder → Syntax.YulExpr → Remainder → Prop)
    (nestedRejects : Remainder → Remainder → Prop) :
    Remainder → Option (DelimitedList Syntax.YulExpr) → Remainder →
      Prop where
  | absent {input : Remainder}
      (openingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .leftParen)) :
      OptionalYulCallArgumentsOrdinaryParses ordinaryParses nestedRejects
        input none input
  | rewound {input : Remainder} (openingSpan : SourceSpan)
      (openingToken : TokenAt input.tokens input.endIndex input.cursor {
        span := openingSpan
        value := .symbol .leftParen
      })
      (attemptRejected : YulCallArgumentsRejects ordinaryParses nestedRejects
        input) :
      OptionalYulCallArgumentsOrdinaryParses ordinaryParses nestedRejects
        input none input
  | present {input output : Remainder}
      {arguments : DelimitedList Syntax.YulExpr}
      (parsed : TrailingDelimitedListParses .leftParen .rightParen
        ordinaryParses input arguments output) :
      OptionalYulCallArgumentsOrdinaryParses ordinaryParses nestedRejects
        input (some arguments) output

/-- Ordinary named-or-called inline-Yul expression grammar. -/
inductive YulNamedExpressionOrdinaryParses
    (ordinaryParses : Remainder → Syntax.YulExpr → Remainder → Prop)
    (nestedRejects : Remainder → Remainder → Prop) :
    Remainder → Syntax.YulExpr → Remainder → Prop where
  | identifier {input afterName output : Remainder}
      {name : Syntax.YulIdentifier}
      (nameParsed : YulNameOrdinaryParses input name afterName)
      (argumentsParsed : OptionalYulCallArgumentsOrdinaryParses
        ordinaryParses nestedRejects afterName none output) :
      YulNamedExpressionOrdinaryParses ordinaryParses nestedRejects input {
        span := name.span
        value := .identifier name
      } output
  | call {input afterName output : Remainder}
      {name : Syntax.YulIdentifier}
      {arguments : DelimitedList Syntax.YulExpr}
      (nameParsed : YulNameOrdinaryParses input name afterName)
      (argumentsParsed : OptionalYulCallArgumentsOrdinaryParses
        ordinaryParses nestedRejects afterName (some arguments) output) :
      YulNamedExpressionOrdinaryParses ordinaryParses nestedRejects input {
        span := SourceSpan.cover name.span arguments.span
        value := .call name arguments
      } output

/-- Forbidden source-level Yul meta-token presence. -/
def YulMetaStartsAt (input : Remainder) : Prop :=
  (∃ span text, TokenAt input.tokens input.endIndex input.cursor {
    span
    value := .yulMetaBacktick text
  }) ∨
  ∃ span text, TokenAt input.tokens input.endIndex input.cursor {
    span
    value := .yulMetaInterpolation text
  }

/-- Exact ordinary outcomes of the literal-before-name core parser. -/
inductive YulExpressionCoreOrdinaryParses
    (ordinaryParses : Remainder → Syntax.YulExpr → Remainder → Prop)
    (nestedRejects : Remainder → Remainder → Prop) :
    Remainder → Syntax.YulExpr → Remainder → Prop where
  | literal {input output : Remainder} {literal : Syntax.YulLiteral}
      (parsed : YulLiteralParses input literal output) :
      YulExpressionCoreOrdinaryParses ordinaryParses nestedRejects input {
        span := literal.span
        value := .literal literal
      } output
  | named {input output : Remainder} {expression : Syntax.YulExpr}
      (literalAbsent : ¬ YulLiteralStartsAt input)
      (parsed : YulNamedExpressionOrdinaryParses ordinaryParses nestedRejects
        input expression output) :
      YulExpressionCoreOrdinaryParses ordinaryParses nestedRejects input
        expression output
  | metaBacktick {input : Remainder} {span : SourceSpan} {text : String}
      (literalAbsent : ¬ YulLiteralStartsAt input)
      (nameAbsent : ¬ YulNameStartsAt input)
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span
        value := .yulMetaBacktick text
      }) :
      YulExpressionCoreOrdinaryParses ordinaryParses nestedRejects input {
        span
        value := .error
      } { input with cursor := input.cursor + 1 }
  | metaInterpolation {input : Remainder} {span : SourceSpan} {text : String}
      (literalAbsent : ¬ YulLiteralStartsAt input)
      (nameAbsent : ¬ YulNameStartsAt input)
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span
        value := .yulMetaInterpolation text
      }) :
      YulExpressionCoreOrdinaryParses ordinaryParses nestedRejects input {
        span
        value := .error
      } { input with cursor := input.cursor + 1 }

/-- Exact evidence that the final core `rejectAt` branch was selected. -/
inductive YulExpressionCoreFinalRejects : Remainder → Prop where
  | final {input : Remainder}
      (literalAbsent : ¬ YulLiteralStartsAt input)
      (nameAbsent : ¬ YulNameStartsAt input)
      (metaAbsent : ¬ YulMetaStartsAt input) :
      YulExpressionCoreFinalRejects input

/-- Exact scan performed after recovery has consumed its first token. -/
inductive YulExpressionRecoveryScanParses (first : SourceSpan) :
    SourceSpan → Remainder → Syntax.YulExpr → Remainder → Prop where
  | stop {last : SourceSpan} {input : Remainder}
      (stops : YulExpressionRejects input input) :
      YulExpressionRecoveryScanParses first last input {
        span := SourceSpan.cover first last
        value := .error
      } input
  | next {last : SourceSpan} {input output : Remainder} {token : Token}
      {expression : Syntax.YulExpr}
      (continues : ¬ YulExpressionRejects input input)
      (current : TokenAt input.tokens input.endIndex input.cursor token)
      (tail : YulExpressionRecoveryScanParses first token.span
        { input with cursor := input.cursor + 1 } expression output) :
      YulExpressionRecoveryScanParses first last input expression output

/-- Ordinary outcomes of one recovering inline-Yul expression layer. -/
inductive YulExpressionLayerOrdinaryParses
    (ordinaryParses : Remainder → Syntax.YulExpr → Remainder → Prop)
    (nestedRejects : Remainder → Remainder → Prop) :
    Remainder → Syntax.YulExpr → Remainder → Prop where
  | core {input output : Remainder} {expression : Syntax.YulExpr}
      (parsed : YulExpressionCoreOrdinaryParses ordinaryParses nestedRejects
        input expression output) :
      YulExpressionLayerOrdinaryParses ordinaryParses nestedRejects input
        expression output
  | recovered {input output : Remainder} {token : Token}
      {expression : Syntax.YulExpr}
      (coreRejected : YulExpressionCoreFinalRejects input)
      (continues : ¬ YulExpressionRejects input input)
      (current : TokenAt input.tokens input.endIndex input.cursor token)
      (scan : YulExpressionRecoveryScanParses token.span token.span
        { input with cursor := input.cursor + 1 } expression output) :
      YulExpressionLayerOrdinaryParses ordinaryParses nestedRejects input
        expression output

end Solcore.Syntax.DeclarativeGrammar
