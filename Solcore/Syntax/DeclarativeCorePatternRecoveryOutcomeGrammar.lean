import Solcore.Syntax.DeclarativeDelimitedOutcomeGrammar

/-!
Parser-independent ordinary outcomes of Core pattern recovery.

The public pattern layer consumes one token before this scan begins.  The
scan gives pattern boundaries priority over token consumption and records a
missing carrier slot inside the active token window.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact stop conditions of the boundary-prioritized pattern recovery scan. -/
inductive PatternRecoveryStops : Remainder → Remainder → Prop where
  | windowEnd {input : Remainder}
      (atEnd : input.endIndex <= input.cursor) :
      PatternRecoveryStops input input
  | comma {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .symbol .comma }) :
      PatternRecoveryStops input input
  | rightParen {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .symbol .rightParen }) :
      PatternRecoveryStops input input
  | fatArrow {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .symbol .fatArrow }) :
      PatternRecoveryStops input input
  | pipe {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .symbol .pipe }) :
      PatternRecoveryStops input input
  | rightBrace {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .symbol .rightBrace }) :
      PatternRecoveryStops input input
  | missingToken {input : Remainder}
      (inside : input.cursor < input.endIndex)
      (missing : input.tokens[input.cursor]? = none) :
      PatternRecoveryStops input input

/-- Exact scan after pattern recovery has consumed its mandatory first token. -/
inductive PatternRecoveryScanParses (first : SourceSpan) :
    SourceSpan → Remainder → Syntax.Pattern → Remainder → Prop where
  | stop {last : SourceSpan} {input : Remainder}
      (stops : PatternRecoveryStops input input) :
      PatternRecoveryScanParses first last input {
        span := SourceSpan.cover first last
        value := .error
      } input
  | next {last : SourceSpan} {input output : Remainder} {token : Token}
      {pattern : Syntax.Pattern}
      (continues : ¬ PatternRecoveryStops input input)
      (current : TokenAt input.tokens input.endIndex input.cursor token)
      (tail : PatternRecoveryScanParses first token.span
        { input with cursor := input.cursor + 1 } pattern output) :
      PatternRecoveryScanParses first last input pattern output

/-- Ordinary pattern recovery, including its mandatory first token. -/
inductive PatternRecoveryParses :
    Remainder → Syntax.Pattern → Remainder → Prop where
  | recovered {input output : Remainder} {token : Token}
      {pattern : Syntax.Pattern}
      (current : TokenAt input.tokens input.endIndex input.cursor token)
      (scan : PatternRecoveryScanParses token.span token.span
        { input with cursor := input.cursor + 1 } pattern output) :
      PatternRecoveryParses input pattern output

/-- Exact non-consuming rejection when recovery cannot consume first. -/
inductive PatternRecoveryRejects : Remainder → Remainder → Prop where
  | windowEnd {input : Remainder}
      (atEnd : input.endIndex <= input.cursor) :
      PatternRecoveryRejects input input
  | missingToken {input : Remainder}
      (inside : input.cursor < input.endIndex)
      (missing : input.tokens[input.cursor]? = none) :
      PatternRecoveryRejects input input

end Solcore.Syntax.DeclarativeGrammar
