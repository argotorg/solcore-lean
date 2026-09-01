import Solcore.Syntax.DeclarativeCoreExpressionAtomDispatcherGrammar
import Solcore.Syntax.DeclarativeCorePatternBasicGrammar
import Solcore.Syntax.DeclarativeCorePatternComptimeGrammar
import Solcore.Syntax.DeclarativeCorePatternConstructorGrammar

/-!
Parser-independent ordered grammar for the non-recovering Core pattern
dispatcher and its diagnostic-free public layer.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Either Boolean hard keyword starts at the current pattern cursor. -/
def BooleanPatternStartsAt (input : Remainder) : Prop :=
  (∃ span, TokenAt input.tokens input.endIndex input.cursor {
    span
    value := .keyword .trueKw
  }) ∨
  ∃ span, TokenAt input.tokens input.endIndex input.cursor {
    span
    value := .keyword .falseKw
  }

/--
Exact priority grammar of `patternCore`.  Every branch after the wildcard
retains all failed executable guards that precede it.
-/
inductive PatternCoreParses
    (nestedParses : Remainder → Syntax.Pattern → Remainder → Prop)
    (expressionParses : Remainder → Syntax.Expr → Remainder → Prop)
    (fallback : ConstructorArgumentsFallbackSpec nestedParses) :
    Remainder → Syntax.Pattern → Remainder → Prop where
  | wildcard {input output : Remainder} {value : Syntax.Pattern}
      (parsed : WildcardPatternParses input value output) :
      PatternCoreParses nestedParses expressionParses fallback input value
        output
  | literal {input output : Remainder} {value : Syntax.Pattern}
      (underscoreAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .underscore))
      (parsed : LiteralPatternParses input value output) :
      PatternCoreParses nestedParses expressionParses fallback input value
        output
  | boolean {input output : Remainder} {value : Syntax.Pattern}
      (underscoreAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .underscore))
      (literalAbsent : ¬ CoreLiteralStartsAt input)
      (parsed : BooleanBinderPatternParses input value output) :
      PatternCoreParses nestedParses expressionParses fallback input value
        output
  | parenthesized {input output : Remainder} {value : Syntax.Pattern}
      (underscoreAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .underscore))
      (literalAbsent : ¬ CoreLiteralStartsAt input)
      (booleanAbsent : ¬ BooleanPatternStartsAt input)
      (parsed : ParenthesizedPatternParses nestedParses input value output) :
      PatternCoreParses nestedParses expressionParses fallback input value
        output
  | dotConstructor {input output : Remainder} {value : Syntax.Pattern}
      (underscoreAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .underscore))
      (literalAbsent : ¬ CoreLiteralStartsAt input)
      (booleanAbsent : ¬ BooleanPatternStartsAt input)
      (leftParenAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .leftParen))
      (parsed : DotConstructorPatternParses nestedParses fallback input value
        output) :
      PatternCoreParses nestedParses expressionParses fallback input value
        output
  | comptime {input output : Remainder} {value : Syntax.Pattern}
      (underscoreAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .underscore))
      (literalAbsent : ¬ CoreLiteralStartsAt input)
      (booleanAbsent : ¬ BooleanPatternStartsAt input)
      (leftParenAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .leftParen))
      (dotAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .dot))
      (parsed : ComptimePatternParses expressionParses input value output) :
      PatternCoreParses nestedParses expressionParses fallback input value
        output
  | qualified {input output : Remainder} {value : Syntax.Pattern}
      (underscoreAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .underscore))
      (literalAbsent : ¬ CoreLiteralStartsAt input)
      (booleanAbsent : ¬ BooleanPatternStartsAt input)
      (leftParenAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .leftParen))
      (dotAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .dot))
      (comptimeAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.identifier ContextualKeyword.comptime.spelling))
      (parsed : QualifiedPatternParses nestedParses fallback input value
        output) :
      PatternCoreParses nestedParses expressionParses fallback input value
        output

/-- Diagnostic-free public pattern parsing has the same independent grammar. -/
abbrev PatternLayerParses := PatternCoreParses

end Solcore.Syntax.DeclarativeGrammar
