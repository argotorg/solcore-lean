import Solcore.Syntax.DeclarativeGrammar

/-!
Parser-independent maximal postfix grammar for Core expressions.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- None of the three canonical postfix suffixes begins at this cursor. -/
def PostfixSuffixAbsentAt (input : Remainder) : Prop :=
  TokenKindAbsentAt input.tokens input.endIndex input.cursor
      (.symbol .leftBracket) ∧
    TokenKindAbsentAt input.tokens input.endIndex input.cursor
      (.symbol .leftParen) ∧
    TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .dot)

/-- Maximal sequence of index, call, and field suffixes. -/
inductive PostfixTailParses
    (nestedParses : Remainder → Syntax.Expr → Remainder → Prop) :
    Remainder → Syntax.Expr → Syntax.Expr → Remainder → Prop where
  | done {input : Remainder} {base : Syntax.Expr}
      (absent : PostfixSuffixAbsentAt input) :
      PostfixTailParses nestedParses input base base input
  | index {input afterOpening afterIndex afterClosing output : Remainder}
      {base index expression : Syntax.Expr}
      (openingSpan closingSpan : SourceSpan)
      (openingToken : ExactTokenParses (.symbol .leftBracket) input
        openingSpan afterOpening)
      (indexParsed : nestedParses afterOpening index afterIndex)
      (closingToken : ExactTokenParses (.symbol .rightBracket) afterIndex
        closingSpan afterClosing)
      (tail : PostfixTailParses nestedParses afterClosing {
        span := SourceSpan.cover base.span closingSpan
        value := .index base (SourceSpan.cover openingSpan closingSpan) index
      } expression output) :
      PostfixTailParses nestedParses input base expression output
  | call {input afterArguments output : Remainder}
      {base expression : Syntax.Expr}
      {arguments : DelimitedList Syntax.Expr}
      (indexAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .leftBracket))
      (argumentsParsed : NoTrailingDelimitedListParses
        .leftParen .rightParen nestedParses input arguments afterArguments)
      (tail : PostfixTailParses nestedParses afterArguments {
        span := SourceSpan.cover base.span arguments.span
        value := .call base arguments
      } expression output) :
      PostfixTailParses nestedParses input base expression output
  | field {input afterDot afterName output : Remainder}
      {base expression : Syntax.Expr} {name : Syntax.Identifier}
      (dotSpan : SourceSpan)
      (indexAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .leftBracket))
      (callAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .leftParen))
      (dotToken : ExactTokenParses (.symbol .dot) input dotSpan afterDot)
      (nameParsed : IdentifierParses afterDot name afterName)
      (tail : PostfixTailParses nestedParses afterName {
        span := SourceSpan.cover base.span name.span
        value := .field base dotSpan name
      } expression output) :
      PostfixTailParses nestedParses input base expression output

/-- One atom followed by its complete maximal postfix suffix sequence. -/
def ExpressionPostfixParses
    (atomParses nestedParses :
      Remainder → Syntax.Expr → Remainder → Prop)
    (input : Remainder) (expression : Syntax.Expr)
    (output : Remainder) : Prop :=
  ∃ base afterAtom,
    atomParses input base afterAtom ∧
    PostfixTailParses nestedParses afterAtom base expression output

end Solcore.Syntax.DeclarativeGrammar
