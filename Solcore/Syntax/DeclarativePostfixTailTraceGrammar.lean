import Solcore.Syntax.DeclarativeCoreExpressionPostfixGrammar
import Solcore.Syntax.DeclarativeDelimitedNoTrailingTraceGrammar
import Solcore.Syntax.DeclarativeIdentifierTraceGrammar

/-! Independent maximal postfix traces. Index, call, and checked-identifier
field suffixes retain their ordered lookahead guards and exact AST spans.
Only call arguments enforce the existing delimited-list child progress rule;
index expressions do not acquire a new progress or carrier restriction. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

def postfixIndexTraceValue (base index : Syntax.Expr)
    (openingSpan closingSpan : SourceSpan) : Syntax.Expr := {
  span := SourceSpan.cover base.span closingSpan
  value := .index base (SourceSpan.cover openingSpan closingSpan) index
}

def postfixCallTraceValue (base : Syntax.Expr)
    (arguments : DelimitedList Syntax.Expr) : Syntax.Expr := {
  span := SourceSpan.cover base.span arguments.span
  value := .call base arguments
}

def postfixFieldTraceValue (base : Syntax.Expr) (dotSpan : SourceSpan)
    (name : Syntax.Identifier) : Syntax.Expr := {
  span := SourceSpan.cover base.span name.span
  value := .field base dotSpan name
}

inductive PostfixTailTraceParses
    (nestedTrace : SourceId → Nat → Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Syntax.Expr → Syntax.Expr → Remainder → List ParseDiagnostic → Prop where
  | done {input : Remainder} {base : Syntax.Expr}
      (absent : PostfixSuffixAbsentAt input) :
      PostfixTailTraceParses nestedTrace source endByte input base base input []
  | index {input afterOpening afterIndex afterClosing output : Remainder}
      {base index expression : Syntax.Expr} {indexEvents tailEvents : List ParseDiagnostic}
      (openingSpan closingSpan : SourceSpan)
      (openingToken : ExactTokenParses (.symbol .leftBracket) input openingSpan afterOpening)
      (indexParsed : nestedTrace source endByte afterOpening index afterIndex indexEvents)
      (closingToken : ExactTokenParses (.symbol .rightBracket) afterIndex closingSpan afterClosing)
      (tail : PostfixTailTraceParses nestedTrace source endByte afterClosing
        (postfixIndexTraceValue base index openingSpan closingSpan) expression output tailEvents) :
      PostfixTailTraceParses nestedTrace source endByte input base expression output (indexEvents ++ tailEvents)
  | call {input afterArguments output : Remainder}
      {base expression : Syntax.Expr} {arguments : DelimitedList Syntax.Expr}
      {argumentEvents tailEvents : List ParseDiagnostic}
      (indexAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .leftBracket))
      (argumentsParsed : NoTrailingDelimitedListTraceParses .leftParen .rightParen true
        nestedTrace source endByte input arguments afterArguments argumentEvents)
      (tail : PostfixTailTraceParses nestedTrace source endByte afterArguments
        (postfixCallTraceValue base arguments) expression output tailEvents) :
      PostfixTailTraceParses nestedTrace source endByte input base expression output (argumentEvents ++ tailEvents)
  | field {input afterDot afterName output : Remainder}
      {base expression : Syntax.Expr} {name : Syntax.Identifier}
      {nameEvents tailEvents : List ParseDiagnostic} (dotSpan : SourceSpan)
      (indexAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .leftBracket))
      (callAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .leftParen))
      (dotToken : ExactTokenParses (.symbol .dot) input dotSpan afterDot)
      (nameParsed : IdentifierTraceParses afterDot name afterName nameEvents)
      (tail : PostfixTailTraceParses nestedTrace source endByte afterName
        (postfixFieldTraceValue base dotSpan name) expression output tailEvents) :
      PostfixTailTraceParses nestedTrace source endByte input base expression output (nameEvents ++ tailEvents)

end Solcore.Syntax.DeclarativeGrammar
