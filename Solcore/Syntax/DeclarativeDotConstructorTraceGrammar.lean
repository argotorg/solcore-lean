import Solcore.Syntax.DeclarativeDelimitedNoTrailingTraceGrammar
import Solcore.Syntax.DeclarativeExpressionNameTraceGrammar

/-! Independent leading-dot constructor success traces. Names are Boolean
first and checked spelling events precede argument events. Optional argument
absence is silent and leaves the remainder unchanged. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive OptionalDotConstructorArgumentsTraceParses
    (elementTrace : SourceId → Nat → Remainder → Syntax.Expr →
      Remainder → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Option (DelimitedList Syntax.Expr) → Remainder → List ParseDiagnostic → Prop where
  | absent {input : Remainder}
      (openingAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .leftParen)) :
      OptionalDotConstructorArgumentsTraceParses elementTrace source endByte input none input []
  | present {input output : Remainder} {arguments : DelimitedList Syntax.Expr}
      {trace : List ParseDiagnostic}
      (parsed : NoTrailingDelimitedListTraceParses .leftParen .rightParen true elementTrace source endByte
        input arguments output trace) :
      OptionalDotConstructorArgumentsTraceParses elementTrace source endByte input (some arguments) output trace

inductive DotConstructorTraceParses
    (elementTrace : SourceId → Nat → Remainder → Syntax.Expr →
      Remainder → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop where
  | parsed {input afterDot afterName output : Remainder} {name : Syntax.Identifier}
      {arguments : Option (DelimitedList Syntax.Expr)} {nameEvents argumentEvents : List ParseDiagnostic}
      (dotSpan : SourceSpan)
      (dotParsed : ExactTokenParses (.symbol .dot) input dotSpan afterDot)
      (nameParsed : ExpressionNameTraceParses source endByte afterDot name afterName nameEvents)
      (argumentsParsed : OptionalDotConstructorArgumentsTraceParses elementTrace source endByte
        afterName arguments output argumentEvents) :
      DotConstructorTraceParses elementTrace source endByte input {
        span := SourceSpan.cover dotSpan (arguments.map (fun values => values.span) |>.getD name.span)
        value := .dotConstructor dotSpan name arguments
      } output (nameEvents ++ argumentEvents)

end Solcore.Syntax.DeclarativeGrammar
