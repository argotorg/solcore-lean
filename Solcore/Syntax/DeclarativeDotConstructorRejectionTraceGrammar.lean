import Solcore.Syntax.DeclarativeDotConstructorTraceGrammar
import Solcore.Syntax.DeclarativeDelimitedNoTrailingRejectionTraceGrammar
import Solcore.Syntax.DeclarativeCoreExpressionDotConstructorOutcomeGrammar

/-! Exact raw leading-dot rejection traces. A missing dot is represented even
outside dispatcher selection. Optional arguments commit only on a left parenthesis;
successful name events precede argument rejection events and the report is uncommitted. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive OptionalDotConstructorArgumentsTraceRejects
    (elementTrace : SourceId → Nat → Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop)
    (elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | present {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
      (openingSpan : SourceSpan)
      (openingToken : TokenAt input.tokens input.endIndex input.cursor {
        span := openingSpan, value := .symbol .leftParen })
      (argumentsRejected : NoTrailingDelimitedListTraceRejects .leftParen .rightParen true .expression
        elementTrace elementRejects source endByte input rejected diagnostic trace) :
      OptionalDotConstructorArgumentsTraceRejects elementTrace elementRejects source endByte
        input rejected diagnostic trace

inductive DotConstructorTraceRejects
    (elementTrace : SourceId → Nat → Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop)
    (elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | dotMissing {input : Remainder} {diagnostic : ParseDiagnostic}
      (dotAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .dot))
      (reported : RejectAtReports source endByte { head := .symbol .dot, tail := [] }
        .expression input diagnostic) :
      DotConstructorTraceRejects elementTrace elementRejects source endByte input input diagnostic []
  | nameRejected {input afterDot rejected : Remainder} {diagnostic : ParseDiagnostic}
      {trace : List ParseDiagnostic} (dotSpan : SourceSpan)
      (dotParsed : ExactTokenParses (.symbol .dot) input dotSpan afterDot)
      (nameRejected : ExpressionNameTraceRejects source endByte afterDot rejected diagnostic trace) :
      DotConstructorTraceRejects elementTrace elementRejects source endByte input rejected diagnostic trace
  | argumentsRejected {input afterDot afterName rejected : Remainder} {name : Syntax.Identifier}
      {diagnostic : ParseDiagnostic} {nameEvents argumentEvents : List ParseDiagnostic} (dotSpan : SourceSpan)
      (dotParsed : ExactTokenParses (.symbol .dot) input dotSpan afterDot)
      (nameParsed : ExpressionNameTraceParses source endByte afterDot name afterName nameEvents)
      (argumentsRejected : OptionalDotConstructorArgumentsTraceRejects elementTrace elementRejects
        source endByte afterName rejected diagnostic argumentEvents) :
      DotConstructorTraceRejects elementTrace elementRejects source endByte
        input rejected diagnostic (nameEvents ++ argumentEvents)

end Solcore.Syntax.DeclarativeGrammar
