import Solcore.Syntax.DeclarativeDelimitedNoTrailingRejectionTraceGrammar

/-! Independent array-literal traces wrap an allow-empty no-trailing bracketed
list. The wrapper changes only the AST: remainder, reports, and events are
unchanged. This relation is not restricted to a dispatch-selected opening. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive ArrayLiteralTraceParses
    (elementTrace : SourceId → Nat → Remainder → Syntax.Expr →
      Remainder → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop where
  | parsed {input output : Remainder} {values : DelimitedList Syntax.Expr}
      {trace : List ParseDiagnostic}
      (valuesParsed : NoTrailingDelimitedListTraceParses .leftBracket .rightBracket true
        elementTrace source endByte input values output trace) :
      ArrayLiteralTraceParses elementTrace source endByte input
        { span := values.span, value := .array values } output trace

abbrev ArrayLiteralTraceRejects
    (elementTrace : SourceId → Nat → Remainder → Syntax.Expr →
      Remainder → List ParseDiagnostic → Prop)
    (elementRejects : SourceId → Nat → Remainder → Remainder →
      ParseDiagnostic → List ParseDiagnostic → Prop) :=
  NoTrailingDelimitedListTraceRejects .leftBracket .rightBracket true .expression
    elementTrace elementRejects

end Solcore.Syntax.DeclarativeGrammar
