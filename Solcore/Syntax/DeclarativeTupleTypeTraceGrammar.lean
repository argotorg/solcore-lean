import Solcore.Syntax.DeclarativeDelimitedTrailingTraceGrammar

/-! Raw tuple-type success maps the complete trailing-enabled list to a type,
including empty and singleton lists. It never introduces expression grouping. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

def tupleTypeTraceValue (values : DelimitedList Syntax.TypeExpr) : Syntax.TypeExpr :=
  { span := values.span, value := .tuple values.elements }

inductive TupleTypeTraceParses
    (typeTrace : SourceId → Nat → Remainder → Syntax.TypeExpr →
      Remainder → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop where
  | parsed {input output : Remainder} {values : DelimitedList Syntax.TypeExpr}
      {trace : List ParseDiagnostic}
      (elements : TrailingDelimitedListTraceParses .leftParen .rightParen true
        typeTrace source endByte input values output trace) :
      TupleTypeTraceParses typeTrace source endByte input (tupleTypeTraceValue values) output trace

end Solcore.Syntax.DeclarativeGrammar
