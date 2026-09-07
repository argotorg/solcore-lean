import Solcore.Syntax.DeclarativeLiteralDiagnosticTraceGrammar
import Solcore.Syntax.DeclarativeIdentifierTraceGrammar
import Solcore.Syntax.DeclarativeCoreIdentifierExpressionOutcomeGrammar

/-! Independent Boolean-first names and identifier-expression traces. Checked
ordinary names retain their complete located spelling diagnostics. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive ExpressionNameTraceParses (source : SourceId) (endByte : Nat) :
    Remainder → Syntax.Identifier → Remainder → List ParseDiagnostic → Prop where
  | boolean {input output : Remainder} {name : Syntax.Identifier} {trace : List ParseDiagnostic}
      (parsed : BooleanIdentifierTraceParses source endByte input name output trace) :
      ExpressionNameTraceParses source endByte input name output trace
  | identifier {input output : Remainder} {name : Syntax.Identifier} {trace : List ParseDiagnostic}
      (booleanAbsent : BooleanPatternAbsentAt input)
      (parsed : IdentifierTraceParses input name output trace) :
      ExpressionNameTraceParses source endByte input name output trace

/-- Rejection occurs only after both Boolean guards fail. Identifier failure
is uncommitted and does not emit a checked-spelling event. -/
def ExpressionNameTraceRejects (source : SourceId) (endByte : Nat)
    (input rejected : Remainder) (diagnostic : ParseDiagnostic)
    (trace : List ParseDiagnostic) : Prop :=
  BooleanPatternAbsentAt input ∧ IdentifierRejects input rejected ∧
    RejectAtReports source endByte { head := .identifier, tail := [] }
      .expression rejected diagnostic ∧ trace = []

inductive IdentifierExpressionTraceParses (source : SourceId) (endByte : Nat) :
    Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop where
  | parsed {input output : Remainder} {name : Syntax.Identifier} {trace : List ParseDiagnostic}
      (nameParsed : ExpressionNameTraceParses source endByte input name output trace) :
      IdentifierExpressionTraceParses source endByte input {
        span := name.span, value := .identifier name
      } output trace

abbrev IdentifierExpressionTraceRejects := ExpressionNameTraceRejects

end Solcore.Syntax.DeclarativeGrammar
