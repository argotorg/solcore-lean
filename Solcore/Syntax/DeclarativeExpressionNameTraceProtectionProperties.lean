import Solcore.Syntax.DeclarativeExpressionNameTraceProperties
import Solcore.Syntax.DeclarativeIdentifierCascadeProperties

/-! Checked-name events survive lexical cascade filtering unchanged, including
their complete spans, spellings, source order, and repeated occurrences. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

theorem IdentifierTraceParses.cascadeFilters
    {input output : Remainder} {name : Syntax.Identifier} {trace : List ParseDiagnostic}
    (parsed : IdentifierTraceParses input name output trace) (text : String) (lexical : List SourceSpan) :
    ParseDiagnosticCascadeFilters text lexical trace trace :=
  (identifierTraceParses_iff.mp parsed).2.cascadeFilters text lexical

theorem ExpressionNameTraceParses.cascadeFilters
    {source : SourceId} {endByte : Nat} {input output : Remainder}
    {name : Syntax.Identifier} {trace : List ParseDiagnostic}
    (parsed : ExpressionNameTraceParses source endByte input name output trace)
    (text : String) (lexical : List SourceSpan) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases parsed with
  | boolean parsed => rw [parsed.2]; exact .nil
  | identifier _ parsed => exact parsed.cascadeFilters text lexical

theorem IdentifierExpressionTraceParses.cascadeFilters
    {source : SourceId} {endByte : Nat} {input output : Remainder}
    {value : Syntax.Expr} {trace : List ParseDiagnostic}
    (parsed : IdentifierExpressionTraceParses source endByte input value output trace)
    (text : String) (lexical : List SourceSpan) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases parsed with
  | parsed name => exact name.cascadeFilters text lexical

/-- Rejected names have no committed event; their separate failure report is
not covered by this preservation claim. -/
theorem ExpressionNameTraceRejects.cascadeFilters
    {source : SourceId} {endByte : Nat} {input rejected : Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ExpressionNameTraceRejects source endByte input rejected diagnostic trace)
    (text : String) (lexical : List SourceSpan) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  rw [rejection.2.2.2]
  exact .nil

end Solcore.Syntax.DeclarativeGrammar
