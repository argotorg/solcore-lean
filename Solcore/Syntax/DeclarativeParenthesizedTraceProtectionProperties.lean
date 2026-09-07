import Solcore.Syntax.DeclarativeParenthesizedTraceGrammar
import Solcore.Syntax.DeclarativeParseDiagnosticCascadeProperties

/-! Parenthesis and comma tokens emit no events. Protected child traces keep
their source order and every duplicate through all successful branches. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {elementTrace : SourceId → Nat → Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat} {text : String} {lexical : List SourceSpan}

theorem ParenthesizedTupleTailTraceParses.cascadeFilters
    (elementProtected : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      ParseDiagnosticCascadeFilters text lexical trace trace)
    {input output : Remainder} {values : List Syntax.Expr} {closingSpan : SourceSpan} {trace : List ParseDiagnostic}
    (parsed : ParenthesizedTupleTailTraceParses elementTrace source endByte input values closingSpan output trace) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  induction parsed with
  | trailing => exact .nil
  | final _ _ _ _ child _ _ _ => exact elementProtected child
  | next _ _ _ _ child _ _ ih => exact (elementProtected child).append ih

theorem ParenthesizedExpressionTraceParses.cascadeFilters
    (elementProtected : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      ParseDiagnosticCascadeFilters text lexical trace trace)
    {input output : Remainder} {value : Syntax.Expr} {trace : List ParseDiagnostic}
    (parsed : ParenthesizedExpressionTraceParses elementTrace source endByte input value output trace) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases parsed with
  | empty => exact .nil
  | group _ _ _ _ child _ _ _ => exact elementProtected child
  | tuple _ _ _ _ child _ tail => exact (elementProtected child).append (tail.cascadeFilters elementProtected)

end Solcore.Syntax.DeclarativeGrammar
