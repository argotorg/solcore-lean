import Solcore.Syntax.DeclarativeReturnStatementTraceGrammar
import Solcore.Syntax.DeclarativeBlockStatementTraceGrammar
import Solcore.Syntax.DeclarativeCoreBlockTailTraceProperties

/-! Complete protected traces compose through returns and raw block
statements. Recovered unexpected-token reports are not presumed protected. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {expressionTrace : SourceId → Nat → Remainder → Syntax.Expr →
    Remainder → List ParseDiagnostic → Prop}
  {statementTrace : SourceId → Nat → Remainder → Syntax.Statement →
    Remainder → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat} {text : String} {lexical : List SourceSpan}

theorem OptionalReturnValueTraceParses.cascadeFilters
    (expressionProtected : ∀ {input value output trace},
      expressionTrace source endByte input value output trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    {input output : Remainder} {value : Option Syntax.Expr} {trace : List ParseDiagnostic}
    (parsed : OptionalReturnValueTraceParses expressionTrace source endByte input value output trace) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases parsed with
  | absent => exact .nil
  | present _ value => exact expressionProtected value

theorem ReturnStatementTraceParses.cascadeFilters
    (expressionProtected : ∀ {input value output trace},
      expressionTrace source endByte input value output trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    {input output : Remainder} {statement : Syntax.Statement} {trace : List ParseDiagnostic}
    (parsed : ReturnStatementTraceParses expressionTrace source endByte input statement output trace) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases parsed with
  | parsed _ _ _ value _ => exact value.cascadeFilters expressionProtected

theorem CoreBlockItemsTraceParses.cascadeFilters
    (statementProtected : ∀ {input statement output trace},
      statementTrace source endByte input statement output trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    {input output : Remainder} {statements : List Syntax.Statement}
    {closingSpan : SourceSpan} {trace : List ParseDiagnostic}
    (parsed : CoreBlockItemsTraceParses statementTrace source endByte
      input statements closingSpan output trace) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  induction parsed with
  | close => exact .nil
  | next _ _ statement _ _ ih => exact (statementProtected statement).append ih

/-- Delayed validation emits only protected constraints, so a raw block
whose statement events are protected retains its entire successful trace. -/
theorem CoreBlockTraceParses.cascadeFilters
    (statementProtected : ∀ {input statement output trace},
      statementTrace source endByte input statement output trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    {policy : CoreBlockTailPolicy} {input output : Remainder} {body : Syntax.Block}
    {trace : List ParseDiagnostic}
    (parsed : CoreBlockTraceParses statementTrace policy source endByte input body output trace) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases parsed with
  | parsed _ _ _ items validation =>
      exact (items.cascadeFilters statementProtected).append (validation.cascadeFilters text lexical)

theorem BlockStatementTraceParses.cascadeFilters
    (statementProtected : ∀ {input statement output trace},
      statementTrace source endByte input statement output trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    {input output : Remainder} {statement : Syntax.Statement} {trace : List ParseDiagnostic}
    (parsed : BlockStatementTraceParses statementTrace source endByte input statement output trace) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases parsed with
  | parsed body => exact body.cascadeFilters statementProtected

end Solcore.Syntax.DeclarativeGrammar
