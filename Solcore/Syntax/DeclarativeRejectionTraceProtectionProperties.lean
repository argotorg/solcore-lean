import Solcore.Syntax.DeclarativeStatementTraceProtectionProperties
import Solcore.Syntax.DeclarativeReturnStatementRejectionTraceGrammar

/-! Protected earlier events survive normalization even when parsing later
rejects. The uncommitted final report is not asserted to be protected. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {expressionTrace : SourceId → Nat → Remainder → Syntax.Expr →
    Remainder → List ParseDiagnostic → Prop}
  {expressionRejects : SourceId → Nat → Remainder → Remainder →
    ParseDiagnostic → List ParseDiagnostic → Prop}
  {statementTrace : SourceId → Nat → Remainder → Syntax.Statement →
    Remainder → List ParseDiagnostic → Prop}
  {statementRejects : SourceId → Nat → Remainder → Remainder →
    ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat} {text : String} {lexical : List SourceSpan}

theorem OptionalReturnValueTraceRejects.cascadeFilters
    (rejectProtected : ∀ {input rejected diagnostic trace},
      expressionRejects source endByte input rejected diagnostic trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : OptionalReturnValueTraceRejects expressionRejects source endByte
      input rejected diagnostic trace) : ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases rejection with
  | expressionRejected _ expression => exact rejectProtected expression

theorem ReturnStatementTraceRejects.cascadeFilters
    (successProtected : ∀ {input value output trace},
      expressionTrace source endByte input value output trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    (rejectProtected : ∀ {input rejected diagnostic trace},
      expressionRejects source endByte input rejected diagnostic trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ReturnStatementTraceRejects expressionTrace expressionRejects source endByte
      input rejected diagnostic trace) : ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases rejection with
  | markerRejected => exact .nil
  | valueRejected _ _ value => exact value.cascadeFilters rejectProtected
  | semicolonRejected _ _ value _ _ => exact value.cascadeFilters successProtected

theorem CoreBlockItemsTraceRejects.cascadeFilters
    (successProtected : ∀ {input statement output trace},
      statementTrace source endByte input statement output trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    (rejectProtected : ∀ {input rejected diagnostic trace},
      statementRejects source endByte input rejected diagnostic trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : CoreBlockItemsTraceRejects statementTrace statementRejects source endByte
      input rejected diagnostic trace) : ParseDiagnosticCascadeFilters text lexical trace trace := by
  induction rejection with
  | missingClose => exact .nil
  | statementRejected _ _ statement => exact rejectProtected statement
  | laterRejected _ _ statement _ _ ih => exact (successProtected statement).append ih

theorem CoreBlockTraceRejects.cascadeFilters
    (successProtected : ∀ {input statement output trace},
      statementTrace source endByte input statement output trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    (rejectProtected : ∀ {input rejected diagnostic trace},
      statementRejects source endByte input rejected diagnostic trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    {policy : CoreBlockTailPolicy} {input rejected : Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : CoreBlockTraceRejects statementTrace statementRejects policy source endByte
      input rejected diagnostic trace) : ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases rejection with
  | openingMissing => exact .nil
  | itemsRejected _ _ items => exact items.cascadeFilters successProtected rejectProtected

theorem BlockStatementTraceRejects.cascadeFilters
    (successProtected : ∀ {input statement output trace},
      statementTrace source endByte input statement output trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    (rejectProtected : ∀ {input rejected diagnostic trace},
      statementRejects source endByte input rejected diagnostic trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : BlockStatementTraceRejects statementTrace statementRejects source endByte
      input rejected diagnostic trace) : ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases rejection with
  | rejected body => exact body.cascadeFilters successProtected rejectProtected

end Solcore.Syntax.DeclarativeGrammar
