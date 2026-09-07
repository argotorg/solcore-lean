import Solcore.Syntax.DeclarativeCoreBlockTraceProperties
import Solcore.Syntax.DeclarativeCoreBlockTailCascadeProperties

/-! Complete raw-block trace normalization keeps the delayed validation suffix.
The body AST determines that suffix, independently of earlier statement events. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable
  {statementTrace : SourceId → Nat → Remainder → Syntax.Statement →
    Remainder → List ParseDiagnostic → Prop}
  {policy : CoreBlockTailPolicy} {source : SourceId} {endByte : Nat}
  {input output : Remainder} {body : Syntax.Block} {trace : List ParseDiagnostic}

/-- The block trace is the ordered statement events followed by the whole
body's validation events. Any independent validation trace fixes that suffix. -/
theorem CoreBlockTraceParses.split_at_validation
    (parsed : CoreBlockTraceParses statementTrace policy source endByte input body output trace)
    {validationEvents : List ParseDiagnostic}
    (validated : CoreBlockTailsDiagnosticTrace policy body.value validationEvents) :
    ∃ openingSpan closingSpan afterOpening statementEvents,
      ExactTokenParses (.symbol .leftBrace) input openingSpan afterOpening ∧
      CoreBlockItemsTraceParses statementTrace source endByte afterOpening body.value
        closingSpan output statementEvents ∧
      body.span = SourceSpan.cover openingSpan closingSpan ∧
      trace = statementEvents ++ validationEvents := by
  cases parsed with
  | parsed opening closing token items actual =>
      exact ⟨opening, closing, _, _, token, items, rfl,
        congrArg (fun tail => _ ++ tail) (actual.output_unique validated)⟩

/-- Normalization filters only the statement-event prefix. Every validation
report remains at the end with its full payload, source span, and multiplicity. -/
theorem CoreBlockTraceParses.cascadeFilters_iff
    (parsed : CoreBlockTraceParses statementTrace policy source endByte input body output trace)
    {validationEvents kept : List ParseDiagnostic}
    (validated : CoreBlockTailsDiagnosticTrace policy body.value validationEvents)
    (text : String) (lexical : List SourceSpan) :
    ParseDiagnosticCascadeFilters text lexical trace kept ↔
      ∃ statementEvents keptStatementEvents,
        trace = statementEvents ++ validationEvents ∧
        ParseDiagnosticCascadeFilters text lexical statementEvents keptStatementEvents ∧
        kept = keptStatementEvents ++ validationEvents := by
  constructor
  · intro filtered
    rcases parsed.split_at_validation validated with
      ⟨_, _, _, statementEvents, _, _, _, traceEq⟩
    rw [traceEq] at filtered
    rcases (validated.append_cascadeFilters_iff text lexical).mp filtered with
      ⟨keptEvents, leading, keptEq⟩
    exact ⟨statementEvents, keptEvents, traceEq, leading, keptEq⟩
  · rintro ⟨statementEvents, keptEvents, traceEq, leading, keptEq⟩
    rw [traceEq, keptEq]
    exact validated.append_cascadeFilters leading

/-- With a fixed validation trace, every normalized block trace ends with that
unchanged suffix, including a suffix containing repeated identical reports. -/
theorem CoreBlockTraceParses.normalized_validation_suffix
    (parsed : CoreBlockTraceParses statementTrace policy source endByte input body output trace)
    {validationEvents kept : List ParseDiagnostic}
    (validated : CoreBlockTailsDiagnosticTrace policy body.value validationEvents)
    {text : String} {lexical : List SourceSpan}
    (filtered : ParseDiagnosticCascadeFilters text lexical trace kept) :
    ∃ keptStatementEvents, kept = keptStatementEvents ++ validationEvents := by
  rcases (parsed.cascadeFilters_iff validated text lexical).mp filtered with
    ⟨_, keptEvents, _, _, keptEq⟩
  exact ⟨keptEvents, keptEq⟩

end Solcore.Syntax.DeclarativeGrammar
