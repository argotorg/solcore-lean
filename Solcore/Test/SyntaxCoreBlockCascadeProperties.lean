import Solcore.Syntax.DeclarativeCoreBlockCascadeProperties

/-! Normalization consumers retain the exact delayed body-validation suffix. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxCoreBlockCascadeProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar

variable
  {statementTrace : SourceId → Nat → Remainder → Statement → Remainder →
    List ParseDiagnostic → Prop}
  {policy : CoreBlockTailPolicy} {source : SourceId} {endByte : Nat}
  {input output : Remainder} {body : Block} {trace validationEvents : List ParseDiagnostic}
  (parsed : CoreBlockTraceParses statementTrace policy source endByte input body output trace)
  (validated : CoreBlockTailsDiagnosticTrace policy body.value validationEvents)

example : ∃ openingSpan closingSpan afterOpening statementEvents,
    ExactTokenParses (.symbol .leftBrace) input openingSpan afterOpening ∧
    CoreBlockItemsTraceParses statementTrace source endByte afterOpening body.value
      closingSpan output statementEvents ∧
    body.span = SourceSpan.cover openingSpan closingSpan ∧
    trace = statementEvents ++ validationEvents := parsed.split_at_validation validated

example (text : String) (lexical : List SourceSpan) {kept : List ParseDiagnostic} :
    ParseDiagnosticCascadeFilters text lexical trace kept ↔
      ∃ statementEvents keptStatementEvents,
        trace = statementEvents ++ validationEvents ∧
        ParseDiagnosticCascadeFilters text lexical statementEvents keptStatementEvents ∧
        kept = keptStatementEvents ++ validationEvents :=
  parsed.cascadeFilters_iff validated text lexical

example {text : String} {lexical : List SourceSpan} {kept : List ParseDiagnostic}
    (filtered : ParseDiagnosticCascadeFilters text lexical trace kept) :
    ∃ leading, kept = leading ++ validationEvents :=
  parsed.normalized_validation_suffix validated filtered

include parsed in
/-- Every normalized result retains both identical validation occurrences in
their final positions, even if earlier statement reports were removed. -/
theorem repeated_validation_reports_remain_last
    {event : ParseDiagnostic}
    (checked : CoreBlockTailsDiagnosticTrace policy body.value [event, event])
    {text : String} {lexical : List SourceSpan} {kept : List ParseDiagnostic}
    (filtered : ParseDiagnosticCascadeFilters text lexical trace kept) :
    ∃ leading, kept = leading ++ [event, event] :=
  parsed.normalized_validation_suffix checked filtered

end Solcore.Test.SyntaxCoreBlockCascadeProperties
