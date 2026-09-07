import Solcore.Syntax.DeclarativeNamedParameterTailTraceGrammar
import Solcore.Syntax.DeclarativeTypedParameterFinishingTraceProperties
import Solcore.Syntax.DeclarativeTypeExprTraceStructuralProperties
import Solcore.Syntax.DeclarativeTypeExprTraceOutcomeProperties
import Solcore.Syntax.DeclarativePrimitiveExactnessProperties

/-! Named-parameter tail traces have exact outcomes and protected ordered
events. Complete recursive type laws discharge child premises unconditionally;
colon guards distinguish the error-valued success from typed success/failure.
The joint bundle is exactness, not a separate outcome-existence assertion. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {start errorSpan : SourceSpan} {marker : Option SourceSpan} {name : Syntax.Identifier}
  {source : SourceId} {endByte : Nat}

theorem NamedParameterTailTraceParses.output_window
    {input output : Remainder} {value : Syntax.FunctionParameter} {trace : List ParseDiagnostic}
    (parsed : NamedParameterTailTraceParses start marker name errorSpan source endByte input value output trace) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex := by
  cases parsed with
  | typed _ colon typed _ =>
      rcases colon with ⟨_, rfl⟩
      exact typed.output_window
  | typeMissing => exact ⟨rfl, rfl⟩

theorem NamedParameterTailTraceParses.result_unique
    {input afterLeft afterRight : Remainder} {left right : Syntax.FunctionParameter}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : NamedParameterTailTraceParses start marker name errorSpan source endByte input left afterLeft leftTrace)
    (rightParsed : NamedParameterTailTraceParses start marker name errorSpan source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  cases leftParsed with
  | typed span colon typed finished =>
      cases rightParsed with
      | typeMissing absent _ => exact False.elim (absent ⟨span, colon.1⟩)
      | typed _ otherColon otherTyped otherFinished =>
          rcases colon.result_unique otherColon with ⟨rfl, rfl⟩
          rcases typed.result_unique otherTyped with ⟨rfl, rfl, rfl⟩
          cases finished.trace_unique otherFinished
          exact ⟨rfl, rfl, rfl⟩
  | typeMissing absent finished =>
      cases rightParsed with
      | typed span colon _ _ => exact False.elim (absent ⟨span, colon.1⟩)
      | typeMissing _ otherFinished => exact ⟨rfl, rfl, finished.trace_unique otherFinished⟩

theorem NamedParameterTailTraceRejects.colon_present
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : NamedParameterTailTraceRejects start marker name errorSpan source endByte input rejected report trace) :
    ∃ span, TokenAt input.tokens input.endIndex input.cursor { span, value := .symbol .colon } := by
  cases rejection with
  | typeRejected span colon _ => exact ⟨span, colon.1⟩

theorem NamedParameterTailTraceRejects.result_unique
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftRejected : NamedParameterTailTraceRejects start marker name errorSpan source endByte
      input afterLeft leftReport leftTrace)
    (rightRejected : NamedParameterTailTraceRejects start marker name errorSpan source endByte
      input afterRight rightReport rightTrace) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace := by
  cases leftRejected with
  | typeRejected _ colon rejected =>
      cases rightRejected with
      | typeRejected _ otherColon otherRejected =>
          rcases colon.result_unique otherColon with ⟨rfl, rfl⟩
          exact rejected.result_unique otherRejected

theorem NamedParameterTailTraceRejects.disjoint_success
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : NamedParameterTailTraceRejects start marker name errorSpan source endByte input rejected report trace) :
    ¬ ∃ value output events, NamedParameterTailTraceParses start marker name errorSpan source endByte input value output events := by
  rintro ⟨value, output, events, parsed⟩
  cases rejection with
  | typeRejected span colon rejected =>
      cases parsed with
      | typeMissing absent _ => exact absent ⟨span, colon.1⟩
      | typed _ otherColon typed _ =>
          rcases colon.result_unique otherColon with ⟨rfl, rfl⟩
          exact rejected.disjoint_success ⟨_, _, _, typed⟩

theorem NamedParameterTailTraceParses.cascadeFilters
    {input output : Remainder} {value : Syntax.FunctionParameter} {trace : List ParseDiagnostic}
    (parsed : NamedParameterTailTraceParses start marker name errorSpan source endByte input value output trace)
    (text : String) (lexical : List SourceSpan) : ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases parsed with
  | typed _ _ typed finished => exact (typed.cascadeFilters text lexical).append (finished.cascadeFilters text lexical)
  | typeMissing _ finished => exact finished.cascadeFilters text lexical

theorem NamedParameterTailTraceRejects.cascadeFilters
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : NamedParameterTailTraceRejects start marker name errorSpan source endByte input rejected report trace)
    (text : String) (lexical : List SourceSpan) : ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases rejection with
  | typeRejected _ _ rejected => exact rejected.cascadeFilters text lexical

theorem namedParameterTailTraceExactOutcomeSpec (start : SourceSpan) (marker : Option SourceSpan)
    (name : Syntax.Identifier) (errorSpan : SourceSpan) {source : SourceId} {endByte : Nat} :
    TraceExactOutcomeSpec (NamedParameterTailTraceParses start marker name errorSpan)
      (NamedParameterTailTraceRejects start marker name errorSpan) source endByte where
  successResultUnique := NamedParameterTailTraceParses.result_unique
  rejectResultUnique := NamedParameterTailTraceRejects.result_unique
  successRejectDisjoint := NamedParameterTailTraceRejects.disjoint_success

end Solcore.Syntax.DeclarativeGrammar
