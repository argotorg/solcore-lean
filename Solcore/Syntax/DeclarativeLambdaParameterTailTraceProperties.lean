import Solcore.Syntax.DeclarativeLambdaParameterTailTraceGrammar
import Solcore.Syntax.DeclarativeNamedParameterTailTraceProperties

/-! Exact lambda-tail outcomes retain the named-tail carrier and ordered
protected events. Colon guards separate inference/missing-type success from
typed success or rejection, independently of executable state or validity. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {source : SourceId} {endByte : Nat} {name : Syntax.Identifier} {marker : SourceSpan}

theorem OrdinaryLambdaParameterTailTraceParses.output_window
    {input output : Remainder} {value : Syntax.LambdaParameter} {trace : List ParseDiagnostic}
    (parsed : OrdinaryLambdaParameterTailTraceParses name source endByte input value output trace) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex := by
  cases parsed with
  | typed _ tail => exact tail.output_window
  | inferred => exact ⟨rfl, rfl⟩

theorem OrdinaryLambdaParameterTailTraceParses.result_unique
    {input afterLeft afterRight : Remainder} {left right : Syntax.LambdaParameter}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : OrdinaryLambdaParameterTailTraceParses name source endByte input left afterLeft leftTrace)
    (rightParsed : OrdinaryLambdaParameterTailTraceParses name source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  cases leftParsed with
  | typed present tail =>
      cases rightParsed with
      | inferred absent => exact False.elim (absent present)
      | typed _ otherTail =>
          rcases tail.result_unique otherTail with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩
  | inferred absent =>
      cases rightParsed with
      | typed present _ => exact False.elim (absent present)
      | inferred => exact ⟨rfl, rfl, rfl⟩

theorem OrdinaryLambdaParameterTailTraceParses.cascadeFilters
    {input output : Remainder} {value : Syntax.LambdaParameter} {trace : List ParseDiagnostic}
    (parsed : OrdinaryLambdaParameterTailTraceParses name source endByte input value output trace)
    (text : String) (lexical : List SourceSpan) : ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases parsed with
  | typed _ tail => exact tail.cascadeFilters text lexical
  | inferred => exact .nil

theorem OrdinaryLambdaParameterTailTraceRejects.result_unique
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftRejected : OrdinaryLambdaParameterTailTraceRejects name source endByte input afterLeft leftReport leftTrace)
    (rightRejected : OrdinaryLambdaParameterTailTraceRejects name source endByte input afterRight rightReport rightTrace) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace :=
  NamedParameterTailTraceRejects.result_unique leftRejected rightRejected

theorem OrdinaryLambdaParameterTailTraceRejects.disjoint_success
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : OrdinaryLambdaParameterTailTraceRejects name source endByte input rejected report trace) :
    ¬ ∃ value output events, OrdinaryLambdaParameterTailTraceParses name source endByte input value output events := by
  rintro ⟨value, output, events, parsed⟩
  cases parsed with
  | typed _ tail => exact NamedParameterTailTraceRejects.disjoint_success rejection ⟨_, _, _, tail⟩
  | inferred absent => exact absent rejection.colon_present

theorem OrdinaryLambdaParameterTailTraceRejects.cascadeFilters
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : OrdinaryLambdaParameterTailTraceRejects name source endByte input rejected report trace)
    (text : String) (lexical : List SourceSpan) : ParseDiagnosticCascadeFilters text lexical trace trace :=
  NamedParameterTailTraceRejects.cascadeFilters rejection text lexical

theorem ordinaryLambdaParameterTailTraceExactOutcomeSpec (name : Syntax.Identifier) :
    TraceExactOutcomeSpec (OrdinaryLambdaParameterTailTraceParses name)
      (OrdinaryLambdaParameterTailTraceRejects name) source endByte where
  successResultUnique := OrdinaryLambdaParameterTailTraceParses.result_unique
  rejectResultUnique := OrdinaryLambdaParameterTailTraceRejects.result_unique
  successRejectDisjoint := OrdinaryLambdaParameterTailTraceRejects.disjoint_success

theorem ComptimeLambdaParameterTailTraceParses.output_window
    {input output : Remainder} {value : Syntax.LambdaParameter} {trace : List ParseDiagnostic}
    (parsed : ComptimeLambdaParameterTailTraceParses marker name source endByte input value output trace) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex := by
  cases parsed with
  | typed _ tail => exact tail.output_window
  | typeMissing => exact ⟨rfl, rfl⟩

theorem ComptimeLambdaParameterTailTraceParses.result_unique
    {input afterLeft afterRight : Remainder} {left right : Syntax.LambdaParameter}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : ComptimeLambdaParameterTailTraceParses marker name source endByte input left afterLeft leftTrace)
    (rightParsed : ComptimeLambdaParameterTailTraceParses marker name source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  cases leftParsed with
  | typed present tail =>
      cases rightParsed with
      | typeMissing absent _ => exact False.elim (absent present)
      | typed _ otherTail =>
          rcases tail.result_unique otherTail with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩
  | typeMissing absent finished =>
      cases rightParsed with
      | typed present _ => exact False.elim (absent present)
      | typeMissing _ otherFinished => exact ⟨rfl, rfl, finished.trace_unique otherFinished⟩

theorem ComptimeLambdaParameterTailTraceParses.cascadeFilters
    {input output : Remainder} {value : Syntax.LambdaParameter} {trace : List ParseDiagnostic}
    (parsed : ComptimeLambdaParameterTailTraceParses marker name source endByte input value output trace)
    (text : String) (lexical : List SourceSpan) : ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases parsed with
  | typed _ tail => exact tail.cascadeFilters text lexical
  | typeMissing _ finished => exact finished.cascadeFilters text lexical

theorem ComptimeLambdaParameterTailTraceRejects.result_unique
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftRejected : ComptimeLambdaParameterTailTraceRejects marker name source endByte input afterLeft leftReport leftTrace)
    (rightRejected : ComptimeLambdaParameterTailTraceRejects marker name source endByte input afterRight rightReport rightTrace) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace :=
  NamedParameterTailTraceRejects.result_unique leftRejected rightRejected

theorem ComptimeLambdaParameterTailTraceRejects.disjoint_success
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ComptimeLambdaParameterTailTraceRejects marker name source endByte input rejected report trace) :
    ¬ ∃ value output events, ComptimeLambdaParameterTailTraceParses marker name source endByte input value output events := by
  rintro ⟨value, output, events, parsed⟩
  cases parsed with
  | typed _ tail => exact NamedParameterTailTraceRejects.disjoint_success rejection ⟨_, _, _, tail⟩
  | typeMissing absent _ => exact absent rejection.colon_present

theorem ComptimeLambdaParameterTailTraceRejects.cascadeFilters
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ComptimeLambdaParameterTailTraceRejects marker name source endByte input rejected report trace)
    (text : String) (lexical : List SourceSpan) : ParseDiagnosticCascadeFilters text lexical trace trace :=
  NamedParameterTailTraceRejects.cascadeFilters rejection text lexical

theorem comptimeLambdaParameterTailTraceExactOutcomeSpec (marker : SourceSpan) (name : Syntax.Identifier) :
    TraceExactOutcomeSpec (ComptimeLambdaParameterTailTraceParses marker name)
      (ComptimeLambdaParameterTailTraceRejects marker name) source endByte where
  successResultUnique := ComptimeLambdaParameterTailTraceParses.result_unique
  rejectResultUnique := ComptimeLambdaParameterTailTraceRejects.result_unique
  successRejectDisjoint := ComptimeLambdaParameterTailTraceRejects.disjoint_success

end Solcore.Syntax.DeclarativeGrammar
