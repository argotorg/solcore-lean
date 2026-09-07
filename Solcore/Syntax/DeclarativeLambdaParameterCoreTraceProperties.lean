import Solcore.Syntax.DeclarativeLambdaParameterCoreTraceGrammar
import Solcore.Syntax.DeclarativeLambdaParameterRawRejectionTraceProperties

/-! Pair selection preserves exact raw outcomes and protected event order.
Opposite branches cannot compete on one input. The joint specification states
uniqueness and disjointness, not existence of an execution or derivation. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {source : SourceId} {endByte : Nat}

theorem LambdaParameterCoreTraceParses.result_unique
    {input afterLeft afterRight : Remainder} {left right : Syntax.LambdaParameter}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : LambdaParameterCoreTraceParses source endByte input left afterLeft leftTrace)
    (rightParsed : LambdaParameterCoreTraceParses source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  cases leftParsed with
  | ordinary absent leftRaw =>
      cases rightParsed with
      | ordinary _ rightRaw => exact ordinaryLambdaParameterTraceExactOutcomeSpec.successResultUnique leftRaw rightRaw
      | comptime present _ => exact False.elim (absent present)
  | comptime present leftRaw =>
      cases rightParsed with
      | ordinary absent _ => exact False.elim (absent present)
      | comptime _ rightRaw => exact comptimeLambdaParameterTraceExactOutcomeSpec.successResultUnique leftRaw rightRaw

theorem LambdaParameterCoreTraceRejects.result_unique
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftRejected : LambdaParameterCoreTraceRejects source endByte input afterLeft leftReport leftTrace)
    (rightRejected : LambdaParameterCoreTraceRejects source endByte input afterRight rightReport rightTrace) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace := by
  cases leftRejected with
  | ordinary absent leftRaw =>
      cases rightRejected with
      | ordinary _ rightRaw => exact ordinaryLambdaParameterTraceExactOutcomeSpec.rejectResultUnique leftRaw rightRaw
      | comptime present _ => exact False.elim (absent present)
  | comptime present leftRaw =>
      cases rightRejected with
      | ordinary absent _ => exact False.elim (absent present)
      | comptime _ rightRaw => exact comptimeLambdaParameterTraceExactOutcomeSpec.rejectResultUnique leftRaw rightRaw

theorem LambdaParameterCoreTraceRejects.disjoint_success
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : LambdaParameterCoreTraceRejects source endByte input rejected report trace) :
    ¬ ∃ value output events, LambdaParameterCoreTraceParses source endByte input value output events := by
  rintro ⟨value, output, events, parsed⟩
  cases rejection with
  | ordinary absent rawRejected =>
      cases parsed with
      | ordinary _ rawParsed =>
          exact ordinaryLambdaParameterTraceExactOutcomeSpec.successRejectDisjoint rawRejected ⟨_, _, _, rawParsed⟩
      | comptime present _ => exact absent present
  | comptime present rawRejected =>
      cases parsed with
      | ordinary absent _ => exact absent present
      | comptime _ rawParsed =>
          exact comptimeLambdaParameterTraceExactOutcomeSpec.successRejectDisjoint rawRejected ⟨_, _, _, rawParsed⟩

theorem LambdaParameterCoreTraceParses.output_window
    {input output : Remainder} {value : Syntax.LambdaParameter} {trace : List ParseDiagnostic}
    (parsed : LambdaParameterCoreTraceParses source endByte input value output trace) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex := by
  cases parsed with
  | ordinary _ raw => exact raw.output_window
  | comptime _ raw => exact raw.output_window

theorem LambdaParameterCoreTraceParses.cascadeFilters
    {input output : Remainder} {value : Syntax.LambdaParameter} {trace : List ParseDiagnostic}
    (parsed : LambdaParameterCoreTraceParses source endByte input value output trace)
    (text : String) (lexical : List SourceSpan) : ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases parsed with
  | ordinary _ raw => exact raw.cascadeFilters text lexical
  | comptime _ raw => exact raw.cascadeFilters text lexical

theorem LambdaParameterCoreTraceRejects.cascadeFilters
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : LambdaParameterCoreTraceRejects source endByte input rejected report trace)
    (text : String) (lexical : List SourceSpan) : ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases rejection with
  | ordinary _ raw => exact raw.cascadeFilters text lexical
  | comptime _ raw => exact raw.cascadeFilters text lexical

theorem lambdaParameterCoreTraceExactOutcomeSpec :
    TraceExactOutcomeSpec LambdaParameterCoreTraceParses LambdaParameterCoreTraceRejects source endByte where
  successResultUnique := LambdaParameterCoreTraceParses.result_unique
  rejectResultUnique := LambdaParameterCoreTraceRejects.result_unique
  successRejectDisjoint := LambdaParameterCoreTraceRejects.disjoint_success

/-- A selected comptime rejection cannot fail at the marker or following name. -/
theorem ComptimeLambdaParameterTraceRejects.tail_of_prefix
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (present : ComptimeLambdaParameterStartsAt input)
    (rejection : ComptimeLambdaParameterTraceRejects source endByte input rejected report trace) :
    ∃ markerSpan afterMarker afterName name nameEvents tailEvents,
      ExactTokenParses (.identifier ContextualKeyword.comptime.spelling) input markerSpan afterMarker ∧
      IdentifierTraceParses afterMarker name afterName nameEvents ∧
      ComptimeLambdaParameterTailTraceRejects markerSpan name
        source endByte afterName rejected report tailEvents ∧ trace = nameEvents ++ tailEvents := by
  rcases present with ⟨selectedMarker, selectedName, spelling, markerToken, nameToken⟩
  cases rejection with
  | markerMissing absent _ => exact False.elim (absent ⟨selectedMarker, markerToken⟩)
  | nameRejected markerSpan marker absent _ =>
      rcases marker with ⟨_, rfl⟩
      exact False.elim (absent ⟨selectedName, spelling, nameToken⟩)
  | tailRejected markerSpan marker nameParsed tail => exact ⟨_, _, _, _, _, _, marker, nameParsed, tail, rfl⟩

end Solcore.Syntax.DeclarativeGrammar
