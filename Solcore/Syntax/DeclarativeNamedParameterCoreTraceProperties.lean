import Solcore.Syntax.DeclarativeNamedParameterCoreTraceGrammar
import Solcore.Syntax.DeclarativeNamedParameterRawRejectionTraceProperties

/-! Pair selection preserves exact raw outcomes and protected event order.
Opposite branches cannot compete on one input. The joint specification states
uniqueness and disjointness, not existence of an execution or derivation. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {source : SourceId} {endByte : Nat}

theorem NamedParameterCoreTraceParses.result_unique
    {input afterLeft afterRight : Remainder} {left right : Syntax.FunctionParameter}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : NamedParameterCoreTraceParses source endByte input left afterLeft leftTrace)
    (rightParsed : NamedParameterCoreTraceParses source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  cases leftParsed with
  | ordinary absent leftRaw =>
      cases rightParsed with
      | ordinary _ rightRaw => exact ordinaryNamedParameterTraceExactOutcomeSpec.successResultUnique leftRaw rightRaw
      | comptime present _ => exact False.elim (absent present)
  | comptime present leftRaw =>
      cases rightParsed with
      | ordinary absent _ => exact False.elim (absent present)
      | comptime _ rightRaw => exact comptimeNamedParameterTraceExactOutcomeSpec.successResultUnique leftRaw rightRaw

theorem NamedParameterCoreTraceRejects.result_unique
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftRejected : NamedParameterCoreTraceRejects source endByte input afterLeft leftReport leftTrace)
    (rightRejected : NamedParameterCoreTraceRejects source endByte input afterRight rightReport rightTrace) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace := by
  cases leftRejected with
  | ordinary absent leftRaw =>
      cases rightRejected with
      | ordinary _ rightRaw => exact ordinaryNamedParameterTraceExactOutcomeSpec.rejectResultUnique leftRaw rightRaw
      | comptime present _ => exact False.elim (absent present)
  | comptime present leftRaw =>
      cases rightRejected with
      | ordinary absent _ => exact False.elim (absent present)
      | comptime _ rightRaw => exact comptimeNamedParameterTraceExactOutcomeSpec.rejectResultUnique leftRaw rightRaw

theorem NamedParameterCoreTraceRejects.disjoint_success
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : NamedParameterCoreTraceRejects source endByte input rejected report trace) :
    ¬ ∃ value output events, NamedParameterCoreTraceParses source endByte input value output events := by
  rintro ⟨value, output, events, parsed⟩
  cases rejection with
  | ordinary absent rawRejected =>
      cases parsed with
      | ordinary _ rawParsed =>
          exact ordinaryNamedParameterTraceExactOutcomeSpec.successRejectDisjoint rawRejected ⟨_, _, _, rawParsed⟩
      | comptime present _ => exact absent present
  | comptime present rawRejected =>
      cases parsed with
      | ordinary absent _ => exact absent present
      | comptime _ rawParsed =>
          exact comptimeNamedParameterTraceExactOutcomeSpec.successRejectDisjoint rawRejected ⟨_, _, _, rawParsed⟩

theorem NamedParameterCoreTraceParses.output_window
    {input output : Remainder} {value : Syntax.FunctionParameter} {trace : List ParseDiagnostic}
    (parsed : NamedParameterCoreTraceParses source endByte input value output trace) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex := by
  cases parsed with
  | ordinary _ raw => exact raw.output_window
  | comptime _ raw => exact raw.output_window

theorem NamedParameterCoreTraceParses.cascadeFilters
    {input output : Remainder} {value : Syntax.FunctionParameter} {trace : List ParseDiagnostic}
    (parsed : NamedParameterCoreTraceParses source endByte input value output trace)
    (text : String) (lexical : List SourceSpan) : ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases parsed with
  | ordinary _ raw => exact raw.cascadeFilters text lexical
  | comptime _ raw => exact raw.cascadeFilters text lexical

theorem NamedParameterCoreTraceRejects.cascadeFilters
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : NamedParameterCoreTraceRejects source endByte input rejected report trace)
    (text : String) (lexical : List SourceSpan) : ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases rejection with
  | ordinary _ raw => exact raw.cascadeFilters text lexical
  | comptime _ raw => exact raw.cascadeFilters text lexical

theorem namedParameterCoreTraceExactOutcomeSpec :
    TraceExactOutcomeSpec NamedParameterCoreTraceParses NamedParameterCoreTraceRejects source endByte where
  successResultUnique := NamedParameterCoreTraceParses.result_unique
  rejectResultUnique := NamedParameterCoreTraceRejects.result_unique
  successRejectDisjoint := NamedParameterCoreTraceRejects.disjoint_success

/-- A selected comptime rejection cannot fail at the marker or following name. -/
theorem ComptimeNamedParameterTraceRejects.tail_of_prefix
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (present : ComptimeLambdaParameterStartsAt input)
    (rejection : ComptimeNamedParameterTraceRejects source endByte input rejected report trace) :
    ∃ markerSpan afterMarker afterName name nameEvents tailEvents,
      ExactTokenParses (.identifier ContextualKeyword.comptime.spelling) input markerSpan afterMarker ∧
      IdentifierTraceParses afterMarker name afterName nameEvents ∧
      NamedParameterTailTraceRejects markerSpan (some markerSpan) name (SourceSpan.cover markerSpan name.span)
        source endByte afterName rejected report tailEvents ∧ trace = nameEvents ++ tailEvents := by
  rcases present with ⟨selectedMarker, selectedName, spelling, markerToken, nameToken⟩
  cases rejection with
  | markerMissing absent _ => exact False.elim (absent ⟨selectedMarker, markerToken⟩)
  | nameRejected markerSpan marker absent _ =>
      rcases marker with ⟨_, rfl⟩
      exact False.elim (absent ⟨selectedName, spelling, nameToken⟩)
  | tailRejected markerSpan marker nameParsed tail => exact ⟨_, _, _, _, _, _, marker, nameParsed, tail, rfl⟩

end Solcore.Syntax.DeclarativeGrammar
