import Solcore.Syntax.DeclarativeLambdaParameterRawTraceProperties
import Solcore.Syntax.DeclarativeRejectionDiagnosticProperties

/-! First-failure exactness for the two raw lambda-parameter forms. A marker failure
is raw comptime rejection, not a selected-core judgment. Name/tail events are
preserved in order, and terminal reports are not part of the emitted trace. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {source : SourceId} {endByte : Nat}

private theorem checked_name_absent_conflict {input output : Remainder}
    {name : Syntax.Identifier} {trace : List ParseDiagnostic}
    (absent : IdentifierAbsentAt input) (parsed : CheckedParameterNameTraceParses input name output trace) : False :=
  absent ⟨name.span, name.value, parsed.ordinary.1⟩

private theorem identifier_absent_conflict {input output : Remainder}
    {name : Syntax.Identifier} {trace : List ParseDiagnostic}
    (absent : IdentifierAbsentAt input) (parsed : IdentifierTraceParses input name output trace) : False :=
  absent ⟨name.span, name.value, (identifierTraceParses_iff.mp parsed).1.1⟩

theorem OrdinaryLambdaParameterTraceRejects.result_unique
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftRejected : OrdinaryLambdaParameterTraceRejects source endByte input afterLeft leftReport leftTrace)
    (rightRejected : OrdinaryLambdaParameterTraceRejects source endByte input afterRight rightReport rightTrace) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace := by
  cases leftRejected with
  | nameRejected absent reported =>
      cases rightRejected with
      | nameRejected _ other => exact ⟨rfl, reported.diagnostic_unique other, rfl⟩
      | tailRejected name _ => exact False.elim (checked_name_absent_conflict absent name)
  | tailRejected name tail =>
      cases rightRejected with
      | nameRejected absent _ => exact False.elim (checked_name_absent_conflict absent name)
      | tailRejected otherName otherTail =>
          rcases name.result_unique otherName with ⟨rfl, rfl, rfl⟩
          rcases tail.result_unique otherTail with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

theorem OrdinaryLambdaParameterTraceRejects.disjoint_success
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : OrdinaryLambdaParameterTraceRejects source endByte input rejected report trace) :
    ¬ ∃ value output events, OrdinaryLambdaParameterTraceParses source endByte input value output events := by
  rintro ⟨value, output, events, parsed⟩
  cases parsed with
  | parsed name tail =>
      cases rejection with
      | nameRejected absent _ => exact checked_name_absent_conflict absent name
      | tailRejected otherName otherTail =>
          rcases name.result_unique otherName with ⟨rfl, rfl, rfl⟩
          exact OrdinaryLambdaParameterTailTraceRejects.disjoint_success otherTail ⟨_, _, _, tail⟩

theorem OrdinaryLambdaParameterTraceRejects.cascadeFilters
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : OrdinaryLambdaParameterTraceRejects source endByte input rejected report trace)
    (text : String) (lexical : List SourceSpan) : ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases rejection with
  | nameRejected => exact .nil
  | tailRejected name tail => exact (name.cascadeFilters text lexical).append (tail.cascadeFilters text lexical)

theorem ordinaryLambdaParameterTraceExactOutcomeSpec {source : SourceId} {endByte : Nat} :
    TraceExactOutcomeSpec OrdinaryLambdaParameterTraceParses OrdinaryLambdaParameterTraceRejects source endByte where
  successResultUnique := OrdinaryLambdaParameterTraceParses.result_unique
  rejectResultUnique := OrdinaryLambdaParameterTraceRejects.result_unique
  successRejectDisjoint := OrdinaryLambdaParameterTraceRejects.disjoint_success

theorem ComptimeLambdaParameterTraceRejects.result_unique
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftRejected : ComptimeLambdaParameterTraceRejects source endByte input afterLeft leftReport leftTrace)
    (rightRejected : ComptimeLambdaParameterTraceRejects source endByte input afterRight rightReport rightTrace) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace := by
  cases leftRejected with
  | markerMissing absent reported =>
      cases rightRejected with
      | markerMissing _ other => exact ⟨rfl, reported.diagnostic_unique other, rfl⟩
      | nameRejected span marker _ _ | tailRejected span marker _ _ => exact False.elim (absent ⟨span, marker.1⟩)
  | nameRejected span marker absent reported =>
      cases rightRejected with
      | markerMissing absent _ => exact False.elim (absent ⟨span, marker.1⟩)
      | nameRejected _ otherMarker _ other =>
          rcases marker.result_unique otherMarker with ⟨rfl, rfl⟩
          exact ⟨rfl, reported.diagnostic_unique other, rfl⟩
      | tailRejected _ otherMarker name _ =>
          rcases marker.result_unique otherMarker with ⟨rfl, rfl⟩
          exact False.elim (identifier_absent_conflict absent name)
  | tailRejected span marker name tail =>
      cases rightRejected with
      | markerMissing absent _ => exact False.elim (absent ⟨span, marker.1⟩)
      | nameRejected _ otherMarker absent _ =>
          rcases marker.result_unique otherMarker with ⟨rfl, rfl⟩
          exact False.elim (identifier_absent_conflict absent name)
      | tailRejected _ otherMarker otherName otherTail =>
          rcases marker.result_unique otherMarker with ⟨rfl, rfl⟩
          rcases name.result_unique otherName with ⟨rfl, rfl, rfl⟩
          rcases tail.result_unique otherTail with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

theorem ComptimeLambdaParameterTraceRejects.disjoint_success
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ComptimeLambdaParameterTraceRejects source endByte input rejected report trace) :
    ¬ ∃ value output events, ComptimeLambdaParameterTraceParses source endByte input value output events := by
  rintro ⟨value, output, events, parsed⟩
  cases parsed with
  | parsed span marker name tail =>
      cases rejection with
      | markerMissing absent _ => exact absent ⟨span, marker.1⟩
      | nameRejected _ otherMarker absent _ =>
          rcases marker.result_unique otherMarker with ⟨rfl, rfl⟩
          exact identifier_absent_conflict absent name
      | tailRejected _ otherMarker otherName otherTail =>
          rcases marker.result_unique otherMarker with ⟨rfl, rfl⟩
          rcases name.result_unique otherName with ⟨rfl, rfl, rfl⟩
          exact ComptimeLambdaParameterTailTraceRejects.disjoint_success otherTail ⟨_, _, _, tail⟩

theorem ComptimeLambdaParameterTraceRejects.cascadeFilters
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ComptimeLambdaParameterTraceRejects source endByte input rejected report trace)
    (text : String) (lexical : List SourceSpan) : ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases rejection with
  | markerMissing | nameRejected => exact .nil
  | tailRejected _ _ name tail =>
      exact ((identifierTraceParses_iff.mp name).2.cascadeFilters text lexical).append (tail.cascadeFilters text lexical)

theorem comptimeLambdaParameterTraceExactOutcomeSpec {source : SourceId} {endByte : Nat} :
    TraceExactOutcomeSpec ComptimeLambdaParameterTraceParses ComptimeLambdaParameterTraceRejects source endByte where
  successResultUnique := ComptimeLambdaParameterTraceParses.result_unique
  rejectResultUnique := ComptimeLambdaParameterTraceRejects.result_unique
  successRejectDisjoint := ComptimeLambdaParameterTraceRejects.disjoint_success

end Solcore.Syntax.DeclarativeGrammar
