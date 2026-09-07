import Solcore.Syntax.DeclarativeNamedParameterRawTraceProperties
import Solcore.Syntax.DeclarativeRejectionDiagnosticProperties

/-! First-failure exactness for the two raw parameter forms. A marker failure
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

theorem OrdinaryNamedParameterTraceRejects.result_unique
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftRejected : OrdinaryNamedParameterTraceRejects source endByte input afterLeft leftReport leftTrace)
    (rightRejected : OrdinaryNamedParameterTraceRejects source endByte input afterRight rightReport rightTrace) :
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

theorem OrdinaryNamedParameterTraceRejects.disjoint_success
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : OrdinaryNamedParameterTraceRejects source endByte input rejected report trace) :
    ¬ ∃ value output events, OrdinaryNamedParameterTraceParses source endByte input value output events := by
  rintro ⟨value, output, events, parsed⟩
  cases parsed with
  | parsed name tail =>
      cases rejection with
      | nameRejected absent _ => exact checked_name_absent_conflict absent name
      | tailRejected otherName otherTail =>
          rcases name.result_unique otherName with ⟨rfl, rfl, rfl⟩
          exact otherTail.disjoint_success ⟨_, _, _, tail⟩

theorem OrdinaryNamedParameterTraceRejects.cascadeFilters
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : OrdinaryNamedParameterTraceRejects source endByte input rejected report trace)
    (text : String) (lexical : List SourceSpan) : ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases rejection with
  | nameRejected => exact .nil
  | tailRejected name tail => exact (name.cascadeFilters text lexical).append (tail.cascadeFilters text lexical)

theorem ordinaryNamedParameterTraceExactOutcomeSpec {source : SourceId} {endByte : Nat} :
    TraceExactOutcomeSpec OrdinaryNamedParameterTraceParses OrdinaryNamedParameterTraceRejects source endByte where
  successResultUnique := OrdinaryNamedParameterTraceParses.result_unique
  rejectResultUnique := OrdinaryNamedParameterTraceRejects.result_unique
  successRejectDisjoint := OrdinaryNamedParameterTraceRejects.disjoint_success

theorem ComptimeNamedParameterTraceRejects.result_unique
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftRejected : ComptimeNamedParameterTraceRejects source endByte input afterLeft leftReport leftTrace)
    (rightRejected : ComptimeNamedParameterTraceRejects source endByte input afterRight rightReport rightTrace) :
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

theorem ComptimeNamedParameterTraceRejects.disjoint_success
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ComptimeNamedParameterTraceRejects source endByte input rejected report trace) :
    ¬ ∃ value output events, ComptimeNamedParameterTraceParses source endByte input value output events := by
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
          exact otherTail.disjoint_success ⟨_, _, _, tail⟩

theorem ComptimeNamedParameterTraceRejects.cascadeFilters
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ComptimeNamedParameterTraceRejects source endByte input rejected report trace)
    (text : String) (lexical : List SourceSpan) : ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases rejection with
  | markerMissing | nameRejected => exact .nil
  | tailRejected _ _ name tail =>
      exact ((identifierTraceParses_iff.mp name).2.cascadeFilters text lexical).append (tail.cascadeFilters text lexical)

theorem comptimeNamedParameterTraceExactOutcomeSpec {source : SourceId} {endByte : Nat} :
    TraceExactOutcomeSpec ComptimeNamedParameterTraceParses ComptimeNamedParameterTraceRejects source endByte where
  successResultUnique := ComptimeNamedParameterTraceParses.result_unique
  rejectResultUnique := ComptimeNamedParameterTraceRejects.result_unique
  successRejectDisjoint := ComptimeNamedParameterTraceRejects.disjoint_success

end Solcore.Syntax.DeclarativeGrammar
