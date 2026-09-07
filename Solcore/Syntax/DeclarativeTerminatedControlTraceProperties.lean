import Solcore.Syntax.DeclarativeTerminatedControlTraceGrammar
import Solcore.Syntax.DeclarativeRejectionDiagnosticProperties
import Solcore.Syntax.DeclarativePrimitiveExactnessProperties

/-! Exact functionality and ordinary erasure of silent control traces. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {keyword : HardKeyword} {statementValue : Syntax.StatementValue}
  {source : SourceId} {endByte : Nat}

theorem TerminatedControlStatementTraceParses.result_unique
    {input afterLeft afterRight : Remainder} {left right : Syntax.Statement}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : TerminatedControlStatementTraceParses keyword statementValue
      source endByte input left afterLeft leftTrace)
    (rightParsed : TerminatedControlStatementTraceParses keyword statementValue
      source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  rcases leftParsed with ⟨leftParsed, rfl⟩
  rcases rightParsed with ⟨rightParsed, rfl⟩
  cases leftParsed with
  | parsed leftMarker leftSemicolon markerLeft semicolonLeft =>
      cases rightParsed with
      | parsed rightMarker rightSemicolon markerRight semicolonRight =>
          rcases markerLeft.result_unique markerRight with ⟨rfl, rfl⟩
          rcases semicolonLeft.result_unique semicolonRight with ⟨rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

theorem TerminatedControlStatementTraceRejects.ordinary
    {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (traced : TerminatedControlStatementTraceRejects keyword source endByte
      input rejected diagnostic trace) : TerminatedControlStatementRejects keyword input rejected := by
  cases traced with
  | markerMissing absent _ => exact .markerMissing absent
  | semicolonMissing span marker absent _ => exact .semicolonMissing span marker absent

theorem TerminatedControlStatementTraceRejects.trace_eq_nil
    {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (traced : TerminatedControlStatementTraceRejects keyword source endByte
      input rejected diagnostic trace) : trace = [] := by
  cases traced <;> rfl

theorem TerminatedControlStatementTraceRejects.result_unique
    {input afterLeft afterRight : Remainder} {left right : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftRejected : TerminatedControlStatementTraceRejects keyword source endByte
      input afterLeft left leftTrace)
    (rightRejected : TerminatedControlStatementTraceRejects keyword source endByte
      input afterRight right rightTrace) :
    afterLeft = afterRight ∧ left = right ∧ leftTrace = rightTrace := by
  cases leftRejected with
  | markerMissing absent reported =>
      cases rightRejected with
      | markerMissing _ rightReported => exact ⟨rfl, reported.diagnostic_unique rightReported, rfl⟩
      | semicolonMissing span marker _ _ => exact False.elim (absent ⟨span, marker.1⟩)
  | semicolonMissing span marker absent reported =>
      cases rightRejected with
      | markerMissing rightAbsent _ => exact False.elim (rightAbsent ⟨span, marker.1⟩)
      | semicolonMissing rightSpan rightMarker _ rightReported =>
          rcases marker.result_unique rightMarker with ⟨rfl, rfl⟩
          exact ⟨rfl, reported.diagnostic_unique rightReported, rfl⟩

end Solcore.Syntax.DeclarativeGrammar
