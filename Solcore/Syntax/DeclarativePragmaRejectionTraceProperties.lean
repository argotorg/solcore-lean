import Solcore.Syntax.DeclarativePragmaRejectionTraceGrammar
import Solcore.Syntax.DeclarativePragmaItemsRejectionTraceProperties
import Solcore.Syntax.DeclarativePragmaCascadeProperties

/-! Erasure, coverage, and raw-event protection for complete pragma rejection. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Complete rejection traces refine the established first-rejecting-stage grammar. -/
theorem PragmaDeclTraceRejects.ordinary
    {source : SourceId} {endByte : Nat} {input rejected : Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (traced : PragmaDeclTraceRejects source endByte input rejected diagnostic trace) :
    PragmaDeclRejects input rejected := by
  cases traced with
  | keywordMissing absent reported => exact .keywordMissing absent
  | nameRejected marker keywordParsed nameRejected reported =>
      exact .nameRejected marker keywordParsed nameRejected
  | itemsRejected marker keywordParsed nameParsed itemsRejected =>
      rcases itemsRejected with ⟨names, rejectedPrefix, events, reported⟩
      exact .itemsRejected marker keywordParsed nameParsed rejectedPrefix.ordinary
  | semicolonMissing marker keywordParsed nameParsed itemsParsed absent reported =>
      exact .semicolonMissing marker keywordParsed nameParsed itemsParsed.1 absent

/-- Every ordinary rejection has an independent report and emitted event trace.
The successful prefix stays hidden, because a rejected reply does not return it. -/
theorem PragmaDeclRejects.exists_trace (source : SourceId) (endByte : Nat)
    {input rejected : Remainder} (rejection : PragmaDeclRejects input rejected) :
    ∃ diagnostic trace, PragmaDeclTraceRejects source endByte input rejected diagnostic trace := by
  cases rejection with
  | keywordMissing absent =>
      rcases rejectAtReports_total source endByte
        { head := .keyword .pragmaKw, tail := [] } .pragmaDecl input with ⟨diagnostic, reported⟩
      exact ⟨diagnostic, [], .keywordMissing absent reported⟩
  | nameRejected marker keywordParsed nameRejected =>
      rcases rejectAtReports_total source endByte
        { head := .identifier, tail := [] } .pragmaDecl rejected with ⟨diagnostic, reported⟩
      exact ⟨diagnostic, [], .nameRejected marker keywordParsed nameRejected reported⟩
  | itemsRejected marker keywordParsed nameParsed itemsRejected =>
      rcases itemsRejected.exists_prefix with ⟨names, rejectedPrefix⟩
      rcases identifierListDiagnosticTrace_total names with ⟨trace, events⟩
      rcases rejectAtReports_total source endByte
        { head := .identifier, tail := [] } .pragmaDecl rejected with ⟨diagnostic, reported⟩
      exact ⟨diagnostic, trace, .itemsRejected marker keywordParsed nameParsed
        ⟨names, rejectedPrefix, events, reported⟩⟩
  | semicolonMissing marker keywordParsed nameParsed itemsParsed absent =>
      rcases identifierListDiagnosticTrace_total _ with ⟨trace, events⟩
      rcases rejectAtReports_total source endByte
        { head := .symbol .semicolon, tail := [] } .pragmaDecl rejected with ⟨diagnostic, reported⟩
      exact ⟨diagnostic, trace, .semicolonMissing marker keywordParsed nameParsed
        ⟨itemsParsed, events⟩ absent reported⟩

/-- Previously emitted checked-item events remain protected even when a later
stage rejects. This does not claim protection of the separate failure report. -/
theorem PragmaDeclTraceRejects.cascadeFilters
    {source : SourceId} {endByte : Nat} {input rejected : Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (traced : PragmaDeclTraceRejects source endByte input rejected diagnostic trace)
    (text : String) (lexical : List SourceSpan) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases traced with
  | keywordMissing => exact .nil
  | nameRejected => exact .nil
  | itemsRejected marker keywordParsed nameParsed itemsRejected =>
      rcases itemsRejected with ⟨names, rejectedPrefix, events, reported⟩
      exact events.cascadeFilters text lexical
  | semicolonMissing marker keywordParsed nameParsed itemsParsed absent reported =>
      exact itemsParsed.2.cascadeFilters text lexical

private theorem itemsRejection_ordinary
    {source : SourceId} {endByte : Nat} {input rejected : Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (traced : PragmaItemsTraceRejects source endByte input rejected diagnostic trace) :
    PragmaItemsRejects input rejected := by
  rcases traced with ⟨names, rejectedPrefix, events, reported⟩
  exact rejectedPrefix.ordinary

/-- Fixed context and input determine the exact first failure and every earlier
event; different rejecting stages cannot select competing reports. -/
theorem PragmaDeclTraceRejects.result_unique
    {source : SourceId} {endByte : Nat} {input afterLeft afterRight : Remainder}
    {leftDiagnostic rightDiagnostic : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (left : PragmaDeclTraceRejects source endByte input afterLeft leftDiagnostic leftTrace)
    (right : PragmaDeclTraceRejects source endByte input afterRight rightDiagnostic rightTrace) :
    afterLeft = afterRight ∧ leftDiagnostic = rightDiagnostic ∧ leftTrace = rightTrace := by
  cases left with
  | keywordMissing absent reported =>
      cases right with
      | keywordMissing _ rightReported => exact ⟨rfl, reported.diagnostic_unique rightReported, rfl⟩
      | nameRejected marker keywordParsed _ _ => exact False.elim (absent ⟨marker, keywordParsed.1⟩)
      | itemsRejected marker keywordParsed _ _ => exact False.elim (absent ⟨marker, keywordParsed.1⟩)
      | semicolonMissing marker keywordParsed _ _ _ _ =>
          exact False.elim (absent ⟨marker, keywordParsed.1⟩)
  | nameRejected marker keywordParsed nameRejected reported =>
      cases right with
      | keywordMissing absent _ => exact False.elim (absent ⟨marker, keywordParsed.1⟩)
      | nameRejected rightMarker rightKeyword rightName rightReported =>
          cases keywordParsed.output_unique rightKeyword
          cases identifierExactOutcomeSpec.rejectOutputUnique nameRejected rightName
          exact ⟨rfl, reported.diagnostic_unique rightReported, rfl⟩
      | itemsRejected rightMarker rightKeyword rightName rightItems =>
          cases keywordParsed.output_unique rightKeyword
          exact False.elim (identifierExactOutcomeSpec.successRejectDisjoint nameRejected
            ⟨_, _, rightName⟩)
      | semicolonMissing rightMarker rightKeyword rightName rightItems rightAbsent rightReported =>
          cases keywordParsed.output_unique rightKeyword
          exact False.elim (identifierExactOutcomeSpec.successRejectDisjoint nameRejected
            ⟨_, _, rightName⟩)
  | itemsRejected marker keywordParsed nameParsed itemsRejected =>
      cases right with
      | keywordMissing absent _ => exact False.elim (absent ⟨marker, keywordParsed.1⟩)
      | nameRejected rightMarker rightKeyword rightName rightReported =>
          cases keywordParsed.output_unique rightKeyword
          exact False.elim (identifierExactOutcomeSpec.successRejectDisjoint rightName
            ⟨_, _, nameParsed⟩)
      | itemsRejected rightMarker rightKeyword rightName rightItems =>
          cases keywordParsed.output_unique rightKeyword
          rcases nameParsed.result_unique rightName with ⟨rfl, rfl⟩
          exact itemsRejected.result_unique rightItems
      | semicolonMissing rightMarker rightKeyword rightName rightItems rightAbsent rightReported =>
          cases keywordParsed.output_unique rightKeyword
          rcases nameParsed.result_unique rightName with ⟨rfl, rfl⟩
          exact False.elim (pragmaItemsExactOutcomeSpec.successRejectDisjoint
            (itemsRejection_ordinary itemsRejected) ⟨_, _, rightItems.1⟩)
  | semicolonMissing marker keywordParsed nameParsed itemsParsed absent reported =>
      cases right with
      | keywordMissing absent _ => exact False.elim (absent ⟨marker, keywordParsed.1⟩)
      | nameRejected rightMarker rightKeyword rightName rightReported =>
          cases keywordParsed.output_unique rightKeyword
          exact False.elim (identifierExactOutcomeSpec.successRejectDisjoint rightName
            ⟨_, _, nameParsed⟩)
      | itemsRejected rightMarker rightKeyword rightName rightItems =>
          cases keywordParsed.output_unique rightKeyword
          rcases nameParsed.result_unique rightName with ⟨rfl, rfl⟩
          exact False.elim (pragmaItemsExactOutcomeSpec.successRejectDisjoint
            (itemsRejection_ordinary rightItems) ⟨_, _, itemsParsed.1⟩)
      | semicolonMissing rightMarker rightKeyword rightName rightItems rightAbsent rightReported =>
          cases keywordParsed.output_unique rightKeyword
          rcases nameParsed.result_unique rightName with ⟨rfl, rfl⟩
          rcases itemsParsed.result_unique rightItems with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, reported.diagnostic_unique rightReported, rfl⟩

end Solcore.Syntax.DeclarativeGrammar
