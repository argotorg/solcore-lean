import Solcore.Syntax.Parser.MappingTypeRejectionTraceSoundnessProperties

/-! Every independent raw mapping failure executes with its exact report and
prior-preserving key/value suffix. Child source/full-window preservation is
explicit, with no progress, valid-carrier, or rejected-state-frame premise. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

theorem parseMappingType_trace_reject_complete
    {nested : Parser TypeExpr}
    {elementTrace : SourceId → Nat → DeclarativeGrammar.Remainder → TypeExpr →
      DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}
    {elementRejects : SourceId → Nat → DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
    (successComplete : ParserTraceSuccessComplete nested elementTrace)
    (rejectComplete : ParserTraceRejectComplete nested elementRejects)
    (contextFrame : ParserSuccessContext nested) :
    ParserTraceRejectComplete (parseMappingType nested)
      (DeclarativeGrammar.MappingTypeTraceRejects elementTrace elementRejects) := by
  intro input after report trace rejection
  cases rejection with
  | markerMissing absent reported =>
      rcases (contextual_reject_reports_iff .mapping .typeExpr).mp ⟨absent, reported⟩ with
        ⟨failure, result, reportEq⟩
      exact ⟨failure, input, by simp only [parseMappingType, bind, result], rfl, reportEq, by simp⟩
  | openingMissing markerSpan marker absent reported =>
      have markerResult := contextual_eq_ok_of_exactTokenParses .mapping .typeExpr marker
      rcases marker with ⟨_, rfl⟩
      rcases (symbol_reject_reports_iff .leftParen .typeExpr
          (input := { input with cursor := input.cursor + 1 })).mp ⟨absent, reported⟩ with
        ⟨failure, result, reportEq⟩
      exact ⟨failure, { input with cursor := input.cursor + 1 },
        by simp only [parseMappingType, bind, markerResult, result], rfl, reportEq,
        by simp only [List.append_nil]; rfl⟩
  | keyRejected markerSpan openingSpan marker opening key =>
      have markerResult := contextual_eq_ok_of_exactTokenParses .mapping .typeExpr marker
      rcases marker with ⟨_, rfl⟩
      have openingResult := symbol_eq_ok_of_exactTokenParses .leftParen .typeExpr
        (input := { input with cursor := input.cursor + 1 }) opening
      rcases opening with ⟨_, rfl⟩
      rcases rejectComplete (input := { input with cursor := input.cursor + 1 + 1 }) key with
        ⟨failure, rejected, result, afterEq, reportEq, events⟩
      exact ⟨failure, rejected, by simp only [parseMappingType, bind, markerResult, openingResult, result],
        afterEq, reportEq, events⟩
  | arrowMissing markerSpan openingSpan marker opening key absent reported =>
      have markerResult := contextual_eq_ok_of_exactTokenParses .mapping .typeExpr marker
      rcases marker with ⟨_, rfl⟩
      have openingResult := symbol_eq_ok_of_exactTokenParses .leftParen .typeExpr
        (input := { input with cursor := input.cursor + 1 }) opening
      rcases opening with ⟨_, rfl⟩
      rcases successComplete (input := { input with cursor := input.cursor + 1 + 1 }) key with
        ⟨afterKey, keyResult, afterEq, events⟩
      have frame := contextFrame keyResult
      have absentAtKey : DeclarativeGrammar.TokenKindAbsentAt afterKey.tokens afterKey.window.endIndex
          afterKey.cursor (.symbol .fatArrow) := by simpa only [← afterEq, State.declarativeRemainder] using absent
      have reportAtKey : DeclarativeGrammar.RejectAtReports afterKey.file.id afterKey.window.endByte
          { head := .symbol .fatArrow, tail := [] } .typeExpr afterKey.declarativeRemainder report := by
        simpa only [frame.1, frame.2, afterEq] using reported
      rcases (symbol_reject_reports_iff .fatArrow .typeExpr).mp ⟨absentAtKey, reportAtKey⟩ with
        ⟨failure, result, reportEq⟩
      exact ⟨failure, afterKey,
        by simp only [parseMappingType, bind, markerResult, openingResult, keyResult, result],
        afterEq, reportEq, events⟩
  | valueRejected markerSpan openingSpan arrowSpan marker opening key arrow value =>
      rename_i afterMarker afterOpening keyRem afterArrow keyValue keyEvents valueEvents
      have markerResult := contextual_eq_ok_of_exactTokenParses .mapping .typeExpr marker
      rcases marker with ⟨_, rfl⟩
      have openingResult := symbol_eq_ok_of_exactTokenParses .leftParen .typeExpr
        (input := { input with cursor := input.cursor + 1 }) opening
      rcases opening with ⟨_, rfl⟩
      rcases successComplete (input := { input with cursor := input.cursor + 1 + 1 }) key with
        ⟨afterKey, keyResult, keyAfter, keyEq⟩
      have frame := contextFrame keyResult
      have arrowAtKey := arrow
      rw [← keyAfter] at arrowAtKey
      have arrowResult := symbol_eq_ok_of_exactTokenParses .fatArrow .typeExpr arrowAtKey
      have valueAtArrow : elementRejects afterKey.file.id afterKey.window.endByte
          ({ afterKey with cursor := afterKey.cursor + 1 } : State).declarativeRemainder after report valueEvents := by
        simpa only [frame.1, frame.2, arrow.2, ← keyAfter, State.declarativeRemainder] using value
      rcases rejectComplete (input := { afterKey with cursor := afterKey.cursor + 1 }) valueAtArrow with
        ⟨failure, rejected, result, afterEq, reportEq, valueEq⟩
      refine ⟨failure, rejected, ?_, afterEq, reportEq, ?_⟩
      · simp only [parseMappingType, bind, markerResult, openingResult, keyResult, arrowResult, result]
      · rw [valueEq]
        change afterKey.diagnostics ++ valueEvents = input.diagnostics ++ _
        rw [keyEq]; exact List.append_assoc _ _ _
  | closingMissing markerSpan openingSpan arrowSpan marker opening key arrow value absent reported =>
      rename_i afterMarker afterOpening keyRem afterArrow keyValue valueValue keyEvents valueEvents
      have markerResult := contextual_eq_ok_of_exactTokenParses .mapping .typeExpr marker
      rcases marker with ⟨_, rfl⟩
      have openingResult := symbol_eq_ok_of_exactTokenParses .leftParen .typeExpr
        (input := { input with cursor := input.cursor + 1 }) opening
      rcases opening with ⟨_, rfl⟩
      rcases successComplete (input := { input with cursor := input.cursor + 1 + 1 }) key with
        ⟨afterKey, keyResult, keyAfter, keyEq⟩
      have keyFrame := contextFrame keyResult
      have arrowAtKey := arrow
      rw [← keyAfter] at arrowAtKey
      have arrowResult := symbol_eq_ok_of_exactTokenParses .fatArrow .typeExpr arrowAtKey
      have valueAtArrow : elementTrace afterKey.file.id afterKey.window.endByte
          ({ afterKey with cursor := afterKey.cursor + 1 } : State).declarativeRemainder valueValue after valueEvents := by
        simpa only [keyFrame.1, keyFrame.2, arrow.2, ← keyAfter, State.declarativeRemainder] using value
      rcases successComplete (input := { afterKey with cursor := afterKey.cursor + 1 }) valueAtArrow with
        ⟨afterValue, valueResult, valueAfter, valueEq⟩
      have valueFrame := contextFrame valueResult
      have absentAtValue : DeclarativeGrammar.TokenKindAbsentAt afterValue.tokens afterValue.window.endIndex
          afterValue.cursor (.symbol .rightParen) := by
        simpa only [← valueAfter, State.declarativeRemainder] using absent
      have reportAtValue : DeclarativeGrammar.RejectAtReports afterValue.file.id afterValue.window.endByte
          { head := .symbol .rightParen, tail := [] } .typeExpr afterValue.declarativeRemainder report := by
        simpa only [valueFrame.1, valueFrame.2, keyFrame.1, keyFrame.2, valueAfter] using reported
      rcases (symbol_reject_reports_iff .rightParen .typeExpr).mp ⟨absentAtValue, reportAtValue⟩ with
        ⟨failure, result, reportEq⟩
      refine ⟨failure, afterValue, ?_, valueAfter, reportEq, ?_⟩
      · simp only [parseMappingType, bind, markerResult, openingResult, keyResult, arrowResult, valueResult, result]
      · rw [valueEq]
        change afterKey.diagnostics ++ valueEvents = input.diagnostics ++ _
        rw [keyEq]; exact List.append_assoc _ _ _

end Solcore.Syntax.Parser
