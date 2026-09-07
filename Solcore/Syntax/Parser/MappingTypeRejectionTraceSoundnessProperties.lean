import Solcore.Syntax.DeclarativeMappingTypeRejectionTraceGrammar
import Solcore.Syntax.Parser.ExactTokenPrimitiveRejectionTraceProperties
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties
import Solcore.Syntax.Parser.DiagnosticTraceContracts
import Solcore.Syntax.Parser.Type

/-! Raw mapping rejection reflects exactly its first failing stage, retaining
earlier key/value diagnostics and never committing the unexpected report. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

theorem parseMappingType_reject_trace_sound
    {nested : Parser TypeExpr}
    {elementTrace : SourceId → Nat → DeclarativeGrammar.Remainder → TypeExpr →
      DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}
    {elementRejects : SourceId → Nat → DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
    (successSound : ParserTraceSuccessSound nested elementTrace)
    (rejectSound : ParserTraceRejectSound nested elementRejects)
    (contextFrame : ParserSuccessContext nested) :
    ParserTraceRejectSound (parseMappingType nested)
      (DeclarativeGrammar.MappingTypeTraceRejects elementTrace elementRejects) := by
  intro input rejected failure result
  unfold parseMappingType at result
  simp only [bind] at result
  cases markerResult : contextual .mapping .typeExpr input with
  | invariant error => simp [markerResult] at result
  | reject markerFailure markerRejected =>
      have shape := acceptToken_reject_state_shape (.contextual .mapping) .typeExpr
        (·.isContextual .mapping) markerResult
      subst markerRejected
      simp only [markerResult] at result
      cases result
      have reported := (contextual_reject_reports_iff .mapping .typeExpr).mpr ⟨failure, markerResult, rfl⟩
      exact ⟨[], .markerMissing reported.1 reported.2, by simp⟩
  | ok marker afterMarker =>
      have markerParsed := contextual_success_exactTokenParses .mapping .typeExpr markerResult
      have shape := (contextual_ok_tokenAt .mapping .typeExpr markerResult).2
      subst afterMarker
      simp only [markerResult] at result
      cases openingResult : symbol .leftParen .typeExpr { input with cursor := input.cursor + 1 } with
      | invariant error => simp [openingResult] at result
      | reject openingFailure openingRejected =>
          have shape := symbol_reject_state_eq .leftParen .typeExpr openingResult
          subst openingRejected
          simp only [openingResult] at result
          cases result
          have reported := (symbol_reject_reports_iff .leftParen .typeExpr).mpr ⟨failure, openingResult, rfl⟩
          exact ⟨[], .openingMissing marker.span markerParsed reported.1 reported.2,
            by simp only [List.append_nil]; rfl⟩
      | ok opening afterOpening =>
          have openingParsed := symbol_success_exactTokenParses .leftParen .typeExpr openingResult
          have shape := (symbol_ok_tokenAt .leftParen .typeExpr openingResult).2
          subst afterOpening
          simp only [openingResult] at result
          cases keyResult : nested { input with cursor := input.cursor + 1 + 1 } with
          | invariant error => simp [keyResult] at result
          | reject keyFailure keyRejected =>
              simp only [keyResult] at result
              cases result
              rcases rejectSound keyResult with ⟨trace, key, events⟩
              exact ⟨trace, .keyRejected marker.span opening.span markerParsed openingParsed key, events⟩
          | ok key afterKey =>
              simp only [keyResult] at result
              rcases successSound keyResult with ⟨keyEvents, keyParsed, keyEq⟩
              have keyFrame := contextFrame keyResult
              cases arrowResult : symbol .fatArrow .typeExpr afterKey with
              | invariant error => simp [arrowResult] at result
              | reject arrowFailure arrowRejected =>
                  have shape := symbol_reject_state_eq .fatArrow .typeExpr arrowResult
                  subst arrowRejected
                  simp only [arrowResult] at result
                  cases result
                  have reported := (symbol_reject_reports_iff .fatArrow .typeExpr).mpr ⟨failure, arrowResult, rfl⟩
                  refine ⟨keyEvents, .arrowMissing marker.span opening.span markerParsed openingParsed
                    keyParsed reported.1 ?_, keyEq⟩
                  simpa only [keyFrame.1, keyFrame.2] using reported.2
              | ok arrow afterArrow =>
                  have arrowParsed := symbol_success_exactTokenParses .fatArrow .typeExpr arrowResult
                  have shape := (symbol_ok_tokenAt .fatArrow .typeExpr arrowResult).2
                  subst afterArrow
                  simp only [arrowResult] at result
                  cases valueResult : nested { afterKey with cursor := afterKey.cursor + 1 } with
                  | invariant error => simp [valueResult] at result
                  | reject valueFailure valueRejected =>
                      simp only [valueResult] at result
                      cases result
                      rcases rejectSound valueResult with ⟨valueEvents, valueRejected, valueEq⟩
                      refine ⟨keyEvents ++ valueEvents, .valueRejected marker.span opening.span arrow.span
                        markerParsed openingParsed keyParsed arrowParsed ?_, ?_⟩
                      · simpa only [keyFrame.1, keyFrame.2] using valueRejected
                      · rw [valueEq]
                        change afterKey.diagnostics ++ valueEvents = input.diagnostics ++ _
                        rw [keyEq]; exact List.append_assoc _ _ _
                  | ok value afterValue =>
                      simp only [valueResult] at result
                      rcases successSound valueResult with ⟨valueEvents, valueParsed, valueEq⟩
                      have valueFrame := contextFrame valueResult
                      cases closingResult : symbol .rightParen .typeExpr afterValue with
                      | invariant error => simp [closingResult] at result
                      | ok closing final => simp [closingResult, pure] at result
                      | reject closingFailure closingRejected =>
                          have shape := symbol_reject_state_eq .rightParen .typeExpr closingResult
                          subst closingRejected
                          simp only [closingResult] at result
                          cases result
                          have reported := (symbol_reject_reports_iff .rightParen .typeExpr).mpr
                            ⟨failure, closingResult, rfl⟩
                          refine ⟨keyEvents ++ valueEvents, .closingMissing (value := value) marker.span opening.span arrow.span
                            markerParsed openingParsed keyParsed arrowParsed ?_ reported.1 ?_, ?_⟩
                          · simpa only [keyFrame.1, keyFrame.2] using valueParsed
                          · simpa only [valueFrame.1, valueFrame.2, keyFrame.1, keyFrame.2] using reported.2
                          · rw [valueEq]
                            change afterKey.diagnostics ++ valueEvents = input.diagnostics ++ _
                            rw [keyEq]; exact List.append_assoc _ _ _

end Solcore.Syntax.Parser
