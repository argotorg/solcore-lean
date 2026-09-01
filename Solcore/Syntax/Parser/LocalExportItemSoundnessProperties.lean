import Solcore.Syntax.Parser.ExportNameSoundnessProperties
import Solcore.Syntax.Parser.ExportPathSoundnessProperties

/-! Success soundness of canonical local export items. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Failed local-item dispatch excludes exactly an identifier-dot prefix. -/
private theorem identifierDotAbsentAt_of_dispatcher_eq_false {input : State}
    (stopped :
      (isIdentifier input && isSymbol
        { input with cursor := input.cursor + 1 } .dot) = false) :
    DeclarativeGrammar.IdentifierDotAbsentAt input.tokens
      input.window.endIndex input.cursor := by
  rintro ⟨identifierSpan, dotSpan, text, identifierAt, dotAt⟩
  have identifierPresent : isIdentifier input = true := by
    unfold isIdentifier State.peekKind? State.peek?
    simp only [identifierAt.1, ↓reduceIte, identifierAt.2, Option.map_some]
  have dotPresent :
      isSymbol { input with cursor := input.cursor + 1 } .dot = true := by
    unfold isSymbol State.peekKind? State.peek?
    simp only [dotAt.1, ↓reduceIte, dotAt.2, Option.map_some]
    rfl
  rw [identifierPresent, dotPresent] at stopped
  contradiction

/-- Every successful local export item follows its prioritized grammar. -/
theorem localExportItem_success_sound {input next : State}
    {item : LocalExportItem}
    (result : ExportInternals.localExportItem input = .ok item next) :
    DeclarativeGrammar.LocalExportItemParses input.declarativeRemainder item
      next.declarativeRemainder := by
  unfold ExportInternals.localExportItem at result
  split at result
  · cases pathResult : ExportInternals.exportPath input with
    | invariant error => simp [pathResult] at result
    | reject failure rejected => simp [pathResult] at result
    | ok path afterPath =>
        have pathGrammar := exportPath_success_sound pathResult
        simp only [pathResult] at result
        cases dotResult : symbol .dot .exportDecl afterPath with
        | invariant error => simp [dotResult] at result
        | reject failure rejected => simp [dotResult] at result
        | ok dot afterDot =>
            have dotSound := symbol_ok_tokenAt .dot .exportDecl dotResult
            simp only [dotResult] at result
            cases markerResult : symbol .star .exportDecl afterDot with
            | invariant error => simp [markerResult] at result
            | reject failure rejected => simp [markerResult] at result
            | ok marker afterMarker =>
                have markerSound := symbol_ok_tokenAt .star .exportDecl
                  markerResult
                simp only [markerResult] at result
                cases result
                have markerToken :
                    DeclarativeGrammar.TokenAt afterPath.tokens
                      afterPath.window.endIndex (afterPath.cursor + 1) {
                        span := marker.span
                        value := .symbol .star
                      } := by
                  simpa only [dotSound.2, State.tokens, State.window,
                    State.cursor] using markerSound.1
                have grammar :=
                  DeclarativeGrammar.LocalExportItemParses.moduleWildcard
                    dot.span marker.span pathGrammar dotSound.1 markerToken
                simpa only [markerSound.2, dotSound.2,
                  State.declarativeRemainder, State.tokens, State.window,
                  State.cursor, Nat.add_assoc] using grammar
  · have dispatcherFalse :
        (isIdentifier input && isSymbol
          { input with cursor := input.cursor + 1 } .dot) = false := by
      cases found : isIdentifier input && isSymbol
          { input with cursor := input.cursor + 1 } .dot <;> simp_all
    have qualifiedAbsent :=
      identifierDotAbsentAt_of_dispatcher_eq_false dispatcherFalse
    cases nameResult : ExportInternals.exportName input with
    | invariant error => simp [nameResult] at result
    | reject failure rejected => simp [nameResult] at result
    | ok name afterName =>
        have nameGrammar := exportName_success_sound nameResult
        simp only [nameResult] at result
        cases result
        exact DeclarativeGrammar.LocalExportItemParses.name qualifiedAbsent
          nameGrammar

/-- Local-item grammar soundness composes with source validity. -/
theorem localExportItem_success_sound_and_validFor {input next : State}
    {item : LocalExportItem} (inputValid : input.ValidFor)
    (result : ExportInternals.localExportItem input = .ok item next) :
    DeclarativeGrammar.LocalExportItemParses input.declarativeRemainder item
        next.declarativeRemainder ∧
      item.ValidFor input.file := by
  refine ⟨localExportItem_success_sound result, ?_⟩
  have valid := localExportItem_validFor input inputValid
  rw [result] at valid
  exact valid.1

end Solcore.Syntax.Parser
