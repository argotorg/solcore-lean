import Solcore.Syntax.Parser.ExportFinishSoundnessProperties
import Solcore.Syntax.Parser.ExportPathSoundnessProperties
import Solcore.Syntax.Parser.ExportSelectionSoundnessProperties

/-! Success soundness of all canonical path-export suffixes. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- A successful path-export helper follows one exact prioritized suffix. -/
theorem pathExport_success_sound (start : SourceSpan)
    {input next : State} {declaration : ExportDecl}
    (result : ExportInternals.pathExport start input =
      .ok declaration next) :
    DeclarativeGrammar.PathExportTailParses start
      input.declarativeRemainder declaration next.declarativeRemainder := by
  unfold ExportInternals.pathExport at result
  cases pathResult : ExportInternals.exportPath input with
  | invariant error => simp [bind, pathResult] at result
  | reject failure rejected => simp [bind, pathResult] at result
  | ok path afterPath =>
      have pathGrammar := exportPath_success_sound pathResult
      simp only [bind, pathResult, getState] at result
      split at result
      · cases dotResult : symbol .dot .exportDecl afterPath with
        | invariant error => simp [dotResult] at result
        | reject failure rejected => simp [dotResult] at result
        | ok dot afterDot =>
            have dotSound := symbol_ok_tokenAt .dot .exportDecl dotResult
            simp only [dotResult] at result
            cases selectionResult : ExportInternals.exportSelection afterDot with
            | invariant error => simp [selectionResult] at result
            | reject failure rejected => simp [selectionResult] at result
            | ok selection afterSelection =>
                have selectionGrammar := exportSelection_success_sound
                  selectionResult
                simp only [selectionResult] at result
                have finishGrammar := finishExport_success_sound start
                  (.itemsFrom path selection) result
                apply DeclarativeGrammar.PathExportTailParses.itemsFrom
                unfold DeclarativeGrammar.ItemsFromExportTailParses
                refine ⟨path, afterPath.declarativeRemainder, dot.span,
                  selection, afterSelection.declarativeRemainder,
                  pathGrammar, dotSound.1, ?_, finishGrammar⟩
                simpa only [dotSound.2, State.declarativeRemainder,
                  State.tokens, State.window, State.cursor] using
                  selectionGrammar
      · have dotFalse : isSymbol afterPath .dot = false := by
          cases found : isSymbol afterPath .dot <;> simp_all
        have dotAbsent := symbolAbsentAt_of_isSymbol_eq_false .dot dotFalse
        split at result
        · cases asResult : keyword .asKw .exportDecl afterPath with
          | invariant error => simp [asResult] at result
          | reject failure rejected => simp [asResult] at result
          | ok asToken afterAs =>
              have asSound := keyword_ok_tokenAt .asKw .exportDecl asResult
              simp only [asResult] at result
              cases aliasResult : identifier .exportDecl afterAs with
              | invariant error => simp [aliasResult] at result
              | reject failure rejected => simp [aliasResult] at result
              | ok alias afterAlias =>
                  have aliasGrammar := identifier_success_sound .exportDecl
                    aliasResult
                  simp only [aliasResult] at result
                  have finishGrammar := finishExport_success_sound start
                    (.moduleAs path alias) result
                  apply DeclarativeGrammar.PathExportTailParses.moduleAs
                  unfold DeclarativeGrammar.ModuleAsExportTailParses
                  refine ⟨path, afterPath.declarativeRemainder,
                    asToken.span, alias, afterAlias.declarativeRemainder,
                    pathGrammar, dotAbsent, asSound.1, ?_, finishGrammar⟩
                  simpa only [asSound.2, State.declarativeRemainder,
                    State.tokens, State.window, State.cursor] using
                    aliasGrammar
        · have asFalse : isKeyword afterPath .asKw = false := by
            cases found : isKeyword afterPath .asKw <;> simp_all
          have asAbsent := keywordAbsentAt_of_isKeyword_eq_false
            .asKw asFalse
          have finishGrammar := finishExport_success_sound start
            (.module path) result
          apply DeclarativeGrammar.PathExportTailParses.module
          unfold DeclarativeGrammar.ModuleExportTailParses
          exact ⟨path, afterPath.declarativeRemainder, pathGrammar,
            dotAbsent, asAbsent, finishGrammar⟩

end Solcore.Syntax.Parser
