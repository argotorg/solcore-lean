import Solcore.Syntax.DeclarativePathExportOutcomeGrammar
import Solcore.Syntax.Parser.CoreIdentifierOutcomeSoundnessProperties
import Solcore.Syntax.Parser.CoreTypeOutcomePrimitiveProperties
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties
import Solcore.Syntax.Parser.ExportPathOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.ExportSelectionOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.FinishExportOrdinaryOutcomeSoundnessProperties

/-! Exact executable rejection reflection for path export payloads. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every executable path-export rejection records the exact first failing
path, selected suffix, alias suffix, or non-recovering finish stage. -/
theorem pathExport_reject_ordinaryOutcome_sound (start : SourceSpan)
    {input rejected : State} {failure : Failure}
    (result : ExportInternals.pathExport start input =
      .reject failure rejected) :
    DeclarativeGrammar.PathExportRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold ExportInternals.pathExport at result
  cases pathResult : ExportInternals.exportPath input with
  | invariant error => simp [bind, pathResult] at result
  | reject pathFailure pathRejected =>
      simp only [bind, pathResult] at result
      cases result
      exact .pathRejected
        (exportPath_reject_ordinaryOutcome_sound pathResult)
  | ok path afterPath =>
      have pathParsed := exportPath_success_ordinaryOutcome_sound pathResult
      simp only [bind, pathResult, getState] at result
      by_cases dotPresent : isSymbol afterPath .dot = true
      · rcases symbol_eq_ok_of_isSymbol_eq_true .dot .exportDecl dotPresent
          with ⟨dot, dotResult⟩
        have dotParsed := symbol_success_exactTokenParses .dot .exportDecl
          dotResult
        have dotGuard : DeclarativeGrammar.PathExportTokenPresentAt
            afterPath.declarativeRemainder (.symbol .dot) :=
          ⟨dot.span, dotParsed.1⟩
        simp only [dotPresent, if_true, dotResult] at result
        cases selectionResult : ExportInternals.exportSelection
            { afterPath with cursor := afterPath.cursor + 1 } with
        | invariant error => simp [selectionResult] at result
        | reject selectionFailure selectionRejected =>
            simp only [selectionResult] at result
            cases result
            exact .selectionRejected dot.span pathParsed dotGuard dotParsed
              (exportSelection_reject_ordinaryOutcome_sound selectionResult)
        | ok selection afterSelection =>
            have selectionParsed :=
              exportSelection_success_ordinaryOutcome_sound selectionResult
            simp only [selectionResult] at result
            exact .selectionFinishRejected dot.span pathParsed dotGuard
              dotParsed selectionParsed
              (finishExport_reject_ordinaryOutcome_sound start
                (.itemsFrom path selection) result)
      · have dotAbsentBool : isSymbol afterPath .dot = false :=
          Bool.eq_false_iff.mpr dotPresent
        simp only [dotAbsentBool, Bool.false_eq_true, if_false] at result
        have dotAbsent := symbolAbsentAt_of_isSymbol_eq_false .dot
          dotAbsentBool
        by_cases asPresent : isKeyword afterPath .asKw = true
        · rcases keyword_eq_ok_of_isKeyword_eq_true .asKw .exportDecl
              asPresent with ⟨asToken, asResult⟩
          have asParsed := keyword_success_exactTokenParses .asKw .exportDecl
            asResult
          have asGuard : DeclarativeGrammar.PathExportTokenPresentAt
              afterPath.declarativeRemainder (.keyword .asKw) :=
            ⟨asToken.span, asParsed.1⟩
          simp only [asPresent, if_true, asResult] at result
          cases aliasResult : identifier .exportDecl
              { afterPath with cursor := afterPath.cursor + 1 } with
          | invariant error => simp [aliasResult] at result
          | reject aliasFailure aliasRejected =>
              simp only [aliasResult] at result
              cases result
              exact .aliasRejected asToken.span pathParsed dotAbsent asGuard
                asParsed (identifier_reject_sound .exportDecl aliasResult)
          | ok alias afterAlias =>
              have aliasParsed := identifier_success_sound .exportDecl
                aliasResult
              simp only [aliasResult] at result
              exact .aliasFinishRejected asToken.span pathParsed dotAbsent
                asGuard asParsed aliasParsed
                (finishExport_reject_ordinaryOutcome_sound start
                  (.moduleAs path alias) result)
        · have asAbsentBool : isKeyword afterPath .asKw = false :=
            Bool.eq_false_iff.mpr asPresent
          simp only [asAbsentBool, Bool.false_eq_true, if_false] at result
          exact .moduleFinishRejected pathParsed dotAbsent
            (keywordAbsentAt_of_isKeyword_eq_false .asKw asAbsentBool)
            (finishExport_reject_ordinaryOutcome_sound start (.module path)
              result)

end Solcore.Syntax.Parser
