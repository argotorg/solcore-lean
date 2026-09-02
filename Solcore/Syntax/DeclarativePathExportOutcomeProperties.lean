import Solcore.Syntax.DeclarativeCoreExpressionPostfixOrdinaryProperties
import Solcore.Syntax.DeclarativeExportPathOutcomeProperties
import Solcore.Syntax.DeclarativeExportSelectionOutcomeProperties
import Solcore.Syntax.DeclarativeFinishExportOutcomeProperties
import Solcore.Syntax.DeclarativePathExportOutcomeGrammar

/-! Deterministic and exclusive broad outcomes for path export payloads. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem token_conflict_after_path {kind : TokenKind}
    {input leftAfter rightAfter : Remainder}
    {leftPath rightPath : Syntax.QualifiedName} {span : SourceSpan}
    (leftParsed : ExportPathOrdinaryParses input leftPath leftAfter)
    (rightParsed : ExportPathOrdinaryParses input rightPath rightAfter)
    (present : TokenAt leftAfter.tokens leftAfter.endIndex leftAfter.cursor {
      span
      value := kind
    })
    (absent : TokenKindAbsentAt rightAfter.tokens rightAfter.endIndex
      rightAfter.cursor kind) : False := by
  have afterPathEq :=
    exportPathDeterministicOutcomeSpec.successOutputUnique leftParsed rightParsed
  subst afterPathEq
  exact absent ⟨span, present⟩
private theorem guard_conflict_after_path {kind : TokenKind}
    {input leftAfter rightAfter : Remainder}
    {leftPath rightPath : Syntax.QualifiedName}
    (leftParsed : ExportPathOrdinaryParses input leftPath leftAfter)
    (rightParsed : ExportPathOrdinaryParses input rightPath rightAfter)
    (present : PathExportTokenPresentAt leftAfter kind)
    (absent : TokenKindAbsentAt rightAfter.tokens rightAfter.endIndex
      rightAfter.cursor kind) : False := by
  have afterPathEq :=
    exportPathDeterministicOutcomeSpec.successOutputUnique leftParsed rightParsed
  subst afterPathEq
  rcases present with ⟨span, token⟩
  exact absent ⟨span, token⟩
private theorem finishExport_output_unique_anyValue
    {start : SourceSpan} {leftValue rightValue : Syntax.ExportDeclValue}
    {input : Remainder} {left right : Syntax.ExportDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : FinishExportOrdinaryParses start leftValue input left
      afterLeft)
    (rightParsed : FinishExportOrdinaryParses start rightValue input right
      afterRight) : afterLeft = afterRight := by
  rcases leftParsed with ⟨leftSpan, leftToken, leftOutput, leftDecl⟩
  rcases rightParsed with ⟨rightSpan, rightToken, rightOutput, rightDecl⟩
  rw [leftOutput, rightOutput]
/-- Ordinary path-export success has one final remainder. -/
theorem PathExportOrdinaryParses.output_unique (start : SourceSpan)
    {input : Remainder} {left right : Syntax.ExportDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : PathExportOrdinaryParses start input left afterLeft)
    (rightParsed : PathExportOrdinaryParses start input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | itemsFrom leftItems =>
      unfold ItemsFromExportTailParses at leftItems
      rcases leftItems with
        ⟨_, _, _, _, _, leftPathParsed, leftDot, leftSelectionParsed, leftFinish⟩
      cases rightParsed with
      | itemsFrom rightItems =>
          unfold ItemsFromExportTailParses at rightItems
          rcases rightItems with
            ⟨_, _, _, _, _, rightPathParsed, _, rightSelectionParsed, rightFinish⟩
          have afterPathEq := exportPathDeterministicOutcomeSpec
            |>.successOutputUnique leftPathParsed rightPathParsed
          subst afterPathEq
          have afterSelectionEq := exportSelectionDeterministicOutcomeSpec
            |>.successOutputUnique leftSelectionParsed rightSelectionParsed
          subst afterSelectionEq
          exact finishExport_output_unique_anyValue leftFinish rightFinish
      | moduleAs rightAlias =>
          unfold ModuleAsExportTailParses at rightAlias
          rcases rightAlias with
            ⟨_, _, _, _, _, rightPathParsed, rightDotAbsent, _, _, _⟩
          exact False.elim (token_conflict_after_path leftPathParsed
            rightPathParsed leftDot rightDotAbsent)
      | module rightModule =>
          unfold ModuleExportTailParses at rightModule
          rcases rightModule with
            ⟨_, _, rightPathParsed, rightDotAbsent, _, _⟩
          exact False.elim (token_conflict_after_path leftPathParsed
            rightPathParsed leftDot rightDotAbsent)
  | moduleAs leftAlias =>
      unfold ModuleAsExportTailParses at leftAlias
      rcases leftAlias with
        ⟨_, _, _, _, _, leftPathParsed, leftDotAbsent, leftAs,
          leftNameParsed, leftFinish⟩
      cases rightParsed with
      | itemsFrom rightItems =>
          unfold ItemsFromExportTailParses at rightItems
          rcases rightItems with
            ⟨_, _, _, _, _, rightPathParsed, rightDot, _, _⟩
          exact False.elim (token_conflict_after_path rightPathParsed
            leftPathParsed rightDot leftDotAbsent)
      | moduleAs rightAlias =>
          unfold ModuleAsExportTailParses at rightAlias
          rcases rightAlias with
            ⟨_, _, _, _, _, rightPathParsed, _, _, rightNameParsed,
              rightFinish⟩
          have afterPathEq := exportPathDeterministicOutcomeSpec
            |>.successOutputUnique leftPathParsed rightPathParsed
          subst afterPathEq
          have afterAliasEq := IdentifierParses.output_unique leftNameParsed
            rightNameParsed
          subst afterAliasEq
          exact finishExport_output_unique_anyValue leftFinish rightFinish
      | module rightModule =>
          unfold ModuleExportTailParses at rightModule
          rcases rightModule with
            ⟨_, _, rightPathParsed, _, rightAsAbsent, _⟩
          exact False.elim (token_conflict_after_path leftPathParsed
            rightPathParsed leftAs rightAsAbsent)
  | module leftModule =>
      unfold ModuleExportTailParses at leftModule
      rcases leftModule with
        ⟨_, _, leftPathParsed, leftDotAbsent, leftAsAbsent, leftFinish⟩
      cases rightParsed with
      | itemsFrom rightItems =>
          unfold ItemsFromExportTailParses at rightItems
          rcases rightItems with
            ⟨_, _, _, _, _, rightPathParsed, rightDot, _, _⟩
          exact False.elim (token_conflict_after_path rightPathParsed
            leftPathParsed rightDot leftDotAbsent)
      | moduleAs rightAlias =>
          unfold ModuleAsExportTailParses at rightAlias
          rcases rightAlias with
            ⟨_, _, _, _, _, rightPathParsed, _, rightAs, _, _⟩
          exact False.elim (token_conflict_after_path rightPathParsed
            leftPathParsed rightAs leftAsAbsent)
      | module rightModule =>
          unfold ModuleExportTailParses at rightModule
          rcases rightModule with
            ⟨_, _, rightPathParsed, _, _, rightFinish⟩
          have afterPathEq := exportPathDeterministicOutcomeSpec
            |>.successOutputUnique leftPathParsed rightPathParsed
          subst afterPathEq
          exact finishExport_output_unique_anyValue leftFinish rightFinish

/-- Exact path-export rejection excludes every ordinary success. -/
theorem PathExportRejects.disjointOrdinary (start : SourceSpan) {input
    rejected : Remainder} (rejection : PathExportRejects input rejected) :
    ¬ ∃ declaration output,
      PathExportOrdinaryParses start input declaration output := by
  rintro ⟨declaration, output, successful⟩
  cases rejection with
  | pathRejected pathRejected =>
      cases successful with
      | itemsFrom parsed =>
          unfold ItemsFromExportTailParses at parsed
          rcases parsed with ⟨_, _, _, _, _, pathParsed, _, _, _⟩
          exact exportPathDeterministicOutcomeSpec.successRejectDisjoint
            pathRejected ⟨_, _, pathParsed⟩
      | moduleAs parsed =>
          unfold ModuleAsExportTailParses at parsed
          rcases parsed with ⟨_, _, _, _, _, pathParsed, _, _, _, _⟩
          exact exportPathDeterministicOutcomeSpec.successRejectDisjoint
            pathRejected ⟨_, _, pathParsed⟩
      | module parsed =>
          unfold ModuleExportTailParses at parsed
          rcases parsed with ⟨_, _, pathParsed, _, _, _⟩
          exact exportPathDeterministicOutcomeSpec.successRejectDisjoint
            pathRejected ⟨_, _, pathParsed⟩
  | selectionRejected dotSpan rejectedPath dotPresent dotParsed
      selectionRejected =>
      cases successful with
      | itemsFrom parsed =>
          unfold ItemsFromExportTailParses at parsed
          rcases parsed with ⟨_, _, _, _, _, pathParsed, _,
            selectionParsed, _⟩
          have afterPathEq := exportPathDeterministicOutcomeSpec
            |>.successOutputUnique rejectedPath pathParsed
          subst afterPathEq
          rw [dotParsed.2] at selectionRejected
          exact exportSelectionDeterministicOutcomeSpec.successRejectDisjoint
            selectionRejected ⟨_, _, selectionParsed⟩
      | moduleAs parsed =>
          unfold ModuleAsExportTailParses at parsed
          rcases parsed with ⟨_, _, _, _, _, pathParsed,
            successfulDotAbsent, _, _, _⟩
          exact guard_conflict_after_path rejectedPath pathParsed dotPresent
            successfulDotAbsent
      | module parsed =>
          unfold ModuleExportTailParses at parsed
          rcases parsed with ⟨_, _, pathParsed, successfulDotAbsent, _, _⟩
          exact guard_conflict_after_path rejectedPath pathParsed dotPresent
            successfulDotAbsent
  | selectionFinishRejected dotSpan rejectedPath dotPresent dotParsed
      rejectedSelection finishRejected =>
      cases successful with
      | itemsFrom parsed =>
          unfold ItemsFromExportTailParses at parsed
          rcases parsed with ⟨path, _, _, selection, _, pathParsed, _,
            selectionParsed, finish⟩
          have afterPathEq := exportPathDeterministicOutcomeSpec
            |>.successOutputUnique rejectedPath pathParsed
          subst afterPathEq
          rw [dotParsed.2] at rejectedSelection
          have afterSelectionEq := exportSelectionDeterministicOutcomeSpec
            |>.successOutputUnique rejectedSelection selectionParsed
          subst afterSelectionEq
          exact (finishExportDeterministicOutcomeSpec start
            (.itemsFrom path selection)).successRejectDisjoint finishRejected
              ⟨_, _, finish⟩
      | moduleAs parsed =>
          unfold ModuleAsExportTailParses at parsed
          rcases parsed with ⟨_, _, _, _, _, pathParsed,
            successfulDotAbsent, _, _, _⟩
          exact guard_conflict_after_path rejectedPath pathParsed dotPresent
            successfulDotAbsent
      | module parsed =>
          unfold ModuleExportTailParses at parsed
          rcases parsed with ⟨_, _, pathParsed, successfulDotAbsent, _, _⟩
          exact guard_conflict_after_path rejectedPath pathParsed dotPresent
            successfulDotAbsent
  | aliasRejected asSpan rejectedPath dotAbsent asPresent asParsed
      aliasRejected =>
      cases successful with
      | itemsFrom parsed =>
          unfold ItemsFromExportTailParses at parsed
          rcases parsed with ⟨_, _, _, _, _, pathParsed, dotToken, _, _⟩
          exact token_conflict_after_path pathParsed rejectedPath dotToken
            dotAbsent
      | moduleAs parsed =>
          unfold ModuleAsExportTailParses at parsed
          rcases parsed with ⟨_, _, _, _, _, pathParsed, _, _,
            aliasParsed, _⟩
          have afterPathEq := exportPathDeterministicOutcomeSpec
            |>.successOutputUnique rejectedPath pathParsed
          subst afterPathEq
          rw [asParsed.2] at aliasRejected
          exact identifierDeterministicOutcomeSpec.successRejectDisjoint
            aliasRejected ⟨_, _, aliasParsed⟩
      | module parsed =>
          unfold ModuleExportTailParses at parsed
          rcases parsed with ⟨_, _, pathParsed, _, successfulAsAbsent, _⟩
          exact guard_conflict_after_path rejectedPath pathParsed asPresent
            successfulAsAbsent
  | aliasFinishRejected asSpan rejectedPath dotAbsent asPresent asParsed
      rejectedAlias finishRejected =>
      cases successful with
      | itemsFrom parsed =>
          unfold ItemsFromExportTailParses at parsed
          rcases parsed with ⟨_, _, _, _, _, pathParsed, dotToken, _, _⟩
          exact token_conflict_after_path pathParsed rejectedPath dotToken
            dotAbsent
      | moduleAs parsed =>
          unfold ModuleAsExportTailParses at parsed
          rcases parsed with ⟨path, _, _, alias, _, pathParsed, _, _,
            aliasParsed, finish⟩
          have afterPathEq := exportPathDeterministicOutcomeSpec
            |>.successOutputUnique rejectedPath pathParsed
          subst afterPathEq
          rw [asParsed.2] at rejectedAlias
          have afterAliasEq := IdentifierParses.output_unique rejectedAlias
            aliasParsed
          subst afterAliasEq
          exact (finishExportDeterministicOutcomeSpec start
            (.moduleAs path alias)).successRejectDisjoint finishRejected
              ⟨_, _, finish⟩
      | module parsed =>
          unfold ModuleExportTailParses at parsed
          rcases parsed with ⟨_, _, pathParsed, _, successfulAsAbsent, _⟩
          exact guard_conflict_after_path rejectedPath pathParsed asPresent
            successfulAsAbsent
  | moduleFinishRejected rejectedPath dotAbsent asAbsent finishRejected =>
      cases successful with
      | itemsFrom parsed =>
          unfold ItemsFromExportTailParses at parsed
          rcases parsed with ⟨_, _, _, _, _, pathParsed, dotToken, _, _⟩
          exact token_conflict_after_path pathParsed rejectedPath dotToken
            dotAbsent
      | moduleAs parsed =>
          unfold ModuleAsExportTailParses at parsed
          rcases parsed with ⟨_, _, _, _, _, pathParsed, _, asToken, _, _⟩
          exact token_conflict_after_path pathParsed rejectedPath asToken
            asAbsent
      | module parsed =>
          unfold ModuleExportTailParses at parsed
          rcases parsed with ⟨path, _, pathParsed, _, _, finish⟩
          have afterPathEq := exportPathDeterministicOutcomeSpec
            |>.successOutputUnique rejectedPath pathParsed
          subst afterPathEq
          exact (finishExportDeterministicOutcomeSpec start
            (.module path)).successRejectDisjoint finishRejected
              ⟨_, _, finish⟩

/-- Deterministic broad path-export outcomes for each fixed outer start. -/
theorem pathExportDeterministicOutcomeSpec (start : SourceSpan) :
    DeterministicOutcomeSpec (PathExportOrdinaryParses start)
      PathExportRejects where
  successOutputUnique := PathExportOrdinaryParses.output_unique start
  successRejectDisjoint := PathExportRejects.disjointOrdinary start

end Solcore.Syntax.DeclarativeGrammar
