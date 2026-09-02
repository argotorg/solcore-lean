import Solcore.Syntax.DeclarativeHidingClauseOutcomeProperties
import Solcore.Syntax.DeclarativeImportTerminatorOutcomeProperties
import Solcore.Syntax.DeclarativeModulePathOutcomeProperties
import Solcore.Syntax.DeclarativeSelectedImportsOutcomeProperties
import Solcore.Syntax.DeclarativeSelectiveImportOutcomeGrammar

/-! Deterministic and exclusive broad selective-import outcomes. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem exactToken_output_unique {kind : TokenKind}
    {input leftOutput rightOutput : Remainder}
    {leftSpan rightSpan : SourceSpan}
    (leftParsed : ExactTokenParses kind input leftSpan leftOutput)
    (rightParsed : ExactTokenParses kind input rightSpan rightOutput) :
    leftOutput = rightOutput := by
  rw [leftParsed.2, rightParsed.2]

private theorem absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

private theorem importTerminator_cross_output_unique
    {leftLast rightLast : SourceSpan} {input : Remainder}
    {leftSpan rightSpan : SourceSpan} {afterLeft afterRight : Remainder}
    (leftParsed : ImportTerminatorOrdinaryParses leftLast input leftSpan
      afterLeft)
    (rightParsed : ImportTerminatorOrdinaryParses rightLast input rightSpan
      afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | semicolon leftSemicolonSpan leftSemicolon =>
      cases rightParsed with
      | semicolon rightSemicolonSpan rightSemicolon =>
          exact exactToken_output_unique leftSemicolon rightSemicolon
      | recovered rightAbsent rightStarts =>
          exact False.elim
            (absent_conflicts_exact rightAbsent leftSemicolon)
  | recovered leftAbsent leftStarts =>
      cases rightParsed with
      | semicolon rightSemicolonSpan rightSemicolon =>
          exact False.elim
            (absent_conflicts_exact leftAbsent rightSemicolon)
      | recovered rightAbsent rightStarts => rfl

/-- Ordinary selective-import payloads have one final remainder. -/
theorem SelectiveImportOrdinaryParses.output_unique (start : SourceSpan)
    {input : Remainder} {left right : Syntax.ImportDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : SelectiveImportOrdinaryParses start input left afterLeft)
    (rightParsed : SelectiveImportOrdinaryParses start input right
      afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftFromSpan leftSelection leftFrom leftPath leftHiding
        leftTerminator =>
      cases rightParsed with
      | parsed rightFromSpan rightSelection rightFrom rightPath rightHiding
            rightTerminator =>
          have afterSelectionEq := SelectedImportsOrdinaryParses.output_unique
            leftSelection rightSelection
          subst afterSelectionEq
          have afterFromEq := exactToken_output_unique leftFrom rightFrom
          subst afterFromEq
          have afterPathEq := ModulePathOrdinaryParses.output_unique leftPath
            rightPath
          subst afterPathEq
          have afterHidingEq := OptionalHidingOrdinaryParses.output_unique
            leftHiding rightHiding
          subst afterHidingEq
          exact importTerminator_cross_output_unique leftTerminator
            rightTerminator

/-- Exact selective-import rejection excludes every broad ordinary success. -/
theorem SelectiveImportRejects.disjointOrdinary (start : SourceSpan)
    {input rejected : Remainder}
    (rejection : SelectiveImportRejects input rejected) :
    ¬ ∃ declaration output,
      SelectiveImportOrdinaryParses start input declaration output := by
  rintro ⟨declaration, output, successful⟩
  cases successful with
  | parsed successfulFromSpan successfulSelection successfulFrom
        successfulPath successfulHiding successfulTerminator =>
      cases rejection with
      | selectionRejected selectionRejected =>
          exact selectedImportsDeterministicOutcomeSpec.successRejectDisjoint
            selectionRejected ⟨_, _, successfulSelection⟩
      | fromMissing rejectedSelection fromAbsent =>
          have afterSelectionEq :=
            SelectedImportsOrdinaryParses.output_unique rejectedSelection
              successfulSelection
          subst afterSelectionEq
          exact absent_conflicts_exact fromAbsent successfulFrom
      | pathRejected rejectedFromSpan rejectedSelection rejectedFrom
            pathRejected =>
          have afterSelectionEq :=
            SelectedImportsOrdinaryParses.output_unique rejectedSelection
              successfulSelection
          subst afterSelectionEq
          have afterFromEq := exactToken_output_unique rejectedFrom
            successfulFrom
          subst afterFromEq
          exact modulePathDeterministicOutcomeSpec.successRejectDisjoint
            pathRejected ⟨_, _, successfulPath⟩
      | hidingRejected rejectedFromSpan rejectedSelection rejectedFrom
            rejectedPath hidingRejected =>
          have afterSelectionEq :=
            SelectedImportsOrdinaryParses.output_unique rejectedSelection
              successfulSelection
          subst afterSelectionEq
          have afterFromEq := exactToken_output_unique rejectedFrom
            successfulFrom
          subst afterFromEq
          have afterPathEq := ModulePathOrdinaryParses.output_unique
            rejectedPath successfulPath
          subst afterPathEq
          exact optionalHidingDeterministicOutcomeSpec.successRejectDisjoint
            hidingRejected ⟨_, _, successfulHiding⟩
      | terminatorRejected rejectedFromSpan rejectedSelection rejectedFrom
            rejectedPath rejectedHiding terminatorRejected =>
          have afterSelectionEq :=
            SelectedImportsOrdinaryParses.output_unique rejectedSelection
              successfulSelection
          subst afterSelectionEq
          have afterFromEq := exactToken_output_unique rejectedFrom
            successfulFrom
          subst afterFromEq
          have afterPathEq := ModulePathOrdinaryParses.output_unique
            rejectedPath successfulPath
          subst afterPathEq
          have afterHidingEq := OptionalHidingOrdinaryParses.output_unique
            rejectedHiding successfulHiding
          subst afterHidingEq
          exact ImportTerminatorRejects.disjointOrdinary _
            terminatorRejected ⟨_, _, successfulTerminator⟩

/-- Selective-import payloads have deterministic and exclusive broad ordinary
outcomes for each fixed declaration start span. -/
theorem selectiveImportDeterministicOutcomeSpec (start : SourceSpan) :
    DeterministicOutcomeSpec (SelectiveImportOrdinaryParses start)
      SelectiveImportRejects where
  successOutputUnique := SelectiveImportOrdinaryParses.output_unique start
  successRejectDisjoint := SelectiveImportRejects.disjointOrdinary start

end Solcore.Syntax.DeclarativeGrammar
