import Solcore.Syntax.DeclarativeHidingClauseOutcomeProperties
import Solcore.Syntax.DeclarativeImportTerminatorOutcomeProperties
import Solcore.Syntax.DeclarativeModulePathOutcomeProperties
import Solcore.Syntax.DeclarativeWildcardImportOutcomeGrammar

/-! Deterministic and exclusive broad wildcard-import outcomes. -/

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

/-- Ordinary wildcard-import payloads have one final remainder. -/
theorem WildcardImportOrdinaryParses.output_unique (start : SourceSpan)
    {input : Remainder} {left right : Syntax.ImportDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : WildcardImportOrdinaryParses start input left afterLeft)
    (rightParsed : WildcardImportOrdinaryParses start input right
      afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftStarSpan leftFromSpan leftStar leftFrom leftPath leftHiding
        leftTerminator =>
      cases rightParsed with
      | parsed rightStarSpan rightFromSpan rightStar rightFrom rightPath
            rightHiding rightTerminator =>
          have afterStarEq := exactToken_output_unique leftStar rightStar
          subst afterStarEq
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

/-- Exact wildcard-import rejection excludes every broad ordinary success. -/
theorem WildcardImportRejects.disjointOrdinary (start : SourceSpan)
    {input rejected : Remainder}
    (rejection : WildcardImportRejects input rejected) :
    ¬ ∃ declaration output,
      WildcardImportOrdinaryParses start input declaration output := by
  rintro ⟨declaration, output, successful⟩
  cases successful with
  | parsed successfulStarSpan successfulFromSpan successfulStar
        successfulFrom successfulPath successfulHiding
        successfulTerminator =>
      cases rejection with
      | starMissing starAbsent =>
          exact absent_conflicts_exact starAbsent successfulStar
      | fromMissing rejectedStarSpan rejectedStar fromAbsent =>
          have afterStarEq := exactToken_output_unique rejectedStar
            successfulStar
          subst afterStarEq
          exact absent_conflicts_exact fromAbsent successfulFrom
      | pathRejected rejectedStarSpan rejectedFromSpan rejectedStar
            rejectedFrom pathRejected =>
          have afterStarEq := exactToken_output_unique rejectedStar
            successfulStar
          subst afterStarEq
          have afterFromEq := exactToken_output_unique rejectedFrom
            successfulFrom
          subst afterFromEq
          exact modulePathDeterministicOutcomeSpec.successRejectDisjoint
            pathRejected ⟨_, _, successfulPath⟩
      | hidingRejected rejectedStarSpan rejectedFromSpan rejectedStar
            rejectedFrom rejectedPath hidingRejected =>
          have afterStarEq := exactToken_output_unique rejectedStar
            successfulStar
          subst afterStarEq
          have afterFromEq := exactToken_output_unique rejectedFrom
            successfulFrom
          subst afterFromEq
          have afterPathEq := ModulePathOrdinaryParses.output_unique
            rejectedPath successfulPath
          subst afterPathEq
          exact optionalHidingDeterministicOutcomeSpec.successRejectDisjoint
            hidingRejected ⟨_, _, successfulHiding⟩
      | terminatorRejected rejectedStarSpan rejectedFromSpan rejectedStar
            rejectedFrom rejectedPath rejectedHiding terminatorRejected =>
          have afterStarEq := exactToken_output_unique rejectedStar
            successfulStar
          subst afterStarEq
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

/-- Wildcard-import payloads have deterministic and exclusive broad ordinary
outcomes for each fixed declaration start span. -/
theorem wildcardImportDeterministicOutcomeSpec (start : SourceSpan) :
    DeterministicOutcomeSpec (WildcardImportOrdinaryParses start)
      WildcardImportRejects where
  successOutputUnique := WildcardImportOrdinaryParses.output_unique start
  successRejectDisjoint := WildcardImportRejects.disjointOrdinary start

end Solcore.Syntax.DeclarativeGrammar
